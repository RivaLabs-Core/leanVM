//! Each instruction class's function ([`super::semantics`]) as a flock gate list.
//!
//! A circuit's ports are whole 64-bit words, and they are the words its table puts
//! on the bus: the values read from the registers, the bytecode's immediate and
//! flags, the result. A circuit is defined on its class's legal flags only, which
//! are one-hot where they select, so a selection is an XOR of products.

use flock::circuit::{Builder, Circuit, Wire};

/// A word of wires, low bit first.
type Word = Vec<Wire>;

fn xor_words(c: &mut Builder, x: &[Wire], y: &[Wire]) -> Word {
    x.iter().zip(y).map(|(&x, &y)| c.xor(x, y)).collect()
}

/// `s·x`, bit by bit.
fn gate_word(c: &mut Builder, s: Wire, x: &[Wire]) -> Word {
    x.iter().map(|&x| c.and(s, x)).collect()
}

/// Whether any bit of `x` is set.
fn any(c: &mut Builder, x: &[Wire]) -> Wire {
    x.iter().fold(None, |acc, &bit| c.or(acc, bit))
}

/// `x + y + carry_in`, and the carry out of the top bit.
fn add_with_carry(c: &mut Builder, x: &[Wire], y: &[Wire], carry_in: Wire) -> (Word, Wire) {
    let mut carry = carry_in;
    let mut sum = Vec::with_capacity(x.len());
    for (&x, &y) in x.iter().zip(y) {
        let xc = c.xor(x, carry);
        let yc = c.xor(y, carry);
        sum.push(c.xor(xc, y));
        let maj = c.and(xc, yc);
        carry = c.xor(maj, carry);
    }
    (sum, carry)
}

/// `x`, its bits from 32 up replaced by bit 31 when `word` is set.
fn sext32_if(c: &mut Builder, word: Wire, x: &[Wire]) -> Word {
    (0..64)
        .map(|i| if i < 32 { x[i] } else { c.mux(word, x[31], x[i]) })
        .collect()
}

/// [`super::Class::Alu`]'s ports.
pub mod alu_ports {
    /// Input words: the two register values, the immediate, the flags.
    pub const V1: usize = 0;
    pub const V2: usize = 1;
    pub const IMM: usize = 2;
    pub const FLAGS: usize = 3;
    /// Output words.
    pub const OUT: usize = 4;
    pub const TAKEN: usize = 5;
}

/// [`super::semantics::alu`].
pub fn alu() -> Circuit {
    let mut c = Builder::new(&[64, 64, 64, 15], &[64, 1]);
    let (v1, v2, imm, f) = (c.input(0), c.input(1), c.input(2), c.input(3));
    let flag = |bit: u64| f[bit.trailing_zeros() as usize];
    use super::alu::*;

    let b = xor_words(&mut c, &v2, &imm);
    // `v1 - b` is `v1 + !b + 1`, and it borrows exactly when that does not carry out.
    let sub = flag(SUB);
    let b_or_not: Word = b.iter().map(|&bit| c.xor(bit, sub)).collect();
    let (sum, carry_out) = add_with_carry(&mut c, &v1, &b_or_not, sub);
    let ltu = c.not(carry_out);
    let signs = c.xor(v1[63], b[63]);
    let lt = c.xor(ltu, signs);
    let diff = xor_words(&mut c, &v1, &b);
    let ne = any(&mut c, &diff);
    let eq = c.not(ne);

    // `out`: the sum unless a selector is set. AND is a product, OR is AND plus XOR.
    let sum = sext32_if(&mut c, flag(WORD), &sum);
    let selectors = [SEL_LT, SEL_LTU, SEL_AND, SEL_OR, SEL_XOR];
    let none = selectors.iter().fold(c.one(), |acc, &s| c.xor(acc, flag(s)));
    let and_or = c.xor(flag(SEL_AND), flag(SEL_OR));
    let or_xor = c.xor(flag(SEL_OR), flag(SEL_XOR));
    let mut out = gate_word(&mut c, none, &sum);
    for i in 0..64 {
        let both = c.and(v1[i], b[i]);
        let and_term = c.and(and_or, both);
        let xor_term = c.and(or_xor, diff[i]);
        let logic = c.xor(and_term, xor_term);
        out[i] = c.xor(out[i], logic);
    }
    let lt_term = c.and(flag(SEL_LT), lt);
    let ltu_term = c.and(flag(SEL_LTU), ltu);
    let compared = c.xor(lt_term, ltu_term);
    out[0] = c.xor(out[0], compared);
    let keep_bit0 = c.not(flag(CLEAR_BIT0));
    out[0] = c.and(keep_bit0, out[0]);

    let (ge, geu) = (c.not(lt), c.not(ltu));
    let taken = [
        (BR_EQ, eq),
        (BR_NE, ne),
        (BR_LT, lt),
        (BR_GE, ge),
        (BR_LTU, ltu),
        (BR_GEU, geu),
    ]
    .into_iter()
    .fold(flag(ALWAYS), |acc, (when, holds)| {
        let term = c.and(flag(when), holds);
        c.xor(acc, term)
    });

    for (i, &wire) in out.iter().enumerate() {
        c.output(0, i, wire);
    }
    c.output(1, 0, taken);
    c.finish()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rv::semantics;
    use crate::transcript::{ProverState, VerifierState};

    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }
        fn word(&mut self) -> u64 {
            match self.next() % 6 {
                0 => [
                    0,
                    1,
                    u64::MAX,
                    1 << 63,
                    (1 << 63) - 1,
                    1 << 31,
                    0xffff_ffff,
                    (1 << 31) - 1,
                ][(self.next() % 8) as usize],
                1 => self.next() as i32 as i64 as u64,
                _ => self.next(),
            }
        }
    }

    /// The circuit's output words on `inputs`, read off the witness it generates.
    fn run(circuit: &Circuit, inputs: &[u64], outputs: std::ops::Range<usize>) -> Vec<u64> {
        let words = 1 << (circuit.k_log() - 6);
        let (mut z, mut az, mut bz) = (vec![0; words], vec![0; words], vec![0; words]);
        circuit.witness_instance(inputs, &mut z, &mut az, &mut bz);
        z[outputs].to_vec()
    }

    #[test]
    fn alu_is_its_reference() {
        let circuit = alu();
        assert_eq!(circuit.k_log(), 10, "an ALU instance is 16 packed words");
        let mut rng = Rng(0xA1);
        for &flags in &crate::rv::alu::LEGAL {
            for round in 0..400 {
                let v1 = rng.word();
                // Equal operands now and then, which random words never are.
                let v2 = if round % 7 == 0 { v1 } else { rng.word() };
                // One of `v2` and `imm` is zero, as the decoder has it.
                let (v2, imm) = if round % 2 == 0 { (v2, 0) } else { (0, v2) };
                let (out, taken) = semantics::alu(v1, v2, imm, flags);
                assert_eq!(
                    run(&circuit, &[v1, v2, imm, flags], alu_ports::OUT..alu_ports::TAKEN + 1),
                    [out, taken as u64],
                    "flags {flags:#x} on {v1:#x}, {v2:#x}, {imm:#x}"
                );
            }
        }
    }

    /// flock proves a batch of honest instances, and refuses one with a flipped output bit.
    #[test]
    fn alu_reduction_roundtrip() {
        const LABEL: &[u8] = b"rv-alu-reduction-test";
        let circuit = alu();
        let block = circuit.block();
        let n_log = 4;
        let mut rng = Rng(0xA2);
        let legal = crate::rv::alu::LEGAL;
        let rows: Vec<[u64; 4]> = (0..1 << n_log)
            .map(|i| [rng.word(), rng.word(), 0, legal[i % legal.len()]])
            .collect();
        let run = |tamper: Option<usize>| {
            let (mut z, a, b, mut z_lincheck) = circuit.generate_witness(&rows, n_log);
            if let Some(bit) = tamper {
                z[bit / 64] ^= 1 << (bit % 64);
                z_lincheck[bit] ^= 1;
            }
            let mut ps = ProverState::from_label(LABEL);
            let stage = block.prove_zerocheck(n_log, &z, &a, &b, &mut ps);
            let claim = block.prove_lincheck(n_log, stage, &z_lincheck, &mut ps);
            let proof = ps.into_proof();
            let mut vs = VerifierState::from_label(LABEL, &proof);
            block.verify(n_log, &mut vs).is_ok_and(|r| r.claim == claim) && vs.finish().is_ok()
        };
        assert!(run(None));
        // An output bit, a spare bit of `taken`'s word, a product.
        for bit in [
            64 * alu_ports::OUT + 5,
            64 * alu_ports::TAKEN + 1,
            circuit.useful_bits() - 1,
        ] {
            assert!(!run(Some(bit)), "flipping bit {bit} must reject");
        }
    }
}
