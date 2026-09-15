//! u64 arithmetic as Flock R1CS circuits, one operation per block: wrapping
//! addition ([`add`]), and multiplication ([`mul`]) wrapping or widening.
//!
//! ## Witness layout per block
//!
//! ```text
//!   z[0         .. 64)        = a                  (free input)
//!   z[64        .. 128)       = b                  (free input)
//!   z[128       .. 128 + N)   = the N-bit result   (committed copies)
//!   z[128 + N]                = 1                  (constant wire)
//!   z[129 + N   .. useful)    = the circuit's products
//!   z[useful    .. 2^k_log)   = padding (forced to 0 by empty rows)
//! ```
//!
//! A circuit is one gate list, where a wire is the gate driving it and each
//! committed wire is a row. As in [`crate::hash`], no matrix is ever built: the
//! verifier walks the list forwards and the prover backwards (doc/leanvm, Annex
//! C "Evaluating the matrices"). The witness is word arithmetic on the same
//! structure the list is built from, one instance at a time.

pub mod add;
pub mod mul;

use crate::lincheck::LincheckCircuit;
use crate::reduction::Block;
use crate::witness::drive_witness_packed_and_lincheck;
use primitives::field::F192;
use zk_alloc::ArenaVec;

pub const A_BASE: usize = 0;
pub const B_BASE: usize = 64;
pub const OUT_BASE: usize = 128;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum U64Op {
    /// `a + b mod 2^64`.
    WrappingAdd,
    /// `a·b mod 2^64`.
    WrappingMul,
    /// `a·b` as a u128.
    WideningMul,
}

impl U64Op {
    /// Bits of the committed result.
    pub const fn out_bits(self) -> usize {
        match self {
            Self::WrappingAdd | Self::WrappingMul => 64,
            Self::WideningMul => 128,
        }
    }
}

/// A wire is the index of the gate driving it.
#[derive(Clone, Copy)]
enum Gate {
    /// The committed free wire at `slot`: an input, or the constant. Row `z[slot]·1 = z[slot]`.
    Free(u32),
    /// `w_x ⊕ w_y`, uncommitted.
    Xor(u32, u32),
    /// Row `w_x · w_y = z[slot]`.
    And(u32, u32, u32),
    /// Row `w_x · 1 = z[slot]`: an affine wire committed, which is how the result leaves the circuit.
    Copy(u32, u32),
}

/// A gate list under construction: the constant wire, `a` and `b` come first,
/// and products take the slots after the constant in the order they are made.
struct Builder {
    gates: Vec<Gate>,
    next_slot: usize,
    one: Option<u32>,
    a: [Option<u32>; 64],
    b: [Option<u32>; 64],
}

impl Builder {
    fn new(out_bits: usize) -> Self {
        let const_pos = OUT_BASE + out_bits;
        let mut c = Self {
            gates: Vec::new(),
            next_slot: const_pos + 1,
            one: None,
            a: [None; 64],
            b: [None; 64],
        };
        c.one = Some(c.push(Gate::Free(const_pos as u32)));
        let a = std::array::from_fn(|i| Some(c.push(Gate::Free((A_BASE + i) as u32))));
        let b = std::array::from_fn(|i| Some(c.push(Gate::Free((B_BASE + i) as u32))));
        (c.a, c.b) = (a, b);
        c
    }

    fn push(&mut self, gate: Gate) -> u32 {
        self.gates.push(gate);
        (self.gates.len() - 1) as u32
    }

    /// `None` is a structural zero.
    fn xor(&mut self, x: Option<u32>, y: Option<u32>) -> Option<u32> {
        match (x, y) {
            (Some(x), Some(y)) => Some(self.push(Gate::Xor(x, y))),
            _ => x.or(y),
        }
    }

    fn and(&mut self, x: Option<u32>, y: Option<u32>) -> u32 {
        let slot = self.next_slot as u32;
        self.next_slot += 1;
        self.push(Gate::And(x.unwrap(), y.unwrap(), slot))
    }

    /// Commits `wire` as result bit `i`.
    fn output(&mut self, i: usize, wire: Option<u32>) {
        self.push(Gate::Copy(
            wire.expect("every result bit has a wire"),
            (OUT_BASE + i) as u32,
        ));
    }
}

/// One instance's words of `z`, `A·z` and `B·z`.
struct Instance<'a> {
    z: &'a mut [u64],
    az: &'a mut [u64],
    bz: &'a mut [u64],
}

impl Instance<'_> {
    /// `width` rows from `slot` whose B side is the constant, with `A·z = z = v`.
    fn unit_rows(&mut self, slot: usize, v: u128, width: usize) {
        or_bits(self.z, slot, v);
        or_bits(self.az, slot, v);
        or_bits(self.bz, slot, u128::MAX >> (128 - width));
    }

    /// Product rows from `slot`, one per position of `mask`, with `A·z = left`,
    /// `B·z = right` and `z = left·right`.
    fn products(&mut self, slot: usize, mask: u128, left: u128, right: u128) {
        if mask != 0 {
            let shift = mask.trailing_zeros();
            or_bits(self.z, slot, (left & right & mask) >> shift);
            or_bits(self.az, slot, (left & mask) >> shift);
            or_bits(self.bz, slot, (right & mask) >> shift);
        }
    }
}

/// OR `v` into `buf` from bit `at`.
#[inline(always)]
fn or_bits(buf: &mut [u64], at: usize, v: u128) {
    let s = at % 64;
    let words = [
        (v << s) as u64,
        ((v >> 1) >> (63 - s)) as u64,
        ((v >> 1) >> (127 - s)) as u64,
    ];
    for (w, x) in buf[at / 64..].iter_mut().zip(words) {
        *w |= x;
    }
}

/// What an operation's witness is computed from, besides its inputs.
enum Plan {
    Add(add::Adder),
    Mul(mul::Multiplier),
}

pub struct U64Circuit {
    op: U64Op,
    gates: Vec<Gate>,
    plan: Plan,
    const_pos: usize,
    k_log: usize,
    useful_bits: usize,
}

impl U64Circuit {
    pub fn new(op: U64Op) -> Self {
        let n = op.out_bits();
        let mut c = Builder::new(n);
        let plan = match op {
            U64Op::WrappingAdd => Plan::Add(add::Adder::build(&mut c)),
            U64Op::WrappingMul | U64Op::WideningMul => Plan::Mul(mul::Multiplier::build(&mut c, n)),
        };
        let useful_bits = c.next_slot;
        Self {
            op,
            gates: c.gates,
            plan,
            const_pos: OUT_BASE + n,
            k_log: useful_bits.next_power_of_two().trailing_zeros() as usize,
            useful_bits,
        }
    }

    pub fn k_log(&self) -> usize {
        self.k_log
    }

    pub fn useful_bits(&self) -> usize {
        self.useful_bits
    }

    pub fn block(&self) -> Block<'_> {
        Block {
            k_log: self.k_log,
            useful_bits: self.useful_bits,
            circuit: self,
        }
    }

    /// `(z, a, b, z_lincheck)` for `pairs` padded with `(0, 0)` to
    /// `2^n_blocks_log` instances: the bit-packed `z`, `A·z` and `B·z`
    /// (`2^k_log / 64` words per instance), and lincheck's byte stripes.
    pub fn generate_witness(
        &self,
        pairs: &[(u64, u64)],
        n_blocks_log: usize,
    ) -> (ArenaVec<u64>, ArenaVec<u64>, ArenaVec<u64>, ArenaVec<u8>) {
        let n = self.op.out_bits();
        drive_witness_packed_and_lincheck(pairs, Some(&(0, 0)), n_blocks_log, self.k_log, |&(a, b), z, az, bz| {
            let mut witness = Instance { z, az, bz };
            let out = match &self.plan {
                Plan::Add(adder) => adder.witness(a, b, &mut witness),
                Plan::Mul(multiplier) => multiplier.witness(a, b, &mut witness),
            };
            witness.unit_rows(A_BASE, a as u128, 64);
            witness.unit_rows(B_BASE, b as u128, 64);
            witness.unit_rows(OUT_BASE, out, n);
            witness.unit_rows(self.const_pos, 1, 1);
        })
    }

    /// The matrix-vector products `(A_0 w, B_0 w)`, by one forward walk.
    fn row_values(&self, w: &[F192]) -> (Vec<F192>, Vec<F192>) {
        let k = self.n_cols();
        assert_eq!(w.len(), k);
        let wc = w[self.const_pos];
        let mut ra = vec![F192::ZERO; k];
        let mut rb = vec![F192::ZERO; k];
        let mut wires: Vec<F192> = Vec::with_capacity(self.gates.len());
        for &gate in &self.gates {
            let v = match gate {
                Gate::Free(s) => {
                    let s = s as usize;
                    (ra[s], rb[s]) = (w[s], wc);
                    w[s]
                }
                Gate::Xor(x, y) => wires[x as usize] + wires[y as usize],
                Gate::And(x, y, s) => {
                    let s = s as usize;
                    (ra[s], rb[s]) = (wires[x as usize], wires[y as usize]);
                    w[s]
                }
                Gate::Copy(x, s) => {
                    let s = s as usize;
                    (ra[s], rb[s]) = (wires[x as usize], wc);
                    w[s]
                }
            };
            wires.push(v);
        }
        (ra, rb)
    }
}

impl LincheckCircuit for U64Circuit {
    fn n_cols(&self) -> usize {
        1 << self.k_log
    }

    fn const_pin_col(&self) -> usize {
        self.const_pos
    }

    /// `(A_0 + α B_0)ᵀ u`, by one backward walk: every gate, in reverse, hands
    /// its wire's adjoint to its operands or deposits it on its slot.
    fn fold_alpha_batched(&self, alpha: F192, u: &[F192]) -> Vec<F192> {
        assert_eq!(u.len(), self.n_cols());
        let c = self.const_pos;
        let mut m = vec![F192::ZERO; u.len()];
        let mut adj = vec![F192::ZERO; self.gates.len()];
        for (i, &gate) in self.gates.iter().enumerate().rev() {
            let g = adj[i];
            match gate {
                Gate::Free(s) => {
                    let s = s as usize;
                    m[s] += g + u[s];
                    m[c] += alpha * u[s];
                }
                Gate::Xor(x, y) => {
                    adj[x as usize] += g;
                    adj[y as usize] += g;
                }
                Gate::And(x, y, s) => {
                    let s = s as usize;
                    m[s] += g;
                    adj[x as usize] += u[s];
                    adj[y as usize] += alpha * u[s];
                }
                Gate::Copy(x, s) => {
                    let s = s as usize;
                    m[s] += g;
                    adj[x as usize] += u[s];
                    m[c] += alpha * u[s];
                }
            }
        }
        m
    }

    fn bilinear_form(&self, alpha: F192, u: &[F192], w: &[F192]) -> Option<F192> {
        let (ra, rb) = self.row_values(w);
        Some(
            u.iter()
                .zip(ra.iter().zip(&rb))
                .fold(F192::ZERO, |acc, (&u, (&a, &b))| acc + u * (a + alpha * b)),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fiat_shamir::transcript::{ProverState, VerifierState};
    use primitives::test_rng::Rng;

    const OPS: [U64Op; 3] = [U64Op::WrappingAdd, U64Op::WrappingMul, U64Op::WideningMul];

    fn native(op: U64Op, a: u64, b: u64) -> u128 {
        let (a, b) = (a as u128, b as u128);
        match op {
            U64Op::WrappingAdd => (a + b) as u64 as u128,
            U64Op::WrappingMul => (a * b) as u64 as u128,
            U64Op::WideningMul => a * b,
        }
    }

    /// Every pairing of the carry-heavy edge values, then random pairs.
    fn pairs(n: usize, seed: u64) -> Vec<(u64, u64)> {
        const EDGES: [u64; 6] = [0, 1, 2, 1 << 63, u64::MAX - 1, u64::MAX];
        let mut rng = Rng::new(seed);
        EDGES
            .iter()
            .flat_map(|&x| EDGES.iter().map(move |&y| (x, y)))
            .chain(std::iter::repeat_with(|| (rng.next_u64(), rng.next_u64())))
            .take(n)
            .collect()
    }

    /// The committed result is the native one and every row holds, which ties
    /// the word-level witness to the gate list the walks read.
    #[test]
    fn witness_is_the_result_and_satisfies_r1cs() {
        let n_log = 6;
        for op in OPS {
            let circuit = U64Circuit::new(op);
            let k = circuit.n_cols();
            let pairs = pairs(1 << n_log, 0x3A11);
            let (z, _, _, _) = circuit.generate_witness(&pairs, n_log);
            for (t, &(x, y)) in pairs.iter().enumerate() {
                let word = |w: usize| z[t * (k / 64) + w];
                let out = (word(2) as u128 | (word(3) as u128) << 64) & (u128::MAX >> (128 - op.out_bits()));
                assert_eq!((word(0), word(1), out), (x, y, native(op, x, y)), "{op:?}");
                let block: Vec<F192> = (0..k)
                    .map(|i| {
                        if (z[(t * k + i) / 64] >> (i % 64)) & 1 == 1 {
                            F192::ONE
                        } else {
                            F192::ZERO
                        }
                    })
                    .collect();
                let (ra, rb) = circuit.row_values(&block);
                assert!((0..k).all(|i| ra[i] * rb[i] == block[i]), "{op:?} ({x}, {y})");
            }
        }
    }

    /// The reduction verifies an honest batch, which is also what ties the
    /// prover's backward walk and the `A·z`, `B·z` tables to the verifier's
    /// forward walk, and rejects one flipped witness bit.
    #[test]
    fn reduction_roundtrip_rejects_tampering() {
        const LABEL: &[u8] = b"flock-arith-reduction-test";
        // The zerocheck needs a cube of at least 2^13 bits.
        let n_log = 5;
        for op in OPS {
            let circuit = U64Circuit::new(op);
            let block = circuit.block();
            let pairs = pairs(1 << n_log, 0x3A12);
            let run = |tamper: Option<usize>| {
                let (mut z, a, b, mut z_lincheck) = circuit.generate_witness(&pairs, n_log);
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
            assert!(run(None), "{op:?}");
            for bit in [A_BASE + 3, OUT_BASE + 5, circuit.const_pos, circuit.useful_bits - 1] {
                assert!(!run(Some(bit)), "{op:?}: flipping bit {bit} must reject");
            }
        }
    }
}
