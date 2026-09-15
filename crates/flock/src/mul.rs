//! u64 multiplication as a Flock R1CS, one product per block: the wrapping
//! `a·b mod 2^64` ([`MulKind::Wrapping`]) or the full `a·b` as a u128
//! ([`MulKind::Widening`]).
//!
//! ## Partial products are free
//!
//! A schoolbook multiplier pays one product per partial product `a_i·b_j`, then
//! one per carry to sum them. Over GF(2) the first half is avoidable: with
//! `e_ij = ¬(a_i ⊕ b_j)`, `2·a_i·b_j = a_i + b_j − 1 + e_ij`, so with
//! `M = 2^64 − 1`
//!
//! ```text
//!   2ab = Σ e_ij·2^(i+j) + (a + b)·M − M²
//!       = Σ e_ij·2^(i+j) + (a + b)·2^64 + ¬a + ¬b + 1 − 2^128
//! ```
//!
//! where `¬a = M − a` is the 64-bit complement. Every term is an affine bit at a
//! fixed column, so the product is a column sum of affine bits. For an `N`-bit
//! result it is taken mod `2^(N+1)`, whose bits `1..=N` are `a·b mod 2^N`.
//!
//! ## Compression
//!
//! Each column is summed by full adders, whose one row is the carry
//! `maj(x, y, z) = (x ⊕ z)(y ⊕ z) ⊕ z`, and by a half adder `x·y` when two bits
//! remain. Sums stay affine and uncommitted. The top column's carries fall off
//! the modulus, so it folds by XOR alone.
//!
//! ## Witness layout per block
//!
//! ```text
//!   z[0         .. 64)        = a             (free input)
//!   z[64        .. 128)       = b             (free input)
//!   z[128       .. 128 + N)   = a·b mod 2^N   (committed copies)
//!   z[128 + N]                = 1             (constant wire)
//!   z[129 + N   .. useful)    = adder products
//!   z[useful    .. 2^k_log)   = padding (forced to 0 by empty rows)
//! ```
//!
//! As in [`crate::hash`], no matrix is ever built. The circuit is one gate
//! list, walked forwards for the verifier, backwards for the prover, and over
//! bits for the witness (doc/leanvm, Annex C "Evaluating the matrices").

use crate::lincheck::LincheckCircuit;
use crate::reduction::Block;
use primitives::bits::{bit_transpose_64bytes, transpose_8_u64s_to_64_bytes};
use primitives::field::F192;
use zk_alloc::ArenaVec;

pub const A_BASE: usize = 0;
pub const B_BASE: usize = 64;
pub const OUT_BASE: usize = 128;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MulKind {
    /// `a·b mod 2^64`.
    Wrapping,
    /// `a·b` as a u128.
    Widening,
}

impl MulKind {
    pub const fn out_bits(self) -> usize {
        match self {
            Self::Wrapping => 64,
            Self::Widening => 128,
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
    /// Row `w_x · 1 = z[slot]`: an affine wire committed, which is how the product leaves the circuit.
    Copy(u32, u32),
}

struct Builder {
    gates: Vec<Gate>,
    next_slot: usize,
}

impl Builder {
    fn push(&mut self, gate: Gate) -> u32 {
        self.gates.push(gate);
        (self.gates.len() - 1) as u32
    }

    fn xor(&mut self, x: u32, y: u32) -> u32 {
        self.push(Gate::Xor(x, y))
    }

    fn and(&mut self, x: u32, y: u32) -> u32 {
        let slot = self.next_slot as u32;
        self.next_slot += 1;
        self.push(Gate::And(x, y, slot))
    }
}

pub struct MulCircuit {
    gates: Vec<Gate>,
    const_pos: usize,
    k_log: usize,
    useful_bits: usize,
}

impl MulCircuit {
    pub fn new(kind: MulKind) -> Self {
        let n = kind.out_bits();
        let const_pos = OUT_BASE + n;
        let mut c = Builder {
            gates: Vec::new(),
            next_slot: const_pos + 1,
        };
        let one = c.push(Gate::Free(const_pos as u32));
        let a: [u32; 64] = std::array::from_fn(|i| c.push(Gate::Free((A_BASE + i) as u32)));
        let b: [u32; 64] = std::array::from_fn(|i| c.push(Gate::Free((B_BASE + i) as u32)));

        // The affine bits of `2ab mod 2^(n+1)`, by column.
        let mut cols = vec![Vec::new(); n + 1];
        for i in 0..64 {
            for j in 0..64.min(n + 1 - i) {
                let x = c.xor(a[i], b[j]);
                cols[i + j].push(c.xor(x, one));
            }
            for x in [a[i], b[i]] {
                cols[i].push(c.xor(x, one));
                if 64 + i <= n {
                    cols[64 + i].push(x);
                }
            }
        }
        // The constant `1 − 2^128`, which is `1 + 2^128` mod `2^129`.
        for p in [0, 128] {
            if p <= n {
                cols[p].push(one);
            }
        }

        for p in 0..=n {
            let mut col = std::mem::take(&mut cols[p]);
            while col.len() > 1 {
                let (x, y) = (col.pop().unwrap(), col.pop().unwrap());
                if p == n {
                    col.push(c.xor(x, y));
                } else if let Some(z) = col.pop() {
                    let xz = c.xor(x, z);
                    let yz = c.xor(y, z);
                    let maj = c.and(xz, yz);
                    cols[p + 1].push(c.xor(maj, z));
                    col.push(c.xor(xz, y));
                } else {
                    cols[p + 1].push(c.and(x, y));
                    col.push(c.xor(x, y));
                }
            }
            // Column 0 is always zero, since `2ab` is even.
            if p > 0 {
                c.push(Gate::Copy(col[0], (OUT_BASE + p - 1) as u32));
            }
        }

        let useful_bits = c.next_slot;
        Self {
            gates: c.gates,
            const_pos,
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

    /// The matrix-vector products `(A_0 w, B_0 w)`, by one forward walk.
    pub fn row_values(&self, w: &[F192]) -> (Vec<F192>, Vec<F192>) {
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

    /// `(z, a, b, z_lincheck)` for `pairs` padded with `(0, 0)` to
    /// `2^n_blocks_log` instances: the bit-packed `z`, `A·z` and `B·z`
    /// (`2^k_log / 64` words per instance), and lincheck's byte stripes.
    ///
    /// The gates run on eight instances at once, one byte per wire with bit `t`
    /// for instance `t`. That is a stripe's own layout, so `z` lands in
    /// `z_lincheck` as it is computed and only the packed tables take a
    /// transpose.
    pub fn generate_witness(
        &self,
        pairs: &[(u64, u64)],
        n_blocks_log: usize,
    ) -> (ArenaVec<u64>, ArenaVec<u64>, ArenaVec<u64>, ArenaVec<u8>) {
        let k = self.n_cols();
        let words = k / 64;
        let n_total = 1usize << n_blocks_log;
        assert!(n_total >= 8, "lincheck stripes need at least 8 instances");
        assert!(pairs.len() <= n_total, "{} pairs exceed {n_total} slots", pairs.len());

        // SAFETY (x4): group `g` writes all of chunk `g` of every table: its
        // stripe is zeroed and then written, and `unstripe` stores every word.
        let mut z = unsafe { ArenaVec::<u64>::uninitialized(n_total * words) };
        let mut a = unsafe { ArenaVec::<u64>::uninitialized(n_total * words) };
        let mut b = unsafe { ArenaVec::<u64>::uninitialized(n_total * words) };
        let mut z_lincheck = unsafe { ArenaVec::<u8>::uninitialized(n_total / 8 * k) };
        let z_chunks = parallel::Chunks::new(&mut z, 8 * words);
        let a_chunks = parallel::Chunks::new(&mut a, 8 * words);
        let b_chunks = parallel::Chunks::new(&mut b, 8 * words);
        let stripes = parallel::Chunks::new(&mut z_lincheck, k);
        parallel::for_each_chunk(n_total / 8, |start, end| {
            let mut wires = Vec::with_capacity(self.gates.len());
            let mut az = vec![0u8; k];
            let mut bz = vec![0u8; k];
            for g in start..end {
                // SAFETY: group `g` takes chunk `g` of each table exactly once, and
                // all four tables stay borrowed for the whole dispatch.
                let (zg, ag, bg, stripe) =
                    unsafe { (z_chunks.get(g), a_chunks.get(g), b_chunks.get(g), stripes.get(g)) };
                let pair = |t: usize| pairs.get(8 * g + t).copied().unwrap_or((0, 0));
                let mut a_in = [0u8; 64];
                let mut b_in = [0u8; 64];
                transpose_8_u64s_to_64_bytes(&std::array::from_fn(|t| pair(t).0), &mut a_in);
                transpose_8_u64s_to_64_bytes(&std::array::from_fn(|t| pair(t).1), &mut b_in);
                self.eval8(&a_in, &b_in, &mut wires, stripe, &mut az, &mut bz);
                unstripe(stripe, zg);
                unstripe(&az, ag);
                unstripe(&bz, bg);
            }
        });
        (z, a, b, z_lincheck)
    }

    /// Run the gates on eight instances, writing each row's `z`, `A·z` and `B·z`
    /// bytes.
    fn eval8(&self, a_in: &[u8; 64], b_in: &[u8; 64], wires: &mut Vec<u8>, z: &mut [u8], az: &mut [u8], bz: &mut [u8]) {
        z.fill(0);
        az.fill(0);
        bz.fill(0);
        wires.clear();
        for &gate in &self.gates {
            let v = match gate {
                Gate::Free(s) => {
                    let s = s as usize;
                    let v = match s {
                        A_BASE..B_BASE => a_in[s - A_BASE],
                        B_BASE..OUT_BASE => b_in[s - B_BASE],
                        _ => 0xFF,
                    };
                    (z[s], az[s], bz[s]) = (v, v, 0xFF);
                    v
                }
                Gate::Xor(x, y) => wires[x as usize] ^ wires[y as usize],
                Gate::And(x, y, s) => {
                    let (l, r) = (wires[x as usize], wires[y as usize]);
                    let s = s as usize;
                    (z[s], az[s], bz[s]) = (l & r, l, r);
                    l & r
                }
                Gate::Copy(x, s) => {
                    let v = wires[x as usize];
                    let s = s as usize;
                    (z[s], az[s], bz[s]) = (v, v, 0xFF);
                    v
                }
            };
            wires.push(v);
        }
    }
}

/// Lay out a stripe (byte `j`, bit `t` = instance `t`'s bit `j`) as its eight
/// instances' packed words. The transpose cycles three index roles, so applying
/// it twice undoes the once `transpose_8_u64s_to_64_bytes` applies.
fn unstripe(stripe: &[u8], out: &mut [u64]) {
    let words = stripe.len() / 64;
    let mut once = [0u8; 64];
    let mut lanes = [0u8; 64];
    for (w, window) in stripe.as_chunks::<64>().0.iter().enumerate() {
        bit_transpose_64bytes(window, &mut once);
        bit_transpose_64bytes(&once, &mut lanes);
        for (t, lane) in lanes.as_chunks::<8>().0.iter().enumerate() {
            out[t * words + w] = u64::from_le_bytes(*lane);
        }
    }
}

impl LincheckCircuit for MulCircuit {
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

    const KINDS: [MulKind; 2] = [MulKind::Wrapping, MulKind::Widening];

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

    /// The committed output is the native product, every row holds, and the
    /// stripes are the packed witness transposed.
    #[test]
    fn witness_is_the_product_and_satisfies_r1cs() {
        let n_log = 6;
        for kind in KINDS {
            let circuit = MulCircuit::new(kind);
            let k = circuit.n_cols();
            let pairs = pairs(1 << n_log, 0x3A11);
            let (z, _, _, z_lincheck) = circuit.generate_witness(&pairs, n_log);
            assert_eq!(
                *z_lincheck,
                *crate::lincheck::pack_z_lincheck_from_packed(&z, circuit.k_log + n_log, circuit.k_log)
            );
            for (t, &(x, y)) in pairs.iter().enumerate() {
                let word = |w: usize| z[t * (k / 64) + w];
                let product = x as u128 * y as u128;
                assert_eq!((word(0), word(1), word(2)), (x, y, product as u64), "{kind:?}");
                if kind == MulKind::Widening {
                    assert_eq!(word(3), (product >> 64) as u64);
                }
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
                assert!((0..k).all(|i| ra[i] * rb[i] == block[i]), "{kind:?} ({x}, {y})");
            }
        }
    }

    /// The reduction verifies an honest batch, which is also what ties the
    /// prover's backward walk to the verifier's forward one, and rejects one
    /// flipped witness bit.
    #[test]
    fn reduction_roundtrip_rejects_tampering() {
        const LABEL: &[u8] = b"flock-mul-reduction-test";
        let n_log = 3;
        for kind in KINDS {
            let circuit = MulCircuit::new(kind);
            let block = circuit.block();
            let pairs = pairs(8, 0x3A12);
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
            assert!(run(None), "{kind:?}");
            for bit in [A_BASE + 3, OUT_BASE + 5, circuit.const_pos, circuit.useful_bits - 1] {
                assert!(!run(Some(bit)), "{kind:?}: flipping bit {bit} must reject");
            }
        }
    }
}
