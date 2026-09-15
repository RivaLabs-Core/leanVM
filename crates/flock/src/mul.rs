//! u64 multiplication as a Flock R1CS, one product per block: the wrapping
//! `a·b mod 2^64` ([`MulKind::Wrapping`]) or the full `a·b` as a u128
//! ([`MulKind::Widening`]).
//!
//! ## Partial products are free
//!
//! A schoolbook multiplier pays one product per partial product `a_i·b_j`, then
//! one per carry to sum them. Over GF(2) the first half is avoidable: with
//! `e_ij = ¬(a_i ⊕ b_j)`, `2·a_i·b_j = a_i + b_j − 1 + e_ij`. Summed, with
//! `M = 2^64 − 1` and `¬a = M − a` the 64-bit complement,
//!
//! ```text
//!   2ab = Σ_i (a_i ? b : ¬b)·2^i + ¬a + ¬b + (a + b)·2^64 + 1 − 2^128
//! ```
//!
//! Every row there is affine in the inputs. Its column 0,
//! `¬(a_0 ⊕ b_0) + ¬a_0 + ¬b_0 + 1`, is `2 + 2g` with `g = ¬a_0·¬b_0`, so after
//! that one product the identity halves: `a·b mod 2^N` is `1 + g` plus the other
//! columns shifted down a place. That is 66 rows of affine bits, with `1` and
//! `g` in the empty low bits of two of them.
//!
//! ## Compression
//!
//! A carry-save step turns three rows into their XOR and their majority shifted
//! up a place. The majority `(x ⊕ z)(y ⊕ z) ⊕ z` is one product at each position
//! where at least two rows have a bit, except where exactly two do and the carry
//! row is still free there: one of the two bits moves into it instead. Taking
//! the three rows that end lowest each time, the 64 steps cost as few products
//! as summing column by column, and a ripple-carry addition finishes the last
//! two rows. The top position's majority would carry out of the modulus, so it
//! is never a product.
//!
//! Every step is word arithmetic on `u128` rows and its products are one run of
//! slots, so an instance's witness is a few shifts and masks per step.
//!
//! ## Witness layout per block
//!
//! ```text
//!   z[0         .. 64)        = a             (free input)
//!   z[64        .. 128)       = b             (free input)
//!   z[128       .. 128 + N)   = a·b mod 2^N   (committed copies)
//!   z[128 + N]                = 1             (constant wire)
//!   z[129 + N   .. useful)    = g, then each step's products
//!   z[useful    .. 2^k_log)   = padding (forced to 0 by empty rows)
//! ```
//!
//! As in [`crate::hash`], no matrix is ever built. The steps also build one gate
//! list, walked forwards for the verifier and backwards for the prover
//! (doc/leanvm, Annex C "Evaluating the matrices").

use crate::lincheck::LincheckCircuit;
use crate::reduction::Block;
use crate::witness::{drive_witness_packed_and_lincheck, or_bit_at};
use primitives::field::F192;
use zk_alloc::ArenaVec;

pub const A_BASE: usize = 0;
pub const B_BASE: usize = 64;
pub const OUT_BASE: usize = 128;

/// The rows `(a_i ? b : ¬b)` for `i < 64`, then the `a` and `b` rows.
const N_ROWS: usize = 66;
const A_ROW: usize = 64;
const B_ROW: usize = 65;

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

/// One carry-save step: rows `x`, `y`, `z` become the sum row, stored in `x`,
/// and the carry row, stored in `y`.
#[derive(Clone, Copy)]
struct Csa {
    x: usize,
    y: usize,
    z: usize,
    /// Positions whose majority is a product, one run of slots from `slot`.
    products: u128,
    /// Positions where the pair's `y` (or `z`) bit moves to the carry row.
    move_y: u128,
    move_z: u128,
    slot: usize,
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
}

/// A row's `(highest, lowest)` position.
fn ends(row: u128) -> (u32, u32) {
    (127 - row.leading_zeros(), row.trailing_zeros())
}

fn is_run(mask: u128) -> bool {
    let run = mask.checked_shr(mask.trailing_zeros()).unwrap_or(0);
    run & run.wrapping_add(1) == 0
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

pub struct MulCircuit {
    gates: Vec<Gate>,
    steps: Vec<Csa>,
    /// The two rows the steps leave, and where adding them makes a product.
    last: (usize, usize),
    carries: u128,
    carry_slot: usize,
    /// Positions below `N`.
    width: u128,
    const_pos: usize,
    k_log: usize,
    useful_bits: usize,
}

impl MulCircuit {
    pub fn new(kind: MulKind) -> Self {
        let n = kind.out_bits();
        let width = u128::MAX >> (128 - n);
        let const_pos = OUT_BASE + n;
        let mut c = Builder {
            gates: Vec::new(),
            next_slot: const_pos + 1,
        };
        let one = Some(c.push(Gate::Free(const_pos as u32)));
        let a: [_; 64] = std::array::from_fn(|i| Some(c.push(Gate::Free((A_BASE + i) as u32))));
        let b: [_; 64] = std::array::from_fn(|i| Some(c.push(Gate::Free((B_BASE + i) as u32))));
        let not_a: [_; 64] = std::array::from_fn(|i| c.xor(a[i], one));
        let not_b: [_; 64] = std::array::from_fn(|i| c.xor(b[i], one));
        let g = Some(c.and(not_a[0], not_b[0]));

        // Each row's wire per position, all shifted down a place: row 0's bit 0
        // is what `g` and the constant 1 replace.
        let mut rows = vec![vec![None; n]; N_ROWS];
        for i in 0..64usize {
            for j in 0..64 {
                if let Some(p) = (i + j).checked_sub(1).filter(|&p| p < n) {
                    rows[i][p] = c.xor(b[j], not_a[i]);
                }
            }
        }
        // `(¬a ≫ 1) + a·2^63`, and the same for `b`.
        for (row, low, high) in [(A_ROW, not_a, a), (B_ROW, not_b, b)] {
            let len = 64.min(n - 63);
            rows[row][..63].copy_from_slice(&low[1..]);
            rows[row][63..63 + len].copy_from_slice(&high[..len]);
        }
        rows[2][0] = one;
        rows[3][0] = g;
        // Half of the constant `2^128`, which survives only mod `2^128`.
        if n == 128 {
            rows[A_ROW][127] = one;
        }
        let mut present: Vec<u128> = rows
            .iter()
            .map(|row| (0..n).filter(|&p| row[p].is_some()).fold(0, |m, p| m | (1 << p)))
            .collect();

        let mut live: Vec<usize> = (0..N_ROWS).collect();
        let mut steps = Vec::new();
        while live.len() > 2 {
            let mut order: Vec<usize> = (0..live.len()).collect();
            order.sort_by_key(|&t| ends(present[live[t]]));
            let [x, y, z] = [live[order[0]], live[order[1]], live[order[2]]];
            live.retain(|r| ![x, y, z].contains(r));
            live.extend([x, y]);

            let (px, py, pz) = (present[x], present[y], present[z]);
            let pairs = ((px & py) | (px & pz) | (py & pz)) & (width >> 1);
            let triples = px & py & pz;
            let (mut products, mut moves) = (0u128, 0u128);
            for p in (0..n - 1).filter(|&p| (pairs >> p) & 1 == 1) {
                // The carry row is free at `p` unless `p − 1` has a product.
                if (triples >> p) & 1 == 0 && (products << 1) >> p & 1 == 0 {
                    moves |= 1 << p;
                } else {
                    products |= 1 << p;
                }
            }
            assert!(is_run(products), "a step's products must be one run of slots");
            let step = Csa {
                x,
                y,
                z,
                products,
                move_y: moves & !pz,
                move_z: moves & pz,
                slot: c.next_slot,
            };

            let (mut sum, mut carry) = (vec![None; n], vec![None; n]);
            for p in 0..n {
                let (wx, wy, wz) = (rows[x][p], rows[y][p], rows[z][p]);
                if (products >> p) & 1 == 1 {
                    let xz = c.xor(wx, wz);
                    let yz = c.xor(wy, wz);
                    let maj = c.and(xz, yz);
                    carry[p + 1] = c.xor(Some(maj), wz);
                    sum[p] = c.xor(xz, wy);
                } else if (step.move_z >> p) & 1 == 1 {
                    carry[p] = wz;
                    sum[p] = c.xor(wx, wy);
                } else if (step.move_y >> p) & 1 == 1 {
                    carry[p] = wy;
                    sum[p] = wx;
                } else {
                    let xz = c.xor(wx, wz);
                    sum[p] = c.xor(xz, wy);
                }
            }
            rows[x] = sum;
            rows[y] = carry;
            present[x] = px | py | pz;
            present[y] = (products << 1) | moves;
            steps.push(step);
        }

        let &[x, y] = live.as_slice() else {
            unreachable!("the steps stop at two rows")
        };
        let carry_slot = c.next_slot;
        let mut carries = 0u128;
        let mut carry = None;
        for p in 0..n {
            let (wx, wy) = (rows[x][p], rows[y][p]);
            let out = if p + 1 < n && [wx, wy, carry].iter().flatten().count() >= 2 {
                carries |= 1 << p;
                let xc = c.xor(wx, carry);
                let yc = c.xor(wy, carry);
                let maj = c.and(xc, yc);
                carry = c.xor(Some(maj), carry);
                c.xor(xc, wy)
            } else {
                let xy = c.xor(wx, wy);
                c.xor(xy, carry.take())
            };
            c.push(Gate::Copy(
                out.expect("every output bit has a wire"),
                (OUT_BASE + p) as u32,
            ));
        }
        assert!(is_run(carries), "the final carries must be one run of slots");

        let useful_bits = c.next_slot;
        Self {
            gates: c.gates,
            steps,
            last: (x, y),
            carries,
            carry_slot,
            width,
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
    pub fn generate_witness(
        &self,
        pairs: &[(u64, u64)],
        n_blocks_log: usize,
    ) -> (ArenaVec<u64>, ArenaVec<u64>, ArenaVec<u64>, ArenaVec<u8>) {
        drive_witness_packed_and_lincheck(pairs, Some(&(0, 0)), n_blocks_log, self.k_log, |&(a, b), z, az, bz| {
            self.block_witness(a, b, z, az, bz)
        })
    }

    /// One instance: its rows run through the steps as words, each step's
    /// products written as one bit field.
    fn block_witness(&self, a: u64, b: u64, z: &mut [u64], az: &mut [u64], bz: &mut [u64]) {
        let (na, nb) = (!a, !b);
        let mut rows = [0u128; N_ROWS];
        for (i, row) in rows[..64].iter_mut().enumerate() {
            let v = (b ^ ((a >> i) & 1).wrapping_sub(1)) as u128;
            *row = if i == 0 { v >> 1 } else { v << (i - 1) };
        }
        rows[A_ROW] = ((na >> 1) as u128) | ((a as u128) << 63) | (1 << 127);
        rows[B_ROW] = ((nb >> 1) as u128) | ((b as u128) << 63);
        rows[2] |= 1;
        rows[3] |= (na & nb & 1) as u128;
        for row in &mut rows {
            *row &= self.width;
        }

        for (base, v) in [(A_BASE, a), (B_BASE, b)] {
            (z[base / 64], az[base / 64], bz[base / 64]) = (v, v, !0);
        }
        for buf in [&mut *z, &mut *az, &mut *bz] {
            or_bit_at(buf, self.const_pos);
        }
        let mut write = |slot: usize, mask: u128, left: u128, right: u128| {
            if mask != 0 {
                let shift = mask.trailing_zeros();
                or_bits(z, slot, (left & right & mask) >> shift);
                or_bits(az, slot, (left & mask) >> shift);
                or_bits(bz, slot, (right & mask) >> shift);
            }
        };
        write(self.const_pos + 1, 1, na as u128, nb as u128);

        for s in &self.steps {
            let (rx, ry, rz) = (rows[s.x], rows[s.y], rows[s.z]);
            let (xz, yz) = (rx ^ rz, ry ^ rz);
            let moved = (ry & s.move_y) | (rz & s.move_z);
            rows[s.x] = rx ^ ry ^ rz ^ moved;
            rows[s.y] = ((((xz & yz) ^ rz) & s.products) << 1) | moved;
            write(s.slot, s.products, xz, yz);
        }

        let (rx, ry) = (rows[self.last.0], rows[self.last.1]);
        let sum = rx.wrapping_add(ry) & self.width;
        let carry_in = sum ^ rx ^ ry;
        write(self.carry_slot, self.carries, rx ^ carry_in, ry ^ carry_in);
        for w in 0..self.width.count_ones() as usize / 64 {
            let v = (sum >> (64 * w)) as u64;
            let i = OUT_BASE / 64 + w;
            (z[i], az[i], bz[i]) = (v, v, !0);
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

    /// The committed output is the native product and every row holds, which
    /// ties the word-level witness to the gate list the walks read.
    #[test]
    fn witness_is_the_product_and_satisfies_r1cs() {
        let n_log = 6;
        for kind in KINDS {
            let circuit = MulCircuit::new(kind);
            let k = circuit.n_cols();
            let pairs = pairs(1 << n_log, 0x3A11);
            let (z, _, _, _) = circuit.generate_witness(&pairs, n_log);
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
    /// prover's backward walk and the `A·z`, `B·z` tables to the verifier's
    /// forward walk, and rejects one flipped witness bit.
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
