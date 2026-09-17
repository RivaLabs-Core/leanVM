//! Bridge to flock's u64 circuits ([`flock::arith`]): `ADD_U64` and `MUL_U64`.
//!
//! Each operation has its own packed witness, committed as one more column of the
//! stacked witness, exactly as `q_flock` is for BLAKE2s ([`crate::hash_flock`]):
//! instance `j` of the batch is row `j` of the instruction's table, and flock's
//! R1CS validity is discharged by the same stacked WHIR opening, through one more
//! ring-switched region.
//!
//! A memory word is 64 bits and the packing is 64 bits a word, so the three words
//! an instruction touches ARE three packed words of its instance: `a` at slot 0,
//! `b` at slot 1, the result at slot 2 ([`SLOTS`]). The table's three value
//! columns are therefore virtual, their claims routed to those slots.

use crate::transcript::{ProverState, VerifierState};
use ::pcs::pack::LOG_PACKING;
use flock::arith::{A_BASE, B_BASE, OUT_BASE, U64Circuit, U64Op};
use flock::reduction::{ReductionReplay, SliceClaim};
use flock::verifier::VerifyError;
use primitives::field::F64;
use std::sync::OnceLock;
use zk_alloc::ArenaVec;

/// The two operations the VM proves through flock.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Op {
    Add,
    Mul,
}

/// The within-instance packed words of `a`, `b` and the result.
pub const SLOTS: [usize; 3] = [A_BASE / 64, B_BASE / 64, OUT_BASE / 64];

/// The zerocheck's cube has at least this many variables (flock's univariate skip
/// plus its fixed-point dimensions), which floors the batch of a small circuit.
const MIN_CUBE_LOG: usize = 13;

impl Op {
    /// `log2` of the bits one instance occupies. A constant, because the layout
    /// needs it before any circuit is built; [`Self::circuit`] checks it.
    pub const fn k_log(self) -> usize {
        match self {
            Self::Add => 8,
            Self::Mul => 12,
        }
    }

    /// `log2` of an instance's packed words: the stride between consecutive
    /// instances' same-slot words, as [`crate::hash_flock::SLOT_STRIDE_LOG`] is.
    pub const fn stride_log(self) -> usize {
        self.k_log() - LOG_PACKING
    }

    /// The operation on two memory words, read as unsigned integers.
    pub fn apply(self, a: F64, b: F64) -> F64 {
        F64(match self {
            Self::Add => a.0.wrapping_add(b.0),
            Self::Mul => a.0.wrapping_mul(b.0),
        })
    }

    /// The gate list, built once: the multiplier's is tens of thousands of gates.
    pub fn circuit(self) -> &'static U64Circuit {
        static CIRCUITS: [OnceLock<U64Circuit>; 2] = [OnceLock::new(), OnceLock::new()];
        let (slot, op) = match self {
            Self::Add => (0, U64Op::WrappingAdd),
            Self::Mul => (1, U64Op::WrappingMul),
        };
        CIRCUITS[slot].get_or_init(|| {
            let circuit = U64Circuit::new(op);
            assert_eq!(circuit.k_log(), self.k_log(), "{self:?}'s block size moved");
            circuit
        })
    }
}

/// `log2` of the batch proving `n_rows` instances: a power of two, at least flock's
/// stripe floor and at least what the zerocheck's cube needs.
pub const fn n_blocks_log(op: Op, n_rows: usize) -> usize {
    let natural = min_n_blocks_log_const(n_rows);
    let floor = MIN_CUBE_LOG.saturating_sub(op.k_log());
    if natural > floor { natural } else { floor }
}

/// [`flock::reduction::min_n_blocks_log`], at compile time.
const fn min_n_blocks_log_const(n_blocks: usize) -> usize {
    let n = if n_blocks > 8 { n_blocks } else { 8 };
    n.next_power_of_two().trailing_zeros() as usize
}

/// The flock-native tables of one operation's batch, kept from the pass that wrote
/// its committed column so the reduction needs no second witness pass.
pub(crate) struct Prepared {
    op: Op,
    n_blocks_log: usize,
    z: ArenaVec<u64>,
    a: ArenaVec<u64>,
    b: ArenaVec<u64>,
    z_lincheck: ArenaVec<u8>,
}

impl Prepared {
    /// Build the batch for `pairs`, one instance per table row, and write its packed
    /// witness into `window`, the operation's committed column.
    pub(crate) fn build(op: Op, pairs: &[(u64, u64)], window: &mut [F64]) -> Self {
        let n_blocks_log = n_blocks_log(op, pairs.len());
        assert_eq!(
            pairs.len(),
            1 << n_blocks_log,
            "a table's rows fill its batch (cpu::filler)"
        );
        let (z, a, b, z_lincheck) = op.circuit().generate_witness(pairs, n_blocks_log);
        assert_eq!(window.len(), z.len(), "the committed column is the wrong size");
        // `F64` is `repr(transparent)` over `u64`, and the packing is bit `i` at
        // position `i` on both sides.
        parallel::chunks_mut_zip(window, &z, 1 << 14, |_, dst, src| {
            for (d, &s) in dst.iter_mut().zip(src) {
                *d = F64(s);
            }
        });
        Self {
            op,
            n_blocks_log,
            z,
            a,
            b,
            z_lincheck,
        }
    }

    /// Flock's zerocheck then lincheck, leaving the one claim on the committed column.
    pub(crate) fn prove(&self, ps: &mut ProverState) -> SliceClaim {
        let block = self.op.circuit().block();
        let stage = block.prove_zerocheck(self.n_blocks_log, &self.z, &self.a, &self.b, ps);
        block.prove_lincheck(self.n_blocks_log, stage, &self.z_lincheck, ps)
    }
}

/// The verifier's replay of the reduction: zerocheck, then lincheck.
pub fn verify_reduction(op: Op, n_blocks_log: usize, vs: &mut VerifierState) -> Result<ReductionReplay, VerifyError> {
    op.circuit().block().verify(n_blocks_log, vs)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The constants the layout is built from are the circuits' own, and the three
    /// words a row touches are whole packed words of its instance.
    #[test]
    fn layout_constants_match_the_circuits() {
        for op in [Op::Add, Op::Mul] {
            assert_eq!(op.circuit().k_log(), op.k_log());
            assert!(op.k_log() + n_blocks_log(op, 1) >= MIN_CUBE_LOG);
        }
        assert_eq!(SLOTS, [0, 1, 2]);
        assert_eq!(n_blocks_log(Op::Add, 1), 5);
        assert_eq!(n_blocks_log(Op::Mul, 1), 3);
        assert_eq!(n_blocks_log(Op::Mul, 9), 4);
    }

    /// The committed column holds each instance's `a`, `b` and result at [`SLOTS`].
    #[test]
    fn committed_words_are_the_operands_and_the_result() {
        for op in [Op::Add, Op::Mul] {
            let n = 1usize << n_blocks_log(op, 1);
            let pairs: Vec<(u64, u64)> = (0..n as u64)
                .map(|i| (u64::MAX - 3 * i, 0x9e37_79b9_7f4a_7c15u64.wrapping_mul(i + 1)))
                .collect();
            let mut window = vec![F64::ZERO; n << op.stride_log()];
            Prepared::build(op, &pairs, &mut window);
            for (j, &(a, b)) in pairs.iter().enumerate() {
                let word = |slot: usize| window[(j << op.stride_log()) + slot];
                assert_eq!(
                    [word(SLOTS[0]), word(SLOTS[1]), word(SLOTS[2])],
                    [F64(a), F64(b), op.apply(F64(a), F64(b))],
                    "{op:?}"
                );
            }
        }
    }
}
