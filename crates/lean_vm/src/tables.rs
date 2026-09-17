//! Per-instruction tables (`doc/leanvm/body/07-instruction-tables.tex`). Each opcode is one [`Table`] impl that declares,
//! in one place, its committed columns, how to fill them from the trace, its bus
//! interactions (flushes), the read-count columns that feed the count channel,
//! and its degree-2 constraints. Column indices here are *local* (`0..n_committed_columns`);
//! `cpu`'s schema offsets them to global witness columns.
//!
//! Every column is `K`-valued (`F64`), and so is every memory cell. Nothing
//! a row DERIVES is a column at all: an operand address `fp·o`, an arithmetic
//! result, the `DEREF` store, the `JUMP` successors are each written out as the
//! degree-2 bus coordinate that carries them (§sec:m3). What a table does commit
//! per memory access is the argument that orders it in time (§sec:memchan): the
//! timestamp `X` of the cell's previous access and the two chunks of the gap to
//! the row's own, each a read of a range array. After the round a table joins the
//! batch its columns are `E`-valued, which is what `eval_constraint` takes.

use crate::colval::ColVal;
use crate::cpu::{Access, Brow, Drow, Jrow, Op, Srow, Trace};
use crate::leaf::Coord::{self, Col, Const, GCol, Prod};
use primitives::field::{F64, F192, mul_by_g};

// ---- the identities ----------------------------------------------------------
//
// Each is written ONCE, generic over the column type: `F64` in the round a table
// joins the batch, `F192` afterwards (see [`ColVal`]). Products of two `K`
// columns stay 64-bit and an `η`-power multiplies through `mul_e`.

/// `JUMP`'s two identities: `b = cond·w` and `cond·(b+1) = 0` (§sec:tab-jump).
///
/// The two relations together force `b = [cond ≠ 0]`: when `cond ≠ 0` the second
/// gives `b = 1` (and the first `w = cond⁻¹`); when `cond = 0` the first gives
/// `b = 0`. The two selections need no identity: the state push carries each as its
/// own degree-2 coordinate (§sec:m3).
fn jump_identity<T: ColVal>(pows: &[F192], cols: &[T], quadratic: bool) -> F192 {
    use jump::*;
    let (b, b1) = if quadratic {
        (T::ZERO, cols[B])
    } else {
        (cols[B], cols[B] + T::ONE)
    };
    T::dot(pows, &[b + cols[V_COND] * cols[W], cols[V_COND] * b1], F192::ZERO)
}

/// Every access's `X·LO = g^{slot}·TS·HI` (§sec:memchan), folded: `w` is
/// [`access_weights`], the identities' `η`-powers then the same times `g^{slot}`,
/// so the clock factors out of the second half. Homogeneous of degree two, so the
/// round coefficient and the value are the same expression.
fn access_identities<T: ColVal>(w: &[F192], cols: &[T], ts: usize, acc: Acc) -> F192 {
    let n = acc.n;
    let left = (0..n).fold(T::lift(F192::ZERO), |sum, i| {
        sum ^ (cols[acc.x(i)] * cols[acc.lo(i)]).mul_e_unreduced(w[i])
    });
    let hi = T::dot(&w[n..2 * n], &cols[acc.hi(0)..acc.hi(0) + n], F192::ZERO);
    T::reduce(left ^ T::lift(cols[ts].mul_e(hi)))
}

/// [`access_identities`]' weights from the `n` identities' `η`-powers.
fn access_weights(pows: &[F192], slots: &[u32]) -> Vec<F192> {
    assert_eq!(pows.len(), slots.len());
    let shifted = pows.iter().zip(slots).map(|(p, &s)| p.mul_base(g_pow(s as usize)));
    pows.iter().copied().chain(shifted).collect()
}

// ---- shared bus vocabulary ---------------------------------------------------

/// `g^k` at compile time (`g = x`, so repeated `mul_by_g` from `g^0 = 1`).
const fn g_pow(k: usize) -> F64 {
    let mut acc = F64::ONE;
    let mut i = 0;
    while i < k {
        acc = mul_by_g(acc);
        i += 1;
    }
    acc
}

// Domain separators (coordinate 0 of every bus tuple): the g-powers g^0 .. g^4.
pub(crate) const SEP_STATE: F64 = g_pow(0);
pub(crate) const SEP_MEM: F64 = g_pow(1);
pub(crate) const SEP_BYTECODE: F64 = g_pow(2);
pub(crate) const SEP_RANGE_LO: F64 = g_pow(3);
pub(crate) const SEP_RANGE_HI: F64 = g_pow(4);

/// Each range array holds `2^RANGE_LOG` entries, so a gap is below `2^(2·RANGE_LOG)`.
pub const RANGE_LOG: usize = 16;

/// The clock advances by this much per instruction, which leaves one timestamp per
/// access slot: `ts = 4·cycle + slot` (§sec:memchan).
pub const CLOCK_STRIDE: u32 = 4;
/// `BLAKE2S` touches eighteen cells, so it takes five cycles' worth of clock.
pub const BLAKE2S_STRIDE: u32 = 20;
/// The clock the run starts on: cycle 1, so the first access is strictly after the
/// memory seed's `g^0`.
pub const CLOCK_START: F64 = g_pow(CLOCK_STRIDE as usize);

/// The low range array's addresses `g^{j+1}`: the `+1` is the strictness of `x < y`.
pub fn range_lo_first() -> F64 {
    F64::G
}
/// The high range array's addresses are the powers of `g^{-2^16}`, from `g^0`.
pub fn range_hi_ratio() -> F64 {
    static RATIO: std::sync::OnceLock<F64> = std::sync::OnceLock::new();
    *RATIO.get_or_init(|| primitives::field::g_pow(1 << RANGE_LOG).inv())
}

// Opcodes (coordinate 3 of a bytecode tuple): `g^t` for table `t` of [`tables`].
pub(crate) const OP_XOR64: F64 = g_pow(0);
pub(crate) const OP_MUL64: F64 = g_pow(1);
pub(crate) const OP_SET: F64 = g_pow(2);
pub(crate) const OP_DEREF: F64 = g_pow(3);
pub(crate) const OP_JUMP: F64 = g_pow(4);
pub(crate) const OP_BLAKE2S: F64 = g_pow(5);

/// Where a table keeps its `n` accesses' columns, grouped by kind so that each
/// kind is contiguous: the previous timestamps `X`, the gap's low and high chunks,
/// then the two range reads' counts.
#[derive(Clone, Copy)]
pub(crate) struct Acc {
    base: usize,
    n: usize,
}

impl Acc {
    const fn new(base: usize, n: usize) -> Self {
        Self { base, n }
    }
    const fn x(&self, i: usize) -> usize {
        self.base + i
    }
    const fn lo(&self, i: usize) -> usize {
        self.base + self.n + i
    }
    const fn hi(&self, i: usize) -> usize {
        self.base + 2 * self.n + i
    }
    const fn count_lo(&self, i: usize) -> usize {
        self.base + 3 * self.n + i
    }
    const fn count_hi(&self, i: usize) -> usize {
        self.base + 4 * self.n + i
    }
    const fn end(&self) -> usize {
        self.base + 5 * self.n
    }
}

/// A table's count columns, in column order: its accesses' range counts, low chunks
/// then high, then its bytecode count.
const fn count_columns<const M: usize>(acc: Acc, rbc: usize) -> [usize; M] {
    assert!(M == 2 * acc.n + 1);
    let mut out = [rbc; M];
    let mut i = 0;
    while i < 2 * acc.n {
        out[i] = acc.count_lo(0) + i;
        i += 1;
    }
    out
}

// ---- flush builder -----------------------------------------------------------

/// Collects a table's push/pull bus interactions in *local* column indices.
pub struct FlushBuilder {
    pub(crate) push: Vec<Vec<Coord>>,
    pub(crate) pull: Vec<Vec<Coord>>,
}

impl FlushBuilder {
    pub(crate) fn new() -> Self {
        Self {
            push: Vec::new(),
            pull: Vec::new(),
        }
    }

    fn pair(&mut self, push: Vec<Coord>, pull: Vec<Coord>) {
        self.push.push(push);
        self.pull.push(pull);
    }

    /// Fall-through state step: the next pc is `g·pc`, fp unchanged, the clock
    /// advanced by `stride`.
    pub(crate) fn state_step(&mut self, pc: usize, fp: usize, ts: usize, stride: u32) {
        self.state_derived(pc, fp, ts, stride, GCol(pc, 1), Col(fp));
    }

    /// Explicit state transition (JUMP): push the next state, which the row
    /// DERIVES from its columns rather than committing, and pull `(pc, fp, ts)`.
    pub(crate) fn state_derived(&mut self, pc: usize, fp: usize, ts: usize, stride: u32, npc: Coord, nfp: Coord) {
        self.pair(
            vec![Const(SEP_STATE), npc, nfp, GCol(ts, stride)],
            vec![Const(SEP_STATE), Col(pc), Col(fp), Col(ts)],
        );
    }

    /// Bytecode read at `pc`: the program tuple (opcode + seven operand slots),
    /// with the per-pc execution count advanced by ×g on the push side.
    pub(crate) fn bytecode(&mut self, pc: usize, count: usize, opcode: F64, operands: &[Coord]) {
        let mut push = vec![Const(SEP_BYTECODE), Col(pc), GCol(count, 1), Const(opcode)];
        let mut pull = vec![Const(SEP_BYTECODE), Col(pc), Col(count), Const(opcode)];
        push.extend_from_slice(operands);
        pull.extend_from_slice(operands);
        self.pair(push, pull);
    }

    /// Access `i` of the row, at clock slot `slot` (§sec:memchan): pull the cell as
    /// its previous access left it, `(X, old)`, push it back as `(g^{slot}·ts, new)`,
    /// and read the gap's two chunks off the range arrays. A value the row DERIVES
    /// rather than commits is passed as its form (§sec:m3).
    pub(crate) fn memory(&mut self, addr: Coord, ts: usize, acc: Acc, i: usize, slot: u32, old: Coord, new: Coord) {
        self.pair(
            vec![Const(SEP_MEM), addr.clone(), GCol(ts, slot), new],
            vec![Const(SEP_MEM), addr, Col(acc.x(i)), old],
        );
        for (sep, chunk, count) in [
            (SEP_RANGE_LO, acc.lo(i), acc.count_lo(i)),
            (SEP_RANGE_HI, acc.hi(i), acc.count_hi(i)),
        ] {
            self.pair(
                vec![Const(sep), Col(chunk), GCol(count, 1)],
                vec![Const(sep), Col(chunk), Col(count)],
            );
        }
    }

    /// A read: [`Self::memory`] leaving the value as it was.
    pub(crate) fn read(&mut self, addr: Coord, ts: usize, acc: Acc, i: usize, slot: u32, val: Coord) {
        self.memory(addr, ts, acc, i, slot, val.clone(), val);
    }
}

// ---- fill context ------------------------------------------------------------

/// Inputs a table needs to fill its columns: the trace rows and the g-power
/// tables for O(1) address, operand and gap-chunk lookups.
pub struct FillCtx<'a> {
    pub(crate) trace: &'a Trace,
    pub(crate) gpow: &'a [F64],
    /// The two range arrays' addresses, by chunk.
    pub(crate) range_lo: &'a [F64],
    pub(crate) range_hi: &'a [F64],
    pub(crate) prog: &'a [Op],
    /// This table's height `2^tau`, the length of every window in `out`, and its row
    /// count too (`cpu::filler`).
    pub(crate) rows: usize,
    /// Which local columns [`Self::col`] / [`Self::cols`] have written. A fill that
    /// misses one would leave the stacked witness holding uninitialized slots, so
    /// [`fill_table`] checks the whole set was covered.
    written: Vec<std::sync::atomic::AtomicBool>,
}

/// Where one column's values go: its window in the stacked witness, or a private
/// buffer if the column is virtual.
pub type ColumnOut<'a> = &'a mut [F64];

impl<'a> FillCtx<'a> {
    pub(crate) fn new(
        trace: &'a Trace,
        gpow: &'a [F64],
        range_lo: &'a [F64],
        range_hi: &'a [F64],
        prog: &'a [Op],
        rows: usize,
        n_cols: usize,
    ) -> Self {
        Self {
            trace,
            gpow,
            range_lo,
            range_hi,
            prog,
            rows,
            written: (0..n_cols).map(|_| false.into()).collect(),
        }
    }

    fn g_at(&self, i: u32) -> F64 {
        self.gpow[i as usize]
    }

    /// The three frame offsets of an arithmetic row, read back from the bytecode
    /// rather than copied into every row (§the trace rows in `cpu::trace`).
    fn ternary_operands(&self, pc: u32) -> (u32, u32, u32) {
        match self.prog[pc as usize] {
            Op::Xor64 { a, b, c } | Op::Mul64 { a, b, c } => (a, b, c),
            op => unreachable!("a three-operand row's pc {pc} holds {op:?}"),
        }
    }

    /// Write local column `at`: `f` over the trace rows.
    fn col<R: Sync>(&self, out: &mut [ColumnOut], rows: &[R], at: usize, f: impl Fn(&R) -> F64 + Sync) {
        self.cols(out, rows, at, |r| [f(r)]);
    }

    /// Write the `N` local columns at `at..at + N` from one closure per row.
    /// Columns fed by the same bytecode decode fill together: splitting them
    /// across `N` passes pays for the decode `N` times.
    fn cols<const N: usize, R: Sync>(
        &self,
        out: &mut [ColumnOut],
        rows: &[R],
        at: usize,
        f: impl Fn(&R) -> [F64; N] + Sync,
    ) {
        self.cols_at(out, rows.len(), at, |i| f(&rows[i]));
    }

    /// The `5·N` columns of a table's accesses.
    fn accesses<const N: usize, R: Sync>(
        &self,
        out: &mut [ColumnOut],
        rows: &[R],
        acc: Acc,
        f: impl Fn(&R) -> &[Access; N] + Sync,
    ) {
        assert_eq!(acc.n, N);
        let mask = (1u32 << RANGE_LOG) - 1;
        self.cols(out, rows, acc.x(0), |r| f(r).map(|a| a.x));
        self.cols(out, rows, acc.lo(0), |r| {
            f(r).map(|a| self.range_lo[(a.gap & mask) as usize])
        });
        self.cols(out, rows, acc.hi(0), |r| {
            f(r).map(|a| self.range_hi[(a.gap >> RANGE_LOG) as usize])
        });
        self.cols(out, rows, acc.count_lo(0), |r| f(r).map(|a| a.count_lo));
        self.cols(out, rows, acc.count_hi(0), |r| f(r).map(|a| a.count_hi));
    }

    /// [`Self::cols`] over row indices, for values held in a side buffer rather
    /// than read off the row.
    fn cols_at<const N: usize>(
        &self,
        out: &mut [ColumnOut],
        n_rows: usize,
        at: usize,
        f: impl Fn(usize) -> [F64; N] + Sync,
    ) {
        let n = self.rows;
        let dst: [parallel::SendPtr<F64>; N] = std::array::from_fn(|k| {
            assert_eq!(out[at + k].len(), n, "column {} has the wrong window length", at + k);
            self.written[at + k].store(true, std::sync::atomic::Ordering::Relaxed);
            parallel::SendPtr(out[at + k].as_mut_ptr())
        });
        // A table's height is its row count (`cpu::filler`), so there is nothing to
        // pad with.
        assert_eq!(n_rows, n, "a table's rows must fill its cube");
        parallel::for_each(n, |i| {
            let v = f(i);
            for (k, p) in dst.iter().enumerate() {
                // SAFETY: distinct `i` write disjoint in-bounds slots of each of the
                // `N` windows, each exactly once, and the dispatch blocks until
                // every write is finished.
                unsafe { p.add(i).write(v[k]) };
            }
        });
    }
}

/// Fill one table's columns and check that every window was written. The stack is
/// allocated uninitialized, so a column the table forgot would be read as
/// indeterminate bytes rather than caught by a length mismatch.
pub(crate) fn fill_table(table: &dyn Table, ctx: &FillCtx, out: &mut [ColumnOut]) {
    table.fill(ctx, out);
    assert_eq!(ctx.written.len(), table.n_committed_columns());
    let all = ctx.written.iter().all(|w| w.load(std::sync::atomic::Ordering::Relaxed));
    assert!(all, "a table left one of its columns unwritten");
}

// ---- the trait ---------------------------------------------------------------

/// One instruction table. Indices in [`flushes`](Table::flushes) and
/// [`count_columns`](Table::count_columns) are local to this table.
pub trait Table: Sync {
    /// Number of committed columns (local indices `0..n_committed_columns`).
    fn n_committed_columns(&self) -> usize;
    /// Local indices of this table's read-count columns: the `g^{count}` values of
    /// its lookups into the read-only arrays (the bytecode, the two range arrays).
    /// The framework treats them specially: each gets its own single-column "count"
    /// bus block.
    fn count_columns(&self) -> &'static [usize];
    /// How many identities [`eval_constraint`](Table::eval_constraint) folds.
    /// Sizes this table's slice of the batch's disjoint `xi`-range (§constraints).
    fn n_constraints(&self) -> usize;
    /// What [`eval_constraint`](Table::eval_constraint) is handed, from this table's
    /// slice of the batch's `xi`-powers: the powers themselves, plus whatever
    /// constant multiples of them the identities need, computed once per proof
    /// rather than per row.
    fn constraint_weights(&self, pows: &[F192]) -> Vec<F192>;
    /// Evaluate the table's degree-2 constraints at one row, reading column values
    /// by local index from `cols` and weighting them by `weights`
    /// ([`constraint_weights`](Table::constraint_weights)). The table sumcheck
    /// carries every committed column of a table, in local order, so `cols` is
    /// indexed directly. With `quadratic=false` it returns `0` on every valid row
    /// (§sec:air); `true` selects only the degree-two terms.
    fn eval_constraint(&self, weights: &[F192], cols: &[F192], quadratic: bool) -> F192;
    /// The same identity over `K`-valued columns, for the round a table joins the
    /// batch, before its columns have been folded into `E` (§sec:air). Both entry
    /// points delegate to one generic definition per table, so they cannot drift.
    fn eval_constraint_k(&self, weights: &[F192], cols: &[F64], quadratic: bool) -> F192;
    /// Declare the table's bus interactions.
    fn flushes(&self, f: &mut FlushBuilder);
    /// Fill this table's columns from the trace: `out[i]` is local column `i`'s
    /// window, already at its final length. Every window must be written in full;
    /// use `FillCtx::col` / `FillCtx::cols`, which record the coverage `fill_table`
    /// checks.
    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]);
}

/// The tables in fixed order `[XOR64, MUL64, SET, DEREF, JUMP, BLAKE2S]`, the order of `row_counts` / `taus` throughout `cpu`. Table `t`'s
/// opcode is `g^t`.
pub const N_TABLES: usize = 6;

pub fn tables() -> [&'static dyn Table; N_TABLES] {
    [
        &Arith64 { is_xor: true },
        &Arith64 { is_xor: false },
        &SetTable,
        &DerefTable,
        &JumpTable,
        &Blake2sTable,
    ]
}

/// Index of the BLAKE2s table in [`tables`].
pub(crate) const BLAKE2S_TABLE: usize = 5;

/// The eighteen cells a `BLAKE2s` row touches, in value-lane order: the four message
/// chunks' two cells each, the digest's four, the chaining value's four and the
/// metadata's two. Recovered from the instruction, not stored per row.
pub(crate) fn blake2s_cells(prog: &[Op], pc: u32, fp: u32) -> [u32; 18] {
    match prog[pc as usize] {
        Op::Blake2s { ins, cv, out, md } => {
            let [m0, m1, m2, m3] = ins.map(|o| fp + o);
            let (cv, out, md) = (fp + cv, fp + out, fp + md);
            [
                m0,
                m0 + 1,
                m1,
                m1 + 1,
                m2,
                m2 + 1,
                m3,
                m3 + 1,
                out,
                out + 1,
                out + 2,
                out + 3,
                cv,
                cv + 1,
                cv + 2,
                cv + 3,
                md,
                md + 1,
            ]
        }
        op => unreachable!("a BLAKE2s row's pc {pc} holds {op:?}"),
    }
}

/// The clock slot of each `BLAKE2s` value lane: the fourteen reads (message,
/// chaining value, metadata) come before the four digest writes, so a digest may
/// land on a cell the same row read.
pub(crate) const BLAKE2S_SLOTS: [u32; 18] = {
    let mut slots = [0; 18];
    let mut lane = 0;
    while lane < 18 {
        slots[lane] = match lane {
            0..8 => lane as u32,      // message: 0..8
            8..12 => lane as u32 + 6, // digest: 14..18
            _ => lane as u32 - 4,     // chaining value 8..12, metadata 12..14
        };
        lane += 1;
    }
    slots
};

/// The value lanes in clock-slot order: the order the machine touches them in.
pub(crate) const BLAKE2S_LANES_BY_SLOT: [usize; 18] = {
    let mut lanes = [0; 18];
    let mut lane = 0;
    while lane < 18 {
        lanes[BLAKE2S_SLOTS[lane] as usize] = lane;
        lane += 1;
    }
    lanes
};

/// BLAKE2s value-column LOCAL indices in canonical slot order
/// `[a0..a3, b0..b3, c0..c3, cv0..cv3, md_lo, md_hi]` (matches
/// `hash_flock::SLOTS`). These columns are VIRTUAL (never committed): `q_flock`
/// already holds those words at fixed packed slots, so `cpu` routes their
/// memory-bus evaluation claims straight to `q_flock` (`slot_claims`): the value the
/// bus flushes IS the flock-proven word.
pub const BLAKE2S_VALUE_COLS: [usize; 18] = {
    let mut cols = [0; 18];
    let mut i = 0;
    while i < 18 {
        cols[i] = blake2st::V0 + i;
        i += 1;
    }
    cols
};

// ---- XOR64 / MUL64 -----------------------------------------------------------

/// `XOR64` and `MUL64` share their column layout, flushes, and fill; they differ
/// only in the opcode tag and in the value written to the destination cell
/// (`v_A + v_B` or `v_A·v_B`), which rides the bus as a form rather than a column
/// (§sec:m3).
struct Arith64 {
    is_xor: bool,
}

mod arith64 {
    use super::Acc;
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const OA: usize = 2;
    pub const OB: usize = 3;
    pub const OC: usize = 4;
    pub const VA: usize = 5;
    pub const VB: usize = 6;
    // What the destination held before the write.
    pub const VC_OLD: usize = 7;
    pub const TS: usize = 8;
    pub const ACC: Acc = Acc::new(9, 3);
    pub const RBC: usize = ACC.end();
    pub const N: usize = RBC + 1;
    pub const SLOTS: [u32; 3] = [0, 1, 2];
}

impl Arith64 {
    fn eval<T: ColVal>(w: &[F192], cols: &[T]) -> F192 {
        access_identities(w, cols, arith64::TS, arith64::ACC)
    }
}

impl Table for Arith64 {
    fn n_committed_columns(&self) -> usize {
        arith64::N
    }
    fn count_columns(&self) -> &'static [usize] {
        const COUNTS: [usize; 7] = count_columns(arith64::ACC, arith64::RBC);
        &COUNTS
    }
    fn n_constraints(&self) -> usize {
        3
    }
    fn constraint_weights(&self, pows: &[F192]) -> Vec<F192> {
        access_weights(pows, &arith64::SLOTS)
    }
    fn eval_constraint(&self, w: &[F192], cols: &[F192], _quadratic: bool) -> F192 {
        Self::eval(w, cols)
    }
    fn eval_constraint_k(&self, w: &[F192], cols: &[F64], _quadratic: bool) -> F192 {
        Self::eval(w, cols)
    }
    fn flushes(&self, f: &mut FlushBuilder) {
        use arith64::*;
        f.state_step(PC, FP, TS, CLOCK_STRIDE);
        f.bytecode(
            PC,
            RBC,
            if self.is_xor { OP_XOR64 } else { OP_MUL64 },
            &[Col(OA), Col(OB), Col(OC), Const(F64::ZERO), Const(F64::ZERO)],
        );
        f.read(Prod(FP, OA, 0), TS, ACC, 0, SLOTS[0], Col(VA));
        f.read(Prod(FP, OB, 0), TS, ACC, 1, SLOTS[1], Col(VB));
        let result = if self.is_xor {
            Coord::Sum(vec![Col(VA), Col(VB)])
        } else {
            Prod(VA, VB, 0)
        };
        f.memory(Prod(FP, OC, 0), TS, ACC, 2, SLOTS[2], Col(VC_OLD), result);
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]) {
        use arith64::*;
        let rows = if self.is_xor {
            &ctx.trace.xor64
        } else {
            &ctx.trace.mul64
        };
        ctx.col(out, rows, PC, |r| ctx.g_at(r.pc));
        ctx.col(out, rows, FP, |r| ctx.g_at(r.fp));
        ctx.cols(out, rows, OA, |r| {
            let (a, b, c) = ctx.ternary_operands(r.pc);
            [ctx.g_at(a), ctx.g_at(b), ctx.g_at(c), r.va, r.vb, r.vc_old, r.ts]
        });
        ctx.accesses(out, rows, ACC, |r| &r.acc);
        ctx.col(out, rows, RBC, |r| r.bytecode_read);
    }
}

// ---- SET ---------------------------------------------------------------------

struct SetTable;

mod set {
    use super::Acc;
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const O: usize = 2;
    // The stored immediate rides the bytecode's second operand slot.
    pub const K: usize = 3;
    pub const V_OLD: usize = 4;
    pub const TS: usize = 5;
    pub const ACC: Acc = Acc::new(6, 1);
    pub const RBC: usize = ACC.end();
    pub const N: usize = RBC + 1;
    pub const SLOTS: [u32; 1] = [0];
}

impl SetTable {
    fn eval<T: ColVal>(w: &[F192], cols: &[T]) -> F192 {
        access_identities(w, cols, set::TS, set::ACC)
    }
}

impl Table for SetTable {
    fn n_committed_columns(&self) -> usize {
        set::N
    }
    fn count_columns(&self) -> &'static [usize] {
        const COUNTS: [usize; 3] = count_columns(set::ACC, set::RBC);
        &COUNTS
    }
    fn n_constraints(&self) -> usize {
        1
    }
    fn constraint_weights(&self, pows: &[F192]) -> Vec<F192> {
        access_weights(pows, &set::SLOTS)
    }
    fn eval_constraint(&self, w: &[F192], cols: &[F192], _quadratic: bool) -> F192 {
        Self::eval(w, cols)
    }
    fn eval_constraint_k(&self, w: &[F192], cols: &[F64], _quadratic: bool) -> F192 {
        Self::eval(w, cols)
    }
    fn flushes(&self, f: &mut FlushBuilder) {
        use set::*;
        f.state_step(PC, FP, TS, CLOCK_STRIDE);
        f.bytecode(
            PC,
            RBC,
            OP_SET,
            &[Col(O), Col(K), Const(F64::ZERO), Const(F64::ZERO), Const(F64::ZERO)],
        );
        f.memory(Prod(FP, O, 0), TS, ACC, 0, SLOTS[0], Col(V_OLD), Col(K));
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]) {
        use set::*;
        let rows = &ctx.trace.set;
        let imm = |r: &Srow| match ctx.prog[r.pc as usize] {
            Op::Set { o, k } => (o, k),
            op => unreachable!("a SET row's pc {} holds {op:?}", r.pc),
        };
        ctx.col(out, rows, PC, |r| ctx.g_at(r.pc));
        ctx.col(out, rows, FP, |r| ctx.g_at(r.fp));
        ctx.cols(out, rows, O, |r| {
            let (o, k) = imm(r);
            [ctx.g_at(o), k, r.v_old, r.ts]
        });
        ctx.accesses(out, rows, ACC, |r| &r.acc);
        ctx.col(out, rows, RBC, |r| r.bytecode_read);
    }
}

// ---- DEREF -------------------------------------------------------------------

struct DerefTable;

mod deref {
    use super::Acc;
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const O1: usize = 2;
    pub const O2: usize = 3;
    pub const O3: usize = 4;
    pub const FPC: usize = 5;
    pub const FFP: usize = 6;
    // The pointer, which forms the pointer-relative address `p·o2` on the bus.
    pub const P: usize = 7;
    // The local cell. The stored word is DERIVED from it, the two flags, `pc` and
    // `fp`, so it is no column.
    pub const V3: usize = 8;
    // What the store target held before the write.
    pub const V2_OLD: usize = 9;
    pub const TS: usize = 10;
    /// Pointer, local cell, store target: the two reads before the write.
    pub const ACC: Acc = Acc::new(11, 3);
    pub const RBC: usize = ACC.end();
    pub const N: usize = RBC + 1;
    pub const SLOTS: [u32; 3] = [0, 1, 2];
}

/// The stored word as a form: `v_2 = (1+f_pc+f_fp)·v_3 + f_pc·(g²·pc) + f_fp·fp`, the
/// flag-selected source of §sec:tab-deref. The `pc` source is the virtual return
/// target `g²·pc`, a free `×g²` on the product coordinate.
fn deref_store() -> Coord {
    use deref::*;
    Coord::Sum(vec![
        Col(V3),
        Prod(FPC, V3, 0),
        Prod(FFP, V3, 0),
        Prod(FPC, PC, 2),
        Prod(FFP, FP, 0),
    ])
}

impl DerefTable {
    fn eval<T: ColVal>(w: &[F192], cols: &[T]) -> F192 {
        access_identities(w, cols, deref::TS, deref::ACC)
    }
}

impl Table for DerefTable {
    fn n_committed_columns(&self) -> usize {
        deref::N
    }
    fn count_columns(&self) -> &'static [usize] {
        const COUNTS: [usize; 7] = count_columns(deref::ACC, deref::RBC);
        &COUNTS
    }
    fn n_constraints(&self) -> usize {
        3
    }
    fn constraint_weights(&self, pows: &[F192]) -> Vec<F192> {
        access_weights(pows, &deref::SLOTS)
    }
    fn eval_constraint(&self, w: &[F192], cols: &[F192], _quadratic: bool) -> F192 {
        Self::eval(w, cols)
    }
    fn eval_constraint_k(&self, w: &[F192], cols: &[F64], _quadratic: bool) -> F192 {
        Self::eval(w, cols)
    }
    fn flushes(&self, f: &mut FlushBuilder) {
        use deref::*;
        f.state_step(PC, FP, TS, CLOCK_STRIDE);
        f.bytecode(PC, RBC, OP_DEREF, &[Col(O1), Col(O2), Col(O3), Col(FPC), Col(FFP)]);
        // The pointer cell and the local cell are frame-relative reads; the store
        // target is pointer-relative, so its address is `p·o2`, and what it is
        // written with is the flag-selected source rather than a column.
        f.read(Prod(FP, O1, 0), TS, ACC, 0, SLOTS[0], Col(P));
        f.read(Prod(FP, O3, 0), TS, ACC, 1, SLOTS[1], Col(V3));
        f.memory(Prod(P, O2, 0), TS, ACC, 2, SLOTS[2], Col(V2_OLD), deref_store());
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]) {
        use deref::*;
        let rows = &ctx.trace.deref;
        let ins = |r: &Drow| match ctx.prog[r.pc as usize] {
            Op::Deref { o1, o2, o3, mode } => (o1, o2, o3, mode),
            op => unreachable!("a DEREF row's pc {} holds {op:?}", r.pc),
        };
        ctx.col(out, rows, PC, |r| ctx.g_at(r.pc));
        ctx.col(out, rows, FP, |r| ctx.g_at(r.fp));
        // The three offsets and the two mode flags follow from ONE bytecode decode.
        ctx.cols(out, rows, O1, |r| {
            let (o1, o2, o3, mode) = ins(r);
            [
                ctx.g_at(o1),
                ctx.g_at(o2),
                ctx.g_at(o3),
                mode.f_pc(),
                mode.f_fp(),
                r.p,
                r.v3,
                r.v2_old,
                r.ts,
            ]
        });
        ctx.accesses(out, rows, ACC, |r| &r.acc);
        ctx.col(out, rows, RBC, |r| r.bytecode_read);
    }
}

// ---- JUMP --------------------------------------------------------------------

struct JumpTable;

mod jump {
    use super::Acc;
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const OC: usize = 2;
    pub const OD: usize = 3;
    pub const OF: usize = 4;
    pub const V_COND: usize = 5;
    pub const V_PC: usize = 6;
    pub const V_FP: usize = 7;
    pub const TS: usize = 8;
    // Local witness columns (committed, never flushed): the inverse hint `w = c⁻¹`
    // and the taken indicator `b = [c ≠ 0]` it certifies.
    pub const W: usize = 9;
    pub const B: usize = 10;
    pub const ACC: Acc = Acc::new(11, 3);
    pub const RBC: usize = ACC.end();
    pub const N: usize = RBC + 1;
    pub const SLOTS: [u32; 3] = [0, 1, 2];
}

impl JumpTable {
    /// The two indicator identities, then the three accesses'.
    fn eval<T: ColVal>(w: &[F192], cols: &[T], quadratic: bool) -> F192 {
        jump_identity(&w[..2], cols, quadratic) + access_identities(&w[2..], cols, jump::TS, jump::ACC)
    }
}

impl Table for JumpTable {
    fn n_committed_columns(&self) -> usize {
        jump::N
    }
    fn count_columns(&self) -> &'static [usize] {
        const COUNTS: [usize; 7] = count_columns(jump::ACC, jump::RBC);
        &COUNTS
    }
    fn n_constraints(&self) -> usize {
        5 // the two indicator identities (the selections ride the state push), then one per access
    }
    fn constraint_weights(&self, pows: &[F192]) -> Vec<F192> {
        let mut w = pows[..2].to_vec();
        w.extend(access_weights(&pows[2..], &jump::SLOTS));
        w
    }
    fn eval_constraint(&self, w: &[F192], cols: &[F192], quadratic: bool) -> F192 {
        Self::eval(w, cols, quadratic)
    }
    fn eval_constraint_k(&self, w: &[F192], cols: &[F64], quadratic: bool) -> F192 {
        Self::eval(w, cols, quadratic)
    }
    fn flushes(&self, f: &mut FlushBuilder) {
        use jump::*;
        // The successor state is DERIVED: `b·d + (b+1)·g·pc` and `b·f + (b+1)·fp`,
        // each degree 2 in K columns, so neither successor is committed. Written
        // out in characteristic 2 as `b·d + b·(g·pc) + g·pc`.
        f.state_derived(
            PC,
            FP,
            TS,
            CLOCK_STRIDE,
            Coord::Sum(vec![Prod(B, V_PC, 0), Prod(B, PC, 1), GCol(PC, 1)]),
            Coord::Sum(vec![Prod(B, V_FP, 0), Prod(B, FP, 0), Col(FP)]),
        );
        f.bytecode(
            PC,
            RBC,
            OP_JUMP,
            &[Col(OC), Col(OD), Col(OF), Const(F64::ZERO), Const(F64::ZERO)],
        );
        f.read(Prod(FP, OC, 0), TS, ACC, 0, SLOTS[0], Col(V_COND));
        f.read(Prod(FP, OD, 0), TS, ACC, 1, SLOTS[1], Col(V_PC));
        f.read(Prod(FP, OF, 0), TS, ACC, 2, SLOTS[2], Col(V_FP));
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]) {
        use jump::*;
        let rows = &ctx.trace.jump;
        let ins = |r: &Jrow| match ctx.prog[r.pc as usize] {
            Op::Jump { oc, od, of } => (oc, od, of),
            op => unreachable!("a JUMP row's pc {} holds {op:?}", r.pc),
        };
        ctx.col(out, rows, PC, |r| ctx.g_at(r.pc));
        ctx.col(out, rows, FP, |r| ctx.g_at(r.fp));
        ctx.cols(out, rows, OC, |r| {
            let (oc, od, of) = ins(r);
            [ctx.g_at(oc), ctx.g_at(od), ctx.g_at(of), r.cond, r.dest, r.frame, r.ts]
        });
        // The is-nonzero witness `w = c⁻¹` (0 where c = 0) for every row, in one
        // batched Montgomery inversion. `prefix[i]` is the running product of the
        // nonzero conditions before row `i`, so `acc` ends as their full product
        // (nonzero, hence invertible). The taken indicator `b = [c ≠ 0]` falls out
        // of the same pass.
        let (w, b) = {
            let mut acc = F64::ONE;
            let mut prefix: Vec<F64> = Vec::with_capacity(rows.len());
            let mut b = vec![F64::ZERO; rows.len()];
            for (i, r) in rows.iter().enumerate() {
                prefix.push(acc);
                if !r.cond.is_zero() {
                    acc *= r.cond;
                    b[i] = F64::ONE;
                }
            }
            let mut inv = acc.inv();
            let mut w = vec![F64::ZERO; rows.len()];
            for (i, r) in rows.iter().enumerate().rev() {
                if !r.cond.is_zero() {
                    w[i] = inv * prefix[i];
                    inv *= r.cond;
                }
            }
            (w, b)
        };
        ctx.cols_at(out, rows.len(), W, |i| [w[i], b[i]]);
        ctx.accesses(out, rows, ACC, |r| &r.acc);
        ctx.col(out, rows, RBC, |r| r.bytecode_read);
    }
}

// ---- BLAKE2s ------------------------------------------------------------------

/// `BLAKE2s` (§sec:tab-blake2s): one standard compression. The four 128-bit message
/// chunks are addressed *independently* at `fp·o_i`, each spanning that cell and its
/// successor, so a caller hashing e.g. `(tweak, pp)` need not copy them into
/// adjacent cells. The digest and the chaining value span four consecutive cells,
/// the metadata two, so the row touches eighteen cells: fourteen reads, then the
/// four digest writes. No address is committed: each rides the bus as the product
/// `fp·o·g^k` (§sec:m3). The compression relating output words to input words is
/// proven by flock's R1CS via `q_flock` (§hash_flock).
///
/// The eighteen cells are eighteen value columns. They are listed in
/// `n_committed_columns` (they need a local index for the flushes and are filled
/// from the trace for the bus), but `cpu` treats them as VIRTUAL (not committed) and
/// routes their bus claims to `q_flock`, which already holds those words (see
/// [`BLAKE2S_VALUE_COLS`]).
struct Blake2sTable;

pub(crate) mod blake2st {
    use super::Acc;
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const O_M0: usize = 2; // operand g-powers of the four message chunks …
    pub const O_CV: usize = 6; // … the chaining value …
    pub const O_OUT: usize = 7; // … the digest …
    pub const O_MD: usize = 8; // … and the metadata.
    // The eighteen value lanes, one per cell: the message chunks' eight, then the
    // digest's four, the chaining value's four and the metadata's counter and flags.
    pub const V0: usize = 9;
    // What the four digest cells held before the write.
    pub const OUT_OLD: usize = 27;
    pub const TS: usize = 31;
    /// One access per value lane, in the same order.
    pub const ACC: Acc = Acc::new(32, 18);
    pub const RBC: usize = ACC.end();
    pub const N: usize = RBC + 1;
    /// The digest's first value lane.
    pub const OUT_LANE: usize = 8;
}

/// The operand and the offset from it of each value lane's cell, in lane order.
const BLAKE2S_LANE_CELLS: [(usize, u32); 18] = {
    use blake2st::*;
    let mut cells = [(0, 0); 18];
    let mut i = 0;
    while i < 18 {
        cells[i] = match i {
            0..8 => (O_M0 + i / 2, (i % 2) as u32),
            8..12 => (O_OUT, (i - 8) as u32),
            12..16 => (O_CV, (i - 12) as u32),
            _ => (O_MD, (i - 16) as u32),
        };
        i += 1;
    }
    cells
};

impl Blake2sTable {
    fn eval<T: ColVal>(w: &[F192], cols: &[T]) -> F192 {
        access_identities(w, cols, blake2st::TS, blake2st::ACC)
    }
}

impl Table for Blake2sTable {
    fn n_committed_columns(&self) -> usize {
        blake2st::N
    }
    fn count_columns(&self) -> &'static [usize] {
        const COUNTS: [usize; 37] = count_columns(blake2st::ACC, blake2st::RBC);
        &COUNTS
    }
    fn n_constraints(&self) -> usize {
        18
    }
    fn constraint_weights(&self, pows: &[F192]) -> Vec<F192> {
        access_weights(pows, &BLAKE2S_SLOTS)
    }
    fn eval_constraint(&self, w: &[F192], cols: &[F192], _quadratic: bool) -> F192 {
        Self::eval(w, cols)
    }
    fn eval_constraint_k(&self, w: &[F192], cols: &[F64], _quadratic: bool) -> F192 {
        Self::eval(w, cols)
    }
    fn flushes(&self, f: &mut FlushBuilder) {
        use blake2st::*;
        f.state_step(PC, FP, TS, BLAKE2S_STRIDE);
        f.bytecode(PC, RBC, OP_BLAKE2S, &std::array::from_fn::<_, 7, _>(|i| Col(O_M0 + i)));
        // A successor cell is a free ×g^k on the address product. The metadata rides
        // the memory bus like every other operand: the read is what binds flock's
        // counter and flag inputs.
        for (lane, &(operand, k)) in BLAKE2S_LANE_CELLS.iter().enumerate() {
            let old = match lane.checked_sub(OUT_LANE) {
                Some(i) if i < 4 => Col(OUT_OLD + i),
                _ => Col(V0 + lane),
            };
            f.memory(
                Prod(FP, operand, k),
                TS,
                ACC,
                lane,
                BLAKE2S_SLOTS[lane],
                old,
                Col(V0 + lane),
            );
        }
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]) {
        use blake2st::*;
        let rows = &ctx.trace.blake2s;
        ctx.col(out, rows, PC, |r| ctx.g_at(r.pc));
        ctx.col(out, rows, FP, |r| ctx.g_at(r.fp));
        ctx.cols(out, rows, O_M0, |r: &Brow| match ctx.prog[r.pc as usize] {
            Op::Blake2s { ins, cv, out, md } => [ins[0], ins[1], ins[2], ins[3], cv, out, md].map(|o| ctx.g_at(o)),
            op => unreachable!("a BLAKE2s row's pc {} holds {op:?}", r.pc),
        });
        ctx.cols(out, rows, V0, |r| r.w);
        ctx.cols(out, rows, OUT_OLD, |r| r.out_old);
        ctx.col(out, rows, TS, |r| r.ts);
        ctx.accesses(out, rows, ACC, |r| &r.acc);
        ctx.col(out, rows, RBC, |r| r.bytecode_read);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::field::powers;

    /// `JUMP`'s two identities vanish on an honest row, taken or not, and reject a
    /// wrong indicator or, for a taken jump, an inverse that is not `cond⁻¹`.
    #[test]
    fn jump_identities_bind_indicator_and_inverse() {
        let pows = powers(F192::new(0x9e37_79b9_7f4a_7c15, 0x1234_5678_9abc_def0, 7), 2);
        for cond in [F64::ZERO, F64(0x9e37_79b9_7f4a_7c15)] {
            let mut row = vec![F64::ZERO; jump::N];
            let w = if cond.is_zero() { F64::ZERO } else { cond.inv() };
            row[jump::V_COND] = cond;
            row[jump::W] = w;
            row[jump::B] = if cond.is_zero() { F64::ZERO } else { F64::ONE };
            assert_eq!(jump_identity(&pows, &row, false), F192::ZERO, "cond = {cond:?}");
            // On a zero condition the inverse is unconstrained, being multiplied by
            // zero: what has to be pinned there is the indicator alone.
            let forgeable: &[usize] = if cond.is_zero() {
                &[jump::B]
            } else {
                &[jump::B, jump::W]
            };
            for &col in forgeable {
                let mut forged = row.clone();
                forged[col] += F64::ONE;
                assert_ne!(
                    jump_identity(&pows, &forged, false),
                    F192::ZERO,
                    "column {col}, cond = {cond:?}"
                );
            }
        }
    }

    /// An access's identity holds exactly when the gap its two chunks spell is the
    /// distance from the previous timestamp to the access's own, less one: the
    /// strict `x < y`, over both column fields.
    #[test]
    fn access_identity_is_the_strict_gap() {
        use primitives::field::g_pow;
        let (x, cycle, slot) = (41usize, 70_000usize, 2usize);
        let gap = CLOCK_STRIDE as usize * cycle + slot - x - 1;
        assert!(gap >> RANGE_LOG > 0, "both chunks are exercised");
        let w = access_weights(&powers(F192::new(3, 5, 7), 3), &arith64::SLOTS);
        let row = |gap: usize| {
            // Accesses 0 and 1 stay all-zero, which the identity accepts.
            let mut row = vec![F64::ZERO; arith64::N];
            row[arith64::TS] = g_pow(CLOCK_STRIDE as usize * cycle);
            row[arith64::ACC.x(slot)] = g_pow(x);
            row[arith64::ACC.lo(slot)] = range_lo_first() * g_pow(gap & 0xffff);
            row[arith64::ACC.hi(slot)] = (0..gap >> RANGE_LOG).fold(F64::ONE, |h, _| h * range_hi_ratio());
            row
        };
        assert_eq!(Arith64::eval(&w, &row(gap)), F192::ZERO);
        let lifted: Vec<F192> = row(gap).into_iter().map(F192::from).collect();
        assert_eq!(Arith64::eval(&w, &lifted), F192::ZERO);
        assert_ne!(Arith64::eval(&w, &row(gap + 1)), F192::ZERO);
        assert_ne!(Arith64::eval(&w, &row(gap + (1 << RANGE_LOG))), F192::ZERO);
    }
}
