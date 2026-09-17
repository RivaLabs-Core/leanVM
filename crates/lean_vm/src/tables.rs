//! Per-instruction tables (`doc/leanvm/body/07-instruction-tables.tex`). Each opcode is one [`Table`] impl that declares,
//! in one place, its committed columns, how to fill them from the trace, its bus
//! interactions (flushes), the read-count columns that feed the count channel,
//! and its degree-2 constraints. Column indices here are *local* (`0..n_committed_columns`);
//! `cpu`'s schema offsets them to global witness columns.
//!
//! Every column is `K`-valued (`F64`), and so is every memory cell. Little a row
//! DERIVES is a column: an arithmetic result, the `DEREF` store, the `JUMP`
//! successors are each written out as the degree-2 bus coordinate that carries them
//! (§sec:m3). What a table does commit per memory access is its address and the
//! argument that orders it in time. Addresses are integers, `fp + o`, and integer
//! addition is no field operation, so the address `A` is a column, tied to its two
//! terms by one read of the `EXP` array, whose entry `A` is `g^A`: the read's value
//! is the product `g^fp·g^o` (§sec:exp). Then (§sec:memchan) the timestamp `X` of
//! the cell's previous access and the two chunks of the gap to the row's own, each a
//! read of a range array. After the round a table joins the
//! batch its columns are `E`-valued, which is what `eval_constraint` takes.

use crate::arith_flock::Op as U64Op;
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

// Domain separators (coordinate 0 of every bus tuple): the g-powers g^0 .. g^5.
pub(crate) const SEP_STATE: F64 = g_pow(0);
pub(crate) const SEP_MEM: F64 = g_pow(1);
pub(crate) const SEP_BYTECODE: F64 = g_pow(2);
pub(crate) const SEP_RANGE_LO: F64 = g_pow(3);
pub(crate) const SEP_RANGE_HI: F64 = g_pow(4);
pub(crate) const SEP_EXP: F64 = g_pow(5);

/// Where a bytecode tuple carries the instruction's successor `pc + 1`, and, for a
/// `DEREF` storing its return address, `pc + 2`: past the opcode and the seven
/// operand slots (§sec:bytecode).
const BYTECODE_SUCC_SLOT: usize = 11;

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
pub(crate) const OP_ADD_U64: F64 = g_pow(6);
pub(crate) const OP_MUL_U64: F64 = g_pow(7);

/// Where a table keeps its `n` accesses' columns, grouped by kind so that each
/// kind is contiguous: the addresses `A`, the previous timestamps `X`, the gap's low
/// and high chunks, then the counts of the three reads (`EXP`, then the two range
/// arrays).
#[derive(Clone, Copy)]
pub(crate) struct Acc {
    base: usize,
    n: usize,
}

impl Acc {
    const fn new(base: usize, n: usize) -> Self {
        Self { base, n }
    }
    const fn a(&self, i: usize) -> usize {
        self.base + i
    }
    const fn x(&self, i: usize) -> usize {
        self.base + self.n + i
    }
    const fn lo(&self, i: usize) -> usize {
        self.base + 2 * self.n + i
    }
    const fn hi(&self, i: usize) -> usize {
        self.base + 3 * self.n + i
    }
    const fn count_exp(&self, i: usize) -> usize {
        self.base + 4 * self.n + i
    }
    const fn count_lo(&self, i: usize) -> usize {
        self.base + 5 * self.n + i
    }
    const fn count_hi(&self, i: usize) -> usize {
        self.base + 6 * self.n + i
    }
    const fn end(&self) -> usize {
        self.base + 7 * self.n
    }
}

/// A table's count columns, in column order: its accesses' three counts each (they
/// end `acc`), then whatever columns follow `acc`, which are counts up to the
/// bytecode's, the last.
const fn count_columns<const M: usize>(acc: Acc, rbc: usize) -> [usize; M] {
    assert!(M == rbc + 1 - acc.count_exp(0));
    let mut out = [0; M];
    let mut i = 0;
    while i < M {
        out[i] = acc.count_exp(0) + i;
        i += 1;
    }
    out
}

/// The columns every table starts with: the state it pulls, `pc`, the frame pointer
/// as the integer `fp` and as its g-power `fpx`, and the clock, then the successor
/// `npc = pc + 1` its bytecode read returns.
#[derive(Clone, Copy)]
pub(crate) struct State {
    pc: usize,
    fp: usize,
    fpx: usize,
    ts: usize,
    npc: usize,
}

/// Every table lays those five out first, in this order.
pub(crate) const STATE: State = State {
    pc: 0,
    fp: 1,
    fpx: 2,
    ts: 3,
    npc: 4,
};
/// The first column after [`STATE`].
const AFTER_STATE: usize = 5;

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

    /// Fall-through state step: the next pc is the successor the bytecode read
    /// returned, the frame unchanged, the clock advanced by `stride`.
    pub(crate) fn state_step(&mut self, st: State, stride: u32) {
        self.state_derived(st, stride, Col(st.npc), Col(st.fp), Col(st.fpx));
    }

    /// Explicit state transition (JUMP): push the next state, which the row
    /// DERIVES from its columns rather than committing, and pull the current one.
    /// The frame pointer rides twice, as the integer and as its g-power (§sec:exp).
    pub(crate) fn state_derived(&mut self, st: State, stride: u32, npc: Coord, nfp: Coord, nfpx: Coord) {
        self.pair(
            vec![Const(SEP_STATE), npc, nfp, nfpx, GCol(st.ts, stride)],
            vec![Const(SEP_STATE), Col(st.pc), Col(st.fp), Col(st.fpx), Col(st.ts)],
        );
    }

    /// Bytecode read at `pc`: the program tuple, which is the opcode, the operand
    /// slots (the unused ones zero), then the successor `pc + 1` and, where `ret` is
    /// given, the return address `pc + 2`; the per-pc execution count is advanced by
    /// ×g on the push side.
    pub(crate) fn bytecode(&mut self, st: State, count: usize, opcode: F64, operands: &[Coord], ret: Option<usize>) {
        let mut tuple = vec![Const(SEP_BYTECODE), Col(st.pc), Col(count), Const(opcode)];
        tuple.extend_from_slice(operands);
        tuple.resize(BYTECODE_SUCC_SLOT, Const(F64::ZERO));
        tuple.push(Col(st.npc));
        tuple.extend(ret.map(Col));
        self.counted(tuple, count);
    }

    /// A read of a lookup array (§sec:lookup): `tuple` as pulled, `tuple[2]` being
    /// its count column `count`, pushed back with the count advanced by ×g.
    fn counted(&mut self, tuple: Vec<Coord>, count: usize) {
        let mut push = tuple.clone();
        push[2] = GCol(count, 1);
        self.pair(push, tuple);
    }

    /// One read of the `EXP` array (§sec:exp): entry `index` is `g^index`, so this
    /// asserts `value = g^index` with `index` a valid address.
    pub(crate) fn exp(&mut self, index: Coord, count: usize, value: Coord) {
        self.counted(vec![Const(SEP_EXP), index, Col(count), value], count);
    }

    /// Access `i` of the row, at clock slot `slot` (§sec:memchan), to the cell whose
    /// address has the g-power `addr_exp`, a product such as `g^fp·g^o`: read the
    /// integer address `A` off `EXP`, pull the cell as its previous access left it,
    /// `(X, old)`, push it back as `(g^{slot}·ts, new)`, and read the gap's two chunks
    /// off the range arrays. A value the row DERIVES rather than commits is passed as
    /// its form (§sec:m3).
    pub(crate) fn memory(&mut self, addr_exp: Coord, ts: usize, acc: Acc, i: usize, slot: u32, old: Coord, new: Coord) {
        self.exp(Col(acc.a(i)), acc.count_exp(i), addr_exp);
        self.pair(
            vec![Const(SEP_MEM), Col(acc.a(i)), GCol(ts, slot), new],
            vec![Const(SEP_MEM), Col(acc.a(i)), Col(acc.x(i)), old],
        );
        self.counted(
            vec![Const(SEP_RANGE_LO), Col(acc.lo(i)), Col(acc.count_lo(i))],
            acc.count_lo(i),
        );
        self.counted(
            vec![Const(SEP_RANGE_HI), Col(acc.hi(i)), Col(acc.count_hi(i))],
            acc.count_hi(i),
        );
    }

    /// A read: [`Self::memory`] leaving the value as it was.
    pub(crate) fn read(&mut self, addr_exp: Coord, ts: usize, acc: Acc, i: usize, slot: u32, val: Coord) {
        self.memory(addr_exp, ts, acc, i, slot, val.clone(), val);
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
            Op::Xor64 { a, b, c } | Op::Mul64 { a, b, c } | Op::AddU64 { a, b, c } | Op::MulU64 { a, b, c } => {
                (a, b, c)
            }
            op => unreachable!("a three-operand row's pc {pc} holds {op:?}"),
        }
    }

    /// The three cells of an arithmetic row.
    fn ternary_cells(&self, pc: u32, fp: u32) -> [u32; 3] {
        let (a, b, c) = self.ternary_operands(pc);
        [fp + a, fp + b, fp + c]
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

    /// The five state columns of [`STATE`]. A padding row sits in frame 0 at clock 0.
    fn state<R: Sync>(&self, out: &mut [ColumnOut], rows: &[R], f: impl Fn(&R) -> (u32, u32, F64) + Sync) {
        self.cols(out, rows, STATE.pc, |r| {
            let (pc, fp, ts) = f(r);
            [F64(pc as u64), F64(fp as u64), self.g_at(fp), ts, F64(pc as u64 + 1)]
        });
    }

    /// The `7·N` columns of a table's accesses, `addrs` giving each one's cell.
    fn accesses<const N: usize, R: Sync>(
        &self,
        out: &mut [ColumnOut],
        rows: &[R],
        acc: Acc,
        addrs: impl Fn(&R) -> [u32; N] + Sync,
        f: impl Fn(&R) -> &[Access; N] + Sync,
    ) {
        assert_eq!(acc.n, N);
        let mask = (1u32 << RANGE_LOG) - 1;
        self.cols(out, rows, acc.a(0), |r| addrs(r).map(|a| F64(a as u64)));
        self.cols(out, rows, acc.x(0), |r| f(r).map(|a| a.x));
        self.cols(out, rows, acc.lo(0), |r| {
            f(r).map(|a| self.range_lo[(a.gap & mask) as usize])
        });
        self.cols(out, rows, acc.hi(0), |r| {
            f(r).map(|a| self.range_hi[(a.gap >> RANGE_LOG) as usize])
        });
        self.cols(out, rows, acc.count_exp(0), |r| f(r).map(|a| a.count_exp));
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

/// The tables in fixed order `[XOR64, MUL64, SET, DEREF, JUMP, BLAKE2S, ADD_U64,
/// MUL_U64]`, the order of `row_counts` / `taus` throughout `cpu`. Table `t`'s
/// opcode is `g^t`.
pub const N_TABLES: usize = 8;

pub fn tables() -> [&'static dyn Table; N_TABLES] {
    [
        &Arith64 { is_xor: true },
        &Arith64 { is_xor: false },
        &SetTable,
        &DerefTable,
        &JumpTable,
        &Blake2sTable,
        &ArithU64 { op: U64Op::Add },
        &ArithU64 { op: U64Op::Mul },
    ]
}

/// Index of the BLAKE2s table in [`tables`].
pub(crate) const BLAKE2S_TABLE: usize = 5;
/// Index of each u64 table in [`tables`].
pub(crate) const fn u64_table(op: U64Op) -> usize {
    match op {
        U64Op::Add => 6,
        U64Op::Mul => 7,
    }
}

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
    pub(crate) use super::STATE;
    use super::{AFTER_STATE, Acc};
    pub const TS: usize = STATE.ts;
    pub const FPX: usize = STATE.fpx;
    // The operands, as the g-powers `g^o` the bytecode carries them as.
    pub const OA: usize = AFTER_STATE;
    pub const OB: usize = OA + 1;
    pub const OC: usize = OA + 2;
    pub const VA: usize = OA + 3;
    pub const VB: usize = OA + 4;
    // What the destination held before the write.
    pub const VC_OLD: usize = OA + 5;
    pub const ACC: Acc = Acc::new(OA + 6, 3);
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
        const COUNTS: [usize; 10] = count_columns(arith64::ACC, arith64::RBC);
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
        f.state_step(STATE, CLOCK_STRIDE);
        f.bytecode(
            STATE,
            RBC,
            if self.is_xor { OP_XOR64 } else { OP_MUL64 },
            &[Col(OA), Col(OB), Col(OC)],
            None,
        );
        f.read(Prod(FPX, OA, 0), TS, ACC, 0, SLOTS[0], Col(VA));
        f.read(Prod(FPX, OB, 0), TS, ACC, 1, SLOTS[1], Col(VB));
        let result = if self.is_xor {
            Coord::Sum(vec![Col(VA), Col(VB)])
        } else {
            Prod(VA, VB, 0)
        };
        f.memory(Prod(FPX, OC, 0), TS, ACC, 2, SLOTS[2], Col(VC_OLD), result);
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]) {
        use arith64::*;
        let rows = if self.is_xor {
            &ctx.trace.xor64
        } else {
            &ctx.trace.mul64
        };
        ctx.state(out, rows, |r| (r.pc, r.fp, r.ts));
        ctx.cols(out, rows, OA, |r| {
            let (a, b, c) = ctx.ternary_operands(r.pc);
            [ctx.g_at(a), ctx.g_at(b), ctx.g_at(c), r.va, r.vb, r.vc_old]
        });
        ctx.accesses(out, rows, ACC, |r| ctx.ternary_cells(r.pc, r.fp), |r| &r.acc);
        ctx.col(out, rows, RBC, |r| r.bytecode_read);
    }
}

// ---- ADD_U64 / MUL_U64 -------------------------------------------------------

/// `ADD_U64` and `MUL_U64` (§sec:tab-u64): the two operands and the result read as
/// unsigned 64-bit integers, the result wrapping. The relation between the three
/// words is proven by flock's R1CS over the operation's own packed witness
/// ([`crate::arith_flock`]), which already holds them, so the three value columns
/// are VIRTUAL like `BLAKE2s`'s: `cpu` routes their claims to that witness
/// ([`U64_VALUE_COLS`]).
struct ArithU64 {
    op: U64Op,
}

pub(crate) mod arith_u64 {
    pub(crate) use super::STATE;
    use super::{AFTER_STATE, Acc};
    pub const TS: usize = STATE.ts;
    pub const FPX: usize = STATE.fpx;
    pub const OA: usize = AFTER_STATE;
    pub const OB: usize = OA + 1;
    pub const OC: usize = OA + 2;
    // The two operands and the result, in the packed witness's slot order.
    pub const VA: usize = OA + 3;
    // What the destination held before the write.
    pub const VC_OLD: usize = VA + 3;
    pub const ACC: Acc = Acc::new(VC_OLD + 1, 3);
    pub const RBC: usize = ACC.end();
    pub const N: usize = RBC + 1;
    pub const SLOTS: [u32; 3] = [0, 1, 2];
}

/// The u64 tables' value-column LOCAL indices, in the order of
/// [`crate::arith_flock::SLOTS`]: `a`, `b`, the result.
pub const U64_VALUE_COLS: [usize; 3] = [arith_u64::VA, arith_u64::VA + 1, arith_u64::VA + 2];

impl ArithU64 {
    fn eval<T: ColVal>(w: &[F192], cols: &[T]) -> F192 {
        access_identities(w, cols, arith_u64::TS, arith_u64::ACC)
    }
}

impl Table for ArithU64 {
    fn n_committed_columns(&self) -> usize {
        arith_u64::N
    }
    fn count_columns(&self) -> &'static [usize] {
        const COUNTS: [usize; 10] = count_columns(arith_u64::ACC, arith_u64::RBC);
        &COUNTS
    }
    fn n_constraints(&self) -> usize {
        3
    }
    fn constraint_weights(&self, pows: &[F192]) -> Vec<F192> {
        access_weights(pows, &arith_u64::SLOTS)
    }
    fn eval_constraint(&self, w: &[F192], cols: &[F192], _quadratic: bool) -> F192 {
        Self::eval(w, cols)
    }
    fn eval_constraint_k(&self, w: &[F192], cols: &[F64], _quadratic: bool) -> F192 {
        Self::eval(w, cols)
    }
    fn flushes(&self, f: &mut FlushBuilder) {
        use arith_u64::*;
        let opcode = match self.op {
            U64Op::Add => OP_ADD_U64,
            U64Op::Mul => OP_MUL_U64,
        };
        f.state_step(STATE, CLOCK_STRIDE);
        f.bytecode(STATE, RBC, opcode, &[Col(OA), Col(OB), Col(OC)], None);
        f.read(Prod(FPX, OA, 0), TS, ACC, 0, SLOTS[0], Col(VA));
        f.read(Prod(FPX, OB, 0), TS, ACC, 1, SLOTS[1], Col(VA + 1));
        f.memory(Prod(FPX, OC, 0), TS, ACC, 2, SLOTS[2], Col(VC_OLD), Col(VA + 2));
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]) {
        use arith_u64::*;
        let rows = match self.op {
            U64Op::Add => &ctx.trace.add_u64,
            U64Op::Mul => &ctx.trace.mul_u64,
        };
        ctx.state(out, rows, |r| (r.pc, r.fp, r.ts));
        ctx.cols(out, rows, OA, |r| {
            let (a, b, c) = ctx.ternary_operands(r.pc);
            [
                ctx.g_at(a),
                ctx.g_at(b),
                ctx.g_at(c),
                r.va,
                r.vb,
                self.op.apply(r.va, r.vb),
                r.vc_old,
            ]
        });
        ctx.accesses(out, rows, ACC, |r| ctx.ternary_cells(r.pc, r.fp), |r| &r.acc);
        ctx.col(out, rows, RBC, |r| r.bytecode_read);
    }
}

// ---- SET ---------------------------------------------------------------------

struct SetTable;

mod set {
    pub(crate) use super::STATE;
    use super::{AFTER_STATE, Acc};
    pub const TS: usize = STATE.ts;
    pub const FPX: usize = STATE.fpx;
    pub const O: usize = AFTER_STATE;
    // The stored immediate rides the bytecode's second operand slot.
    pub const K: usize = O + 1;
    pub const V_OLD: usize = O + 2;
    pub const ACC: Acc = Acc::new(O + 3, 1);
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
        const COUNTS: [usize; 4] = count_columns(set::ACC, set::RBC);
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
        f.state_step(STATE, CLOCK_STRIDE);
        f.bytecode(STATE, RBC, OP_SET, &[Col(O), Col(K)], None);
        f.memory(Prod(FPX, O, 0), TS, ACC, 0, SLOTS[0], Col(V_OLD), Col(K));
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]) {
        use set::*;
        let rows = &ctx.trace.set;
        let imm = |r: &Srow| match ctx.prog[r.pc as usize] {
            Op::Set { o, k } => (o, k),
            op => unreachable!("a SET row's pc {} holds {op:?}", r.pc),
        };
        ctx.state(out, rows, |r| (r.pc, r.fp, r.ts));
        ctx.cols(out, rows, O, |r| {
            let (o, k) = imm(r);
            [ctx.g_at(o), k, r.v_old]
        });
        ctx.accesses(out, rows, ACC, |r| [r.fp + imm(r).0], |r| &r.acc);
        ctx.col(out, rows, RBC, |r| r.bytecode_read);
    }
}

// ---- DEREF -------------------------------------------------------------------

struct DerefTable;

mod deref {
    pub(crate) use super::STATE;
    use super::{AFTER_STATE, Acc};
    pub const TS: usize = STATE.ts;
    pub const FP: usize = STATE.fp;
    pub const FPX: usize = STATE.fpx;
    pub const O1: usize = AFTER_STATE;
    pub const O2: usize = O1 + 1;
    pub const O3: usize = O1 + 2;
    pub const FPC: usize = O1 + 3;
    pub const FFP: usize = O1 + 4;
    // The return address `pc + 2` the bytecode read returns in `deref_pc` mode, zero
    // in the other two.
    pub const RET: usize = O1 + 5;
    // The pointer, an integer, and its g-power, read off `EXP`: the target's address
    // is `p + o2`, so its g-power is `px·g^o2`.
    pub const P: usize = O1 + 6;
    pub const PX: usize = O1 + 7;
    // The local cell. The stored word is DERIVED from it, the two flags, `ret` and
    // `fp`, so it is no column.
    pub const V3: usize = O1 + 8;
    // What the store target held before the write.
    pub const V2_OLD: usize = O1 + 9;
    /// Pointer, local cell, store target: the two reads before the write.
    pub const ACC: Acc = Acc::new(O1 + 10, 3);
    // The count of the pointer's own `EXP` read.
    pub const COUNT_PX: usize = ACC.end();
    pub const RBC: usize = COUNT_PX + 1;
    pub const N: usize = RBC + 1;
    pub const SLOTS: [u32; 3] = [0, 1, 2];
}

/// The stored word as a form: `v_2 = (1+f_pc+f_fp)·v_3 + ret + f_fp·fp`, the
/// flag-selected source of §sec:tab-deref. The return target `ret = pc + 2` comes with
/// the bytecode read, already zero outside `deref_pc` mode.
fn deref_store() -> Coord {
    use deref::*;
    Coord::Sum(vec![
        Col(V3),
        Prod(FPC, V3, 0),
        Prod(FFP, V3, 0),
        Col(RET),
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
        const COUNTS: [usize; 11] = count_columns(deref::ACC, deref::RBC);
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
        f.state_step(STATE, CLOCK_STRIDE);
        f.bytecode(
            STATE,
            RBC,
            OP_DEREF,
            &[Col(O1), Col(O2), Col(O3), Col(FPC), Col(FFP)],
            Some(RET),
        );
        // The pointer cell and the local cell are frame-relative reads; the store
        // target is pointer-relative, `p + o2`, so the pointer's g-power is read off
        // `EXP` first, and what the target is written with is the flag-selected source
        // rather than a column.
        f.read(Prod(FPX, O1, 0), TS, ACC, 0, SLOTS[0], Col(P));
        f.read(Prod(FPX, O3, 0), TS, ACC, 1, SLOTS[1], Col(V3));
        f.exp(Col(P), COUNT_PX, Col(PX));
        f.memory(Prod(PX, O2, 0), TS, ACC, 2, SLOTS[2], Col(V2_OLD), deref_store());
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]) {
        use deref::*;
        let rows = &ctx.trace.deref;
        let ins = |r: &Drow| match ctx.prog[r.pc as usize] {
            Op::Deref { o1, o2, o3, mode } => (o1, o2, o3, mode),
            op => unreachable!("a DEREF row's pc {} holds {op:?}", r.pc),
        };
        ctx.state(out, rows, |r| (r.pc, r.fp, r.ts));
        // The three offsets, the two mode flags and the return address follow from ONE
        // bytecode decode.
        ctx.cols(out, rows, O1, |r| {
            let (o1, o2, o3, mode) = ins(r);
            [
                ctx.g_at(o1),
                ctx.g_at(o2),
                ctx.g_at(o3),
                mode.f_pc(),
                mode.f_fp(),
                mode.ret(r.pc),
                r.p,
                ctx.g_at(r.p.0 as u32),
                r.v3,
                r.v2_old,
            ]
        });
        ctx.accesses(
            out,
            rows,
            ACC,
            |r| {
                let (o1, o2, o3, _) = ins(r);
                [r.fp + o1, r.fp + o3, r.p.0 as u32 + o2]
            },
            |r| &r.acc,
        );
        ctx.col(out, rows, COUNT_PX, |r| r.count_px);
        ctx.col(out, rows, RBC, |r| r.bytecode_read);
    }
}

// ---- JUMP --------------------------------------------------------------------

struct JumpTable;

mod jump {
    pub(crate) use super::STATE;
    use super::{AFTER_STATE, Acc};
    pub const TS: usize = STATE.ts;
    pub const FP: usize = STATE.fp;
    pub const FPX: usize = STATE.fpx;
    pub const NPC: usize = STATE.npc;
    pub const OC: usize = AFTER_STATE;
    pub const OD: usize = OC + 1;
    pub const OF: usize = OC + 2;
    pub const V_COND: usize = OC + 3;
    pub const V_PC: usize = OC + 4;
    pub const V_FP: usize = OC + 5;
    // The g-power of the frame the jump loads, read off `EXP`; `g^0` when it loads
    // none.
    pub const V_FPX: usize = OC + 6;
    // Local witness columns (committed, never flushed): the inverse hint `w = c⁻¹`
    // and the taken indicator `b = [c ≠ 0]` it certifies.
    pub const W: usize = OC + 7;
    pub const B: usize = OC + 8;
    pub const ACC: Acc = Acc::new(OC + 9, 3);
    // The count of the new frame's `EXP` read.
    pub const COUNT_FPX: usize = ACC.end();
    pub const RBC: usize = COUNT_FPX + 1;
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
        const COUNTS: [usize; 11] = count_columns(jump::ACC, jump::RBC);
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
        // The successor state is DERIVED: `b·d + (b+1)·npc`, and `b·f + (b+1)·fp` in
        // both of the frame pointer's forms, each degree 2 in K columns, so no
        // successor is committed. Written out in characteristic 2 as `b·d + b·npc +
        // npc`.
        let select = |taken, otherwise| Coord::Sum(vec![Prod(B, taken, 0), Prod(B, otherwise, 0), Col(otherwise)]);
        f.state_derived(
            STATE,
            CLOCK_STRIDE,
            select(V_PC, NPC),
            select(V_FP, FP),
            select(V_FPX, FPX),
        );
        f.bytecode(STATE, RBC, OP_JUMP, &[Col(OC), Col(OD), Col(OF)], None);
        f.read(Prod(FPX, OC, 0), TS, ACC, 0, SLOTS[0], Col(V_COND));
        f.read(Prod(FPX, OD, 0), TS, ACC, 1, SLOTS[1], Col(V_PC));
        f.read(Prod(FPX, OF, 0), TS, ACC, 2, SLOTS[2], Col(V_FP));
        // The new frame's g-power, read at `b·v_fp`: a jump not taken loads no frame,
        // so it reads entry 0 rather than whatever the cell holds.
        f.exp(Prod(B, V_FP, 0), COUNT_FPX, Col(V_FPX));
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]) {
        use jump::*;
        let rows = &ctx.trace.jump;
        let ins = |r: &Jrow| match ctx.prog[r.pc as usize] {
            Op::Jump { oc, od, of } => (oc, od, of),
            op => unreachable!("a JUMP row's pc {} holds {op:?}", r.pc),
        };
        ctx.state(out, rows, |r| (r.pc, r.fp, r.ts));
        ctx.cols(out, rows, OC, |r| {
            let (oc, od, of) = ins(r);
            let loaded = if r.cond.is_zero() { 0 } else { r.frame.0 as u32 };
            [
                ctx.g_at(oc),
                ctx.g_at(od),
                ctx.g_at(of),
                r.cond,
                r.dest,
                r.frame,
                ctx.g_at(loaded),
            ]
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
        ctx.accesses(
            out,
            rows,
            ACC,
            |r| {
                let (oc, od, of) = ins(r);
                [r.fp + oc, r.fp + od, r.fp + of]
            },
            |r| &r.acc,
        );
        ctx.col(out, rows, COUNT_FPX, |r| r.count_fpx);
        ctx.col(out, rows, RBC, |r| r.bytecode_read);
    }
}

// ---- BLAKE2s ------------------------------------------------------------------

/// `BLAKE2s` (§sec:tab-blake2s): one standard compression. The four 128-bit message
/// chunks are addressed *independently* at `fp + o_i`, each spanning that cell and its
/// successor, so a caller hashing e.g. `(tweak, pp)` need not copy them into
/// adjacent cells. The digest and the chaining value span four consecutive cells,
/// the metadata two, so the row touches eighteen cells: fourteen reads, then the
/// four digest writes. Each cell's address `fp + o + k` is a column, read off `EXP`
/// at the product `g^fp·g^o·g^k` (§sec:exp). The compression relating output words to input words is
/// proven by flock's R1CS via `q_flock` (§hash_flock).
///
/// The eighteen cells are eighteen value columns. They are listed in
/// `n_committed_columns` (they need a local index for the flushes and are filled
/// from the trace for the bus), but `cpu` treats them as VIRTUAL (not committed) and
/// routes their bus claims to `q_flock`, which already holds those words (see
/// [`BLAKE2S_VALUE_COLS`]).
struct Blake2sTable;

pub(crate) mod blake2st {
    pub(crate) use super::STATE;
    use super::{AFTER_STATE, Acc};
    pub const TS: usize = STATE.ts;
    pub const FPX: usize = STATE.fpx;
    pub const O_M0: usize = AFTER_STATE; // operand g-powers of the four message chunks …
    pub const O_CV: usize = O_M0 + 4; // … the chaining value …
    pub const O_OUT: usize = O_M0 + 5; // … the digest …
    pub const O_MD: usize = O_M0 + 6; // … and the metadata.
    // The eighteen value lanes, one per cell: the message chunks' eight, then the
    // digest's four, the chaining value's four and the metadata's counter and flags.
    pub const V0: usize = O_M0 + 7;
    // What the four digest cells held before the write.
    pub const OUT_OLD: usize = V0 + 18;
    /// One access per value lane, in the same order.
    pub const ACC: Acc = Acc::new(OUT_OLD + 4, 18);
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
        const COUNTS: [usize; 55] = count_columns(blake2st::ACC, blake2st::RBC);
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
        f.state_step(STATE, BLAKE2S_STRIDE);
        f.bytecode(
            STATE,
            RBC,
            OP_BLAKE2S,
            &std::array::from_fn::<_, 7, _>(|i| Col(O_M0 + i)),
            None,
        );
        // A successor cell is a free ×g^k on the address's g-power. The metadata rides
        // the memory bus like every other operand: the read is what binds flock's
        // counter and flag inputs.
        for (lane, &(operand, k)) in BLAKE2S_LANE_CELLS.iter().enumerate() {
            let old = match lane.checked_sub(OUT_LANE) {
                Some(i) if i < 4 => Col(OUT_OLD + i),
                _ => Col(V0 + lane),
            };
            f.memory(
                Prod(FPX, operand, k),
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
        ctx.state(out, rows, |r| (r.pc, r.fp, r.ts));
        ctx.cols(out, rows, O_M0, |r: &Brow| match ctx.prog[r.pc as usize] {
            Op::Blake2s { ins, cv, out, md } => [ins[0], ins[1], ins[2], ins[3], cv, out, md].map(|o| ctx.g_at(o)),
            op => unreachable!("a BLAKE2s row's pc {} holds {op:?}", r.pc),
        });
        ctx.cols(out, rows, V0, |r| r.w);
        ctx.cols(out, rows, OUT_OLD, |r| r.out_old);
        ctx.accesses(out, rows, ACC, |r| blake2s_cells(ctx.prog, r.pc, r.fp), |r| &r.acc);
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
