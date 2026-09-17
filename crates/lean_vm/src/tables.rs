//! Per-instruction tables (`doc/leanvm/body/07-instruction-tables.tex`). Each opcode is one [`Table`] impl that declares,
//! in one place, its committed columns, how to fill them from the trace, its bus
//! interactions (flushes), the read-count columns that feed the count channel,
//! and its degree-2 constraint. Column indices here are *local* (`0..n_committed_columns`);
//! `cpu`'s schema offsets them to global witness columns.
//!
//! Every column is `K`-valued (`F64`), and so is every memory cell. Nothing
//! a row DERIVES is a column at all: an operand address `fp·o`, an arithmetic
//! result, the `DEREF` store, the `JUMP` successors are each written out as the
//! degree-2 bus coordinate that carries them (§sec:m3), which leaves `JUMP`'s
//! is-nonzero indicator as the one identity any table still has. After the round a
//! table joins the batch its columns are `E`-valued, which is what
//! `eval_constraint` takes.

use crate::colval::ColVal;
use crate::cpu::{Brow, Drow, Jrow, Op, Srow, Trace};
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

// Domain separators (coordinate 0 of every bus tuple): the g-powers g^0, g^1, g^2.
pub(crate) const SEP_STATE: F64 = g_pow(0);
pub(crate) const SEP_MEM: F64 = g_pow(1);
pub(crate) const SEP_BYTECODE: F64 = g_pow(2);

// Opcodes (coordinate 3 of a bytecode tuple): `g^t` for table `t` of [`tables`].
pub(crate) const OP_XOR64: F64 = g_pow(0);
pub(crate) const OP_MUL64: F64 = g_pow(1);
pub(crate) const OP_SET: F64 = g_pow(2);
pub(crate) const OP_DEREF: F64 = g_pow(3);
pub(crate) const OP_JUMP: F64 = g_pow(4);
pub(crate) const OP_BLAKE2S: F64 = g_pow(5);

// ---- flush builder -----------------------------------------------------------

/// Collects a table's push/pull bus interactions in *local* column indices. The
/// push/pull of a memory-checked entry differ only by one coordinate carrying the
/// post-increment `g·count` (`GCol`) instead of the pre-increment (`Col`); these
/// helpers encode that pairing so each table reads declaratively.
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

    /// Fall-through state step: the next pc is `g·pc`, fp unchanged.
    pub(crate) fn state_step(&mut self, pc: usize, fp: usize) {
        self.pair(
            vec![Const(SEP_STATE), GCol(pc, 1), Col(fp)],
            vec![Const(SEP_STATE), Col(pc), Col(fp)],
        );
    }

    /// Explicit state transition (JUMP): push the next state, which the row
    /// DERIVES from its columns rather than committing, and pull `(pc, fp)`.
    pub(crate) fn state_derived(&mut self, pc: usize, fp: usize, npc: Coord, nfp: Coord) {
        self.pair(
            vec![Const(SEP_STATE), npc, nfp],
            vec![Const(SEP_STATE), Col(pc), Col(fp)],
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

    /// Memory access: the word at `addr`, with the cell's access count advanced by
    /// ×g on the push side. A value the row DERIVES rather than commits (an
    /// arithmetic result, a `DEREF` store) is passed as its form: the cell then holds
    /// whatever the form says, which removes both a value column and the identity
    /// that would tie it (§sec:m3).
    pub(crate) fn memory(&mut self, addr: Coord, count: usize, val: Coord) {
        self.pair(
            vec![Const(SEP_MEM), addr.clone(), GCol(count, 1), val.clone()],
            vec![Const(SEP_MEM), addr, Col(count), val],
        );
    }
}

// ---- fill context ------------------------------------------------------------

/// Inputs a table needs to fill its columns: the trace rows, the final memory
/// image (for read values), and `g^0..` for O(1) address/operand lookups.
pub struct FillCtx<'a> {
    pub(crate) trace: &'a Trace,
    pub(crate) mem: &'a [F64],
    pub(crate) gpow: &'a [F64],
    pub(crate) prog: &'a [Op],
    /// This table's height `2^tau`, the length of every window in `out`, and its row
    /// count too: every row is a row the program executed (`cpu::filler`).
    pub(crate) rows: usize,
    /// Which local columns [`Self::col`] / [`Self::cols`] have written. A fill that
    /// misses one would leave the stacked witness holding uninitialized slots, so
    /// [`fill_table`] checks the whole set was covered.
    written: std::sync::atomic::AtomicU64,
}

/// Where one column's values go: its window in the stacked witness, or a private
/// buffer if the column is virtual.
pub type ColumnOut<'a> = &'a mut [F64];

impl<'a> FillCtx<'a> {
    pub(crate) fn new(trace: &'a Trace, mem: &'a [F64], gpow: &'a [F64], prog: &'a [Op], rows: usize) -> Self {
        Self {
            trace,
            mem,
            gpow,
            prog,
            rows,
            written: std::sync::atomic::AtomicU64::new(0),
        }
    }

    fn g_at(&self, i: u32) -> F64 {
        self.gpow[i as usize]
    }

    fn cell(&self, addr: u32) -> F64 {
        self.mem[addr as usize]
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
            self.written
                .fetch_or(1 << (at + k), std::sync::atomic::Ordering::Relaxed);
            parallel::SendPtr(out[at + k].as_mut_ptr())
        });
        // Every row is a row the program executed: a table's height is its row
        // count (`cpu::filler`), so there is nothing to pad with.
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
    let n = table.n_committed_columns();
    assert!(n <= 64, "the write mask covers at most 64 columns per table");
    let all = if n == 64 { u64::MAX } else { (1u64 << n) - 1 };
    let written = ctx.written.load(std::sync::atomic::Ordering::Relaxed);
    assert_eq!(written, all, "a table left one of its columns unwritten");
}

// ---- the trait ---------------------------------------------------------------

/// One instruction table. Indices in [`flushes`](Table::flushes) and
/// [`count_columns`](Table::count_columns) are local to this table.
pub trait Table: Sync {
    /// Number of committed columns (local indices `0..n_committed_columns`).
    fn n_committed_columns(&self) -> usize;
    /// Local indices of this table's read-count columns: the `g^{count}` values
    /// recording how many times each accessed cell (and the pc) was read. The
    /// framework treats them specially: each gets its own single-column "count"
    /// bus block.
    fn count_columns(&self) -> &'static [usize];
    /// How many identities [`eval_constraint`](Table::eval_constraint) folds.
    /// Sizes this table's slice of the batch's disjoint `xi`-range (§constraints).
    /// Defaults to none, which is every table but `JUMP`: a relation whose value
    /// rides the bus as a coordinate needs no identity to tie it (§sec:m3).
    fn n_constraints(&self) -> usize {
        0
    }
    /// Evaluate the table's degree-2 constraint at one row, reading column values
    /// by local index from `cols` (e.g. `cols[jump::V_COND]`) and weighting identity
    /// `i` by `pows[i]`, this table's slice of the batch's `xi`-powers. The slice is
    /// exactly [`n_constraints`](Table::n_constraints) long: an identity indexed
    /// past its end panics rather than silently reaching into the next table's
    /// range. The table sumcheck carries every committed column of a table, in
    /// local order, so `cols` is indexed directly. With `quadratic=false` it returns
    /// `0` on every valid row (§sec:air); `true` selects only the degree-two terms.
    /// The default is the constraint-free case; a table that declares constraints
    /// and forgets to evaluate them trips the assert instead of dropping them.
    fn eval_constraint(&self, pows: &[F192], _cols: &[F192], _quadratic: bool) -> F192 {
        assert!(pows.is_empty(), "a table with constraints must evaluate them");
        F192::ZERO
    }
    /// The same identity over `K`-valued columns, for the round a table joins the
    /// batch, before its columns have been folded into `E` (§sec:air). Both entry
    /// points delegate to one generic definition per table, so they cannot drift.
    fn eval_constraint_k(&self, pows: &[F192], _cols: &[F64], _quadratic: bool) -> F192 {
        assert!(pows.is_empty(), "a table with constraints must evaluate them");
        F192::ZERO
    }
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

/// The eighteen cells a `BLAKE2s` row reads, in value-lane order: the four message
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
/// only in the opcode tag and in how the destination cell's value rides the bus
/// (`v_A + v_B` or `v_A·v_B`). Neither commits that value and neither has an
/// identity: bus balance IS the assertion (§sec:m3).
struct Arith64 {
    is_xor: bool,
}

mod arith64 {
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const OA: usize = 2;
    pub const OB: usize = 3;
    pub const OC: usize = 4;
    pub const VA: usize = 5;
    pub const VB: usize = 6;
    pub const RA: usize = 7;
    pub const RB: usize = 8;
    pub const RC: usize = 9;
    pub const RBC: usize = 10;
    pub const N: usize = 11;
}

impl Table for Arith64 {
    fn n_committed_columns(&self) -> usize {
        arith64::N
    }
    fn count_columns(&self) -> &'static [usize] {
        use arith64::*;
        &[RA, RB, RC, RBC]
    }
    fn flushes(&self, f: &mut FlushBuilder) {
        use arith64::*;
        f.state_step(PC, FP);
        f.bytecode(
            PC,
            RBC,
            if self.is_xor { OP_XOR64 } else { OP_MUL64 },
            &[Col(OA), Col(OB), Col(OC), Const(F64::ZERO), Const(F64::ZERO)],
        );
        f.memory(Prod(FP, OA, 0), RA, Col(VA));
        f.memory(Prod(FP, OB, 0), RB, Col(VB));
        let result = if self.is_xor {
            Coord::Sum(vec![Col(VA), Col(VB)])
        } else {
            Prod(VA, VB, 0)
        };
        f.memory(Prod(FP, OC, 0), RC, result);
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
            [
                ctx.g_at(a),
                ctx.g_at(b),
                ctx.g_at(c),
                ctx.cell(r.fp + a),
                ctx.cell(r.fp + b),
            ]
        });
        ctx.cols(out, rows, RA, |r| [r.ra, r.rb, r.rc]);
        ctx.col(out, rows, RBC, |r| r.bytecode_read);
    }
}

// ---- SET ---------------------------------------------------------------------

struct SetTable;

mod set {
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const O: usize = 2;
    // The stored immediate rides the bytecode's second operand slot.
    pub const K: usize = 3;
    pub const R: usize = 4;
    pub const RBC: usize = 5;
    pub const N: usize = 6;
}

impl Table for SetTable {
    fn n_committed_columns(&self) -> usize {
        set::N
    }
    fn count_columns(&self) -> &'static [usize] {
        use set::*;
        &[R, RBC]
    }
    fn flushes(&self, f: &mut FlushBuilder) {
        use set::*;
        f.state_step(PC, FP);
        f.bytecode(
            PC,
            RBC,
            OP_SET,
            &[Col(O), Col(K), Const(F64::ZERO), Const(F64::ZERO), Const(F64::ZERO)],
        );
        f.memory(Prod(FP, O, 0), R, Col(K));
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
            [ctx.g_at(o), k]
        });
        ctx.col(out, rows, R, |r| r.r);
        ctx.col(out, rows, RBC, |r| r.bytecode_read);
    }
}

// ---- DEREF -------------------------------------------------------------------

struct DerefTable;

mod deref {
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const O1: usize = 2;
    pub const O2: usize = 3;
    pub const O3: usize = 4;
    pub const FPC: usize = 5;
    pub const FFP: usize = 6;
    // The pointer, which forms the pointer-relative address `p·o2` on the bus.
    pub const P: usize = 7;
    // The local cell. The store target is DERIVED from it, the two flags, `pc` and
    // `fp`, so it is no column.
    pub const V3: usize = 8;
    pub const R1: usize = 9;
    pub const R2: usize = 10;
    pub const R3: usize = 11;
    pub const RBC: usize = 12;
    pub const N: usize = 13;
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

impl Table for DerefTable {
    fn n_committed_columns(&self) -> usize {
        deref::N
    }
    fn count_columns(&self) -> &'static [usize] {
        use deref::*;
        &[R1, R2, R3, RBC]
    }
    fn flushes(&self, f: &mut FlushBuilder) {
        use deref::*;
        f.state_step(PC, FP);
        f.bytecode(PC, RBC, OP_DEREF, &[Col(O1), Col(O2), Col(O3), Col(FPC), Col(FFP)]);
        // The pointer cell and the local cell are frame-relative; the store target
        // is pointer-relative, so its address is `p·o2`, and its value is the
        // flag-selected source rather than a column.
        f.memory(Prod(FP, O1, 0), R1, Col(P));
        f.memory(Prod(P, O2, 0), R2, deref_store());
        f.memory(Prod(FP, O3, 0), R3, Col(V3));
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
        // The three offsets, the two mode flags, the pointer and the local cell all
        // follow from ONE bytecode decode.
        ctx.cols(out, rows, O1, |r| {
            let (o1, o2, o3, mode) = ins(r);
            [
                ctx.g_at(o1),
                ctx.g_at(o2),
                ctx.g_at(o3),
                mode.f_pc(),
                mode.f_fp(),
                ctx.cell(r.fp + o1),
                ctx.cell(r.fp + o3),
            ]
        });
        ctx.cols(out, rows, R1, |r| [r.r1, r.r2, r.r3]);
        ctx.col(out, rows, RBC, |r| r.bytecode_read);
    }
}

// ---- JUMP --------------------------------------------------------------------

struct JumpTable;

mod jump {
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const OC: usize = 2;
    pub const OD: usize = 3;
    pub const OF: usize = 4;
    pub const V_COND: usize = 5;
    pub const V_PC: usize = 6;
    pub const V_FP: usize = 7;
    pub const RC: usize = 8;
    pub const RD: usize = 9;
    pub const RF: usize = 10;
    pub const RBC: usize = 11;
    // Local witness columns (committed, never flushed): the inverse hint `w = c⁻¹`
    // and the taken indicator `b = [c ≠ 0]` it certifies.
    pub const W: usize = 12;
    pub const B: usize = 13;
    pub const N: usize = 14;
}

impl Table for JumpTable {
    fn n_committed_columns(&self) -> usize {
        jump::N
    }
    fn count_columns(&self) -> &'static [usize] {
        use jump::*;
        &[RC, RD, RF, RBC]
    }
    fn n_constraints(&self) -> usize {
        2 // the two indicator identities; the selections ride the state push
    }
    fn eval_constraint(&self, pows: &[F192], cols: &[F192], quadratic: bool) -> F192 {
        jump_identity(pows, cols, quadratic)
    }
    fn eval_constraint_k(&self, pows: &[F192], cols: &[F64], quadratic: bool) -> F192 {
        jump_identity(pows, cols, quadratic)
    }
    fn flushes(&self, f: &mut FlushBuilder) {
        use jump::*;
        // The successor state is DERIVED: `b·d + (b+1)·g·pc` and `b·f + (b+1)·fp`,
        // each degree 2 in K columns, so neither successor is committed. Written
        // out in characteristic 2 as `b·d + b·(g·pc) + g·pc`.
        f.state_derived(
            PC,
            FP,
            Coord::Sum(vec![Prod(B, V_PC, 0), Prod(B, PC, 1), GCol(PC, 1)]),
            Coord::Sum(vec![Prod(B, V_FP, 0), Prod(B, FP, 0), Col(FP)]),
        );
        f.bytecode(
            PC,
            RBC,
            OP_JUMP,
            &[Col(OC), Col(OD), Col(OF), Const(F64::ZERO), Const(F64::ZERO)],
        );
        f.memory(Prod(FP, OC, 0), RC, Col(V_COND));
        f.memory(Prod(FP, OD, 0), RD, Col(V_PC));
        f.memory(Prod(FP, OF, 0), RF, Col(V_FP));
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]) {
        use jump::*;
        let rows = &ctx.trace.jump;
        let ins = |r: &Jrow| match ctx.prog[r.pc as usize] {
            Op::Jump { oc, od, of } => (oc, od, of),
            op => unreachable!("a JUMP row's pc {} holds {op:?}", r.pc),
        };
        let cond = |r: &Jrow| ctx.cell(r.fp + ins(r).0);
        ctx.col(out, rows, PC, |r| ctx.g_at(r.pc));
        ctx.col(out, rows, FP, |r| ctx.g_at(r.fp));
        // The three offsets and the three cells they name come out of ONE decode.
        ctx.cols(out, rows, OC, |r| {
            let (oc, od, of) = ins(r);
            [
                ctx.g_at(oc),
                ctx.g_at(od),
                ctx.g_at(of),
                ctx.cell(r.fp + oc),
                ctx.cell(r.fp + od),
                ctx.cell(r.fp + of),
            ]
        });
        // The is-nonzero witness `w = c⁻¹` (0 where c = 0) for every row, in one
        // batched Montgomery inversion. `prefix[i]` is the running product of the
        // nonzero conditions before row `i`, so `acc` ends as their full product
        // (nonzero, hence invertible). The taken indicator `b = [c ≠ 0]` falls out
        // of the same pass, so it costs no extra decode.
        let (w, b) = {
            let mut acc = F64::ONE;
            let mut prefix: Vec<F64> = Vec::with_capacity(rows.len());
            let mut b = vec![F64::ZERO; rows.len()];
            for (i, r) in rows.iter().enumerate() {
                prefix.push(acc);
                let c = cond(r);
                if !c.is_zero() {
                    acc *= c;
                    b[i] = F64::ONE;
                }
            }
            let mut inv = acc.inv();
            let mut w = vec![F64::ZERO; rows.len()];
            for (i, r) in rows.iter().enumerate().rev() {
                let c = cond(r);
                if !c.is_zero() {
                    w[i] = inv * prefix[i];
                    inv *= c;
                }
            }
            (w, b)
        };
        ctx.cols_at(out, rows.len(), W, |i| [w[i], b[i]]);
        ctx.cols(out, rows, RC, |r| [r.rc, r.rd, r.rf]);
        ctx.col(out, rows, RBC, |r| r.bytecode_read);
    }
}

// ---- BLAKE2s ------------------------------------------------------------------

/// `BLAKE2s` (§sec:tab-blake2s): one standard compression. The four 128-bit message
/// chunks are addressed *independently* at `fp·o_i`, each spanning that cell and its
/// successor, so a caller hashing e.g. `(tweak, pp)` need not copy them into
/// adjacent cells. The digest and the chaining value span four consecutive cells,
/// the metadata two, so the row reads eighteen cells. No address is committed: each
/// rides the bus as the product `fp·o·g^k` (§sec:m3). The compression relating
/// output words to input words is proven by flock's R1CS via `q_flock`
/// (§hash_flock), which leaves this table with no identity of its own.
///
/// The eighteen cells are eighteen value columns. They are listed in
/// `n_committed_columns` (they need a local index for the flushes and are filled
/// from the trace for the bus), but `cpu` treats them as VIRTUAL (not committed) and
/// routes their bus claims to `q_flock`, which already holds those words (see
/// [`BLAKE2S_VALUE_COLS`]).
struct Blake2sTable;

pub(crate) mod blake2st {
    pub const PC: usize = 0;
    pub const FP: usize = 1;
    pub const O_M0: usize = 2; // operand g-powers of the four message chunks …
    pub const O_CV: usize = 6; // … the chaining value …
    pub const O_OUT: usize = 7; // … the digest …
    pub const O_MD: usize = 8; // … and the metadata.
    // The eighteen value lanes, one per cell: the message chunks' eight, then the
    // digest's four, the chaining value's four and the metadata's counter and flags.
    pub const V0: usize = 9;
    // One read count per value lane, in the same order.
    pub const R0: usize = 27;
    pub const RBC: usize = 45;
    pub const N: usize = 46;
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

impl Table for Blake2sTable {
    fn n_committed_columns(&self) -> usize {
        blake2st::N
    }
    fn count_columns(&self) -> &'static [usize] {
        const COUNTS: [usize; 19] = {
            let mut c = [blake2st::RBC; 19];
            let mut i = 0;
            while i < 18 {
                c[i] = blake2st::R0 + i;
                i += 1;
            }
            c
        };
        &COUNTS
    }
    fn flushes(&self, f: &mut FlushBuilder) {
        use blake2st::*;
        f.state_step(PC, FP);
        f.bytecode(PC, RBC, OP_BLAKE2S, &std::array::from_fn::<_, 7, _>(|i| Col(O_M0 + i)));
        // A successor cell is a free ×g^k on the address product. The metadata rides
        // the memory bus like every other operand: the read is what binds flock's
        // counter and flag inputs.
        for (lane, &(operand, k)) in BLAKE2S_LANE_CELLS.iter().enumerate() {
            f.memory(Prod(FP, operand, k), R0 + lane, Col(V0 + lane));
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
        ctx.cols(out, rows, V0, |r| {
            blake2s_cells(ctx.prog, r.pc, r.fp).map(|a| ctx.cell(a))
        });
        ctx.cols(out, rows, R0, |r| r.r);
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
}
