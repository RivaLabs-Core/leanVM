//! The instruction tables (`doc/leanvm/body/07-instruction-tables.tex`): one per
//! instruction class ([`crate::rv::Class`]), all of them the same table, which a
//! [`ClassSpec`] specializes. Column indices here are *local*
//! (`0..n_committed_columns`); `cpu`'s schema offsets them to global witness columns.
//!
//! A table does plumbing only. What its class computes is a flock circuit
//! ([`crate::rv::circuits`]), and every word that circuit reads or writes is a
//! VIRTUAL column here: it lives in the circuit's packed witness
//! ([`crate::class_flock`]) and rides the bus from there, in the register tuples and
//! the bytecode tuple, which is all that binds the circuit to the machine. What a
//! row commits of its own is the rest of its bytecode entry, the old value of the
//! register it writes, and per register access the argument that orders it in time
//! (§sec:memchan): the timestamp `X` of the cell's previous access and the two chunks
//! of the gap to the row's own, each a read of a range array.

use crate::colval::ColVal;
use crate::cpu::{Access, Row, Trace};
use crate::leaf::Coord::{self, Col, Const, GCol, Prod};
use crate::rv::{self, Class};
use flock::circuit::Circuit;
use primitives::field::{F64, F192, mul_by_g};

// ---- the identities ----------------------------------------------------------
//
// Written ONCE, generic over the column type: `F64` in the round a table joins the
// batch, `F192` afterwards (see [`ColVal`]). Products of two `K` columns stay
// 64-bit and an `η`-power multiplies through `mul_e`.

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

// Domain separators (coordinate 0 of every bus tuple). `g^1` is RAM's.
pub(crate) const SEP_STATE: F64 = g_pow(0);
pub(crate) const SEP_BYTECODE: F64 = g_pow(2);
pub(crate) const SEP_RANGE_LO: F64 = g_pow(3);
pub(crate) const SEP_RANGE_HI: F64 = g_pow(4);
pub(crate) const SEP_REG: F64 = g_pow(5);

/// Each range array holds `2^RANGE_LOG` entries, so a gap is below `2^(2·RANGE_LOG)`.
pub const RANGE_LOG: usize = 16;

/// The clock advances by this much per instruction, which leaves one timestamp per
/// access slot: `ts = 4·cycle + slot` (§sec:memchan).
pub const CLOCK_STRIDE: u32 = 4;
/// The clock the run starts on: cycle 1, so the first access is strictly after the
/// seeds' `g^0`.
pub const CLOCK_START: F64 = g_pow(CLOCK_STRIDE as usize);
/// A row's clock slots: `rs1`, `rs2`, then `rd` last. Slot 2 is the RAM access's.
pub const REG_SLOTS: [u32; 3] = [0, 1, 3];

/// The low range array's addresses `g^{j+1}`: the `+1` is the strictness of `x < y`.
pub fn range_lo_first() -> F64 {
    F64::G
}
/// The high range array's addresses are the powers of `g^{-2^16}`, from `g^0`.
pub fn range_hi_ratio() -> F64 {
    static RATIO: std::sync::OnceLock<F64> = std::sync::OnceLock::new();
    *RATIO.get_or_init(|| primitives::field::g_pow(1 << RANGE_LOG).inv())
}

/// Where a table keeps its `n` accesses' columns, grouped by kind so that each kind
/// is contiguous: the previous timestamps `X`, the gap's low and high chunks, then
/// the counts of the two range reads.
#[derive(Clone, Copy)]
pub(crate) struct Acc {
    base: usize,
    n: usize,
}

impl Acc {
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

    /// Pull the current state and push the next: `npc`, which a row DERIVES from its
    /// columns rather than committing, and the clock advanced by the stride.
    fn state(&mut self, pc: usize, ts: usize, npc: Coord) {
        self.pair(
            vec![Const(SEP_STATE), npc, GCol(ts, CLOCK_STRIDE)],
            vec![Const(SEP_STATE), Col(pc), Col(ts)],
        );
    }

    /// A read of a lookup array (§sec:lookup): `tuple` as pulled, `tuple[2]` being
    /// its count column `count`, pushed back with the count advanced by ×g.
    fn counted(&mut self, tuple: Vec<Coord>, count: usize) {
        let mut push = tuple.clone();
        push[2] = GCol(count, 1);
        self.pair(push, tuple);
    }

    /// Access `i` of the row, at clock slot `slot` (§sec:memchan), to the cell `addr`
    /// of the array `sep`: pull the cell as its previous access left it, `(X, old)`,
    /// push it back as `(g^{slot}·ts, new)`, and read the gap's two chunks off the
    /// range arrays. A value the row DERIVES rather than commits is passed as its
    /// form (§sec:m3).
    #[allow(clippy::too_many_arguments)]
    fn access(&mut self, sep: F64, addr: Coord, ts: usize, acc: Acc, i: usize, slot: u32, old: Coord, new: Coord) {
        self.pair(
            vec![Const(sep), addr.clone(), GCol(ts, slot), new],
            vec![Const(sep), addr, Col(acc.x(i)), old],
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
}

// ---- fill context ------------------------------------------------------------

/// Inputs a table needs to fill its columns.
pub struct FillCtx<'a> {
    pub(crate) trace: &'a Trace,
    /// The two range arrays' addresses, by chunk.
    pub(crate) range_lo: &'a [F64],
    pub(crate) range_hi: &'a [F64],
    pub(crate) program: &'a rv::Program,
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
        range_lo: &'a [F64],
        range_hi: &'a [F64],
        program: &'a rv::Program,
        rows: usize,
        n_cols: usize,
    ) -> Self {
        Self {
            trace,
            range_lo,
            range_hi,
            program,
            rows,
            written: (0..n_cols).map(|_| false.into()).collect(),
        }
    }

    /// Write local column `at`: `f` over the trace rows.
    fn col<R: Sync>(&self, out: &mut [ColumnOut], rows: &[R], at: usize, f: impl Fn(&R) -> F64 + Sync) {
        self.cols(out, rows, at, |r| [f(r)]);
    }

    /// Write the `N` local columns at `at..at + N` from one closure per row.
    fn cols<const N: usize, R: Sync>(
        &self,
        out: &mut [ColumnOut],
        rows: &[R],
        at: usize,
        f: impl Fn(&R) -> [F64; N] + Sync,
    ) {
        let n = self.rows;
        let dst: [parallel::SendPtr<F64>; N] = std::array::from_fn(|k| {
            assert_eq!(out[at + k].len(), n, "column {} has the wrong window length", at + k);
            self.written[at + k].store(true, std::sync::atomic::Ordering::Relaxed);
            parallel::SendPtr(out[at + k].as_mut_ptr())
        });
        // A table's height is its row count (`cpu::filler`), so there is nothing to
        // pad with.
        assert_eq!(rows.len(), n, "a table's rows must fill its cube");
        parallel::for_each(n, |i| {
            let v = f(&rows[i]);
            for (k, p) in dst.iter().enumerate() {
                // SAFETY: distinct `i` write disjoint in-bounds slots of each of the
                // `N` windows, each exactly once, and the dispatch blocks until
                // every write is finished.
                unsafe { p.add(i).write(v[k]) };
            }
        });
    }

    /// The `5·n` columns of a table's accesses, one kind at a time.
    fn accesses<R: Sync>(&self, out: &mut [ColumnOut], rows: &[R], acc: Acc, f: impl Fn(&R) -> &[Access] + Sync) {
        let mask = (1u32 << RANGE_LOG) - 1;
        for i in 0..acc.n {
            self.col(out, rows, acc.x(i), |r| f(r)[i].x);
            self.col(out, rows, acc.lo(i), |r| self.range_lo[(f(r)[i].gap & mask) as usize]);
            self.col(out, rows, acc.hi(i), |r| {
                self.range_hi[(f(r)[i].gap >> RANGE_LOG) as usize]
            });
            self.col(out, rows, acc.count_lo(i), |r| f(r)[i].count_lo);
            self.col(out, rows, acc.count_hi(i), |r| f(r)[i].count_hi);
        }
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
    /// Number of columns (local indices `0..n_committed_columns`), the virtual ones included.
    fn n_committed_columns(&self) -> usize;
    /// Local indices of this table's read-count columns: the `g^{count}` values of
    /// its lookups into the read-only arrays (the bytecode, the two range arrays).
    /// The framework treats them specially: each gets its own single-column "count"
    /// bus block.
    fn count_columns(&self) -> &[usize];
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
    /// carries every column of a table, in local order, so `cols` is indexed
    /// directly. With `quadratic=false` it returns `0` on every valid row
    /// (§sec:air); `true` selects only the degree-two terms.
    fn eval_constraint(&self, weights: &[F192], cols: &[F192], quadratic: bool) -> F192;
    /// The same identity over `K`-valued columns, for the round a table joins the
    /// batch, before its columns have been folded into `E` (§sec:air). Both entry
    /// points delegate to one generic definition, so they cannot drift.
    fn eval_constraint_k(&self, weights: &[F192], cols: &[F64], quadratic: bool) -> F192;
    /// Declare the table's bus interactions.
    fn flushes(&self, f: &mut FlushBuilder);
    /// Fill this table's columns from the trace: `out[i]` is local column `i`'s
    /// window, already at its final length. Every window must be written in full;
    /// use `FillCtx::col` / `FillCtx::cols`, which record the coverage `fill_table`
    /// checks.
    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]);
}

// ---- the classes -------------------------------------------------------------

/// A word a class's circuit reads or writes, which is a virtual column of its table.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Word {
    /// The bytecode's selector bits and immediate.
    Flags,
    Imm,
    /// The two registers read.
    V1,
    V2,
    /// What the class computes.
    Out,
    /// Whether the branch is taken, 0 or 1.
    Taken,
}

/// What specializes the class table to one instruction class.
pub struct ClassSpec {
    pub class: Class,
    pub name: &'static str,
    /// Branches and jumps: the bytecode's `dt`, `link` and `jalr` fields, and the
    /// circuit's `taken` word. Without them the next `pc` is `pc + 4` and `rd`
    /// receives `out`.
    pub control: bool,
    pub circuit: fn() -> Circuit,
    /// `log2` of the bits one instance of the circuit occupies. A constant, because
    /// the layout needs it before any circuit is built; [`crate::class_flock`] checks it.
    pub k_log: usize,
    /// The circuit's port words in order, the first `n_inputs` of them its inputs.
    pub ports: &'static [Word],
    pub n_inputs: usize,
}

pub static ALU: ClassSpec = ClassSpec {
    class: Class::Alu,
    name: "ALU",
    control: true,
    circuit: rv::circuits::alu,
    k_log: 10,
    ports: &[Word::V1, Word::V2, Word::Imm, Word::Flags, Word::Out, Word::Taken],
    n_inputs: 4,
};

/// The tables, in the order of `row_counts` / `taus` throughout `cpu`. Table `t`'s
/// class tag in the bytecode is `g^t`.
pub const N_TABLES: usize = 1;
pub static CLASSES: [&ClassSpec; N_TABLES] = [&ALU];

/// The table running `class`, if it has one yet.
pub fn table_of(class: Class) -> Option<usize> {
    CLASSES.iter().position(|spec| spec.class == class)
}

pub fn tables() -> [&'static dyn Table; N_TABLES] {
    static TABLES: std::sync::OnceLock<Vec<ClassTable>> = std::sync::OnceLock::new();
    let tables = TABLES.get_or_init(|| (0..N_TABLES).map(ClassTable::new).collect());
    std::array::from_fn(|t| &tables[t] as &dyn Table)
}

/// The local column of each of table `t`'s circuit words, in port order.
pub(crate) fn word_columns(t: usize) -> Vec<usize> {
    let cols = Cols::new(CLASSES[t].control);
    CLASSES[t].ports.iter().map(|&w| cols.word(w)).collect()
}

/// A class table's local columns.
#[derive(Clone, Copy)]
struct Cols {
    pc: usize,
    ts: usize,
    // The bytecode entry's fields that are no circuit word.
    a1: usize,
    a2: usize,
    ad: usize,
    pc4: usize,
    /// `dt`, then `link` and `jalr`.
    control: Option<usize>,
    /// What `ad` held before the write.
    vd_old: usize,
    flags: usize,
    imm: usize,
    v1: usize,
    v2: usize,
    out: usize,
    taken: Option<usize>,
    acc: Acc,
    /// The bytecode read's count, the last column.
    rbc: usize,
}

impl Cols {
    fn new(control: bool) -> Self {
        let mut next = 0;
        let mut take = |n: usize| {
            next += n;
            next - n
        };
        let (pc, ts, a1, a2, ad, pc4) = (take(1), take(1), take(1), take(1), take(1), take(1));
        let control_at = control.then(|| take(3));
        let (vd_old, flags, imm, v1, v2, out) = (take(1), take(1), take(1), take(1), take(1), take(1));
        let taken = control.then(|| take(1));
        let acc = Acc { base: take(15), n: 3 };
        Self {
            pc,
            ts,
            a1,
            a2,
            ad,
            pc4,
            control: control_at,
            vd_old,
            flags,
            imm,
            v1,
            v2,
            out,
            taken,
            acc,
            rbc: take(1),
        }
    }

    fn word(&self, word: Word) -> usize {
        match word {
            Word::Flags => self.flags,
            Word::Imm => self.imm,
            Word::V1 => self.v1,
            Word::V2 => self.v2,
            Word::Out => self.out,
            Word::Taken => self.taken.expect("only a control class has a taken word"),
        }
    }
}

/// The table of one instruction class (§sec:tables): the state step, the bytecode
/// read, two register reads and one register write.
struct ClassTable {
    index: usize,
    spec: &'static ClassSpec,
    cols: Cols,
    counts: Vec<usize>,
}

impl ClassTable {
    fn new(index: usize) -> Self {
        let spec = CLASSES[index];
        let cols = Cols::new(spec.control);
        assert_eq!(cols.rbc, cols.acc.end(), "the counts are the table's last columns");
        Self {
            index,
            spec,
            cols,
            // The accesses' counts end `acc`, and the bytecode's follows.
            counts: (cols.acc.count_lo(0)..=cols.rbc).collect(),
        }
    }

    fn eval<T: ColVal>(&self, w: &[F192], cols: &[T]) -> F192 {
        access_identities(w, cols, self.cols.ts, self.cols.acc)
    }
}

impl Table for ClassTable {
    fn n_committed_columns(&self) -> usize {
        self.cols.rbc + 1
    }
    fn count_columns(&self) -> &[usize] {
        &self.counts
    }
    fn n_constraints(&self) -> usize {
        self.cols.acc.n
    }
    fn constraint_weights(&self, pows: &[F192]) -> Vec<F192> {
        access_weights(pows, &REG_SLOTS)
    }
    fn eval_constraint(&self, w: &[F192], cols: &[F192], _quadratic: bool) -> F192 {
        self.eval(w, cols)
    }
    fn eval_constraint_k(&self, w: &[F192], cols: &[F64], _quadratic: bool) -> F192 {
        self.eval(w, cols)
    }
    fn flushes(&self, f: &mut FlushBuilder) {
        let c = &self.cols;
        // What the row derives: the next `pc`, `pc4 + taken·dt + jalr·(out + pc4)`, and
        // what `rd` receives, `out + link·(out + pc4)`, each of degree 2 (§sec:m3).
        let (npc, vd, control) = match (c.control, c.taken) {
            (Some(dt), Some(taken)) => {
                let (link, jalr) = (dt + 1, dt + 2);
                (
                    Coord::Sum(vec![
                        Col(c.pc4),
                        Prod(taken, dt, 0),
                        Prod(jalr, c.out, 0),
                        Prod(jalr, c.pc4, 0),
                    ]),
                    Coord::Sum(vec![Col(c.out), Prod(link, c.out, 0), Prod(link, c.pc4, 0)]),
                    vec![Col(dt), Col(link), Col(jalr)],
                )
            }
            _ => (Col(c.pc4), Col(c.out), Vec::new()),
        };
        f.state(c.pc, c.ts, npc);
        let mut entry = vec![
            Const(SEP_BYTECODE),
            Col(c.pc),
            Col(c.rbc),
            Const(g_pow(self.index)),
            Col(c.flags),
            Col(c.a1),
            Col(c.a2),
            Col(c.ad),
            Col(c.imm),
            Col(c.pc4),
        ];
        entry.extend(control);
        f.counted(entry, c.rbc);
        let [s1, s2, sd] = REG_SLOTS;
        f.access(SEP_REG, Col(c.a1), c.ts, c.acc, 0, s1, Col(c.v1), Col(c.v1));
        f.access(SEP_REG, Col(c.a2), c.ts, c.acc, 1, s2, Col(c.v2), Col(c.v2));
        f.access(SEP_REG, Col(c.ad), c.ts, c.acc, 2, sd, Col(c.vd_old), vd);
    }
    fn fill(&self, ctx: &FillCtx, out: &mut [ColumnOut]) {
        let c = &self.cols;
        let rows: &[Row] = &ctx.trace.rows[self.index];
        let p = ctx.program;
        let entry = |r: &Row| &p.entries[r.index as usize];
        ctx.cols(out, rows, c.pc, |r| {
            let (e, pc) = (entry(r), p.pc_of(r.index as usize));
            [
                F64(pc),
                r.ts,
                F64(e.a1 as u64),
                F64(e.a2 as u64),
                F64(e.ad as u64),
                F64(pc.wrapping_add(4)),
            ]
        });
        if let Some(dt) = c.control {
            ctx.cols(out, rows, dt, |r| {
                let e = entry(r);
                [F64(p.dt_of(r.index as usize)), F64(e.link as u64), F64(e.jalr as u64)]
            });
        }
        ctx.cols(out, rows, c.vd_old, |r| {
            let e = entry(r);
            [
                F64(r.vd_old),
                F64(e.flags),
                F64(e.imm),
                F64(r.v1),
                F64(r.v2),
                F64(r.out),
            ]
        });
        if let Some(taken) = c.taken {
            ctx.col(out, rows, taken, |r| F64(r.taken as u64));
        }
        ctx.accesses(out, rows, c.acc, |r| &r.acc);
        ctx.col(out, rows, c.rbc, |r| r.bytecode_read);
        debug_assert_eq!(self.spec.ports.len(), word_columns(self.index).len());
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::field::powers;

    /// An access's identity vanishes exactly when the previous timestamp, the two
    /// chunks and the row's own timestamp agree: `x + gap + 1 = 4·cycle + slot`.
    #[test]
    fn access_identity_is_the_strict_gap() {
        use primitives::field::g_pow;
        let table = ClassTable::new(0);
        let (x, cycle, access) = (41usize, 70_000usize, 2usize);
        let slot = REG_SLOTS[access] as usize;
        let gap = CLOCK_STRIDE as usize * cycle + slot - x - 1;
        assert!(gap >> RANGE_LOG > 0, "both chunks are exercised");
        let w = table.constraint_weights(&powers(F192::new(3, 5, 7), 3));
        let row = |gap: usize| {
            // Accesses 0 and 1 stay all-zero, which the identity accepts.
            let mut row = vec![F64::ZERO; table.n_committed_columns()];
            row[table.cols.ts] = g_pow(CLOCK_STRIDE as usize * cycle);
            row[table.cols.acc.x(access)] = g_pow(x);
            row[table.cols.acc.lo(access)] = range_lo_first() * g_pow(gap & 0xffff);
            row[table.cols.acc.hi(access)] = (0..gap >> RANGE_LOG).fold(F64::ONE, |h, _| h * range_hi_ratio());
            row
        };
        assert_eq!(table.eval(&w, &row(gap)), F192::ZERO);
        let lifted: Vec<F192> = row(gap).into_iter().map(F192::from).collect();
        assert_eq!(table.eval(&w, &lifted), F192::ZERO);
        assert_ne!(table.eval(&w, &row(gap + 1)), F192::ZERO);
        assert_ne!(table.eval(&w, &row(gap + (1 << RANGE_LOG))), F192::ZERO);
    }
}
