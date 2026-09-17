//! Filling every table to a power of two with padding rows at clock zero.
//!
//! A table is proven over a power-of-two number of rows, so a run whose counts are not
//! powers of two has to make up the difference. The bytecode carries, per table and per
//! size in [`SIZES`], a *block*: that many dummy instructions of the table's opcode,
//! then a `JUMP` back to the block's own first instruction ([`append_blocks`]).
//!
//! So a block is a **cycle**, and no program code jumps into it. Its rows carry the
//! clock `ts = 0`, which is what makes it balance: `0·g^k = 0`, so the state tuples
//! pushed and pulled around the cycle cancel among themselves for any number of
//! traversals, where a real clock would have moved on. And zero is no power of `g`, so
//! nothing such a row puts on the bus can meet a tuple of the run itself: its memory
//! accesses are forced to the previous timestamp `0` as well, and each cancels against
//! itself (doc §Filling the tables). The rows therefore touch no memory, and the prover
//! writes them out rather than executing anything.
//!
//! A traversal of the size-`s` block costs exactly `s + 1` rows: `s` of its own table and
//! one `JUMP`. Nothing else, and nothing on any other table. That is what makes the solve
//! here exact, with no calibrated cost model and no residual to correct.
//!
//! The sizes are powers of two so any fill is reachable exactly, while the bulk rides the
//! largest block at one `JUMP` per 128 rows. A table already sitting on a power of two is
//! never entered at all.

use super::Op;
use crate::tables::N_TABLES;

/// Block sizes, largest first: a fill of `f` rows takes `f / 128` traversals of the
/// largest block and then one per set bit of the remainder.
pub const SIZES: [usize; 8] = [128, 64, 32, 16, 8, 4, 2, 1];

/// Least rows a table can be proven over. Only the flock-backed tables have one above
/// `1`: flock sizes a batch to at least eight instances and its zerocheck to a cube of
/// at least `2^13` bits, which is thirty-two instances of the adder's small block
/// ([`crate::arith_flock::n_blocks_log`]). Filling such a table below its floor would
/// leave it padded up to it, which is the padding this exists to avoid.
pub const MIN_ROWS: [usize; N_TABLES] = [
    1,
    1,
    1,
    1,
    1,
    8,
    1 << crate::arith_flock::n_blocks_log(crate::arith_flock::Op::Add, 1),
    1 << crate::arith_flock::n_blocks_log(crate::arith_flock::Op::Mul, 1),
];

/// The `JUMP` table's index in [`crate::cpu::Stats::TABLES`]. Every traversal of every
/// block lands its closing jump here, so this table is solved last, absorbing the cost
/// of the whole fill.
pub const JUMP: usize = 4;

/// One block in the bytecode: `size` dummy rows of `table`'s opcode at `pc`, then the
/// jump back to `pc`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Block {
    pub pc: u32,
    pub size: u32,
    pub table: u8,
}

/// The dummy instruction of table `t`: every operand names cell zero, which a
/// padding row never touches for real.
fn dummy(t: usize) -> Op {
    match t {
        0 => Op::Xor64 { a: 0, b: 0, c: 0 },
        1 => Op::Mul64 { a: 0, b: 0, c: 0 },
        2 => Op::Set {
            o: 0,
            k: primitives::field::F64::ZERO,
        },
        3 => Op::Deref {
            o1: 0,
            o2: 0,
            o3: 0,
            mode: super::DerefMode::Cell,
        },
        4 => Op::Jump { oc: 0, od: 0, of: 0 },
        5 => Op::Blake2s {
            ins: [0; 4],
            cv: 0,
            out: 0,
            md: 0,
        },
        6 => Op::AddU64 { a: 0, b: 0, c: 0 },
        7 => Op::MulU64 { a: 0, b: 0, c: 0 },
        _ => unreachable!("table {t}"),
    }
}

/// Append every table's blocks to `prog`, returning where each one landed.
pub fn append_blocks(prog: &mut Vec<Op>) -> Vec<Block> {
    let mut blocks = Vec::new();
    for t in 0..N_TABLES {
        for size in SIZES {
            blocks.push(Block {
                pc: prog.len() as u32,
                size: size as u32,
                table: t as u8,
            });
            prog.extend(std::iter::repeat_n(dummy(t), size));
            // The closing jump, which a padding row takes back to the block's top.
            prog.push(dummy(JUMP));
        }
    }
    blocks
}

/// Traversals per block: `plan[t][k]` is how many times the size-`SIZES[k]` block of
/// table `t` is traversed.
pub type Plan = [[usize; SIZES.len()]; N_TABLES];

/// Traversals in total, which is the number of `JUMP` rows the fill costs.
pub fn traversals(plan: &Plan) -> usize {
    plan.iter().flatten().sum()
}

/// The fill a plan delivers to each table, not counting the closing jumps.
fn delivered(plan: &Plan) -> [usize; N_TABLES] {
    let mut out = [0usize; N_TABLES];
    for (t, row) in plan.iter().enumerate() {
        for (k, &n) in row.iter().enumerate() {
            out[t] += n * SIZES[k];
        }
    }
    out
}

/// Traversals delivering exactly `fill` rows: as many of the largest block as fit, then
/// the binary decomposition of what is left.
fn decompose(fill: usize) -> [usize; SIZES.len()] {
    let mut out = [0usize; SIZES.len()];
    let mut left = fill;
    for (k, &s) in SIZES.iter().enumerate() {
        out[k] = left / s;
        left -= out[k] * s;
    }
    debug_assert_eq!(left, 0, "the sizes end at 1, so nothing can be left over");
    out
}

/// The smallest power of two that is at least `n`, and at least `1`.
fn ceil_pow2(n: usize) -> usize {
    n.max(1).next_power_of_two()
}

/// Traversals whose rows land on `JUMP` itself, delivering exactly `gap` rows. A
/// traversal of the size-`s` block gives that table `s + 1` rows here, its dummies plus
/// its own closing jump, so the sizes to decompose over are `s + 1`, which are not powers
/// of two. `2` and `3` are among them, so every gap but `1` is reachable; a gap of `1`
/// returns `None` and the caller takes a larger target.
fn decompose_jump(gap: usize) -> Option<[usize; SIZES.len()]> {
    if gap == 1 {
        return None;
    }
    let mut out = [0usize; SIZES.len()];
    let mut left = gap;
    for (k, &s) in SIZES.iter().enumerate() {
        // Never leave exactly one row behind, which nothing can deliver.
        while left > s && left - (s + 1) != 1 {
            out[k] += 1;
            left -= s + 1;
        }
    }
    (left == 0).then_some(out)
}

/// A plan taking every table from `base` to an exact power of two, or `None` if some
/// table cannot be filled at all.
///
/// Every table but `JUMP` is independent: its fill is the distance to its next power of
/// two, decomposed into traversals. `JUMP` is not, because every traversal of the whole
/// fill lands a row there, its own traversals included. Counting those first makes it a
/// single decomposition rather than a fixpoint.
pub fn solve(base: [usize; N_TABLES]) -> Option<Plan> {
    let mut plan: Plan = [[0; SIZES.len()]; N_TABLES];
    for t in 0..N_TABLES {
        if t != JUMP {
            plan[t] = decompose(ceil_pow2(base[t].max(MIN_ROWS[t])) - base[t]);
        }
    }
    // What `JUMP` already owes: its own rows, plus one per traversal so far.
    let owed = base[JUMP] + traversals(&plan);
    let mut target = ceil_pow2(owed.max(MIN_ROWS[JUMP]));
    loop {
        if let Some(jump_steps) = decompose_jump(target - owed) {
            plan[JUMP] = jump_steps;
            debug_assert!(is_filled(filled(base, &plan)));
            return Some(plan);
        }
        target = target.checked_mul(2)?;
    }
}

/// The cycles a run needs, in the order the interpreter should walk them: for each, the
/// block's first pc, its size, and how many times to traverse it. Panics if `blocks` is
/// missing one the plan calls for, which can only mean bytecode that was assembled without them.
pub fn cycles(blocks: &[Block], base: [usize; N_TABLES]) -> Vec<(u32, u32, usize)> {
    let plan = solve(base).unwrap_or_else(|| panic!("no fill plan from {base:?}"));
    let mut out = Vec::new();
    for (t, row) in plan.iter().enumerate() {
        for (k, &n) in row.iter().enumerate() {
            if n == 0 {
                continue;
            }
            let size = SIZES[k] as u32;
            let block = blocks
                .iter()
                .find(|b| b.table as usize == t && b.size == size)
                .unwrap_or_else(|| panic!("the program has no fill block for table {t}, size {size}"));
            out.push((block.pc, size, n));
        }
    }
    out
}

/// The row counts a plan produces from `base`: its fill, plus one `JUMP` per traversal.
pub fn filled(base: [usize; N_TABLES], plan: &Plan) -> [usize; N_TABLES] {
    let mut out = base;
    for (t, add) in delivered(plan).into_iter().enumerate() {
        out[t] += add;
    }
    out[JUMP] += traversals(plan);
    out
}

/// Every table an exact power of two, at or above its floor: what a run has to look
/// like to be provable at all.
pub fn is_filled(counts: [usize; N_TABLES]) -> bool {
    counts
        .iter()
        .enumerate()
        .all(|(u, &c)| c.is_power_of_two() && c >= MIN_ROWS[u])
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Whatever the shape of the run, every table comes out an exact power of two at or
    /// above its floor.
    #[test]
    fn solve_reaches_power_of_two_floors() {
        let cases: [[usize; N_TABLES]; 6] = [
            [0; N_TABLES],
            [1; N_TABLES],
            [125_000, 286_000, 341_000, 508_000, 114_000, 130_000, 90_000, 70_000],
            // Tables already exactly on a power of two, the awkward case: the closing
            // jumps of every other table's traversals still have to fit somewhere.
            [1 << 17, 1 << 12, 1000, 1 << 19, 1 << 16, 8, 1 << 10, 1 << 11],
            [1, 2, 3, 4, 5, 6, 7, 8],
            [0, 0, 0, 0, 1 << 20, 0, 0, 0],
        ];
        for base in cases {
            let plan = solve(base).unwrap_or_else(|| panic!("no plan for {base:?}"));
            let got = filled(base, &plan);
            assert!(is_filled(got), "{base:?} filled to {got:?}");
            for t in 0..N_TABLES {
                assert!(got[t] >= base[t], "rows cannot be removed");
            }
        }
    }

    /// The bulk of a fill rides the largest block, so the fill stays cheap: one closing
    /// jump per 128 rows, plus at most one traversal per size per table for the
    /// remainders.
    #[test]
    fn fill_uses_bulk_blocks() {
        let base = [125_000, 286_000, 341_000, 508_000, 114_000, 130_000, 90_000, 70_000];
        let plan = solve(base).expect("solvable");
        let fill: usize = delivered(&plan).iter().sum();
        assert!(
            traversals(&plan) <= fill / SIZES[0] + SIZES.len() * N_TABLES,
            "{} traversals for {fill} rows",
            traversals(&plan)
        );
    }
}
