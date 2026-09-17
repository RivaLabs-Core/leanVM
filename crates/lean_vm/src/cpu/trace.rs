//! Per-opcode trace rows, emitted during execution and assembled into a [`Trace`].
//!
//! Memory is read-write, so a cell's value depends on when it is read: a row carries
//! the values its accesses saw, along with the step's `(pc, fp)`, its clock, and per
//! access what the memory argument needs ([`Access`]). Operands and immediates still
//! come from `prog[pc]`, and addresses from `fp` plus those operands.

use primitives::field::F64;

/// One memory access, as the memory argument sees it (§sec:memchan).
#[derive(Clone, Copy)]
pub(crate) struct Access {
    /// `g^x`, the timestamp of the cell's previous access. Zero on a padding row.
    pub(crate) x: F64,
    /// `y - x - 1` for this access's timestamp `y`: what the two range reads certify
    /// to be below `2^32`.
    pub(crate) gap: u32,
    /// The read counts of the two range-array entries the gap's chunks name.
    pub(crate) count_lo: F64,
    pub(crate) count_hi: F64,
}

impl Access {
    /// A slot still to be filled.
    pub(crate) const EMPTY: Self = Self {
        x: F64::ZERO,
        gap: 0,
        count_lo: F64::ZERO,
        count_hi: F64::ZERO,
    };
}

/// `XOR64`, `MUL64`, `ADD_U64` or `MUL_U64` row: the three cells are `fp·g^{a,b,c}`.
pub(crate) struct Xrow {
    pub(crate) pc: u32,
    pub(crate) fp: u32, // frame base: address = fp + offset, operand = g^offset
    /// The row's clock `g^{4·cycle}`, zero on a padding row.
    pub(crate) ts: F64,
    pub(crate) va: F64,
    pub(crate) vb: F64,
    /// What the destination held before the write.
    pub(crate) vc_old: F64,
    pub(crate) acc: [Access; 3],
    pub(crate) bytecode_read: F64,
}
pub(crate) struct Srow {
    pub(crate) pc: u32,
    pub(crate) fp: u32,
    pub(crate) ts: F64,
    pub(crate) v_old: F64,
    pub(crate) acc: [Access; 1],
    pub(crate) bytecode_read: F64,
}
pub(crate) struct Drow {
    pub(crate) pc: u32,
    pub(crate) fp: u32,
    pub(crate) ts: F64,
    pub(crate) p: F64,
    pub(crate) v3: F64,
    /// What the store target held before the write.
    pub(crate) v2_old: F64,
    /// Pointer, local cell, store target.
    pub(crate) acc: [Access; 3],
    pub(crate) bytecode_read: F64,
}
pub(crate) struct Jrow {
    pub(crate) pc: u32,
    pub(crate) fp: u32,
    pub(crate) ts: F64,
    pub(crate) cond: F64,
    pub(crate) dest: F64,
    pub(crate) frame: F64,
    pub(crate) acc: [Access; 3],
    pub(crate) bytecode_read: F64,
}

/// `BLAKE2s` row: the eighteen cells in the value-lane order of
/// [`crate::tables::BLAKE2S_VALUE_COLS`], the digest lanes holding what was written.
pub(crate) struct Brow {
    pub(crate) pc: u32,
    pub(crate) fp: u32,
    pub(crate) ts: F64,
    pub(crate) w: [F64; 18],
    /// What the four digest cells held before the write.
    pub(crate) out_old: [F64; 4],
    pub(crate) acc: [Access; 18],
    pub(crate) bytecode_read: F64,
}

pub(crate) struct Trace {
    pub(crate) xor64: Vec<Xrow>,
    pub(crate) mul64: Vec<Xrow>,
    pub(crate) set: Vec<Srow>,
    pub(crate) deref: Vec<Drow>,
    pub(crate) jump: Vec<Jrow>,
    pub(crate) blake2s: Vec<Brow>,
    pub(crate) add_u64: Vec<Xrow>,
    pub(crate) mul_u64: Vec<Xrow>,
    /// Per cell, the timestamp `g^y` of its last access; `g^0` if never touched.
    pub(crate) mem_ts: Vec<F64>,
    pub(crate) bytecode_count: Vec<F64>, // per-pc running execution count g^{count}; final = g^{A[pc]}
    /// Final read counts of the two range arrays' entries.
    pub(crate) range_lo_count: Vec<F64>,
    pub(crate) range_hi_count: Vec<F64>,
    /// The clock `g^{4·cycle}` the run ended on: the final state's timestamp.
    pub(crate) ts_final: F64,
}

impl Trace {
    /// Rows per instruction table, in [`crate::cpu::Stats::TABLES`] order.
    pub(crate) fn row_counts(&self) -> [usize; crate::tables::N_TABLES] {
        [
            self.xor64.len(),
            self.mul64.len(),
            self.set.len(),
            self.deref.len(),
            self.jump.len(),
            self.blake2s.len(),
            self.add_u64.len(),
            self.mul_u64.len(),
        ]
    }
}
