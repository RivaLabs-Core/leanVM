//! Per-opcode trace rows, emitted during execution and assembled into a [`Trace`].
//!
//! A row carries only what the witness fill cannot recover: the step's
//! `(pc, fp)` and the access counts read at access time. Everything else is a
//! function of those: operands and immediates come from `prog[pc]`, addresses
//! from `fp` plus those operands, and values from the final memory image, which
//! is write-once and so still holds what each accessed cell held at the time it
//! was accessed. The rows are the interpreter's largest write stream, so what
//! they do not carry they do not pay for, twice: once writing them and once
//! reading them back.

use primitives::field::F64;

/// `XOR64` or `MUL64` row: the three cells are `fp·g^{a,b,c}`.
pub(crate) struct Xrow {
    pub(crate) pc: u32,
    pub(crate) fp: u32, // frame base: address = fp + offset, operand = g^offset
    pub(crate) ra: F64,
    pub(crate) rb: F64,
    pub(crate) rc: F64,
    pub(crate) bytecode_read: F64,
}
/// `XOR192` or `MUL192` row: one count per limb cell of each operand.
pub(crate) struct X3row {
    pub(crate) pc: u32,
    pub(crate) fp: u32,
    pub(crate) ra: [F64; 3],
    pub(crate) rb: [F64; 3],
    pub(crate) rc: [F64; 3],
    pub(crate) bytecode_read: F64,
}
pub(crate) struct Srow {
    pub(crate) pc: u32,
    pub(crate) fp: u32,
    pub(crate) r: F64,
    pub(crate) bytecode_read: F64,
}
pub(crate) struct Drow {
    pub(crate) pc: u32,
    pub(crate) fp: u32,
    pub(crate) r1: F64,
    pub(crate) r2: F64,
    pub(crate) r3: F64,
    pub(crate) bytecode_read: F64,
}
pub(crate) struct Jrow {
    pub(crate) pc: u32,
    pub(crate) fp: u32,
    pub(crate) rc: F64,
    pub(crate) rd: F64,
    pub(crate) rf: F64,
    pub(crate) bytecode_read: F64,
}

/// `BLAKE2s` row: one access count per cell, in the value-lane order of
/// [`crate::tables::BLAKE2S_VALUE_COLS`].
pub(crate) struct Brow {
    pub(crate) pc: u32,
    pub(crate) fp: u32,
    pub(crate) r: [F64; 18],
    pub(crate) bytecode_read: F64,
}

pub(crate) struct Trace {
    pub(crate) xor64: Vec<Xrow>,
    pub(crate) mul64: Vec<Xrow>,
    pub(crate) set: Vec<Srow>,
    pub(crate) deref: Vec<Drow>,
    pub(crate) jump: Vec<Jrow>,
    pub(crate) blake2s: Vec<Brow>,
    pub(crate) xor192: Vec<X3row>,
    pub(crate) mul192: Vec<X3row>,
    pub(crate) mem_count: Vec<F64>, // per-cell running access count g^{count}; final = g^{A[i]}
    pub(crate) bytecode_count: Vec<F64>, // per-pc running execution count g^{count}; final = g^{A[pc]}
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
            self.xor192.len(),
            self.mul192.len(),
        ]
    }
}
