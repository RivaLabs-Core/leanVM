//! The ISA and the `DEREF` store modes.

use primitives::field::F64;

/// One instruction (§sec:vm). Every `u32` operand is an offset into the current
/// frame: `m[x]` below is the cell `fp + x`. Cells, `pc` and `fp` are numbered
/// `0, 1, 2, ...`, and a word used as a pointer, a jump target or a frame holds that
/// integer, `F64(i)`.
#[derive(Clone, Copy, Debug)]
pub enum Op {
    /// `m[c] = m[a] + m[b]` in `K`.
    Xor64 { a: u32, b: u32, c: u32 },
    /// `m[c] = m[a] · m[b]` in `K`.
    Mul64 { a: u32, b: u32, c: u32 },
    /// `m[o] = k`.
    Set { o: u32, k: F64 },
    /// A store through a pointer: the cell `m[o1] + o2`, an absolute address, receives
    /// `m[o3]`, `pc + 2` or `fp` according to `mode`. `m[o3]` is read in every mode.
    Deref { o1: u32, o2: u32, o3: u32, mode: DerefMode },
    /// If `m[oc]` is nonzero, continue at `pc = m[od]` in the frame `fp = m[of]`;
    /// otherwise fall through. A call is a `Deref` in `Pc` mode then a `Jump`, which
    /// returns to the instruction after the `Jump`.
    Jump { oc: u32, od: u32, of: u32 },
    /// One standard BLAKE2s compression. Each message chunk `ins[i]` names two
    /// consecutive 64-bit cells, so the 64-byte block is addressed as four
    /// independent 128-bit chunks. The chaining value and the digest each span
    /// four consecutive cells, the metadata `counter | f0 ‖ f1` two. The
    /// compression relation is proven by flock.
    Blake2s { ins: [u32; 4], cv: u32, out: u32, md: u32 },
    /// `m[c] = m[a] + m[b] mod 2^64`, the three words read as unsigned integers.
    AddU64 { a: u32, b: u32, c: u32 },
    /// `m[c] = m[a] · m[b] mod 2^64`.
    MulU64 { a: u32, b: u32, c: u32 },
}

/// The source `DEREF` stores at `mem[loc_o1 + o2]`: a local cell, the return
/// address `pc + 2`, or the frame pointer. Encoded as two boolean flags `(f_pc,
/// f_fp)`: `Cell=(0,0)`, `Pc=(1,0)`, `Fp=(0,1)`, keeping the store constraint degree 2.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DerefMode {
    Cell,
    Pc,
    Fp,
}

impl DerefMode {
    pub(crate) fn f_pc(self) -> F64 {
        if self == DerefMode::Pc { F64::ONE } else { F64::ZERO }
    }
    pub(crate) fn f_fp(self) -> F64 {
        if self == DerefMode::Fp { F64::ONE } else { F64::ZERO }
    }
    /// The return address the bytecode entry at `pc` carries: `pc + 2` in `Pc` mode,
    /// zero otherwise.
    pub(crate) fn ret(self, pc: u32) -> F64 {
        if self == DerefMode::Pc {
            F64(pc as u64 + 2)
        } else {
            F64::ZERO
        }
    }
}
