//! The machine: run the bytecode over read-write memory and record, for every
//! access, what the memory argument needs ([`Trace`]).
//!
//! The memory's initial contents are the public words, then zeros. A program is
//! hand-assembled ([`Program::from_body`]); there is no advice channel yet, so a run
//! is a function of the bytecode and the public input.

use super::*;
use crate::tables::{BLAKE2S_LANES_BY_SLOT, BLAKE2S_STRIDE, CLOCK_STRIDE, RANGE_LOG};
use primitives::field::{F64, mul_by_g};

pub struct Execution {
    /// Data memory before the run (size cells, power of two).
    pub init: Vec<F64>,
    /// Data memory after the run, same size.
    pub mem: Vec<F64>,
    pub cycles: usize,   // number of rows proven, padding rows included
    pub mem_used: usize, // cells actually touched, before the power-of-two pad of `mem`
    /// Rows per table before the padding rows: the work the program itself does, as
    /// against the power-of-two heights that get proven. Cost measurements want this one.
    pub base_counts: [usize; crate::tables::N_TABLES],
    pub(crate) trace: Trace, // rows, final timestamps and counts, emitted in the same walk
}

/// Read-write data memory, and what the memory argument keeps per cell and per
/// range-array entry (§sec:memchan). Every method is `#[inline(always)]`: they sit
/// in the machine's hot opcode loop.
struct Ram {
    init: Vec<F64>,
    cells: Vec<F64>,
    /// Each cell's last access, as the clock's exponent and as its g-power.
    last: Vec<u32>,
    last_ts: Vec<F64>,
    /// Running read counts `g^{count}` of the `EXP` array's entries, one per cell.
    exp: Vec<F64>,
    /// Running read counts `g^{count}` of the two range arrays' entries.
    range_lo: Vec<F64>,
    range_hi: Vec<F64>,
}

impl Ram {
    fn new(image: Vec<F64>) -> Self {
        let mut ram = Self {
            init: image,
            cells: Vec::new(),
            last: Vec::new(),
            last_ts: Vec::new(),
            exp: Vec::new(),
            range_lo: vec![F64::ONE; 1 << RANGE_LOG],
            range_hi: vec![F64::ONE; 1 << RANGE_LOG],
        };
        ram.cells = ram.init.clone();
        ram.resize(ram.init.len());
        ram
    }

    /// Cells past the initial image start at zero, last accessed at the seed's `g^0`.
    fn resize(&mut self, n: usize) {
        self.init.resize(n, F64::ZERO);
        self.cells.resize(n, F64::ZERO);
        self.last.resize(n, 0);
        self.last_ts.resize(n, F64::ONE);
        self.exp.resize(n, F64::ONE);
    }

    /// One read of the `EXP` entry at `index`: every address is read there, and so
    /// is every pointer and loaded frame, which therefore have to be addresses.
    #[inline(always)]
    fn exp_read(&mut self, index: u32) -> F64 {
        if index as usize >= self.exp.len() {
            self.resize(index as usize + 1);
        }
        let count = self.exp[index as usize];
        self.exp[index as usize] = mul_by_g(count);
        count
    }

    #[inline(always)]
    fn get(&mut self, cell: u32) -> F64 {
        if cell as usize >= self.cells.len() {
            self.resize(cell as usize + 1);
        }
        self.cells[cell as usize]
    }

    #[inline(always)]
    fn put(&mut self, cell: u32, v: F64) {
        if cell as usize >= self.cells.len() {
            self.resize(cell as usize + 1);
        }
        self.cells[cell as usize] = v;
    }

    /// One read of each range array, at the chunks of `gap`.
    #[inline(always)]
    fn range_reads(&mut self, gap: u32) -> (F64, F64) {
        let (lo, hi) = ((gap & ((1 << RANGE_LOG) - 1)) as usize, (gap >> RANGE_LOG) as usize);
        let counts = (self.range_lo[lo], self.range_hi[hi]);
        self.range_lo[lo] = mul_by_g(counts.0);
        self.range_hi[hi] = mul_by_g(counts.1);
        counts
    }

    /// Access `cell` at clock `y`, whose g-power is `ts`. The cell must have been
    /// touched by [`Self::get`] or [`Self::put`] already, which sizes the vectors.
    #[inline(always)]
    fn access(&mut self, cell: u32, y: u32, ts: F64) -> Access {
        let c = cell as usize;
        let (x, x_ts) = (self.last[c], self.last_ts[c]);
        // The clock only moves forward, and starts after the seed's zero.
        let gap = y - x - 1;
        let (count_lo, count_hi) = self.range_reads(gap);
        self.last[c] = y;
        self.last_ts[c] = ts;
        Access {
            x: x_ts,
            gap,
            count_exp: self.exp_read(cell),
            count_lo,
            count_hi,
        }
    }

    /// A padding row's access: clock zero on both sides, so the identity holds with
    /// the first entry of each range array. Its address is still read off `EXP`.
    #[inline(always)]
    fn padding_access(&mut self, cell: u32) -> Access {
        let (count_lo, count_hi) = self.range_reads(0);
        Access {
            x: F64::ZERO,
            gap: 0,
            count_exp: self.exp_read(cell),
            count_lo,
            count_hi,
        }
    }
}

impl Program {
    /// Run the program on `public_input`, which seeds the first four memory cells
    /// (§sec:e2e-pi), recording every row, then write out the padding rows that bring
    /// each table to a power of two ([`filler`]).
    pub fn execute(&self, public_input: [F64; 4]) -> Execution {
        let ending_pc = (self.prog.len() - 1) as u32; // last bytecode slot
        // A word read as an address: a pointer, a jump target or a frame.
        let index = |word: F64, bound: usize, what: &str, pc: u32| {
            assert!(
                (word.0 as usize) < bound,
                "{what} 0x{:016x} at pc {pc} is out of range",
                word.0
            );
            word.0 as u32
        };
        let mut m = Ram::new(public_input.to_vec());
        // Per-pc bytecode execution count (g^{count}).
        let mut bytecode_count: Vec<F64> = vec![F64::ONE; self.prog.len()];
        let mut fetch = |pc: u32| {
            let v = bytecode_count[pc as usize];
            bytecode_count[pc as usize] = mul_by_g(v);
            v
        };
        let mut xor64: Vec<Xrow> = Vec::new();
        let mut mul64: Vec<Xrow> = Vec::new();
        let mut set: Vec<Srow> = Vec::new();
        let mut deref: Vec<Drow> = Vec::new();
        let mut jump: Vec<Jrow> = Vec::new();
        let mut blake2s: Vec<Brow> = Vec::new();
        let mut add_u64: Vec<Xrow> = Vec::new();
        let mut mul_u64: Vec<Xrow> = Vec::new();

        let (mut pc, mut fp) = (0u32, 0u32);
        // The clock, as an exponent and as its g-power: cycle 1, so that the first
        // access comes strictly after the memory seed.
        let mut tick = CLOCK_STRIDE;
        let mut ts = crate::tables::CLOCK_START;
        let mut steps = 0usize;
        while pc != ending_pc {
            // A cell's first access is measured from the seed, so the whole run has
            // to fit the range a gap can take (§sec:memchan).
            assert!(
                tick < u32::MAX - BLAKE2S_STRIDE,
                "the run exceeds 2^32 clock ticks, the largest gap the memory argument certifies"
            );
            let bytecode_read = fetch(pc);
            let (ts1, ts2) = (mul_by_g(ts), mul_by_g(mul_by_g(ts)));
            let mut stride = CLOCK_STRIDE;
            let op = self.prog[pc as usize];
            match op {
                Op::Xor64 { a, b, c } | Op::Mul64 { a, b, c } | Op::AddU64 { a, b, c } | Op::MulU64 { a, b, c } => {
                    use crate::arith_flock::Op as U64;
                    let (aa, ab, ac) = (fp + a, fp + b, fp + c);
                    let (va, vb, vc_old) = (m.get(aa), m.get(ab), m.get(ac));
                    let (vc, rows) = match op {
                        Op::Xor64 { .. } => (va + vb, &mut xor64),
                        Op::Mul64 { .. } => (va * vb, &mut mul64),
                        Op::AddU64 { .. } => (U64::Add.apply(va, vb), &mut add_u64),
                        _ => (U64::Mul.apply(va, vb), &mut mul_u64),
                    };
                    m.put(ac, vc);
                    rows.push(Xrow {
                        pc,
                        fp,
                        ts,
                        va,
                        vb,
                        vc_old,
                        acc: [
                            m.access(aa, tick, ts),
                            m.access(ab, tick + 1, ts1),
                            m.access(ac, tick + 2, ts2),
                        ],
                        bytecode_read,
                    });
                    pc += 1;
                }
                Op::Set { o, k } => {
                    let a = fp + o;
                    let v_old = m.get(a);
                    m.put(a, k);
                    set.push(Srow {
                        pc,
                        fp,
                        ts,
                        v_old,
                        acc: [m.access(a, tick, ts)],
                        bytecode_read,
                    });
                    pc += 1;
                }
                Op::Deref { o1, o2, o3, mode } => {
                    let (a1, a3) = (fp + o1, fp + o3);
                    let (p, v3) = (m.get(a1), m.get(a3));
                    let a2 = index(p, 1 << MAX_LOG_MEM, "DEREF pointer", pc) + o2;
                    let v2_old = m.get(a2);
                    m.put(
                        a2,
                        match mode {
                            DerefMode::Cell => v3,
                            // The return target and the frame base are stored as
                            // integers, and JUMP reads them back.
                            DerefMode::Pc => mode.ret(pc),
                            DerefMode::Fp => F64(fp as u64),
                        },
                    );
                    deref.push(Drow {
                        pc,
                        fp,
                        ts,
                        p,
                        v3,
                        v2_old,
                        acc: [
                            m.access(a1, tick, ts),
                            m.access(a3, tick + 1, ts1),
                            m.access(a2, tick + 2, ts2),
                        ],
                        count_px: m.exp_read(p.0 as u32),
                        bytecode_read,
                    });
                    pc += 1;
                }
                Op::Jump { oc, od, of } => {
                    let (ac, ad, af) = (fp + oc, fp + od, fp + of);
                    let (cond, dest, frame) = (m.get(ac), m.get(ad), m.get(af));
                    // The is-nonzero witness `w = c⁻¹` is never used for control
                    // flow, only recorded as a witness column, so it is not
                    // computed here at all: `JumpTable::fill` batch-inverts every
                    // row's condition at once.
                    let next = if cond.is_zero() {
                        (pc + 1, fp)
                    } else {
                        (
                            index(dest, self.prog.len(), "JUMP target", pc),
                            index(frame, 1 << MAX_LOG_MEM, "JUMP frame", pc),
                        )
                    };
                    jump.push(Jrow {
                        pc,
                        fp,
                        ts,
                        cond,
                        dest,
                        frame,
                        acc: [
                            m.access(ac, tick, ts),
                            m.access(ad, tick + 1, ts1),
                            m.access(af, tick + 2, ts2),
                        ],
                        // A jump not taken loads no frame, and reads entry 0.
                        count_fpx: m.exp_read(if cond.is_zero() { 0 } else { next.1 }),
                        bytecode_read,
                    });
                    (pc, fp) = next;
                }
                Op::Blake2s { .. } => {
                    // Every cell the row touches, in value-lane order: the message
                    // chunks, the digest, the chaining value, the metadata. All of
                    // them are read before the digest is written, so it may land on
                    // a cell the compression read.
                    let cells = crate::tables::blake2s_cells(&self.prog, pc, fp);
                    let mut w = cells.map(|a| m.get(a));
                    let out_old = [w[8], w[9], w[10], w[11]];
                    // No table constraint covers the digest: the relation is proven
                    // by flock (§hash_flock).
                    let digest = blake2s_compress(
                        [w[0], w[1], w[2], w[3]],
                        [w[4], w[5], w[6], w[7]],
                        [w[12], w[13], w[14], w[15]],
                        [w[16], w[17]],
                    );
                    for (k, &word) in digest.iter().enumerate() {
                        m.put(cells[8 + k], word);
                        w[8 + k] = word;
                    }
                    let mut acc = [Access::EMPTY; 18];
                    let mut y = ts;
                    for (slot, &lane) in BLAKE2S_LANES_BY_SLOT.iter().enumerate() {
                        acc[lane] = m.access(cells[lane], tick + slot as u32, y);
                        y = mul_by_g(y);
                    }
                    blake2s.push(Brow {
                        pc,
                        fp,
                        ts,
                        w,
                        out_old,
                        acc,
                        bytecode_read,
                    });
                    stride = BLAKE2S_STRIDE;
                    pc += 1;
                }
            }
            tick += stride;
            for _ in 0..stride {
                ts = mul_by_g(ts);
            }
            steps += 1;
        }
        assert_eq!(fp, 0, "main must halt at the last pc in frame 0");
        let base_counts = [
            xor64.len(),
            mul64.len(),
            set.len(),
            deref.len(),
            jump.len(),
            blake2s.len(),
            add_u64.len(),
            mul_u64.len(),
        ];

        // The padding rows, written out rather than executed: they sit at clock zero
        // and touch no memory, every read holding zero and every write rewriting what
        // was there (`filler`). Only a block's closing jump holds anything else: a
        // nonzero condition, and its own block's top as the destination, in frame 0.
        // Their addresses are still read off `EXP`, which those reads count.
        // A hand-assembled program carries no blocks and has to land on powers of two
        // by itself, which `Layout` checks.
        if !self.filler.is_empty() {
            let zero_digest = blake2s_compress([F64::ZERO; 4], [F64::ZERO; 4], [F64::ZERO; 4], [F64::ZERO; 2]);
            for (block_pc, size, traversals) in super::filler::cycles(&self.filler, base_counts) {
                let top = F64(block_pc as u64);
                for _ in 0..traversals {
                    for pc in block_pc..=block_pc + size {
                        let bytecode_read = fetch(pc);
                        let (fp, ts) = (0, F64::ZERO);
                        let closing = pc == block_pc + size;
                        match self.prog[pc as usize] {
                            // Zero operands, and zero is the result of all four.
                            op @ (Op::Xor64 { a, b, c }
                            | Op::Mul64 { a, b, c }
                            | Op::AddU64 { a, b, c }
                            | Op::MulU64 { a, b, c }) => {
                                let rows = match op {
                                    Op::Xor64 { .. } => &mut xor64,
                                    Op::Mul64 { .. } => &mut mul64,
                                    Op::AddU64 { .. } => &mut add_u64,
                                    _ => &mut mul_u64,
                                };
                                rows.push(Xrow {
                                    pc,
                                    fp,
                                    ts,
                                    va: F64::ZERO,
                                    vb: F64::ZERO,
                                    vc_old: F64::ZERO,
                                    acc: [a, b, c].map(|cell| m.padding_access(cell)),
                                    bytecode_read,
                                });
                            }
                            Op::Set { o, k } => set.push(Srow {
                                pc,
                                fp,
                                ts,
                                v_old: k,
                                acc: [m.padding_access(o)],
                                bytecode_read,
                            }),
                            // A null pointer, and the store rewrites what it stores.
                            Op::Deref { o1, o2, o3, mode } => deref.push(Drow {
                                pc,
                                fp,
                                ts,
                                p: F64::ZERO,
                                v3: F64::ZERO,
                                v2_old: mode.ret(pc),
                                acc: [o1, o3, o2].map(|cell| m.padding_access(cell)),
                                count_px: m.exp_read(0),
                                bytecode_read,
                            }),
                            Op::Jump { oc, od, of } => jump.push(Jrow {
                                pc,
                                fp,
                                ts,
                                cond: if closing { F64::ONE } else { F64::ZERO },
                                dest: if closing { top } else { F64::ZERO },
                                frame: F64::ZERO,
                                acc: [oc, od, of].map(|cell| m.padding_access(cell)),
                                count_fpx: m.exp_read(0),
                                bytecode_read,
                            }),
                            Op::Blake2s { .. } => {
                                let mut w = [F64::ZERO; 18];
                                w[8..12].copy_from_slice(&zero_digest);
                                blake2s.push(Brow {
                                    pc,
                                    fp,
                                    ts,
                                    w,
                                    out_old: zero_digest,
                                    acc: crate::tables::blake2s_cells(&self.prog, pc, fp)
                                        .map(|cell| m.padding_access(cell)),
                                    bytecode_read,
                                });
                            }
                        }
                        steps += 1;
                    }
                }
            }
        }

        // Pad memory to a power of two (the boundary tables read a dense image),
        // at least 2^MIN_LOG_MEM cells (doc §Memory).
        let mem_used = m.cells.len();
        let cells = mem_used.next_power_of_two().max(1 << MIN_LOG_MEM);
        assert!(cells <= 1 << MAX_LOG_MEM, "data memory exceeds 2^{MAX_LOG_MEM} cells");
        m.resize(cells);
        let trace = Trace {
            xor64,
            mul64,
            set,
            deref,
            jump,
            blake2s,
            add_u64,
            mul_u64,
            mem_ts: m.last_ts,
            bytecode_count,
            exp_count: m.exp,
            range_lo_count: m.range_lo,
            range_hi_count: m.range_hi,
            ts_final: ts,
        };
        Execution {
            init: m.init,
            mem: m.cells,
            cycles: steps,
            mem_used,
            base_counts,
            trace,
        }
    }
}
