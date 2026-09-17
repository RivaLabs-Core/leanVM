//! Run the program on the reference interpreter ([`crate::rv::Machine`]) and record,
//! for every access, what the memory argument needs ([`Trace`]).

use super::*;
use crate::rv::{self, LOG_REGS, Machine, Trap, semantics};
use crate::tables::{CLOCK_STRIDE, RANGE_LOG, REG_SLOTS};
use primitives::field::{F64, mul_by_g};

pub struct Execution {
    /// The public output: `a0..a3` as the run left them.
    pub output: [u64; 4],
    pub cycles: usize, // number of rows proven, padding rows included
    /// Rows per table before the padding rows: the work the program itself does, as
    /// against the power-of-two heights that get proven. Cost measurements want this one.
    pub base_counts: [usize; crate::tables::N_TABLES],
    pub(crate) trace: Trace, // rows, final timestamps and counts, emitted in the same walk
}

/// Running read counts `g^{count}` of the two range arrays' entries, which every
/// read-write array's gap checks share.
struct Ranges {
    lo: Vec<F64>,
    hi: Vec<F64>,
}

impl Ranges {
    /// One read of each range array, at the chunks of `gap`.
    #[inline(always)]
    fn read(&mut self, gap: u32) -> (F64, F64) {
        let (lo, hi) = ((gap & ((1 << RANGE_LOG) - 1)) as usize, (gap >> RANGE_LOG) as usize);
        let counts = (self.lo[lo], self.hi[hi]);
        self.lo[lo] = mul_by_g(counts.0);
        self.hi[hi] = mul_by_g(counts.1);
        counts
    }
}

/// What the memory argument keeps per cell of one read-write array (§sec:memchan):
/// its last access, as the clock's exponent and as its g-power.
struct Cells {
    last: Vec<u32>,
    last_ts: Vec<F64>,
}

impl Cells {
    /// Every cell starts last accessed at the seed's `g^0`.
    fn new(n: usize) -> Self {
        Self {
            last: vec![0; n],
            last_ts: vec![F64::ONE; n],
        }
    }

    /// Access `cell` at clock `y`, whose g-power is `ts`.
    #[inline(always)]
    fn access(&mut self, ranges: &mut Ranges, cell: usize, y: u32, ts: F64) -> Access {
        let (x, x_ts) = (self.last[cell], self.last_ts[cell]);
        // The clock only moves forward, and starts after the seed's zero.
        let gap = y - x - 1;
        let (count_lo, count_hi) = ranges.read(gap);
        self.last[cell] = y;
        self.last_ts[cell] = ts;
        Access {
            x: x_ts,
            gap,
            count_lo,
            count_hi,
        }
    }
}

/// A padding row's access: clock zero on both sides, so the identity holds with the
/// first entry of each range array.
fn padding_access(ranges: &mut Ranges) -> Access {
    let (count_lo, count_hi) = ranges.read(0);
    Access {
        x: F64::ZERO,
        gap: 0,
        count_lo,
        count_hi,
    }
}

/// `ts·g^k`.
fn advance(ts: F64, k: u32) -> F64 {
    (0..k).fold(ts, |t, _| mul_by_g(t))
}

impl Program {
    /// Run the program, recording every row, then write out the padding rows that
    /// bring each table to a power of two ([`filler`]). A run that traps has no proof.
    pub fn execute(&self) -> Result<Execution, Trap> {
        let p = &self.rv;
        let mut m = Machine::new(p);
        let mut ranges = Ranges {
            lo: vec![F64::ONE; 1 << RANGE_LOG],
            hi: vec![F64::ONE; 1 << RANGE_LOG],
        };
        let mut regs = Cells::new(1 << LOG_REGS);
        // Per-pc bytecode execution count (g^{count}).
        let mut bytecode_count: Vec<F64> = vec![F64::ONE; p.entries.len()];
        let mut fetch = |index: usize| {
            let v = bytecode_count[index];
            bytecode_count[index] = mul_by_g(v);
            v
        };
        let mut rows: [Vec<Row>; crate::tables::N_TABLES] = std::array::from_fn(|_| Vec::new());

        // The clock, as an exponent and as its g-power: cycle 1, so that the first
        // access comes strictly after the seeds.
        let mut tick = CLOCK_STRIDE;
        let mut ts = crate::tables::CLOCK_START;
        while !m.halted() {
            // A cell's first access is measured from the seed, so the whole run has
            // to fit the range a gap can take (§sec:memchan).
            if tick >= u32::MAX - CLOCK_STRIDE {
                return Err(Trap::CycleCap);
            }
            let step = m.step()?;
            let e = &p.entries[step.index];
            let table = crate::tables::table_of(e.class)
                .unwrap_or_else(|| panic!("no table proves {:?} yet (pc {:#x})", e.class, p.pc_of(step.index)));
            let acc = [e.a1, e.a2, e.ad].map(|cell| cell as usize);
            let acc = std::array::from_fn(|i| {
                regs.access(&mut ranges, acc[i], tick + REG_SLOTS[i], advance(ts, REG_SLOTS[i]))
            });
            rows[table].push(Row {
                index: step.index as u32,
                ts,
                v1: step.v1,
                v2: step.v2,
                out: step.out,
                taken: step.taken,
                vd_old: step.vd_old,
                acc,
                bytecode_read: fetch(step.index),
            });
            tick += CLOCK_STRIDE;
            ts = advance(ts, CLOCK_STRIDE);
        }
        let syscall = m.regs[rv::SYSCALL_REG as usize];
        if syscall != rv::SYS_EXIT {
            return Err(Trap::NotAnExit { syscall });
        }
        let output = rv::OUTPUT_REGS.map(|r| m.regs[r as usize]);
        let base_counts: [usize; crate::tables::N_TABLES] = std::array::from_fn(|t| rows[t].len());

        // The padding rows, written out rather than executed: they sit at clock zero
        // and touch no register, every read holding zero and the write rewriting what
        // it writes (`filler`). Their circuit instance is an honest one, on those zeros.
        for (first, size, traversals) in super::filler::cycles(&self.filler, base_counts) {
            for _ in 0..traversals {
                for index in first..=first + size {
                    let e = &p.entries[index];
                    let table = crate::tables::table_of(e.class).expect("a fill block's class has a table");
                    let (out, taken) = match e.class {
                        rv::Class::Alu => semantics::alu(0, 0, e.imm, e.flags),
                        class => unreachable!("no fill block of {class:?}"),
                    };
                    rows[table].push(Row {
                        index: index as u32,
                        ts: F64::ZERO,
                        v1: 0,
                        v2: 0,
                        out,
                        taken,
                        vd_old: if e.link { p.pc_of(index) + 4 } else { out },
                        acc: std::array::from_fn(|_| padding_access(&mut ranges)),
                        bytecode_read: fetch(index),
                    });
                }
            }
        }

        let cycles = rows.iter().map(Vec::len).sum();
        let trace = Trace {
            rows,
            reg_fin: m.regs.iter().map(|&r| F64(r)).collect(),
            reg_ts: regs.last_ts,
            bytecode_count,
            range_lo_count: ranges.lo,
            range_hi_count: ranges.hi,
            ts_final: ts,
        };
        Ok(Execution {
            output,
            cycles,
            base_counts,
            trace,
        })
    }
}
