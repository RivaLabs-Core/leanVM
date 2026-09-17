//! The write-once execution interpreter: run the compiled program to produce
//! the final memory image and the per-opcode [`Trace`].

use std::collections::HashMap;

use super::*;
use primitives::{
    field::{F64, F192, mul_by_g},
    pretty_f64, pretty_integer,
};

pub struct Execution {
    pub mem: Vec<F64>,   // data memory after the run, write-once (size cells, power of two)
    pub cycles: usize,   // number of instructions the run executed (trace length)
    pub mem_used: usize, // cells actually touched, before the power-of-two pad of `mem`
    /// Rows per table before the fill blocks ran: the work the program itself does, as
    /// against the power-of-two heights that get proven. Cost measurements want this one.
    pub base_counts: [usize; crate::tables::N_TABLES],
    /// Cells an instruction read that nothing ever wrote, so the value it read was
    /// ZERO here and prover-chosen in a proof: memory is a committed array and the
    /// bus only forces accesses to one address to *agree*, never that the address
    /// was written. `zkDSL.md` says don't; this is what says whether the emitted
    /// code did. A non-empty list means a live value came from outside the
    /// constraint system, so an `assert` on it is vacuous and a published value is
    /// free, which is a compiler bug and not a program one: the lowering dropped a
    /// store its source asked for.
    ///
    /// Legitimate unconstrained cells are absent by construction, not by
    /// exemption: a range-check touch's two cells are resolved to ZERO by the
    /// deferred fixup before this is taken, and an arithmetic back-solve writes its
    /// operand before reading it.
    pub unconstrained_reads: Vec<u32>,
    pub(crate) trace: Trace, // rows + final access-count columns, emitted in the same walk
}

fn pop_witness<'a>(
    witness: &'a HashMap<String, Vec<Vec<F64>>>,
    positions: &mut HashMap<&'a str, usize>,
    name: &'a str,
    len: u32,
) -> &'a [F64] {
    let entries = witness
        .get(name)
        .unwrap_or_else(|| panic!("no witness stream `{name}` (Program::set_witness)"));
    let position = positions.entry(name).or_default();
    let entry = entries.get(*position).unwrap_or_else(|| {
        panic!(
            "witness stream `{name}` exhausted (needs entry {}, has {})",
            *position + 1,
            entries.len()
        )
    });
    assert_eq!(
        entry.len(),
        len as usize,
        "witness `{name}` entry {} holds {} values, the destination {len}",
        *position,
        entry.len()
    );
    *position += 1;
    entry
}

impl Program {
    /// Run the program in write-once *fill* mode to produce its [`Execution`]:
    /// the final memory image and the step count. The public input seeds the
    /// first four memory cells (§sec:e2e-pi). Compilation yields the `Program`;
    /// executing it (here) and proving it are separate later phases.
    pub fn execute(&self, public_input: [F64; 4]) -> Execution {
        // One interpretation of the program, then the fill. The blocks that bring every
        // table to a power of two are cycles no program code enters (`cpu::filler`), so
        // they run after the chain has halted, by which point the program's own row
        // counts are final; a traversal costs exactly its block's size plus its closing
        // jump, so the solve is exact and no second run is needed to correct it.
        use super::hints::{BitsDest, GPow, RHint};

        let ending_pc = (self.prog.len() - 1) as u32; // last bytecode slot, g^{B-1}

        // g^j and its reverse index g^j ↦ j, seeded for the program counters and
        // return targets and grown on demand past that.
        let mut g = GPow::new(self.prog.len() + 2);

        // Dense write-once data memory (read path stays a vector for speed), the
        // per-cell access count (g^{count}, default g^0 = 1), and a written mask.
        let n0 = self.main_frame.max(4) as usize;
        let mut m = Mem {
            cells: vec![F64::ZERO; n0],
            written: vec![false; n0],
            count: vec![F64::ONE; n0],
            dbg_pc: 0,
            dbg_line: 0,
            dbg_hint: None,
        };
        // Seed the public input into the first four cells (§sec:e2e-pi).
        for (i, &word) in public_input.iter().enumerate() {
            m.cells[i] = word;
            m.written[i] = true;
        }

        // Per-pc bytecode execution count (g^{count}).
        let mut bytecode_count: Vec<F64> = vec![F64::ONE; self.prog.len()];

        let mut next_free = self.main_frame;
        let (mut pc, mut fp) = (0u32, 0u32);
        let mut steps = 0usize;
        // Per-pc hint index. `self.hints` is keyed by pc, so probing it each step
        // costs a hash of the counter for what is almost always a miss; the
        // program has one bytecode slot per pc, so flatten the map into a dense
        // table: 0 = no hints, otherwise the 1-based index into `hint_lists`.
        let mut hint_at = vec![0u32; self.prog.len()];
        let mut hint_lists: Vec<&[RHint]> = Vec::with_capacity(self.hints.len());
        for (&hpc, hs) in &self.hints {
            hint_lists.push(hs.as_slice());
            hint_at[hpc as usize] = hint_lists.len() as u32;
        }
        // `DBG_PROF=1`: per-pc step counts, printed as a per-function cycle
        // profile after the run (needs `fn_ranges`, i.e. a compiled program).
        let mut prof: Option<Vec<u64>> = std::env::var("DBG_PROF").is_ok().then(|| vec![0u64; self.prog.len()]);

        // Per-stream cursor into the named witness data (`hint_witness` pops
        // sequentially).
        let mut witness_positions: HashMap<&str, usize> = HashMap::new();
        // Baby-step table for `hint_decompose_bits_exponent`, built on first use.
        let mut dlog_cache: Option<(GPow, F64)> = None;

        // Rows per table before the fill runs, captured when the chain halts.
        let mut base_counts: Option<[usize; crate::tables::N_TABLES]> = None;
        // Where the fill's frames begin, captured at the same moment, so
        // `unconstrained_reads` can speak about the program's own cells only. The
        // fill's rows exist to reach a power-of-two height and are soundness-neutral
        // (doc §Filling the tables), so they read cells nobody writes as a matter of
        // course; the program's own cells are all below this mark, since the
        // allocator serves them and a range check's absolute write lands under
        // `2^MIN_LOG_MEM`.
        let mut fill_base = usize::MAX;

        // Per-opcode trace rows, accumulated during the walk and assembled into the
        // `Trace` once the run finishes (alongside the final count columns).
        let mut xor64: Vec<Xrow> = Vec::new();
        let mut mul64: Vec<Xrow> = Vec::new();
        let mut xor192: Vec<X3row> = Vec::new();
        let mut mul192: Vec<X3row> = Vec::new();
        let mut set: Vec<Srow> = Vec::new();
        let mut deref: Vec<Drow> = Vec::new();
        let mut jump: Vec<Jrow> = Vec::new();
        let mut blake2s: Vec<Brow> = Vec::new();

        // `DEREF Cell` touches whose two sides are both still unwritten (the
        // range-check gadget's unconstrained target cells), as `(a2, a3)`,
        // resolved after the run: write-once memory is order-independent, so the
        // value can be decided at the end (leanVM's end-of-execution deref-hint
        // resolution).
        let mut deferred: Vec<(usize, u32)> = Vec::new();

        // The three dense per-cell vectors, kept in lockstep. Every method is
        // `#[inline(always)]`: they sit in the interpreter's hot opcode loop.
        struct Mem {
            cells: Vec<F64>,
            written: Vec<bool>,
            count: Vec<F64>,
            /// The pc of the currently executing instruction, and the name of the
            /// computed-advice hint if the write comes from one, so the
            /// write-once panic can report where the conflict happened. Plain
            /// fields rather than thread-locals: this is written on every step,
            /// and a thread-local costs a lazy-init check each time.
            dbg_pc: u32,
            /// Source line of that pc, or 0 when the program carries no table.
            dbg_line: u32,
            dbg_hint: Option<&'static str>,
        }
        impl Mem {
            // Grow the dense vectors so `idx` is in range. All accessed cells
            // satisfy cell < next_free after their frame's allocation, so this
            // only ever extends.
            #[inline(always)]
            fn ensure(&mut self, idx: usize) {
                if idx >= self.cells.len() {
                    let n = idx + 1;
                    self.cells.resize(n, F64::ZERO);
                    self.written.resize(n, false);
                    self.count.resize(n, F64::ONE);
                }
            }
            #[inline(always)]
            fn is_written(&self, cell: u32) -> bool {
                (cell as usize) < self.written.len() && self.written[cell as usize]
            }
            // Read a cell; an unwritten cell reads as ZERO.
            #[inline(always)]
            fn get(&self, cell: u32) -> F64 {
                if self.is_written(cell) {
                    self.cells[cell as usize]
                } else {
                    F64::ZERO
                }
            }
            // The `E` element in three consecutive cells.
            #[inline(always)]
            fn get3(&self, cell: u32) -> F192 {
                F192::new(self.get(cell).0, self.get(cell + 1).0, self.get(cell + 2).0)
            }
            // Write-once store: writing a different value to an already-set cell panics.
            #[inline(always)]
            fn put(&mut self, cell: u32, v: F64) {
                self.ensure(cell as usize);
                let c = cell as usize;
                if self.written[c] {
                    assert!(
                        self.cells[c] == v,
                        "write-once conflict at cell {cell} ({}, hint {:?}): had {:#x}, new {:#x}",
                        if self.dbg_line == 0 {
                            format!("pc {}", self.dbg_pc)
                        } else {
                            format!("line {}, pc {}", self.dbg_line, self.dbg_pc)
                        },
                        self.dbg_hint,
                        self.cells[c].0,
                        v.0
                    );
                } else {
                    self.cells[c] = v;
                    self.written[c] = true;
                }
            }
            #[inline(always)]
            fn put3(&mut self, cell: u32, v: F192) {
                self.put(cell, F64(v.c0));
                self.put(cell + 1, F64(v.c1));
                self.put(cell + 2, F64(v.c2));
            }
            // Read the running access count and advance it by ×g (the free increment).
            // ×g is ×x, i.e. `mul_by_g`, a shift+fold rather than a PMULL; this runs on every
            // memory access (several million per run), so the cheap form matters.
            #[inline(always)]
            fn bump_access_count(&mut self, cell: u32) -> F64 {
                self.ensure(cell as usize);
                let cell_idx = cell as usize;
                let count = self.count[cell_idx];
                self.count[cell_idx] = mul_by_g(count);
                count
            }
            #[inline(always)]
            fn bump3(&mut self, cell: u32) -> [F64; 3] {
                [
                    self.bump_access_count(cell),
                    self.bump_access_count(cell + 1),
                    self.bump_access_count(cell + 2),
                ]
            }
        }
        // Bounded discrete log for `hint_decompose_bits_exponent`: find n < 2^nbits
        // with g^n = x, by baby-step giant-step (baby table g^j for j < 2^17,
        // built once per run; giant step ×g^(-2^17)). Prover-side only: the
        // program re-verifies the hinted bits itself.
        fn bounded_dlog(cache: &mut Option<(GPow, F64)>, x: F64, nbits: u32) -> u128 {
            const LOG_BABY: u32 = 17;
            let (baby, giant) = cache.get_or_insert_with(|| {
                let baby = GPow::new((1usize << LOG_BABY) - 1);
                // g^(2^17), one past the table; its inverse is the giant step.
                let giant = mul_by_g(baby.pow((1usize << LOG_BABY) - 1)).inv();
                (baby, giant)
            });
            let mut y = x;
            let max_giant = if nbits > LOG_BABY {
                1u64 << (nbits - LOG_BABY)
            } else {
                1
            };
            for a in 0..max_giant {
                if let Some(j) = baby.log(y) {
                    return (a as u128) << LOG_BABY | j as u128;
                }
                y *= *giant;
            }
            panic!("hint_decompose_bits_exponent: value is not g^n for n < 2^{nbits}")
        }

        // The cell a heap run starts at: read the pointer back out of memory and
        // invert it. Shared by every hint that writes through one.
        fn heap_base(m: &Mem, g: &mut GPow, cell: u32, what: &str) -> u32 {
            g.log(m.get(cell))
                .unwrap_or_else(|| panic!("{what} pointer is not a g-power"))
        }

        // Where a computed-advice bit buffer starts: a frame run needs no lookup
        // at all, which is the point of having one.
        fn bits_base(m: &Mem, g: &mut GPow, fp: u32, dest: BitsDest, what: &str) -> u32 {
            match dest {
                BitsDest::Stack(base) => fp + base,
                BitsDest::Heap(ptr) => heap_base(m, g, fp + ptr, what),
            }
        }

        // The program's own chain runs to the halt sentinel; the fill blocks then run, one
        // cycle at a time. A cycle is entered at its block's first instruction, in a frame
        // of its own, and traversed for the rows `filler::solve` asks of it, always a whole
        // number of traversals, so the state tuples it pushes are exactly the ones it pulls
        // (doc §Filling the tables). `left` is the rows still to run in the current cycle,
        // and `None` while the chain runs.
        let mut cycles: std::vec::IntoIter<(u32, u32, usize)> = Vec::new().into_iter();
        let mut left: Option<usize> = None;
        loop {
            // The chain reached the sentinel, or a cycle has run its rows.
            let switch = match left {
                None => pc == ending_pc,
                Some(n) => n == 0,
            };
            if switch {
                if left.is_none() {
                    assert_eq!((pc, fp), (ending_pc, 0), "main must halt at the sentinel pc g^{{B-1}}");
                    let counts = [
                        xor64.len(),
                        mul64.len(),
                        set.len(),
                        deref.len(),
                        jump.len(),
                        blake2s.len(),
                        xor192.len(),
                        mul192.len(),
                    ];
                    base_counts = Some(counts);
                    fill_base = (1usize << crate::cpu::MIN_LOG_MEM).max(next_free as usize);
                    // A frame per cycle, from the same bump allocator that serves `Alloc`
                    // but never below the memory floor: a range check's `DEREF` writes the
                    // absolute cell its bound names, which can be any cell under
                    // `2^MIN_LOG_MEM` and so is nobody's to reserve (`lower_assert_lt`).
                    use super::filler::frame as fr;
                    let mut runs: Vec<(u32, u32, usize)> = Vec::new();
                    // A hand-assembled program carries no blocks and has to land on
                    // powers of two by itself, which `Layout` checks.
                    if !self.filler.is_empty() {
                        let mut frame = (1u32 << crate::cpu::MIN_LOG_MEM).max(next_free);
                        for (block_pc, size, n) in super::filler::cycles(&self.filler, counts) {
                            g.grow_to(frame as usize);
                            g.note(frame as usize);
                            // What the closing jump reads: back to the block's own first
                            // instruction, in this same frame. Then the pointer the `DEREF`
                            // dummy follows, memory cell `0`.
                            m.put(frame + fr::DEST, g.pow(block_pc as usize));
                            m.put(frame + fr::NEXT_FP, g.pow(frame as usize));
                            m.put(frame + fr::PTR, F64::ONE);
                            runs.push((block_pc, frame, n * (size as usize + 1)));
                            frame += fr::CELLS;
                        }
                        next_free = frame;
                    }
                    cycles = runs.into_iter();
                }
                match cycles.next() {
                    Some((p, f, rows)) => {
                        pc = p;
                        fp = f;
                        left = Some(rows);
                    }
                    None => break,
                }
            }
            if let Some(n) = &mut left {
                *n -= 1;
            }
            assert!(steps < 100_000_000, "step limit exceeded (runaway recursion?)");
            m.dbg_pc = pc;
            m.dbg_line = self.src_lines.get(pc as usize).copied().unwrap_or(0);
            if let Some(p) = prof.as_mut() {
                p[pc as usize] += 1;
            }

            // Apply the hints scheduled before this instruction.
            if hint_at[pc as usize] != 0 {
                let hs = hint_lists[hint_at[pc as usize] as usize - 1];
                for h in hs {
                    m.dbg_hint = Some(match h {
                        RHint::ResolveDeref { .. } => "ResolveDeref",
                        RHint::FrameAddress { .. } => "FrameAddress",
                        RHint::AllocFrames { .. } => "AllocFrames",
                        RHint::Alloc { .. } => "Alloc",
                        RHint::AllocDyn { .. } => "AllocDyn",
                        RHint::WitnessStack { .. } => "WitnessStack",
                        RHint::WitnessHeap { .. } => "WitnessHeap",
                        RHint::Log2Ceil { .. } => "Log2Ceil",
                        RHint::BitDecompose { .. } => "BitDecompose",
                        RHint::BitDecomposeExp { .. } => "BitDecomposeExp",
                        RHint::Inverse { .. } => "Inverse",
                        RHint::Inverse192 { .. } => "Inverse192",
                        RHint::Print { .. } => "Print",
                    });
                    match h {
                        RHint::ResolveDeref { ptr, offset, dst } => {
                            let base = heap_base(&m, &mut g, fp + ptr, "cached DEREF");
                            let src = base + offset;
                            let dst = fp + dst;
                            match (m.written[src as usize], m.written[dst as usize]) {
                                (true, false) => m.put(dst, m.cells[src as usize]),
                                (false, true) => m.put(src, m.cells[dst as usize]),
                                _ => {}
                            }
                        }
                        RHint::FrameAddress { offset } => {
                            g.note((fp + offset) as usize);
                        }
                        // A fresh region: write its base `g^{next_free}` into the
                        // pointer cell (once) and reserve `size` cells. `AllocDyn`
                        // reads the size from a cell at runtime.
                        RHint::Alloc { .. } | RHint::AllocDyn { .. } | RHint::AllocFrames { .. } => {
                            let (ptr, size) = match *h {
                                RHint::Alloc { ptr, size } => (ptr, size),
                                RHint::AllocFrames {
                                    ptr,
                                    size,
                                    end,
                                    start_inverse,
                                } => {
                                    let span = m.get(fp + end) * start_inverse;
                                    assert!(!span.is_zero(), "loop bound is zero");
                                    let max_frames = ((1u64 << 28) - u64::from(next_free)) / u64::from(size);
                                    let max_span = max_frames.saturating_sub(1) as usize;
                                    let mut exponent = g.log(span);
                                    while exponent.is_none() && g.covered() <= max_span {
                                        g.grow_to((2 * g.covered()).min(max_span));
                                        exponent = g.log(span);
                                    }
                                    let n = exponent.expect("loop bound exceeds the address space") + 1;
                                    (ptr, size.checked_mul(n).expect("loop frames overflow"))
                                }
                                // A runtime size is carried in the exponent:
                                // the cell holds g^k, allocate k cells (reverse
                                // g-power lookup, growing the index if needed).
                                RHint::AllocDyn { ptr, size } => {
                                    let sz = m.get(fp + size);
                                    let cells = g.log(sz).unwrap_or_else(|| {
                                        g.grow_to(1 << 20);
                                        g.log(sz)
                                            .unwrap_or_else(|| panic!("HeapBuf size is not a g-power below 2^20 cells"))
                                    });
                                    (ptr, cells)
                                }
                                _ => unreachable!(),
                            };
                            let cell = fp + ptr;
                            m.ensure(cell as usize);
                            if !m.written[cell as usize] {
                                let base = next_free;
                                next_free += size;
                                g.grow_to((base + size) as usize);
                                // The base is about to become a pointer in memory.
                                g.note(base as usize);
                                m.ensure(next_free as usize);
                                m.cells[cell as usize] = g.pow(base as usize);
                                m.written[cell as usize] = true;
                            }
                        }
                        RHint::Print { label, cell } => {
                            let c = fp + cell;
                            m.ensure(c as usize);
                            if m.written[c as usize] {
                                let v = m.cells[c as usize];
                                // Small integers and small g-powers overlap (8 = x^3
                                // = g^3): show every reading that applies.
                                let k = g.log(v);
                                let small = v.0 < 1 << 32;
                                match (k, small) {
                                    (Some(k), true) => {
                                        eprintln!("[print] {label} = {} (g^{})", pretty_integer(v.0), pretty_integer(k))
                                    }
                                    (Some(k), false) => {
                                        eprintln!("[print] {label} = g^{}", pretty_integer(k))
                                    }
                                    (None, true) => {
                                        eprintln!("[print] {label} = {}", pretty_integer(v.0))
                                    }
                                    (None, false) => eprintln!("[print] {label} = {:#x}", v.0),
                                }
                            } else {
                                eprintln!("[print] {label} = <unwritten>");
                            }
                        }
                        RHint::WitnessStack { name, base, len } => {
                            let values = pop_witness(&self.witness, &mut witness_positions, name, *len);
                            for (k, &value) in values.iter().enumerate() {
                                m.put(fp + base + k as u32, value);
                            }
                        }
                        RHint::WitnessHeap { name, ptr, lo, len } => {
                            let b = heap_base(&m, &mut g, fp + ptr, "hint_witness heap");
                            let values = pop_witness(&self.witness, &mut witness_positions, name, *len);
                            for (k, &value) in values.iter().enumerate() {
                                m.put(b + lo + k as u32, value);
                            }
                        }
                        RHint::Log2Ceil {
                            bits,
                            dst,
                            nbits,
                            floor,
                        } => {
                            let b = bits_base(&m, &mut g, fp, *bits, "log2_ceil");
                            let mut word: u128 = 0;
                            for j in 0..*nbits {
                                if !m.get(b + j).is_zero() {
                                    word |= 1u128 << j;
                                }
                            }
                            let cl = if word <= 1 {
                                0
                            } else {
                                u128::BITS - (word - 1).leading_zeros()
                            };
                            let mu = cl.max(*floor);
                            m.put(fp + dst, primitives::field::g_pow(mu as usize));
                        }
                        RHint::BitDecompose { value, bits, nbits } => {
                            assert!(*nbits <= 64, "a machine word has 64 bits");
                            let v = m.get(fp + value).0;
                            let bb = bits_base(&m, &mut g, fp, *bits, "decompose");
                            for j in 0..*nbits {
                                m.put(bb + j, F64((v >> j) & 1));
                            }
                        }
                        RHint::BitDecomposeExp { value, bits, nbits } => {
                            let x = m.get(fp + value);
                            let n = bounded_dlog(&mut dlog_cache, x, *nbits);
                            let bb = bits_base(&m, &mut g, fp, *bits, "hint_decompose_bits_exponent");
                            for j in 0..*nbits {
                                m.put(bb + j, F64(((n >> j) & 1) as u64));
                            }
                        }
                        RHint::Inverse { value, dst } => {
                            let v = m.get(fp + value);
                            m.put(fp + dst, if v.is_zero() { F64::ZERO } else { v.inv() });
                        }
                        RHint::Inverse192 { value, dst } => {
                            let v = m.get3(fp + value);
                            m.put3(fp + dst, if v.is_zero() { F192::ZERO } else { v.inv() });
                        }
                    }
                    m.dbg_hint = None;
                }
            }
            // Cover the g-powers this step may index (g²·pc return target, g^fp).
            // Guarded so the steady state is a length compare, not a call.
            let need = (pc as usize + 2).max(fp as usize);
            if g.covered() <= need {
                g.grow_to(need);
            }

            let bytecode_read = {
                let v = bytecode_count[pc as usize];
                bytecode_count[pc as usize] = mul_by_g(v);
                v
            };

            // Loaded once: the shared arithmetic arms need the discriminant again,
            // and `Op` is wide enough that re-reading it costs a second load.
            let op = self.prog[pc as usize];
            match op {
                Op::Xor64 { a, b, c } | Op::Mul64 { a, b, c } => {
                    let is_xor = matches!(op, Op::Xor64 { .. });
                    let (aa, ab, ac) = (fp + a, fp + b, fp + c);
                    // The row is the equality `m[c] = m[a] op m[b]` over write-once
                    // memory. Normally the operands are known and the result is
                    // computed forward; for a `MUL` whose result is already written
                    // and exactly one of whose operands is not, the runner
                    // back-solves that operand, which is what produces the
                    // range-check complement `y = g^{k-1}·x^{-1}` from
                    // `MUL x·y = g^{k-1}`, and the quotient of `a / b`, with no
                    // dedicated hint.
                    //
                    // `XOR` deliberately does NOT deduce. Nothing asks it to (both
                    // users are `MUL`), and an `XOR` into an already-written cell is
                    // how `assert a == b` is spelled, so deducing there would define
                    // the operand the assert exists to check instead of failing on it.
                    if !is_xor && m.is_written(ac) {
                        let (ha, hb) = (m.is_written(aa), m.is_written(ab));
                        if ha ^ hb {
                            let vk = m.get(if ha { aa } else { ab });
                            assert!(!vk.is_zero(), "cannot back-solve MUL64 through a zero operand");
                            m.put(if ha { ab } else { aa }, m.get(ac) * vk.inv());
                        }
                    }
                    let va = m.get(aa);
                    let vb = m.get(ab);
                    let vc = if is_xor { va + vb } else { va * vb };
                    m.put(ac, vc);
                    let ra = m.bump_access_count(aa);
                    let rb = m.bump_access_count(ab);
                    let rc = m.bump_access_count(ac);
                    let row = Xrow {
                        pc,
                        fp,
                        ra,
                        rb,
                        rc,
                        bytecode_read,
                    };
                    if is_xor {
                        xor64.push(row);
                    } else {
                        mul64.push(row);
                    }
                    pc += 1;
                }
                Op::Xor192 { a, b, c } | Op::Mul192 { a, b, c } => {
                    let is_xor = matches!(op, Op::Xor192 { .. });
                    let (aa, ab, ac) = (fp + a, fp + b, fp + c);
                    let written = |m: &Mem, cell: u32| (0..3).filter(|&i| m.is_written(cell + i)).count();
                    // The `MUL64` back-solve, `div192`'s quotient: an operand not fully
                    // written is solved for when the other one is, its written limbs
                    // checked like any store.
                    if !is_xor && written(&m, ac) == 3 {
                        let (wa, wb) = (written(&m, aa), written(&m, ab));
                        if (wa == 3) != (wb == 3) {
                            let vk = m.get3(if wa == 3 { aa } else { ab });
                            assert!(!vk.is_zero(), "cannot back-solve MUL192 through a zero operand");
                            m.put3(if wa == 3 { ab } else { aa }, m.get3(ac) * vk.inv());
                        }
                    }
                    let (va, vb) = (m.get3(aa), m.get3(ab));
                    m.put3(ac, if is_xor { va + vb } else { va * vb });
                    let row = X3row {
                        pc,
                        fp,
                        ra: m.bump3(aa),
                        rb: m.bump3(ab),
                        rc: m.bump3(ac),
                        bytecode_read,
                    };
                    if is_xor {
                        xor192.push(row);
                    } else {
                        mul192.push(row);
                    }
                    pc += 1;
                }
                Op::Set { o, k } => {
                    let a = fp + o;
                    m.put(a, k);
                    let r = m.bump_access_count(a);
                    set.push(Srow {
                        pc,
                        fp,
                        r,
                        bytecode_read,
                    });
                    pc += 1;
                }
                Op::Deref { o1, o2, o3, mode } => {
                    let a1 = fp + o1;
                    let p = m.get(a1);
                    let base = match g.log(p) {
                        Some(b) => b,
                        None => {
                            // Not indexed yet: grow the g-power index to the minimum
                            // memory size, since range-check touches point anywhere below
                            // their bound (≤ 2^MIN_LOG_MEM), not just at allocated
                            // frames/buffers. A value still absent is no valid
                            // pointer: a wild deref, or a failed range check
                            // (`assert log _ < _`) surfacing honestly.
                            g.grow_to(1 << MIN_LOG_MEM);
                            g.log(p).unwrap_or_else(|| {
                                panic!(
                                    "DEREF pointer is not a small g-power at pc {pc} (in {}): a wild \
                                     pointer, or a failed range check \
                                     (value 0x{:016x})",
                                    self.site_at(pc),
                                    p.0
                                )
                            })
                        }
                    };
                    let a2 = (base + o2) as usize;
                    let a3 = fp + o3;
                    match mode {
                        DerefMode::Cell => {
                            // Equality m[a2] == m[a3]: fill the unset side.
                            m.ensure(a2);
                            let has2 = m.written[a2];
                            let has3 = m.is_written(a3);
                            match (has2, has3) {
                                (true, true) => assert!(
                                    m.cells[a2] == m.get(a3),
                                    "DEREF mismatch at pc {pc} (in {}): m[{a2}] = {:#x} but m[fp+{o3}] = {:#x}",
                                    self.site_at(pc),
                                    m.cells[a2].0,
                                    m.get(a3).0,
                                ),
                                (true, false) => {
                                    let v = m.cells[a2];
                                    m.put(a3, v);
                                }
                                (false, true) => {
                                    let v = m.get(a3);
                                    m.put(a2 as u32, v);
                                }
                                (false, false) => {
                                    // Both sides still unwritten: a range-check
                                    // touch (only the address validity of `a2`
                                    // matters, not its value). Defer the equality
                                    // to after the run, once `m[a2]`'s final value
                                    // (a later program write, or ZERO) is known;
                                    // the row itself needs no patch, since the
                                    // fill reads both values out of that image.
                                    deferred.push((a2, a3));
                                }
                            }
                        }
                        DerefMode::Pc => {
                            // The return target and the frame base are stored as
                            // addresses, and JUMP reads them back.
                            g.note(pc as usize + 2);
                            let v = g.pow(pc as usize + 2);
                            m.put(a2 as u32, v);
                        }
                        DerefMode::Fp => {
                            g.note(fp as usize);
                            let v = g.pow(fp as usize);
                            m.put(a2 as u32, v);
                        }
                    }
                    let r1 = m.bump_access_count(a1);
                    let r2 = m.bump_access_count(a2 as u32);
                    let r3 = m.bump_access_count(a3);
                    deref.push(Drow {
                        pc,
                        fp,
                        r1,
                        r2,
                        r3,
                        bytecode_read,
                    });
                    pc += 1;
                }
                Op::Jump { oc, od, of } => {
                    let (ac, ad, af) = (fp + oc, fp + od, fp + of);
                    let (c, d, f) = (m.get(ac), m.get(ad), m.get(af));
                    // The is-nonzero witness `w = c⁻¹` is never used for control
                    // flow, only recorded as a witness column, so it is not
                    // computed here at all: `JumpTable::fill` batch-inverts every
                    // row's condition at once (§the trace rows in `cpu::trace`).
                    let rc = m.bump_access_count(ac);
                    let rd = m.bump_access_count(ad);
                    let rf = m.bump_access_count(af);
                    jump.push(Jrow {
                        pc,
                        fp,
                        rc,
                        rd,
                        rf,
                        bytecode_read,
                    });
                    if c.is_zero() {
                        pc += 1;
                    } else {
                        pc = g.log(d).expect("JUMP target not a g-power");
                        fp = g.log(f).expect("JUMP fp not a g-power");
                    }
                }
                Op::Blake2s { .. } => {
                    // Every cell the row touches, in value-lane order: the message
                    // chunks, the digest, the chaining value, the metadata.
                    let cells = crate::tables::blake2s_cells(&self.prog, pc, fp);
                    let w = cells.map(|a| m.get(a));
                    // Compress the 64 message bytes to the 32-byte result. No table
                    // constraint covers the digest (the relation is proven by flock,
                    // §hash_flock); the interpreter still computes the definite digest
                    // so the output cells are consistent for any later read.
                    let digest = blake2s_compress(
                        [w[0], w[1], w[2], w[3]],
                        [w[4], w[5], w[6], w[7]],
                        [w[12], w[13], w[14], w[15]],
                        [w[16], w[17]],
                    );
                    for (k, &word) in digest.iter().enumerate() {
                        m.put(cells[8 + k], word);
                    }
                    blake2s.push(Brow {
                        pc,
                        fp,
                        r: cells.map(|a| m.bump_access_count(a)),
                        bytecode_read,
                    });
                    pc += 1;
                }
            }
            steps += 1;
        }

        if let Some(p) = &prof {
            let mut rows: Vec<(String, u64)> = self
                .fn_ranges
                .iter()
                .map(|(name, entry, len)| {
                    let total: u64 = p[*entry as usize..(*entry + *len) as usize].iter().sum();
                    (name.clone(), total)
                })
                .collect();
            rows.sort_by_key(|(_, c)| std::cmp::Reverse(*c));
            // `DBG_PROF_DUMP=path`: also write the raw per-pc counts plus the
            // function table, so an offline pass can attribute the straight-line
            // cycles of one big function to its source regions (the call sites of
            // the lowered `for` helpers are the landmarks).
            if let Ok(path) = std::env::var("DBG_PROF_DUMP") {
                let mut out = format!("# steps {steps}\n");
                for (name, entry, len) in &self.fn_ranges {
                    out += &format!("F {name} {entry} {len}\n");
                }
                for (pc, c) in p.iter().enumerate() {
                    if *c > 0 {
                        out += &format!("{pc} {c}\n");
                    }
                }
                let path = if std::path::Path::new(&path).exists() {
                    format!("{path}.{}", std::process::id())
                } else {
                    path
                };
                std::fs::write(&path, out).expect("write DBG_PROF_DUMP");
                eprintln!("== DBG_PROF: per-pc counts m.written to {path}");
            }
            eprintln!("== DBG_PROF: cycles by function ({} total) ==", pretty_integer(steps));
            for (name, c) in rows.iter().filter(|(_, c)| *c > 0) {
                eprintln!(
                    "  {:>13}  {:>7}%  {name}",
                    pretty_integer(c),
                    pretty_f64(100.0 * *c as f64 / steps as f64)
                );
            }
        }

        // Resolve the deferred DEREF touches: a fixpoint, so a touch whose cell is
        // filled by another deferred entry picks up that value; cells nobody ever
        // writes are fixed to ZERO. The rows need no patch: the fill reads both
        // sides out of the finished image, and their access counts were already
        // bumped during the walk (the memory bus is order-independent, it only
        // needs every access to agree on the value).
        while {
            let before = deferred.len();
            deferred.retain(|&(a2, a3)| {
                if m.written[a2] {
                    let v = m.cells[a2];
                    m.put(a3, v);
                    false
                } else {
                    true
                }
            });
            deferred.len() < before
        } {}
        for (a2, a3) in deferred {
            // Never written: the cells are genuinely unconstrained; fix them to ZERO.
            m.put(a2 as u32, F64::ZERO);
            m.put(a3, F64::ZERO);
        }

        // Cells an instruction touched that nothing ever wrote. Read off the two
        // dense vectors rather than recorded in `Mem::get`, which is in the opcode
        // loop: an access bumps the count, so `count != ONE` means touched, and
        // `written` is already there. Taken AFTER the deferred fixup, so a
        // range-check touch, whose cells are legitimately unconstrained and were
        // just fixed to ZERO, does not appear.
        let unconstrained_reads: Vec<u32> = (0..m.cells.len().min(fill_base))
            .filter(|&c| !m.written[c] && m.count[c] != F64::ONE)
            .map(|c| c as u32)
            .collect();

        // Pad memory to a power of two (the boundary tables read a dense image),
        // at least 2^MIN_LOG_MEM cells (doc §Memory).
        let mem_used = m.cells.len();
        let cells = m.cells.len().next_power_of_two().max(1 << MIN_LOG_MEM);
        assert!(cells <= 1 << MAX_LOG_MEM, "data memory exceeds 2^{MAX_LOG_MEM} cells");
        m.cells.resize(cells, F64::ZERO);
        m.count.resize(cells, F64::ONE);
        let trace = Trace {
            xor64,
            mul64,
            set,
            deref,
            jump,
            blake2s,
            xor192,
            mul192,
            mem_count: m.count,
            bytecode_count,
        };
        Execution {
            mem: m.cells,
            cycles: steps,
            mem_used,
            // Taken when the chain halted, which every run does before it can leave the
            // loop at all.
            base_counts: base_counts.expect("the run halted, so its own counts were taken"),
            unconstrained_reads,
            trace,
        }
    }
}
