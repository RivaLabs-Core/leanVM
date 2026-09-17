//! Execution, in two passes.
//!
//! The machine's memory is read-write, and its initial contents are the prover's
//! to choose, the public input aside. [`Program::run`] is the machine: it reads,
//! computes, writes, and records for every access what the memory argument needs.
//!
//! A zkDSL program is written against write-once memory, where a cell nothing has
//! written yet is prover-chosen and a second write is an equality. For such a
//! program ([`Program::write_once`]) the first pass, [`Program::solve_write_once`],
//! finds the one memory image every instruction agrees with: hints fill their cells,
//! an unset operand is back-solved, a `DEREF` fills whichever side is unset. That
//! image is a fixed point of the machine, so handing it over as the initial memory
//! makes every write rewrite the value already there. The proof no longer enforces
//! the discipline, only this pass does: a conflicting write is a panic here and
//! nothing at all to the verifier.

use std::collections::HashMap;

use super::*;
use crate::tables::{BLAKE2S_LANES_BY_SLOT, BLAKE2S_STRIDE, CLOCK_STRIDE, RANGE_LOG};
use primitives::{
    field::{F64, mul_by_g},
    pretty_f64, pretty_integer,
};

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
    /// Write-once programs only: cells an instruction read that nothing ever wrote,
    /// so the value it read was ZERO here and prover-chosen in a proof. `zkDSL.md`
    /// says don't; this is what says whether the emitted code did. A non-empty list
    /// means a live value came from outside the program, which is a compiler bug
    /// and not a program one: the lowering dropped a store its source asked for.
    ///
    /// Legitimate unconstrained cells are absent by construction, not by
    /// exemption: a range-check touch's two cells are resolved to ZERO by the
    /// deferred fixup before this is taken, and an arithmetic back-solve writes its
    /// operand before reading it.
    pub unconstrained_reads: Vec<u32>,
    pub(crate) trace: Trace, // rows, final timestamps and counts, emitted in the same walk
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
    /// Run the program on `public_input`, which seeds the first four memory cells
    /// (§sec:e2e-pi). Compilation yields the `Program`; executing it (here) and
    /// proving it are separate later phases.
    pub fn execute(&self, public_input: [F64; 4]) -> Execution {
        if self.write_once {
            let (image, unconstrained_reads, g) = self.solve_write_once(public_input);
            self.run(image, g, unconstrained_reads)
        } else {
            assert!(self.hints.is_empty(), "hints fill write-once cells");
            let g = super::hints::GPow::new(self.prog.len() + 2);
            self.run(public_input.to_vec(), g, Vec::new())
        }
    }

    /// The memory image a write-once program's instructions all agree with, the
    /// cells nothing wrote ([`Execution::unconstrained_reads`]), and the g-power
    /// index the walk built.
    fn solve_write_once(&self, public_input: [F64; 4]) -> (Vec<F64>, Vec<u32>, super::hints::GPow) {
        use super::hints::{BitsDest, GPow, RHint};

        let ending_pc = (self.prog.len() - 1) as u32; // last bytecode slot, g^{B-1}

        // g^j and its reverse index g^j ↦ j, seeded for the program counters and
        // return targets and grown on demand past that.
        let mut g = GPow::new(self.prog.len() + 2);

        // Dense write-once data memory (read path stays a vector for speed), a
        // written mask, and which cells an instruction touched.
        let n0 = self.main_frame.max(4) as usize;
        let mut m = Mem {
            cells: vec![F64::ZERO; n0],
            written: vec![false; n0],
            touched: vec![false; n0],
            dbg_pc: 0,
            dbg_line: 0,
            dbg_hint: None,
        };
        // Seed the public input into the first four cells (§sec:e2e-pi).
        for (i, &word) in public_input.iter().enumerate() {
            m.cells[i] = word;
            m.written[i] = true;
        }

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
        // Per-stream cursor into the named witness data (`hint_witness` pops
        // sequentially).
        let mut witness_positions: HashMap<&str, usize> = HashMap::new();
        // Baby-step table for `hint_decompose_bits_exponent`, built on first use.
        let mut dlog_cache: Option<(GPow, F64)> = None;

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
            touched: Vec<bool>,
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
                    self.touched.resize(n, false);
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
            // Record that an instruction accessed the cell.
            #[inline(always)]
            fn touch(&mut self, cell: u32) {
                self.ensure(cell as usize);
                self.touched[cell as usize] = true;
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

        while pc != ending_pc {
            assert!(steps < 100_000_000, "step limit exceeded (runaway recursion?)");
            m.dbg_pc = pc;
            m.dbg_line = self.src_lines.get(pc as usize).copied().unwrap_or(0);
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
                    for cell in [aa, ab, ac] {
                        m.touch(cell);
                    }
                    pc += 1;
                }
                Op::AddU64 { a, b, c } | Op::MulU64 { a, b, c } => {
                    let u64_op = match op {
                        Op::AddU64 { .. } => crate::arith_flock::Op::Add,
                        _ => crate::arith_flock::Op::Mul,
                    };
                    let (aa, ab, ac) = (fp + a, fp + b, fp + c);
                    let vc = u64_op.apply(m.get(aa), m.get(ab));
                    m.put(ac, vc);
                    for cell in [aa, ab, ac] {
                        m.touch(cell);
                    }
                    pc += 1;
                }
                Op::Set { o, k } => {
                    let a = fp + o;
                    m.put(a, k);
                    m.touch(a);
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
                    for cell in [a1, a2 as u32, a3] {
                        m.touch(cell);
                    }
                    pc += 1;
                }
                Op::Jump { oc, od, of } => {
                    let (ac, ad, af) = (fp + oc, fp + od, fp + of);
                    let (c, d, f) = (m.get(ac), m.get(ad), m.get(af));
                    for cell in [ac, ad, af] {
                        m.touch(cell);
                    }
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
                    let digest = blake2s_compress(
                        [w[0], w[1], w[2], w[3]],
                        [w[4], w[5], w[6], w[7]],
                        [w[12], w[13], w[14], w[15]],
                        [w[16], w[17]],
                    );
                    for (k, &word) in digest.iter().enumerate() {
                        m.put(cells[8 + k], word);
                    }
                    for cell in cells {
                        m.touch(cell);
                    }
                    pc += 1;
                }
            }
            steps += 1;
        }

        assert_eq!((pc, fp), (ending_pc, 0), "main must halt at the sentinel pc g^{{B-1}}");

        // Resolve the deferred DEREF touches: a fixpoint, so a touch whose cell is
        // filled by another deferred entry picks up that value; cells nobody ever
        // writes are fixed to ZERO. The rows need no patch: the machine reads
        // both sides out of the finished image.
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

        // Cells an instruction touched that nothing ever wrote. Taken AFTER the
        // deferred fixup, so a range-check touch, whose cells are legitimately
        // unconstrained and were just fixed to ZERO, does not appear.
        let unconstrained_reads: Vec<u32> = (0..m.cells.len())
            .filter(|&c| !m.written[c] && m.touched[c])
            .map(|c| c as u32)
            .collect();
        (m.cells, unconstrained_reads, g)
    }
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
    /// Running read counts `g^{count}` of the two range arrays' entries.
    range_lo: Vec<F64>,
    range_hi: Vec<F64>,
}

impl Ram {
    fn new(image: Vec<F64>, floor: usize) -> Self {
        let mut ram = Self {
            init: image,
            cells: Vec::new(),
            last: Vec::new(),
            last_ts: Vec::new(),
            range_lo: vec![F64::ONE; 1 << RANGE_LOG],
            range_hi: vec![F64::ONE; 1 << RANGE_LOG],
        };
        ram.cells = ram.init.clone();
        ram.resize(ram.init.len().max(floor));
        ram
    }

    /// Cells past the initial image start at zero, last accessed at the seed's `g^0`.
    fn resize(&mut self, n: usize) {
        self.init.resize(n, F64::ZERO);
        self.cells.resize(n, F64::ZERO);
        self.last.resize(n, 0);
        self.last_ts.resize(n, F64::ONE);
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
            count_lo,
            count_hi,
        }
    }

    /// A padding row's access: clock zero on both sides, so the identity holds with
    /// the first entry of each range array.
    #[inline(always)]
    fn padding_access(&mut self) -> Access {
        let (count_lo, count_hi) = self.range_reads(0);
        Access {
            x: F64::ZERO,
            gap: 0,
            count_lo,
            count_hi,
        }
    }
}

impl Program {
    /// The machine: run the bytecode over read-write memory starting from `image`,
    /// recording every row, then write out the padding rows that bring each table to
    /// a power of two ([`filler`]).
    fn run(&self, image: Vec<F64>, mut g: super::hints::GPow, unconstrained_reads: Vec<u32>) -> Execution {
        let ending_pc = (self.prog.len() - 1) as u32; // last bytecode slot, g^{B-1}
        let mut m = Ram::new(image, self.main_frame.max(4) as usize);
        // Per-pc bytecode execution count (g^{count}).
        let mut bytecode_count: Vec<F64> = vec![F64::ONE; self.prog.len()];
        let mut fetch = |pc: u32| {
            let v = bytecode_count[pc as usize];
            bytecode_count[pc as usize] = mul_by_g(v);
            v
        };
        // `DBG_PROF=1`: per-pc step counts, printed as a per-function cycle
        // profile after the run (needs `fn_ranges`, i.e. a compiled program).
        let mut prof: Option<Vec<u64>> = std::env::var("DBG_PROF").is_ok().then(|| vec![0u64; self.prog.len()]);

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
            if let Some(p) = prof.as_mut() {
                p[pc as usize] += 1;
            }
            // Cover the g-powers this step may index (g²·pc return target, g^fp).
            let need = (pc as usize + 2).max(fp as usize);
            if g.covered() <= need {
                g.grow_to(need);
            }
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
                    let base = g.log(p).unwrap_or_else(|| {
                        panic!(
                            "DEREF pointer is not a small g-power at pc {pc} (in {}): a wild pointer \
                             (value 0x{:016x})",
                            self.site_at(pc),
                            p.0
                        )
                    });
                    let a2 = base + o2;
                    let v2_old = m.get(a2);
                    m.put(
                        a2,
                        match mode {
                            DerefMode::Cell => v3,
                            // The return target and the frame base are stored as
                            // addresses, and JUMP reads them back.
                            DerefMode::Pc => {
                                g.note(pc as usize + 2);
                                g.pow(pc as usize + 2)
                            }
                            DerefMode::Fp => {
                                g.note(fp as usize);
                                g.pow(fp as usize)
                            }
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
                        bytecode_read,
                    });
                    if cond.is_zero() {
                        pc += 1;
                    } else {
                        pc = g.log(dest).expect("JUMP target not a g-power");
                        fp = g.log(frame).expect("JUMP fp not a g-power");
                    }
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
        assert_eq!(fp, 0, "main must halt at the sentinel pc g^{{B-1}} in frame 0");
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
        // A hand-assembled program carries no blocks and has to land on powers of two
        // by itself, which `Layout` checks.
        if !self.filler.is_empty() {
            let zero_digest = blake2s_compress([F64::ZERO; 4], [F64::ZERO; 4], [F64::ZERO; 4], [F64::ZERO; 2]);
            for (block_pc, size, traversals) in super::filler::cycles(&self.filler, base_counts) {
                let top = g.pow(block_pc as usize);
                for _ in 0..traversals {
                    for pc in block_pc..=block_pc + size {
                        let bytecode_read = fetch(pc);
                        let (fp, ts) = (0, F64::ZERO);
                        let closing = pc == block_pc + size;
                        match self.prog[pc as usize] {
                            // Zero operands, and zero is the result of all four.
                            op @ (Op::Xor64 { .. } | Op::Mul64 { .. } | Op::AddU64 { .. } | Op::MulU64 { .. }) => {
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
                                    acc: std::array::from_fn(|_| m.padding_access()),
                                    bytecode_read,
                                });
                            }
                            Op::Set { k, .. } => set.push(Srow {
                                pc,
                                fp,
                                ts,
                                v_old: k,
                                acc: [m.padding_access()],
                                bytecode_read,
                            }),
                            Op::Deref { mode, .. } => deref.push(Drow {
                                pc,
                                fp,
                                ts,
                                p: F64::ZERO,
                                v3: F64::ZERO,
                                v2_old: match mode {
                                    DerefMode::Cell => F64::ZERO,
                                    DerefMode::Pc => g.pow(pc as usize + 2),
                                    DerefMode::Fp => F64::ONE,
                                },
                                acc: std::array::from_fn(|_| m.padding_access()),
                                bytecode_read,
                            }),
                            Op::Jump { .. } => jump.push(Jrow {
                                pc,
                                fp,
                                ts,
                                cond: if closing { top } else { F64::ZERO },
                                dest: if closing { top } else { F64::ZERO },
                                frame: if closing { F64::ONE } else { F64::ZERO },
                                acc: std::array::from_fn(|_| m.padding_access()),
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
                                    acc: std::array::from_fn(|_| m.padding_access()),
                                    bytecode_read,
                                });
                            }
                        }
                        steps += 1;
                    }
                }
            }
        }

        if let Some(p) = &prof {
            self.print_profile(p);
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
            unconstrained_reads,
            trace,
        }
    }

    /// `DBG_PROF=1`: the run's cycles by function, from its per-pc step counts.
    fn print_profile(&self, p: &[u64]) {
        let steps: u64 = p.iter().sum();
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
            eprintln!("== DBG_PROF: per-pc counts written to {path}");
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
}
