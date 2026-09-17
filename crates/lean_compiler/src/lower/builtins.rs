//! The precompile and the hints: the two places a value arrives without an
//! instruction computing it.
//!
//! `blake2s` is a STATEMENT, not an expression: it writes its digest into a
//! four-cell run the caller names, so a pre-written destination checks the digest
//! instead of computing it, by the same write-once rule as any store.
//!
//! A hint writes values the prover chose and the circuit did not, so **the
//! program must constrain them**. A hint names its destination's PHYSICAL cells,
//! and since every store emits there is nothing for the compiler to prepare: a
//! later `s[k] = <checked value>` is a second write of that cell, which is the
//! assertion that pins the hinted value.

use super::*;

/// One word of a `blake2s` message operand: a compile-time constant, a cell, or
/// the list element at this index, evaluated only once its chunk has cells.
#[derive(Clone, Copy)]
enum Word {
    Const(F64),
    Cell(Off),
    Expr(usize),
}

impl FnLower<'_> {
    /// `blake2s(a, b, out)`: the digest of the two 256-bit operands lands in the
    /// existing 4-cell run `out` (write-once: if `out` was already written, this
    /// asserts the digest equals it). A heap `out` slice takes the digest via a
    /// fresh stack run and four `DEREF`s after the hash, the store direction
    /// being the same instruction as the load (write-once fills the unset side).
    /// Keyword arguments set the metadata: `counter=` / `final=` / `last_node=`
    /// build it at compile time, `md=` takes the two cells from values the program
    /// computed.
    fn lower_blake2s(&mut self, args: &[Expr]) {
        let first_kw = args
            .iter()
            .position(|a| matches!(a, Expr::Call(name, _) if name.starts_with("__kw_")))
            .unwrap_or(args.len());
        if first_kw != 3 {
            self.fail("blake2s takes three positional arguments: (a, b, out)")
        };
        if !(args[first_kw..]
            .iter()
            .all(|a| matches!(a, Expr::Call(name, v) if name.starts_with("__kw_") && v.len() == 1)))
        {
            self.fail("keyword arguments must follow the three positional blake2s arguments")
        };
        let mut kwargs: HashMap<&str, &Expr> = HashMap::new();
        for kw in &args[first_kw..] {
            let Expr::Call(name, value) = kw else { unreachable!() };
            let key = name.strip_prefix("__kw_").unwrap();
            if kwargs.insert(key, &value[0]).is_some() {
                self.fail(format!("duplicate blake2s keyword `{key}`"))
            };
        }
        let allowed = ["cv", "counter", "final", "last_node", "md"];
        if !(kwargs.keys().all(|k| allowed.contains(k))) {
            // Sorted: a `HashMap`'s order would make the same mistake report
            // differently between builds.
            let mut bad: Vec<&&str> = kwargs.keys().filter(|k| !allowed.contains(k)).collect();
            bad.sort_unstable();
            self.fail(format!("unknown blake2s keyword {bad:?}; the keywords are {allowed:?}"))
        };
        let customized = kwargs.keys().any(|k| matches!(*k, "counter" | "final" | "last_node"));
        // `md=` hands over the whole metadata as runtime values, so it replaces the
        // three keywords that would otherwise build it.
        let runtime_md = kwargs.get("md").copied();
        if runtime_md.is_some() && customized {
            self.fail("blake2s md= is the whole metadata, so counter=, final= and last_node= cannot come with it")
        };
        if kwargs.contains_key("cv") && !customized && runtime_md.is_none() {
            self.fail(
                "blake2s with cv= requires one of counter=, final=, last_node= or md=, since a chained \
                 block is not the default one-block hash",
            )
        };

        let a = self.blake2s_chunks(&args[0]);
        let b = self.blake2s_chunks(&args[1]);
        let out = self.cell_run(&args[2]);
        if out.cells() != 4 {
            self.fail("a blake2s digest destination spans exactly 4 cells; slice a larger buffer: `buf[lo:lo + 4]`")
        }
        let (c, heap_out) = match out {
            CellRun::Stack { base, .. } => (base, None),
            CellRun::Heap { ptr, lo, .. } => (self.alloc_stack(4), Some((ptr, lo))),
        };
        let cv = match kwargs.get("cv") {
            Some(value) => self.run(value, 4),
            None => self.const_run(&lean_vm::hash_flock::IV),
        };
        let md = match runtime_md {
            // Metadata the program computes, which is what lets a hash whose block
            // count is only known at run time carry the byte counter the standard
            // asks for (doc §sec:prog-byte-counter).
            //
            // Aliasing the digest destination is the one case write-once does not
            // catch: the runner reads the metadata before storing the digest, while
            // the witness reads the finished memory image, so the two disagree and
            // the proof fails its opening rather than saying why.
            Some(expr) => {
                let md = self.run(expr, 2);
                if md + 2 > c && md < c + 4 {
                    self.fail("blake2s md= must not name a cell of the digest destination")
                };
                md
            }
            None => {
                let const_kw = |this: &Self, name: &str, default: u128| -> u128 {
                    kwargs
                        .get(name)
                        .map(|e| {
                            this.try_const_int(e).unwrap_or_else(|| {
                                self.fail(format!(
                                    "BLAKE2s `{name}` must be a compile-time integer, got `{e:?}`; \
                                     a metadata computed at run time goes through md="
                                ))
                            })
                        })
                        .unwrap_or(default)
                };
                // BLAKE2s metadata is just the cumulative byte counter and two flags, so
                // a multi-block hash is `counter = 64 * blocks_before + bytes_in_this_block`
                // and `final = 1` on the last block. The default is the one-block hash of
                // a full 64-byte input, which is what `vmhash::compress` and every Merkle
                // node use.
                let counter = const_kw(self, "counter", 64);
                let counter = u64::try_from(counter)
                    .unwrap_or_else(|_| self.fail(format!("blake2s counter= {counter} does not fit in u64")));
                let f0 = if const_kw(self, "final", if customized { 0 } else { 1 }) != 0 {
                    lean_vm::hash_flock::FINAL_FLAG
                } else {
                    0
                };
                let f1 = if const_kw(self, "last_node", 0) != 0 {
                    u32::MAX
                } else {
                    0
                };
                // A compile-time metadata is a pooled run: one per distinct value
                // per frame, however many compressions read it.
                self.const_run(&lean_vm::hash_flock::metadata(counter, f0, f1))
            }
        };
        self.emit(LOp::Blake2s {
            ins: [a[0], a[1], b[0], b[1]],
            cv,
            c,
            md,
        });
        if let Some((ptr, lo)) = heap_out {
            for k in 0..4 {
                self.deref(ptr, lo + k, c + k, DerefMode::Cell);
            }
        }
    }

    /// The statement-position builtins, `true` if `f` was one of them (else the
    /// caller emits an ordinary call). The `hint_*` ones queue prover-side
    /// advice, re-checked in-circuit by their caller: `hint_decompose_bits`
    /// writes a value's bits into a buffer, `hint_decompose_bits_exponent` the
    /// bits of `n` where the value is `g^n` (a bounded dlog at witness
    /// generation).
    pub(super) fn lower_builtin(&mut self, f: &str, args: &[Expr]) -> bool {
        match f {
            "hint_decompose_bits" | "hint_decompose_bits_exponent" => {
                if args.len() != 3 {
                    self.fail(format!(
                        "{f} takes three arguments, `(bits, value, nbits)`, got {}",
                        args.len()
                    ))
                };
                let nbits = self.const_index(&args[2]);
                if f == "hint_decompose_bits" && nbits > 64 {
                    self.fail(format!(
                        "hint_decompose_bits of a 64-bit word takes at most 64 bits, got {nbits}"
                    ))
                }
                let bits = self.bits_dest(&args[0], nbits, f);
                let value = self.expr(&args[1]);
                self.pending.push(Hint::Resolved(if f == "hint_decompose_bits" {
                    RHint::BitDecompose { value, bits, nbits }
                } else {
                    RHint::BitDecomposeExp { value, bits, nbits }
                }));
            }
            "blake2s" => self.lower_blake2s(args),
            _ => return false,
        }
        true
    }

    /// A `blake2s` message operand as its two chunk bases, each two consecutive
    /// cells. The opcode addresses the chunks independently, so a LIST LITERAL
    /// operand gathers nothing it does not have to: a chunk whose two words already
    /// sit side by side is used in place, a constant one is a pooled run, and any
    /// other chunk is a fresh pair. A computed word is evaluated straight into its
    /// pair, so only a word that already lives in a cell is copied.
    pub(super) fn blake2s_chunks(&mut self, e: &Expr) -> [Off; 2] {
        let Expr::ListLit(elems) = e else {
            let base = self.run(e, 4);
            return [base, base + 2];
        };
        let mut words: Vec<Word> = Vec::new();
        for (i, el) in elems.iter().enumerate() {
            match self.run_len(el) {
                Some(w) => {
                    let base = self.run(el, w);
                    words.extend((base..base + w).map(Word::Cell));
                }
                None => words.push(match (self.try_field_const(el), el) {
                    (Some(v), _) => Word::Const(v),
                    (None, Expr::Var(_)) => Word::Cell(self.expr(el)),
                    (None, Expr::Index(arr, idx)) if self.stack_of(arr).is_some() => {
                        Word::Cell(self.frame_cell(arr, idx).expect("a StackBuf element"))
                    }
                    (None, _) => Word::Expr(i),
                }),
            }
        }
        if words.len() != 4 {
            self.fail(format!(
                "a blake2s message operand is 4 words, this list spells {}",
                words.len()
            ))
        }
        let mut chunks = [0; 2];
        for (i, chunk) in chunks.iter_mut().enumerate() {
            *chunk = match (words[2 * i], words[2 * i + 1]) {
                (Word::Const(x), Word::Const(y)) => self.const_run(&[x, y]),
                (Word::Cell(x), Word::Cell(y)) if y == x + 1 => x,
                (x, y) => {
                    let t = self.alloc_stack(2);
                    for (k, w) in [x, y].into_iter().enumerate() {
                        match w {
                            Word::Const(v) => self.set_const(t + k as u32, v),
                            Word::Cell(c) => self.copy(c, t + k as u32),
                            Word::Expr(i) => self.expr_into(&elems[i], t + k as u32),
                        }
                    }
                    t
                }
            };
        }
        chunks
    }

    /// A computed-advice bit buffer's destination ([`BitsDest`]). Not
    /// [`Self::cell_run`]: these builtins take a bare `HeapBuf` and carry the
    /// length in `nbits`, where a cell run would demand a slice.
    pub(super) fn bits_dest(&mut self, e: &Expr, nbits: u32, what: &str) -> BitsDest {
        match self.stack_of(e) {
            Some((base, len)) => {
                if len < nbits {
                    self.fail(format!(
                        "{what} needs {nbits} cells, its StackBuf destination has {len}"
                    ))
                };
                BitsDest::Stack(base)
            }
            None => {
                // Bounds-checked like the `StackBuf` arm above, and like every
                // other heap consumer. Without this a `HeapBuf` destination wrote
                // `nbits` cells with nothing checking the buffer held them, so the
                // bits ran on into the next buffer while the same call with a
                // `StackBuf` destination was rejected.
                self.check_heap_bound(e, 0, u128::from(nbits));
                BitsDest::Heap(self.expr(e))
            }
        }
    }

    /// `hint_witness(dest, "name")`: resolve `dest` to a run of cells and
    /// queue the witness-fill hint (no instructions: the values are written
    /// by the runner before the next instruction executes, unconstrained).
    pub(super) fn lower_hint_witness(&mut self, dest: &Expr, name: &str) {
        let name = name.to_string();
        let hint = match self.cell_run(dest) {
            CellRun::Stack { base, len } => RHint::WitnessStack { name, base, len },
            CellRun::Heap { ptr, lo, len } => RHint::WitnessHeap { name, ptr, lo, len },
        };
        self.pending.push(Hint::Resolved(hint));
    }
}
