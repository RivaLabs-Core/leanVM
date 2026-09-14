//! Run values: consecutive cells read and written as one value. A 192-bit element
//! is a run of three cells, its limbs low first; a BLAKE2s digest is a run of four.
//!
//! An instruction reads only frame cells, so a heap slice used as a value is copied
//! onto the stack first, one `DEREF` a cell. A copy between frame runs is an
//! `XOR192` against a pooled zero run, one instruction per three cells.

use super::*;

impl FnLower<'_> {
    /// How many cells the value `e` spans, or `None` for a scalar. Emits nothing.
    pub(super) fn run_len(&self, e: &Expr) -> Option<u32> {
        match e {
            Expr::Var(v) => match self.scope.bound(v)?.val {
                Binding::Stack(_, n) => Some(n),
                Binding::Const192(_) => Some(3),
                _ => None,
            },
            Expr::Slice(_, lo, hi) => match (self.try_const_index(lo), self.try_const_index(hi)) {
                (Some(lo), Some(hi)) if lo < hi => Some(hi - lo),
                _ => plus_k(lo, hi).and_then(|k| u32::try_from(k).ok()),
            },
            Expr::ListLit(elems) => Some(elems.iter().map(|el| self.run_len(el).unwrap_or(1)).sum()),
            Expr::Call(f, _) if parser::RUN192_BUILTINS.contains(&f.as_str()) => Some(3),
            Expr::Call(f, _) => match self.callee_def(f)?.return_shapes.as_slice() {
                [Shape::StackBuf(n)] => Some(*n),
                _ => None,
            },
            _ => None,
        }
    }

    fn expect_run(&self, e: &Expr, len: u32) {
        match self.run_len(e) {
            Some(n) if n == len => {}
            Some(n) => self.fail(format!("expected a {len}-cell value, got a {n}-cell one: `{e:?}`")),
            None => self.fail(format!("expected a {len}-cell value, got the scalar `{e:?}`")),
        }
    }

    /// The 192-bit constant `e` is, when it is one: an `f192` literal, a name bound
    /// to one, a list of three constant words, or a 192-bit builtin over constants.
    pub(super) fn const192(&self, e: &Expr) -> Option<F192> {
        match e {
            Expr::Var(v) => match self.scope.bound(v)?.val {
                Binding::Const192(c) => Some(c),
                _ => None,
            },
            Expr::Call(f, args) if f == "f192" && args.len() == 3 => {
                let limb = |a: &Expr| self.try_const_int(a).and_then(lit_field);
                Some(F192::new(limb(&args[0])?.0, limb(&args[1])?.0, limb(&args[2])?.0))
            }
            Expr::ListLit(elems) if elems.len() == 3 && elems.iter().all(|el| self.run_len(el).is_none()) => {
                let w = |i: usize| self.try_field_const(&elems[i]);
                Some(F192::new(w(0)?.0, w(1)?.0, w(2)?.0))
            }
            Expr::Call(f, args) if matches!(f.as_str(), "add192" | "mul192" | "div192") && args.len() == 2 => {
                // A product with a zero factor is zero whatever the other one is.
                if f == "mul192" && args.iter().any(|a| self.const192(a) == Some(F192::ZERO)) {
                    return Some(F192::ZERO);
                }
                let (a, b) = (self.const192(&args[0])?, self.const192(&args[1])?);
                match f.as_str() {
                    "add192" => Some(a + b),
                    "mul192" => Some(a * b),
                    _ => (!b.is_zero()).then(|| a * b.inv()),
                }
            }
            _ => None,
        }
    }

    /// The operand a 192-bit builtin reduces to without an instruction: `a + 0`,
    /// `a · 1` and `a / 1` are `a`.
    fn identity192<'e>(&self, f: &str, args: &'e [Expr]) -> Option<&'e Expr> {
        let [a, b] = args else { return None };
        let (ca, cb) = (self.const192(a), self.const192(b));
        match f {
            "add192" if ca == Some(F192::ZERO) => Some(b),
            "add192" if cb == Some(F192::ZERO) => Some(a),
            "mul192" if ca == Some(F192::ONE) => Some(b),
            "mul192" | "div192" if cb == Some(F192::ONE) => Some(a),
            _ => None,
        }
    }

    /// The value `e` as `len` consecutive frame cells, returning the first. A run
    /// already in the frame is used in place; anything else lands in fresh cells.
    pub(super) fn run(&mut self, e: &Expr, len: u32) -> Off {
        self.expect_run(e, len);
        if let Some(c) = self.const192(e) {
            return self.const_run(&[F64(c.c0), F64(c.c1), F64(c.c2)]);
        }
        if let Expr::Call(f, args) = e
            && let Some(x) = self.identity192(f, args)
        {
            return self.run(x, len);
        }
        match e {
            Expr::Var(_) => self.stack_of(e).expect("a run name").0,
            Expr::Slice(..) => match self.cell_run(e) {
                CellRun::Stack { base, .. } => base,
                CellRun::Heap { ptr, lo, len } => {
                    if let Some(&t) = self.scope.run_loads.get(&(ptr, lo, len)) {
                        // The dominating DEREFs may have deferred equalities between
                        // unwritten cells.
                        for k in 0..len {
                            self.pending.push(Hint::Resolved(RHint::ResolveDeref {
                                ptr,
                                offset: lo + k,
                                dst: t + k,
                            }));
                        }
                        return t;
                    }
                    let t = self.alloc_stack(len);
                    for k in 0..len {
                        self.deref(ptr, lo + k, t + k, DerefMode::Cell);
                    }
                    self.scope.run_loads.insert((ptr, lo, len), t);
                    t
                }
            },
            Expr::ListLit(elems) => {
                if let Some(words) = elems
                    .iter()
                    .map(|el| self.try_field_const(el))
                    .collect::<Option<Vec<_>>>()
                {
                    return self.const_run(&words);
                }
                let t = self.alloc_stack(len);
                self.run_into(e, t, len);
                t
            }
            Expr::Call(f, args) if f == "f192" => {
                let words = self.f192_words(args);
                self.const_run(&words)
            }
            Expr::Call(f, args) if f == "add192" || f == "mul192" => {
                let (a, b) = self.run_operands(f, args);
                let op = if f == "add192" { PureOp::Xor192 } else { PureOp::Mul192 };
                self.pure(op, a, b)
            }
            Expr::Call(f, _) if f == "div192" => {
                let t = self.alloc_stack(3);
                self.run_into(e, t, 3);
                t
            }
            Expr::Call(f, args) => {
                let dst = self.call(f, args, 1)[0];
                match self.inline_stack_ret.take().and_then(|b| b.into_iter().next()) {
                    Some(RetBind::Stack(base, _)) => base,
                    _ => dst,
                }
            }
            _ => unreachable!("`run_len` names every run shape"),
        }
    }

    /// Evaluate the value `e` into the `len` cells at `dst`. A cell already written
    /// makes its write the equality assertion, as for any store.
    pub(super) fn run_into(&mut self, e: &Expr, dst: Off, len: u32) {
        self.expect_run(e, len);
        if let Expr::Call(f, args) = e
            && self.const192(e).is_none()
            && let Some(x) = self.identity192(f, args)
        {
            return self.run_into(x, dst, len);
        }
        match e {
            Expr::Call(f, args) if f == "add192" || f == "mul192" => {
                let (a, b) = self.run_operands(f, args);
                if f == "add192" {
                    self.emit(LOp::Xor192 { a, b, c: dst });
                } else {
                    self.emit(LOp::Mul192 { a, b, c: dst });
                }
            }
            // The quotient is the product's unwritten operand: witness generation
            // back-solves it and the `MUL192` pins `q·b == a`.
            Expr::Call(f, args) if f == "div192" => {
                let (a, b) = self.run_operands(f, args);
                self.emit(LOp::Mul192 { a: dst, b, c: a });
            }
            Expr::Call(f, args) if f == "f192" => {
                for (k, w) in self.f192_words(args).into_iter().enumerate() {
                    self.set_const(dst + k as u32, w);
                }
            }
            Expr::ListLit(elems) => {
                let mut off = 0;
                for el in elems {
                    match self.run_len(el) {
                        Some(w) => {
                            self.run_into(el, dst + off, w);
                            off += w;
                        }
                        None => {
                            self.expr_into(el, dst + off);
                            off += 1;
                        }
                    }
                }
            }
            // A heap run `DEREF`s straight into `dst`: either side may be the unset one.
            Expr::Slice(arr, ..) if self.stack_of(arr).is_none() => {
                let CellRun::Heap { ptr, lo, .. } = self.cell_run(e) else {
                    unreachable!("a heap slice")
                };
                for k in 0..len {
                    self.deref(ptr, lo + k, dst + k, DerefMode::Cell);
                }
            }
            _ => {
                let src = self.run(e, len);
                self.copy_run(src, dst, len);
            }
        }
    }

    /// `dst = src` over `len` cells: `XOR192` against the pooled zero run three
    /// cells at a time, the rest cell by cell.
    pub(super) fn copy_run(&mut self, src: Off, dst: Off, len: u32) {
        if src == dst {
            return;
        }
        let mut k = 0;
        if len >= 3 {
            let zero = self.const_run(&[F64::ZERO; 3]);
            while k + 3 <= len {
                self.emit(LOp::Xor192 {
                    a: src + k,
                    b: zero,
                    c: dst + k,
                });
                k += 3;
            }
        }
        for k in k..len {
            self.copy(src + k, dst + k);
        }
    }

    /// A run holding `words`, shared by every dominated use in scope. Like
    /// [`Self::const_cell`] its `SET`s precede every use and it reverts at a branch
    /// join with the rest of [`Scope`].
    pub(super) fn const_run(&mut self, words: &[F64]) -> Off {
        let key: Vec<u64> = words.iter().map(|w| w.0).collect();
        if let Some(&o) = self.scope.const_runs.get(&key) {
            return o;
        }
        let o = self.alloc_stack(words.len() as u32);
        for (k, &w) in words.iter().enumerate() {
            self.set_const(o + k as u32, w);
            self.scope.const_cells.entry(w.0).or_insert(o + k as u32);
        }
        self.scope.const_runs.insert(key, o);
        o
    }

    /// The three limbs of `f192(c0, c1, c2)`, each a compile-time integer.
    fn f192_words(&self, args: &[Expr]) -> Vec<F64> {
        if args.len() != 3 {
            self.fail("f192(c0, c1, c2) takes three limbs")
        }
        args.iter()
            .map(|a| {
                self.try_const_int(a)
                    .and_then(lit_field)
                    .unwrap_or_else(|| self.fail(format!("an f192 limb is a compile-time 64-bit integer, got `{a:?}`")))
            })
            .collect()
    }

    /// The two three-cell operands of a 192-bit builtin, left first.
    fn run_operands(&mut self, f: &str, args: &[Expr]) -> (Off, Off) {
        let [a, b] = args else {
            self.fail(format!("{f}(a, b) takes two 192-bit values"))
        };
        (self.run(a, 3), self.run(b, 3))
    }

    /// `assert_eq192(a, b)`: `XOR192` into the pooled zero run, whose double write is
    /// the assertion, as for `assert a == b`.
    pub(super) fn lower_assert_eq192(&mut self, a: &Expr, b: &Expr) {
        let (la, lb) = (self.run(a, 3), self.run(b, 3));
        let zero = self.const_run(&[F64::ZERO; 3]);
        self.emit(LOp::Xor192 { a: la, b: lb, c: zero });
    }

    /// `assert_ne192(a, b)`: `x = a + b`, a hinted `inv = x⁻¹`, and `MUL192 x·inv`
    /// into the pooled one run. Sound as for `assert a != b`: `x = 0` makes the
    /// product zero whatever the hint.
    pub(super) fn lower_assert_ne192(&mut self, a: &Expr, b: &Expr) {
        let (la, lb) = (self.run(a, 3), self.run(b, 3));
        let x = self.pure(PureOp::Xor192, la, lb);
        let one = self.const_run(&[F64::ONE, F64::ZERO, F64::ZERO]);
        let inv = self.alloc_stack(3);
        self.pending
            .push(Hint::Resolved(RHint::Inverse192 { value: x, dst: inv }));
        self.emit(LOp::Mul192 { a: x, b: inv, c: one });
    }

    /// `buf[lo:hi] = value`: a frame run takes the value in place; a heap run takes
    /// it through one `DEREF` a cell, the value lowered first as for a scalar store.
    pub(super) fn lower_store_run(&mut self, target: &Expr, value: &Expr) {
        let Expr::Slice(arr, ..) = target else {
            unreachable!("the parser builds a run store from a slice")
        };
        if self.stack_of(arr).is_some() {
            let CellRun::Stack { base, len } = self.cell_run(target) else {
                unreachable!("a frame slice")
            };
            self.run_into(value, base, len);
            return;
        }
        let len = self
            .run_len(target)
            .unwrap_or_else(|| self.fail(format!("a run store needs a slice of known length, got `{target:?}`")));
        let v = self.run(value, len);
        let CellRun::Heap { ptr, lo, .. } = self.cell_run(target) else {
            unreachable!("a heap slice")
        };
        for k in 0..len {
            self.deref(ptr, lo + k, v + k, DerefMode::Cell);
        }
        // The heap run now equals `v`, so a dominated read of it reuses `v`.
        self.scope.run_loads.entry((ptr, lo, len)).or_insert(v);
    }
}
