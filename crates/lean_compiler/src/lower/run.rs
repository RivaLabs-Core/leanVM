//! Run values: consecutive cells read and written as one value. A BLAKE2s digest
//! is a run of four.
//!
//! An instruction reads only frame cells, so a heap slice used as a value is copied
//! onto the stack first, one `DEREF` a cell. A copy between frame runs is one
//! instruction a cell.

use super::*;

impl FnLower<'_> {
    /// How many cells the value `e` spans, or `None` for a scalar. Emits nothing.
    pub(super) fn run_len(&self, e: &Expr) -> Option<u32> {
        match e {
            Expr::Var(v) => match self.scope.bound(v)?.val {
                Binding::Stack(_, n) => Some(n),
                _ => None,
            },
            Expr::Slice(_, lo, hi) => match (self.try_const_index(lo), self.try_const_index(hi)) {
                (Some(lo), Some(hi)) if lo < hi => Some(hi - lo),
                _ => plus_k(lo, hi).and_then(|k| u32::try_from(k).ok()),
            },
            Expr::ListLit(elems) => Some(elems.iter().map(|el| self.run_len(el).unwrap_or(1)).sum()),
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

    /// The value `e` as `len` consecutive frame cells, returning the first. A run
    /// already in the frame is used in place; anything else lands in fresh cells.
    pub(super) fn run(&mut self, e: &Expr, len: u32) -> Off {
        self.expect_run(e, len);
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
        match e {
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

    /// `dst = src` over `len` cells, cell by cell.
    pub(super) fn copy_run(&mut self, src: Off, dst: Off, len: u32) {
        if src == dst {
            return;
        }
        for k in 0..len {
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
