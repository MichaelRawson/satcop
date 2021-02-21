use crate::block::{Block, Id, Off, Range};
use crate::syntax::{Sym, Trm, Var};
use std::ops::Index;

#[derive(Debug, Clone, Copy)]
pub(crate) struct Bound(Var);

#[derive(Debug, Default)]
pub(crate) struct Bindings {
    bound: Block<Option<Off<Trm>>>,
    trail: Block<Bound>,
}

impl Bindings {
    pub(crate) fn ensure_capacity(&mut self, max: Var) {
        self.bound.ensure_capacity(Id::new(max.0), Default::default);
    }

    pub(crate) fn mark(&self) -> Id<Bound> {
        self.trail.len()
    }

    pub(crate) fn undo_to_mark(&mut self, mark: Id<Bound>) {
        for id in Range::new(mark, self.trail.len()) {
            let Bound(Var(x)) = self.trail[id];
            self.bound[Id::new(x)] = None;
        }
        self.trail.truncate(mark);
    }

    pub(crate) fn resolve(
        &self,
        terms: &Block<Trm>,
        mut term: Off<Trm>,
    ) -> Off<Trm> {
        while terms[term.id].is_var() {
            let x = terms[term.id].as_var().offset(term.offset);
            if let Some(bound) = self[x] {
                term = bound;
            } else {
                break;
            }
        }
        term
    }

    pub(crate) fn unify(
        &mut self,
        syms: &Block<Sym>,
        terms: &Block<Trm>,
        mut left: Off<Trm>,
        mut right: Off<Trm>,
    ) -> bool {
        let lsym = terms[left.id].as_sym();
        let rsym = terms[right.id].as_sym();
        if lsym != rsym {
            return false;
        }
        let arity = syms[lsym].arity;
        for _ in 0..arity {
            left.id.index += 1;
            right.id.index += 1;
            let s = Off::new(terms[left.id].as_arg(), left.offset);
            let t = Off::new(terms[right.id].as_arg(), right.offset);
            let s = self.resolve(terms, s);
            let t = self.resolve(terms, t);
            if terms[s.id].is_var() {
                let x = terms[s.id].as_var().offset(s.offset);
                if !self.try_bind(syms, terms, x, t) {
                    return false;
                }
            } else if terms[t.id].is_var() {
                let x = terms[t.id].as_var().offset(t.offset);
                if !self.try_bind(syms, terms, x, s) {
                    return false;
                }
            } else if !self.unify(syms, terms, s, t) {
                return false;
            }
        }
        true
    }

    pub(crate) fn equal(
        &mut self,
        syms: &Block<Sym>,
        terms: &Block<Trm>,
        mut left: Off<Trm>,
        mut right: Off<Trm>,
    ) -> bool {
        if terms[left.id] != terms[right.id] {
            return false;
        }
        if !terms[left.id].is_sym() {
            return true;
        }
        let sym = terms[left.id].as_sym();
        let arity = syms[sym].arity;
        for _ in 0..arity {
            left.id.index += 1;
            right.id.index += 1;
            let s = Off::new(terms[left.id].as_arg(), left.offset);
            let t = Off::new(terms[right.id].as_arg(), right.offset);
            let s = self.resolve(terms, s);
            let t = self.resolve(terms, t);
            if !self.equal(syms, terms, s, t) {
                return false;
            }
        }
        true
    }

    fn try_bind(
        &mut self,
        syms: &Block<Sym>,
        terms: &Block<Trm>,
        x: Var,
        t: Off<Trm>,
    ) -> bool {
        if self.occurs(syms, terms, x, t) {
            return false;
        }
        self.trail.push(Bound(x));
        self.bound[Id::new(x.0)] = Some(t);
        true
    }

    fn occurs(
        &self,
        syms: &Block<Sym>,
        terms: &Block<Trm>,
        x: Var,
        mut t: Off<Trm>,
    ) -> bool {
        if terms[t.id].is_var() {
            let t = terms[t.id].as_var().offset(t.offset);
            x == t
        } else {
            let arity = syms[terms[t.id].as_sym()].arity;
            for _ in 0..arity {
                t.id.index += 1;
                let t = Off::new(terms[t.id].as_arg(), t.offset);
                let t = self.resolve(terms, t);
                if self.occurs(syms, terms, x, t) {
                    return true;
                }
            }
            false
        }
    }
}

impl Index<Var> for Bindings {
    type Output = Option<Off<Trm>>;
    fn index(&self, x: Var) -> &Self::Output {
        &self.bound[Id::new(x.0)]
    }
}
