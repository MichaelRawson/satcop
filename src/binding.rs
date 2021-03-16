use crate::block::{Block, BlockMap, Id, Off, Range};
use crate::syntax::{Symbol, Term, Var};

#[derive(Debug, Clone, Copy)]
pub(crate) struct Bound(Id<Var>);

#[derive(Debug, Default)]
pub(crate) struct Bindings {
    bound: BlockMap<Var, Option<Off<Term>>>,
    trail: Block<Bound>,
}

impl Bindings {
    pub(crate) fn clear(&mut self) {
        self.bound.clear();
        self.trail.clear();
    }

    pub(crate) fn ensure_capacity(&mut self, len: Id<Var>) {
        self.bound.resize_with(len, Default::default);
    }

    pub(crate) fn mark(&self) -> Id<Bound> {
        self.trail.len()
    }

    pub(crate) fn undo_to_mark(&mut self, mark: Id<Bound>) {
        for id in Range::new(mark, self.trail.len()) {
            let Bound(x) = self.trail[id];
            self.bound[x] = None;
        }
        self.trail.truncate(mark);
    }

    pub(crate) fn resolve(
        &self,
        terms: &Block<Term>,
        mut term: Off<Term>,
    ) -> Off<Term> {
        while terms[term.id].is_var() {
            let x = terms[term.id].as_var().offset(term.offset);
            if let Some(bound) = self.bound[x] {
                term = bound;
            } else {
                break;
            }
        }
        term
    }

    pub(crate) fn unify(
        &mut self,
        syms: &Block<Symbol>,
        terms: &Block<Term>,
        mut left: Off<Term>,
        mut right: Off<Term>,
    ) -> bool {
        let lsym = terms[left.id].as_sym();
        let rsym = terms[right.id].as_sym();
        if lsym != rsym {
            return false;
        }
        let arity = syms[lsym].arity;
        for _ in 0..arity {
            left.id.increment();
            right.id.increment();
            let s = Off::new(terms[left.id].as_arg(), left.offset);
            let t = Off::new(terms[right.id].as_arg(), right.offset);
            let s = self.resolve(terms, s);
            let t = self.resolve(terms, t);
            match (terms[s.id].is_var(), terms[t.id].is_var()) {
                (true, true) => {
                    let x = terms[s.id].as_var().offset(s.offset);
                    let y = terms[t.id].as_var().offset(t.offset);
                    if x != y {
                        self.bind(x, t);
                    }
                }
                (true, false) => {
                    let x = terms[s.id].as_var().offset(s.offset);
                    if !self.try_bind(syms, terms, x, t) {
                        return false;
                    }
                }
                (false, true) => {
                    let x = terms[t.id].as_var().offset(t.offset);
                    if !self.try_bind(syms, terms, x, s) {
                        return false;
                    }
                }
                (false, false) => {
                    if !self.unify(syms, terms, s, t) {
                        return false;
                    }
                }
            }
        }
        true
    }

    pub(crate) fn equal(
        &mut self,
        syms: &Block<Symbol>,
        terms: &Block<Term>,
        left: Off<Term>,
        right: Off<Term>,
    ) -> bool {
        let mut left = self.resolve(terms, left);
        let mut right = self.resolve(terms, right);
        let lvar = terms[left.id].is_var();
        let rvar = terms[right.id].is_var();
        if lvar != rvar {
            return false;
        }
        if lvar && rvar {
            let x = terms[left.id].as_var().offset(left.offset);
            let y = terms[right.id].as_var().offset(right.offset);
            return x == y;
        }
        let lsym = terms[left.id].as_sym();
        let rsym = terms[right.id].as_sym();
        if lsym != rsym {
            return false;
        }
        let arity = syms[lsym].arity;
        for _ in 0..arity {
            left.id.increment();
            right.id.increment();
            let s = Off::new(terms[left.id].as_arg(), left.offset);
            let t = Off::new(terms[right.id].as_arg(), right.offset);
            if !self.equal(syms, terms, s, t) {
                return false;
            }
        }
        true
    }

    pub(crate) fn occurs(
        &self,
        syms: &Block<Symbol>,
        terms: &Block<Term>,
        x: Id<Var>,
        mut t: Off<Term>,
    ) -> bool {
        if terms[t.id].is_var() {
            let t = terms[t.id].as_var().offset(t.offset);
            x == t
        } else {
            let arity = syms[terms[t.id].as_sym()].arity;
            for _ in 0..arity {
                t.id.increment();
                let t = Off::new(terms[t.id].as_arg(), t.offset);
                let t = self.resolve(terms, t);
                if self.occurs(syms, terms, x, t) {
                    return true;
                }
            }
            false
        }
    }

    fn try_bind(
        &mut self,
        syms: &Block<Symbol>,
        terms: &Block<Term>,
        x: Id<Var>,
        t: Off<Term>,
    ) -> bool {
        if self.occurs(syms, terms, x, t) {
            return false;
        }
        self.bind(x, t);
        true
    }

    fn bind(&mut self, x: Id<Var>, t: Off<Term>) {
        self.trail.push(Bound(x));
        self.bound[x] = Some(t);
    }
}
