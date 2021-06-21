use crate::block::{BlockMap, Id, Range};
use crate::digest::{Digest, DigestMap};
use crate::syntax::*;
use fnv::{FnvHashMap, FnvHashSet};
use std::rc::Rc;

pub(crate) const FALLBACK_GROUNDING: Id<Symbol> = Id::new(0);

#[derive(Default)]
pub(crate) struct Builder {
    matrix: Matrix,
    vars: BlockMap<Var, Id<Term>>,
    terms: DigestMap<Id<Term>>,
    goal_constants: FnvHashMap<Id<Symbol>, u32>,
    goals: Vec<Id<Clause>>,
    positives: Vec<Id<Clause>>,
    has_equality: bool,
    has_non_goal: bool,
}

impl Builder {
    pub(crate) fn initialise(&mut self) {
        self.new_symbol(Symbol {
            arity: 0,
            sort: Sort::Obj,
            name: Name::Grounding,
        });
        self.new_symbol(Symbol {
            arity: 2,
            sort: Sort::Bool,
            name: Name::Equality,
        });
    }

    pub(crate) fn have_conjecture(&mut self) {
        self.matrix.have_conjecture = true;
    }

    pub(crate) fn finish(mut self) -> Matrix {
        if self.has_equality {
            self.add_equality_axioms();
        }
        self.matrix.grounding_constant = self
            .goal_constants
            .drain()
            .max_by_key(|(_, count)| *count)
            .map(|(sym, _)| sym)
            .unwrap_or(FALLBACK_GROUNDING);
        if self.goals.is_empty() || !self.has_non_goal {
            self.matrix.start = self.positives;
        } else {
            self.matrix.start = self.goals;
        }
        self.matrix
    }

    pub(crate) fn new_symbol(&mut self, sym: Symbol) -> Id<Symbol> {
        let id = self.matrix.symbols.push(sym);
        self.matrix.index.push([vec![], vec![]]);
        id
    }

    pub(crate) fn clause(
        &mut self,
        clause: CNF,
        vars: Id<Var>,
        info: Info,
        constraints: bool,
    ) {
        let positive = clause.0.iter().all(|lit| lit.pol);
        let id = self.matrix.clauses.len();
        while vars > self.vars.len() {
            let var = self.vars.len();
            self.vars.push(self.matrix.terms.push(Term::var(var)));
        }
        let mut disequations = FnvHashSet::default();
        let lstart = self.matrix.literals.len();
        for literal in clause.0 {
            self.literal(&mut disequations, id, info.is_goal, literal);
        }
        let lstop = self.matrix.literals.len();
        let literals = Range::new(lstart, lstop);
        for id1 in literals {
            let lit1 = self.matrix.literals[id1];
            for id2 in Range::new(id1.offset(1), lstop) {
                let lit2 = self.matrix.literals[id2];
                if lit1.pol != lit2.pol {
                    let left = lit1.atom;
                    let right = lit2.atom;
                    let sym1 = self.matrix.terms[left];
                    let sym2 = self.matrix.terms[right];
                    if sym1 == sym2 {
                        disequations.insert(Disequation { left, right });
                    }
                }
            }
        }
        let dstart = self.matrix.disequations.len();
        if constraints {
            for diseq in &disequations {
                if self.possibly_equal(diseq.left, diseq.right)
                    && !self.subsumed(
                        &disequations,
                        diseq.left,
                        diseq.right,
                        true,
                    )
                {
                    self.matrix.disequations.push(*diseq);
                }
            }
        }
        let dstop = self.matrix.disequations.len();
        let disequations = Range::new(dstart, dstop);
        let id = self.matrix.clauses.push(Clause {
            vars,
            literals,
            disequations,
        });
        if positive {
            self.positives.push(id);
        }
        if info.is_goal {
            self.goals.push(id);
        } else {
            self.has_non_goal = true;
        }
        self.matrix.info.push(info);
    }

    fn literal(
        &mut self,
        disequations: &mut FnvHashSet<Disequation>,
        cls: Id<Clause>,
        is_goal: bool,
        literal: NNFLiteral,
    ) -> Id<Literal> {
        let pol = literal.pol;
        let atom = self.term(is_goal, &literal.atom);
        let symbol = self.matrix.terms[atom].as_sym();
        if symbol == EQUALITY {
            self.has_equality = true;
            if pol {
                let mut left = self.matrix.terms[atom.offset(1)].as_arg();
                let mut right = self.matrix.terms[atom.offset(2)].as_arg();
                if left > right {
                    std::mem::swap(&mut left, &mut right);
                }
                disequations.insert(Disequation { left, right });
            }
        }
        let lit = self.matrix.literals.push(Literal { pol, atom });
        self.matrix.index[symbol][pol as usize].push(Position { cls, lit });
        lit
    }

    fn term(&mut self, is_goal: bool, term: &Rc<FOFTerm>) -> Id<Term> {
        match &**term {
            FOFTerm::Var(y) => self.vars[*y],
            FOFTerm::Fun(f, ts) => {
                if is_goal
                    && self.matrix.symbols[*f].arity == 0
                    && self.matrix.symbols[*f].sort == Sort::Obj
                {
                    *self.goal_constants.entry(*f).or_default() += 1;
                }
                let mut digest = Digest::default();
                digest.update(f.as_u32());
                let mut args = vec![];
                for t in ts {
                    let t = self.term(is_goal, t);
                    args.push(t);
                    digest.update(t.as_u32());
                }
                if let Some(shared) = self.terms.get(&digest) {
                    return *shared;
                }
                let id = self.matrix.terms.push(Term::sym(*f));
                for arg in args {
                    self.matrix.terms.push(Term::arg(arg));
                }
                self.terms.insert(digest, id);
                id
            }
        }
    }

    fn possibly_equal(&self, mut left: Id<Term>, mut right: Id<Term>) -> bool {
        if left == right {
            return true;
        }
        if self.matrix.terms[left].is_var() {
            return !self.occurs(self.matrix.terms[left].as_var(), right);
        }
        if self.matrix.terms[right].is_var() {
            return !self.occurs(self.matrix.terms[right].as_var(), left);
        }
        let lsym = self.matrix.terms[left].as_sym();
        let rsym = self.matrix.terms[right].as_sym();
        if lsym != rsym {
            return false;
        }
        let arity = self.matrix.symbols[lsym].arity;
        for _ in 0..arity {
            left.increment();
            right.increment();
            if !self.possibly_equal(
                self.matrix.terms[left].as_arg(),
                self.matrix.terms[right].as_arg(),
            ) {
                return false;
            }
        }
        true
    }

    fn subsumed(
        &self,
        disequations: &FnvHashSet<Disequation>,
        mut left: Id<Term>,
        mut right: Id<Term>,
        top: bool,
    ) -> bool {
        if !top
            && (disequations.contains(&Disequation { left, right })
                || disequations.contains(&Disequation {
                    left: right,
                    right: left,
                }))
        {
            return true;
        }
        if self.matrix.terms[left].is_var()
            || self.matrix.terms[right].is_var()
        {
            return false;
        }
        let sym = self.matrix.terms[left].as_sym();
        let arity = self.matrix.symbols[sym].arity;
        for _ in 0..arity {
            left.increment();
            right.increment();
            if self.subsumed(
                disequations,
                self.matrix.terms[left].as_arg(),
                self.matrix.terms[right].as_arg(),
                false,
            ) {
                return true;
            }
        }
        false
    }

    fn occurs(&self, x: Id<Var>, mut t: Id<Term>) -> bool {
        if self.matrix.terms[t].is_var() {
            x == self.matrix.terms[t].as_var()
        } else {
            let sym = self.matrix.terms[t].as_sym();
            let arity = self.matrix.symbols[sym].arity;
            for _ in 0..arity {
                t.increment();
                if self.occurs(x, self.matrix.terms[t].as_arg()) {
                    return true;
                }
            }
            false
        }
    }

    fn add_equality_axioms(&mut self) {
        let info = Info {
            is_goal: false,
            source: Source::Equality,
        };
        let v0 = Rc::new(FOFTerm::Var(Id::new(0)));
        let v1 = Rc::new(FOFTerm::Var(Id::new(1)));
        self.clause(
            CNF(vec![NNFLiteral {
                pol: true,
                atom: Rc::new(FOFTerm::Fun(
                    EQUALITY,
                    vec![v0.clone(), v0.clone()],
                )),
            }]),
            Id::new(1),
            info.clone(),
            false,
        );
        let v2 = Rc::new(FOFTerm::Var(Id::new(2)));
        self.clause(
            CNF(vec![
                NNFLiteral {
                    pol: false,
                    atom: Rc::new(FOFTerm::Fun(
                        EQUALITY,
                        vec![v0.clone(), v1.clone()],
                    )),
                },
                NNFLiteral {
                    pol: true,
                    atom: Rc::new(FOFTerm::Fun(
                        EQUALITY,
                        vec![v1.clone(), v0.clone()],
                    )),
                },
            ]),
            Id::new(2),
            info.clone(),
            true,
        );
        self.clause(
            CNF(vec![
                NNFLiteral {
                    pol: false,
                    atom: Rc::new(FOFTerm::Fun(
                        EQUALITY,
                        vec![v0.clone(), v1.clone()],
                    )),
                },
                NNFLiteral {
                    pol: false,
                    atom: Rc::new(FOFTerm::Fun(
                        EQUALITY,
                        vec![v1, v2.clone()],
                    )),
                },
                NNFLiteral {
                    pol: true,
                    atom: Rc::new(FOFTerm::Fun(EQUALITY, vec![v0, v2])),
                },
            ]),
            Id::new(3),
            info.clone(),
            true,
        );
        for id in self.matrix.symbols.range() {
            let sym = &self.matrix.symbols[id];
            if !sym.name.needs_congruence() {
                continue;
            }
            let arity = sym.arity;
            let sort = sym.sort;
            if arity == 0 {
                continue;
            }
            let mut lits = vec![];
            let mut args1 = vec![];
            let mut args2 = vec![];
            for i in 0..arity {
                let v1 = Rc::new(FOFTerm::Var(Id::new(2 * i)));
                let v2 = Rc::new(FOFTerm::Var(Id::new(2 * i + 1)));
                lits.push(NNFLiteral {
                    pol: false,
                    atom: Rc::new(FOFTerm::Fun(
                        EQUALITY,
                        vec![v1.clone(), v2.clone()],
                    )),
                });
                args1.push(v1.clone());
                args2.push(v2.clone());
            }
            let t1 = Rc::new(FOFTerm::Fun(id, args1));
            let t2 = Rc::new(FOFTerm::Fun(id, args2));
            match sort {
                Sort::Obj => {
                    lits.push(NNFLiteral {
                        pol: true,
                        atom: Rc::new(FOFTerm::Fun(EQUALITY, vec![t1, t2])),
                    });
                }
                Sort::Bool => {
                    lits.push(NNFLiteral {
                        pol: false,
                        atom: t1,
                    });
                    lits.push(NNFLiteral {
                        pol: true,
                        atom: t2,
                    });
                }
            }
            self.clause(CNF(lits), Id::new(arity * 2), info.clone(), true);
        }
    }
}
