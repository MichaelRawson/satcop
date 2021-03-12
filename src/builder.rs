use crate::block::{Block, Id, Range};
use crate::digest::{Digest, DigestMap};
use crate::syntax::*;
use fnv::{FnvHashMap, FnvHashSet};
use std::rc::Rc;

pub(crate) const FALLBACK_GROUNDING: Id<Symbol> = Id::new(0);

pub(crate) struct Builder {
    matrix: Matrix,
    vars: Block<Id<Term>>,
    terms: DigestMap<Id<Term>>,
    goal_constants: FnvHashMap<Id<Symbol>, u32>,
    has_equality: bool,
}

impl Default for Builder {
    fn default() -> Self {
        let matrix = Matrix::default();
        let vars = Block::default();
        let terms = DigestMap::default();
        let goal_constants = FnvHashMap::default();
        let has_equality = false;
        let mut result = Self {
            matrix,
            vars,
            terms,
            goal_constants,
            has_equality,
        };
        result.new_symbol(Symbol {
            arity: 0,
            sort: Sort::Unused,
            name: Name::Unused,
        });
        result.new_symbol(Symbol {
            arity: 2,
            sort: Sort::Bool,
            name: Name::Equality,
        });
        result
    }
}

impl Builder {
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
        self.matrix
    }

    pub(crate) fn new_symbol(&mut self, sym: Symbol) -> Id<Symbol> {
        let id = self.matrix.symbols.push(sym);
        self.matrix.index.block.push([vec![], vec![]]);
        id
    }

    pub(crate) fn clause(
        &mut self,
        clause: CNF,
        vars: u32,
        info: Info,
        constraints: bool,
    ) {
        let id = self.matrix.clauses.len();
        if clause.0.is_empty() || info.is_goal {
            self.matrix.start.push(id);
        }
        while vars > self.vars.len().index {
            let var = Var(self.vars.len().index);
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
            for id2 in Range::new(Id::new(id1.index + 1), lstop) {
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
            for diseq in disequations {
                if self.possibly_equal(diseq.left, diseq.right) {
                    self.matrix.disequations.push(diseq);
                }
            }
        }
        let dstop = self.matrix.disequations.len();
        let disequations = Range::new(dstart, dstop);
        self.matrix.clauses.push(Clause {
            vars,
            literals,
            disequations,
        });
        self.matrix.info.block.push(info);
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
                let mut left =
                    self.matrix.terms[Id::new(atom.index + 1)].as_arg();
                let mut right =
                    self.matrix.terms[Id::new(atom.index + 2)].as_arg();
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
            FOFTerm::Var(Var(y)) => self.vars[Id::new(*y)],
            FOFTerm::Fun(f, ts) => {
                if is_goal
                    && self.matrix.symbols[*f].arity == 0
                    && self.matrix.symbols[*f].sort == Sort::Obj
                {
                    *self.goal_constants.entry(*f).or_default() += 1;
                }
                let mut digest = Digest::default();
                digest.update(f.index);
                let mut args = vec![];
                for t in ts {
                    let t = self.term(is_goal, t);
                    args.push(t);
                    digest.update(t.index);
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
            left.index += 1;
            right.index += 1;
            if !self.possibly_equal(
                self.matrix.terms[left].as_arg(),
                self.matrix.terms[right].as_arg(),
            ) {
                return false;
            }
        }
        true
    }

    fn occurs(&self, x: Var, mut t: Id<Term>) -> bool {
        if self.matrix.terms[t].is_var() {
            x == self.matrix.terms[t].as_var()
        } else {
            let sym = self.matrix.terms[t].as_sym();
            let arity = self.matrix.symbols[sym].arity;
            for _ in 0..arity {
                t.index += 1;
                if self.occurs(x, self.matrix.terms[t].as_arg()) {
                    return true;
                }
            }
            false
        }
    }

    fn add_equality_axioms(&mut self) {
        let v0 = Rc::new(FOFTerm::Var(Var(0)));
        let v1 = Rc::new(FOFTerm::Var(Var(1)));
        let v2 = Rc::new(FOFTerm::Var(Var(2)));
        self.clause(
            CNF(vec![NNFLiteral {
                pol: true,
                atom: Rc::new(FOFTerm::Fun(
                    EQUALITY,
                    vec![v0.clone(), v0.clone()],
                )),
            }]),
            1,
            Info { is_goal: false },
            false,
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
                    pol: true,
                    atom: Rc::new(FOFTerm::Fun(
                        EQUALITY,
                        vec![v1.clone(), v0.clone()],
                    )),
                },
            ]),
            2,
            Info { is_goal: false },
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
            3,
            Info { is_goal: false },
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
                let v1 = Rc::new(FOFTerm::Var(Var(2 * i)));
                let v2 = Rc::new(FOFTerm::Var(Var(2 * i + 1)));
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
                Sort::Unused => unreachable!(),
            }
            self.clause(CNF(lits), arity * 2, Info { is_goal: false }, true);
        }
    }
}
