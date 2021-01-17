use crate::block::{Id, Range};
use crate::matrix::*;
use crate::syntax::*;
use fnv::FnvHashMap;
use std::rc::Rc;

pub(crate) struct Builder {
    matrix: Matrix,
    vars: FnvHashMap<Var, Id<Trm>>,
    funs: FnvHashMap<Vec<Trm>, Id<Trm>>,
    has_equality: bool,
}

impl Default for Builder {
    fn default() -> Self {
        let matrix = Matrix::default();
        let vars = FnvHashMap::default();
        let funs = FnvHashMap::default();
        let has_equality = false;
        let mut result = Self {
            matrix,
            vars,
            funs,
            has_equality,
        };
        result.sym(Sym {
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
        self.matrix
    }

    pub(crate) fn sym(&mut self, sym: Sym) -> Id<Sym> {
        let id = self.matrix.syms.len();
        self.matrix.syms.push(sym);
        self.matrix.index.block.push(Entry {
            pol: [vec![], vec![]],
        });
        id
    }

    fn term(&mut self, term: Term) -> Id<Trm> {
        match term {
            Term::Var(x) => {
                let id = self.matrix.terms.len();
                let matrix = &mut self.matrix;
                *self.vars.entry(x).or_insert_with(|| {
                    matrix.terms.push(Trm::var(x));
                    id
                })
            }
            Term::Fun(f, ts) => {
                let mut args = vec![];
                for t in ts {
                    args.push(Trm::arg(self.term(t)));
                }
                let id = self.matrix.terms.len();
                self.matrix.terms.push(Trm::sym(f));
                for arg in args {
                    self.matrix.terms.push(arg);
                }
                let range = Range::new(id, self.matrix.terms.len());
                let slice = &self.matrix.terms[range];
                match self.funs.get(slice) {
                    Some(result) => {
                        self.matrix.terms.truncate(id);
                        *result
                    }
                    None => {
                        self.funs.insert(slice.into(), id);
                        id
                    }
                }
            }
        }
    }

    fn literal(&mut self, cls: Id<Cls>, literal: CNFLiteral) -> Id<Lit> {
        let id = self.matrix.lits.len();
        let pol = literal.pol;
        let atom = self.term(literal.atom);
        let symbol = self.matrix.terms[atom].as_sym();
        if Sym::is_eq(symbol) {
            self.has_equality = true;
        }
        self.matrix.index[symbol].pol[pol as usize].push(Pos { cls, lit: id });
        self.matrix.lits.push(Lit { pol, atom });
        id
    }

    pub(crate) fn clause(
        &mut self,
        clause: CNFFormula,
        vars: u32,
        info: Info,
    ) {
        let id = self.matrix.clauses.len();
        let start = self.matrix.lits.len();
        for literal in clause.0 {
            self.literal(id, literal);
        }
        let stop = self.matrix.lits.len();
        let lits = Range::new(start, stop);
        if info.is_goal {
            self.matrix.start.push(id);
        }
        self.matrix.clauses.push(Cls { lits, vars });
        self.matrix.info.block.push(info);
    }

    fn add_equality_axioms(&mut self) {
        let eq = Id::new(0);
        self.clause(
            CNFFormula(vec![CNFLiteral {
                pol: true,
                atom: Term::Fun(
                    eq,
                    vec![Term::Var(Var(1)), Term::Var(Var(1))],
                ),
            }]),
            1,
            Info {
                source: Source::EqualityAxiom,
                name: "reflexivity".into(),
                is_goal: false,
            },
        );
        self.clause(
            CNFFormula(vec![
                CNFLiteral {
                    pol: false,
                    atom: Term::Fun(
                        eq,
                        vec![Term::Var(Var(1)), Term::Var(Var(2))],
                    ),
                },
                CNFLiteral {
                    pol: true,
                    atom: Term::Fun(
                        eq,
                        vec![Term::Var(Var(2)), Term::Var(Var(1))],
                    ),
                },
            ]),
            2,
            Info {
                source: Source::EqualityAxiom,
                name: "symmetry".into(),
                is_goal: false,
            },
        );
        self.clause(
            CNFFormula(vec![
                CNFLiteral {
                    pol: false,
                    atom: Term::Fun(
                        eq,
                        vec![Term::Var(Var(1)), Term::Var(Var(2))],
                    ),
                },
                CNFLiteral {
                    pol: false,
                    atom: Term::Fun(
                        eq,
                        vec![Term::Var(Var(2)), Term::Var(Var(3))],
                    ),
                },
                CNFLiteral {
                    pol: true,
                    atom: Term::Fun(
                        eq,
                        vec![Term::Var(Var(1)), Term::Var(Var(3))],
                    ),
                },
            ]),
            3,
            Info {
                source: Source::EqualityAxiom,
                name: "transitivity".into(),
                is_goal: false,
            },
        );
        let cong_name: Rc<str> = "congruence".into();
        for id in self.matrix.syms.range() {
            let sym = &self.matrix.syms[id];
            let arity = sym.arity;
            let sort = sym.sort;
            if arity == 0 {
                continue;
            }
            let mut lits = vec![];
            let mut args1 = vec![];
            let mut args2 = vec![];
            for i in 0..arity {
                let v1 = Var(2 * i + 1);
                let v2 = Var(2 * i + 2);
                lits.push(CNFLiteral {
                    pol: false,
                    atom: Term::Fun(eq, vec![Term::Var(v1), Term::Var(v2)]),
                });
                args1.push(Term::Var(v1));
                args2.push(Term::Var(v2));
            }
            let t1 = Term::Fun(id, args1);
            let t2 = Term::Fun(id, args2);
            match sort {
                Sort::Obj => {
                    lits.push(CNFLiteral {
                        pol: true,
                        atom: Term::Fun(eq, vec![t1, t2]),
                    });
                }
                Sort::Bool => {
                    lits.push(CNFLiteral {
                        pol: false,
                        atom: t1,
                    });
                    lits.push(CNFLiteral {
                        pol: true,
                        atom: t2,
                    });
                }
            }
            self.clause(
                CNFFormula(lits),
                arity * 2,
                Info {
                    source: Source::EqualityAxiom,
                    name: cong_name.clone(),
                    is_goal: false,
                },
            );
        }
    }
}
