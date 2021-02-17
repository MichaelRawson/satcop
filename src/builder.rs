use crate::block::{Id, Range};
use crate::digest::{Digest, DigestMap};
use crate::matrix::*;
use crate::syntax::*;
use std::rc::Rc;

pub(crate) struct Builder {
    matrix: Matrix,
    vars: Vec<Id<Trm>>,
    args: Vec<Id<Trm>>,
    terms: DigestMap<Id<Trm>>,
    has_equality: bool,
}

impl Default for Builder {
    fn default() -> Self {
        let matrix = Matrix::default();
        let vars = vec![];
        let args = vec![];
        let terms = DigestMap::default();
        let has_equality = false;
        let mut result = Self {
            matrix,
            vars,
            args,
            terms,
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
        for id in self.matrix.syms.range() {
            for pol in 0..2 {
                let index = &mut self.matrix.index[id].pol[pol];
                let clauses = &self.matrix.clauses;
                index.sort_unstable_by_key(|pos| clauses[pos.cls].lits.len());
            }
        }
        self.matrix
    }

    pub(crate) fn sym(&mut self, sym: Sym) -> Id<Sym> {
        let id = self.matrix.syms.push(sym);
        self.matrix.index.block.push(Entry {
            pol: [vec![], vec![]],
        });
        id
    }

    fn term(&mut self, term: Term) -> Id<Trm> {
        match term {
            Term::Var(x) => {
                let Var(y) = x;
                let y = y as usize;
                if y >= self.vars.len() {
                    let matrix = &mut self.matrix;
                    self.vars
                        .resize_with(y + 1, || matrix.terms.push(Trm::var(x)));
                }
                self.vars[y]
            }
            Term::Fun(f, ts) => {
                let record = self.args.len();
                for t in ts {
                    let t = self.term(t);
                    self.args.push(t);
                }

                let id = self.matrix.terms.len();
                self.matrix.terms.push(Trm::sym(f));
                let mut digest = Digest::default();
                digest.update(f.index);
                for arg in self.args.drain(record..) {
                    self.matrix.terms.push(Trm::arg(arg));
                    digest.update(arg.index);
                }
                if let Some(shared) = self.terms.get(&digest) {
                    self.matrix.terms.truncate(id);
                    *shared
                } else {
                    self.terms.insert(digest, id);
                    id
                }
            }
        }
    }

    fn literal(&mut self, cls: Id<Cls>, literal: CNFLiteral) -> Id<Lit> {
        let pol = literal.pol;
        let atom = self.term(literal.atom);
        let symbol = self.matrix.terms[atom].as_sym();
        if symbol == EQUALITY {
            self.has_equality = true;
        }
        let id = self.matrix.lits.push(Lit { pol, atom });
        self.matrix.index[symbol].pol[pol as usize].push(Pos { cls, lit: id });
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
        self.clause(
            CNFFormula(vec![CNFLiteral {
                pol: true,
                atom: Term::Fun(
                    EQUALITY,
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
                        EQUALITY,
                        vec![Term::Var(Var(1)), Term::Var(Var(2))],
                    ),
                },
                CNFLiteral {
                    pol: true,
                    atom: Term::Fun(
                        EQUALITY,
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
                        EQUALITY,
                        vec![Term::Var(Var(1)), Term::Var(Var(2))],
                    ),
                },
                CNFLiteral {
                    pol: false,
                    atom: Term::Fun(
                        EQUALITY,
                        vec![Term::Var(Var(2)), Term::Var(Var(3))],
                    ),
                },
                CNFLiteral {
                    pol: true,
                    atom: Term::Fun(
                        EQUALITY,
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
                let v1 = Var(2 * i + 1);
                let v2 = Var(2 * i + 2);
                lits.push(CNFLiteral {
                    pol: false,
                    atom: Term::Fun(
                        EQUALITY,
                        vec![Term::Var(v1), Term::Var(v2)],
                    ),
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
                        atom: Term::Fun(EQUALITY, vec![t1, t2]),
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
