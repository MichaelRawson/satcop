use crate::block::{Block, Id, Range};
use crate::digest::{Digest, DigestMap};
use crate::matrix::*;
use crate::syntax::*;
use std::rc::Rc;

pub(crate) struct Builder {
    matrix: Matrix,
    vars: Block<Id<Trm>>,
    args: Vec<Id<Trm>>,
    terms: DigestMap<Id<Trm>>,
    has_equality: bool,
}

impl Default for Builder {
    fn default() -> Self {
        let matrix = Matrix::default();
        let vars = Block::default();
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
            arity: 0,
            sort: Sort::Bool,
            name: Name::Equality,
        });
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
        let id = self.matrix.syms.push(sym);
        self.matrix.index.block.push(Entry {
            pol: [vec![], vec![]],
        });
        id
    }

    fn term(&mut self, term: &Rc<Term>) -> Id<Trm> {
        match &**term {
            Term::Var(Var(y)) => self.vars[Id::new(*y)],
            Term::Fun(f, ts) => {
                let record = self.args.len();
                for t in ts {
                    let t = self.term(t);
                    self.args.push(t);
                }
                let mut digest = Digest::default();
                digest.update(f.index);
                for arg in &self.args[record..] {
                    digest.update(arg.index);
                }
                if let Some(shared) = self.terms.get(&digest) {
                    self.args.truncate(record);
                    return *shared;
                }
                let id = self.matrix.terms.push(Trm::sym(*f));
                for arg in self.args.drain(record..) {
                    self.matrix.terms.push(Trm::arg(arg));
                }
                self.terms.insert(digest, id);
                id
            }
        }
    }

    fn literal(&mut self, cls: Id<Cls>, literal: CNFLiteral) -> Id<Lit> {
        let pol = literal.pol;
        let atom = self.term(&literal.atom);
        let symbol = self.matrix.terms[atom].as_sym();
        if symbol == EQUALITY {
            self.has_equality = true;
            if pol {
                let left = self.matrix.terms[Id::new(atom.index + 1)].as_arg();
                let right =
                    self.matrix.terms[Id::new(atom.index + 2)].as_arg();
                self.matrix.diseqs.push(DisEq { left, right });
            }
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
        constraints: bool,
    ) {
        let id = self.matrix.clauses.len();
        if clause.0.is_empty() || info.is_goal {
            self.matrix.start.push(id);
        }
        while vars > self.vars.len().index {
            let var = Var(self.vars.len().index);
            self.vars.push(self.matrix.terms.push(Trm::var(var)));
        }
        let lstart = self.matrix.lits.len();
        let dstart = self.matrix.diseqs.len();
        for literal in clause.0 {
            self.literal(id, literal);
        }
        let lstop = self.matrix.lits.len();
        let lits = Range::new(lstart, lstop);
        for id1 in lits {
            let lit1 = self.matrix.lits[id1];
            for id2 in Range::new(Id::new(id1.index + 1), lstop) {
                let lit2 = self.matrix.lits[id2];
                if lit1.pol != lit2.pol {
                    let left = lit1.atom;
                    let right = lit2.atom;
                    let sym1 = self.matrix.terms[left];
                    let sym2 = self.matrix.terms[right];
                    if sym1 == sym2 {
                        self.matrix.diseqs.push(DisEq { left, right });
                    }
                }
            }
        }
        if !constraints {
            self.matrix.diseqs.truncate(dstart);
        }
        let dstop = self.matrix.diseqs.len();
        let diseqs = Range::new(dstart, dstop);
        self.matrix.clauses.push(Cls { vars, lits, diseqs });
        self.matrix.info.block.push(info);
    }

    fn add_equality_axioms(&mut self) {
        let v0 = Rc::new(Term::Var(Var(0)));
        let v1 = Rc::new(Term::Var(Var(1)));
        let v2 = Rc::new(Term::Var(Var(2)));
        self.clause(
            CNFFormula(vec![CNFLiteral {
                pol: true,
                atom: Rc::new(Term::Fun(
                    EQUALITY,
                    vec![v0.clone(), v0.clone()],
                )),
            }]),
            1,
            Info {
                source: Source::EqualityAxiom,
                name: "reflexivity".into(),
                is_goal: false,
            },
            false,
        );
        self.clause(
            CNFFormula(vec![
                CNFLiteral {
                    pol: false,
                    atom: Rc::new(Term::Fun(
                        EQUALITY,
                        vec![v0.clone(), v1.clone()],
                    )),
                },
                CNFLiteral {
                    pol: true,
                    atom: Rc::new(Term::Fun(
                        EQUALITY,
                        vec![v1.clone(), v0.clone()],
                    )),
                },
            ]),
            2,
            Info {
                source: Source::EqualityAxiom,
                name: "symmetry".into(),
                is_goal: false,
            },
            true,
        );
        self.clause(
            CNFFormula(vec![
                CNFLiteral {
                    pol: false,
                    atom: Rc::new(Term::Fun(
                        EQUALITY,
                        vec![v0.clone(), v1.clone()],
                    )),
                },
                CNFLiteral {
                    pol: false,
                    atom: Rc::new(Term::Fun(EQUALITY, vec![v1, v2.clone()])),
                },
                CNFLiteral {
                    pol: true,
                    atom: Rc::new(Term::Fun(EQUALITY, vec![v0, v2])),
                },
            ]),
            3,
            Info {
                source: Source::EqualityAxiom,
                name: "transitivity".into(),
                is_goal: false,
            },
            true,
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
                let v1 = Rc::new(Term::Var(Var(2 * i)));
                let v2 = Rc::new(Term::Var(Var(2 * i + 1)));
                lits.push(CNFLiteral {
                    pol: false,
                    atom: Rc::new(Term::Fun(
                        EQUALITY,
                        vec![v1.clone(), v2.clone()],
                    )),
                });
                args1.push(v1.clone());
                args2.push(v2.clone());
            }
            let t1 = Rc::new(Term::Fun(id, args1));
            let t2 = Rc::new(Term::Fun(id, args2));
            match sort {
                Sort::Obj => {
                    lits.push(CNFLiteral {
                        pol: true,
                        atom: Rc::new(Term::Fun(EQUALITY, vec![t1, t2])),
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
                true,
            );
        }
    }
}
