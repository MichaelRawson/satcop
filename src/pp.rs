use crate::block::Id;
use crate::builder::Builder;
use crate::matrix::Matrix;
use crate::syntax::*;
use std::fmt;

enum SkNNF {
    Lit(CNFLiteral),
    And(Vec<SkNNF>),
    Or(Vec<SkNNF>),
}

impl fmt::Debug for SkNNF {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Lit(lit) => write!(f, "{:?}", lit),
            Self::And(fs) => write!(f, "and{:?}", fs),
            Self::Or(fs) => write!(f, "or{:?}", fs),
        }
    }
}

impl SkNNF {
    fn vars(&self, vars: &mut Vec<bool>) {
        match self {
            Self::Lit(lit) => {
                lit.vars(vars);
            }
            Self::And(fs) | Self::Or(fs) => {
                for f in fs {
                    f.vars(vars);
                }
            }
        }
    }
}

#[derive(Default)]
pub(crate) struct PreProcessor {
    builder: Builder,
    bound: Vec<Var>,
    subst: Vec<Option<Term>>,
    vars: Vec<bool>,
    rename: Vec<u32>,
    fresh_skolem: u32,
    fresh_definition: u32,
    fresh_rename: u32,
}

impl PreProcessor {
    pub(crate) fn sym(&mut self, sym: Sym) -> Id<Sym> {
        self.builder.sym(sym)
    }

    pub(crate) fn finish(self) -> Matrix {
        self.builder.finish()
    }

    fn sknnf_term(&mut self, term: &Term) -> Term {
        match term {
            Term::Var(x) => {
                self.subst[x.0 as usize].clone().unwrap_or(Term::Var(*x))
            }
            Term::Fun(f, ts) => {
                Term::Fun(*f, ts.iter().map(|t| self.sknnf_term(t)).collect())
            }
        }
    }

    fn sknnf_atom(&mut self, pol: bool, atom: &Atom) -> SkNNF {
        match atom {
            Atom::Bool(p) => {
                if *p == pol {
                    SkNNF::And(vec![])
                } else {
                    SkNNF::Or(vec![])
                }
            }
            Atom::Pred(p) => SkNNF::Lit(CNFLiteral {
                pol,
                atom: self.sknnf_term(p),
            }),
        }
    }

    fn sknnf_formula(&mut self, pol: bool, formula: &Formula) -> SkNNF {
        match (pol, formula) {
            (_, Formula::Atom(atom)) => self.sknnf_atom(pol, atom),
            (_, Formula::Not(f)) => self.sknnf_formula(!pol, &*f),
            (true, Formula::And(fs)) | (false, Formula::Or(fs)) => SkNNF::And(
                fs.iter().map(|f| self.sknnf_formula(pol, f)).collect(),
            ),
            (true, Formula::Or(fs)) | (false, Formula::And(fs)) => SkNNF::Or(
                fs.iter().map(|f| self.sknnf_formula(pol, f)).collect(),
            ),
            (_, Formula::Eqv(l, r)) => {
                let p = self.sknnf_formula(pol, &*l);
                let notp = self.sknnf_formula(!pol, &*l);
                let q = self.sknnf_formula(true, &*r);
                let notq = self.sknnf_formula(false, &*r);
                SkNNF::And(vec![
                    SkNNF::Or(vec![notp, q]),
                    SkNNF::Or(vec![notq, p]),
                ])
            }
            (true, Formula::Ex(x, f)) | (false, Formula::All(x, f)) => {
                let arity = self.bound.len() as u32;
                let sort = Sort::Obj;
                let name = Name::Skolem(self.fresh_skolem);
                self.fresh_skolem += 1;
                let sym = self.sym(Sym { arity, sort, name });
                let skolem = Term::Fun(
                    sym,
                    self.bound.iter().copied().map(Term::Var).collect(),
                );
                self.subst[x.0 as usize] = Some(skolem);
                self.sknnf_formula(pol, &*f)
            }
            (true, Formula::All(x, f)) | (false, Formula::Ex(x, f)) => {
                self.bound.push(*x);
                let f = self.sknnf_formula(pol, &*f);
                self.bound.pop();
                f
            }
        }
    }

    fn cnf(&mut self, formula: SkNNF, info: Info) {
        match formula {
            SkNNF::Lit(lit) => {
                self.finalise_clause(CNFFormula(vec![lit]), info)
            }
            SkNNF::And(fs) => {
                for f in fs {
                    self.cnf(f, info.clone());
                }
            }
            SkNNF::Or(mut fs) => {
                let mut literals = vec![];
                while let Some(f) = fs.pop() {
                    match f {
                        SkNNF::Lit(lit) => {
                            literals.push(lit);
                        }
                        SkNNF::And(gs) if gs.is_empty() => {
                            return;
                        }
                        SkNNF::And(gs) if gs.len() == 1 => {
                            fs.extend(gs.into_iter());
                        }
                        SkNNF::And(gs) => {
                            self.vars.resize(self.subst.len(), false);
                            for g in &gs {
                                g.vars(&mut self.vars);
                            }
                            let vars = self
                                .vars
                                .drain(..)
                                .enumerate()
                                .filter(|(_, present)| *present)
                                .map(|(i, _)| Term::Var(Var(i as u32)))
                                .collect::<Vec<_>>();
                            let arity = vars.len() as u32;
                            let sort = Sort::Bool;
                            let name = Name::Definition(self.fresh_definition);
                            self.fresh_definition += 1;
                            let sym = self.sym(Sym { arity, sort, name });
                            let definition = Term::Fun(sym, vars);
                            for g in gs {
                                self.cnf(
                                    SkNNF::Or(vec![
                                        SkNNF::Lit(CNFLiteral {
                                            pol: false,
                                            atom: definition.clone(),
                                        }),
                                        g,
                                    ]),
                                    info.clone(),
                                )
                            }
                            fs.push(SkNNF::Lit(CNFLiteral {
                                pol: true,
                                atom: definition,
                            }));
                        }
                        SkNNF::Or(gs) => {
                            fs.extend(gs);
                        }
                    }
                }
                self.finalise_clause(CNFFormula(literals), info);
            }
        }
    }

    fn rename_term(&mut self, term: &mut Term) {
        match term {
            Term::Var(x) => {
                let index = x.0 as usize;
                let renamed = self.rename[index];
                if renamed == 0 {
                    self.fresh_rename += 1;
                    self.rename[index] = self.fresh_rename;
                    *x = Var(self.fresh_rename);
                } else {
                    *x = Var(renamed);
                }
            }
            Term::Fun(_, ref mut ts) => {
                for t in ts {
                    self.rename_term(t);
                }
            }
        }
    }

    fn rename(&mut self, clause: &mut CNFFormula) {
        self.fresh_rename = 0;
        self.rename.clear();
        self.rename.resize(self.subst.len(), 0);
        for literal in &mut clause.0 {
            self.rename_term(&mut literal.atom);
        }
    }

    fn finalise_clause(&mut self, mut clause: CNFFormula, info: Info) {
        self.rename(&mut clause);
        self.builder.clause(clause, self.fresh_rename, info);
    }

    pub(crate) fn process(
        &mut self,
        formula: Formula,
        info: Info,
        max_var: u32,
    ) {
        self.subst.clear();
        self.subst.resize(max_var as usize, None);
        let sknnf = self.sknnf_formula(true, &formula);
        self.cnf(sknnf, info);
    }
}
