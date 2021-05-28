use crate::block::{BlockMap, Id};
use crate::builder::Builder;
use crate::syntax::*;
use std::rc::Rc;

#[derive(Default)]
pub(crate) struct PP {
    builder: Builder,
    bound: Vec<Rc<FOFTerm>>,
    subst: BlockMap<Var, Option<Rc<FOFTerm>>>,
    fresh_skolem: Id<Skolem>,
    rename: BlockMap<Var, Option<Id<Var>>>,
    fresh_rename: Id<Var>,
}

impl PP {
    pub(crate) fn initialise(&mut self) {
        self.builder.initialise();
    }

    pub(crate) fn new_symbol(&mut self, sym: Symbol) -> Id<Symbol> {
        self.builder.new_symbol(sym)
    }

    pub(crate) fn process(
        &mut self,
        formula: FOF,
        is_goal: bool,
        source: Source,
        max_var: Id<Var>,
    ) {
        self.subst.clear();
        self.subst.resize_with(max_var, Option::default);
        let nnf = self.nnf(true, &formula);
        self.clausify(nnf, is_goal, &source);
    }

    pub(crate) fn finish(self) -> Matrix {
        self.builder.finish()
    }

    fn clausify(&mut self, nnf: NNF, is_goal: bool, source: &Source) {
        for mut clause in self.cnf(nnf) {
            self.rename_clause(self.subst.len(), &mut clause);
            self.builder.clause(
                clause,
                self.fresh_rename,
                Info {
                    is_goal,
                    source: source.clone(),
                },
                true,
            );
        }
    }

    fn nnf(&mut self, pol: bool, formula: &FOF) -> NNF {
        match (pol, formula) {
            (pol, FOF::Atom(FOFAtom::Bool(b))) => {
                if *b == pol {
                    NNF::And(vec![])
                } else {
                    NNF::And(vec![NNF::Or(vec![])])
                }
            }
            (pol, FOF::Atom(FOFAtom::Pred(pred))) => NNF::Lit(NNFLiteral {
                pol,
                atom: pred.clone(),
            }),
            (pol, FOF::Not(f)) => self.nnf(!pol, &**f),
            (true, FOF::And(fs)) | (false, FOF::Or(fs)) => {
                NNF::And(fs.iter().map(|f| self.nnf(pol, f)).collect())
            }
            (true, FOF::Or(fs)) | (false, FOF::And(fs)) => {
                NNF::Or(fs.iter().map(|f| self.nnf(pol, f)).collect())
            }
            (pol, FOF::Eqv(l, r)) => {
                let lnnf = self.nnf(pol, l);
                let nlnnf = lnnf.negated();
                let rnnf = self.nnf(true, r);
                let nrnnf = rnnf.negated();
                NNF::And(vec![
                    NNF::Or(vec![nlnnf, rnnf]),
                    NNF::Or(vec![nrnnf, lnnf]),
                ])
            }
            (true, FOF::All(x, f)) | (false, FOF::Ex(x, f)) => {
                NNF::All(*x, Box::new(self.nnf(pol, f)))
            }
            (true, FOF::Ex(x, f)) | (false, FOF::All(x, f)) => {
                NNF::Ex(*x, Box::new(self.nnf(pol, f)))
            }
        }
    }

    fn cnf(&mut self, formula: NNF) -> Vec<CNF> {
        let clauses = match formula {
            NNF::Lit(NNFLiteral { pol, atom }) => {
                vec![CNF(vec![NNFLiteral {
                    pol,
                    atom: self.substitute(&atom),
                }])]
            }
            NNF::And(fs) => fs.into_iter().flat_map(|f| self.cnf(f)).collect(),
            NNF::Or(fs) => {
                let mut result = vec![CNF(vec![])];
                for f in fs {
                    let cnf = self.cnf(f);
                    result = Self::distribute(result, cnf);
                }
                result
            }
            NNF::All(x, f) => {
                let bound = Rc::new(FOFTerm::Var(x));
                self.bound.push(bound);
                let result = self.cnf(*f);
                self.bound.pop();
                result
            }
            NNF::Ex(x, f) => {
                let arity = self.bound.len() as u32;
                let sort = Sort::Obj;
                let name = Name::Skolem(self.fresh_skolem);
                self.fresh_skolem.increment();
                let sym = self.new_symbol(Symbol { arity, sort, name });
                let skolem = Rc::new(FOFTerm::Fun(sym, self.bound.clone()));
                self.subst[x] = Some(skolem);
                self.cnf(*f)
            }
        };
        let mut result = vec![];
        'clauses: for mut clause in clauses {
            clause.0.sort();
            clause.0.dedup();
            for lit in &clause.0 {
                if let FOFTerm::Fun(sym, args) = &*lit.atom {
                    if *sym == EQUALITY {
                        if let [ref x, ref y] = args.as_slice() {
                            if x == y {
                                continue 'clauses;
                            }
                        }
                    }
                }
                let contradiction = |other: &NNFLiteral| {
                    lit.atom == other.atom && lit.pol != other.pol
                };
                if clause.0.iter().any(contradiction) {
                    continue 'clauses;
                }
            }
            result.push(clause);
        }
        result
    }

    fn distribute(left: Vec<CNF>, right: Vec<CNF>) -> Vec<CNF> {
        let mut result = vec![];
        for c in &left {
            for d in &right {
                let mut clause = vec![];
                clause.extend(c.0.iter().cloned());
                clause.extend(d.0.iter().cloned());
                result.push(CNF(clause));
            }
        }
        result
    }

    fn rename_clause(&mut self, num_vars: Id<Var>, clause: &mut CNF) {
        self.fresh_rename = Id::new(0);
        self.rename.clear();
        self.rename.resize_with(num_vars, Option::default);
        for literal in &mut clause.0 {
            literal.atom = self.rename_term(&literal.atom);
        }
    }

    fn rename_term(&mut self, term: &Rc<FOFTerm>) -> Rc<FOFTerm> {
        Rc::new(match &**term {
            FOFTerm::Var(x) => {
                let renamed = if let Some(renamed) = self.rename[*x] {
                    renamed
                } else {
                    let renamed = self.fresh_rename;
                    self.rename[*x] = Some(renamed);
                    self.fresh_rename.increment();
                    renamed
                };
                FOFTerm::Var(renamed)
            }
            FOFTerm::Fun(f, ts) => FOFTerm::Fun(
                *f,
                ts.iter().map(|t| self.rename_term(t)).collect(),
            ),
        })
    }

    fn substitute(&mut self, term: &Rc<FOFTerm>) -> Rc<FOFTerm> {
        match &**term {
            FOFTerm::Var(x) => {
                self.subst[*x].clone().unwrap_or_else(|| term.clone())
            }
            FOFTerm::Fun(f, ts) => Rc::new(FOFTerm::Fun(
                *f,
                ts.iter().map(|t| self.substitute(t)).collect(),
            )),
        }
    }
}
