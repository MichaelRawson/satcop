use crate::block::Id;
use crate::builder::Builder;
use crate::matrix::Matrix;
use crate::syntax::*;
use std::rc::Rc;

const THRESHOLD: u32 = 4;

#[derive(Debug)]
struct Definition {
    clauses: Vec<CNFFormula>,
    atom: Rc<Term>,
}

#[derive(Default)]
pub(crate) struct PP {
    builder: Builder,
    bound: Vec<Rc<Term>>,
    subst: Vec<Option<Rc<Term>>>,
    fresh_skolem: u32,
    rename: Vec<u32>,
    fresh_rename: u32,
    fresh_definition: u32,
}

impl PP {
    fn term(&mut self, term: &Rc<Term>) -> Rc<Term> {
        match &**term {
            Term::Var(x) => self.subst[x.0 as usize]
                .clone()
                .unwrap_or_else(|| term.clone()),
            Term::Fun(f, ts) => Rc::new(Term::Fun(
                *f,
                ts.iter().map(|t| self.term(t)).collect(),
            )),
        }
    }

    fn distribute(
        left: Vec<CNFFormula>,
        right: Vec<CNFFormula>,
    ) -> Vec<CNFFormula> {
        let mut result = vec![];
        for c in &left {
            for d in &right {
                let mut clause = vec![];
                clause.extend(c.0.clone());
                clause.extend(d.0.clone());
                result.push(CNFFormula(clause));
            }
        }
        result
    }

    fn cnf(
        &mut self,
        pol: bool,
        formula: &Formula,
        info: &Info,
    ) -> Vec<CNFFormula> {
        match (pol, formula) {
            (pol, Formula::Atom(Atom::Bool(b))) => {
                if *b == pol {
                    vec![]
                } else {
                    vec![CNFFormula(vec![])]
                }
            }
            (pol, Formula::Atom(Atom::Pred(pred))) => {
                vec![CNFFormula(vec![CNFLiteral {
                    pol,
                    atom: self.term(&pred),
                }])]
            }
            (pol, Formula::Not(f)) => self.cnf(!pol, &**f, info),
            (true, Formula::And(fs)) | (false, Formula::Or(fs)) => {
                fs.iter().flat_map(|f| self.cnf(pol, f, info)).collect()
            }
            (true, Formula::Or(fs)) | (false, Formula::And(fs)) => {
                let mut result = vec![];
                for f in fs {
                    let cnf = self.cnf(pol, f, info);
                    if result.is_empty() {
                        result = cnf;
                    } else {
                        result = Self::distribute(result, cnf);
                    }
                }
                result
            }
            (pol, Formula::Eqv(l, r)) => {
                let lcnf = self.cnf(pol, &**l, info);
                let nlcnf = self.cnf(!pol, &**l, info);
                let rcnf = self.cnf(true, &**r, info);
                let nrcnf = self.cnf(false, &**r, info);
                let l2r = Self::distribute(nlcnf, rcnf);
                let r2l = Self::distribute(nrcnf, lcnf);
                let mut result = l2r;
                result.extend(r2l.into_iter());
                result
            }
            (true, Formula::All(x, f)) | (false, Formula::Ex(x, f)) => {
                self.bound.push(Rc::new(Term::Var(*x)));
                let result = self.cnf(pol, &**f, info);
                self.bound.pop();
                result
            }
            (true, Formula::Ex(x, f)) | (false, Formula::All(x, f)) => {
                let arity = self.bound.len() as u32;
                let sort = Sort::Obj;
                let name = Name::Skolem(self.fresh_skolem);
                self.fresh_skolem += 1;
                let sym = self.sym(Sym { arity, sort, name });
                let skolem = Rc::new(Term::Fun(sym, self.bound.clone()));
                self.subst[x.0 as usize] = Some(skolem);
                self.cnf(pol, &**f, info)
            }
        }
    }

    fn definition(&mut self, formula: &Formula) -> Atom {
        let mut vars = vec![];
        vars.resize(self.subst.len(), false);
        formula.vars(&mut vars);
        let vars = vars
            .into_iter()
            .enumerate()
            .filter(|(_, present)| *present)
            .map(|(i, _)| Rc::new(Term::Var(Var(i as u32))))
            .collect::<Vec<_>>();
        let arity = vars.len() as u32;
        let sort = Sort::Bool;
        let name = Name::Definition(self.fresh_definition);
        self.fresh_definition += 1;
        let sym = self.sym(Sym { arity, sort, name });
        Atom::Pred(Rc::new(Term::Fun(sym, vars)))
    }

    fn define(
        &mut self,
        pol: Option<bool>,
        definition: Atom,
        formula: Formula,
        info: &Info,
    ) {
        let definition = Formula::Atom(definition);
        let formula = match pol {
            Some(true) => Formula::Or(vec![definition.negated(), formula]),
            Some(false) => Formula::Or(vec![formula.negated(), definition]),
            None => Formula::Eqv(Box::new(definition), Box::new(formula)),
        };
        let mut info = info.clone();
        info.is_goal = false;
        self.cnf_and_finalise(formula, &info);
    }

    fn name(
        &mut self,
        pol: Option<bool>,
        formula: &mut Formula,
        info: &Info,
    ) -> (u32, u32) {
        let (p, np) = match formula {
            Formula::Atom(_) => (1, 1),
            Formula::Not(f) => {
                let (p, np) = self.name(pol.map(|pol| !pol), f, info);
                (np, p)
            }
            Formula::Or(fs) => {
                let mut p_all = 1;
                let mut np_all = 0;
                for f in fs {
                    let (p, np) = self.name(pol, f, info);
                    p_all *= p;
                    np_all += np;
                }
                (p_all, np_all)
            }
            Formula::And(fs) => {
                let mut p_all = 0;
                let mut np_all = 1;
                for f in fs {
                    let (p, np) = self.name(pol, f, info);
                    p_all += p;
                    np_all *= np;
                }
                (p_all, np_all)
            }
            Formula::Eqv(l, r) => {
                let (l, nl) = self.name(None, l, info);
                let (r, nr) = self.name(None, r, info);

                (nl * r + nr * l, l * r + nr * nl)
            }
            Formula::All(_, f) | Formula::Ex(_, f) => self.name(pol, f, info),
        };
        let num_clauses = match pol {
            Some(true) => p,
            Some(false) => np,
            None => p + np,
        };
        if num_clauses > THRESHOLD {
            let definition = self.definition(formula);
            let formula =
                std::mem::replace(formula, Formula::Atom(definition.clone()));
            self.define(pol, definition, formula, info);
            (1, 1)
        } else {
            (p, np)
        }
    }

    fn rename_term(&mut self, term: &Rc<Term>) -> Rc<Term> {
        Rc::new(match &**term {
            Term::Var(x) => {
                let index = x.0 as usize;
                let renamed = self.rename[index];
                Term::Var(Var(if renamed == 0 {
                    self.fresh_rename += 1;
                    self.rename[index] = self.fresh_rename;
                    self.fresh_rename
                } else {
                    renamed
                }))
            }
            Term::Fun(f, ts) => {
                Term::Fun(*f, ts.iter().map(|t| self.rename_term(t)).collect())
            }
        })
    }

    fn rename_clause(&mut self, clause: &mut CNFFormula) {
        self.fresh_rename = 0;
        self.rename.clear();
        self.rename.resize(self.subst.len(), 0);
        for literal in &mut clause.0 {
            literal.atom = self.rename_term(&literal.atom);
        }
    }

    fn finalise_clause(&mut self, mut clause: CNFFormula, info: Info) {
        self.rename_clause(&mut clause);
        //dbg!(&clause);
        self.builder.clause(clause, self.fresh_rename, info);
    }

    pub(crate) fn sym(&mut self, sym: Sym) -> Id<Sym> {
        self.builder.sym(sym)
    }

    pub(crate) fn finish(self) -> Matrix {
        self.builder.finish()
    }

    fn cnf_and_finalise(&mut self, formula: Formula, info: &Info) {
        for clause in self.cnf(true, &formula, &info) {
            self.finalise_clause(clause, info.clone());
        }
    }

    pub(crate) fn process(
        &mut self,
        mut formula: Formula,
        info: Info,
        max_var: u32,
    ) {
        self.subst.clear();
        self.subst.resize(max_var as usize, None);
        self.name(Some(true), &mut formula, &info);
        self.cnf_and_finalise(formula, &info);
    }
}
