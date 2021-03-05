use crate::block::Id;
use crate::builder::Builder;
use crate::matrix::{Matrix, EQUALITY};
use crate::syntax::*;
use std::rc::Rc;

const THRESHOLD: u32 = 32;

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

#[derive(Debug)]
enum NNF {
    Lit(bool, Rc<Term>),
    Or(Vec<NNF>),
    And(Vec<NNF>),
    All(Var, Box<NNF>),
    Ex(Var, Box<NNF>),
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
                clause.extend(c.0.iter().cloned());
                clause.extend(d.0.iter().cloned());
                result.push(CNFFormula(clause));
            }
        }
        result
    }

    fn cnf(&mut self, formula: NNF, info: &Info) -> Vec<CNFFormula> {
        let clauses = match formula {
            NNF::Lit(pol, pred) => {
                vec![CNFFormula(vec![CNFLiteral {
                    pol,
                    atom: self.term(&pred),
                }])]
            }
            NNF::And(fs) => {
                fs.into_iter().flat_map(|f| self.cnf(f, info)).collect()
            }
            NNF::Or(fs) => {
                let mut result = vec![CNFFormula(vec![])];
                for f in fs {
                    let cnf = self.cnf(f, info);
                    result = Self::distribute(result, cnf);
                }
                result
            }
            NNF::All(x, f) => {
                let bound = Rc::new(Term::Var(x));
                self.bound.push(bound);
                let result = self.cnf(*f, info);
                self.bound.pop();
                result
            }
            NNF::Ex(x, f) => {
                let arity = self.bound.len() as u32;
                let sort = Sort::Obj;
                let name = Name::Skolem(self.fresh_skolem);
                self.fresh_skolem += 1;
                let sym = self.sym(Sym { arity, sort, name });
                let skolem = Rc::new(Term::Fun(sym, self.bound.clone()));
                self.subst[x.0 as usize] = Some(skolem);
                self.cnf(*f, info)
            }
        };
        let mut result = vec![];
        'clauses: for mut clause in clauses {
            clause.0.sort();
            clause.0.dedup();
            for lit in &clause.0 {
                if let Term::Fun(sym, args) = &*lit.atom {
                    if *sym == EQUALITY {
                        if let [ref x, ref y] = args.as_slice() {
                            if x == y {
                                continue 'clauses;
                            }
                        }
                    }
                }
                let contradiction = |other: &CNFLiteral| {
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

    fn nnf(&mut self, pol: bool, formula: &Formula) -> NNF {
        match (pol, formula) {
            (pol, Formula::Atom(Atom::Bool(b))) => {
                if *b == pol {
                    NNF::And(vec![])
                } else {
                    NNF::And(vec![NNF::Or(vec![])])
                }
            }
            (pol, Formula::Atom(Atom::Pred(pred))) => {
                NNF::Lit(pol, pred.clone())
            }
            (pol, Formula::Not(f)) => self.nnf(!pol, &**f),
            (true, Formula::And(fs)) | (false, Formula::Or(fs)) => {
                NNF::And(fs.iter().map(|f| self.nnf(pol, f)).collect())
            }
            (true, Formula::Or(fs)) | (false, Formula::And(fs)) => {
                NNF::Or(fs.iter().map(|f| self.nnf(pol, f)).collect())
            }
            (pol, Formula::Eqv(l, r)) => NNF::And(vec![
                NNF::Or(vec![self.nnf(!pol, l), self.nnf(true, r)]),
                NNF::Or(vec![self.nnf(false, r), self.nnf(pol, l)]),
            ]),
            (true, Formula::All(x, f)) | (false, Formula::Ex(x, f)) => {
                NNF::All(*x, Box::new(self.nnf(pol, f)))
            }
            (true, Formula::Ex(x, f)) | (false, Formula::All(x, f)) => {
                NNF::Ex(*x, Box::new(self.nnf(pol, f)))
            }
        }
    }

    fn definition(&mut self, formula: &Formula) -> (Vec<Var>, Atom) {
        let mut vars = vec![];
        vars.resize(self.subst.len(), false);
        formula.vars(&mut vars);
        let vars = vars
            .into_iter()
            .enumerate()
            .filter(|(_, present)| *present)
            .map(|(i, _)| Var(i as u32))
            .collect::<Vec<_>>();
        let arity = vars.len() as u32;
        let args = vars
            .iter()
            .copied()
            .map(|x| Rc::new(Term::Var(x)))
            .collect::<Vec<_>>();
        let sort = Sort::Bool;
        let name = Name::Definition(self.fresh_definition);
        self.fresh_definition += 1;
        let sym = self.sym(Sym { arity, sort, name });
        (vars, Atom::Pred(Rc::new(Term::Fun(sym, args))))
    }

    fn define(
        &mut self,
        pol: Option<bool>,
        mut vars: Vec<Var>,
        definition: Atom,
        formula: Formula,
        info: &Info,
    ) {
        let definition = Formula::Atom(definition);
        let mut formula = match pol {
            Some(true) => Formula::Or(vec![definition.negated(), formula]),
            Some(false) => Formula::Or(vec![formula.negated(), definition]),
            None => Formula::Eqv(Box::new(definition), Box::new(formula)),
        };
        while let Some(x) = vars.pop() {
            formula = Formula::All(x, Box::new(formula));
        }
        let mut info = info.clone();
        info.is_goal = false;
        self.cnf_and_finalise(formula, &info);
    }

    fn name(
        &mut self,
        pol: Option<bool>,
        formula: &mut Formula,
        name: bool,
        info: &Info,
    ) -> (u32, u32) {
        use std::cmp::min;
        let (p, np) = match formula {
            Formula::Atom(_) => (1, 1),
            Formula::Not(f) => {
                let (p, np) = self.name(pol.map(|pol| !pol), f, name, info);
                (np, p)
            }
            Formula::Or(fs) => {
                let mut p_all = 1;
                let mut np_all = 0;
                for f in fs {
                    let (p, np) = self.name(pol, f, true, info);
                    p_all = min(THRESHOLD + 1, p_all * p);
                    np_all = min(THRESHOLD + 1, np_all + np);
                }
                (p_all, np_all)
            }
            Formula::And(fs) => {
                let mut p_all = 0;
                let mut np_all = 1;
                for f in fs {
                    let (p, np) = self.name(pol, f, false, info);
                    p_all = min(THRESHOLD + 1, p_all + p);
                    np_all = min(THRESHOLD + 1, np_all * np);
                }
                (p_all, np_all)
            }
            Formula::Eqv(l, r) => {
                let (l, nl) = self.name(None, l, true, info);
                let (r, nr) = self.name(None, r, true, info);

                (nl * r + nr * l, l * r + nr * nl)
            }
            Formula::All(_, f) | Formula::Ex(_, f) => {
                self.name(pol, f, name, info)
            }
        };
        let num = match pol {
            Some(true) => p,
            Some(false) => np,
            None => p + np,
        };
        if name && num > THRESHOLD {
            let (vars, definition) = self.definition(formula);
            let formula =
                std::mem::replace(formula, Formula::Atom(definition.clone()));
            self.define(pol, vars, definition, formula, info);
            (1, 1)
        } else {
            (p, np)
        }
    }

    fn rename_term(&mut self, term: &Rc<Term>) -> Rc<Term> {
        Rc::new(match &**term {
            Term::Var(x) => {
                let index = x.0 as usize;
                let mut renamed = self.rename[index];
                if renamed == u32::MAX {
                    renamed = self.fresh_rename;
                    self.rename[index] = renamed;
                    self.fresh_rename += 1;
                }
                Term::Var(Var(renamed))
            }
            Term::Fun(f, ts) => {
                Term::Fun(*f, ts.iter().map(|t| self.rename_term(t)).collect())
            }
        })
    }

    fn rename_clause(&mut self, clause: &mut CNFFormula) {
        self.fresh_rename = 0;
        self.rename.clear();
        self.rename.resize(self.subst.len(), u32::MAX);
        for literal in &mut clause.0 {
            literal.atom = self.rename_term(&literal.atom);
        }
    }

    fn finalise_clause(&mut self, mut clause: CNFFormula, info: Info) {
        self.rename_clause(&mut clause);
        self.builder.clause(clause, self.fresh_rename, info, true);
    }

    pub(crate) fn sym(&mut self, sym: Sym) -> Id<Sym> {
        self.builder.sym(sym)
    }

    pub(crate) fn finish(self) -> Matrix {
        self.builder.finish()
    }

    fn cnf_and_finalise(&mut self, formula: Formula, info: &Info) {
        let nnf = self.nnf(true, &formula);
        for clause in self.cnf(nnf, &info) {
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
        self.name(Some(true), &mut formula, false, &info);
        self.cnf_and_finalise(formula, &info);
    }
}
