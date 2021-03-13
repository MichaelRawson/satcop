use crate::block::Id;
use crate::builder::Builder;
use crate::cee;
use crate::options::Options;
use crate::syntax::*;
use std::rc::Rc;

#[derive(Debug)]
struct Definition {
    clauses: Vec<CNF>,
    atom: Rc<Term>,
}

#[derive(Default)]
pub(crate) struct PP {
    builder: Builder,
    bound: Vec<Rc<FOFTerm>>,
    subst: Vec<Option<Rc<FOFTerm>>>,
    fresh_skolem: u32,
    rename: Vec<u32>,
    fresh_rename: u32,
    fresh_definition: u32,
}

impl PP {
    pub(crate) fn new_symbol(&mut self, sym: Symbol) -> Id<Symbol> {
        self.builder.new_symbol(sym)
    }

    pub(crate) fn process(
        &mut self,
        opts: &Options,
        mut formula: FOF,
        info: Info,
        max_var: u32,
    ) {
        self.subst.clear();
        self.subst.resize(max_var as usize, None);
        self.name(opts, Some(true), &mut formula, false, &info);
        self.after_naming(opts, formula, &info);
    }

    pub(crate) fn finish(self, opts: &Options) -> Matrix {
        self.builder.finish(opts)
    }

    fn after_naming(&mut self, opts: &Options, formula: FOF, info: &Info) {
        let nnf = self.nnf(true, &formula);
        for mut clause in self.cnf(nnf, &info) {
            if opts.cee {
                self.cee(clause, info);
            } else {
                self.rename_clause(self.subst.len() as u32, &mut clause);
                self.builder.clause(
                    clause,
                    vec![],
                    self.fresh_rename,
                    info.clone(),
                    true,
                );
            }
        }
    }

    fn cee(&mut self, mut clause: CNF, info: &Info) {
        let mut fresh = self.subst.len() as u32;
        cee::monotonicity(&mut fresh, &mut clause);
        cee::reflexivity(&mut clause);
        for mut clause in cee::symmetry(&clause) {
            let mut fresh2 = fresh;
            let orderings = cee::transitivity(&mut fresh2, &mut clause);
            self.rename_clause(fresh2, &mut clause);
            let orderings = orderings
                .into_iter()
                .map(|(left, right)| {
                    (self.rename_term(&left), self.rename_term(&right))
                })
                .collect();
            self.builder.clause(
                clause,
                orderings,
                self.fresh_rename,
                info.clone(),
                true,
            );
        }
    }

    fn name(
        &mut self,
        opts: &Options,
        pol: Option<bool>,
        formula: &mut FOF,
        name: bool,
        info: &Info,
    ) -> (u32, u32) {
        let cap = |n| std::cmp::min(opts.naming + 1, n);
        let (p, np) = match formula {
            FOF::Atom(FOFAtom::Bool(false)) => (1, 0),
            FOF::Atom(FOFAtom::Bool(true)) => (0, 1),
            FOF::Atom(FOFAtom::Pred(_)) => (1, 1),
            FOF::Not(f) => {
                let (p, np) =
                    self.name(opts, pol.map(|pol| !pol), f, name, info);
                (np, p)
            }
            FOF::Or(fs) => {
                let mut p_all = 1;
                let mut np_all = 0;
                for f in fs {
                    let (p, np) = self.name(opts, pol, f, true, info);
                    p_all = cap(p_all * p);
                    np_all = cap(np_all + np);
                }
                (p_all, np_all)
            }
            FOF::And(fs) => {
                let mut p_all = 0;
                let mut np_all = 1;
                for f in fs {
                    let (p, np) = self.name(opts, pol, f, false, info);
                    p_all = cap(p_all + p);
                    np_all = cap(np_all * np);
                }
                (p_all, np_all)
            }
            FOF::Eqv(l, r) => {
                let (l, nl) = self.name(opts, None, l, true, info);
                let (r, nr) = self.name(opts, None, r, true, info);

                (nl * r + nr * l, l * r + nr * nl)
            }
            FOF::All(_, f) | FOF::Ex(_, f) => {
                self.name(opts, pol, f, name, info)
            }
        };
        let num = match pol {
            Some(true) => p,
            Some(false) => np,
            None => p + np,
        };
        if name && num > opts.naming {
            let (vars, definition) = self.definition(formula);
            let formula =
                std::mem::replace(formula, FOF::Atom(definition.clone()));
            self.define(opts, pol, vars, definition, formula, info);
            (1, 1)
        } else {
            (p, np)
        }
    }

    fn definition(&mut self, formula: &FOF) -> (Vec<Var>, FOFAtom) {
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
            .map(|x| Rc::new(FOFTerm::Var(x)))
            .collect::<Vec<_>>();
        let sort = Sort::Bool;
        let name = Name::Definition(self.fresh_definition);
        self.fresh_definition += 1;
        let sym = self.new_symbol(Symbol { arity, sort, name });
        (vars, FOFAtom::Pred(Rc::new(FOFTerm::Fun(sym, args))))
    }

    fn define(
        &mut self,
        opts: &Options,
        pol: Option<bool>,
        mut vars: Vec<Var>,
        definition: FOFAtom,
        formula: FOF,
        info: &Info,
    ) {
        let definition = FOF::Atom(definition);
        let mut formula = match pol {
            Some(true) => FOF::Or(vec![definition.negated(), formula]),
            Some(false) => FOF::Or(vec![formula.negated(), definition]),
            None => FOF::Eqv(Box::new(definition), Box::new(formula)),
        };
        while let Some(x) = vars.pop() {
            formula = FOF::All(x, Box::new(formula));
        }
        let mut info = info.clone();
        info.is_goal = false;
        self.after_naming(opts, formula, &info);
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
            (pol, FOF::Atom(FOFAtom::Pred(pred))) => {
                NNF::Lit(pol, pred.clone())
            }
            (pol, FOF::Not(f)) => self.nnf(!pol, &**f),
            (true, FOF::And(fs)) | (false, FOF::Or(fs)) => {
                NNF::And(fs.iter().map(|f| self.nnf(pol, f)).collect())
            }
            (true, FOF::Or(fs)) | (false, FOF::And(fs)) => {
                NNF::Or(fs.iter().map(|f| self.nnf(pol, f)).collect())
            }
            (pol, FOF::Eqv(l, r)) => NNF::And(vec![
                NNF::Or(vec![self.nnf(!pol, l), self.nnf(true, r)]),
                NNF::Or(vec![self.nnf(false, r), self.nnf(pol, l)]),
            ]),
            (true, FOF::All(x, f)) | (false, FOF::Ex(x, f)) => {
                NNF::All(*x, Box::new(self.nnf(pol, f)))
            }
            (true, FOF::Ex(x, f)) | (false, FOF::All(x, f)) => {
                NNF::Ex(*x, Box::new(self.nnf(pol, f)))
            }
        }
    }

    fn cnf(&mut self, formula: NNF, info: &Info) -> Vec<CNF> {
        let clauses = match formula {
            NNF::Lit(pol, pred) => {
                vec![CNF(vec![NNFLiteral {
                    pol,
                    atom: self.substitute(&pred),
                }])]
            }
            NNF::And(fs) => {
                fs.into_iter().flat_map(|f| self.cnf(f, info)).collect()
            }
            NNF::Or(fs) => {
                let mut result = vec![CNF(vec![])];
                for f in fs {
                    let cnf = self.cnf(f, info);
                    result = Self::distribute(result, cnf);
                }
                result
            }
            NNF::All(x, f) => {
                let bound = Rc::new(FOFTerm::Var(x));
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
                let sym = self.new_symbol(Symbol { arity, sort, name });
                let skolem = Rc::new(FOFTerm::Fun(sym, self.bound.clone()));
                self.subst[x.0 as usize] = Some(skolem);
                self.cnf(*f, info)
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

    fn rename_clause(&mut self, num_vars: u32, clause: &mut CNF) {
        self.fresh_rename = 0;
        self.rename.clear();
        self.rename.resize(num_vars as usize, u32::MAX);
        for literal in &mut clause.0 {
            literal.atom = self.rename_term(&literal.atom);
        }
    }

    fn rename_term(&mut self, term: &Rc<FOFTerm>) -> Rc<FOFTerm> {
        Rc::new(match &**term {
            FOFTerm::Var(x) => {
                let index = x.0 as usize;
                let mut renamed = self.rename[index];
                if renamed == u32::MAX {
                    renamed = self.fresh_rename;
                    self.rename[index] = renamed;
                    self.fresh_rename += 1;
                }
                FOFTerm::Var(Var(renamed))
            }
            FOFTerm::Fun(f, ts) => FOFTerm::Fun(
                *f,
                ts.iter().map(|t| self.rename_term(t)).collect(),
            ),
        })
    }

    fn substitute(&mut self, term: &Rc<FOFTerm>) -> Rc<FOFTerm> {
        match &**term {
            FOFTerm::Var(x) => self.subst[x.0 as usize]
                .clone()
                .unwrap_or_else(|| term.clone()),
            FOFTerm::Fun(f, ts) => Rc::new(FOFTerm::Fun(
                *f,
                ts.iter().map(|t| self.substitute(t)).collect(),
            )),
        }
    }
}
