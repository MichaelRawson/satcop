use crate::block::Id;
use crate::matrix::*;
use crate::options::Options;
use crate::pp::PreProcessor;
use crate::syntax;
use anyhow::Context;
use fnv::{FnvHashMap, FnvHashSet};
use memmap::Mmap;
use std::borrow::Cow;
use std::rc::Rc;
use std::{env, fs, path};
use thiserror::Error;
use tptp::cnf::*;
use tptp::common::*;
use tptp::fof::*;
use tptp::top::*;
use tptp::{cnf, common, fof, TPTPIterator};

#[error("{}: syntax error", self.0)]
#[derive(Debug, Error)]
pub(crate) struct SyntaxError(String);

#[error("unsupported item: {}", self.0)]
#[derive(Debug, Error)]
pub(crate) struct Unsupported(String);

fn open_path_no_parent(path: &path::Path) -> anyhow::Result<fs::File> {
    let directory = env::var("TPTP_DIR")
        .map(path::PathBuf::from)
        .or_else(|_| env::current_dir())?;
    let path = directory.join(path);
    fs::File::open(&path)
        .map_err(anyhow::Error::from)
        .with_context(|| format!("opening '{}'...", path.display()))
}

fn open_path_with_parent(
    parent: &path::Path,
    path: &path::Path,
) -> anyhow::Result<fs::File> {
    fs::File::open(parent.join(path)).map_err(anyhow::Error::from)
}

fn open_path(
    parent: Option<&path::Path>,
    path: &path::Path,
) -> anyhow::Result<fs::File> {
    if let Some(parent) = parent {
        open_path_with_parent(parent, path)
            .or_else(|_| open_path_no_parent(path))
            .with_context(|| {
                format!(
                    "failed relative include '{}'",
                    parent.join(path).display()
                )
            })
    } else {
        open_path_no_parent(path)
    }
}

fn read_path(
    parent: Option<&path::Path>,
    path: &path::Path,
) -> anyhow::Result<Option<Mmap>> {
    let file = open_path(parent, path)?;
    let metadata = file.metadata()?;
    let map = if metadata.len() > 0 {
        Some(unsafe { Mmap::map(&file) }.context("memory-mapping file")?)
    } else {
        None
    };
    Ok(map)
}

#[derive(PartialEq, Eq, Hash)]
struct SymEntry<'a> {
    arity: u32,
    sort: syntax::Sort,
    name: Cow<'a, str>,
}

#[derive(Default)]
struct Loader {
    pp: PreProcessor,
    fresh: u32,
    free: Vec<(String, syntax::Var)>,
    bound: Vec<(String, syntax::Var)>,
    lower: FnvHashMap<SymEntry<'static>, Id<syntax::Sym>>,
    quoted: FnvHashMap<SymEntry<'static>, Id<syntax::Sym>>,
    number: FnvHashMap<String, Id<syntax::Sym>>,
    distinct: FnvHashMap<String, Id<syntax::Sym>>,
}

impl Loader {
    pub(crate) fn finish(self) -> Matrix {
        self.pp.finish()
    }

    fn defined_term(
        &mut self,
        term: common::DefinedTerm,
        sort: syntax::Sort,
    ) -> anyhow::Result<syntax::Term> {
        let (lookup, borrowed) = match term {
            common::DefinedTerm::Number(ref number) => {
                let borrowed = match number {
                    Number::Integer(n) => n.0,
                    Number::Rational(r) => r.0,
                    Number::Real(r) => r.0,
                };
                (&mut self.number, borrowed)
            }
            common::DefinedTerm::Distinct(ref distinct) => {
                (&mut self.distinct, distinct.0)
            }
        };
        let sym = if let Some(sym) = lookup.get(borrowed) {
            *sym
        } else {
            let string = borrowed.to_string();
            let name = match term {
                common::DefinedTerm::Number(_) => {
                    syntax::Name::Number(string.clone())
                }
                common::DefinedTerm::Distinct(_) => {
                    syntax::Name::Distinct(string.clone())
                }
            };
            let arity = 0;
            let sym = self.pp.sym(syntax::Sym { arity, sort, name });
            lookup.insert(string, sym);
            sym
        };
        Ok(syntax::Term::Fun(sym, vec![]))
    }

    fn fof_plain_term(
        &mut self,
        term: PlainTerm,
        sort: syntax::Sort,
    ) -> anyhow::Result<syntax::Term> {
        let (sym, args) = match term {
            PlainTerm::Constant(c) => (c.0 .0, vec![]),
            PlainTerm::Function(f, args) => (f.0, args.0),
        };
        let arity = args.len() as u32;
        let (lookup, borrowed) = match sym {
            AtomicWord::Lower(ref w) => (&mut self.lower, w.0),
            AtomicWord::SingleQuoted(ref q) => (&mut self.quoted, q.0),
        };
        let name = Cow::Borrowed(borrowed);
        let entry = SymEntry { arity, sort, name };
        let sym = if let Some(sym) = lookup.get(&entry) {
            *sym
        } else {
            let string = borrowed.to_string();
            let name = Cow::Owned(string.clone());
            let entry = SymEntry { arity, sort, name };
            let name = match sym {
                AtomicWord::Lower(_) => syntax::Name::Atom(string),
                AtomicWord::SingleQuoted(_) => syntax::Name::Quoted(string),
            };
            let sym = self.pp.sym(syntax::Sym { arity, sort, name });
            lookup.insert(entry, sym);
            sym
        };
        let args = args
            .into_iter()
            .map(|t| self.fof_term(t, syntax::Sort::Obj))
            .collect::<anyhow::Result<_>>()?;
        Ok(syntax::Term::Fun(sym, args))
    }

    fn fof_defined_term(
        &mut self,
        term: fof::DefinedTerm,
        sort: syntax::Sort,
    ) -> anyhow::Result<syntax::Term> {
        match term {
            fof::DefinedTerm::Defined(defined) => {
                self.defined_term(defined, sort)
            }
            fof::DefinedTerm::Atomic(atomic) => {
                Err(Unsupported(atomic.to_string()).into())
            }
        }
    }

    fn fof_function_term(
        &mut self,
        term: FunctionTerm,
        sort: syntax::Sort,
    ) -> anyhow::Result<syntax::Term> {
        match term {
            FunctionTerm::Plain(term) => self.fof_plain_term(term, sort),
            FunctionTerm::Defined(def) => self.fof_defined_term(def, sort),
            FunctionTerm::System(system) => {
                Err(Unsupported(system.to_string()).into())
            }
        }
    }

    fn fof_term(
        &mut self,
        term: Term,
        sort: syntax::Sort,
    ) -> anyhow::Result<syntax::Term> {
        Ok(match term {
            Term::Function(term) => self.fof_function_term(*term, sort)?,
            Term::Variable(x) => {
                let name = x.0 .0;
                let var = if let Some((_, var)) =
                    self.bound.iter().rev().find(|(bound, _)| bound == name)
                {
                    *var
                } else if let Some((_, var)) =
                    self.free.iter().find(|(free, _)| free == name)
                {
                    *var
                } else {
                    let var = syntax::Var(self.fresh);
                    self.fresh += 1;
                    self.free.push((name.to_string(), var));
                    var
                };
                syntax::Term::Var(var)
            }
        })
    }

    fn fof_defined_plain_formula(
        &mut self,
        atom: DefinedPlainFormula,
    ) -> anyhow::Result<syntax::Atom> {
        match atom.0 {
            DefinedPlainTerm::Constant(c) => match c.0 .0 .0 .0 .0 {
                "true" => Ok(syntax::Atom::Bool(true)),
                "false" => Ok(syntax::Atom::Bool(false)),
                _ => Err(Unsupported(c.to_string()).into()),
            },
            f @ DefinedPlainTerm::Function(_, _) => {
                Err(Unsupported(f.to_string()).into())
            }
        }
    }

    fn fof_defined_atomic_formula(
        &mut self,
        atom: DefinedAtomicFormula,
    ) -> anyhow::Result<syntax::Atom> {
        Ok(match atom {
            DefinedAtomicFormula::Plain(plain) => {
                self.fof_defined_plain_formula(plain)?
            }
            DefinedAtomicFormula::Infix(infix) => {
                syntax::Atom::Pred(syntax::Term::Fun(
                    EQUALITY,
                    vec![
                        self.fof_term(*infix.left, syntax::Sort::Obj)?,
                        self.fof_term(*infix.right, syntax::Sort::Obj)?,
                    ],
                ))
            }
        })
    }

    fn fof_atomic_formula(
        &mut self,
        atom: AtomicFormula,
    ) -> anyhow::Result<syntax::Atom> {
        match atom {
            AtomicFormula::Plain(plain) => Ok(syntax::Atom::Pred(
                self.fof_plain_term(plain.0, syntax::Sort::Bool)?,
            )),
            AtomicFormula::Defined(defined) => {
                Ok(self.fof_defined_atomic_formula(defined)?)
            }
            AtomicFormula::System(system) => {
                Err(Unsupported(system.to_string()).into())
            }
        }
    }

    fn fof_infix_unary(
        &mut self,
        infix: InfixUnary,
    ) -> anyhow::Result<syntax::Formula> {
        Ok(syntax::Formula::Atom(syntax::Atom::Pred(syntax::Term::Fun(
            EQUALITY,
            vec![
                self.fof_term(*infix.left, syntax::Sort::Obj)?,
                self.fof_term(*infix.right, syntax::Sort::Obj)?,
            ],
        )))
        .negated())
    }

    fn fof_unit_formula(
        &mut self,
        fof: UnitFormula,
    ) -> anyhow::Result<syntax::Formula> {
        match fof {
            UnitFormula::Unitary(f) => self.fof_unitary_formula(f),
            UnitFormula::Unary(f) => self.fof_unary_formula(f),
        }
    }

    fn fof_binary_assoc(
        &mut self,
        fof: BinaryAssoc,
    ) -> anyhow::Result<syntax::Formula> {
        Ok(match fof {
            BinaryAssoc::And(fs) => syntax::Formula::And(
                fs.0.into_iter()
                    .map(|f| self.fof_unit_formula(f))
                    .collect::<anyhow::Result<_>>()?,
            ),
            BinaryAssoc::Or(fs) => syntax::Formula::Or(
                fs.0.into_iter()
                    .map(|f| self.fof_unit_formula(f))
                    .collect::<anyhow::Result<_>>()?,
            ),
        })
    }

    fn fof_binary_nonassoc(
        &mut self,
        fof: BinaryNonassoc,
    ) -> anyhow::Result<syntax::Formula> {
        let left = self.fof_unit_formula(*fof.left)?;
        let right = self.fof_unit_formula(*fof.right)?;
        use NonassocConnective as NC;
        Ok(match fof.op {
            NC::LRImplies => syntax::Formula::Or(vec![left.negated(), right]),
            NC::RLImplies => syntax::Formula::Or(vec![left, right.negated()]),
            NC::Equivalent => {
                syntax::Formula::Eqv(Box::new(left), Box::new(right))
            }
            NC::NotEquivalent => {
                syntax::Formula::Eqv(Box::new(left), Box::new(right)).negated()
            }
            NC::NotAnd => syntax::Formula::And(vec![left, right]).negated(),
            NC::NotOr => syntax::Formula::Or(vec![left, right]).negated(),
        })
    }

    fn fof_binary_formula(
        &mut self,
        fof: BinaryFormula,
    ) -> anyhow::Result<syntax::Formula> {
        match fof {
            BinaryFormula::Assoc(f) => self.fof_binary_assoc(f),
            BinaryFormula::Nonassoc(f) => self.fof_binary_nonassoc(f),
        }
    }

    fn fof_quantified_formula(
        &mut self,
        fof: QuantifiedFormula,
    ) -> anyhow::Result<syntax::Formula> {
        let num_bound = fof.bound.0.len();
        for x in fof.bound.0.into_iter() {
            let string = x.0 .0.to_string();
            let var = syntax::Var(self.fresh);
            self.fresh += 1;
            self.bound.push((string, var));
        }
        let mut f = self.fof_unit_formula(*fof.formula)?;
        for _ in 0..num_bound {
            let (_, var) = self.bound.pop().expect("bound this earlier");
            let boxed = Box::new(f);
            f = match fof.quantifier {
                Quantifier::Forall => syntax::Formula::All(var, boxed),
                Quantifier::Exists => syntax::Formula::Ex(var, boxed),
            };
        }
        Ok(f)
    }

    fn fof_unitary_formula(
        &mut self,
        fof: UnitaryFormula,
    ) -> anyhow::Result<syntax::Formula> {
        Ok(match fof {
            UnitaryFormula::Quantified(f) => self.fof_quantified_formula(f)?,
            UnitaryFormula::Atomic(f) => {
                syntax::Formula::Atom(self.fof_atomic_formula(*f)?)
            }
            UnitaryFormula::Parenthesised(f) => self.fof_logic_formula(*f)?,
        })
    }

    fn fof_unary_formula(
        &mut self,
        fof: UnaryFormula,
    ) -> anyhow::Result<syntax::Formula> {
        Ok(match fof {
            UnaryFormula::Unary(_, f) => self.fof_unit_formula(*f)?.negated(),
            UnaryFormula::InfixUnary(f) => self.fof_infix_unary(f)?,
        })
    }

    fn fof_logic_formula(
        &mut self,
        fof: LogicFormula,
    ) -> anyhow::Result<syntax::Formula> {
        match fof {
            LogicFormula::Binary(f) => self.fof_binary_formula(f),
            LogicFormula::Unary(f) => self.fof_unary_formula(f),
            LogicFormula::Unitary(f) => self.fof_unitary_formula(f),
        }
    }

    fn fof_formula(
        &mut self,
        fof: fof::Formula,
    ) -> anyhow::Result<syntax::Formula> {
        self.fof_logic_formula(fof.0)
    }

    fn literal(&mut self, lit: Literal) -> anyhow::Result<syntax::Formula> {
        Ok(match lit {
            Literal::Atomic(atomic) => {
                syntax::Formula::Atom(self.fof_atomic_formula(atomic)?)
            }
            Literal::NegatedAtomic(atomic) => {
                syntax::Formula::Atom(self.fof_atomic_formula(atomic)?)
                    .negated()
            }
            Literal::Infix(infix) => self.fof_infix_unary(infix)?,
        })
    }

    fn cnf_formula(
        &mut self,
        cnf: cnf::Formula,
    ) -> anyhow::Result<syntax::Formula> {
        let disjunction = match cnf {
            cnf::Formula::Disjunction(d) => d,
            cnf::Formula::Parenthesised(d) => d,
        };
        Ok(syntax::Formula::Or(
            disjunction
                .0
                .into_iter()
                .map(|lit| self.literal(lit))
                .collect::<anyhow::Result<_>>()?,
        ))
    }

    fn annotated<D: Dialect>(
        &mut self,
        file: Rc<str>,
        selection: Option<&FnvHashSet<Name>>,
        annotated: Annotated<D>,
    ) -> anyhow::Result<()> {
        if selection
            .map(|selection| !selection.contains(&annotated.name))
            .unwrap_or_default()
        {
            return Ok(());
        }

        let role = (annotated.role.0).0;
        let negate = role == "conjecture";
        let is_goal = negate || role == "negated_conjecture";
        let name = Rc::from(annotated.name.to_string());
        let info = syntax::Info {
            source: syntax::Source::File(file),
            name,
            is_goal,
        };

        self.fresh = 0;
        self.free.clear();
        let mut formula = annotated.formula.load(self)?;
        if negate {
            formula = formula.negated();
        }
        self.pp.process(formula, info, self.fresh);
        Ok(())
    }

    fn load(
        &mut self,
        parent: Option<&path::Path>,
        selection: Option<FnvHashSet<Name>>,
        path: &path::Path,
    ) -> anyhow::Result<()> {
        let filename: Rc<str> = format!("{}", path.display()).into();
        let map = read_path(parent, path)?;
        let bytes = map.as_deref().unwrap_or_default();
        let statements = TPTPIterator::<()>::new(bytes);
        for statement in statements {
            let statement = statement
                .map_err(|_| SyntaxError(path.display().to_string()))?;
            match statement {
                TPTPInput::Annotated(annotated) => match *annotated {
                    AnnotatedFormula::Fof(fof) => {
                        self.annotated(
                            filename.clone(),
                            selection.as_ref(),
                            fof.0,
                        )?;
                    }
                    AnnotatedFormula::Cnf(cnf) => {
                        self.annotated(
                            filename.clone(),
                            selection.as_ref(),
                            cnf.0,
                        )?;
                    }
                },
                TPTPInput::Include(include) => {
                    let Include {
                        file_name,
                        selection,
                    } = *include;
                    let included = path::Path::new((file_name.0).0);
                    let selection: Option<FnvHashSet<_>> =
                        selection.0.map(|list| list.0.into_iter().collect());
                    self.load(path.parent(), selection, included)
                        .with_context(|| {
                            format!("included '{}'", included.display(),)
                        })?;
                }
            }
        }
        Ok(())
    }
}

trait Dialect {
    fn load(self, loader: &mut Loader) -> anyhow::Result<syntax::Formula>;
}

impl Dialect for fof::Formula<'_> {
    fn load(self, loader: &mut Loader) -> anyhow::Result<syntax::Formula> {
        loader.fof_formula(self)
    }
}

impl Dialect for cnf::Formula<'_> {
    fn load(self, loader: &mut Loader) -> anyhow::Result<syntax::Formula> {
        loader.cnf_formula(self)
    }
}

pub(crate) fn load(options: &Options) -> anyhow::Result<Matrix> {
    let mut loader = Loader::default();
    loader.load(None, None, &options.path).with_context(|| {
        format!("failed to load from '{}'", options.path.display())
    })?;
    Ok(loader.finish())
}
