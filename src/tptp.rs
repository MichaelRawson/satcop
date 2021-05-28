use crate::block::Id;
use crate::options::Options;
use crate::pp::PP;
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

#[derive(Debug, Error)]
#[error("{}: syntax error", self.0)]
pub(crate) struct SyntaxError(String);

#[derive(Debug, Error)]
#[error("unsupported item: {}", self.0)]
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
struct SymbolEntry<'a> {
    arity: u32,
    sort: syntax::Sort,
    name: Cow<'a, str>,
}

#[derive(Default)]
struct Loader {
    pp: PP,
    fresh: Id<syntax::Var>,
    free: Vec<(String, Id<syntax::Var>)>,
    bound: Vec<(String, Id<syntax::Var>)>,
    lower: FnvHashMap<SymbolEntry<'static>, Id<syntax::Symbol>>,
    quoted: FnvHashMap<SymbolEntry<'static>, Id<syntax::Symbol>>,
    number: FnvHashMap<String, Id<syntax::Symbol>>,
    distinct: FnvHashMap<String, Id<syntax::Symbol>>,
}

impl Loader {
    pub(crate) fn initialise(&mut self) {
        self.pp.initialise();
    }

    pub(crate) fn finish(self, options: &Options) -> syntax::Matrix {
        self.pp.finish(options)
    }

    fn defined_term(
        &mut self,
        term: common::DefinedTerm,
        sort: syntax::Sort,
    ) -> Rc<syntax::FOFTerm> {
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
            let sym = self.pp.new_symbol(syntax::Symbol { arity, sort, name });
            lookup.insert(string, sym);
            sym
        };
        Rc::new(syntax::FOFTerm::Fun(sym, vec![]))
    }

    fn fof_plain_term(
        &mut self,
        term: PlainTerm,
        sort: syntax::Sort,
    ) -> anyhow::Result<Rc<syntax::FOFTerm>> {
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
        let entry = SymbolEntry { arity, sort, name };
        let sym = if let Some(sym) = lookup.get(&entry) {
            *sym
        } else {
            let string = borrowed.to_string();
            let name = Cow::Owned(string.clone());
            let entry = SymbolEntry { arity, sort, name };
            let name = match sym {
                AtomicWord::Lower(_) => syntax::Name::Atom(string),
                AtomicWord::SingleQuoted(_) => syntax::Name::Quoted(string),
            };
            let sym = self.pp.new_symbol(syntax::Symbol { arity, sort, name });
            lookup.insert(entry, sym);
            sym
        };
        let args = args
            .into_iter()
            .map(|t| self.fof_term(t, syntax::Sort::Obj))
            .collect::<anyhow::Result<_>>()?;
        Ok(Rc::new(syntax::FOFTerm::Fun(sym, args)))
    }

    fn fof_defined_term(
        &mut self,
        term: fof::DefinedTerm,
        sort: syntax::Sort,
    ) -> anyhow::Result<Rc<syntax::FOFTerm>> {
        match term {
            fof::DefinedTerm::Defined(defined) => {
                Ok(self.defined_term(defined, sort))
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
    ) -> anyhow::Result<Rc<syntax::FOFTerm>> {
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
    ) -> anyhow::Result<Rc<syntax::FOFTerm>> {
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
                    let var = self.fresh;
                    self.fresh.increment();
                    self.free.push((name.to_string(), var));
                    var
                };
                Rc::new(syntax::FOFTerm::Var(var))
            }
        })
    }

    fn fof_defined_plain_formula(
        &mut self,
        atom: DefinedPlainFormula,
    ) -> anyhow::Result<syntax::FOFAtom> {
        match atom.0 {
            DefinedPlainTerm::Constant(c) => match c.0 .0 .0 .0 .0 {
                "true" => Ok(syntax::FOFAtom::Bool(true)),
                "false" => Ok(syntax::FOFAtom::Bool(false)),
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
    ) -> anyhow::Result<syntax::FOFAtom> {
        Ok(match atom {
            DefinedAtomicFormula::Plain(plain) => {
                self.fof_defined_plain_formula(plain)?
            }
            DefinedAtomicFormula::Infix(infix) => {
                syntax::FOFAtom::Pred(Rc::new(syntax::FOFTerm::Fun(
                    syntax::EQUALITY,
                    vec![
                        self.fof_term(*infix.left, syntax::Sort::Obj)?,
                        self.fof_term(*infix.right, syntax::Sort::Obj)?,
                    ],
                )))
            }
        })
    }

    fn fof_atomic_formula(
        &mut self,
        atom: AtomicFormula,
    ) -> anyhow::Result<syntax::FOFAtom> {
        match atom {
            AtomicFormula::Plain(plain) => Ok(syntax::FOFAtom::Pred(
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
    ) -> anyhow::Result<syntax::FOF> {
        Ok(syntax::FOF::Atom(syntax::FOFAtom::Pred(Rc::new(
            syntax::FOFTerm::Fun(
                syntax::EQUALITY,
                vec![
                    self.fof_term(*infix.left, syntax::Sort::Obj)?,
                    self.fof_term(*infix.right, syntax::Sort::Obj)?,
                ],
            ),
        )))
        .negated())
    }

    fn fof_unit_formula(
        &mut self,
        fof: UnitFormula,
    ) -> anyhow::Result<syntax::FOF> {
        match fof {
            UnitFormula::Unitary(f) => self.fof_unitary_formula(f),
            UnitFormula::Unary(f) => self.fof_unary_formula(f),
        }
    }

    fn fof_binary_assoc(
        &mut self,
        fof: BinaryAssoc,
    ) -> anyhow::Result<syntax::FOF> {
        Ok(match fof {
            BinaryAssoc::And(fs) => syntax::FOF::And(
                fs.0.into_iter()
                    .map(|f| self.fof_unit_formula(f))
                    .collect::<anyhow::Result<_>>()?,
            ),
            BinaryAssoc::Or(fs) => syntax::FOF::Or(
                fs.0.into_iter()
                    .map(|f| self.fof_unit_formula(f))
                    .collect::<anyhow::Result<_>>()?,
            ),
        })
    }

    fn fof_binary_nonassoc(
        &mut self,
        fof: BinaryNonassoc,
    ) -> anyhow::Result<syntax::FOF> {
        let left = self.fof_unit_formula(*fof.left)?;
        let right = self.fof_unit_formula(*fof.right)?;
        use NonassocConnective as NC;
        Ok(match fof.op {
            NC::LRImplies => syntax::FOF::Or(vec![left.negated(), right]),
            NC::RLImplies => syntax::FOF::Or(vec![left, right.negated()]),
            NC::Equivalent => {
                syntax::FOF::Eqv(Box::new(left), Box::new(right))
            }
            NC::NotEquivalent => {
                syntax::FOF::Eqv(Box::new(left), Box::new(right)).negated()
            }
            NC::NotAnd => syntax::FOF::And(vec![left, right]).negated(),
            NC::NotOr => syntax::FOF::Or(vec![left, right]).negated(),
        })
    }

    fn fof_binary_formula(
        &mut self,
        fof: BinaryFormula,
    ) -> anyhow::Result<syntax::FOF> {
        match fof {
            BinaryFormula::Assoc(f) => self.fof_binary_assoc(f),
            BinaryFormula::Nonassoc(f) => self.fof_binary_nonassoc(f),
        }
    }

    fn fof_quantified_formula(
        &mut self,
        fof: QuantifiedFormula,
    ) -> anyhow::Result<syntax::FOF> {
        let num_bound = fof.bound.0.len();
        for x in fof.bound.0.into_iter() {
            let string = x.0 .0.to_string();
            let var = self.fresh;
            self.fresh.increment();
            self.bound.push((string, var));
        }
        let mut f = self.fof_unit_formula(*fof.formula)?;
        for _ in 0..num_bound {
            let (_, var) = self.bound.pop().expect("bound this earlier");
            f = match fof.quantifier {
                Quantifier::Forall => syntax::FOF::All(var, Box::new(f)),
                Quantifier::Exists => syntax::FOF::Ex(var, Box::new(f)),
            };
        }
        Ok(f)
    }

    fn fof_unitary_formula(
        &mut self,
        fof: UnitaryFormula,
    ) -> anyhow::Result<syntax::FOF> {
        Ok(match fof {
            UnitaryFormula::Quantified(f) => self.fof_quantified_formula(f)?,
            UnitaryFormula::Atomic(f) => {
                syntax::FOF::Atom(self.fof_atomic_formula(*f)?)
            }
            UnitaryFormula::Parenthesised(f) => self.fof_logic_formula(*f)?,
        })
    }

    fn fof_unary_formula(
        &mut self,
        fof: UnaryFormula,
    ) -> anyhow::Result<syntax::FOF> {
        Ok(match fof {
            UnaryFormula::Unary(_, f) => self.fof_unit_formula(*f)?.negated(),
            UnaryFormula::InfixUnary(f) => self.fof_infix_unary(f)?,
        })
    }

    fn fof_logic_formula(
        &mut self,
        fof: LogicFormula,
    ) -> anyhow::Result<syntax::FOF> {
        match fof {
            LogicFormula::Binary(f) => self.fof_binary_formula(f),
            LogicFormula::Unary(f) => self.fof_unary_formula(f),
            LogicFormula::Unitary(f) => self.fof_unitary_formula(f),
        }
    }

    fn fof_formula(
        &mut self,
        fof: fof::Formula,
    ) -> anyhow::Result<syntax::FOF> {
        self.fof_logic_formula(fof.0)
    }

    fn literal(&mut self, lit: Literal) -> anyhow::Result<syntax::FOF> {
        Ok(match lit {
            Literal::Atomic(atomic) => {
                syntax::FOF::Atom(self.fof_atomic_formula(atomic)?)
            }
            Literal::NegatedAtomic(atomic) => {
                syntax::FOF::Atom(self.fof_atomic_formula(atomic)?).negated()
            }
            Literal::Infix(infix) => self.fof_infix_unary(infix)?,
        })
    }

    fn cnf_formula(
        &mut self,
        cnf: cnf::Formula,
    ) -> anyhow::Result<syntax::FOF> {
        let disjunction = match cnf {
            cnf::Formula::Disjunction(d) => d,
            cnf::Formula::Parenthesised(d) => d,
        };
        Ok(syntax::FOF::Or(
            disjunction
                .0
                .into_iter()
                .map(|lit| self.literal(lit))
                .collect::<anyhow::Result<_>>()?,
        ))
    }

    fn annotated<D: Dialect>(
        &mut self,
        options: &Options,
        selection: Option<&FnvHashSet<Name>>,
        path: Rc<str>,
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
        let source = syntax::Source::Axiom {
            path,
            name: format!("{}", &annotated.name),
        };

        self.fresh = Id::new(0);
        self.free.clear();
        let mut formula = annotated.formula.load(self)?;
        if negate {
            formula = formula.negated();
        }
        self.pp
            .process(options, formula, is_goal, source, self.fresh);
        Ok(())
    }

    fn load(
        &mut self,
        options: &Options,
        parent: Option<&path::Path>,
        selection: Option<FnvHashSet<Name>>,
        path: &path::Path,
    ) -> anyhow::Result<()> {
        let display_path: Rc<str> = format!("'{}'", path.display()).into();
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
                            options,
                            selection.as_ref(),
                            display_path.clone(),
                            fof.0,
                        )?;
                    }
                    AnnotatedFormula::Cnf(cnf) => {
                        self.annotated(
                            options,
                            selection.as_ref(),
                            display_path.clone(),
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
                    self.load(options, path.parent(), selection, included)
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
    fn load(self, loader: &mut Loader) -> anyhow::Result<syntax::FOF>;
}

impl Dialect for fof::Formula<'_> {
    fn load(self, loader: &mut Loader) -> anyhow::Result<syntax::FOF> {
        loader.fof_formula(self)
    }
}

impl Dialect for cnf::Formula<'_> {
    fn load(self, loader: &mut Loader) -> anyhow::Result<syntax::FOF> {
        loader.cnf_formula(self)
    }
}

pub(crate) fn load(options: &Options) -> anyhow::Result<syntax::Matrix> {
    let mut loader = Loader::default();
    loader.initialise();
    loader
        .load(options, None, None, &options.path)
        .with_context(|| {
            format!("failed to load from '{}'", options.path.display())
        })?;
    Ok(loader.finish(options))
}
