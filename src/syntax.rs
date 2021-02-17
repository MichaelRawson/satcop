use crate::block::{Id, Range};
use std::fmt;
use std::rc::Rc;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Sort {
    Bool,
    Obj,
}

pub(crate) enum Name {
    Equality,
    Atom(String),
    Quoted(String),
    Number(String),
    Distinct(String),
    Skolem(u32),
    Definition(u32),
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Equality => write!(f, "="),
            Self::Atom(s) | Self::Number(s) => write!(f, "{}", s),
            Self::Quoted(quoted) => write!(f, "'{}'", quoted),
            Self::Distinct(distinct) => write!(f, "\"{}\"", distinct),
            Self::Skolem(n) => write!(f, "sK{}", n),
            Self::Definition(n) => write!(f, "sP{}", n),
        }
    }
}

impl Name {
    pub(crate) fn needs_congruence(&self) -> bool {
        !matches!(self, Name::Equality | Name::Definition(_))
    }
}

pub(crate) struct Sym {
    pub(crate) arity: u32,
    pub(crate) sort: Sort,
    pub(crate) name: Name,
}

impl fmt::Debug for Sym {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}/{}", self.name, self.arity)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct Var(pub(crate) u32);

impl Var {
    pub(crate) fn offset(&self, offset: u32) -> Self {
        Self(self.0 + offset)
    }
}

impl fmt::Debug for Var {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "X{}", self.0)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct Trm(i32);

impl Trm {
    pub(crate) fn var(x: Var) -> Self {
        Self(-(x.0 as i32))
    }

    pub(crate) fn sym(f: Id<Sym>) -> Self {
        Self(f.index as i32)
    }

    pub(crate) fn arg(arg: Id<Trm>) -> Self {
        Self(arg.index as i32)
    }

    pub(crate) fn is_var(&self) -> bool {
        self.0 < 0
    }

    pub(crate) fn is_sym(&self) -> bool {
        self.0 >= 0
    }

    pub(crate) fn as_var(&self) -> Var {
        Var(-self.0 as u32)
    }

    pub(crate) fn as_sym(&self) -> Id<Sym> {
        Id::new(self.0 as u32)
    }

    pub(crate) fn as_arg(&self) -> Id<Trm> {
        Id::new(self.0 as u32)
    }
}

impl fmt::Debug for Trm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Clone, Copy)]
pub(crate) struct Lit {
    pub(crate) pol: bool,
    pub(crate) atom: Id<Trm>,
}

impl fmt::Debug for Lit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if !self.pol {
            write!(f, "¬")?;
        }
        write!(f, "{:?}", self.atom)
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct Cls {
    pub(crate) lits: Range<Lit>,
    pub(crate) vars: u32,
}

#[derive(Clone)]
pub(crate) enum Term {
    Var(Var),
    Fun(Id<Sym>, Vec<Term>),
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Var(x) => x.fmt(f),
            Self::Fun(g, args) if args.is_empty() => write!(f, "{:?}", g),
            Self::Fun(g, args) => write!(f, "{:?}{:?}", g, args),
        }
    }
}

impl Term {
    fn vars(&self, vars: &mut Vec<bool>) {
        match self {
            Self::Var(x) => {
                vars[x.0 as usize] = true;
            }
            Self::Fun(_, ts) => {
                for t in ts {
                    t.vars(vars);
                }
            }
        }
    }
}

pub(crate) enum Atom {
    Bool(bool),
    Pred(Term),
}

impl fmt::Debug for Atom {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Bool(b) => write!(f, "{:?}", b),
            Self::Pred(p) => write!(f, "{:?}", p),
        }
    }
}

pub(crate) enum Formula {
    Atom(Atom),
    Not(Box<Formula>),
    And(Vec<Formula>),
    Or(Vec<Formula>),
    Eqv(Box<Formula>, Box<Formula>),
    All(Var, Box<Formula>),
    Ex(Var, Box<Formula>),
}

impl Formula {
    pub(crate) fn negated(self) -> Self {
        Self::Not(Box::new(self))
    }
}

impl fmt::Debug for Formula {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Atom(atom) => write!(f, "{:?}", atom),
            Self::Not(g) => write!(f, "¬{:?}", g),
            Self::And(fs) => write!(f, "and{:?}", fs),
            Self::Or(fs) => write!(f, "or{:?}", fs),
            Self::Eqv(l, r) => write!(f, "({:?} <=> {:?})", l, r),
            Self::All(x, g) => write!(f, "!{:?}. {:?}", x, g),
            Self::Ex(x, g) => write!(f, "?{:?}. {:?}", x, g),
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) enum Source {
    EqualityAxiom,
    File(Rc<str>),
}

#[derive(Debug, Clone)]
pub(crate) struct Info {
    pub(crate) source: Source,
    pub(crate) name: Rc<str>,
    pub(crate) is_goal: bool,
}

impl Info {
    pub(crate) fn clone_nongoal(&self) -> Self {
        let mut clone = self.clone();
        clone.is_goal = false;
        clone
    }
}

pub(crate) struct CNFLiteral {
    pub(crate) pol: bool,
    pub(crate) atom: Term,
}

impl fmt::Debug for CNFLiteral {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if !self.pol {
            write!(f, "¬")?;
        }
        write!(f, "{:?}", self.atom)
    }
}

impl CNFLiteral {
    pub(crate) fn vars(&self, vars: &mut Vec<bool>) {
        self.atom.vars(vars);
    }
}

pub(crate) struct CNFFormula(pub(crate) Vec<CNFLiteral>);

impl fmt::Debug for CNFFormula {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.0)
    }
}
