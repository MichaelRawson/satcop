use crate::binding::Bindings;
use crate::block::{Block, BlockMap, Id, Off, Range};
use std::fmt;
use std::rc::Rc;

pub(crate) const EQUALITY: Id<Symbol> = Id::new(1);

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Sort {
    Bool,
    Obj,
}

pub(crate) enum Name {
    Grounding,
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
            Self::Grounding => write!(f, "sG"),
            Self::Equality => write!(f, "sPE"),
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

pub(crate) struct Symbol {
    pub(crate) arity: u32,
    pub(crate) sort: Sort,
    pub(crate) name: Name,
}

impl fmt::Debug for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}/{}", self.name, self.arity)
    }
}

#[derive(Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
pub(crate) struct Term(i32);

impl Term {
    pub(crate) fn var(x: Var) -> Self {
        Self(-(x.0 as i32))
    }

    pub(crate) fn sym(f: Id<Symbol>) -> Self {
        Self(f.index as i32)
    }

    pub(crate) fn arg(arg: Id<Self>) -> Self {
        Self(arg.index as i32)
    }

    pub(crate) fn is_var(&self) -> bool {
        self.0 <= 0
    }

    pub(crate) fn as_var(&self) -> Var {
        Var(-self.0 as u32)
    }

    pub(crate) fn as_sym(&self) -> Id<Symbol> {
        Id::new(self.0 as u32)
    }

    pub(crate) fn as_arg(&self) -> Id<Self> {
        Id::new(self.0 as u32)
    }
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Clone, Copy)]
pub(crate) struct Literal {
    pub(crate) pol: bool,
    pub(crate) atom: Id<Term>,
}

impl fmt::Debug for Literal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if !self.pol {
            write!(f, "¬")?;
        }
        write!(f, "{:?}", self.atom)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct Disequation {
    pub(crate) left: Id<Term>,
    pub(crate) right: Id<Term>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct Ordering {
    pub(crate) left: Id<Term>,
    pub(crate) right: Id<Term>,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct Clause {
    pub(crate) vars: u32,
    pub(crate) literals: Range<Literal>,
    pub(crate) disequations: Range<Disequation>,
    pub(crate) orderings: Range<Ordering>,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct Position {
    pub(crate) cls: Id<Clause>,
    pub(crate) lit: Id<Literal>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Source {
    Equality,
    Axiom { path: Rc<str>, name: String },
}

#[derive(Debug, Clone)]
pub(crate) struct Info {
    pub(crate) is_goal: bool,
    pub(crate) source: Source,
}

#[derive(Debug, Default)]
pub(crate) struct Matrix {
    pub(crate) symbols: Block<Symbol>,
    pub(crate) terms: Block<Term>,
    pub(crate) literals: Block<Literal>,
    pub(crate) disequations: Block<Disequation>,
    pub(crate) orderings: Block<Ordering>,
    pub(crate) clauses: Block<Clause>,
    pub(crate) info: BlockMap<Clause, Info>,
    pub(crate) start: Block<Id<Clause>>,
    pub(crate) index: BlockMap<Symbol, [Vec<Position>; 2]>,
    pub(crate) grounding_constant: Id<Symbol>,
}

impl Matrix {
    pub(crate) fn print_cnf(&self) {
        let mut bindings = Bindings::default();
        for id in self.clauses.range() {
            print!("cnf(c{}, ", id.index);
            if self.info[id].is_goal {
                print!("negated_conjecture, ");
            } else {
                print!("axiom, ");
            }
            let clause = self.clauses[id];
            if clause.literals.is_empty() {
                print!("$false")
            } else {
                bindings.ensure_capacity(Var(clause.vars));
                for id in clause.literals {
                    if id != clause.literals.start {
                        print!(" | ");
                    }
                    self.print_literal(&bindings, Off::new(id, 0));
                }
            }
            print!("). % ");
            let mut sep = false;
            for id in clause.disequations {
                if sep {
                    print!(", ");
                }
                sep = true;
                let Disequation { left, right } = self.disequations[id];
                self.print_term(&bindings, Off::new(left, 0));
                print!(" != ");
                self.print_term(&bindings, Off::new(right, 0));
            }
            for id in clause.orderings {
                if sep {
                    print!(", ");
                }
                sep = true;
                let Ordering { left, right } = self.orderings[id];
                self.print_term(&bindings, Off::new(left, 0));
                print!(" >= ");
                self.print_term(&bindings, Off::new(right, 0));
            }
            println!();
        }
    }

    pub(crate) fn print_literal(
        &self,
        bindings: &Bindings,
        lit: Off<Literal>,
    ) {
        if !self.literals[lit.id].pol {
            print!("~");
        }
        self.print_term(
            &bindings,
            Off::new(self.literals[lit.id].atom, lit.offset),
        );
    }

    pub(crate) fn print_term(&self, bindings: &Bindings, term: Off<Term>) {
        let mut term = bindings.resolve(&self.terms, term);
        if self.terms[term.id].is_var() {
            print!("X{}", self.terms[term.id].as_var().offset(term.offset).0);
        } else {
            let sym = self.terms[term.id].as_sym();
            let arity = self.symbols[sym].arity;
            print!("{}", self.symbols[sym].name);
            if arity == 0 {
                return;
            }
            print!("(");
            for i in 0..arity {
                if i != 0 {
                    print!(",");
                }
                term.id.index += 1;
                let arg = self.terms[term.id].as_arg();
                self.print_term(bindings, Off::new(arg, term.offset));
            }
            print!(")");
        }
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum FOFTerm {
    Var(Var),
    Fun(Id<Symbol>, Vec<Rc<FOFTerm>>),
}

impl FOFTerm {
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

impl fmt::Debug for FOFTerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Var(x) => x.fmt(f),
            Self::Fun(g, args) if args.is_empty() => write!(f, "{:?}", g),
            Self::Fun(g, args) => write!(f, "{:?}{:?}", g, args),
        }
    }
}

#[derive(Clone)]
pub(crate) enum FOFAtom {
    Bool(bool),
    Pred(Rc<FOFTerm>),
}

impl FOFAtom {
    pub(crate) fn vars(&self, vars: &mut Vec<bool>) {
        match self {
            Self::Bool(_) => {}
            Self::Pred(p) => {
                p.vars(vars);
            }
        }
    }
}

impl fmt::Debug for FOFAtom {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Bool(b) => write!(f, "{:?}", b),
            Self::Pred(p) => write!(f, "{:?}", p),
        }
    }
}

pub(crate) enum FOF {
    Atom(FOFAtom),
    Not(Box<FOF>),
    And(Vec<FOF>),
    Or(Vec<FOF>),
    Eqv(Box<FOF>, Box<FOF>),
    All(Var, Box<FOF>),
    Ex(Var, Box<FOF>),
}

impl FOF {
    pub(crate) fn negated(self) -> Self {
        Self::Not(Box::new(self))
    }

    pub(crate) fn vars(&self, vars: &mut Vec<bool>) {
        match self {
            Self::Atom(atom) => {
                atom.vars(vars);
            }
            Self::Not(f) | Self::All(_, f) | Self::Ex(_, f) => {
                f.vars(vars);
            }
            Self::And(fs) | Self::Or(fs) => {
                for f in fs {
                    f.vars(vars);
                }
            }
            Self::Eqv(l, r) => {
                l.vars(vars);
                r.vars(vars);
            }
        }
    }
}

impl fmt::Debug for FOF {
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

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct NNFLiteral {
    pub(crate) pol: bool,
    pub(crate) atom: Rc<FOFTerm>,
}

impl fmt::Debug for NNFLiteral {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if !self.pol {
            write!(f, "¬")?;
        }
        write!(f, "{:?}", self.atom)
    }
}

#[derive(Debug)]
pub(crate) enum NNF {
    Lit(NNFLiteral),
    And(Vec<NNF>),
    Or(Vec<NNF>),
    All(Var, Box<NNF>),
    Ex(Var, Box<NNF>),
}

pub(crate) struct CNF(pub(crate) Vec<NNFLiteral>);

impl fmt::Debug for CNF {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.0)
    }
}
