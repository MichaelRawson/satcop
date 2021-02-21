use crate::block::{Block, BlockMap, Id};
use crate::syntax::{Cls, DisEq, Info, Lit, Sym, Trm};

pub(crate) const EQUALITY: Id<Sym> = Id::new(0);

#[derive(Debug, Clone, Copy)]
pub(crate) struct Pos {
    pub(crate) cls: Id<Cls>,
    pub(crate) lit: Id<Lit>,
}

#[derive(Debug)]
pub(crate) struct Entry {
    pub(crate) pol: [Vec<Pos>; 2],
}

#[derive(Debug, Default)]
pub(crate) struct Matrix {
    pub(crate) syms: Block<Sym>,
    pub(crate) terms: Block<Trm>,
    pub(crate) lits: Block<Lit>,
    pub(crate) diseqs: Block<DisEq>,
    pub(crate) clauses: Block<Cls>,
    pub(crate) info: BlockMap<Cls, Info>,
    pub(crate) start: Vec<Id<Cls>>,
    pub(crate) index: BlockMap<Sym, Entry>,
}
