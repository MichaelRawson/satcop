use crate::block::{Block, BlockMap, Id};
use crate::syntax::{Cls, Info, Lit, Sym, Trm};

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
    pub(crate) clauses: Block<Cls>,
    pub(crate) info: BlockMap<Cls, Info>,
    pub(crate) start: Vec<Id<Cls>>,
    pub(crate) index: BlockMap<Sym, Entry>,
}
