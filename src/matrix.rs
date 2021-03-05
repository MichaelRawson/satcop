use crate::block::{Block, BlockMap, Id};
use crate::syntax::{Cls, DisEq, Info, Lit, Sym, Trm};
use fnv::FnvHashSet;

pub(crate) const EQUALITY: Id<Sym> = Id::new(1);

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
    pub(crate) goal_constants: FnvHashSet<Id<Sym>>,
    pub(crate) terms: Block<Trm>,
    pub(crate) lits: Block<Lit>,
    pub(crate) diseqs: Block<DisEq>,
    pub(crate) clauses: Block<Cls>,
    pub(crate) info: BlockMap<Cls, Info>,
    pub(crate) start: Block<Id<Cls>>,
    pub(crate) index: BlockMap<Sym, Entry>,
}

impl Matrix {
    pub(crate) fn dump_cnf(&self) {
        for id in self.clauses.range() {
            print!("cnf(c{}, ", id.index);
            if self.info[id].is_goal {
                print!("negated_conjecture, ");
            } else {
                print!("axiom, ");
            }
            let clause = self.clauses[id];
            if clause.lits.is_empty() {
                print!("$false")
            } else {
                for id in clause.lits {
                    if id != clause.lits.start {
                        print!(" | ");
                    }
                    let lit = self.lits[id];
                    if !lit.pol {
                        print!("~");
                    }
                    self.dump_term(lit.atom);
                }
            }
            println!(").")
        }
    }

    fn dump_term(&self, mut id: Id<Trm>) {
        let term = self.terms[id];
        if term.is_var() {
            print!("X{}", term.as_var().0);
        } else {
            let sym = term.as_sym();
            if sym == EQUALITY {
                id.index += 1;
                self.dump_term(self.terms[id].as_arg());
                print!(" = ");
                id.index += 1;
                self.dump_term(self.terms[id].as_arg());
            } else {
                let arity = self.syms[sym].arity;
                print!("{}", self.syms[sym].name);
                if arity == 0 {
                    return;
                }
                print!("(");
                for i in 0..arity {
                    if i != 0 {
                        print!(",");
                    }
                    id.index += 1;
                    let arg = self.terms[id].as_arg();
                    self.dump_term(arg);
                }
                print!(")");
            }
        }
    }
}
