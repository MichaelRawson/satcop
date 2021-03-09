use crate::binding::Bindings;
use crate::block::{Block, BlockMap, Id, Off};
use crate::syntax::{Cls, DisEq, Info, Lit, Sym, Trm, Var};

pub(crate) const FALLBACK_GROUNDING: Id<Sym> = Id::new(0);
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
    pub(crate) terms: Block<Trm>,
    pub(crate) lits: Block<Lit>,
    pub(crate) diseqs: Block<DisEq>,
    pub(crate) clauses: Block<Cls>,
    pub(crate) info: BlockMap<Cls, Info>,
    pub(crate) start: Block<Id<Cls>>,
    pub(crate) index: BlockMap<Sym, Entry>,
    pub(crate) max_var: Var,
    pub(crate) grounding_constants: Block<Id<Sym>>,
}

impl Matrix {
    pub(crate) fn print_cnf(&self) {
        let mut bindings = Bindings::default();
        bindings.ensure_capacity(self.max_var);
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
                    self.print_literal(&bindings, Off::new(id, 0));
                }
            }
            println!(").")
        }
    }

    pub(crate) fn print_literal(&self, bindings: &Bindings, lit: Off<Lit>) {
        if !self.lits[lit.id].pol {
            print!("~");
        }
        self.print_term(&bindings, Off::new(self.lits[lit.id].atom, lit.offset));
    }

    fn print_term(&self, bindings: &Bindings, term: Off<Trm>) {
        let mut term = bindings.resolve(&self.terms, term);
        if self.terms[term.id].is_var() {
            print!("X{}", self.terms[term.id].as_var().offset(term.offset).0);
        } else {
            let sym = self.terms[term.id].as_sym();
            if sym == EQUALITY {
                term.id.index += 1;
                self.print_term(
                    bindings,
                    Off::new(self.terms[term.id].as_arg(), term.offset),
                );
                print!(" = ");
                term.id.index += 1;
                self.print_term(
                    bindings,
                    Off::new(self.terms[term.id].as_arg(), term.offset),
                );
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
                    term.id.index += 1;
                    let arg = self.terms[term.id].as_arg();
                    self.print_term(bindings, Off::new(arg, term.offset));
                }
                print!(")");
            }
        }
    }
}
