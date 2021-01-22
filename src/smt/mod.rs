mod dpll;

use crate::binding::Bindings;
use crate::block::{Block, Id, Off, Range};
use crate::matrix::Matrix;
use crate::sharing::Sharing;
use crate::syntax;
use dpll::{Lit, DPLL};
use fnv::FnvHashMap;

#[derive(Debug, Clone, Copy)]
struct Trm(u32);

#[derive(Debug, Clone, Copy)]
pub(crate) struct Atom(Id<Trm>);

const VAR: Id<Trm> = Id::new(0);

pub(crate) struct Solver {
    dpll: DPLL,
    terms: Block<Trm>,
    term_scratch: Vec<Trm>,
    term_sharing: Sharing<u32, Id<Trm>>,
    atoms: Block<Atom>,
    atom_map: FnvHashMap<Id<Trm>, Id<Atom>>,
    lit_scratch: Vec<Lit>,
    clause_sharing: Sharing<Lit, Id<Lit>>,
}

impl Solver {
    pub(crate) fn assert(
        &mut self,
        matrix: &Matrix,
        bindings: &Bindings,
        clause: Off<syntax::Cls>,
    ) -> bool {
        self.clause(matrix, bindings, clause)
            .map(|clause| self.dpll.assert(clause))
            .unwrap_or(true)
    }

    fn clause(
        &mut self,
        matrix: &Matrix,
        bindings: &Bindings,
        clause: Off<syntax::Cls>,
    ) -> Option<Range<Lit>> {
        for lit in matrix.clauses[clause.id].lits {
            self.literal(matrix, bindings, Off::new(lit, clause.offset));
        }
        self.lit_scratch.sort_unstable();
        self.lit_scratch.dedup();
        let mut last_atom = None;
        let mut tautology = false;
        for lit in &self.lit_scratch {
            if Some(lit.atom) == last_atom {
                tautology = true;
                break;
            }
            last_atom = Some(lit.atom);
        }
        if tautology {
            self.lit_scratch.clear();
            return None;
        }

        let mut node = self.clause_sharing.start();
        for lit in &self.lit_scratch {
            node = self.clause_sharing.next(node, *lit);
        }
        let start = self.dpll.literals.len();
        let shared = self.clause_sharing.finish(node, start);
        if start == shared {
            for lit in self.lit_scratch.drain(..) {
                self.dpll.literals.push(lit);
            }
            let stop = self.dpll.literals.len();
            let clause = Range::new(start, stop);
            Some(clause)
        } else {
            self.lit_scratch.clear();
            None
        }
    }

    fn literal(
        &mut self,
        matrix: &Matrix,
        bindings: &Bindings,
        lit: Off<syntax::Lit>,
    ) {
        let syntax::Lit { pol, atom } = matrix.lits[lit.id];
        let atom = self.atom(matrix, bindings, Off::new(atom, lit.offset));
        self.lit_scratch.push(Lit { pol, atom });
    }

    pub(crate) fn atom(
        &mut self,
        matrix: &Matrix,
        bindings: &Bindings,
        atom: Off<syntax::Trm>,
    ) -> Id<Atom> {
        let term = self.term(matrix, bindings, atom);
        let atoms = &mut self.atoms;
        let dpll = &mut self.dpll;
        *self.atom_map.entry(term).or_insert_with(|| {
            let id = atoms.push(Atom(term));
            dpll.new_atom(id);
            id
        })
    }

    fn term(
        &mut self,
        matrix: &Matrix,
        bindings: &Bindings,
        mut term: Off<syntax::Trm>,
    ) -> Id<Trm> {
        let sym = matrix.terms[term.id].as_sym();
        let mut node = self.term_sharing.start();
        let record = self.term_scratch.len();
        self.term_scratch.push(Trm(sym.index));
        node = self.term_sharing.next(node, sym.index);
        let arity = matrix.syms[sym].arity;
        for _ in 0..arity {
            term.id.index += 1;
            let arg = matrix.terms[term.id].as_arg();
            let arg =
                bindings.resolve(&matrix.terms, Off::new(arg, term.offset));
            let arg = if matrix.terms[arg.id].is_var() {
                VAR
            } else {
                self.term(matrix, bindings, arg)
            };
            self.term_scratch.push(Trm(arg.index));
            node = self.term_sharing.next(node, arg.index);
        }
        let id = self.terms.len();
        let shared = self.term_sharing.finish(node, id);
        if id == shared {
            for item in self.term_scratch.drain(record..) {
                self.terms.push(item);
            }
        }
        shared
    }
}

impl Default for Solver {
    fn default() -> Self {
        let dpll = DPLL::default();
        let mut terms = Block::default();
        terms.push(Trm(0));
        let term_scratch = vec![];
        let term_sharing = Sharing::default();
        let atoms = Block::default();
        let atom_map = FnvHashMap::default();
        let lit_scratch = vec![];
        let clause_sharing = Sharing::default();
        Self {
            dpll,
            terms,
            term_scratch,
            term_sharing,
            atoms,
            atom_map,
            lit_scratch,
            clause_sharing,
        }
    }
}
