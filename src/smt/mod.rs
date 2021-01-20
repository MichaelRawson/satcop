use crate::binding::Bindings;
use crate::block::{Block, Id, Off, Range};
use crate::matrix::Matrix;
use crate::sharing::Sharing;
use crate::syntax;
use fnv::FnvHashMap;

#[derive(Debug, Clone, Copy)]
struct Trm(u32);

#[derive(Debug, Clone, Copy)]
pub(crate) struct Atom(Id<Trm>);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Lit {
    pol: bool,
    atom: Id<Atom>,
}

const VAR: Id<Trm> = Id::new(0);

pub(crate) struct Solver {
    terms: Block<Trm>,
    term_scratch: Block<Trm>,
    term_sharing: Sharing<u32, Id<Trm>>,
    atoms: Block<Atom>,
    atom_map: FnvHashMap<Id<Trm>, Id<Atom>>,
    literals: Block<Lit>,
    clause_sharing: Sharing<Lit, Id<Lit>>,
}

impl Solver {
    pub(crate) fn assert(
        &mut self,
        matrix: &Matrix,
        bindings: &Bindings,
        clause: Off<syntax::Cls>,
    ) {
        let clause =
            if let Some(clause) = self.clause(matrix, bindings, clause) {
                clause
            } else {
                return;
            };
    }

    fn clause(
        &mut self,
        matrix: &Matrix,
        bindings: &Bindings,
        clause: Off<syntax::Cls>,
    ) -> Option<Range<Lit>> {
        let start = self.literals.len();
        for lit in matrix.clauses[clause.id].lits {
            self.literal(matrix, bindings, Off::new(lit, clause.offset));
        }
        let stop = self.literals.len();
        let clause = Range::new(start, stop);
        self.literals[clause].sort_unstable();
        let mut node = self.clause_sharing.start();
        for id in clause {
            node = self.clause_sharing.next(node, self.literals[id]);
        }
        let shared = self.clause_sharing.finish(node, start);
        if start == shared {
            return Some(clause);
        }
        self.literals.truncate(start);
        None
    }

    fn literal(
        &mut self,
        matrix: &Matrix,
        bindings: &Bindings,
        lit: Off<syntax::Lit>,
    ) {
        let syntax::Lit { pol, atom } = matrix.lits[lit.id];
        let atom = self.atom(matrix, bindings, Off::new(atom, lit.offset));
        self.literals.push(Lit { pol, atom });
    }

    pub(crate) fn atom(
        &mut self,
        matrix: &Matrix,
        bindings: &Bindings,
        atom: Off<syntax::Trm>,
    ) -> Id<Atom> {
        let term = self.term(matrix, bindings, atom);
        let atoms = &mut self.atoms;
        *self
            .atom_map
            .entry(term)
            .or_insert_with(|| atoms.push(Atom(term)))
    }

    fn term(
        &mut self,
        matrix: &Matrix,
        bindings: &Bindings,
        mut term: Off<syntax::Trm>,
    ) -> Id<Trm> {
        let sym = matrix.terms[term.id].as_sym();
        let mut node = self.term_sharing.start();
        let record = self.term_scratch.push(Trm(sym.index));
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
            for recorded in Range::new(record, self.term_scratch.len()) {
                self.terms.push(self.term_scratch[recorded]);
            }
        }
        self.term_scratch.truncate(record);
        shared
    }
}

impl Default for Solver {
    fn default() -> Self {
        let mut terms = Block::default();
        terms.push(Trm(0));
        let term_scratch = Block::default();
        let term_sharing = Sharing::default();
        let atoms = Block::default();
        let atom_map = FnvHashMap::default();
        let literals = Block::default();
        let clause_sharing = Sharing::default();
        Self {
            terms,
            term_scratch,
            term_sharing,
            atoms,
            atom_map,
            literals,
            clause_sharing,
        }
    }
}
