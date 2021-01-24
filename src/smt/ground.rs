use super::{Atom, Lit, Trm};
use crate::binding::Bindings;
use crate::block::{Block, BlockMap, Id, Off, Range};
use crate::matrix::Matrix;
use crate::syntax;
use crate::trie::Trie;

const VAR: Id<Trm> = Id::new(0);

pub(crate) struct Ground {
    terms: Block<Trm>,
    args: Vec<Id<Trm>>,
    term_sharing: BlockMap<syntax::Sym, Trie<Id<Trm>, Id<Trm>>>,
    pub(crate) atom_counter: Id<Atom>,
    atom_map: BlockMap<Trm, Option<Id<Atom>>>,
    pub(crate) literals: Block<Lit>,
    clause_sharing: Trie<Lit, ()>,
}

impl Default for Ground {
    fn default() -> Self {
        let mut terms = Block::default();
        terms.push(Trm(0));
        let args = vec![];
        let term_sharing = BlockMap::default();
        let atom_counter = Id::default();
        let atom_map = BlockMap::default();
        let literals = Block::default();
        let clause_sharing = Trie::default();
        Self {
            terms,
            args,
            term_sharing,
            atom_counter,
            atom_map,
            literals,
            clause_sharing,
        }
    }
}

impl Ground {
    pub(crate) fn clause(
        &mut self,
        matrix: &Matrix,
        bindings: &Bindings,
        clause: Off<syntax::Cls>,
    ) -> Option<Range<Lit>> {
        let start = self.literals.len();
        for lit in matrix.clauses[clause.id].lits {
            let lit =
                self.literal(matrix, bindings, Off::new(lit, clause.offset));
            self.literals.push(lit);
        }
        let stop = self.literals.len();
        let clause = Range::new(start, stop);
        let mut node = &mut self.clause_sharing;
        for lit in clause {
            node = node.next(self.literals[lit]);
        }
        if node.value.is_some() {
            self.literals.truncate(start);
            None
        } else {
            node.value = Some(());
            Some(clause)
        }
    }

    pub(crate) fn literal(
        &mut self,
        matrix: &Matrix,
        bindings: &Bindings,
        lit: Off<syntax::Lit>,
    ) -> Lit {
        let syntax::Lit { pol, atom } = matrix.lits[lit.id];
        let atom = self.atom(matrix, bindings, Off::new(atom, lit.offset));
        Lit { pol, atom }
    }

    pub(crate) fn atom(
        &mut self,
        matrix: &Matrix,
        bindings: &Bindings,
        atom: Off<syntax::Trm>,
    ) -> Id<Atom> {
        let term = self.term(matrix, bindings, atom);
        self.atom_map.ensure_capacity(term, Default::default);
        if let Some(atom) = self.atom_map[term] {
            atom
        } else {
            let atom = self.atom_counter;
            self.atom_map[term] = Some(atom);
            self.atom_counter.index += 1;
            atom
        }
    }

    fn term(
        &mut self,
        matrix: &Matrix,
        bindings: &Bindings,
        term: Off<syntax::Trm>,
    ) -> Id<Trm> {
        let sym = matrix.terms[term.id].as_sym();
        let record = self.args.len();
        let arity = matrix.syms[sym].arity;
        let mut argit = term.id;
        for _ in 0..arity {
            argit.index += 1;
            let arg = matrix.terms[argit].as_arg();
            let arg =
                bindings.resolve(&matrix.terms, Off::new(arg, term.offset));
            let arg = if matrix.terms[arg.id].is_var() {
                VAR
            } else {
                self.term(matrix, bindings, arg)
            };
            self.args.push(arg);
        }
        let id = self.terms.len();
        self.term_sharing.ensure_capacity(sym, Default::default);
        self.terms.push(Trm(sym.index));
        let mut node = &mut self.term_sharing[sym];
        for arg in self.args.drain(record..) {
            self.terms.push(Trm(arg.index));
            node = node.next(arg);
        }
        if let Some(shared) = node.value {
            self.terms.truncate(id);
            shared
        } else {
            node.value = Some(id);
            id
        }
    }
}
