use super::{Atom, Lit, Trm};
use crate::binding::Bindings;
use crate::block::{Block, BlockMap, Id, Off, Range};
use crate::digest::{Digest, DigestMap, DigestSet};
use crate::matrix::Matrix;
use crate::syntax;

const VAR: Id<Trm> = Id::new(0);

pub(crate) struct Ground {
    pub(crate) atom_counter: Id<Atom>,
    terms: Block<Trm>,
    args: Vec<Id<Trm>>,
    term_sharing: DigestMap<Id<Trm>>,
    atom_map: BlockMap<Trm, Option<Id<Atom>>>,
    clause_cache: DigestSet,
}

impl Default for Ground {
    fn default() -> Self {
        let mut terms = Block::default();
        terms.push(Trm(0));
        let args = vec![];
        let term_sharing = DigestMap::default();
        let atom_counter = Id::default();
        let atom_map = BlockMap::default();
        let clause_cache = DigestSet::default();
        Self {
            atom_counter,
            terms,
            args,
            term_sharing,
            atom_map,
            clause_cache,
        }
    }
}

impl Ground {
    pub(crate) fn clause(
        &mut self,
        literals: &mut Block<Lit>,
        matrix: &Matrix,
        bindings: &Bindings,
        clause: Off<syntax::Cls>,
    ) -> Option<Range<Lit>> {
        let start = literals.len();
        let mut discard_clause = false;
        'next: for lit in matrix.clauses[clause.id].lits {
            let lit =
                self.literal(matrix, bindings, Off::new(lit, clause.offset));
            for id in Range::new(start, literals.len()) {
                let other = literals[id];
                if other.atom == lit.atom {
                    if other.pol == lit.pol {
                        continue 'next;
                    } else {
                        discard_clause = true;
                    }
                }
            }
            literals.push(lit);
        }
        if discard_clause {
            literals.truncate(start);
            return None;
        }

        let stop = literals.len();
        let clause = Range::new(start, stop);
        let mut digest = Digest::default();
        for lit in clause {
            let Lit { pol, atom } = literals[lit];
            digest.update(pol);
            digest.update(atom.index);
        }
        if self.clause_cache.contains(&digest) {
            literals.truncate(start);
            None
        } else {
            self.clause_cache.insert(digest);
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
        self.terms.push(Trm(sym.index));
        let mut digest = Digest::default();
        digest.update(sym.index);
        for arg in self.args.drain(record..) {
            self.terms.push(Trm(arg.index));
            digest.update(arg.index);
        }
        if let Some(shared) = self.term_sharing.get(&digest) {
            self.terms.truncate(id);
            *shared
        } else {
            self.term_sharing.insert(digest, id);
            id
        }
    }
}
