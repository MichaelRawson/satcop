mod dpll;

use crate::binding::Bindings;
use crate::block::{Block, Id, Off, Range};
use crate::digest::{Digest, DigestMap, DigestSet};
use crate::matrix::Matrix;
use crate::syntax;
use dpll::DPLL;

#[derive(Debug)]
struct Atom;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct Lit {
    atom: Id<Atom>,
    pol: bool,
}

pub(crate) struct Solver {
    dpll: DPLL,
    clause_cache: DigestSet,
    literals: Block<Lit>,
    atoms: DigestMap<Id<Atom>>,
    fresh: Id<Atom>,
}

impl Default for Solver {
    fn default() -> Self {
        let dpll = DPLL::default();
        let clause_cache = DigestSet::default();
        let literals = Block::default();
        let atoms = DigestMap::default();
        let fresh = Id::new(0);
        Self {
            dpll,
            clause_cache,
            literals,
            atoms,
            fresh,
        }
    }
}

impl Solver {
    pub(crate) fn assert(
        &mut self,
        matrix: &Matrix,
        bindings: &Bindings,
        clause: Off<syntax::Cls>,
    ) -> bool {
        let grounded = self.clause(matrix, bindings, clause);
        if let Some(clause) = grounded {
            self.dpll.assert(&mut self.literals, clause);
            true
        } else {
            false
        }
    }

    pub(crate) fn solve(&mut self) -> bool {
        self.dpll.solve(&mut self.literals)
    }

    pub(crate) fn is_ground_false(
        &mut self,
        matrix: &Matrix,
        bindings: &Bindings,
        lit: Off<syntax::Lit>,
    ) -> bool {
        let mut ground = true;
        let lit = self.literal(matrix, bindings, lit, &mut ground);
        ground && self.dpll.is_assigned_false(lit)
    }

    fn clause(
        &mut self,
        matrix: &Matrix,
        bindings: &Bindings,
        clause: Off<syntax::Cls>,
    ) -> Option<Range<Lit>> {
        let start = self.literals.len();
        let mut discard_clause = false;
        'next: for lit in matrix.clauses[clause.id].lits {
            let mut _ground = true;
            let lit = self.literal(
                matrix,
                bindings,
                Off::new(lit, clause.offset),
                &mut _ground
            );
            for id in Range::new(start, self.literals.len()) {
                let other = self.literals[id];
                if other.atom == lit.atom {
                    if other.pol == lit.pol {
                        continue 'next;
                    } else {
                        discard_clause = true;
                    }
                }
            }
            self.literals.push(lit);
        }
        if discard_clause {
            self.literals.truncate(start);
            return None;
        }

        let stop = self.literals.len();
        let clause = Range::new(start, stop);
        let mut digest = Digest::default();
        for lit in clause {
            let Lit { pol, atom } = self.literals[lit];
            digest.update(pol);
            digest.update(atom.index);
        }
        if self.clause_cache.contains(&digest) {
            self.literals.truncate(start);
            None
        } else {
            self.clause_cache.insert(digest);
            Some(clause)
        }
    }

    fn literal(
        &mut self,
        matrix: &Matrix,
        bindings: &Bindings,
        lit: Off<syntax::Lit>,
        ground: &mut bool
    ) -> Lit {
        let syntax::Lit { pol, atom } = matrix.lits[lit.id];
        let atom =
            self.atom(matrix, bindings, Off::new(atom, lit.offset), ground);
        Lit { pol, atom }
    }

    fn atom(
        &mut self,
        matrix: &Matrix,
        bindings: &Bindings,
        atom: Off<syntax::Trm>,
        ground: &mut bool
    ) -> Id<Atom> {
        let mut digest = Digest::default();
        self.term(matrix, bindings, atom, &mut digest, ground);
        let fresh = &mut self.fresh;
        let atom = *self.atoms.entry(digest).or_insert_with(|| {
            let atom = *fresh;
            fresh.index += 1;
            atom
        });
        self.dpll.max_atom(atom);
        atom
    }

    fn term(
        &mut self,
        matrix: &Matrix,
        bindings: &Bindings,
        term: Off<syntax::Trm>,
        digest: &mut Digest,
        ground: &mut bool,
    ) {
        let sym = matrix.terms[term.id].as_sym();
        digest.update(sym.index);
        let arity = matrix.syms[sym].arity;
        let mut argit = term.id;
        for _ in 0..arity {
            argit.index += 1;
            let arg = matrix.terms[argit].as_arg();
            let arg =
                bindings.resolve(&matrix.terms, Off::new(arg, term.offset));
            if matrix.terms[arg.id].is_var() {
                digest.update(0u128);
                *ground = false;
            } else {
                self.term(matrix, bindings, arg, digest, ground);
            };
        }
    }
}
