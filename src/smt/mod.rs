mod dpll;

use crate::binding::Bindings;
use crate::block::{Block, BlockMap, Id, Off, Range};
use crate::digest::{Digest, DigestMap, DigestSet};
use crate::matrix::{Matrix, EQUALITY};
use crate::syntax;
use crate::syntax::Sym;
use dpll::DPLL;

#[derive(Debug, Clone, Copy)]
struct Trm(u32);

const VAR: Id<Trm> = Id::new(0);

impl Trm {
    fn sym(sym: Id<Sym>) -> Self {
        Self(sym.index)
    }

    fn arg(arg: Id<Self>) -> Self {
        Self(arg.index)
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct Atom(Id<Trm>);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct Lit {
    pub(crate) atom: Id<Atom>,
    pub(crate) pol: bool,
}

#[derive(Debug, Clone, Copy)]
pub(super) struct Decision {
    pub(super) assignment: Lit,
    reason: Option<Range<Lit>>,
}

pub(crate) struct Solver {
    empty_clause: bool,
    dpll: DPLL,
    clause_cache: DigestSet,
    literals: Block<Lit>,
    atoms: Block<Atom>,
    atom_map: BlockMap<Trm, Option<Id<Atom>>>,
    terms: Block<Trm>,
    term_sharing: DigestMap<Id<Trm>>,
    arg_scratch: Vec<Id<Trm>>,
}

impl Default for Solver {
    fn default() -> Self {
        let empty_clause = false;
        let dpll = DPLL::default();
        let clause_cache = DigestSet::default();
        let literals = Block::default();
        let atoms = Block::default();
        let atom_map = BlockMap::default();
        let mut terms = Block::default();
        terms.push(Trm::sym(EQUALITY));
        let term_sharing = DigestMap::default();
        let arg_scratch = vec![];
        Self {
            empty_clause,
            dpll,
            clause_cache,
            literals,
            atoms,
            atom_map,
            terms,
            term_sharing,
            arg_scratch,
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
            if clause.len() == 0 {
                self.empty_clause = true;
                return true;
            }
            self.dpll.assert(&self.literals, clause);
            true
        } else {
            false
        }
    }

    pub(crate) fn solve(&mut self) -> bool {
        if self.empty_clause {
            return false;
        }
        'restart: loop {
            self.dpll.restart();
            if !self.dpll.propagate(&mut self.literals) {
                return false;
            }
            while self.dpll.tiebreak(&mut self.literals) {
                let start = self.literals.len();
                if !self.dpll.propagate(&mut self.literals) {
                    self.dpll.analyze_conflict(&mut self.literals, start);
                    continue 'restart;
                }
            }
            return true;
        }
    }

    pub(crate) fn assigned_false(
        &mut self,
        matrix: &Matrix,
        bindings: &Bindings,
        lit: Off<syntax::Lit>,
    ) -> bool {
        let lit = self.literal(matrix, bindings, lit);
        self.dpll.assigned_false(lit)
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
            let lit =
                self.literal(matrix, bindings, Off::new(lit, clause.offset));
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
    ) -> Lit {
        let syntax::Lit { pol, atom } = matrix.lits[lit.id];
        let atom = self.atom(matrix, bindings, Off::new(atom, lit.offset));
        Lit { pol, atom }
    }

    fn atom(
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
            let atom = self.atoms.push(Atom(term));
            self.dpll.max_atom(atom);
            self.atom_map[term] = Some(atom);
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
        let record = self.arg_scratch.len();
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
            self.arg_scratch.push(arg);
        }
        if sym == EQUALITY {
            let left = self.arg_scratch[record];
            let right = self.arg_scratch[record + 1];
            if left < right {
                self.arg_scratch.swap(record, record + 1);
            }
        }
        let id = self.terms.push(Trm(sym.index));
        let mut digest = Digest::default();
        digest.update(sym.index);
        for arg in self.arg_scratch.drain(record..) {
            self.terms.push(Trm::arg(arg));
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
