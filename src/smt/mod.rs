mod dpll;
mod euf;

use crate::binding::Bindings;
use crate::block::{Block, BlockMap, Id, Off, Range};
use crate::digest::{Digest, DigestMap, DigestSet};
use crate::matrix::{Matrix, EQUALITY};
use crate::syntax;
use crate::syntax::Sym;
use dpll::DPLL;
use euf::EUF;

#[derive(Debug, Clone, Copy)]
struct Trm(u32);

impl Trm {
    fn as_sym(self) -> Id<Sym> {
        Id::new(self.0)
    }

    fn as_arg(self) -> Id<Trm> {
        Id::new(self.0)
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
    euf: EUF,
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
        let euf = EUF::default();
        let clause_cache = DigestSet::default();
        let literals = Block::default();
        let atoms = Block::default();
        let atom_map = BlockMap::default();
        let mut terms = Block::default();
        terms.push(Trm(0));
        let term_sharing = DigestMap::default();
        let arg_scratch = vec![];
        Self {
            empty_clause,
            dpll,
            euf,
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
            self.euf.max_term(self.terms.len());
            self.dpll.max_atom(self.atoms.len());
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
            self.euf.restart();
            if !self.dpll.propagate(&mut self.literals) {
                return false;
            }
            if !self.consult_theories(Id::new(0)) {
                return false;
            }
            while self.dpll.tiebreak(&mut self.literals) {
                let start = self.literals.len();
                let checkpoint = self.dpll.trail.len();
                if !self.dpll.propagate(&mut self.literals) {
                    self.dpll.analyze_conflict(&mut self.literals, start);
                    continue 'restart;
                }
                if !self.consult_theories(checkpoint) {
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

    fn consult_theories(&mut self, start: Id<Decision>) -> bool {
        for id in Range::new(start, self.dpll.trail.len()) {
            let assignment = self.dpll.trail[id].assignment;
            let atom = assignment.atom;
            let Atom(term) = self.atoms[atom];
            if self.terms[term].as_sym() == EQUALITY {
                let left = self.terms[Id::new(term.index + 1)].as_arg();
                let right = self.terms[Id::new(term.index + 2)].as_arg();
                if assignment.pol {
                    self.euf.assert_eq(assignment, left, right);
                } else {
                    self.euf.assert_neq(assignment, left, right);
                }
            }
        }
        self.euf.check(&mut self.literals)
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
                Id::new(0)
            } else {
                self.term(matrix, bindings, arg)
            };
            self.arg_scratch.push(arg);
        }
        let id = self.terms.len();
        self.terms.push(Trm(sym.index));
        let mut digest = Digest::default();
        digest.update(sym.index);
        for arg in self.arg_scratch.drain(record..) {
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
