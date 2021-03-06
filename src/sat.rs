use crate::binding::Bindings;
use crate::block::{Id, Off};
use crate::digest::{Digest, DigestMap, DigestSet};
use crate::matrix::Matrix;
use crate::syntax::{Cls, Lit, Sym, Trm};
use std::os::raw::c_int;

const PICOSAT_UNSATISFIABLE: c_int = 20;

#[repr(C)]
struct PicoSAT {
    _unused: [u8; 0],
}

#[link(name = "picosat")]
extern "C" {
    fn picosat_init() -> *mut PicoSAT;
    fn picosat_add(sat: *mut PicoSAT, lit: c_int);
    fn picosat_sat(sat: *mut PicoSAT, limit: c_int) -> c_int;
    fn picosat_changed(sat: *mut PicoSAT) -> c_int;
    fn picosat_deref_toplevel(sat: *mut PicoSAT, lit: c_int) -> c_int;
}

pub(crate) struct Solver {
    sat: *mut PicoSAT,
    atoms: DigestMap<c_int>,
    cache: DigestSet,
    fresh: c_int,
}

impl Default for Solver {
    fn default() -> Self {
        let sat = unsafe { picosat_init() };
        let atoms = DigestMap::default();
        let cache = DigestSet::default();
        let fresh = 0;
        Self {
            sat,
            atoms,
            cache,
            fresh,
        }
    }
}

impl Solver {
    pub(crate) fn assert(
        &mut self,
        matrix: &Matrix,
        bindings: &Bindings,
        clauses: &[Off<Cls>],
    ) {
        let mut scratch = vec![];
        'clauses: for clause in clauses {
            for ground in matrix.grounding_constants.range() {
                let mut digest = Digest::default();
                for lit in matrix.clauses[clause.id].lits {
                    let lit = self.literal(
                        matrix,
                        bindings,
                        Off::new(lit, clause.offset),
                        matrix.grounding_constants[ground],
                    );
                    digest.update(lit as u32);
                    scratch.push(lit);
                }
                if self.cache.insert(digest) {
                    for lit in scratch.drain(..) {
                        unsafe { picosat_add(self.sat, lit) };
                    }
                    unsafe { picosat_add(self.sat, 0) };
                } else {
                    scratch.clear();
                    continue 'clauses;
                }
            }
        }
    }

    pub(crate) fn solve(&mut self) -> bool {
        unsafe { picosat_sat(self.sat, -1) != PICOSAT_UNSATISFIABLE }
    }

    pub(crate) fn model_changed(&mut self) -> bool {
        unsafe { picosat_changed(self.sat) != 0 }
    }

    pub(crate) fn is_assigned_false(
        &mut self,
        matrix: &Matrix,
        bindings: &Bindings,
        lit: Off<Lit>,
    ) -> bool {
        let lit = self.literal(matrix, bindings, lit, Id::new(0));
        unsafe { picosat_deref_toplevel(self.sat, lit) == -1 }
    }

    fn literal(
        &mut self,
        matrix: &Matrix,
        bindings: &Bindings,
        lit: Off<Lit>,
        ground: Id<Sym>,
    ) -> c_int {
        let Lit { pol, atom } = matrix.lits[lit.id];
        let mut lit =
            self.atom(matrix, bindings, Off::new(atom, lit.offset), ground);
        if !pol {
            lit = -lit;
        }
        lit
    }

    fn atom(
        &mut self,
        matrix: &Matrix,
        bindings: &Bindings,
        atom: Off<Trm>,
        ground: Id<Sym>,
    ) -> c_int {
        let mut digest = Digest::default();
        self.term(&mut digest, matrix, bindings, atom, ground);
        let fresh = &mut self.fresh;
        let atom = *self.atoms.entry(digest).or_insert_with(|| {
            *fresh += 1;
            *fresh
        });
        atom
    }

    fn term(
        &mut self,
        digest: &mut Digest,
        matrix: &Matrix,
        bindings: &Bindings,
        term: Off<Trm>,
        ground: Id<Sym>,
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
                digest.update(ground.index);
            } else {
                self.term(digest, matrix, bindings, arg, ground);
            };
        }
    }
}
