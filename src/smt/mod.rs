mod dpll;
mod ground;

use crate::binding::Bindings;
use crate::block::{Id, Off};
use crate::matrix::Matrix;
use crate::syntax;

use dpll::DPLL;
use ground::Ground;

#[derive(Debug, Clone, Copy)]
struct Trm(u32);

#[derive(Debug, Clone, Copy)]
pub(crate) struct Atom(Id<Trm>);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct Lit {
    pub(crate) atom: Id<Atom>,
    pub(crate) pol: bool,
}

#[derive(Default)]
pub(crate) struct Solver {
    dpll: DPLL,
    ground: Ground,
}

impl Solver {
    pub(crate) fn assert(
        &mut self,
        matrix: &Matrix,
        bindings: &Bindings,
        clause: Off<syntax::Cls>,
    ) {
        if let Some(clause) = self.ground.clause(matrix, bindings, clause) {
            self.dpll.max_atom(self.ground.atom_counter);
            self.dpll.assert(&self.ground.literals, clause);
        }
    }

    pub(crate) fn solve(&mut self) -> bool {
        self.dpll.solve(&self.ground.literals)
    }

    pub(crate) fn assigned_false(
        &mut self,
        matrix: &Matrix,
        bindings: &Bindings,
        lit: Off<syntax::Lit>,
    ) -> bool {
        let lit = self.ground.literal(matrix, bindings, lit);
        self.dpll.assigned_false(lit)
    }

    pub(crate) fn has_restarted(&mut self) -> bool {
        std::mem::take(&mut self.dpll.restarted)
    }
}