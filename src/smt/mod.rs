mod dpll;
mod ground;

use crate::binding::Bindings;
use crate::block::{Block, Id, Off};
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
    empty_clause: bool,
    literals: Block<Lit>,
    dpll: DPLL,
    ground: Ground,
}

impl Solver {
    pub(crate) fn assert(
        &mut self,
        matrix: &Matrix,
        bindings: &Bindings,
        clause: Off<syntax::Cls>,
    ) -> bool {
        let grounded =
            self.ground
                .clause(&mut self.literals, matrix, bindings, clause);
        self.dpll.max_atom(self.ground.atom_counter);
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
            if self.dpll.propagate(&self.literals).is_some() {
                return false;
            }
            while self.dpll.tiebreak(&self.literals) {
                if let Some(conflict) = self.dpll.propagate(&self.literals) {
                    self.dpll.analyze_conflict(&mut self.literals, conflict);
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
        let lit = self.ground.literal(matrix, bindings, lit);
        self.dpll.assigned_false(lit)
    }
}
