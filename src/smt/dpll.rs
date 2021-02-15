use super::{Atom, Lit};
use crate::block::{Block, BlockMap, Id, Range};

#[derive(Debug, Clone, Copy)]
struct Cls {
    lits: Range<Lit>,
    watch: [Id<Lit>; 2],
}

#[derive(Debug, Clone, Copy)]
struct Decision {
    assignment: Lit,
    reason: Option<Range<Lit>>,
}

#[derive(Debug, Clone, Copy)]
struct Propagation {
    lit: Id<Lit>,
    reason: Range<Lit>,
}

#[derive(Default)]
pub(crate) struct DPLL {
    units: Vec<Id<Lit>>,
    clauses: Block<Cls>,
    assignment: BlockMap<Atom, Option<bool>>,
    watch: BlockMap<Atom, [Vec<Id<Cls>>; 2]>,
    trail: Vec<Decision>,
    propagating: Vec<Propagation>,
    conflict: Vec<Lit>,
    next: Id<Atom>,
}

impl DPLL {
    pub(crate) fn max_atom(&mut self, max: Id<Atom>) {
        self.assignment.ensure_capacity(max, Default::default);
        self.watch.ensure_capacity(max, Default::default);
    }

    pub(crate) fn assert(&mut self, literals: &Block<Lit>, lits: Range<Lit>) {
        /*
        print!("cnf(1, axiom, $false");
        for lit in lits {
            let Lit { pol, atom } = literals[lit];
            print!(" | ");
            if !pol {
                print!("~");
            }
            print!("p{}", atom.index);
        }
        println!(").");
        */

        let length = lits.len();
        if length == 1 {
            let unit = lits.start;
            self.units.push(unit);
        } else {
            let watch = [lits.start, Id::new(lits.start.index + 1)];
            let id = self.clauses.push(Cls { lits, watch });
            for watched in &watch {
                let Lit { atom, pol } = literals[*watched];
                self.watch[atom][pol as usize].push(id);
            }
        }
    }

    pub(crate) fn assigned_false(&self, lit: Lit) -> bool {
        self.assignment[lit.atom] != Some(lit.pol)
    }

    pub(crate) fn restart(&mut self) {
        self.trail.clear();
        for id in self.assignment.range() {
            self.assignment[id] = None;
        }
        self.next = Id::default();
        for unit in &self.units {
            let reason = Range::new(*unit, Id::new(unit.index + 1));
            self.propagating.push(Propagation { lit: *unit, reason });
        }
    }

    pub(crate) fn propagate(
        &mut self,
        literals: &Block<Lit>,
    ) -> Option<Range<Lit>> {
        while let Some(Propagation { lit, reason }) = self.propagating.pop() {
            let Lit { atom, pol } = literals[lit];
            if let Some(assigned) = self.assignment[atom] {
                if assigned != pol {
                    self.propagating.clear();
                    return Some(reason);
                }
            } else {
                self.assign(literals, Lit { atom, pol }, Some(reason));
            }
        }
        None
    }

    pub(crate) fn analyze_conflict(
        &mut self,
        literals: &mut Block<Lit>,
        reason: Range<Lit>,
    ) {
        for id in reason {
            self.conflict.push(literals[id]);
        }
        while let Some(Decision { assignment, reason }) = self.trail.pop() {
            if let Some(reason) = reason {
                if let Some(position) = self.conflict.iter().position(|lit| {
                    lit.atom == assignment.atom && lit.pol != assignment.pol
                }) {
                    let resolvent = self.conflict.swap_remove(position);
                    self.resolve(literals, resolvent, reason);
                }
            }
        }

        let start = literals.len();
        for lit in self.conflict.drain(..) {
            literals.push(lit);
        }
        let stop = literals.len();
        self.assert(literals, Range::new(start, stop));
    }

    fn resolve(&mut self, literals: &Block<Lit>, on: Lit, reason: Range<Lit>) {
        for other in reason {
            let other = literals[other];
            if other.atom != on.atom
                && !self.conflict.iter().any(|lit| lit == &other)
            {
                self.conflict.push(other);
            }
        }
    }

    pub(crate) fn tiebreak(&mut self, literals: &Block<Lit>) -> bool {
        while self.next < self.assignment.len() {
            let atom = self.next;
            self.next.index += 1;
            if self.assignment[atom].is_some() {
                continue;
            }
            self.assign(literals, Lit { atom, pol: false }, None);
            return true;
        }
        false
    }

    fn assign(
        &mut self,
        literals: &Block<Lit>,
        assignment: Lit,
        reason: Option<Range<Lit>>,
    ) {
        self.trail.push(Decision { assignment, reason });
        let Lit { atom, pol } = assignment;
        self.assignment[atom] = Some(pol);
        self.analyze_assignment(literals, atom, pol);
    }

    fn analyze_assignment(
        &mut self,
        literals: &Block<Lit>,
        atom: Id<Atom>,
        pol: bool,
    ) {
        let mut i = 0;
        while i < self.watch[atom][!pol as usize].len() {
            let id = self.watch[atom][!pol as usize][i];
            let clause = self.clauses[id];
            let [w1, w2] = clause.watch;
            let feasible = if literals[w1].atom == atom { w2 } else { w1 };
            if let Some(new) = clause
                .lits
                .into_iter()
                .find(|lit| *lit != feasible && self.feasible(literals, *lit))
            {
                let watch = [feasible, new];
                self.clauses[id].watch = watch;
                self.watch[atom][!pol as usize].swap_remove(i);
                let Lit { atom, pol } = literals[new];
                self.watch[atom][pol as usize].push(id);
            } else {
                if self.assignment[literals[feasible].atom].is_none() {
                    self.propagating.push(Propagation {
                        lit: feasible,
                        reason: clause.lits,
                    });
                }
                i += 1;
            }
        }
    }

    fn feasible(&self, literals: &Block<Lit>, lit: Id<Lit>) -> bool {
        let Lit { atom, pol } = literals[lit];
        let assignment = self.assignment[atom];
        assignment.is_none() || assignment == Some(pol)
    }
}
