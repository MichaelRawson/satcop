use super::{Atom, Decision, Lit};
use crate::block::{Block, BlockMap, Id, Range};

#[derive(Debug, Clone, Copy)]
struct Cls {
    lits: Range<Lit>,
}

#[derive(Debug, Clone, Copy)]
struct Propagation {
    lit: Id<Lit>,
    reason: Range<Lit>,
}

#[derive(Default)]
pub(super) struct DPLL {
    pub(super) trail: Block<Decision>,
    units: Vec<Id<Lit>>,
    clauses: Block<Cls>,
    assignment: BlockMap<Atom, Option<bool>>,
    watch: BlockMap<Atom, [Vec<Id<Cls>>; 2]>,
    propagating: Vec<Propagation>,
    next: Id<Atom>,
}

impl DPLL {
    pub(super) fn max_atom(&mut self, max: Id<Atom>) {
        self.assignment.ensure_capacity(max, Default::default);
        self.watch.ensure_capacity(max, Default::default);
    }

    pub(super) fn assert(&mut self, literals: &Block<Lit>, clause: Range<Lit>) {
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

        let length = clause.len();
        if length == 1 {
            let unit = clause.start;
            self.units.push(unit);
        } else {
            let id = self.clauses.push(Cls { lits: clause });
            let watch = [clause.start, Id::new(clause.start.index + 1)];
            for watched in &watch {
                let Lit { atom, pol } = literals[*watched];
                self.watch[atom][pol as usize].push(id);
            }
        }
    }

    pub(super) fn assigned_false(&self, lit: Lit) -> bool {
        self.assignment[lit.atom] != Some(lit.pol)
    }

    pub(super) fn restart(&mut self) {
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

    pub(super) fn propagate(
        &mut self,
        literals: &mut Block<Lit>,
    ) -> bool {
        while let Some(Propagation { lit, reason }) = self.propagating.pop() {
            let Lit { atom, pol } = literals[lit];
            if let Some(assigned) = self.assignment[atom] {
                if assigned != pol {
                    for id in reason {
                        literals.push(literals[id]);
                    }
                    self.propagating.clear();
                    return false;
                }
            } else {
                self.assign(literals, Lit { atom, pol }, Some(reason));
            }
        }
        true
    }

    pub(super) fn analyze_conflict(
        &mut self,
        literals: &mut Block<Lit>,
        start: Id<Lit>,
    ) {
        while let Some(Decision { assignment, reason }) = self.trail.pop() {
            if let Some(reason) = reason {
                if let Some(position) =
                    Range::new(start, literals.len()).into_iter().find(|id| {
                        literals[*id].atom == assignment.atom
                            && literals[*id].pol != assignment.pol
                    })
                {
                    let resolvent = literals.swap_remove(position);
                    self.resolve(literals, start, resolvent, reason);
                }
            }
        }
        let stop = literals.len();
        self.assert(literals, Range::new(start, stop));
    }

    fn resolve(
        &mut self,
        literals: &mut Block<Lit>,
        start: Id<Lit>,
        on: Lit,
        reason: Range<Lit>,
    ) {
        for other in reason {
            let other = literals[other];
            if other.atom == on.atom {
                continue;
            }
            if Range::new(start, literals.len())
                .into_iter()
                .any(|id| literals[id] == other)
            {
                continue;
            }
            literals.push(other);
        }
    }

    pub(super) fn tiebreak(&mut self, literals: &mut Block<Lit>) -> bool {
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
        literals: &mut Block<Lit>,
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
        literals: &mut Block<Lit>,
        atom: Id<Atom>,
        pol: bool,
    ) {
        let mut i = 0;
        'watch: while i < self.watch[atom][!pol as usize].len() {
            let id = self.watch[atom][!pol as usize][i];
            let clause = self.clauses[id];
            let w1 = clause.lits.start;
            let w2 = Id::new(clause.lits.start.index + 1);
            let (assigned, feasible) = if literals[w1].atom == atom {
                (w1, w2)
            } else {
                (w2, w1)
            };
            for other in clause.lits.into_iter().skip(2) {
                if self.feasible(literals, other) {
                    literals.swap(assigned, other);
                    self.watch[atom][!pol as usize].swap_remove(i);
                    let Lit { atom, pol } = literals[assigned];
                    self.watch[atom][pol as usize].push(id);
                    continue 'watch;
                }
            }
            if self.assignment[literals[feasible].atom].is_none() {
                self.propagating.push(Propagation {
                    lit: feasible,
                    reason: clause.lits,
                });
            }
            i += 1;
        }
    }

    fn feasible(&self, literals: &Block<Lit>, lit: Id<Lit>) -> bool {
        let Lit { atom, pol } = literals[lit];
        let assignment = self.assignment[atom];
        assignment.is_none() || assignment == Some(pol)
    }
}
