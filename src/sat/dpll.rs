use super::{Atom, Lit};
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

#[derive(Debug, Clone, Copy)]
struct Decision {
    assignment: Lit,
    reason: Option<Range<Lit>>,
}

#[derive(Default)]
pub(super) struct DPLL {
    trail: Vec<Decision>,
    units: Vec<Id<Lit>>,
    clauses: Block<Cls>,
    assignment: BlockMap<Atom, Option<bool>>,
    watch: BlockMap<Atom, [Block<Id<Cls>>; 2]>,
    propagating: Vec<Propagation>,
    next: Id<Atom>,
    empty_clause: bool,
}

impl DPLL {
    pub(super) fn max_atom(&mut self, max: Id<Atom>) {
        self.assignment.ensure_capacity(max, Default::default);
        self.watch.ensure_capacity(max, Default::default);
    }

    pub(super) fn assert(
        &mut self,
        literals: &mut Block<Lit>,
        clause: Range<Lit>,
    ) {
        /*
        print!("cnf(1, axiom, $false");
        for lit in clause {
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
        if length == 0 {
            self.empty_clause = true;
        } else if length == 1 {
            let unit = clause.start;
            self.units.push(unit);
            while let Some(decision) = self.trail.pop() {
                self.assignment[decision.assignment.atom] = None;
            }
            self.next = Id::new(0);
        } else {
            let id = self.clauses.push(Cls { lits: clause });
            while clause
                .into_iter()
                .filter(|id| self.feasible(literals, *id))
                .count()
                < 2
            {
                while let Some(Decision { assignment, reason }) =
                    self.trail.pop()
                {
                    let atom = assignment.atom;
                    self.assignment[atom] = None;
                    if reason.is_none() {
                        self.next = atom;
                        break;
                    }
                }
            }
            let mut index = 0;
            for id in clause {
                if index > 1 {
                    break;
                }
                if self.feasible(literals, id) {
                    let mut dest = clause.start;
                    dest.index += index;
                    #[allow(clippy::manual_swap)]
                    {
                        let replaced = literals[dest];
                        literals[dest] = literals[id];
                        literals[id] = replaced;
                    }
                    index += 1;
                }
            }
            let watch = [clause.start, Id::new(clause.start.index + 1)];
            for watched in &watch {
                let Lit { atom, pol } = literals[*watched];
                self.watch[atom][pol as usize].push(id);
            }
        }
    }

    pub(super) fn solve(&mut self, literals: &mut Block<Lit>) -> bool {
        loop {
            if self.empty_clause {
                return false;
            }
            if self.trail.is_empty() {
                for unit in &self.units {
                    let unit = *unit;
                    let reason = Range::new(unit, Id::new(unit.index + 1));
                    self.propagating.push(Propagation { lit: unit, reason });
                }
            }
            let start = literals.len();
            if !self.propagate(literals) {
                self.analyze_conflict(literals, start);
                continue;
            }
            if !self.tiebreak(literals) {
                return true;
            }
        }
    }

    pub(super) fn is_assigned_false(&self, lit: Lit) -> bool {
        let Lit { atom, pol } = lit;
        self.assignment[atom] == Some(!pol)
    }

    fn propagate(&mut self, literals: &mut Block<Lit>) -> bool {
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

    fn analyze_conflict(&mut self, literals: &mut Block<Lit>, start: Id<Lit>) {
        while let Some(Decision { assignment, reason }) = self.trail.pop() {
            self.assignment[assignment.atom] = None;
            if let Some(reason) = reason {
                if let Some(position) =
                    Range::new(start, literals.len()).into_iter().find(|id| {
                        literals[*id].atom == assignment.atom
                            && literals[*id].pol != assignment.pol
                    })
                {
                    let resolvent = literals[position];
                    literals[position] = literals[literals.last()];
                    literals.pop();
                    self.resolve(literals, start, resolvent, reason);
                }
            }
        }
        self.next = Id::new(0);
        self.assert(literals, Range::new(start, literals.len()));
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

    fn tiebreak(&mut self, literals: &mut Block<Lit>) -> bool {
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
        let mut i = Id::new(0);
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
                    let new = literals[other];
                    let old = literals[assigned];
                    let last = self.watch[atom][!pol as usize]
                        [self.watch[atom][!pol as usize].last()];
                    self.watch[atom][!pol as usize][i] = last;
                    self.watch[atom][!pol as usize].pop();
                    self.watch[new.atom][new.pol as usize].push(id);
                    literals[other] = old;
                    literals[assigned] = new;
                    continue 'watch;
                }
            }
            if self.assignment[literals[feasible].atom].is_none() {
                self.propagating.push(Propagation {
                    lit: feasible,
                    reason: clause.lits,
                });
            }
            i.index += 1;
        }
    }

    fn feasible(&self, literals: &Block<Lit>, lit: Id<Lit>) -> bool {
        let Lit { atom, pol } = literals[lit];
        let assignment = self.assignment[atom];
        assignment.is_none() || assignment == Some(pol)
    }
}
