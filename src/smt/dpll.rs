use crate::block::{Block, BlockMap, Id, Range};
use super::Atom;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct Lit {
    pub(crate) atom: Id<Atom>,
    pub(crate) pol: bool,
}

#[derive(Debug, Clone, Copy)]
struct Cls {
    lits: Range<Lit>,
    watch: [Id<Lit>; 2],
}

#[derive(Debug, Clone, Copy)]
struct Decision {
    atom: Id<Atom>,
    backtrack: bool,
}

#[derive(Default)]
pub(crate) struct DPLL {
    pub(crate) literals: Block<Lit>,
    units: Vec<Id<Lit>>,
    clauses: Block<Cls>,
    assignment: BlockMap<Atom, Option<bool>>,
    watch: BlockMap<Atom, [Vec<Id<Cls>>; 2]>,
    trail: Vec<Decision>,
    propagating: Vec<Id<Lit>>,
    next: Id<Atom>,
}

impl DPLL {
    pub(crate) fn new_atom(&mut self, max: Id<Atom>) {
        self.assignment.ensure_capacity(max, Default::default);
        self.watch.ensure_capacity(max, Default::default);
    }

    pub(crate) fn assert(&mut self, lits: Range<Lit>) -> bool {
        let length = lits.len();
        if length == 0 {
            return false;
        } else if length == 1 {
            let unit = lits.start;
            self.units.push(unit);
            self.restart();
        } else {
            let watch = if let Some(watch) = self.find_watch(lits) {
                watch
            }
            else {
                self.restart();
                [lits.start, Id::new(lits.start.index + 1)]
            };
            let id = self.clauses.push(Cls { lits, watch });
            for watched in &watch {
                let Lit { atom, pol } = self.literals[*watched];
                self.watch[atom][pol as usize].push(id);
            }
        }
        self.solve()
    }

    fn restart(&mut self) {
        self.trail.clear();
        for id in self.assignment.range() {
            self.assignment[id] = None;
        }
        self.next = Id::default();
        for unit in &self.units {
            self.propagating.push(*unit);
        }
    }

    fn solve(&mut self) -> bool {
        if !self.propagate() {
            return false;
        }
        while self.decide() {
            let atom = self.next;
            self.assign(Lit { atom, pol: false }, true);
            self.next.index += 1;
            while !self.propagate() {
                if !self.backtrack() {
                    return false;
                }
            }
        }
        true
    }

    fn decide(&mut self) -> bool {
        while self.next < self.assignment.len() {
            if self.assignment[self.next].is_none() {
                return true;
            }
            self.next.index += 1;
        }
        false
    }

    fn backtrack(&mut self) -> bool {
        self.propagating.clear();
        while let Some(Decision { atom, backtrack }) = self.trail.pop() {
            if backtrack {
                self.next = atom;
                self.assign(Lit { atom, pol: true }, false);
                self.next.index += 1;
                return true;
            }
            self.assignment[atom] = None;
        }
        false
    }

    fn propagate(&mut self) -> bool {
        while let Some(id) = self.propagating.pop() {
            let Lit { atom, pol } = self.literals[id];
            if self.assignment[atom] == Some(!pol) {
                return false;
            }
            self.assign(Lit { atom, pol }, false);
        }
        true
    }

    fn assign(&mut self, lit: Lit, backtrack: bool) {
        let Lit { atom, pol } = lit;
        self.trail.push(Decision { atom, backtrack });
        self.assignment[atom] = Some(pol);
        self.analyze_assignment(atom, pol);
    }

    fn analyze_assignment(&mut self, atom: Id<Atom>, pol: bool) {
        let mut i = 0;
        while i < self.watch[atom][!pol as usize].len() {
            let id = self.watch[atom][!pol as usize][i];
            let clause = self.clauses[id];
            let [w1, w2] = clause.watch;
            let feasible = if self.literals[w1].atom == atom {
                w2
            } else {
                w1
            };
            if let Some(new) = clause
                .lits
                .into_iter()
                .find(|lit| *lit != feasible && self.feasible(*lit))
            {
                let watch = [feasible, new];
                self.clauses[id].watch = watch;
                self.watch[atom][!pol as usize].swap_remove(i);
                let Lit { atom, pol } = self.literals[new];
                self.watch[atom][pol as usize].push(id);
            } else {
                if self.assignment[self.literals[feasible].atom].is_none() {
                    self.propagating.push(feasible);
                }
                i += 1;
            }
        }
    }

    fn find_watch(&self, lits: Range<Lit>) -> Option<[Id<Lit>; 2]> {
        let mut feasible = lits.into_iter().filter(|lit| self.feasible(*lit));
        let l1 = feasible.next()?;
        let l2 = feasible.next()?;
        Some([l1, l2])
    }

    fn feasible(&self, lit: Id<Lit>) -> bool {
        let Lit { atom, pol } = self.literals[lit];
        let assignment = self.assignment[atom];
        assignment.is_none() || assignment == Some(pol)
    }
}
