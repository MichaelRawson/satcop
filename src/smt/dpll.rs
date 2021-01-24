use super::{Atom, Lit};
use crate::block::{Block, BlockMap, Id, Range};

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
    solved: bool,
    units: Vec<Id<Lit>>,
    clauses: Block<Cls>,
    assignment: BlockMap<Atom, Option<bool>>,
    watch: BlockMap<Atom, [Vec<Id<Cls>>; 2]>,
    trail: Vec<Decision>,
    propagating: Vec<Id<Lit>>,
    next: Id<Atom>,
}

impl DPLL {
    pub(crate) fn max_atom(&mut self, max: Id<Atom>) {
        self.assignment.ensure_capacity(max, Default::default);
        self.watch.ensure_capacity(max, Default::default);
    }

    pub(crate) fn assert(&mut self, block: &Block<Lit>, lits: Range<Lit>) {
        let length = lits.len();
        if length == 1 {
            let unit = lits.start;
            self.units.push(unit);
            self.restart();
        } else {
            let watch = if let Some(watch) = self.find_watch(block, lits) {
                watch
            } else {
                self.restart();
                [lits.start, Id::new(lits.start.index + 1)]
            };
            let id = self.clauses.push(Cls { lits, watch });
            for watched in &watch {
                let Lit { atom, pol } = block[*watched];
                self.watch[atom][pol as usize].push(id);
            }
        }
        self.solved = false;
    }

    pub(crate) fn solve(&mut self, block: &Block<Lit>) -> bool {
        if self.solved {
            return true;
        }

        if !self.propagate(block) {
            return false;
        }
        while self.next < self.assignment.len() {
            let atom = self.next;
            self.next.index += 1;
            if self.assignment[atom].is_some() {
                continue;
            }
            self.assign(block, Lit { atom, pol: false }, true);
            while !self.propagate(block) {
                if !self.backtrack(block) {
                    return false;
                }
            }
        }
        self.solved = true;
        true
    }

    pub(crate) fn assigned_true(&self, lit: Lit) -> bool {
        self.assignment[lit.atom] == Some(lit.pol)
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

    fn backtrack(&mut self, block: &Block<Lit>) -> bool {
        self.propagating.clear();
        while let Some(Decision { atom, backtrack }) = self.trail.pop() {
            self.next = atom;
            if backtrack {
                self.next.index += 1;
                self.assign(block, Lit { atom, pol: true }, false);
                return true;
            }
            self.assignment[atom] = None;
        }
        false
    }

    fn propagate(&mut self, block: &Block<Lit>) -> bool {
        while let Some(id) = self.propagating.pop() {
            let Lit { atom, pol } = block[id];
            if self.assignment[atom] == Some(!pol) {
                return false;
            }
            self.assign(block, Lit { atom, pol }, false);
        }
        true
    }

    fn assign(&mut self, block: &Block<Lit>, lit: Lit, backtrack: bool) {
        let Lit { atom, pol } = lit;
        self.trail.push(Decision { atom, backtrack });
        self.assignment[atom] = Some(pol);
        self.analyze_assignment(block, atom, pol);
    }

    fn analyze_assignment(
        &mut self,
        block: &Block<Lit>,
        atom: Id<Atom>,
        pol: bool,
    ) {
        let mut i = 0;
        while i < self.watch[atom][!pol as usize].len() {
            let id = self.watch[atom][!pol as usize][i];
            let clause = self.clauses[id];
            let [w1, w2] = clause.watch;
            let feasible = if block[w1].atom == atom { w2 } else { w1 };
            if let Some(new) = clause
                .lits
                .into_iter()
                .find(|lit| *lit != feasible && self.feasible(block, *lit))
            {
                let watch = [feasible, new];
                self.clauses[id].watch = watch;
                self.watch[atom][!pol as usize].swap_remove(i);
                let Lit { atom, pol } = block[new];
                self.watch[atom][pol as usize].push(id);
            } else {
                if self.assignment[block[feasible].atom].is_none() {
                    self.propagating.push(feasible);
                }
                i += 1;
            }
        }
    }

    fn find_watch(
        &self,
        block: &Block<Lit>,
        lits: Range<Lit>,
    ) -> Option<[Id<Lit>; 2]> {
        let mut feasible =
            lits.into_iter().filter(|lit| self.feasible(block, *lit));
        let l1 = feasible.next()?;
        let l2 = feasible.next()?;
        Some([l1, l2])
    }

    fn feasible(&self, block: &Block<Lit>, lit: Id<Lit>) -> bool {
        let Lit { atom, pol } = block[lit];
        let assignment = self.assignment[atom];
        assignment.is_none() || assignment == Some(pol)
    }
}
