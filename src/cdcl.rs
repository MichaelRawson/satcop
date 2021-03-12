use crate::block::{Block, BlockMap, Id, Range};

#[derive(Debug, Clone, Copy)]
pub(crate) struct Atom;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Literal {
    pub(crate) pol: bool,
    pub(crate) atom: Id<Atom>,
}

#[derive(Debug, Clone, Copy)]
struct Clause {
    literals: Range<Literal>,
}

#[derive(Debug, Clone, Copy)]
struct Propagation {
    literal: Id<Literal>,
    reason: Id<Clause>,
}

#[derive(Debug, Clone, Copy)]
struct Decision {
    assignment: Literal,
    reason: Option<Id<Clause>>,
}

#[derive(Default)]
pub(crate) struct CDCL {
    fresh: Id<Atom>,
    literals: Block<Literal>,
    clauses: Block<Clause>,
    assignment: BlockMap<Atom, Option<bool>>,
    trail: Vec<Decision>,
    propagating: Vec<Propagation>,
    next: Id<Atom>,
    empty_clause: bool,
    units: Vec<Id<Clause>>,
    binary: BlockMap<Atom, [Block<Id<Clause>>; 2]>,
    watch: BlockMap<Atom, [Block<Id<Clause>>; 2]>,
}

impl CDCL {
    pub(super) fn fresh_atom(&mut self) -> Id<Atom> {
        let fresh = self.fresh;
        self.fresh.index += 1;
        self.assignment.block.push(None);
        self.binary.block.push([Block::default(), Block::default()]);
        self.watch.block.push([Block::default(), Block::default()]);
        fresh
    }

    pub(super) fn assert(&mut self, clause: &[Literal]) {
        let start = self.literals.len();
        for literal in clause {
            self.literals.push(*literal);
        }
        let end = self.literals.len();
        let literals = Range::new(start, end);
        self.index(literals);
    }

    pub(super) fn solve(&mut self) -> bool {
        'restart: loop {
            if self.empty_clause {
                return false;
            }
            self.trail.clear();
            for id in self.assignment.block.range() {
                self.assignment.block[id] = None;
            }
            self.next = Id::new(0);
            for unit in &self.units {
                let literal = self.clauses[*unit].literals.start;
                self.propagating.push(Propagation {
                    literal,
                    reason: *unit,
                });
            }
            loop {
                let start = self.literals.len();
                if !self.propagate() {
                    self.analyze_conflict(start);
                    continue 'restart;
                }
                if !self.tiebreak() {
                    return true;
                }
            }
        }
    }

    pub(super) fn is_assigned_false(&self, literal: Literal) -> bool {
        let Literal { atom, pol } = literal;
        self.assignment[atom] == Some(!pol)
    }

    fn index(&mut self, literals: Range<Literal>) {
        /*
        print!("cnf({}, axiom, ", self.clauses.len().index);
        if literals.is_empty() {
            print!("$false");
        } else {
            for id in literals {
                if id != literals.start {
                    print!(" | ");
                }
                let Literal { pol, atom } = self.literals[id];
                if !pol {
                    print!("~");
                }
                print!("p{}", atom.index);
            }
        }
        println!(").");
        */

        let clause = Clause { literals };
        let id = self.clauses.push(clause);
        let length = literals.len();
        if length == 0 {
            self.empty_clause = true;
        } else if length == 1 {
            self.units.push(id);
        } else if length == 2 {
            let l1 = literals.start;
            let mut l2 = literals.start;
            l2.index += 1;
            self.binary[self.literals[l1].atom]
                [self.literals[l1].pol as usize]
                .push(id);
            self.binary[self.literals[l2].atom]
                [self.literals[l2].pol as usize]
                .push(id);
        } else {
            let w1 = literals.start;
            let mut w2 = literals.start;
            w2.index += 1;
            let watch = [w1, w2];
            for watched in &watch {
                let Literal { atom, pol } = self.literals[*watched];
                self.watch[atom][pol as usize].push(id);
            }
        }
    }

    fn propagate(&mut self) -> bool {
        while let Some(Propagation { literal, reason }) =
            self.propagating.pop()
        {
            let literal = self.literals[literal];
            if let Some(assigned) = self.assignment[literal.atom] {
                if assigned != literal.pol {
                    for id in self.clauses[reason].literals {
                        self.literals.push(self.literals[id]);
                    }
                    self.propagating.clear();
                    return false;
                }
            } else {
                self.assign(literal, Some(reason));
            }
        }
        true
    }

    fn analyze_conflict(&mut self, start: Id<Literal>) {
        while let Some(Decision { assignment, reason }) = self.trail.pop() {
            self.assignment[assignment.atom] = None;
            if let Some(reason) = reason {
                if let Some(position) = Range::new(start, self.literals.len())
                    .into_iter()
                    .find(|id| {
                        self.literals[*id].atom == assignment.atom
                            && self.literals[*id].pol != assignment.pol
                    })
                {
                    let resolvent = self.literals[position];
                    if let Some(last) = self.literals.pop() {
                        if position != self.literals.len() {
                            self.literals[position] = last;
                        }
                    } else {
                        unreachable!();
                    }
                    self.resolve(start, resolvent, reason);
                }
            }
        }
        self.index(Range::new(start, self.literals.len()));
    }

    fn resolve(
        &mut self,
        start: Id<Literal>,
        on: Literal,
        reason: Id<Clause>,
    ) {
        for other in self.clauses[reason].literals {
            let other = self.literals[other];
            if other.atom == on.atom {
                continue;
            }
            if Range::new(start, self.literals.len())
                .into_iter()
                .any(|id| self.literals[id] == other)
            {
                continue;
            }
            self.literals.push(other);
        }
    }

    fn tiebreak(&mut self) -> bool {
        while self.next < self.assignment.len() {
            let atom = self.next;
            self.next.index += 1;
            if self.assignment[atom].is_some() {
                continue;
            }
            let pol = false;
            self.assign(Literal { atom, pol }, None);
            return true;
        }
        false
    }

    fn assign(&mut self, assignment: Literal, reason: Option<Id<Clause>>) {
        self.trail.push(Decision { assignment, reason });
        let Literal { atom, pol } = assignment;
        self.assignment[atom] = Some(pol);
        self.analyze_assignment(atom, pol);
    }

    fn analyze_assignment(&mut self, atom: Id<Atom>, pol: bool) {
        let mut i = Id::new(0);
        for i in self.binary[atom][!pol as usize].range() {
            let id = self.binary[atom][!pol as usize][i];
            let clause = self.clauses[id];
            let l1 = clause.literals.start;
            let mut l2 = clause.literals.start;
            l2.index += 1;
            let feasible = if self.literals[l1].atom == atom {
                l2
            } else {
                l1
            };
            if self.assignment[self.literals[feasible].atom].is_none() {
                self.propagating.push(Propagation {
                    literal: feasible,
                    reason: id,
                });
            }
        }
        'watch: while i < self.watch[atom][!pol as usize].len() {
            let id = self.watch[atom][!pol as usize][i];
            let clause = self.clauses[id];
            let w1 = clause.literals.start;
            let mut w2 = clause.literals.start;
            w2.index += 1;
            let (assigned, feasible) = if self.literals[w1].atom == atom {
                (w1, w2)
            } else {
                (w2, w1)
            };
            for other in clause.literals.into_iter().skip(2) {
                if self.feasible(other) {
                    let new = self.literals[other];
                    let old = self.literals[assigned];
                    if let Some(last) = self.watch[atom][!pol as usize].pop() {
                        if i != self.watch[atom][!pol as usize].len() {
                            self.watch[atom][!pol as usize][i] = last;
                        }
                    } else {
                        unreachable!()
                    }
                    self.watch[new.atom][new.pol as usize].push(id);
                    self.literals[other] = old;
                    self.literals[assigned] = new;
                    continue 'watch;
                }
            }
            if self.assignment[self.literals[feasible].atom].is_none() {
                self.propagating.push(Propagation {
                    literal: feasible,
                    reason: id,
                });
            }
            i.index += 1;
        }
    }

    fn feasible(&self, id: Id<Literal>) -> bool {
        let Literal { atom, pol } = self.literals[id];
        let assignment = self.assignment[atom];
        assignment.is_none() || assignment == Some(pol)
    }
}
