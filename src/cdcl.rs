use crate::block::{Block, BlockMap, Id, Range};
use fnv::FnvHashSet;

#[derive(Debug, Clone, Copy)]
pub(crate) struct Atom;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Literal {
    pub(crate) pol: bool,
    pub(crate) atom: Id<Atom>,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct Clause {
    pub(crate) literals: Range<Literal>,
    parents: Range<Parent>,
}

#[derive(Debug, Clone, Copy)]
struct Parent(Id<Clause>);

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
    pub(crate) literals: Block<Literal>,
    pub(crate) clauses: Block<Clause>,
    assignment: BlockMap<Atom, Option<bool>>,
    derivation: Block<Parent>,
    trail: Vec<Decision>,
    propagating: Vec<Propagation>,
    next: Id<Atom>,
    empty: Option<Id<Clause>>,
    units: Vec<Id<Clause>>,
    binary: BlockMap<Atom, [Block<Id<Clause>>; 2]>,
    watch: BlockMap<Atom, [Block<Id<Clause>>; 2]>,
}

impl CDCL {
    pub(crate) fn fresh_atom(&mut self) -> Id<Atom> {
        let fresh = self.fresh;
        self.fresh.increment();
        self.assignment.push(None);
        self.binary.push([Block::default(), Block::default()]);
        self.watch.push([Block::default(), Block::default()]);
        fresh
    }

    pub(crate) fn assert(&mut self, clause: &[Literal]) -> Id<Clause> {
        let start = self.literals.len();
        for literal in clause {
            self.literals.push(*literal);
        }
        let end = self.literals.len();
        let literals = Range::new(start, end);
        let parents = Range::new(Id::new(0), Id::new(0));
        self.index(Clause { literals, parents })
    }

    pub(crate) fn solve(&mut self) -> bool {
        'restart: loop {
            if self.empty.is_some() {
                return false;
            }
            self.trail.clear();
            for id in self.assignment.range() {
                self.assignment[id] = None;
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
                if let Some(conflict) = self.propagate() {
                    self.analyze_conflict(conflict);
                    continue 'restart;
                }
                if !self.tiebreak() {
                    return true;
                }
            }
        }
    }

    pub(crate) fn is_assigned_false(&self, literal: Literal) -> bool {
        let Literal { atom, pol } = literal;
        self.assignment[atom] == Some(!pol)
    }

    pub(crate) fn core(&self) -> Vec<Id<Clause>> {
        let mut todo = vec![self.empty.unwrap()];
        let mut core = vec![];
        let mut done = FnvHashSet::default();
        while let Some(next) = todo.pop() {
            if done.insert(next) {
                let parents = self.clauses[next].parents;
                if parents.is_empty() {
                    core.push(next);
                } else {
                    for parent in parents {
                        todo.push(self.derivation[parent].0);
                    }
                }
            }
        }
        core.sort();
        core
    }

    fn index(&mut self, clause: Clause) -> Id<Clause> {
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

        let id = self.clauses.push(clause);
        let length = clause.literals.len();
        if length == 0 {
            self.empty = Some(id);
        } else if length == 1 {
            self.units.push(id);
        } else if length == 2 {
            let l1 = clause.literals.start;
            let l2 = l1.offset(1);
            self.binary[self.literals[l1].atom]
                [self.literals[l1].pol as usize]
                .push(id);
            self.binary[self.literals[l2].atom]
                [self.literals[l2].pol as usize]
                .push(id);
        } else {
            let w1 = clause.literals.start;
            let w2 = w1.offset(1);
            let watch = [w1, w2];
            for watched in &watch {
                let Literal { atom, pol } = self.literals[*watched];
                self.watch[atom][pol as usize].push(id);
            }
        }
        id
    }

    fn propagate(&mut self) -> Option<Id<Clause>> {
        while let Some(Propagation { literal, reason }) =
            self.propagating.pop()
        {
            let literal = self.literals[literal];
            if let Some(assigned) = self.assignment[literal.atom] {
                if assigned != literal.pol {
                    self.propagating.clear();
                    return Some(reason);
                }
            } else {
                self.assign(literal, Some(reason));
            }
        }
        None
    }

    fn analyze_conflict(&mut self, conflict: Id<Clause>) {
        let literal_start = self.literals.len();
        let derivation_start = self.derivation.len();
        for id in self.clauses[conflict].literals {
            self.literals.push(self.literals[id]);
        }
        self.derivation.push(Parent(conflict));
        while let Some(Decision { assignment, reason }) = self.trail.pop() {
            self.assignment[assignment.atom] = None;
            if let Some(reason) = reason {
                if let Some(position) =
                    Range::new(literal_start, self.literals.len())
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
                    self.resolve(literal_start, resolvent, reason);
                    self.derivation.push(Parent(reason));
                }
            }
        }
        self.index(Clause {
            literals: Range::new(literal_start, self.literals.len()),
            parents: Range::new(derivation_start, self.derivation.len()),
        });
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
            self.next.increment();
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
            let l2 = l1.offset(1);
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
            let w2 = w1.offset(1);
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
            i.increment();
        }
    }

    fn feasible(&self, id: Id<Literal>) -> bool {
        let Literal { atom, pol } = self.literals[id];
        let assignment = self.assignment[atom];
        assignment.is_none() || assignment == Some(pol)
    }
}
