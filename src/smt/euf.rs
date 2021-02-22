use super::{Lit, Trm};
use crate::block::{Block, BlockMap, Id};

#[derive(Clone, Copy)]
struct Set {
    parent: Id<Set>,
    rank: u32,
}

#[derive(Default)]
struct Disjoint {
    sets: Block<Set>,
    terms: BlockMap<Trm, Option<Id<Set>>>,
}

impl Disjoint {
    fn clear(&mut self) {
        self.sets.clear();
        for id in self.terms.range() {
            self.terms[id] = None;
        }
    }

    fn max_term(&mut self, id: Id<Trm>) {
        self.terms.ensure_capacity(id, Default::default);
    }

    fn singleton(&mut self) -> Id<Set> {
        let parent = self.sets.len();
        let rank = 0;
        let set = Set { parent, rank };
        self.sets.push(set)
    }

    fn find(&mut self, id: Id<Trm>) -> Id<Set> {
        let mut current = if let Some(set) = self.terms[id] {
            set
        } else {
            let set = self.singleton();
            self.terms[id] = Some(set);
            return set;
        };
        while self.sets[current].parent != current {
            let parent = self.sets[current].parent;
            let grandparent = self.sets[parent].parent;
            self.sets[current].parent = grandparent;
            current = grandparent;
        }
        current
    }

    fn merge(&mut self, left: Id<Set>, right: Id<Set>) {
        let left_rank = self.sets[left].rank;
        let right_rank = self.sets[right].rank;
        if left_rank > right_rank {
            self.sets[right].parent = left;
        } else {
            self.sets[left].parent = right;
            if left_rank == right_rank {
                self.sets[right].rank += 1;
            }
        }
    }
}

#[derive(Default)]
pub(super) struct EUF {
    eq: Vec<(Lit, Id<Trm>, Id<Trm>)>,
    neq: Vec<(Lit, Id<Trm>, Id<Trm>)>,
    disjoint: Disjoint,
}

impl EUF {
    pub(super) fn restart(&mut self) {
        self.disjoint.clear();
        self.eq.clear();
        self.neq.clear();
    }

    pub(super) fn max_term(&mut self, id: Id<Trm>) {
        self.disjoint.max_term(id);
    }

    pub(super) fn assert_eq(
        &mut self,
        lit: Lit,
        left: Id<Trm>,
        right: Id<Trm>,
    ) {
        if left == right {
            return;
        }
        self.eq.push((lit, left, right));
        self.merge_equal(left, right);
    }

    pub(super) fn assert_neq(
        &mut self,
        lit: Lit,
        left: Id<Trm>,
        right: Id<Trm>,
    ) {
        self.neq.push((lit, left, right));
    }

    pub(super) fn check(&mut self, literals: &mut Block<Lit>) -> bool {
        if let Some((left, right)) = self.find_conflict(literals) {
            for candidate in 0..self.eq.len() {
                self.disjoint.clear();
                for i in 0..self.eq.len() {
                    if i == candidate {
                        continue;
                    }
                    let (_, left, right) = self.eq[i];
                    self.merge_equal(left, right);
                    let lset = self.disjoint.find(left);
                    let rset = self.disjoint.find(right);
                    if lset == rset {
                        break;
                    }
                }
                let lset = self.disjoint.find(left);
                let rset = self.disjoint.find(right);
                if lset != rset {
                    let mut lit = self.eq[candidate].0;
                    lit.pol = !lit.pol;
                    literals.push(lit);
                }
            }
            return false;
        }
        true
    }

    fn merge_equal(&mut self, left: Id<Trm>, right: Id<Trm>) {
        let left = self.disjoint.find(left);
        let right = self.disjoint.find(right);
        self.disjoint.merge(left, right);
    }

    fn find_conflict(
        &mut self,
        literals: &mut Block<Lit>,
    ) -> Option<(Id<Trm>, Id<Trm>)> {
        for (mut lit, left, right) in self.neq.iter().copied() {
            let lset = self.disjoint.find(left);
            let rset = self.disjoint.find(right);
            if lset == rset {
                lit.pol = !lit.pol;
                literals.push(lit);
                return Some((left, right));
            }
        }
        None
    }
}
