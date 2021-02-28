use crate::binding::Bindings;
use crate::block::{Block, Id, Off};
use crate::matrix::Matrix;
use crate::sat;
use crate::syntax::{Cls, Lit, Trm, Var};
use rand::rngs::SmallRng;
use rand::seq::SliceRandom;
use rand::SeedableRng;

#[derive(Debug, Clone, Copy)]
struct Constraint {
    left: Off<Trm>,
    right: Off<Trm>,
}

pub(crate) struct Search<'matrix> {
    matrix: &'matrix Matrix,
    rng: SmallRng,
    solver: sat::Solver,
    bindings: Bindings,
    path: Block<Off<Lit>>,
    todo: Block<Id<Lit>>,
    clauses: Vec<Off<Cls>>,
    offset: u32,
    asserted_new_clause: bool,
}

impl<'matrix> Search<'matrix> {
    pub(crate) fn new(matrix: &'matrix Matrix) -> Self {
        let rng = SmallRng::seed_from_u64(0);
        let solver = sat::Solver::default();
        let bindings = Bindings::default();
        let path = Block::default();
        let todo = Block::default();
        let clauses = vec![];
        let offset = 0;
        let asserted_new_clause = false;
        Self {
            matrix,
            rng,
            solver,
            bindings,
            path,
            todo,
            clauses,
            offset,
            asserted_new_clause,
        }
    }

    pub(crate) fn go(&mut self) -> bool {
        let mut limit = 0;
        loop {
            self.asserted_new_clause = false;
            if let Some(start) = self.matrix.start[self.matrix.start.range()]
                .choose(&mut self.rng)
                .copied()
            {
                if self.start(start, limit) {
                    return true;
                }
            } else {
                return false;
            };
            if self.asserted_new_clause {
                if !self.solver.solve() {
                    return true;
                }
            } else {
                limit += 1;
            }
        }
    }

    fn start(&mut self, id: Id<Cls>, limit: u32) -> bool {
        let cls = self.matrix.clauses[id];
        self.clauses.push(Off::new(id, 0));
        self.bindings.ensure_capacity(Var(cls.vars));
        self.assert_all_clauses();
        self.offset = cls.vars;
        assert!(self.todo.len() == Id::new(0));
        for lit in cls.lits {
            self.todo.push(lit);
        }
        let todo = self.todo.range();
        self.todo[todo].shuffle(&mut self.rng);
        for todo in todo {
            let lit = Off::new(self.todo[todo], 0);
            if !self.prove(lit, limit) {
                self.bindings.clear();
                self.clauses.clear();
                self.todo.clear();
                return false;
            }
        }
        self.todo.clear();
        true
    }

    fn prove(&mut self, goal: Off<Lit>, limit: u32) -> bool {
        let offset = goal.offset;
        let Lit { pol, atom } = self.matrix.lits[goal.id];
        let sym = self.matrix.terms[atom].as_sym();
        let atom = Off::new(atom, offset);

        for cls in &self.clauses {
            let diseqs = self.matrix.clauses[cls.id].diseqs;
            for diseq in &self.matrix.diseqs[diseqs] {
                if self.bindings.equal(
                    &self.matrix.syms,
                    &self.matrix.terms,
                    Off::new(diseq.left, cls.offset),
                    Off::new(diseq.right, cls.offset),
                ) {
                    return false;
                }
            }
        }
        let save_bindings = self.bindings.mark();
        // reductions
        for pid in self.path.range() {
            let plit = self.path[pid];
            let ppol = self.matrix.lits[plit.id].pol;
            let patom = Off::new(self.matrix.lits[plit.id].atom, plit.offset);
            let psym = self.matrix.terms[patom.id].as_sym();

            if sym != psym {
                continue;
            }
            if pol == ppol {
                if self.bindings.equal(
                    &self.matrix.syms,
                    &self.matrix.terms,
                    atom,
                    patom,
                ) {
                    return false;
                }
            } else {
                if self.bindings.unify(
                    &self.matrix.syms,
                    &self.matrix.terms,
                    atom,
                    patom,
                ) {
                    self.assert_all_clauses();
                    return true;
                }
                self.bindings.undo_to_mark(save_bindings);
            }
        }

        let save_clauses = self.clauses.len();
        let save_offset = self.offset;
        // extensions
        self.path.push(goal);
        let mut alternatives =
            self.matrix.index[sym].pol[!pol as usize].clone();
        alternatives.shuffle(&mut self.rng);
        'extensions: for pos in alternatives {
            let cls = &self.matrix.clauses[pos.cls];
            let mut clen = cls.lits.len();
            if clen > limit {
                continue;
            }
            self.bindings.ensure_capacity(Var(self.offset + cls.vars));
            if self.bindings.unify(
                &self.matrix.syms,
                &self.matrix.terms,
                atom,
                Off::new(self.matrix.lits[pos.lit].atom, self.offset),
            ) {
                self.clauses.push(Off::new(pos.cls, self.offset));
                self.assert_all_clauses();
                self.offset += cls.vars;
                let mut promises = cls
                    .lits
                    .into_iter()
                    .filter(|id| *id != pos.lit)
                    .collect::<Vec<_>>();
                promises.shuffle(&mut self.rng);
                for id in promises {
                    let lit = Off::new(id, save_offset);
                    if !self.prove(lit, limit - clen) {
                        self.offset = save_offset;
                        self.clauses.truncate(save_clauses);
                        self.bindings.undo_to_mark(save_bindings);
                        continue 'extensions;
                    }
                    clen -= 1;
                }
                self.path.pop();
                return true;
            }
            self.bindings.undo_to_mark(save_bindings);
        }
        self.offset = save_offset;
        self.path.pop();
        false
    }

    fn assert_all_clauses(&mut self) {
        for clause in &self.clauses {
            self.asserted_new_clause |=
                self.solver.assert(self.matrix, &self.bindings, *clause);
        }
    }
}
