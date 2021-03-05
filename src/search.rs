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
    matrix: &'matrix mut Matrix,
    rng: SmallRng,
    solver: sat::Solver,
    bindings: Bindings,
    path: Block<Off<Lit>>,
    clauses: Vec<Off<Cls>>,
    offset: u32,
}

impl<'matrix> Search<'matrix> {
    pub(crate) fn new(matrix: &'matrix mut Matrix) -> Self {
        let rng = SmallRng::seed_from_u64(0);
        let solver = sat::Solver::new(matrix);
        let bindings = Bindings::default();
        let path = Block::default();
        let clauses = vec![];
        let offset = 0;
        Self {
            matrix,
            rng,
            solver,
            bindings,
            path,
            clauses,
            offset,
        }
    }

    pub(crate) fn go(&mut self) -> bool {
        let mut limit = 0;
        if self.matrix.start.range().is_empty() {
            return false;
        }
        loop {
            for start in self.matrix.start.range() {
                self.start(self.matrix.start[start], limit);
            }
            if !self.solver.solve() {
                return true;
            }
            if !self.solver.model_changed() {
                limit += 1;
            }
        }
    }

    fn start(&mut self, id: Id<Cls>, limit: u32) -> bool {
        let cls = self.matrix.clauses[id];
        self.clauses.push(Off::new(id, 0));
        self.bindings.ensure_capacity(Var(cls.vars));
        self.solver
            .assert(self.matrix, &self.bindings, &self.clauses);
        self.offset = cls.vars;
        let mut promises = cls.lits.into_iter().collect::<Vec<_>>();
        promises.shuffle(&mut self.rng);
        for id in promises {
            let lit = Off::new(id, 0);
            if !self.prove(lit, limit) {
                self.bindings.clear();
                self.clauses.clear();
                return false;
            }
        }
        true
    }

    fn prove(&mut self, goal: Off<Lit>, limit: u32) -> bool {
        if self
            .solver
            .is_assigned_false(self.matrix, &self.bindings, goal)
        {
            return true;
        }

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
            if self
                .solver
                .is_assigned_false(self.matrix, &self.bindings, plit)
            {
                return true;
            }
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
                    self.solver.assert(
                        self.matrix,
                        &self.bindings,
                        &self.clauses,
                    );
                    return true;
                }
                self.bindings.undo_to_mark(save_bindings);
            }
        }

        if limit == 0 {
            return false;
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
                self.solver
                    .assert(self.matrix, &self.bindings, &self.clauses);
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
}
