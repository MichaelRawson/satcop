use crate::binding::Bindings;
use crate::block::{Block, Id, Off};
use crate::sat;
use crate::syntax::{Clause, Literal, Matrix, Term, Var};
use rand::rngs::SmallRng;
use rand::seq::SliceRandom;
use rand::SeedableRng;

#[derive(Debug, Clone, Copy)]
struct Constraint {
    left: Off<Term>,
    right: Off<Term>,
}

pub(crate) struct Search<'matrix> {
    matrix: &'matrix mut Matrix,
    rng: SmallRng,
    solver: sat::Solver,
    bindings: Bindings,
    path: Block<Off<Literal>>,
    clauses: Vec<Off<Clause>>,
    offset: u32,
    depth_limit: u32,
}

impl<'matrix> Search<'matrix> {
    pub(crate) fn new(matrix: &'matrix mut Matrix) -> Self {
        let rng = SmallRng::seed_from_u64(0);
        let solver = sat::Solver::default();
        let bindings = Bindings::default();
        let path = Block::default();
        let clauses = vec![];
        let offset = 0;
        let depth_limit = 0;
        Self {
            matrix,
            rng,
            solver,
            bindings,
            path,
            clauses,
            offset,
            depth_limit,
        }
    }

    pub(crate) fn go(&mut self) -> bool {
        if self.matrix.start.range().is_empty() {
            return false;
        }
        loop {
            for start in self.matrix.start.range() {
                if self.start(self.matrix.start[start]) {
                    return true;
                }
            }
            if !self.solver.solve() {
                return true;
            }
            if !self.solver.model_changed() {
                self.depth_limit += 1;
            }
        }
    }

    fn start(&mut self, id: Id<Clause>) -> bool {
        let cls = self.matrix.clauses[id];
        self.clauses.push(Off::new(id, 0));
        self.bindings.ensure_capacity(Var(cls.vars));
        self.solver
            .assert(self.matrix, &self.bindings, &self.clauses);
        self.offset = cls.vars;
        let mut promises = cls.literals.into_iter().collect::<Vec<_>>();
        promises.shuffle(&mut self.rng);
        for id in promises {
            let lit = Off::new(id, 0);
            if !self.prove(lit) {
                self.bindings.clear();
                self.clauses.clear();
                return false;
            }
        }
        true
    }

    fn prove(&mut self, goal: Off<Literal>) -> bool {
        if self
            .solver
            .is_assigned_false(self.matrix, &self.bindings, goal)
        {
            return true;
        }

        let offset = goal.offset;
        let Literal { pol, atom } = self.matrix.literals[goal.id];
        let sym = self.matrix.terms[atom].as_sym();
        let atom = Off::new(atom, offset);

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
            let ppol = self.matrix.literals[plit.id].pol;
            let patom =
                Off::new(self.matrix.literals[plit.id].atom, plit.offset);
            let psym = self.matrix.terms[patom.id].as_sym();

            if sym != psym {
                continue;
            }
            if pol == ppol {
                if self.bindings.equal(
                    &self.matrix.symbols,
                    &self.matrix.terms,
                    atom,
                    patom,
                ) {
                    return false;
                }
            } else {
                if self.bindings.unify(
                    &self.matrix.symbols,
                    &self.matrix.terms,
                    atom,
                    patom,
                ) && self.check_constraints()
                {
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

        if self.depth_limit <= self.path.len().index {
            return false;
        }

        // extensions
        let save_clauses = self.clauses.len();
        let save_offset = self.offset;
        self.path.push(goal);
        let mut alternatives =
            self.matrix.index[sym].pol[!pol as usize].clone();
        alternatives.shuffle(&mut self.rng);

        /*
        for pid in self.path.range() {
            self.matrix.print_literal(&self.bindings, self.path[pid]);
            println!()
        }
        println!("-------------------");
        */
        'extensions: for pos in alternatives {
            let cls = self.matrix.clauses[pos.cls];
            self.bindings.ensure_capacity(Var(self.offset + cls.vars));
            if self.bindings.unify(
                &self.matrix.symbols,
                &self.matrix.terms,
                atom,
                Off::new(self.matrix.literals[pos.lit].atom, self.offset),
            ) {
                self.clauses.push(Off::new(pos.cls, self.offset));
                self.offset += cls.vars;
                if !self.check_constraints() {
                    self.offset = save_offset;
                    self.clauses.truncate(save_clauses);
                    self.bindings.undo_to_mark(save_bindings);
                    continue 'extensions;
                }
                self.solver
                    .assert(self.matrix, &self.bindings, &self.clauses);
                let mut promises = cls
                    .literals
                    .into_iter()
                    .filter(|id| *id != pos.lit)
                    .collect::<Vec<_>>();
                promises.shuffle(&mut self.rng);
                for id in promises {
                    let lit = Off::new(id, save_offset);
                    if !self.prove(lit) {
                        self.offset = save_offset;
                        self.clauses.truncate(save_clauses);
                        self.bindings.undo_to_mark(save_bindings);
                        continue 'extensions;
                    }
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

    fn check_constraints(&mut self) -> bool {
        for cls in &self.clauses {
            let diseqs = self.matrix.clauses[cls.id].disequations;
            for diseq in &self.matrix.disequations[diseqs] {
                if self.bindings.equal(
                    &self.matrix.symbols,
                    &self.matrix.terms,
                    Off::new(diseq.left, cls.offset),
                    Off::new(diseq.right, cls.offset),
                ) {
                    return false;
                }
            }
        }
        true
    }
}
