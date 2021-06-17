use crate::binding::Bindings;
use crate::block::{Block, Id, Off};
use crate::ground::Ground;
use crate::options::Options;
use crate::rng::DefaultRng;
use crate::statistics;
use crate::syntax::{Clause, Literal, Matrix, Term};
use rand::seq::SliceRandom;
use std::io::Write;

#[derive(Debug, Clone, Copy)]
struct Path(Off<Literal>);

#[derive(Default)]
pub(crate) struct Search {
    rng: DefaultRng,
    ground: Ground,
    bindings: Bindings,
    path: Block<Path>,
    clauses: Vec<Off<Clause>>,
    depth_limit: Id<Path>,
    offset: u32,
}

impl Search {
    pub(crate) fn seed(&mut self, seed: u64) {
        self.rng.seed(seed);
        self.ground.seed(seed);
    }

    pub(crate) fn go(&mut self, options: &Options, matrix: &Matrix) -> bool {
        if matrix.start.is_empty() {
            return false;
        }
        if options.proof {
            self.ground.record_proof();
        }
        self.depth_limit.increment();

        for id in &matrix.start {
            let cls = matrix.clauses[*id];
            self.clauses.push(Off::new(*id, 0));
            self.bindings.ensure_capacity(cls.vars);
            self.ground.assert(matrix, &self.bindings, &self.clauses);
            self.clauses.clear();
        }
        if self.ground.unsat() {
            return true;
        }
        self.ground.seen_new_clause();

        loop {
            statistics::ITERATIVE_DEEPENING_STEPS.inc();
            for start in &matrix.start {
                self.start(matrix, *start);
            }
            if self.ground.unsat() {
                return true;
            }
            if !self.ground.seen_new_clause() {
                self.depth_limit.increment();
                statistics::MAXIMUM_PATH_LIMIT.max(self.depth_limit.as_u32());
            }
        }
    }

    pub(crate) fn print_proof<W: Write>(
        &self,
        w: &mut W,
        matrix: &Matrix,
    ) -> anyhow::Result<()> {
        self.ground.print_proof(w, matrix)
    }

    fn start(&mut self, matrix: &Matrix, id: Id<Clause>) -> bool {
        let cls = matrix.clauses[id];
        self.clauses.push(Off::new(id, 0));
        self.bindings.ensure_capacity(cls.vars);
        self.offset = cls.vars.as_u32();
        let mut promises = cls.literals.into_iter().collect::<Vec<_>>();
        promises.shuffle(self.rng.get());
        for id in promises {
            let lit = Off::new(id, 0);
            if !self.prove(matrix, lit) {
                self.bindings.clear();
                self.clauses.clear();
                return false;
            }
        }
        self.bindings.clear();
        self.clauses.clear();
        true
    }

    fn prove(&mut self, matrix: &Matrix, goal: Off<Literal>) -> bool {
        if self.ground.unsat() {
            return true;
        }
        statistics::LITERAL_ATTEMPTS.inc();
        let offset = goal.offset;
        let Literal { pol, atom } = matrix.literals[goal.id];
        let sym = matrix.terms[atom].as_sym();
        let atom = Off::new(atom, offset);

        // regularity
        for pid in self.path.range() {
            let Path(plit) = self.path[pid];
            let ppol = matrix.literals[plit.id].pol;
            let patom = Off::new(matrix.literals[plit.id].atom, plit.offset);
            let psym = matrix.terms[patom.id].as_sym();
            if sym != psym || pol != ppol {
                continue;
            }
            if self
                .bindings
                .equal(&matrix.symbols, &matrix.terms, atom, patom)
            {
                statistics::REGULARITY_FAILURES.inc();
                return false;
            }
        }

        let save_bindings = self.bindings.mark();
        // reductions
        for pid in self.path.range() {
            let Path(plit) = self.path[pid];
            let ppol = matrix.literals[plit.id].pol;
            let patom = Off::new(matrix.literals[plit.id].atom, plit.offset);
            let psym = matrix.terms[patom.id].as_sym();
            if sym != psym || pol == ppol {
                continue;
            }
            if self.unify(matrix, atom, patom) {
                statistics::REDUCTIONS.inc();
                self.ground.assert(matrix, &self.bindings, &self.clauses);
                return true;
            }
            self.bindings.undo_to_mark(save_bindings);
        }

        // depth limit
        if self.depth_limit <= self.path.len() {
            statistics::DEPTH_FAILURES.inc();
            return false;
        }

        // extensions
        let save_clauses = self.clauses.len();
        let save_offset = self.offset;
        self.path.push(Path(goal));
        let mut alternatives = matrix.index[sym][!pol as usize].clone();
        alternatives.shuffle(self.rng.get());

        'extensions: for pos in alternatives {
            let cls = matrix.clauses[pos.cls];
            self.bindings.ensure_capacity(cls.vars.offset(self.offset));
            if self.unify(
                matrix,
                atom,
                Off::new(matrix.literals[pos.lit].atom, self.offset),
            ) {
                statistics::EXTENSIONS.inc();
                self.clauses.push(Off::new(pos.cls, self.offset));
                self.offset += cls.vars.as_u32();
                self.ground.assert(matrix, &self.bindings, &self.clauses);
                let mut promises = cls
                    .literals
                    .into_iter()
                    .filter(|id| *id != pos.lit)
                    .collect::<Vec<_>>();
                promises.shuffle(self.rng.get());
                while let Some(index) = promises.iter().position(|id| {
                    self.ground.is_assigned_true(
                        matrix,
                        &self.bindings,
                        Off::new(*id, save_offset),
                    )
                }) {
                    let id = promises.swap_remove(index);
                    let lit = Off::new(id, save_offset);
                    if !self.prove(matrix, lit) {
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

    fn unify(
        &mut self,
        matrix: &Matrix,
        left: Off<Term>,
        right: Off<Term>,
    ) -> bool {
        if !self
            .bindings
            .unify(&matrix.symbols, &matrix.terms, left, right)
        {
            return false;
        }
        for cls in &self.clauses {
            let diseqs = matrix.clauses[cls.id].disequations;
            for diseq in &matrix.disequations[diseqs] {
                if self.bindings.equal(
                    &matrix.symbols,
                    &matrix.terms,
                    Off::new(diseq.left, cls.offset),
                    Off::new(diseq.right, cls.offset),
                ) {
                    statistics::TAUTOLOGY_FAILURES.inc();
                    return false;
                }
            }
        }
        true
    }
}
