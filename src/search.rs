use crate::binding::Bindings;
use crate::block::{Block, Id, Off};
use crate::ground::Ground;
use crate::options::Options;
use crate::rng::DefaultRng;
use crate::statistics;
use crate::syntax::{Clause, Literal, Matrix, Term};
use crate::tstp;
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
    new_clause: bool,
}

impl Search {
    pub(crate) fn seed(&mut self, seed: u64) {
        self.rng.seed(seed);
        self.ground.seed(seed);
    }

    pub(crate) fn print_proof<W: Write>(
        &self,
        w: &mut W,
        options: &Options,
        matrix: &Matrix,
    ) -> anyhow::Result<()> {
        tstp::print_proof(w, &self.ground, options, matrix)
    }

    pub(crate) fn go(&mut self, matrix: &Matrix) {
        self.depth_limit.increment();

        for id in &matrix.start {
            self.bindings.resize(matrix.clauses[*id].vars);
            let cls = Off::new(*id, 0);
            self.ground.insert_clause(matrix, &self.bindings, cls);
        }
        if self.ground.unsat() {
            return;
        }

        loop {
            statistics::ITERATIVE_DEEPENING_STEPS.inc();
            for start in &matrix.start {
                self.start(matrix, *start);
            }
            if self.ground.unsat() {
                return;
            }
            if std::mem::take(&mut self.new_clause) {
                statistics::MAXIMUM_PATH_LIMIT.max(self.depth_limit.as_u32());
            } else {
                self.depth_limit.increment();
            }
        }
    }

    fn start(&mut self, matrix: &Matrix, id: Id<Clause>) -> bool {
        let cls = matrix.clauses[id];
        self.clauses.push(Off::new(id, 0));
        self.bindings.resize(cls.vars);
        self.offset = cls.vars.as_u32();
        let mut promises = cls.literals.into_iter().collect::<Vec<_>>();
        self.rng.shuffle(&mut promises);
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
        let Literal { pol, atom } = matrix.literals[goal.id];
        let sym = matrix.terms[atom].as_sym();
        let atom = goal.commute(|_| atom);

        // regularity
        for pid in self.path.range() {
            let Path(plit) = self.path[pid];
            let ppol = matrix.literals[plit.id].pol;
            let patom = plit.commute(|id| matrix.literals[id].atom);
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
            let patom = plit.commute(|id| matrix.literals[id].atom);
            let psym = matrix.terms[patom.id].as_sym();
            if sym != psym || pol == ppol {
                continue;
            }
            if self.unify(matrix, atom, patom) {
                statistics::REDUCTIONS.inc();
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
        self.rng.shuffle(&mut alternatives);

        'extensions: for pos in alternatives {
            let cls = matrix.clauses[pos.cls];
            self.bindings.resize(cls.vars.offset(self.offset));
            self.clauses.push(Off::new(pos.cls, self.offset));
            if self.unify(
                matrix,
                atom,
                Off::new(matrix.literals[pos.lit].atom, self.offset),
            ) {
                statistics::EXTENSIONS.inc();
                self.offset += cls.vars.as_u32();
                let mut promises = cls
                    .literals
                    .into_iter()
                    .filter(|id| *id != pos.lit)
                    .collect::<Vec<_>>();
                self.rng.shuffle(&mut promises);
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
            self.clauses.pop();
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
                    cls.commute(|_| diseq.left),
                    cls.commute(|_| diseq.right),
                ) {
                    statistics::TAUTOLOGY_FAILURES.inc();
                    return false;
                }
            }
        }
        for clause in &self.clauses {
            if !self.ground.contains_clause(matrix, &self.bindings, *clause) {
                self.new_clause = true;
                self.ground.insert_clause(matrix, &self.bindings, *clause);
            }
        }
        true
    }
}
