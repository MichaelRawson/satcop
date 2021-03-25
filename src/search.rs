use crate::binding::Bindings;
use crate::block::{Block, Id, Off};
use crate::lpo;
use crate::options::Options;
use crate::sat;
use crate::statistics::Statistics;
use crate::syntax::{Clause, Literal, Matrix};
use rand::rngs::SmallRng;
use rand::seq::SliceRandom;
use rand::SeedableRng;
use std::io::Write;

#[derive(Debug, Clone, Copy)]
struct Path(Off<Literal>);

pub(crate) struct Search<'matrix> {
    matrix: &'matrix mut Matrix,
    statistics: Statistics,
    rng: SmallRng,
    solver: sat::Solver,
    bindings: Bindings,
    path: Block<Path>,
    clauses: Vec<Off<Clause>>,
    depth_limit: Id<Path>,
    offset: u32,
}

impl<'matrix> Search<'matrix> {
    pub(crate) fn new(matrix: &'matrix mut Matrix) -> Self {
        let statistics = Statistics {
            symbols: matrix.symbols.len().as_u32() - 2,
            clauses: matrix.clauses.len().as_u32(),
            start_clauses: matrix.start.range().len(),
            ..Default::default()
        };
        let rng = SmallRng::seed_from_u64(0);
        let solver = sat::Solver::default();
        let bindings = Bindings::default();
        let path = Block::default();
        let clauses = vec![];
        let depth_limit = Id::new(0);
        let offset = 0;
        Self {
            matrix,
            statistics,
            rng,
            solver,
            bindings,
            path,
            clauses,
            depth_limit,
            offset,
        }
    }

    pub(crate) fn go(&mut self, options: &Options) -> bool {
        let start_clauses = self.matrix.start.range();
        if start_clauses.is_empty() {
            return false;
        }
        loop {
            self.statistics.iterative_deepening_steps += 1;
            for start in start_clauses {
                self.start(options, self.matrix.start[start]);
            }
            if self.solver.seen_new_clause() {
                if !self.solver.solve(&mut self.statistics) {
                    return true;
                }
            } else {
                self.depth_limit.increment();
                self.statistics.maximum_path_limit = self.depth_limit.as_u32();
            }
        }
    }

    pub(crate) fn print_statistics<W: Write>(
        &self,
        w: &mut W,
    ) -> anyhow::Result<()> {
        self.statistics.print(w)
    }

    pub(crate) fn print_proof<W: Write>(
        &self,
        w: &mut W,
    ) -> anyhow::Result<()> {
        self.solver.print_proof(w, self.matrix)
    }

    fn start(&mut self, options: &Options, id: Id<Clause>) -> bool {
        let cls = self.matrix.clauses[id];
        self.clauses.push(Off::new(id, 0));
        self.bindings.ensure_capacity(cls.vars);
        self.solver.assert(
            &mut self.statistics,
            options,
            self.matrix,
            &self.bindings,
            &self.clauses,
        );
        self.offset = cls.vars.as_u32();
        let mut promises = cls.literals.into_iter().collect::<Vec<_>>();
        promises.shuffle(&mut self.rng);
        for id in promises {
            let lit = Off::new(id, 0);
            if !self.prove(options, lit) {
                self.bindings.clear();
                self.clauses.clear();
                return false;
            }
        }
        self.bindings.clear();
        self.clauses.clear();
        true
    }

    fn prove(&mut self, options: &Options, goal: Off<Literal>) -> bool {
        self.statistics.literal_attempts += 1;
        let offset = goal.offset;
        let Literal { pol, atom } = self.matrix.literals[goal.id];
        let sym = self.matrix.terms[atom].as_sym();
        let atom = Off::new(atom, offset);

        // regularity
        for pid in self.path.range() {
            let Path(plit) = self.path[pid];
            let ppol = self.matrix.literals[plit.id].pol;
            let patom =
                Off::new(self.matrix.literals[plit.id].atom, plit.offset);
            let psym = self.matrix.terms[patom.id].as_sym();
            if sym != psym || pol != ppol {
                continue;
            }
            if self.bindings.equal(
                &self.matrix.symbols,
                &self.matrix.terms,
                atom,
                patom,
            ) {
                self.statistics.regularity_failures += 1;
                return false;
            }
        }

        // model lemmata
        if self
            .solver
            .is_assigned_false(self.matrix, &self.bindings, goal)
        {
            self.statistics.goals_assigned_false += 1;
            return true;
        }
        for id in self.path.range() {
            let Path(plit) = self.path[id];
            if self
                .solver
                .is_assigned_false(self.matrix, &self.bindings, plit)
            {
                self.statistics.paths_assigned_false += 1;
                return true;
            }
        }

        let save_bindings = self.bindings.mark();
        // reductions
        for pid in self.path.range() {
            let Path(plit) = self.path[pid];
            let ppol = self.matrix.literals[plit.id].pol;
            let patom =
                Off::new(self.matrix.literals[plit.id].atom, plit.offset);
            let psym = self.matrix.terms[patom.id].as_sym();
            if sym != psym || pol == ppol {
                continue;
            }
            if self.bindings.unify(
                &self.matrix.symbols,
                &self.matrix.terms,
                atom,
                patom,
            ) && self.check_constraints()
            {
                self.statistics.reductions += 1;
                self.solver.assert(
                    &mut self.statistics,
                    options,
                    self.matrix,
                    &self.bindings,
                    &self.clauses,
                );
                return true;
            }
            self.bindings.undo_to_mark(save_bindings);
        }

        // depth limit
        if self.depth_limit <= self.path.len() {
            self.statistics.depth_failures += 1;
            return false;
        }

        // extensions
        let save_clauses = self.clauses.len();
        let save_offset = self.offset;
        self.path.push(Path(goal));
        let mut alternatives = self.matrix.index[sym][!pol as usize].clone();
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
            self.bindings.ensure_capacity(cls.vars.offset(self.offset));
            if self.bindings.unify(
                &self.matrix.symbols,
                &self.matrix.terms,
                atom,
                Off::new(self.matrix.literals[pos.lit].atom, self.offset),
            ) {
                self.statistics.extensions += 1;
                self.clauses.push(Off::new(pos.cls, self.offset));
                self.offset += cls.vars.as_u32();
                if !self.check_constraints() {
                    self.offset = save_offset;
                    self.clauses.truncate(save_clauses);
                    self.bindings.undo_to_mark(save_bindings);
                    continue 'extensions;
                }
                self.solver.assert(
                    &mut self.statistics,
                    options,
                    self.matrix,
                    &self.bindings,
                    &self.clauses,
                );
                let mut promises = cls
                    .literals
                    .into_iter()
                    .filter(|id| *id != pos.lit)
                    .collect::<Vec<_>>();
                promises.shuffle(&mut self.rng);
                for id in promises {
                    let lit = Off::new(id, save_offset);
                    if !self.prove(options, lit) {
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
                    self.statistics.tautology_failures += 1;
                    return false;
                }
            }
            let orderings = self.matrix.clauses[cls.id].orderings;
            for ordering in &self.matrix.orderings[orderings] {
                use std::cmp::Ordering::Less;
                let comparison = lpo::cmp(
                    &self.matrix.symbols,
                    &self.matrix.terms,
                    &self.bindings,
                    Off::new(ordering.left, cls.offset),
                    Off::new(ordering.right, cls.offset),
                );
                /*
                self.matrix.print_term(
                    &self.bindings,
                    Off::new(ordering.left, cls.offset),
                );
                print!("\t");
                self.matrix.print_term(
                    &self.bindings,
                    Off::new(ordering.right, cls.offset),
                );
                println!("\t{:?}", comparison);
                */
                if matches!(comparison, Some(Less)) {
                    self.statistics.ordering_failures += 1;
                    return false;
                }
            }
        }
        true
    }
}
