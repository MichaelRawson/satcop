use crate::binding::Bindings;
use crate::block::{Block, Id, Off};
use crate::matrix::Matrix;
use crate::smt;
use crate::syntax::{Cls, Lit, Trm, Var};

#[derive(Debug)]
struct Path {
    lit: Off<Lit>,
    parent: Id<Path>,
}

#[derive(Debug)]
struct Goal {
    lit: Off<Lit>,
    path: Id<Path>,
}

#[derive(Debug, Clone, Copy)]
struct Constraint {
    left: Off<Trm>,
    right: Off<Trm>,
}

pub(crate) struct Search<'matrix> {
    matrix: &'matrix Matrix,
    solver: smt::Solver,
    asserted_new_clause: bool,
    bindings: Bindings,
    path: Block<Path>,
    todo: Vec<Goal>,
    constraints: Vec<Constraint>,
    clauses: Vec<Off<Cls>>,
    offset: u32,
    limit: u32,
    steps: u64,
}

impl<'matrix> Search<'matrix> {
    pub(crate) fn new(matrix: &'matrix Matrix) -> Self {
        let solver = smt::Solver::default();
        let asserted_new_clause = false;
        let bindings = Bindings::default();
        let mut path = Block::default();
        path.push(Path {
            lit: Off::new(Id::default(), 0),
            parent: Id::default(),
        });
        let todo = vec![];
        let constraints = vec![];
        let clauses = vec![];
        let offset = 0;
        let limit = 0;
        let steps = 0;
        Self {
            matrix,
            solver,
            asserted_new_clause,
            bindings,
            path,
            todo,
            constraints,
            clauses,
            offset,
            limit,
            steps,
        }
    }

    pub(crate) fn go(&mut self) {
        self.limit = 0;
        loop {
            self.asserted_new_clause = false;
            for start in &self.matrix.start {
                self.start(*start);
            }
            if !self.asserted_new_clause {
                self.limit += 1;
            }
        }
    }

    fn start(&mut self, id: Id<Cls>) {
        let cls = &self.matrix.clauses[id];
        let path = Id::default();
        for id in cls.lits {
            self.todo.push(Goal {
                lit: Off::new(id, self.offset),
                path,
            });
        }
        self.clauses.push(Off::new(id, self.offset));
        self.bindings.ensure_capacity(Var(self.offset + cls.vars));
        self.offset = cls.vars;
        self.prove();
        self.offset = 0;
        self.clauses.clear();
        self.todo.clear();
    }

    fn prove(&mut self) {
        self.steps += 1;
        for constraint in &self.constraints {
            if self.bindings.args_equal(
                &self.matrix.syms,
                &self.matrix.terms,
                constraint.left,
                constraint.right,
            ) {
                return;
            }
        }
        let mut new_clause = false;
        for clause in &self.clauses {
            new_clause |=
                self.solver.assert(self.matrix, &self.bindings, *clause);
        }
        self.asserted_new_clause |= new_clause;
        if new_clause && !self.solver.solve() {
            println!("% SZS status Unsatisfiable");
            std::process::exit(0);
        }

        let goal = if let Some(goal) = self.todo.pop() {
            goal
        } else {
            return;
        };

        // check the goal and everything on the path is (assigned) true
        if self
            .solver
            .assigned_false(self.matrix, &self.bindings, goal.lit)
        {
            self.prove();
            self.todo.push(goal);
            return;
        }
        let mut path = goal.path;
        while path.index != 0 {
            if self.solver.assigned_false(
                self.matrix,
                &self.bindings,
                self.path[path].lit,
            ) {
                self.prove();
                self.todo.push(goal);
                return;
            }
            path = self.path[path].parent;
        }

        let undo_regularity = self.constraints.len();
        let undo_bindings = self.bindings.mark();
        let offset = goal.lit.offset;
        let Lit { pol, atom } = self.matrix.lits[goal.lit.id];
        let sym = self.matrix.terms[atom].as_sym();
        let left = Off::new(atom, offset);

        // reductions
        let mut path_len = 0;
        let mut path = goal.path;
        while path.index != 0 {
            let path_data = self.path[path].lit;
            let path_lit = self.matrix.lits[path_data.id];
            let path_sym = self.matrix.terms[path_lit.atom].as_sym();
            path = self.path[path].parent;
            path_len += 1;
            if path_sym != sym {
                continue;
            }

            let right = Off::new(path_lit.atom, path_data.offset);
            if path_lit.pol != pol {
                if self.bindings.args_unify(
                    &self.matrix.syms,
                    &self.matrix.terms,
                    sym,
                    left,
                    right,
                ) {
                    self.prove();
                }
                self.bindings.undo_to_mark(undo_bindings);
            }
            self.constraints.push(Constraint { left, right });
        }

        // extensions
        if path_len < self.limit {
            let undo_todo = self.todo.len();
            let path = self.path.push(Path {
                lit: goal.lit,
                parent: goal.path,
            });
            for pos in &self.matrix.index[sym].pol[!pol as usize] {
                let cls = self.matrix.clauses[pos.cls];
                self.bindings.ensure_capacity(Var(self.offset + cls.vars));
                if self.bindings.args_unify(
                    &self.matrix.syms,
                    &self.matrix.terms,
                    sym,
                    Off::new(atom, offset),
                    Off::new(self.matrix.lits[pos.lit].atom, self.offset),
                ) {
                    self.clauses.push(Off::new(pos.cls, self.offset));
                    for id in cls.lits {
                        if id != pos.lit {
                            let lit = Off::new(id, self.offset);
                            self.todo.push(Goal { path, lit });
                        }
                    }
                    self.offset += cls.vars;
                    self.prove();
                    self.offset -= cls.vars;
                    self.todo.truncate(undo_todo);
                    self.clauses.pop();
                }
                self.bindings.undo_to_mark(undo_bindings);
            }
            self.path.pop();
        }

        self.constraints.truncate(undo_regularity);
        self.todo.push(goal);
    }
}
