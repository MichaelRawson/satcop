use crate::binding::Bindings;
use crate::block::{Block, Id, Off};
use crate::matrix::Matrix;
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
    bindings: Bindings,
    path: Block<Path>,
    todo: Vec<Goal>,
    constraints: Vec<Constraint>,
    offset: u32,
    limit: u32,
}

impl<'matrix> Search<'matrix> {
    pub(crate) fn new(matrix: &'matrix Matrix) -> Self {
        let bindings = Bindings::default();
        let mut path = Block::default();
        path.push(Path {
            lit: Off::new(Id::new(0), 0),
            parent: Id::new(0),
        });
        let todo = vec![];
        let constraints = vec![];
        let offset = 0;
        let limit = 0;
        Self {
            matrix,
            bindings,
            path,
            todo,
            constraints,
            offset,
            limit,
        }
    }

    pub(crate) fn go(&mut self) {
        self.limit = 1;
        loop {
            for start in &self.matrix.start {
                self.start(*start);
            }
            self.limit += 1;
        }
    }

    fn start(&mut self, id: Id<Cls>) {
        let cls = &self.matrix.clauses[id];
        let path = Id::new(0);
        for id in cls.lits {
            self.todo.push(Goal {
                lit: Off::new(id, self.offset),
                path,
            });
        }
        self.bindings.ensure_capacity(Var(self.offset + cls.vars));
        self.offset = cls.vars;
        self.prove();
        self.offset = 0;
        self.todo.clear();
    }

    fn prove(&mut self) {
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

        let goal = if let Some(goal) = self.todo.pop() {
            goal
        } else {
            println!("% SZS status Theorem");
            std::process::exit(0);
        };

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
            let path = self.path.len();
            self.path.push(Path {
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
                }
                self.bindings.undo_to_mark(undo_bindings);
            }
            self.path.pop();
        }

        self.constraints.truncate(undo_regularity);
        self.todo.push(goal);
    }
}
