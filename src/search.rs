use crate::binding::Bindings;
use crate::block::{Block, Id, Off};
use crate::matrix::{Matrix, Pos};
use crate::syntax::{Cls, Lit, Var};

#[derive(Debug)]
struct Path {
    lit: Off<Lit>,
    parent: Id<Path>,
}

#[derive(Debug, Clone, Copy)]
struct Goal {
    lit: Off<Lit>,
    path: Id<Path>,
}

pub(crate) struct Search<'matrix> {
    matrix: &'matrix Matrix,
    bindings: Bindings,
    path: Block<Path>,
    todo: Vec<Goal>,
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
        let offset = 0;
        let limit = 0;
        Self {
            matrix,
            bindings,
            path,
            todo,
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
        for lit in cls.lits {
            self.todo.push(Goal {
                lit: Off::new(lit, 0),
                path,
            });
        }
        self.bindings.ensure_capacity(Var(self.offset + cls.vars));
        self.offset = cls.vars;
        self.prove();
        self.offset = 0;
        self.todo.clear();
    }

    #[inline(never)]
    fn prove(&mut self) {
        let goal = if let Some(goal) = self.todo.pop() {
            goal
        } else {
            println!("% SZS status Theorem");
            std::process::exit(0);
        };

        let undo_bindings = self.bindings.mark();
        let lit = self.matrix.lits[goal.lit.id];

        let mut path_len = 0;
        let mut path = goal.path;
        while path.index != 0 {
            let path_lit = self.path[path].lit;
            if self.matrix.lits[path_lit.id].pol != lit.pol {
                self.reduce(goal.lit, path_lit);
                self.bindings.undo_to_mark(undo_bindings);
            }
            path_len += 1;
            path = self.path[path].parent;
        }

        if path_len < self.limit {
            let undo_todo = self.todo.len();
            let path = self.path.len();
            self.path.push(Path {
                lit: goal.lit,
                parent: goal.path,
            });
            let sym = self.matrix.terms[lit.atom].as_sym();
            for pos in &self.matrix.index[sym].pol[!lit.pol as usize] {
                self.extend(goal, *pos, path);
                self.bindings.undo_to_mark(undo_bindings);
                self.todo.truncate(undo_todo);
            }
            self.path.pop();
        }

        self.todo.push(goal);
    }

    #[inline(always)]
    fn reduce(&mut self, lit: Off<Lit>, path: Off<Lit>) {
        if self.bindings.unify(
            &self.matrix.syms,
            &self.matrix.terms,
            Off::new(self.matrix.lits[lit.id].atom, lit.offset),
            Off::new(self.matrix.lits[path.id].atom, path.offset),
        ) {
            self.prove();
        }
    }

    #[inline(always)]
    fn extend(&mut self, goal: Goal, pos: Pos, path: Id<Path>) {
        let cls = self.matrix.clauses[pos.cls];
        self.bindings.ensure_capacity(Var(self.offset + cls.vars));
        if !self.bindings.unify(
            &self.matrix.syms,
            &self.matrix.terms,
            Off::new(self.matrix.lits[goal.lit.id].atom, goal.lit.offset),
            Off::new(self.matrix.lits[pos.lit].atom, self.offset),
        ) {
            return;
        }

        for id in cls.lits {
            if id == pos.lit {
                continue;
            }
            self.todo.push(Goal {
                path,
                lit: Off::new(id, self.offset)
            });
        }
        self.offset += cls.vars;
        self.prove();

        self.offset -= cls.vars;
    }
}
