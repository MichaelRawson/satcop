use crate::block::{Block, BlockMap, Id, Range};
use crate::rng::DefaultRng;
use crate::statistics::Statistics;
use rand::seq::SliceRandom;
use rand::Rng;
use std::os::raw::c_int;

#[derive(Debug, Clone, Copy)]
pub(crate) struct Var;

#[derive(Debug, Clone, Copy)]
pub(crate) struct Lit(pub(crate) i32);

impl Lit {
    pub(crate) fn new(pol: bool, var: Id<Var>) -> Self {
        let mut lit = var.as_u32() as i32 + 1;
        if !pol {
            lit = -lit;
        }
        Self(lit)
    }

    pub(crate) fn pol(self) -> bool {
        self.0 > 0
    }

    pub(crate) fn var(self) -> Id<Var> {
        Id::new(self.0.abs() as u32 - 1)
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct Cls;

const PICOSAT_UNSATISFIABLE: c_int = 20;
const ITERATIONS: u32 = 10000;

#[repr(C)]
struct PicoSAT {
    _unused: [u8; 0],
}

#[link(name = "picosat")]
extern "C" {
    fn picosat_init() -> *mut PicoSAT;
    fn picosat_enable_trace_generation(sat: *mut PicoSAT) -> c_int;
    fn picosat_add(sat: *mut PicoSAT, lit: c_int) -> c_int;
    fn picosat_sat(sat: *mut PicoSAT, limit: c_int) -> c_int;
    fn picosat_deref(sat: *mut PicoSAT, lit: c_int) -> c_int;
    fn picosat_deref_toplevel(sat: *mut PicoSAT, lit: c_int) -> c_int;
    fn picosat_added_original_clauses(sat: *mut PicoSAT) -> c_int;
    fn picosat_coreclause(sat: *mut PicoSAT, i: c_int) -> c_int;
}

struct CDCL(*mut PicoSAT);

impl Default for CDCL {
    fn default() -> Self {
        let sat = unsafe { picosat_init() };
        Self(sat)
    }
}

impl CDCL {
    fn enable_traces(&mut self) {
        assert!(unsafe { picosat_enable_trace_generation(self.0) } != 0);
    }

    fn assert(&mut self, clause: &[Lit]) {
        for lit in clause {
            let lit = lit.0 as c_int;
            unsafe { picosat_add(self.0, lit) };
        }
        unsafe { picosat_add(self.0, 0) };
    }

    fn solve(&mut self) -> bool {
        let result = unsafe { picosat_sat(self.0, -1) };
        result != PICOSAT_UNSATISFIABLE
    }

    fn assigned(&self, var: Id<Var>) -> bool {
        let lit = Lit::new(true, var);
        let assignment = unsafe { picosat_deref(self.0, lit.0 as c_int) };
        assignment == 1
    }

    fn forced(&self, var: Id<Var>) -> bool {
        let lit = Lit::new(true, var);
        let assignment =
            unsafe { picosat_deref_toplevel(self.0, lit.0 as c_int) };
        assignment != 0
    }

    fn core(&self) -> Vec<Id<Cls>> {
        let mut core = vec![];
        for i in 0..unsafe { picosat_added_original_clauses(self.0) } {
            if unsafe { picosat_coreclause(self.0, i) } != 0 {
                core.push(Id::new(i as u32));
            }
        }
        core
    }
}

#[derive(Debug)]
struct Watch {
    clause: Id<Cls>,
    rest: Option<Box<Watch>>,
}

#[derive(Default)]
pub(crate) struct Solver {
    pub(crate) clauses: BlockMap<Cls, Range<Lit>>,
    pub(crate) literals: Block<Lit>,
    pub(crate) assignment: BlockMap<Var, bool>,
    pub(crate) unsat: bool,
    forced: BlockMap<Var, bool>,
    watch: BlockMap<Var, Option<Box<Watch>>>,
    unsatisfied: Vec<Id<Cls>>,
    rng: DefaultRng,
    cdcl: CDCL,
}

impl Solver {
    pub(crate) fn enable_traces(&mut self) {
        self.cdcl.enable_traces();
    }

    pub(crate) fn add_var(&mut self) {
        self.assignment.push(false);
        self.forced.push(false);
        self.watch.push(None);
    }

    pub(crate) fn assert(
        &mut self,
        statistics: &mut Statistics,
        clause: &[Lit],
    ) {
        if self.unsat {
            return;
        }
        self.cdcl.assert(clause);
        let start = self.literals.len();
        for literal in clause {
            self.literals.push(*literal);
        }
        let end = self.literals.len();
        let literals = Range::new(start, end);
        let id = self.clauses.push(literals);

        if clause.len() == 1 {
            let unit = clause[0];
            self.forced[unit.var()] = true;
            if self.assignment[unit.var()] != unit.pol() {
                self.flip(unit.var());
            }
        }
        if !self.satisfy(id) {
            self.unsatisfied.push(id);
        }
        self.solve(statistics);
    }

    pub(crate) fn core(&self) -> Vec<Id<Cls>> {
        self.cdcl.core()
    }

    fn solve(&mut self, statistics: &mut Statistics) {
        let mut possible = vec![];
        for _ in 0..ITERATIONS {
            let unsatisfied = if let Some(unsatisfied) = self.choose_unsat() {
                unsatisfied
            } else {
                statistics.walksat_solved += 1;
                return;
            };
            possible.clear();
            possible.extend(
                self.clauses[unsatisfied]
                    .into_iter()
                    .map(|id| self.literals[id])
                    .filter(|lit| !self.forced[lit.var()]),
            );
            if let Some(flip) = possible.choose(self.rng.get()) {
                self.flip(flip.var());
                self.satisfy(unsatisfied);
            } else {
                self.unsatisfied.push(unsatisfied);
                break;
            }
        }
        if self.cdcl.solve() {
            statistics.cdcl_solved += 1;
            for var in self.assignment.range() {
                if !self.forced[var] {
                    self.forced[var] = self.cdcl.forced(var);
                    if self.assignment[var] != self.cdcl.assigned(var) {
                        self.flip(var);
                    }
                }
            }
        } else {
            self.unsat = true;
        }
    }

    fn choose_unsat(&mut self) -> Option<Id<Cls>> {
        while !self.unsatisfied.is_empty() {
            let index = self.rng.get().gen_range(0..self.unsatisfied.len());
            let unsatisfied = self.unsatisfied.swap_remove(index);
            if !self.satisfy(unsatisfied) {
                return Some(unsatisfied);
            }
        }
        None
    }

    fn satisfy(&mut self, clause: Id<Cls>) -> bool {
        for pos in self.clauses[clause] {
            let lit = self.literals[pos];
            if self.assignment[lit.var()] == lit.pol() {
                let rest = std::mem::take(&mut self.watch[lit.var()]);
                let watch = Box::new(Watch { clause, rest });
                self.watch[lit.var()] = Some(watch);
                return true;
            }
        }
        false
    }

    fn flip(&mut self, var: Id<Var>) {
        self.assignment[var] = !self.assignment[var];
        let mut watch = std::mem::take(&mut self.watch[var]);
        while let Some(boxed) = watch {
            let Watch { clause, rest } = *boxed;
            if !self.satisfy(clause) {
                self.unsatisfied.push(clause);
            }
            watch = rest;
        }
    }
}
