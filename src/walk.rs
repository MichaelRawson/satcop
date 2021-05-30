use crate::block::{Block, BlockMap, Id, Range};
use crate::default_rng::DefaultRng;
use crate::sat::{SATCls, SATLit, SATVar};
use crate::statistics::Statistics;
use rand::seq::SliceRandom;
use rand::Rng;
use std::os::raw::c_int;

const PICOSAT_UNSATISFIABLE: c_int = 20;
const ITERATIONS: u32 = 1000;

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

struct Pico(*mut PicoSAT);

impl Default for Pico {
    fn default() -> Self {
        let sat = unsafe { picosat_init() };
        Self(sat)
    }
}

impl Pico {
    fn enable_traces(&mut self) {
        assert!(unsafe { picosat_enable_trace_generation(self.0) } != 0);
    }

    fn assert(&mut self, clause: &[SATLit]) {
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

    fn assigned(&self, var: Id<SATVar>) -> bool {
        let lit = SATLit::new(true, var);
        let assignment = unsafe { picosat_deref(self.0, lit.0 as c_int) };
        assignment == 1
    }

    fn forced(&self, var: Id<SATVar>) -> bool {
        let lit = SATLit::new(true, var);
        let assignment =
            unsafe { picosat_deref_toplevel(self.0, lit.0 as c_int) };
        assignment != 0
    }

    fn core(&self) -> Vec<Id<SATCls>> {
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
    clause: Id<SATCls>,
    rest: Option<Box<Watch>>,
}

#[derive(Default)]
pub(crate) struct Walk {
    pub(crate) clauses: BlockMap<SATCls, Range<SATLit>>,
    pub(crate) literals: Block<SATLit>,
    pub(crate) assignment: BlockMap<SATVar, bool>,
    forced: BlockMap<SATVar, bool>,
    watch: BlockMap<SATVar, Option<Box<Watch>>>,
    unsatisfied: Vec<Id<SATCls>>,
    rng: DefaultRng,
    pico: Pico,
}

impl Walk {
    pub(crate) fn enable_traces(&mut self) {
        self.pico.enable_traces();
    }

    pub(crate) fn add_var(&mut self) {
        self.assignment.push(false);
        self.forced.push(false);
        self.watch.push(None);
    }

    pub(crate) fn assert(&mut self, clause: &[SATLit]) {
        self.pico.assert(clause);
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
    }

    pub(crate) fn solve(&mut self, statistics: &mut Statistics) -> bool {
        let mut possible = vec![];
        for _ in 0..ITERATIONS {
            let unsatisfied = if let Some(unsatisfied) = self.choose_unsat() {
                unsatisfied
            } else {
                statistics.walksat_solved += 1;
                return true;
            };
            possible.clear();
            possible.extend(
                self.clauses[unsatisfied]
                    .into_iter()
                    .map(|id| self.literals[id])
                    .filter(|lit| !self.forced[lit.var()]),
            );
            if let Some(flip) = possible.choose(&mut self.rng.0) {
                self.flip(flip.var());
                self.satisfy(unsatisfied);
            } else {
                self.unsatisfied.push(unsatisfied);
                break;
            }
        }
        if self.pico.solve() {
            statistics.cdcl_solved += 1;
            for var in self.assignment.range() {
                if !self.forced[var] {
                    self.forced[var] = self.pico.forced(var);
                    if self.assignment[var] != self.pico.assigned(var) {
                        self.flip(var);
                    }
                }
            }
            true
        } else {
            false
        }
    }

    pub(crate) fn core(&self) -> Vec<Id<SATCls>> {
        self.pico.core()
    }

    fn choose_unsat(&mut self) -> Option<Id<SATCls>> {
        while !self.unsatisfied.is_empty() {
            let index = self.rng.0.gen_range(0..self.unsatisfied.len());
            let unsatisfied = self.unsatisfied.swap_remove(index);
            if !self.satisfy(unsatisfied) {
                return Some(unsatisfied);
            }
        }
        None
    }

    fn satisfy(&mut self, clause: Id<SATCls>) -> bool {
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

    fn flip(&mut self, var: Id<SATVar>) {
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
