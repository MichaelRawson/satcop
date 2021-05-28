use crate::block::Id;
use crate::sat::{SATCls, SATLit, SATVar};
use std::os::raw::c_int;

const PICOSAT_UNSATISFIABLE: c_int = 20;

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
    fn picosat_added_original_clauses(sat: *mut PicoSAT) -> c_int;
    fn picosat_coreclause(sat: *mut PicoSAT, i: c_int) -> c_int;
}

pub(crate) struct Pico(*mut PicoSAT);

impl Default for Pico {
    fn default() -> Self {
        let sat = unsafe { picosat_init() };
        Self(sat)
    }
}

impl Pico {
    pub(crate) fn enable_traces(&mut self) {
        assert!(unsafe { picosat_enable_trace_generation(self.0) } != 0);
    }

    pub(crate) fn assert(&mut self, clause: &[SATLit]) {
        for lit in clause {
            let lit = lit.0 as c_int;
            unsafe { picosat_add(self.0, lit) };
        }
        unsafe { picosat_add(self.0, 0) };
    }

    pub(crate) fn solve(&mut self) -> bool {
        let result = unsafe { picosat_sat(self.0, -1) };
        result != PICOSAT_UNSATISFIABLE
    }

    pub(crate) fn assignment(&self, var: Id<SATVar>) -> bool {
        let lit = SATLit::new(true, var);
        let assignment = unsafe { picosat_deref(self.0, lit.0 as c_int) };
        assignment == 1
    }

    pub(crate) fn core(&self) -> Vec<Id<SATCls>> {
        let mut core = vec![];
        for i in 0..unsafe { picosat_added_original_clauses(self.0) } {
            if unsafe { picosat_coreclause(self.0, i) } != 0 {
                core.push(Id::new(i as u32));
            }
        }
        core
    }
}
