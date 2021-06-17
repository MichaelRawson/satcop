use std::fmt;
use std::io::Write;
use std::sync::atomic::{AtomicU32, Ordering};

#[derive(Default)]
pub(crate) struct Counter(AtomicU32);

impl fmt::Display for Counter {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.load(Ordering::Relaxed).fmt(f)
    }
}

impl Counter {
    const fn new() -> Self {
        Self(AtomicU32::new(0))
    }

    pub(crate) fn set(&self, val: u32) {
        self.0.store(val, Ordering::Relaxed);
    }

    pub(crate) fn inc(&self) {
        self.0.fetch_add(1, Ordering::Relaxed);
    }

    pub(crate) fn max(&self, val: u32) {
        self.0.fetch_max(val, Ordering::Relaxed);
    }
}

pub(crate) static SYMBOLS: Counter = Counter::new();
pub(crate) static CLAUSES: Counter = Counter::new();
pub(crate) static START_CLAUSES: Counter = Counter::new();
pub(crate) static ITERATIVE_DEEPENING_STEPS: Counter = Counter::new();
pub(crate) static MAXIMUM_PATH_LIMIT: Counter = Counter::new();
pub(crate) static LITERAL_ATTEMPTS: Counter = Counter::new();
pub(crate) static DEPTH_FAILURES: Counter = Counter::new();
pub(crate) static REGULARITY_FAILURES: Counter = Counter::new();
pub(crate) static TAUTOLOGY_FAILURES: Counter = Counter::new();
pub(crate) static REDUCTIONS: Counter = Counter::new();
pub(crate) static EXTENSIONS: Counter = Counter::new();
pub(crate) static SAT_VARIABLES: Counter = Counter::new();
pub(crate) static SAT_CLAUSES: Counter = Counter::new();
pub(crate) static WALKSAT_SOLVED: Counter = Counter::new();
pub(crate) static CDCL_SOLVED: Counter = Counter::new();

pub(crate) fn print<W: Write>(w: &mut W) -> anyhow::Result<()> {
    writeln!(w, "% symbols: {}", SYMBOLS)?;
    writeln!(w, "% clauses: {}", CLAUSES)?;
    writeln!(w, "% start clauses: {}", START_CLAUSES)?;
    writeln!(
        w,
        "% iterative deepening steps: {}",
        ITERATIVE_DEEPENING_STEPS
    )?;
    writeln!(w, "% maximum path limit: {}", MAXIMUM_PATH_LIMIT)?;
    writeln!(w, "% literal attempts: {}", LITERAL_ATTEMPTS)?;
    writeln!(w, "% depth failures: {}", DEPTH_FAILURES)?;
    writeln!(w, "% regularity failures: {}", REGULARITY_FAILURES)?;
    writeln!(w, "% tautology failures: {}", TAUTOLOGY_FAILURES)?;
    writeln!(w, "% reductions: {}", REDUCTIONS)?;
    writeln!(w, "% extensions: {}", EXTENSIONS)?;
    writeln!(w, "% SAT variables: {}", SAT_VARIABLES)?;
    writeln!(w, "% SAT clauses: {}", SAT_CLAUSES)?;
    writeln!(w, "% WalkSAT solutions: {}", WALKSAT_SOLVED)?;
    writeln!(w, "% CDCL solutions: {}", CDCL_SOLVED)?;
    Ok(())
}
