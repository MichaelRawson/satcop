#![allow(clippy::upper_case_acronyms)]

mod binding;
mod block;
mod builder;
mod digest;
mod ground;
mod options;
mod pp;
mod rng;
mod sat;
mod search;
mod statistics;
mod syntax;
mod tptp;
mod tstp;

use crate::options::Options;
use crate::search::Search;
use crate::syntax::Matrix;
use anyhow::Context;
use std::io::stdout;
use std::sync::Arc;
use std::time::{Duration, Instant};

const STACK: usize = 0x1000000;

fn report_err<T>(err: anyhow::Error) -> T {
    eprintln!("satcop: {:?}", err.context("fatal error, exiting"));
    std::process::exit(1);
}

fn go(matrix: Arc<Matrix>, options: Arc<Options>, index: usize) {
    let mut search = Search::default();
    search.seed(index as u64);
    if search.go(&*options, &matrix) {
        let stdout = stdout();
        let mut lock = stdout.lock();
        tstp::unsatisfiable(&mut lock, &options)
            .context("printing unsat")
            .unwrap_or_else(report_err);
        if options.statistics {
            statistics::print(&mut lock)
                .context("printing statistics")
                .unwrap_or_else(report_err);
        }
        if options.proof {
            tstp::print_proof(&mut lock, &options, &matrix, &search)
                .context("printing proof")
                .unwrap_or_else(report_err);
        }
        std::process::exit(0);
    } else {
        let stdout = stdout();
        let mut lock = stdout.lock();
        tstp::gaveup(&mut lock, &options)
            .context("printing gaveup")
            .unwrap_or_else(report_err);
        std::process::exit(0);
    }
}

fn main() {
    let start = Instant::now();
    let options = Arc::new(Options::new());
    let matrix = Arc::new(tptp::load(&options).unwrap_or_else(|err| {
        tstp::load_error(&err);
        report_err(err)
    }));
    if options.clausify {
        matrix.print_cnf();
        return;
    }

    statistics::SYMBOLS.set(matrix.symbols.len().as_u32());
    statistics::CLAUSES.set(matrix.clauses.len().as_u32());
    statistics::START_CLAUSES.set(matrix.start.len() as u32);
    for i in 0..num_cpus::get() {
        let thread_opts = options.clone();
        let thread_matrix = matrix.clone();
        std::thread::Builder::new()
            .stack_size(STACK)
            .name("satcop".to_string())
            .spawn(move || go(thread_matrix, thread_opts, i))
            .context("spawning thread")
            .unwrap_or_else(report_err);
    }

    let assigned = Duration::new(options.time, 0);
    let elapsed = start.elapsed();
    if let Some(remaining) = assigned.checked_sub(elapsed) {
        std::thread::sleep(remaining);
    }
    let stdout = stdout();
    let mut lock = stdout.lock();
    tstp::timeout(&mut lock, &options)
        .context("printing timeout")
        .unwrap_or_else(report_err);
    std::process::exit(0);
}
