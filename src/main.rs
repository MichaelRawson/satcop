mod binding;
mod block;
mod builder;
mod digest;
mod matrix;
mod options;
mod pp;
mod sat;
mod search;
mod syntax;
mod tptp;
mod tstp;

use crate::options::Options;
use crate::search::Search;
use anyhow::Context;
use std::io::stdout;
use std::sync::Arc;
use std::time::Duration;

const STACK: usize = 0x1000000;

fn report_err<T>(err: anyhow::Error) -> T {
    eprintln!("satcop: {:?}", err.context("fatal error, exiting"));
    std::process::exit(1);
}

fn go(options: Arc<Options>) {
    let matrix = tptp::load(&options).unwrap_or_else(|err| {
        tstp::load_error(&err);
        report_err(err)
    });
    if options.clausify {
        matrix.dump_cnf();
        std::process::exit(0);
    }
    let mut search = Search::new(&matrix);
    if search.go() {
        let stdout = stdout();
        let mut lock = stdout.lock();
        tstp::unsatisfiable(&mut lock, &options)
            .context("printing unsat")
            .unwrap_or_else(report_err);
        std::process::exit(0);
    }
    else {
        let stdout = stdout();
        let mut lock = stdout.lock();
        tstp::gaveup(&mut lock, &options)
            .context("printing gaveup")
            .unwrap_or_else(report_err);
        std::process::exit(0);
    }
}

fn main() {
    let options = Arc::new(Options::new());
    {
        let thread_opts = options.clone();
        std::thread::Builder::new()
            .stack_size(STACK)
            .name("satcop".to_string())
            .spawn(move || go(thread_opts))
            .context("spawning thread")
            .unwrap_or_else(report_err);
    }
    std::thread::sleep(Duration::new(options.time, 0));
    let stdout = stdout();
    let mut lock = stdout.lock();
    tstp::timeout(&mut lock, &options)
        .context("printing timeout")
        .unwrap_or_else(report_err);
    std::process::exit(0);
}
