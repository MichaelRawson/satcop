mod binding;
mod block;
mod builder;
mod matrix;
mod options;
mod pp;
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
    eprintln!("lazycop: {:?}", err.context("fatal error, exiting"));
    std::process::exit(1);
}

fn go(options: Arc<Options>) {
    let matrix = tptp::load(&options).unwrap_or_else(|err| {
        tstp::load_error(&err);
        report_err(err)
    });
    let mut search = Search::new(&matrix);
    search.go();
}

fn main() {
    let options = Arc::new(Options::new());
    {
        let thread_opts = options.clone();
        std::thread::Builder::new()
            .stack_size(STACK)
            .name("lazycop".to_string())
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
