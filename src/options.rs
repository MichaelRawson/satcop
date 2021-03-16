use clap::Clap;
use std::path::PathBuf;

#[derive(Clap)]
#[clap(
    name = "SATCoP",
    about = env!("CARGO_PKG_DESCRIPTION"),
    version = env!("CARGO_PKG_VERSION"),
    author = env!("CARGO_PKG_AUTHORS")
)]
pub(crate) struct Options {
    #[clap(parse(from_os_str), about = "path to input problem")]
    pub(crate) path: PathBuf,

    #[clap(long, about = "Print normal form and exit")]
    pub(crate) clausify: bool,

    #[clap(long, default_value = "10", about = "time limit (secs)")]
    pub(crate) time: u64,

    #[clap(
        long,
        default_value = "32",
        about = "threshold for naming subformulae"
    )]
    pub(crate) naming: u32,

    #[clap(long, about = "apply constrained equality elimination")]
    pub(crate) cee: bool,
}

impl Options {
    pub(crate) fn new() -> Self {
        Self::parse()
    }
}
