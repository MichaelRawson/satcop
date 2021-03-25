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

    #[clap(long, about = "Apply constrained equality elimination")]
    pub(crate) cee: bool,

    #[clap(long, about = "Print search statistcs")]
    pub(crate) statistics: bool,

    #[clap(long, about = "Print a proof, if found")]
    pub(crate) proof: bool,

    #[clap(long, default_value = "10", about = "time limit (secs)")]
    pub(crate) time: u64,
}

impl Options {
    pub(crate) fn new() -> Self {
        Self::parse()
    }
}
