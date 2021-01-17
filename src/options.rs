use clap::Clap;
use std::path::PathBuf;

#[derive(Clap)]
pub(crate) struct Options {
    #[clap(parse(from_os_str))]
    pub(crate) path: PathBuf,

    #[clap(long, default_value = "10")]
    pub(crate) time: u64,
}

impl Options {
    pub(crate) fn new() -> Self {
        Self::parse()
    }
}
