use crate::options::Options;
use crate::tptp::{SyntaxError, Unsupported};
use std::io::Write;

fn get_problem_name(options: &Options) -> &str {
    options
        .path
        .file_stem()
        .and_then(|name| name.to_str())
        .unwrap_or_default()
}

pub(crate) fn load_error(error: &anyhow::Error) {
    if error.is::<SyntaxError>() {
        println!("% SZS status SyntaxError");
    } else if error.is::<Unsupported>() {
        println!("% SZS status Inappropriate");
    } else if error.is::<std::io::Error>() {
        println!("% SZS status OSError");
    }
}

pub(crate) fn gaveup<W: Write>(
    w: &mut W,
    options: &Options,
) -> anyhow::Result<()> {
    let name = get_problem_name(options);
    writeln!(w, "% SZS status GaveUp for {}", name)?;
    Ok(())
}

pub(crate) fn unsatisfiable<W: Write>(
    w: &mut W,
    options: &Options,
) -> anyhow::Result<()> {
    let name = get_problem_name(options);
    writeln!(w, "% SZS status Unsatisfiable for {}", name)?;
    Ok(())
}

pub(crate) fn timeout<W: Write>(
    w: &mut W,
    options: &Options,
) -> anyhow::Result<()> {
    let name = get_problem_name(options);
    writeln!(w, "% SZS status TimeOut for {}", name)?;
    Ok(())
}