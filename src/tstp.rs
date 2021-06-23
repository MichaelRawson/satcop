use crate::ground::Ground;
use crate::options::Options;
use crate::syntax::Matrix;
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

pub(crate) fn timeout<W: Write>(
    w: &mut W,
    options: &Options,
) -> anyhow::Result<()> {
    let name = get_problem_name(options);
    writeln!(w, "% SZS status TimeOut for {}", name)?;
    Ok(())
}

pub(crate) fn print_proof<W: Write>(
    w: &mut W,
    ground: &Ground,
    options: &Options,
    matrix: &Matrix,
) -> anyhow::Result<()> {
    let name = get_problem_name(options);
    let status = if matrix.have_conjecture {
        "Theorem"
    } else {
        "Unsatisfiable"
    };
    writeln!(w, "% SZS status {} for {}", status, name)?;
    if !options.quiet {
        writeln!(w, "% SZS output start ListOfCNF for {}", name)?;
        ground.print_proof(w, matrix)?;
        writeln!(w, "% SZS output end ListOfCNF for {}", name)?;
    }
    Ok(())
}
