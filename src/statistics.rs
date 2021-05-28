use std::io::Write;

#[derive(Default)]
pub(crate) struct Statistics {
    pub(crate) symbols: u32,
    pub(crate) clauses: u32,
    pub(crate) start_clauses: u32,
    pub(crate) iterative_deepening_steps: u32,
    pub(crate) maximum_path_limit: u32,
    pub(crate) literal_attempts: u32,
    pub(crate) depth_failures: u32,
    pub(crate) regularity_failures: u32,
    pub(crate) tautology_failures: u32,
    pub(crate) goals_assigned_false: u32,
    pub(crate) paths_assigned_false: u32,
    pub(crate) reductions: u32,
    pub(crate) extensions: u32,
    pub(crate) sat_variables: u32,
    pub(crate) sat_clauses: u32,
}

impl Statistics {
    pub(crate) fn print<W: Write>(&self, w: &mut W) -> anyhow::Result<()> {
        writeln!(w, "% symbols: {}", self.symbols)?;
        writeln!(w, "% clauses: {}", self.clauses)?;
        writeln!(w, "% start clauses: {}", self.start_clauses)?;
        writeln!(
            w,
            "% iterative deepening steps: {}",
            self.iterative_deepening_steps
        )?;
        writeln!(w, "% maximum path limit: {}", self.maximum_path_limit)?;
        writeln!(w, "% literal attempts: {}", self.literal_attempts)?;
        writeln!(w, "% depth failures: {}", self.depth_failures)?;
        writeln!(w, "% regularity failures: {}", self.regularity_failures)?;
        writeln!(w, "% tautology failures: {}", self.tautology_failures)?;
        writeln!(
            w,
            "% goal literals assigned false: {}",
            self.goals_assigned_false
        )?;
        writeln!(
            w,
            "% path literals assigned false: {}",
            self.paths_assigned_false
        )?;
        writeln!(w, "% reductions: {}", self.reductions)?;
        writeln!(w, "% extensions: {}", self.extensions)?;
        writeln!(w, "% SAT variables: {}", self.sat_variables)?;
        writeln!(w, "% SAT clauses: {}", self.sat_clauses)?;
        Ok(())
    }
}
