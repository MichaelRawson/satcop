use crate::binding::Bindings;
use crate::block::{Block, BlockMap, Id, Off};
use crate::digest::{Digest, DigestMap, DigestSet};
use crate::sat;
use crate::statistics::Statistics;
use crate::syntax::*;
use std::io::Write;

#[derive(Debug, Clone, Copy)]
struct Record(u32);

impl Record {
    fn arg(id: Id<Self>) -> Self {
        Self(id.as_u32())
    }

    fn sym(id: Id<Symbol>) -> Self {
        Self(id.as_u32())
    }

    fn var() -> Self {
        Self(u32::MAX)
    }

    fn is_var(self) -> bool {
        self.0 == u32::MAX
    }

    fn as_arg(self) -> Id<Self> {
        Id::new(self.0)
    }

    fn as_sym(self) -> Id<Symbol> {
        Id::new(self.0)
    }
}

#[derive(Default)]
pub(crate) struct Ground {
    sat: sat::Solver,
    scratch: Vec<sat::Lit>,
    atoms: DigestMap<Id<sat::Var>>,
    cache: DigestSet,
    fresh: Id<sat::Var>,
    new_clause: bool,
    record: bool,
    origins: BlockMap<sat::Cls, Id<Clause>>,
    record_terms: Block<Record>,
    record_cache: DigestMap<Id<Record>>,
    atom_record: BlockMap<sat::Var, Id<Record>>,
}

impl Ground {
    pub(crate) fn record_proof(&mut self) {
        self.sat.enable_traces();
        self.record = true;
    }

    pub(crate) fn assert(
        &mut self,
        statistics: &mut Statistics,
        matrix: &Matrix,
        bindings: &Bindings,
        clauses: &[Off<Clause>],
    ) {
        for clause in clauses {
            let mut digest = Digest::default();
            for literal in matrix.clauses[clause.id].literals {
                let literal = self.literal(
                    statistics,
                    matrix,
                    bindings,
                    Off::new(literal, clause.offset),
                );
                self.scratch.push(literal);
                let code = literal.0 as u32;
                digest.update(code);
            }
            if self.cache.insert(digest) {
                self.new_clause = true;
                statistics.sat_clauses += 1;
                self.sat.assert(&self.scratch);
                if self.record {
                    self.origins.push(clause.id);
                }
            }
            self.scratch.clear();
        }
    }

    pub(crate) fn solve(&mut self, statistics: &mut Statistics) -> bool {
        self.sat.solve(statistics)
    }

    pub(crate) fn seen_new_clause(&mut self) -> bool {
        std::mem::take(&mut self.new_clause)
    }

    pub(crate) fn is_ground_assigned_false(
        &mut self,
        matrix: &Matrix,
        bindings: &Bindings,
        literal: Off<Literal>,
    ) -> bool {
        if let Some(literal) = self.ground_literal(matrix, bindings, literal) {
            self.sat.assignment[literal.var()] != literal.pol()
        } else {
            false
        }
    }

    pub(crate) fn print_proof<W: Write>(
        &self,
        w: &mut W,
        matrix: &Matrix,
    ) -> anyhow::Result<()> {
        for (gi, record) in self.sat.core().into_iter().enumerate() {
            let origin = self.origins[record];
            write!(w, "cnf(g{}, plain, ", gi)?;
            let clause = self.sat.clauses[record];
            if clause.is_empty() {
                write!(w, "$false")?;
            } else {
                let mut print_sep = false;
                for literal in clause {
                    let literal = self.sat.literals[literal];
                    if print_sep {
                        write!(w, " | ")?;
                    }
                    if !literal.pol() {
                        write!(w, "~")?;
                    }
                    let record = self.atom_record[literal.var()];
                    self.print_record(w, matrix, record)?;
                    print_sep = true;
                }
            }
            write!(w, ", inference(ground_cnf, [], [")?;
            match &matrix.info[origin].source {
                Source::Equality => {
                    write!(w, "theory(equality)")?;
                }
                Source::Axiom { path, name } => {
                    write!(w, "file({}, {})", path, name)?;
                }
            }
            writeln!(w, "])).")?;
        }
        Ok(())
    }

    fn print_record<W: Write>(
        &self,
        w: &mut W,
        matrix: &Matrix,
        mut record: Id<Record>,
    ) -> anyhow::Result<()> {
        let sym = self.record_terms[record].as_sym();
        write!(w, "{}", &matrix.symbols[sym].name)?;
        let arity = matrix.symbols[sym].arity;
        if arity == 0 {
            return Ok(());
        }
        write!(w, "(")?;
        for i in 0..arity {
            record.increment();
            if i > 0 {
                write!(w, ",")?;
            }
            if self.record_terms[record].is_var() {
                write!(
                    w,
                    "{}",
                    &matrix.symbols[matrix.grounding_constant].name
                )?;
            } else {
                let arg = self.record_terms[record].as_arg();
                self.print_record(w, matrix, arg)?;
            }
        }
        write!(w, ")")?;
        Ok(())
    }

    fn literal(
        &mut self,
        statistics: &mut Statistics,
        matrix: &Matrix,
        bindings: &Bindings,
        lit: Off<Literal>,
    ) -> sat::Lit {
        let Literal { pol, atom } = matrix.literals[lit.id];
        let atom = Off::new(atom, lit.offset);
        let mut digest = Digest::default();
        self.term(&mut digest, matrix, bindings, atom);
        let mut new = false;
        let fresh = &mut self.fresh;
        let solver = &mut self.sat;
        let sat = *self.atoms.entry(digest).or_insert_with(|| {
            statistics.sat_variables += 1;
            new = true;
            solver.add_var();
            let var = *fresh;
            fresh.increment();
            var
        });
        if new && self.record {
            let record = self.record(matrix, bindings, atom);
            self.atom_record.push(record);
        }
        sat::Lit::new(pol, sat)
    }

    fn term(
        &mut self,
        digest: &mut Digest,
        matrix: &Matrix,
        bindings: &Bindings,
        term: Off<Term>,
    ) {
        let sym = matrix.terms[term.id].as_sym();
        digest.update(sym.as_u32());
        let arity = matrix.symbols[sym].arity;
        let mut argit = term.id;
        for _ in 0..arity {
            argit.increment();
            let arg = matrix.terms[argit].as_arg();
            let arg =
                bindings.resolve(&matrix.terms, Off::new(arg, term.offset));
            if matrix.terms[arg.id].is_var() {
                digest.update(matrix.grounding_constant.as_u32());
            } else {
                self.term(digest, matrix, bindings, arg);
            };
        }
    }

    fn ground_literal(
        &mut self,
        matrix: &Matrix,
        bindings: &Bindings,
        literal: Off<Literal>,
    ) -> Option<sat::Lit> {
        let Literal { pol, atom } = matrix.literals[literal.id];
        let mut digest = Digest::default();
        let atom = Off::new(atom, literal.offset);
        if !self.ground_term(&mut digest, matrix, bindings, atom) {
            return None;
        }
        let atom = *self.atoms.get(&digest)?;
        Some(sat::Lit::new(pol, atom))
    }

    fn ground_term(
        &mut self,
        digest: &mut Digest,
        matrix: &Matrix,
        bindings: &Bindings,
        mut term: Off<Term>,
    ) -> bool {
        let sym = matrix.terms[term.id].as_sym();
        digest.update(sym.as_u32());
        let arity = matrix.symbols[sym].arity;
        for _ in 0..arity {
            term.id.increment();
            let arg = matrix.terms[term.id].as_arg();
            let arg =
                bindings.resolve(&matrix.terms, Off::new(arg, term.offset));
            if matrix.terms[arg.id].is_var() {
                return false;
            } else {
                self.ground_term(digest, matrix, bindings, arg);
            };
        }
        true
    }

    fn record(
        &mut self,
        matrix: &Matrix,
        bindings: &Bindings,
        term: Off<Term>,
    ) -> Id<Record> {
        let sym = matrix.terms[term.id].as_sym();
        let mut recorded = vec![Record::sym(sym)];
        let mut digest = Digest::default();
        digest.update(sym.as_u32());

        let arity = matrix.symbols[sym].arity;
        let mut argit = term.id;
        for _ in 0..arity {
            argit.increment();
            let arg = matrix.terms[argit].as_arg();
            let arg =
                bindings.resolve(&matrix.terms, Off::new(arg, term.offset));
            let arg = if matrix.terms[arg.id].is_var() {
                Record::var()
            } else {
                Record::arg(self.record(matrix, bindings, arg))
            };
            recorded.push(arg);
            digest.update(arg.0);
        }
        let record_terms = &mut self.record_terms;
        *self.record_cache.entry(digest).or_insert_with(|| {
            let start = record_terms.len();
            for record in recorded {
                record_terms.push(record);
            }
            start
        })
    }
}