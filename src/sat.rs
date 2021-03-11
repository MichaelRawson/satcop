use crate::binding::Bindings;
use crate::block::{Id, Off};
use crate::cdcl;
use crate::digest::{Digest, DigestMap, DigestSet};
use crate::syntax::{Clause, Literal, Matrix, Term};

#[derive(Default)]
pub(crate) struct Solver {
    cdcl: cdcl::CDCL,
    scratch: Vec<cdcl::Literal>,
    atoms: DigestMap<Id<cdcl::Atom>>,
    cache: DigestSet,
    new_clause: bool,
}

impl Solver {
    pub(crate) fn assert(
        &mut self,
        matrix: &Matrix,
        bindings: &Bindings,
        clauses: &[Off<Clause>],
    ) {
        for clause in clauses {
            let mut digest = Digest::default();
            for literal in matrix.clauses[clause.id].literals {
                let literal = self.literal(
                    matrix,
                    bindings,
                    Off::new(literal, clause.offset),
                );
                if !self.scratch.contains(&literal) {
                    self.scratch.push(literal);
                    let mut code = literal.atom.index as i32 + 1;
                    if !literal.pol {
                        code = -code;
                    }
                    let code = code as u32;
                    digest.update(code);
                }
            }
            if self.cache.insert(digest) {
                self.cdcl.assert(&self.scratch);
                self.new_clause = true;
            }
            self.scratch.clear();
        }
    }

    pub(crate) fn solve(&mut self) -> bool {
        self.cdcl.solve()
    }

    pub(crate) fn seen_new_clause(&mut self) -> bool {
        std::mem::take(&mut self.new_clause)
    }

    pub(crate) fn is_assigned_false(
        &mut self,
        matrix: &Matrix,
        bindings: &Bindings,
        literal: Off<Literal>,
    ) -> bool {
        if let Some(literal) = self.ground_literal(matrix, bindings, literal) {
            self.cdcl.is_assigned_false(literal)
        } else {
            false
        }
    }

    fn literal(
        &mut self,
        matrix: &Matrix,
        bindings: &Bindings,
        lit: Off<Literal>,
    ) -> cdcl::Literal {
        let Literal { pol, atom } = matrix.literals[lit.id];
        let atom = Off::new(atom, lit.offset);
        let mut digest = Digest::default();
        self.term(&mut digest, matrix, bindings, atom);
        let cdcl = &mut self.cdcl;
        let atom = *self
            .atoms
            .entry(digest)
            .or_insert_with(|| cdcl.fresh_atom());
        cdcl::Literal { pol, atom }
    }

    fn term(
        &mut self,
        digest: &mut Digest,
        matrix: &Matrix,
        bindings: &Bindings,
        term: Off<Term>,
    ) {
        let sym = matrix.terms[term.id].as_sym();
        digest.update(sym.index);
        let arity = matrix.symbols[sym].arity;
        let mut argit = term.id;
        for _ in 0..arity {
            argit.index += 1;
            let arg = matrix.terms[argit].as_arg();
            let arg =
                bindings.resolve(&matrix.terms, Off::new(arg, term.offset));
            if matrix.terms[arg.id].is_var() {
                digest.update(matrix.grounding_constant.index);
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
    ) -> Option<cdcl::Literal> {
        let Literal { pol, atom } = matrix.literals[literal.id];
        let mut digest = Digest::default();
        let atom = Off::new(atom, literal.offset);
        if !self.ground_term(&mut digest, matrix, bindings, atom) {
            return None;
        }
        let atom = *self.atoms.get(&digest)?;
        Some(cdcl::Literal { pol, atom })
    }

    fn ground_term(
        &mut self,
        digest: &mut Digest,
        matrix: &Matrix,
        bindings: &Bindings,
        mut term: Off<Term>,
    ) -> bool {
        let sym = matrix.terms[term.id].as_sym();
        digest.update(sym.index);
        let arity = matrix.symbols[sym].arity;
        for _ in 0..arity {
            term.id.index += 1;
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
}
