use crate::syntax::*;
use fnv::FnvHashMap;
use std::rc::Rc;

pub(crate) fn monotonicity(fresh: &mut u32, clause: &mut CNF) {
    let mut defs = FnvHashMap::default();
    for index in 0..clause.0.len() {
        let NNFLiteral { pol, atom } = clause.0[index].clone();
        let (f, args) = if let FOFTerm::Fun(f, args) = &*atom {
            (*f, args)
        } else {
            unreachable!();
        };
        let atom = if f == EQUALITY {
            let left = flatten_args(fresh, &mut defs, clause, &args[0]);
            let right = flatten_args(fresh, &mut defs, clause, &args[1]);
            Rc::new(FOFTerm::Fun(EQUALITY, vec![left, right]))
        } else {
            flatten_args(fresh, &mut defs, clause, &atom)
        };
        clause.0[index] = NNFLiteral { pol, atom };
    }
}

fn flatten_args(
    fresh: &mut u32,
    defs: &mut FnvHashMap<Rc<FOFTerm>, Rc<FOFTerm>>,
    clause: &mut CNF,
    term: &Rc<FOFTerm>,
) -> Rc<FOFTerm> {
    let (f, args) = if let FOFTerm::Fun(f, args) = &**term {
        (*f, args)
    } else {
        return term.clone();
    };
    let args = args
        .iter()
        .map(|arg| flatten(fresh, defs, clause, arg))
        .collect();
    Rc::new(FOFTerm::Fun(f, args))
}

pub(crate) fn reflexivity(clause: &mut CNF) {
    let mut index = 0;
    while index < clause.0.len() {
        if let Some((x, y)) = as_variable_disequation(&clause.0[index]) {
            clause.0.swap_remove(index);
            for literal in &mut clause.0 {
                literal.atom = subst(x, &y, &literal.atom);
            }
        } else {
            index += 1;
        }
    }
}

pub(crate) fn symmetry(clause: &CNF) -> Vec<CNF> {
    let mut result = vec![];
    let mut sofar = vec![];
    swapsies(&mut result, &mut sofar, &clause.0);
    result
}

pub(crate) fn transitivity(
    fresh: &mut u32,
    clause: &mut CNF,
) -> Vec<(Rc<FOFTerm>, Rc<FOFTerm>)> {
    let mut orderings = vec![];
    for index in 0..clause.0.len() {
        let atom = clause.0[index].atom.clone();
        let (f, args) = if let FOFTerm::Fun(f, args) = &*atom {
            (*f, args)
        } else {
            unreachable!();
        };
        if f != EQUALITY {
            continue;
        }
        let left = &args[0];
        let right = &args[1];
        if matches!(&**right, FOFTerm::Var(_)) {
            orderings.push((left.clone(), right.clone()));
            continue;
        }
        let link = Rc::new(FOFTerm::Var(Var(*fresh)));
        *fresh += 1;
        orderings.push((left.clone(), link.clone()));
        orderings.push((right.clone(), link.clone()));
        clause.0[index].atom =
            Rc::new(FOFTerm::Fun(EQUALITY, vec![left.clone(), link.clone()]));
        clause.0.push(NNFLiteral {
            pol: false,
            atom: Rc::new(FOFTerm::Fun(EQUALITY, vec![right.clone(), link])),
        });
    }
    orderings
}

fn flatten(
    fresh: &mut u32,
    defs: &mut FnvHashMap<Rc<FOFTerm>, Rc<FOFTerm>>,
    clause: &mut CNF,
    term: &Rc<FOFTerm>,
) -> Rc<FOFTerm> {
    let (f, args) = if let FOFTerm::Fun(f, args) = &**term {
        (f, args)
    } else {
        return term.clone();
    };
    let args = args
        .iter()
        .map(|arg| flatten(fresh, defs, clause, arg))
        .collect();
    let term = Rc::new(FOFTerm::Fun(*f, args));
    defs.entry(term.clone())
        .or_insert_with(|| {
            let var = Rc::new(FOFTerm::Var(Var(*fresh)));
            *fresh += 1;
            let equation =
                Rc::new(FOFTerm::Fun(EQUALITY, vec![var.clone(), term]));
            clause.0.push(NNFLiteral {
                pol: false,
                atom: equation,
            });
            var
        })
        .clone()
}

fn as_variable_disequation(
    literal: &NNFLiteral,
) -> Option<(Var, Rc<FOFTerm>)> {
    if literal.pol {
        return None;
    }
    let (f, args) = if let FOFTerm::Fun(f, args) = &*literal.atom {
        (*f, args)
    } else {
        unreachable!();
    };
    if f != EQUALITY {
        return None;
    }
    let (left, right) = if let [l, r] = args.as_slice() {
        (l, r)
    } else {
        unreachable!();
    };
    let x = if let FOFTerm::Var(x) = &**left {
        *x
    } else {
        return None;
    };
    let y = if let FOFTerm::Var(_) = &**right {
        right.clone()
    } else {
        return None;
    };
    Some((x, y))
}

fn subst(from: Var, to: &Rc<FOFTerm>, term: &Rc<FOFTerm>) -> Rc<FOFTerm> {
    match &**term {
        FOFTerm::Var(x) if *x == from => to.clone(),
        FOFTerm::Var(_) => term.clone(),
        FOFTerm::Fun(f, args) => Rc::new(FOFTerm::Fun(
            *f,
            args.iter().map(|arg| subst(from, to, arg)).collect(),
        )),
    }
}

fn swapsies(
    result: &mut Vec<CNF>,
    sofar: &mut Vec<NNFLiteral>,
    todo: &[NNFLiteral],
) {
    if todo.is_empty() {
        result.push(CNF(sofar.clone()));
        return;
    }
    let literal = todo[0].clone();
    let (f, args) = if let FOFTerm::Fun(f, args) = &*literal.atom {
        (*f, args)
    } else {
        unreachable!()
    };
    if f != EQUALITY {
        sofar.push(literal);
        swapsies(result, sofar, &todo[1..]);
        sofar.pop();
    } else if literal.pol {
        let swapped = NNFLiteral {
            pol: true,
            atom: Rc::new(FOFTerm::Fun(
                EQUALITY,
                vec![args[1].clone(), args[0].clone()],
            )),
        };
        sofar.push(literal);
        swapsies(result, sofar, &todo[1..]);
        sofar.pop();
        sofar.push(swapped);
        swapsies(result, sofar, &todo[1..]);
        sofar.pop();
    } else {
        let literal = if matches!(&*args[0], FOFTerm::Var(_)) {
            NNFLiteral {
                pol: false,
                atom: Rc::new(FOFTerm::Fun(
                    EQUALITY,
                    vec![args[1].clone(), args[0].clone()],
                )),
            }
        } else {
            literal
        };
        sofar.push(literal);
        swapsies(result, sofar, &todo[1..]);
        sofar.pop();
    }
}
