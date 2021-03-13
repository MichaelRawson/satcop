use crate::binding::Bindings;
use crate::block::{Block, Id, Off};
use crate::syntax::{Symbol, Term};
use std::cmp::Ordering;
use Ordering::*;

fn flip(ordering: Option<Ordering>) -> Option<Ordering> {
    ordering.map(|ordering| ordering.reverse())
}

fn sym(syms: &Block<Symbol>, left: Id<Symbol>, right: Id<Symbol>) -> Ordering {
    let left_arity = syms[left].arity;
    let right_arity = syms[right].arity;
    left_arity
        .cmp(&right_arity)
        .then(left.index.cmp(&right.index))
}

fn alpha(
    syms: &Block<Symbol>,
    terms: &Block<Term>,
    bindings: &Bindings,
    mut ss: Off<Term>,
    t: Off<Term>,
    s_stop: Id<Term>,
) -> Option<Ordering> {
    while ss.id != s_stop {
        match cmp(
            syms,
            terms,
            bindings,
            Off::new(terms[ss.id].as_arg(), ss.offset),
            t,
        ) {
            Some(Equal) | Some(Greater) => {
                return Some(Greater);
            }
            _ => {}
        }
        ss.id.index += 1;
    }
    None
}

fn ma(
    syms: &Block<Symbol>,
    terms: &Block<Term>,
    bindings: &Bindings,
    s: Off<Term>,
    mut tt: Off<Term>,
    stop: Id<Term>,
) -> Option<Ordering> {
    while tt.id != stop {
        let comparison = cmp(
            syms,
            terms,
            bindings,
            s,
            Off::new(terms[tt.id].as_arg(), tt.offset),
        );
        tt.id.index += 1;
        match comparison {
            Some(Greater) => {}
            Some(_) => return Some(Less),
            None => return flip(alpha(syms, terms, bindings, tt, s, stop)),
        }
    }
    Some(Greater)
}

fn lma(
    syms: &Block<Symbol>,
    terms: &Block<Term>,
    bindings: &Bindings,
    sym: Id<Symbol>,
    s: Off<Term>,
    t: Off<Term>,
) -> Option<Ordering> {
    let arity = syms[sym].arity;
    let mut ss = s.id;
    ss.index += 1;
    let mut tt = t.id;
    tt.index += 1;
    let mut s_stop = s.id;
    s_stop.index += arity + 1;
    let mut t_stop = t.id;
    t_stop.index += arity + 1;
    while ss != s_stop {
        match cmp(
            syms,
            terms,
            bindings,
            Off::new(terms[ss].as_arg(), s.offset),
            Off::new(terms[tt].as_arg(), t.offset),
        ) {
            Some(Less) => {
                return flip(ma(
                    syms,
                    terms,
                    bindings,
                    t,
                    Off::new(ss, s.offset),
                    s_stop,
                ));
            }
            Some(Equal) => {
                ss.index += 1;
                tt.index += 1;
            }
            Some(Greater) => {
                return ma(
                    syms,
                    terms,
                    bindings,
                    s,
                    Off::new(tt, t.offset),
                    t_stop,
                );
            }
            None => {
                return alpha(
                    syms,
                    terms,
                    bindings,
                    Off::new(ss, s.offset),
                    t,
                    s_stop,
                )
                .or_else(|| {
                    flip(alpha(
                        syms,
                        terms,
                        bindings,
                        Off::new(tt, t.offset),
                        s,
                        t_stop,
                    ))
                });
            }
        }
    }
    Some(Ordering::Equal)
}

pub(crate) fn cmp(
    syms: &Block<Symbol>,
    terms: &Block<Term>,
    bindings: &Bindings,
    s: Off<Term>,
    t: Off<Term>,
) -> Option<Ordering> {
    let s = bindings.resolve(terms, s);
    let t = bindings.resolve(terms, t);
    match (terms[s.id].is_var(), terms[t.id].is_var()) {
        (true, true) => {
            if terms[s.id].as_var().offset(s.offset)
                == terms[t.id].as_var().offset(t.offset)
            {
                Some(Equal)
            } else {
                None
            }
        }
        (true, false) => {
            if bindings.occurs(
                syms,
                terms,
                terms[s.id].as_var().offset(s.offset),
                t,
            ) {
                Some(Less)
            } else {
                None
            }
        }
        (false, true) => {
            if bindings.occurs(
                syms,
                terms,
                terms[t.id].as_var().offset(t.offset),
                s,
            ) {
                Some(Greater)
            } else {
                None
            }
        }
        (false, false) => {
            let f = terms[s.id].as_sym();
            let f_arity = syms[f].arity;
            let g = terms[t.id].as_sym();
            let g_arity = syms[g].arity;
            let mut ss = s;
            ss.id.index += 1;
            let mut s_stop = s.id;
            s_stop.index += f_arity + 1;
            let mut tt = t;
            tt.id.index += 1;
            let mut t_stop = t.id;
            t_stop.index += g_arity + 1;
            match sym(syms, f, g) {
                Less => flip(ma(syms, terms, bindings, t, ss, s_stop)),
                Equal => lma(syms, terms, bindings, f, s, t),
                Greater => ma(syms, terms, bindings, s, tt, t_stop),
            }
        }
    }
}
