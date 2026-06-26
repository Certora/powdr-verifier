//! Grounded lemmas for ``uf_xor`` / ``uf_and`` / ``uf_or``.

use std::collections::{BTreeMap, BTreeSet, HashSet};

use smt2::{Script, Term};
use smt2::parse::Command;

use crate::passes::skolem::term_util::{
    atom, int_literal, list, scoped_free_variables,
};

const UF_XOR: &str = "uf_xor";
const UF_AND: &str = "uf_and";
const UF_OR: &str = "uf_or";

#[derive(Default, Clone)]
struct BitwiseTerms {
    xors: BTreeMap<String, Term>,
    ands: BTreeMap<String, Term>,
    ors: BTreeMap<String, Term>,
}

impl BitwiseTerms {
    fn non_empty(&self) -> bool {
        !self.xors.is_empty() || !self.ands.is_empty() || !self.ors.is_empty()
    }
}

#[derive(Default)]
struct BitwiseStats {
    seen_xor: usize,
    seen_and: usize,
    seen_or: usize,
    emitted_xor: usize,
    emitted_and: usize,
    emitted_or: usize,
    emitted_link: usize,
}

pub fn apply(script: &Script) -> Result<(Script, serde_json::Value), String> {
    let mut cur = script.clone();
    let mut stats = BitwiseStats::default();
    let mut seen_top: BTreeSet<String> = BTreeSet::new();
    let mut top_axioms = 0usize;

    for generators in [
        vec![ground_linking_lemmas as fn(&BitwiseTerms) -> Vec<Term>],
        vec![
            ground_xor_lemmas as fn(&BitwiseTerms) -> Vec<Term>,
            ground_and_lemmas as fn(&BitwiseTerms) -> Vec<Term>,
            ground_or_lemmas as fn(&BitwiseTerms) -> Vec<Term>,
        ],
    ] {
        let mut commands = Vec::new();
        for cmd in &cur.commands {
            if cmd.name() == "assert" {
                let body = smt2::term::assert_body(&cmd.raw)
                    .ok_or_else(|| format!("malformed assert: {}", cmd.raw))?;
                let term = Term::parse(&body)?;
                let new_body = transform_assert(&term, &generators, &mut stats);
                commands.push(Command::new(smt2::term::replace_assert_body(
                    &cmd.raw,
                    &new_body.to_string(),
                )));
                let terms = collect_bitwise_terms(&new_body, None);
                for axiom in emit_axioms(&terms, &generators, &mut stats) {
                    let key = axiom.to_string();
                    if seen_top.insert(key.clone()) {
                        top_axioms += 1;
                        commands.push(Command::new(format!("(assert {key})")));
                    }
                }
            } else {
                commands.push(cmd.clone());
            }
        }
        cur = Script::from_commands(commands);
    }

    Ok((
        cur,
        serde_json::json!({
            "top_level_bitwise_axiom_asserts": top_axioms,
            "bitwise_stats": {
                "seen": {
                    "xor": stats.seen_xor,
                    "and": stats.seen_and,
                    "or": stats.seen_or,
                },
                "emitted": {
                    "xor": stats.emitted_xor,
                    "and": stats.emitted_and,
                    "or": stats.emitted_or,
                    "link": stats.emitted_link,
                },
            },
        }),
    ))
}

fn transform_assert(
    term: &Term,
    generators: &[fn(&BitwiseTerms) -> Vec<Term>],
    stats: &mut BitwiseStats,
) -> Term {
    if is_quantifier(term) {
        return transform_quantifier(term, generators, stats);
    }
    fold_bitwise(term)
}

fn transform_quantifier(term: &Term, generators: &[fn(&BitwiseTerms) -> Vec<Term>], stats: &mut BitwiseStats) -> Term {
    let Term::List(items) = term else {
        return term.clone();
    };
    let qvars = quantifier_var_names(&items[1]);
    let body = fold_bitwise(&items[2]);
    let axioms = emit_axioms(&collect_bitwise_terms(&body, Some(&qvars)), generators, stats);
    let new_body = conjoin_axioms(&body, axioms);
    Term::List(vec![items[0].clone(), items[1].clone(), new_body])
}

fn emit_axioms(
    terms: &BitwiseTerms,
    generators: &[fn(&BitwiseTerms) -> Vec<Term>],
    stats: &mut BitwiseStats,
) -> Vec<Term> {
    if !terms.non_empty() {
        stats.seen_xor += terms.xors.len();
        stats.seen_and += terms.ands.len();
        stats.seen_or += terms.ors.len();
    }
    let mut out = Vec::new();
    for gen in generators {
        for ax in gen(terms) {
            if is_trueish(&ax) {
                continue;
            }
            note_emitted(stats, &ax);
            out.push(ax);
        }
    }
    out
}

fn note_emitted(stats: &mut BitwiseStats, ax: &Term) {
    let s = ax.to_string();
    if s.contains("uf_xor") && s.contains("uf_and") && s.contains("=>") {
        stats.emitted_link += 1;
    } else if s.contains("uf_xor") {
        stats.emitted_xor += 1;
    } else if s.contains("uf_and") {
        stats.emitted_and += 1;
    } else if s.contains("uf_or") {
        stats.emitted_or += 1;
    }
}

fn is_trueish(term: &Term) -> bool {
    matches!(term, Term::Atom(s) if s == "true")
}

fn collect_bitwise_terms(formula: &Term, qvarset: Option<&HashSet<String>>) -> BitwiseTerms {
    let mut out = BitwiseTerms::default();
    let mut stack = vec![formula.clone()];
    let mut seen = HashSet::new();
    while let Some(node) = stack.pop() {
        let key = node.to_string();
        if !seen.insert(key) {
            continue;
        }
        if let Some((name, _, _)) = uf_binary(&node) {
            let keep = qvarset.map(|qs| {
                !scoped_free_variables(&node, &HashSet::new())
                    .is_disjoint(qs)
            }).unwrap_or(true);
            if keep {
                match name {
                    UF_XOR => {
                        out.xors.insert(node.to_string(), node.clone());
                    }
                    UF_AND => {
                        out.ands.insert(node.to_string(), node.clone());
                    }
                    UF_OR => {
                        out.ors.insert(node.to_string(), node.clone());
                    }
                    _ => {}
                }
            }
        }
        if !is_quantifier(&node) {
            if let Term::List(items) = &node {
                for a in &items[1..] {
                    stack.push(a.clone());
                }
            }
        }
    }
    out
}

fn uf_binary(term: &Term) -> Option<(&str, Term, Term)> {
    let Term::List(items) = term else {
        return None;
    };
    if items.len() != 3 {
        return None;
    }
    let Term::Atom(name) = &items[0] else {
        return None;
    };
    if name != UF_XOR && name != UF_AND && name != UF_OR {
        return None;
    }
    Some((name.as_str(), items[1].clone(), items[2].clone()))
}

fn fold_bitwise(term: &Term) -> Term {
    if is_quantifier(term) {
        let Term::List(items) = term else {
            return term.clone();
        };
        return Term::List(vec![
            items[0].clone(),
            items[1].clone(),
            fold_bitwise(&items[2]),
        ]);
    }
    if let Some((name, x, y)) = uf_binary(term) {
        let x = fold_bitwise(&x);
        let y = fold_bitwise(&y);
        if let Some(folded) = fold_uf(name, &x, &y) {
            return folded;
        }
        return list(name, vec![x, y]);
    }
    match term {
        Term::List(items) if !items.is_empty() => Term::List(
            std::iter::once(items[0].clone())
                .chain(items[1..].iter().map(fold_bitwise))
                .collect(),
        ),
        _ => term.clone(),
    }
}

fn fold_uf(name: &str, x: &Term, y: &Term) -> Option<Term> {
    match name {
        UF_XOR => {
            if is_zero(x) {
                return Some(y.clone());
            }
            if is_zero(y) {
                return Some(x.clone());
            }
            if terms_equal(x, y) {
                return Some(atom("0"));
            }
        }
        UF_AND => {
            if is_zero(x) || is_zero(y) {
                return Some(atom("0"));
            }
            if terms_equal(x, y) {
                return Some(x.clone());
            }
        }
        UF_OR => {
            if is_zero(x) {
                return Some(y.clone());
            }
            if is_zero(y) {
                return Some(x.clone());
            }
            if terms_equal(x, y) {
                return Some(x.clone());
            }
        }
        _ => {}
    }
    None
}

fn ground_linking_lemmas(t: &BitwiseTerms) -> Vec<Term> {
    let mut out = Vec::new();
    for term in t.xors.values() {
        let (_, x, y) = uf_binary(term).unwrap();
        if terms_equal(&x, &y) {
            continue;
        }
        let conj = list(UF_AND, vec![x.clone(), y.clone()]);
        let disj = list(UF_OR, vec![x.clone(), y.clone()]);
        let guard = byte_guard(&x, &y);
        out.push(implies(
            guard.clone(),
            eq(plus(x.clone(), y.clone()), plus(term.clone(), times(atom("2"), conj.clone()))),
        ));
        out.push(implies(
            guard.clone(),
            and(vec![
                le(atom("0"), conj.clone()),
                le(conj.clone(), x.clone()),
                le(conj.clone(), y.clone()),
            ]),
        ));
        out.push(implies(
            guard,
            and(vec![
                eq(disj.clone(), minus(plus(x.clone(), y.clone()), conj)),
                le(atom("0"), disj.clone()),
                le(disj, atom("255")),
            ]),
        ));
    }
    out
}

fn ground_xor_lemmas(t: &BitwiseTerms) -> Vec<Term> {
    let mut out = Vec::new();
    for term in t.xors.values() {
        let (_, x, y) = uf_binary(term).unwrap();
        if terms_equal(&x, &y) {
            out.push(eq(term.clone(), atom("0")));
            continue;
        }
        out.push(iff(eq(x.clone(), y.clone()), eq(term.clone(), atom("0"))));
        out.push(iff(eq(x.clone(), atom("0")), eq(term.clone(), y.clone())));
        out.push(iff(eq(y.clone(), atom("0")), eq(term.clone(), x.clone())));
        out.push(implies(
            and(vec![
                le(atom("0"), x.clone()),
                le(x.clone(), atom("255")),
                eq(y.clone(), atom("255")),
            ]),
            eq(term.clone(), minus(atom("255"), x.clone())),
        ));
        out.push(implies(
            and(vec![
                le(atom("0"), y.clone()),
                le(y.clone(), atom("255")),
                eq(x.clone(), atom("255")),
            ]),
            eq(term.clone(), minus(atom("255"), y.clone())),
        ));
        out.push(iff(eq(x.clone(), term.clone()), eq(y.clone(), atom("0"))));
        out.push(iff(eq(y.clone(), term.clone()), eq(x.clone(), atom("0"))));
    }
    out
}

fn ground_and_lemmas(t: &BitwiseTerms) -> Vec<Term> {
    let mut out = Vec::new();
    for term in t.ands.values() {
        let (_, x, y) = uf_binary(term).unwrap();
        if terms_equal(&x, &y) {
            out.push(eq(term.clone(), x.clone()));
            continue;
        }
        out.push(iff(eq(x.clone(), y.clone()), eq(term.clone(), x.clone())));
        out.push(iff(eq(x.clone(), atom("0")), eq(term.clone(), atom("0"))));
        out.push(iff(eq(y.clone(), atom("0")), eq(term.clone(), atom("0"))));
        out.push(implies(
            and(vec![
                le(atom("0"), x.clone()),
                le(x.clone(), atom("255")),
                eq(y.clone(), atom("255")),
            ]),
            eq(term.clone(), x.clone()),
        ));
        out.push(implies(
            and(vec![
                le(atom("0"), y.clone()),
                le(y.clone(), atom("255")),
                eq(x.clone(), atom("255")),
            ]),
            eq(term.clone(), y.clone()),
        ));
    }
    out
}

fn ground_or_lemmas(t: &BitwiseTerms) -> Vec<Term> {
    let mut out = Vec::new();
    for term in t.ors.values() {
        let (_, x, y) = uf_binary(term).unwrap();
        if terms_equal(&x, &y) {
            out.push(eq(term.clone(), x.clone()));
            continue;
        }
        out.push(iff(eq(x.clone(), y.clone()), eq(term.clone(), x.clone())));
        out.push(iff(eq(x.clone(), atom("0")), eq(term.clone(), y.clone())));
        out.push(iff(eq(y.clone(), atom("0")), eq(term.clone(), x.clone())));
        out.push(implies(
            and(vec![
                le(atom("0"), x.clone()),
                le(x.clone(), atom("255")),
                eq(y.clone(), atom("255")),
            ]),
            eq(term.clone(), atom("255")),
        ));
        out.push(implies(
            and(vec![
                le(atom("0"), y.clone()),
                le(y.clone(), atom("255")),
                eq(x.clone(), atom("255")),
            ]),
            eq(term.clone(), atom("255")),
        ));
    }
    out
}

fn conjoin_axioms(body: &Term, axioms: Vec<Term>) -> Term {
    if axioms.is_empty() {
        return body.clone();
    }
    let mut parts = if is_and(body) {
        and_parts(body)
    } else {
        vec![body.clone()]
    };
    parts.extend(axioms);
    and(parts)
}

fn is_and(term: &Term) -> bool {
    matches!(term, Term::List(items) if matches!(items.first(), Some(Term::Atom(s)) if s == "and"))
}

fn and_parts(term: &Term) -> Vec<Term> {
    let Term::List(items) = term else {
        return vec![term.clone()];
    };
    items[1..].to_vec()
}

fn is_quantifier(term: &Term) -> bool {
    matches!(
        term,
        Term::List(items)
            if matches!(items.first(), Some(Term::Atom(s)) if s == "forall" || s == "exists")
                && items.len() >= 3
    )
}

fn quantifier_var_names(decls: &Term) -> HashSet<String> {
    let Term::List(items) = decls else {
        return HashSet::new();
    };
    items
        .iter()
        .filter_map(|d| match d {
            Term::List(pair) if !pair.is_empty() => {
                if let Term::Atom(name) = &pair[0] {
                    Some(name.clone())
                } else {
                    None
                }
            }
            Term::Atom(name) => Some(name.clone()),
            _ => None,
        })
        .collect()
}

fn terms_equal(a: &Term, b: &Term) -> bool {
    a.to_string() == b.to_string()
}

fn is_zero(t: &Term) -> bool {
    int_literal(t) == Some(0)
}

fn eq(a: Term, b: Term) -> Term {
    list("=", vec![a, b])
}

fn iff(a: Term, b: Term) -> Term {
    list("=", vec![a, b])
}

fn implies(a: Term, b: Term) -> Term {
    list("=>", vec![a, b])
}

fn and(parts: Vec<Term>) -> Term {
    if parts.len() == 1 {
        return parts[0].clone();
    }
    list("and", parts)
}

fn plus(a: Term, b: Term) -> Term {
    list("+", vec![a, b])
}

fn minus(a: Term, b: Term) -> Term {
    list("-", vec![a, b])
}

fn times(a: Term, b: Term) -> Term {
    list("*", vec![a, b])
}

fn le(a: Term, b: Term) -> Term {
    list("<=", vec![a, b])
}

fn byte_guard(x: &Term, y: &Term) -> Term {
    and(vec![
        le(atom("0"), x.clone()),
        le(x.clone(), atom("255")),
        le(atom("0"), y.clone()),
        le(y.clone(), atom("255")),
    ])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn noop_without_bitwise_uf_use() {
        let script = Script::parse(
            "(declare-fun uf_xor (Int Int) Int)\n(declare-fun x () Int)\n(assert (= x 7))\n(check-sat)\n",
        )
        .unwrap();
        let (out, stats) = apply(&script).unwrap();
        assert_eq!(stats["top_level_bitwise_axiom_asserts"], 0);
        let s = smt2::dump_string(&out);
        assert!(s.contains("(= x 7)"));
    }

    #[test]
    fn grounds_xor_axioms() {
        let script = Script::parse(
            "(declare-fun uf_xor (Int Int) Int)\n(declare-fun x () Int)\n(declare-fun y () Int)\n(declare-fun z () Int)\n(assert (= (uf_xor x y) z))\n(check-sat)\n",
        )
        .unwrap();
        let (out, stats) = apply(&script).unwrap();
        assert!(stats["top_level_bitwise_axiom_asserts"].as_u64().unwrap() > 0);
        let s = smt2::dump_string(&out);
        assert!(s.contains("(= (= x y) (= (uf_xor x y) 0))"));
        assert!(s.contains("(= (uf_xor x y) z)"));
    }

    #[test]
    fn folds_xor_xx_to_zero() {
        let script = Script::parse(
            "(declare-fun uf_xor (Int Int) Int)\n(declare-fun x () Int)\n(assert (= (uf_xor x x) 0))\n(check-sat)\n",
        )
        .unwrap();
        let (out, _) = apply(&script).unwrap();
        let s = smt2::dump_string(&out);
        assert!(!s.contains("(=>"));
        assert!(s.contains("(= 0 0)"));
    }

    #[test]
    fn injects_axioms_inside_quantifier() {
        let script = Script::parse(
            "(declare-fun uf_xor (Int Int) Int)\n(declare-fun y () Int)\n(declare-fun z () Int)\n(assert (forall ((x Int)) (= (uf_xor x y) z)))\n(check-sat)\n",
        )
        .unwrap();
        let (out, _) = apply(&script).unwrap();
        let s = smt2::dump_string(&out);
        assert!(s.contains("(forall ((x Int))"));
        assert!(s.contains("(and (= (uf_xor x y) z)"));
        assert!(s.contains("(= (= x y) (= (uf_xor x y) 0))"));
    }
}
