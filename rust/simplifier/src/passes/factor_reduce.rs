//! `factor_reduce`: discharge `(mod Q P) = 0` atoms that are polynomial
//! multiples of a known-zero hypothesis `(mod B P) = 0`.
//!
//! The powdr optimizer's `remove_redundant_constraints` (trivial_simp) drops
//! `A·B ≡ 0` whenever `B ≡ 0` is already a constraint (a factor of it is asserted
//! zero). In the verifier's *expanded* mod-polynomial encoding z3 can't see that
//! structure and must re-derive `Q ≡ 0` via ideal-membership / a finite-domain
//! case-split, which times out (e.g. the `flags` selector-sum constraints in the
//! 008_trivial_simp soundness VCs: `S·(S−1)·(S−2) ≡ 0` dropped because
//! `(S−1)·(S−2) ≡ 0` is kept).
//!
//! This pass re-applies the factor reasoning: if a top-level known-zero `B`
//! properly divides `Q` (`deg B < deg Q`, `B | Q`), then `Q ≡ 0` is entailed, so
//! rewrite `(mod Q P) = 0 → true`. Under the negated goal that turns
//! `¬(mod Q P = 0)` into `false`, dropping the hard disjunct.
//!
//! Sound: `B ≡ 0` is a global conjunct hypothesis and `B | Q` over ℤ implies
//! `Q ≡ 0 (mod P)`, so `(mod Q P) = 0` is globally true. The strict-degree
//! requirement means only *proper* multiples are reduced, never a hypothesis by
//! itself.

use smt2::{map_asserts, map_bool_children_opt, unwrap_zero_mod_eq, Script};
use z3::ast::{Ast, AstKind, Bool, Dynamic, Int};
use z3::DeclKind;

use crate::passes::normalize::field_mod;
use crate::poly_factor::divides;

pub fn apply(script: &Script) -> Result<(Script, serde_json::Value), String> {
    let field = match field_mod() {
        Some(p) => p,
        None => return Ok((script.clone(), serde_json::json!({"reduced": 0}))),
    };

    let hyps = collect_known_zero(script, field);
    if hyps.is_empty() {
        return Ok((
            script.clone(),
            serde_json::json!({"reduced": 0, "hypotheses": 0}),
        ));
    }
    let hyp_degs: Vec<usize> = hyps.iter().map(total_degree).collect();

    let mut reduced = 0usize;
    let out = map_asserts(script, |b| {
        Ok(reduce_once(b, &hyps, &hyp_degs, field, &mut reduced).unwrap_or_else(|| b.clone()))
    })?;

    Ok((
        out,
        serde_json::json!({"reduced": reduced, "hypotheses": hyps.len()}),
    ))
}

/// Top-level known-zero polynomials: `(mod B P) = 0` conjuncts, including
/// conjuncts of a top-level `(and ...)`. Not anything inside an `or`/`not`.
fn collect_known_zero(script: &Script, p: i128) -> Vec<Int> {
    let mut out = Vec::new();
    for cmd in &script.commands {
        if let Some(b) = cmd.assert_bool() {
            collect_conjunct_zeros(&b, p, &mut out);
        }
    }
    out
}

fn collect_conjunct_zeros(term: &Bool, p: i128, out: &mut Vec<Int>) {
    if let Some(q) = unwrap_zero_mod_eq(term, p) {
        out.push(q);
        return;
    }
    let d = Dynamic::from_ast(term);
    if d.kind() == AstKind::App && d.decl().kind() == DeclKind::And {
        for ch in d.children() {
            if let Some(cb) = ch.as_bool() {
                collect_conjunct_zeros(&cb, p, out);
            }
        }
    }
}

/// Returns `Some` only when a subtree changed (identity-preserving walk).
fn reduce_once(
    term: &Bool,
    hyps: &[Int],
    hyp_degs: &[usize],
    p: i128,
    count: &mut usize,
) -> Option<Bool> {
    if let Some(q) = unwrap_zero_mod_eq(term, p) {
        let qd = total_degree(&q);
        for (b, &bd) in hyps.iter().zip(hyp_degs) {
            // Proper multiple only: deg B in (0, deg Q). Never reduces a
            // hypothesis by itself (equal degree) or a constant divisor.
            if bd == 0 || bd >= qd {
                continue;
            }
            if divides(&q, b, p as u64).unwrap_or(false) {
                *count += 1;
                return Some(Bool::from_bool(true));
            }
        }
        return None;
    }
    map_bool_children_opt(term, &mut |child| reduce_once(child, hyps, hyp_degs, p, count))
}

/// Total (multivariate) degree of an Int polynomial expression.
fn total_degree(e: &Int) -> usize {
    let d = Dynamic::from_ast(e);
    if d.kind() == AstKind::Numeral {
        return 0;
    }
    if d.kind() == AstKind::App {
        return match d.decl().kind() {
            DeclKind::Add | DeclKind::Sub => d
                .children()
                .iter()
                .filter_map(|c| c.as_int())
                .map(|c| total_degree(&c))
                .max()
                .unwrap_or(0),
            DeclKind::Uminus => d
                .children()
                .into_iter()
                .next()
                .and_then(|c| c.as_int())
                .map(|c| total_degree(&c))
                .unwrap_or(0),
            DeclKind::Mul => d
                .children()
                .iter()
                .filter_map(|c| c.as_int())
                .map(|c| total_degree(&c))
                .sum(),
            // bare variable / opaque symbol
            _ => 1,
        };
    }
    1
}

#[cfg(test)]
mod tests {
    use super::*;

    const P: i128 = 2013265921;

    #[test]
    fn reduces_proper_multiple() {
        let _field_env = crate::field_env_guard();
        std::env::set_var("SIMPLIFIER_FIELD_MOD", P.to_string());
        // hypothesis (x-1)(x-2) = 0; goal atom x*(x-1)(x-2) = 0 is a proper
        // multiple -> reduced to true (the disjunct under `not` drops).
        let script = Script::parse(&format!(
            "(declare-fun x () Int)\n\
             (assert (= (mod (* (- x 1) (- x 2)) {P}) 0))\n\
             (assert (or (not (= (mod (* x (* (- x 1) (- x 2))) {P}) 0)) (< x 0)))\n\
             (check-sat)\n"
        ))
        .unwrap();
        let (out, stats) = apply(&script).unwrap();
        assert_eq!(stats["reduced"], 1, "{}", smt2::dump_string(&out));
        assert!(smt2::dump_string(&out).contains("true"));
    }

    #[test]
    fn keeps_non_multiple_and_hypothesis() {
        let _field_env = crate::field_env_guard();
        std::env::set_var("SIMPLIFIER_FIELD_MOD", P.to_string());
        // (x-1)=0 neither divides (y-3) (different var) nor is a proper divisor
        // of itself (equal degree) -> nothing reduced.
        let script = Script::parse(&format!(
            "(declare-fun x () Int)\n(declare-fun y () Int)\n\
             (assert (= (mod (- x 1) {P}) 0))\n\
             (assert (or (not (= (mod (- y 3) {P}) 0)) (< x 0)))\n\
             (check-sat)\n"
        ))
        .unwrap();
        let (_out, stats) = apply(&script).unwrap();
        assert_eq!(stats["reduced"], 0);
    }
}
