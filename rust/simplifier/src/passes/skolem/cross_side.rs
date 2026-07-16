//! Cross-side derived-witness fallback.
//!
//! A `rule_based`-style rewrite can leave a comparison / is-zero gadget column
//! (`diff_marker`, `diff_inv_marker`, `diff_val`, …) defined as a *derived*
//! column on one side while the other (checked/quantified) side keeps it as a
//! plain constrained witness with no derived definition. The same-name fallback
//! (`names`) only pins the quantified copy `<checked>-X` to `<other>-X` when the
//! latter survives as a *declared free* symbol -- which is not guaranteed (it may
//! have been derived-away/substituted). When it does not, the column is left
//! unwitnessed, the simplifier frees it, and the solver assigns a value that
//! violates the gadget => spurious `sat`.
//!
//! This runs last (after `names` / `derived` / `witness` / `isolate` / `rules`)
//! and only touches quantified columns nothing else pinned. For each such column
//! `<checked>-X` it looks up the other side's derived definition `<other>-X =
//! expr` among the loaded pins and pins `<checked>-X` to `expr` with every free
//! variable's before-/after- prefix swapped onto the checked side. Both sides
//! compute the same gadget over the same (same-name-pinned) inputs, so the
//! swapped definition is a valid -- indeed the canonical -- witness. Sound: an
//! added witness can only discharge a spurious failure, never mask a real one (a
//! wrong witness merely fails to close the case, leaving the `sat`).

use std::collections::{HashMap, HashSet};

use smt2::ast_build::substitute_dyn;
use smt2::ast_util::{scoped_free_symbol_ids, swap_prefix, symbol_name_for_id};
use z3::ast::{Bool, Dynamic, Int};

use super::map::SkolemMap;
use super::types::{SkolemPin, SortKind};
use super::utils::split_equation;

/// Swap the before-/after- prefix on every free variable of `expr`.
fn swap_expr_prefix(expr: &Dynamic, sorts: &HashMap<String, SortKind>) -> Dynamic {
    let mut out = expr.clone();
    for id in scoped_free_symbol_ids(&out, &HashSet::new()) {
        let Some(name) = symbol_name_for_id(id) else {
            continue;
        };
        let Some(swapped) = swap_prefix(&name) else {
            continue;
        };
        let rep = match sorts.get(&name).copied().unwrap_or(SortKind::Other) {
            SortKind::Bool => Dynamic::from_ast(&Bool::new_const(swapped.as_str())),
            _ => Dynamic::from_ast(&Int::new_const(swapped.as_str())),
        };
        out = substitute_dyn(&out, &name, &rep);
    }
    out
}

pub fn contribute(map: &mut SkolemMap, pins: &[SkolemPin], sorts: &HashMap<String, SortKind>) {
    // Other-side derived definitions, keyed by the defined variable's name.
    let mut defs: HashMap<String, Dynamic> = HashMap::new();
    for pin in pins {
        if let Some((var, expr)) = split_equation(&pin.equation) {
            defs.entry(var).or_insert(expr);
        }
    }
    if defs.is_empty() {
        return;
    }
    for q in map.qvars.clone() {
        if map.is_pinned(q) {
            continue;
        }
        let Some(q_name) = symbol_name_for_id(q) else {
            continue;
        };
        let Some(partner) = swap_prefix(&q_name) else {
            continue;
        };
        let Some(expr) = defs.get(&partner) else {
            continue;
        };
        let witness = swap_expr_prefix(expr, sorts);
        map.pin(q, witness, "cross-side-derived");
    }
}
