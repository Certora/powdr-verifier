//! SMT-backed strengthening for small finite integer domains (choice/or-eq).

use std::collections::{HashMap, HashSet};

use smt2::{and_parts, decl_name, free_int_nodes, int_from_i128, is_int_const, or_parts, Script, SmtCommand};
use z3::SatResult;
use z3::ast::{Ast, AstKind, Bool, Dynamic, Int};
use z3::DeclKind;

use crate::expr_util::{rebuild_script, AssertBuildCtx};

const MAX_VALUES: usize = 3;
const MAX_PAIRS: usize = 20;
const RLIMIT: u32 = 1_000_000;

pub fn apply(script: &Script) -> Result<(Script, serde_json::Value), String> {
    let assertions = collect_assert_terms(script);
    let mut stats = serde_json::json!({
        "base_asserts": assertions.len(),
    });

    if assertions.is_empty() {
        stats["choice_symbols"] = 0.into();
        stats["pairs_probed"] = 0.into();
        stats["clusters_probed"] = 0.into();
        stats["added_facts"] = 0.into();
        return Ok((script.clone(), stats));
    }

    let choices = collect_choices(&assertions, MAX_VALUES);
    stats["choice_symbols"] = choices.len().into();
    if choices.is_empty() {
        stats["pairs_probed"] = 0.into();
        stats["clusters_probed"] = 0.into();
        stats["added_facts"] = 0.into();
        return Ok((script.clone(), stats));
    }

    let prefix = declare_block(script);
    let mut remaining: Vec<Int> = choices.keys().cloned().collect();
    remaining.sort_by_cached_key(|s| decl_name(&s.decl()));
    let mut symbols_probed = 0usize;
    let mut clusters_probed = 0usize;
    let mut flag_vars_total = 0usize;
    let mut flag_local_total = 0usize;
    let mut batch: Vec<Bool> = Vec::new();
    let mut cluster_stats = Vec::new();

    while !remaining.is_empty() && symbols_probed < MAX_PAIRS {
        let seed = remaining.remove(0);
        let cluster = flag_cluster(&seed, &assertions, &choices);
        remaining.retain(|s| !cluster.contains(s));

        let mut cluster_choices: HashMap<Int, Vec<i128>> = cluster
            .iter()
            .filter_map(|s| choices.get(s).map(|v| (s.clone(), v.clone())))
            .collect();
        if cluster_choices.is_empty() {
            continue;
        }

        let n_syms = cluster_choices.len();
        if symbols_probed + n_syms > MAX_PAIRS {
            let take = MAX_PAIRS - symbols_probed;
            cluster_choices = cluster_choices.into_iter().take(take).collect();
        }

        let rel = cluster_assertions(&assertions, &cluster);
        clusters_probed += 1;
        symbols_probed += cluster_choices.len();
        flag_vars_total += cluster.len();
        flag_local_total += rel.len();

        let outcomes = probe_cluster(&prefix, &rel, &cluster_choices, &mut batch);
        cluster_stats.push(serde_json::json!({
            "index": clusters_probed,
            "n_vars": cluster_choices.len(),
            "n_flag_vars": cluster.len(),
            "n_asserts": rel.len(),
            "probes_sat": outcomes.probes_sat,
            "probes_unsat": outcomes.probes_unsat,
            "probes_unknown": outcomes.probes_unknown,
            "excluded": outcomes.excluded,
        }));
    }

    stats["pairs_probed"] = symbols_probed.into();
    stats["clusters_probed"] = clusters_probed.into();
    stats["flag_vars"] = flag_vars_total.into();
    stats["flag_local_asserts"] = flag_local_total.into();
    stats["clusters"] = serde_json::Value::Array(cluster_stats);

    let added = batch.len();
    stats["added_facts"] = added.into();

    if batch.is_empty() {
        return Ok((script.clone(), stats));
    }

    let mut ctx = AssertBuildCtx::from_script(script)?;
    let mut commands: Vec<SmtCommand> = Vec::new();
    let mut inserted = false;
    for cmd in &script.commands {
        if !inserted && cmd.name() == "check-sat" {
            for fact in &batch {
                ctx.push_assert(&mut commands, fact)?;
            }
            inserted = true;
        }
        if let Some(b) = cmd.assert_bool() {
            ctx.push_assert(&mut commands, b)?;
        } else {
            commands.push(cmd.clone());
        }
    }
    if !inserted {
        for fact in &batch {
            ctx.push_assert(&mut commands, fact)?;
        }
    }

    Ok((rebuild_script(&script.source, commands), stats))
}

fn collect_assert_terms(script: &Script) -> Vec<Bool> {
    script
        .commands
        .iter()
        .filter_map(|c| c.assert_bool().cloned())
        .collect()
}

fn declare_block(script: &Script) -> String {
    let mut out = String::new();
    out.push_str("(set-logic ALL)\n");
    for cmd in &script.commands {
        if cmd.name() == "declare-fun" {
            out.push_str(&cmd.to_smtlib(&script.source));
            out.push('\n');
        }
    }
    out
}

fn collect_choices(assertions: &[Bool], max_n: usize) -> HashMap<Int, Vec<i128>> {
    let mut raw: HashMap<Int, Vec<i128>> = HashMap::new();
    for a in assertions {
        for (sym, _, vals) in choices_in_assertion(a) {
            let cur = raw.entry(sym).or_default();
            for v in vals {
                if !cur.contains(&v) {
                    cur.push(v);
                }
            }
            cur.sort();
        }
    }
    raw.into_iter()
        .filter(|(_, vals)| vals.len() > 1 && vals.len() <= max_n)
        .collect()
}

fn choices_in_assertion(f: &Bool) -> Vec<(Int, Bool, Vec<i128>)> {
    if let Some((sym, vals)) = parse_or_equalities(f) {
        return vec![(sym, f.clone(), vals)];
    }
    let Some(and_terms) = and_parts(f) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for arg in and_terms {
        if let Some((sym, vals)) = parse_or_equalities(&arg) {
            out.push((sym, arg.clone(), vals));
        }
    }
    out
}

fn parse_or_equalities(f: &Bool) -> Option<(Int, Vec<i128>)> {
    let parts = or_parts(f)?;
    let mut sym: Option<Int> = None;
    let mut vals = Vec::new();
    for d in parts {
        let (s, v) = eq_symbol_int(&d)?;
        if let Some(existing) = &sym {
            if !existing.ast_eq(&s) {
                return None;
            }
        } else {
            sym = Some(s);
        }
        vals.push(v);
    }
    let sym = sym?;
    if vals.is_empty() {
        return None;
    }
    vals.sort();
    vals.dedup();
    Some((sym, vals))
}

fn eq_symbol_int(term: &Bool) -> Option<(Int, i128)> {
    let ast = Dynamic::from_ast(term);
    if ast.kind() != AstKind::App || ast.num_children() != 2 || ast.decl().kind() != DeclKind::Eq {
        return None;
    }
    let lhs = ast.nth_child(0)?;
    let rhs = ast.nth_child(1)?;
    if let Some(sym) = lhs.as_int() {
        if is_int_const(&lhs) {
            if let Some(v) = smt2::int_value_dyn(&rhs) {
                return Some((sym, v));
            }
        }
    }
    if let Some(sym) = rhs.as_int() {
        if is_int_const(&rhs) {
            if let Some(v) = smt2::int_value_dyn(&lhs) {
                return Some((sym, v));
            }
        }
    }
    None
}

fn const_pinned_in(f: &Bool) -> HashSet<Int> {
    if let Some((sym, _)) = eq_symbol_int(f) {
        return HashSet::from([sym]);
    }
    if let Some(parts) = and_parts(f) {
        return parts.iter().flat_map(const_pinned_in).collect();
    }
    HashSet::new()
}

fn flag_cluster(
    seed: &Int,
    assertions: &[Bool],
    choices: &HashMap<Int, Vec<i128>>,
) -> HashSet<Int> {
    let choice_syms: HashSet<Int> = choices.keys().cloned().collect();
    let mut cluster: HashSet<Int> = HashSet::from([seed.clone()]);
    let mut changed = true;
    while changed {
        changed = false;
        for a in assertions {
            let fvs = free_int_nodes(a);
            if fvs.is_disjoint(&cluster) {
                continue;
            }
            let new_pins = const_pinned_in(a);
            if !new_pins.is_subset(&cluster) {
                for p in new_pins {
                    if cluster.insert(p) {
                        changed = true;
                    }
                }
            }
        }
        for a in assertions {
            let fvs = free_int_nodes(a);
            if fvs.is_disjoint(&cluster) {
                continue;
            }
            let extras: HashSet<Int> = fvs.difference(&cluster).cloned().collect();
            if extras.is_subset(&choice_syms) {
                for s in extras {
                    if cluster.insert(s) {
                        changed = true;
                    }
                }
            }
        }
    }
    cluster
}

fn cluster_assertions(assertions: &[Bool], cluster: &HashSet<Int>) -> Vec<Bool> {
    assertions
        .iter()
        .filter(|a| free_int_nodes(a).is_subset(cluster))
        .cloned()
        .collect()
}

struct ProbeOutcomes {
    probes_sat: usize,
    probes_unsat: usize,
    probes_unknown: usize,
    excluded: usize,
}

fn batch_insert(batch: &mut Vec<Bool>, fact: Bool) -> bool {
    if batch.iter().any(|b| b.ast_eq(&fact)) {
        return false;
    }
    batch.push(fact);
    true
}

fn probe_cluster(
    prefix: &str,
    rel: &[Bool],
    cluster_choices: &HashMap<Int, Vec<i128>>,
    batch: &mut Vec<Bool>,
) -> ProbeOutcomes {
    let mut out = ProbeOutcomes {
        probes_sat: 0,
        probes_unsat: 0,
        probes_unknown: 0,
        excluded: 0,
    };

    let solver = z3::Solver::new();
    set_rlimit(&solver);
    solver.from_string(prefix.as_bytes());
    for a in rel {
        solver.assert(a);
    }

    let mut syms: Vec<_> = cluster_choices.iter().collect();
    syms.sort_by_cached_key(|(s, _)| decl_name(&s.decl()));
    for (sym, vals) in syms {
        for v in vals {
            let probe = sym.eq(&int_from_i128(*v));
            let r = probe_assumption(&solver, &probe);
            match r {
                Some(true) => out.probes_sat += 1,
                Some(false) => {
                    out.probes_unsat += 1;
                    let ne = probe.not();
                    if batch_insert(batch, ne.clone()) {
                        out.excluded += 1;
                        solver.assert(&ne);
                    }
                }
                None => out.probes_unknown += 1,
            }
        }
    }
    out
}

fn set_rlimit(solver: &z3::Solver) {
    let mut params = z3::Params::new();
    params.set_u32("rlimit", RLIMIT);
    solver.set_params(&params);
}

fn probe_assumption(solver: &z3::Solver, assumption: &Bool) -> Option<bool> {
    solver.push();
    solver.assert(assumption);
    let r = solver.check();
    solver.pop(1);
    match r {
        SatResult::Sat => Some(true),
        SatResult::Unsat => Some(false),
        SatResult::Unknown => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn has_z3() -> bool {
        std::process::Command::new("pkg-config")
            .args(["--exists", "z3"])
            .status()
            .map(|s| s.success())
            .unwrap_or(false)
    }

    fn int_const(name: &str) -> Int {
        Int::new_const(name)
    }

    #[test]
    fn flag_cluster_drops_wide_columns() {
        let script = Script::parse(
            "(assert (or (= opcode_and_flag 0) (= opcode_and_flag 1)))\n\
             (assert (= (* opcode_and_flag a__0_0) a__0_0))\n\
             (check-sat)\n",
        )
        .unwrap();
        let asserts = collect_assert_terms(&script);
        let flag_dom = asserts[0].clone();
        let choices = collect_choices(&asserts, 3);
        let cluster = flag_cluster(&int_const("opcode_and_flag"), &asserts, &choices);
        assert!(cluster.contains(&int_const("opcode_and_flag")));
        assert!(!cluster.contains(&int_const("a__0_0")));
        let sliced = cluster_assertions(&asserts, &cluster);
        assert_eq!(sliced.len(), 1);
        assert!(sliced[0].ast_eq(&flag_dom));
    }

    #[test]
    fn flag_cluster_links_pinned_aux_vars() {
        let script = Script::parse(
            "(assert (and (or (= x 0) (= x 1)) (= y 0)))\n(check-sat)\n",
        )
        .unwrap();
        let asserts = collect_assert_terms(&script);
        let choices = collect_choices(&asserts, 3);
        let cluster = flag_cluster(&int_const("x"), &asserts, &choices);
        assert_eq!(
            cluster,
            HashSet::from([int_const("x"), int_const("y")])
        );
    }

    #[test]
    fn excludes_singleton_via_bounds() {
        if !has_z3() {
            return;
        }
        std::env::set_var("SIMPLIFIER_FIELD_MOD", "2013265921");
        let script = Script::parse(
            "(declare-fun x () Int)\n(assert (and (or (= x 0) (= x 1)) (<= 1 x) (<= x 1)))\n(check-sat)\n",
        )
        .unwrap();
        let (out, stats) = apply(&script).unwrap();
        assert!(stats["added_facts"].as_u64().unwrap() >= 1);
        let s = smt2::dump_string(&out);
        assert!(s.contains("(not (= x 0))"));
    }

    #[test]
    fn binary_disjunction_no_facts() {
        if !has_z3() {
            return;
        }
        let script = Script::parse(
            "(declare-fun x () Int)\n(assert (or (= x 0) (= x 1)))\n(check-sat)\n",
        )
        .unwrap();
        let (out, stats) = apply(&script).unwrap();
        assert_eq!(stats["added_facts"], 0);
        assert_eq!(
            out.commands.iter().filter(|c| c.name() == "assert").count(),
            1
        );
    }
}
