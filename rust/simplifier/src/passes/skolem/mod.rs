pub(crate) mod ast_build;
mod derived;
mod isolate;
mod map;
mod names;
mod rules;
pub(crate) mod types;
pub(crate) mod utils;
mod witness;

use std::collections::{HashMap, HashSet};

use smt2::ast_util::{is_forall, or_body_parts, rebuild_quantifier_dyn};
use smt2::{map_asserts, map_bool_children, Script};
use z3::ast::{Ast, AstKind, Bool, Dynamic, Int};

use crate::expr_util::AssertBuildCtx;
use self::ast_build::field_mod;
use self::map::SkolemMap;
use self::types::SortKind;
use self::utils::{
    collect_declared_symbols, collect_symbol_sorts, declare_fun_block, load_skolem_setinfos,
    parse_forall,
};

const SKOLEM_SETINFO_PREFIX: &str = ":skolem-";

pub fn apply(script: &Script) -> Result<(Script, serde_json::Value), String> {
    let field = field_mod();
    let declared = collect_declared_symbols(script);
    let sorts = collect_symbol_sorts(script);
    let (pins, pins_dropped_not_live) = load_skolem_setinfos(script);
    let candidates = field
        .map(|p| witness::collect_candidates(script, p))
        .unwrap_or_default();
    let decl_block = declare_fun_block(script);

    let mut applied: HashMap<String, usize> = HashMap::new();
    let mut qvar_sets: Vec<HashSet<String>> = Vec::new();

    let out = map_asserts(script, |body| {
        Ok(walk_assert(
            script,
            body,
            &declared,
            &sorts,
            &pins,
            &candidates,
            &decl_block,
            field,
            &mut applied,
            &mut qvar_sets,
        ))
    })?;

    let all_qvars: HashSet<String> = qvar_sets.iter().flatten().cloned().collect();
    let free_pins = if let Some(p) = field {
        rules::contribute_free(&out, &all_qvars, p)
    } else {
        Vec::new()
    };
    if !free_pins.is_empty() {
        applied.insert("rules-free".to_string(), free_pins.len());
    }

    let mut commands = out.commands.clone();
    if !free_pins.is_empty() {
        let insert_idx = out
            .commands
            .iter()
            .position(|c| c.name() == "check-sat")
            .unwrap_or(out.commands.len());
        let mut new_cmds = Vec::with_capacity(out.commands.len() + free_pins.len());
        let mut build = AssertBuildCtx::from_script(&out)?;
        new_cmds.extend(out.commands[..insert_idx].iter().cloned());
        for (var, expr) in free_pins {
            let eq = if let Some(i) = expr.as_int() {
                Int::new_const(var.as_str()).eq(&i)
            } else if let Some(b) = expr.as_bool() {
                Bool::new_const(var.as_str()).eq(&b)
            } else {
                continue;
            };
            build.push_assert(&mut new_cmds, &eq)?;
        }
        new_cmds.extend(out.commands[insert_idx..].iter().cloned());
        commands = new_cmds;
    }

    commands.retain(|cmd| {
        if cmd.name() != "set-info" {
            return true;
        }
        !cmd.to_smtlib(&out.source).contains(SKOLEM_SETINFO_PREFIX)
    });

    let out = Script::from_commands(&out.source, commands);

    let stats = serde_json::json!({
        "pins_by_source": applied,
        "free_value_asserts": applied.get("rules-free").copied().unwrap_or(0),
        "pins_dropped_not_live": pins_dropped_not_live,
    });
    Ok((out, stats))
}

fn walk_assert(
    script: &Script,
    term: &Bool,
    declared: &HashMap<String, String>,
    sorts: &HashMap<String, SortKind>,
    pins: &[types::SkolemPin],
    candidates: &[witness::WitnessCandidate],
    decl_block: &str,
    field: Option<i128>,
    applied: &mut HashMap<String, usize>,
    qvar_sets: &mut Vec<HashSet<String>>,
) -> Bool {
    walk_assert_dyn(
        script,
        &Dynamic::from_ast(term),
        declared,
        sorts,
        pins,
        candidates,
        decl_block,
        field,
        applied,
        qvar_sets,
    )
    .as_bool()
    .unwrap_or_else(|| term.clone())
}

fn walk_assert_dyn(
    script: &Script,
    term: &Dynamic,
    declared: &HashMap<String, String>,
    sorts: &HashMap<String, SortKind>,
    pins: &[types::SkolemPin],
    candidates: &[witness::WitnessCandidate],
    decl_block: &str,
    field: Option<i128>,
    applied: &mut HashMap<String, usize>,
    qvar_sets: &mut Vec<HashSet<String>>,
) -> Dynamic {
    if term.kind() == AstKind::Quantifier {
        if is_forall(term) {
            return Dynamic::from_ast(&walk_forall(
                script,
                term,
                declared,
                sorts,
                pins,
                candidates,
                decl_block,
                field,
                applied,
                qvar_sets,
            ));
        }
        let bounds = smt2::quantifier_bounds(term);
        let Some(body) = smt2::quantifier_body_bool(term) else {
            return term.clone();
        };
        let body = walk_assert(
            script,
            &body,
            declared,
            sorts,
            pins,
            candidates,
            decl_block,
            field,
            applied,
            qvar_sets,
        );
        return Dynamic::from_ast(&rebuild_quantifier_dyn(false, &bounds, &body));
    }
    if let Some(b) = term.as_bool() {
        return Dynamic::from_ast(&map_bool_children(&b, &mut |child| {
            walk_assert(
                script,
                child,
                declared,
                sorts,
                pins,
                candidates,
                decl_block,
                field,
                applied,
                qvar_sets,
            )
        }));
    }
    term.clone()
}

fn walk_forall(
    script: &Script,
    term: &Dynamic,
    declared: &HashMap<String, String>,
    sorts: &HashMap<String, SortKind>,
    pins: &[types::SkolemPin],
    candidates: &[witness::WitnessCandidate],
    decl_block: &str,
    field: Option<i128>,
    applied: &mut HashMap<String, usize>,
    qvar_sets: &mut Vec<HashSet<String>>,
) -> Bool {
    let Some((qvars, bounds, body)) = parse_forall(term) else {
        return term.as_bool().unwrap_or_else(|| Bool::from_bool(true));
    };
    qvar_sets.push(qvars.iter().map(|(n, _)| n.clone()).collect());

    let body = crate::passes::lift::name_debruijn_bool(&body, term, script)
        .unwrap_or_else(|_| body.clone());

    let mut skolem = SkolemMap::new(&qvars);
    names::contribute(&mut skolem, declared, sorts);
    derived::contribute(&mut skolem, pins);
    if let Some(p) = field {
        witness::contribute(&mut skolem, &body, candidates, p);
    }
    isolate::contribute(
        &mut skolem,
        &body,
        sorts,
        decl_block,
        &qvars.iter().map(|(n, _)| n.clone()).collect::<Vec<_>>(),
    );

    for src in skolem.sources.values() {
        *applied.entry(src.clone()).or_insert(0) += 1;
    }

    let disjuncts = skolem.emit_disjuncts();
    if disjuncts.is_empty() {
        return term.as_bool().unwrap_or_else(|| Bool::from_bool(true));
    }

    let new_body = if let Some(mut args) = or_body_parts(&body) {
        args.extend(disjuncts);
        Bool::or(&args.iter().collect::<Vec<_>>())
    } else {
        let mut args = vec![body];
        args.extend(disjuncts);
        Bool::or(&args.iter().collect::<Vec<_>>())
    };

    rebuild_quantifier_dyn(true, &bounds, &new_body)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn skolem_applies_memory_bus_pins() {
        std::env::set_var("SIMPLIFIER_FIELD_MOD", "2013265921");
        let script = Script::parse(
            "(declare-fun after-memory_isinput_0 () Bool)\n\
             (declare-fun after-memory_isoutput_0 () Bool)\n\
             (set-info :skolem-memory-bus-0 |(= before-memory_isinput_0 after-memory_isinput_0)|)\n\
             (set-info :skolem-memory-bus-1 |(= before-memory_isoutput_0 after-memory_isoutput_0)|)\n\
             (assert (forall ((before-memory_isinput_0 Bool) (before-memory_isoutput_0 Bool)) \
               (or (= before-memory_isinput_0 after-memory_isinput_0) \
                   (= before-memory_isoutput_0 after-memory_isoutput_0))))\n\
             (check-sat)\n",
        )
        .unwrap();
        let (out, stats) = apply(&script).unwrap();
        assert!(
            stats["pins_by_source"]["memory_bus"]
                .as_u64()
                .unwrap_or(0)
                >= 2
        );
        let s = smt2::dump_string(&out);
        assert!(s.contains("not (= before-memory_isinput_0 after-memory_isinput_0)"));
        assert!(s.contains("not (= before-memory_isoutput_0 after-memory_isoutput_0)"));
    }

    #[test]
    fn pins_same_name_program_var() {
        let script = Script::parse(
            "(declare-fun before-x@0 () Int)\n\
             (declare-fun after-x@0 () Int)\n\
             (assert (forall ((before-x@0 Int)) (or (= before-x@0 0))))\n\
             (check-sat)\n",
        )
        .unwrap();
        std::env::set_var("SIMPLIFIER_FIELD_MOD", "2147483647");
        let (out, stats) = apply(&script).unwrap();
        let s = smt2::dump_string(&out);
        assert!(s.contains("(not (= before-x@0"));
        assert!(stats["pins_by_source"]["names"].as_u64().unwrap_or(0) >= 1);
    }

    #[test]
    fn forall_body_or_body_parts_after_nnf() {
        use smt2::ast_util::{or_body_parts, or_parts};
        use smt2::iter_nodes_dyn;
        use super::utils::parse_forall;
        std::env::set_var("SIMPLIFIER_FIELD_MOD", "2013265921");
        let raw = std::fs::read_to_string(
            "/home/gereon/certora/powdr/verifier/data/guest-keccak-selection/verify-apc_candidate_2105892_035_inlining-apc_candidate_2105892_036_remove_disconnected.soundness.smt2",
        )
        .unwrap();
        let script = Script::parse(&raw).unwrap();
        let (nnf, _) = crate::passes::nnf::apply(&script).unwrap();
        let top = nnf.commands.iter().find_map(|c| c.assert_bool()).unwrap();
        let mut body = None;
        for node in iter_nodes_dyn(&Dynamic::from_ast(top)) {
            if let Some((qvars, _, b)) = parse_forall(&node) {
                if qvars.iter().any(|(n, _)| n.contains("rs1_aux_cols__base__timestamp_lt_aux__lower_decomp__0_1@24")) {
                    body = Some(b);
                    break;
                }
            }
        }
        let body = body.expect("inner forall");
        let ast = Dynamic::from_ast(&body);
        let head = if ast.kind() == AstKind::App {
            smt2::ast_util::decl_name(&ast.decl())
        } else {
            format!("{:?}", ast.kind())
        };
        assert!(
            or_body_parts(&body).is_some(),
            "head={head} or_parts={:?}",
            or_parts(&body).map(|v| v.len())
        );
    }

    #[test]
    fn keccak_2104736_witness_pins_diff_inv_markers() {
        use smt2::dump_string;
        std::env::set_var("SIMPLIFIER_FIELD_MOD", "2013265921");
        let raw = std::fs::read_to_string(
            "/home/gereon/certora/powdr/verifier/data/guest-keccak-selection/verify-apc_candidate_2104736_008_trivial_simp-apc_candidate_2104736_009_rule_based.soundness.smt2",
        )
        .unwrap();
        let script = Script::parse(&raw).unwrap();
        let (nnf, _) = crate::passes::nnf::apply(&script).unwrap();
        let field = 2013265921i128;
        let cands = witness::collect_candidates(&nnf, field);
        assert!(!cands.is_empty(), "no witness candidates");
        let (sk, stats) = apply(&nnf).unwrap();
        let witness = stats["pins_by_source"].get("witness");
        let s = dump_string(&sk);
        assert!(
            s.contains("(not (= before-diff_inv_marker__0_4@168"),
            "missing witness pin disjuncts; witness={witness:?} candidates={}",
            cands.len()
        );
    }

    #[test]
    fn keccak_2106348_isolate_pins_reads_aux() {
        use smt2::dump_string;
        std::env::set_var("SIMPLIFIER_FIELD_MOD", "2013265921");
        let raw = std::fs::read_to_string(
            "/home/gereon/certora/powdr/verifier/data/guest-keccak-selection/verify-apc_candidate_2106348_035_inlining-apc_candidate_2106348_036_remove_disconnected.soundness.smt2",
        )
        .unwrap();
        let script = Script::parse(&raw).unwrap();
        let (nnf, _) = crate::passes::nnf::apply(&script).unwrap();
        let (sk, stats) = apply(&nnf).unwrap();
        let isolate = stats["pins_by_source"].get("isolate");
        let s = dump_string(&sk);
        assert!(
            s.contains("before-reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_1@25 (mod 0"),
            "missing reads_aux__0 isolate pin; isolate={isolate:?}"
        );
    }

    #[test]
    fn witness_contribute_handles_quantifier_bound_vars() {
        std::env::set_var("SIMPLIFIER_FIELD_MOD", "2013265921");
        let script = Script::parse(
            "(declare-fun marker () Int)\n\
             (assert (forall ((p Bool) (q Int)) \
               (or p (= (mod (* q marker) 2013265921) 0))))\n\
             (check-sat)\n",
        )
        .unwrap();
        let (script, _) = crate::passes::nnf::apply(&script).unwrap();
        apply(&script).expect("skolem must not panic on quantifier bound vars");
    }
}
