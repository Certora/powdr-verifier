//! Z3 tactic simplification over SMT-LIB scripts.

use std::collections::{BTreeMap, HashSet};

use smt2::{
    asserts_excluding_true, declare_fun_name_cmd, declared_symbol_names,
    extra_declarations, free_variables_bool, parse_single_command, splice_z3_result,
    Script,
};
use z3::{SatResult, Tactic};

use crate::expr_util::AssertBuildCtx;

const DEFAULT_TACTICS: &[&str] = &[
    "propagate-values",
    "elim-term-ite",
    "propagate-ineqs",
    "solve-eqs",
    "ctx-simplify",
];

const REPEAT_MAX: u32 = 1024;

pub fn build_tactic(tactic_args: &[String]) -> Tactic {
    let base = match tactic_args {
        [] => {
            let mut chain = Tactic::new(DEFAULT_TACTICS[0]);
            for name in &DEFAULT_TACTICS[1..] {
                let next = Tactic::new(name);
                chain = chain.and_then(&next);
            }
            Tactic::repeat(&chain, REPEAT_MAX)
        }
        [single] => Tactic::new(single),
        many => {
            let mut chain = Tactic::new(&many[0]);
            for name in &many[1..] {
                let next = Tactic::new(name);
                chain = chain.and_then(&next);
            }
            chain
        }
    };
    base
}

fn sat_result_str(r: SatResult) -> &'static str {
    match r {
        SatResult::Sat => "sat",
        SatResult::Unsat => "unsat",
        SatResult::Unknown => "unknown",
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum DeclSort {
    Int,
    Bool,
    Array,
}

fn sort_kind_to_smt(sort: DeclSort) -> &'static str {
    match sort {
        DeclSort::Bool => "Bool",
        DeclSort::Array => "(Array Int Int)",
        DeclSort::Int => "Int",
    }
}

fn infer_free_symbol_sort(name: &str, sorts: &std::collections::HashMap<String, DeclSort>) -> DeclSort {
    if let Some(sort) = sorts.get(name) {
        return *sort;
    }
    if let Some(swapped) = smt2::swap_prefix(name) {
        if let Some(sort) = sorts.get(&swapped) {
            return *sort;
        }
    }
    if name.contains("memory_is") {
        return DeclSort::Bool;
    }
    DeclSort::Int
}

fn is_let_temp_symbol(name: &str) -> bool {
    let Some(rest) = name.strip_prefix("a!") else {
        return false;
    };
    !rest.is_empty() && rest.chars().all(|c| c.is_ascii_digit())
}

/// Declare symbols free in ``assert`` bodies but missing from ``declare-fun``.
/// Mirrors Python ``_ensure_declarations_for_asserts`` before Z3 sees the script.
fn ensure_assert_declarations(script: &Script) -> Result<(Script, usize), String> {
    let mut build = AssertBuildCtx::from_script(script)?;
    let mut sorts = collect_symbol_sorts(script);
    let declared: HashSet<String> = script
        .commands
        .iter()
        .filter_map(declare_fun_name_cmd)
        .collect();
    let mut missing: BTreeMap<String, DeclSort> = BTreeMap::new();
    for cmd in &script.commands {
        let Some(body) = cmd.assert_bool() else {
            continue;
        };
        for sym in free_variables_bool(body) {
            if is_let_temp_symbol(&sym) {
                continue;
            }
            if declared.contains(&sym) || missing.contains_key(&sym) {
                continue;
            }
            let sort = infer_free_symbol_sort(&sym, &sorts);
            missing.insert(sym.clone(), sort);
            sorts.insert(sym, sort);
        }
    }
    if missing.is_empty() {
        return Ok((script.clone(), 0));
    }
    let first_assert = script
        .commands
        .iter()
        .position(|c| c.assert_bool().is_some())
        .ok_or("missing assert")?;
    let mut decl_cmds = Vec::new();
    for (name, sort) in &missing {
        let raw = format!("(declare-fun {name} () {})", sort_kind_to_smt(*sort));
        let cmd = parse_single_command(&raw, build.parse())?;
        decl_cmds.push(cmd);
    }
    let n = decl_cmds.len();
    let mut commands = script.commands.clone();
    commands.splice(first_assert..first_assert, decl_cmds);
    Ok((Script::from_commands(&script.source, commands), n))
}

pub fn apply(script: &Script, tactic_args: &[String]) -> Result<(Script, serde_json::Value), String> {
    let (script, ensured_decls) = ensure_assert_declarations(script)?;
    let parts = script.split_at_check_sat()?;
    let asserts_in = parts.asserts_in();
    let z3_input = parts.z3_input_string(&script.source);

    let tactic = build_tactic(tactic_args);
    let solver = tactic.solver();
    solver.from_string(z3_input.as_bytes());
    let z3_check = solver.check();

    let processed_str = solver.to_string();
    let processed = Script::parse(&processed_str)?;

    let prefix_names = declared_symbol_names(&parts.prefix);
    let extra = extra_declarations(&processed.commands, &prefix_names);
    let new_asserts = asserts_excluding_true(&processed.commands);

    let out = splice_z3_result(&parts, &processed.commands, &script.source);
    let stats = serde_json::json!({
        "backend": "rust",
        "z3_version": z3::full_version(),
        "z3_check": sat_result_str(z3_check),
        "asserts_in": asserts_in,
        "asserts_out": new_asserts.len(),
        "extra_declarations": extra.len(),
        "ensured_declarations": ensured_decls,
        "tactic_args": if tactic_args.is_empty() { serde_json::Value::Null } else { serde_json::json!(tactic_args) },
    });
    Ok((out, stats))
}

fn sort_from_decl(raw: &str) -> DeclSort {
    if raw.contains("(Array") || raw.contains(" Array ") {
        DeclSort::Array
    } else if raw.contains("Bool") {
        DeclSort::Bool
    } else {
        DeclSort::Int
    }
}

fn collect_symbol_sorts(script: &Script) -> std::collections::HashMap<String, DeclSort> {
    let mut out = std::collections::HashMap::new();
    for cmd in &script.commands {
        if let Some(name) = declare_fun_name_cmd(cmd) {
            let raw = cmd.to_smtlib(&script.source);
            out.insert(name, sort_from_decl(&raw));
        }
    }
    out
}
