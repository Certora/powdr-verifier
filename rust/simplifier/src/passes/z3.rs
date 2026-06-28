//! Z3 tactic simplification over SMT-LIB scripts.

use std::collections::{BTreeMap, HashSet};

use smt2::{parse::Command, splice_z3_result, Script, Term};
use z3::{SatResult, Tactic};

use crate::passes::skolem::term_util::{free_variables, swap_prefix, symbol_sort};
use crate::passes::skolem::types::SortKind;
use crate::passes::skolem::utils::{collect_symbol_sorts, declare_fun_name};

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

fn sort_kind_to_smt(sort: SortKind) -> &'static str {
    match sort {
        SortKind::Bool => "Bool",
        SortKind::Array => "(Array Int Int)",
        SortKind::Int | SortKind::Other => "Int",
    }
}

fn infer_free_symbol_sort(
    name: &str,
    sorts: &std::collections::HashMap<String, SortKind>,
) -> SortKind {
    if sorts.contains_key(name) {
        return symbol_sort(name, sorts);
    }
    if let Some(swapped) = swap_prefix(name) {
        if sorts.contains_key(&swapped) {
            return symbol_sort(&swapped, sorts);
        }
    }
    if name.contains("memory_is") {
        return SortKind::Bool;
    }
    SortKind::Int
}

/// Declare symbols free in ``assert`` bodies but missing from ``declare-fun``.
/// Mirrors Python ``_ensure_declarations_for_asserts`` before Z3 sees the script.
fn ensure_assert_declarations(script: &Script) -> Result<(Script, usize), String> {
    let mut sorts = collect_symbol_sorts(script);
    let declared: HashSet<String> = script
        .commands
        .iter()
        .filter(|c| c.name() == "declare-fun")
        .filter_map(|c| declare_fun_name(&c.raw))
        .collect();
    let mut missing: BTreeMap<String, SortKind> = BTreeMap::new();
    for cmd in &script.commands {
        if cmd.name() != "assert" {
            continue;
        }
        let Some(body) = smt2::term::assert_body(&cmd.raw) else {
            continue;
        };
        let term = Term::parse(&body)?;
        for sym in free_variables(&term) {
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
        .position(|c| c.name() == "assert")
        .ok_or("missing assert")?;
    let decl_cmds: Vec<Command> = missing
        .iter()
        .map(|(name, sort)| {
            Command::new(format!(
                "(declare-fun {name} () {})",
                sort_kind_to_smt(*sort)
            ))
        })
        .collect();
    let n = decl_cmds.len();
    let mut commands = script.commands.clone();
    commands.splice(first_assert..first_assert, decl_cmds);
    Ok((Script::from_commands(commands), n))
}

pub fn apply(script: &Script, tactic_args: &[String]) -> Result<(Script, serde_json::Value), String> {
    let (script, ensured_decls) = ensure_assert_declarations(script)?;
    let parts = script.split_at_check_sat()?;
    let asserts_in = parts.asserts_in();
    let z3_input = parts.z3_input_string();

    let tactic = build_tactic(tactic_args);
    let solver = tactic.solver();
    solver.from_string(z3_input.as_bytes());
    let z3_check = solver.check();

    let processed_str = solver.to_string();
    let processed = Script::parse(&processed_str)?;

    let prefix_names = smt2::declared_symbol_names(&parts.prefix);
    let extra = smt2::extra_declarations(&processed.commands, &prefix_names);
    let new_asserts = smt2::asserts_excluding_true(&processed.commands);

    let out = splice_z3_result(&parts, &processed.commands);
    let stats = serde_json::json!({
        "backend": "rust",
        "z3_check": sat_result_str(z3_check),
        "asserts_in": asserts_in,
        "asserts_out": new_asserts.len(),
        "extra_declarations": extra.len(),
        "ensured_declarations": ensured_decls,
        "tactic_args": if tactic_args.is_empty() { serde_json::Value::Null } else { serde_json::json!(tactic_args) },
    });
    Ok((out, stats))
}
