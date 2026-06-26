//! Z3 tactic simplification over SMT-LIB scripts.

use smt2::{splice_z3_result, Script};
use z3::{SatResult, Tactic};

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

pub fn apply(script: &Script, tactic_args: &[String]) -> Result<(Script, serde_json::Value), String> {
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
        "tactic_args": if tactic_args.is_empty() { serde_json::Value::Null } else { serde_json::json!(tactic_args) },
    });
    Ok((out, stats))
}
