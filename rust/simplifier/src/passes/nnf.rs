//! NNF via Z3 ``nnf`` tactic.

use smt2::{splice_z3_result, Script};
use z3::{SatResult, Tactic};

fn sat_result_str(r: SatResult) -> &'static str {
    match r {
        SatResult::Sat => "sat",
        SatResult::Unsat => "unsat",
        SatResult::Unknown => "unknown",
    }
}

pub fn apply(script: &Script) -> Result<(Script, serde_json::Value), String> {
    let parts = script.split_at_check_sat()?;
    let asserts_in = parts.asserts_in();
    let z3_input = parts.z3_input_string();

    let tactic = Tactic::new("nnf");
    let solver = tactic.solver();
    solver.from_string(z3_input.as_bytes());
    let z3_check = solver.check();

    let processed_str = solver.to_string();
    let processed = Script::parse(&processed_str)?;

    let out = splice_z3_result(&parts, &processed.commands);
    let new_asserts = smt2::asserts_excluding_true(&processed.commands);
    let changed = asserts_in; // conservative; Z3 may rewrite all asserts
    let stats = serde_json::json!({
        "asserts": asserts_in,
        "asserts_changed": changed.min(new_asserts.len()),
        "z3_check": sat_result_str(z3_check),
    });
    Ok((out, stats))
}
