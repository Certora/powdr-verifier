//! Quantifier-freedom check on asserts.

use smt2::Script;
use z3::ast::{Ast, AstKind, Bool};

pub fn apply(script: &Script) -> Result<(Script, serde_json::Value), String> {
    let parts = script.split_at_check_sat()?;
    let z3_input = parts.z3_input_string();

    let solver = z3::Solver::new();
    solver.from_string(z3_input.as_bytes());

    let mut is_qf = true;
    for a in solver.get_assertions() {
        if has_quantifier(&a) {
            is_qf = false;
            break;
        }
    }

    let result = if is_qf { "qf" } else { "not-qf" };
    let stats = serde_json::json!({
        "expected": "qf",
        "result": result,
    });
    Ok((script.clone(), stats))
}

fn has_quantifier(ast: &Bool) -> bool {
    if ast.kind() == AstKind::Quantifier {
        return true;
    }
    for c in ast.children() {
        if let Some(b) = c.as_bool() {
            if has_quantifier(&b) {
                return true;
            }
        }
    }
    false
}
