//! Constant folding on assert bodies (no Z3 simplify).

use smt2::{map_asserts, Script};
use z3::ast::Bool;

use crate::fold::fold_constants_fixpoint;

fn field_mod() -> Option<u64> {
    std::env::var("SIMPLIFIER_FIELD_MOD")
        .ok()
        .and_then(|s| s.parse().ok())
}

pub fn apply(script: &Script) -> Result<(Script, serde_json::Value), String> {
    let total = smt2::assert_commands(script).len();
    let mut changed = 0usize;
    let field_mod = field_mod();
    let out = map_asserts(script, |b: &Bool| {
        let folded = fold_constants_fixpoint(b, field_mod, 3);
        if folded.to_string() != b.to_string() {
            changed += 1;
        }
        Ok(folded)
    })?;
    let stats = serde_json::json!({
        "asserts_total": total,
        "asserts_changed": changed,
    });
    Ok((out, stats))
}
