//! Constant folding on assert bodies (no Z3 simplify).

use smt2::{map_asserts, Script, Term};

fn field_mod() -> Option<u64> {
    std::env::var("SIMPLIFIER_FIELD_MOD")
        .ok()
        .and_then(|s| s.parse().ok())
}

pub fn apply(script: &Script) -> Result<(Script, serde_json::Value), String> {
    let total = smt2::assert_commands(script).len();
    let mut changed = 0usize;
    let field_mod = field_mod();
    let out = map_asserts(script, |body| {
        let term = Term::parse(body)?;
        let folded = smt2::fold_constants_fixpoint(&term, field_mod, 3);
        let new_body = folded.to_string();
        if new_body != body {
            changed += 1;
        }
        Ok(new_body)
    })?;
    let stats = serde_json::json!({
        "asserts_total": total,
        "asserts_changed": changed,
    });
    Ok((out, stats))
}
