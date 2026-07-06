//! Pretty-print ``assert`` commands (Python ``pretty`` tactic).

use smt2::{pretty_print_script, Script};

pub fn apply(script: &Script) -> Result<(Script, serde_json::Value), String> {
    let asserts = smt2::assert_commands(script).len();
    let out = pretty_print_script(script)?;
    let stats = serde_json::json!({ "asserts": asserts, "pretty": true });
    Ok((out, stats))
}
