//! Pretty-print ``assert`` commands (Python ``pretty`` tactic).

use smt2::{has_quantifier, pretty_print_script, Script};

pub fn apply(script: &Script) -> Result<(Script, serde_json::Value), String> {
    let asserts = smt2::assert_commands(script).len();
    let quantified = script.commands.iter().any(|cmd| {
        cmd.assert_bool()
            .is_some_and(has_quantifier)
    });
    if quantified {
        return Ok((
            script.clone(),
            serde_json::json!({ "asserts": asserts, "pretty": false, "skipped": "quantifiers" }),
        ));
    }
    let out = pretty_print_script(script)?;
    let stats = serde_json::json!({ "asserts": asserts, "pretty": true });
    Ok((out, stats))
}
