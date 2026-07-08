//! Collapsed/expanded witness pass on Z3 AST.

use smt2::ast_util::unwrap_zero_mod_eq;
use smt2::{Script, SmtCommand};
use z3::ast::{Ast, AstKind, Dynamic};

pub fn apply(script: &Script) -> Result<(Script, serde_json::Value), String> {
    let field = std::env::var("SIMPLIFIER_FIELD_MOD")
        .ok()
        .and_then(|s| s.parse::<i128>().ok())
        .ok_or("SIMPLIFIER_FIELD_MOD not set")?;
    let candidates = count_candidates(script, field);
    Ok((
        script.clone(),
        serde_json::json!({ "witness_candidates": candidates }),
    ))
}

fn count_candidates(script: &Script, field: i128) -> usize {
    script
        .commands
        .iter()
        .filter_map(SmtCommand::assert_bool)
        .map(|b| {
            let mut count = 0usize;
            let mut stack = vec![Dynamic::from_ast(b)];
            while let Some(node) = stack.pop() {
                if let Some(nb) = node.as_bool() {
                    if unwrap_zero_mod_eq(&nb, field).is_some() {
                        count += 1;
                    }
                }
                if node.kind() == AstKind::Quantifier {
                    continue;
                }
                for ch in node.children() {
                    stack.push(ch);
                }
            }
            count
        })
        .sum()
}
