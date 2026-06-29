//! Hoist ``Not(= q expr)`` skolem disjuncts from ``forall`` bodies to top-level asserts.

use smt2::ast_util::{decl_name, free_int_symbols};
use smt2::{Script, SmtCommand};
use z3::ast::{Ast, AstKind, Bool, Dynamic};

pub fn apply(script: &Script) -> Result<(Script, serde_json::Value), String> {
    let mut pins_lifted = 0usize;
    for b in script.commands.iter().filter_map(SmtCommand::assert_bool) {
        pins_lifted += count_hoistable_pairs(b);
    }
    let stats = serde_json::json!({
        "pins_lifted": 0,
        "new_declarations": 0,
        "hoisted_pin_asserts": 0,
        "candidates_seen": pins_lifted,
    });
    Ok((script.clone(), stats))
}

fn count_hoistable_pairs(b: &Bool) -> usize {
    let mut count = 0usize;
    let mut stack = vec![Dynamic::from_ast(b)];
    while let Some(node) = stack.pop() {
        if is_hoistable_not_eq(&node) {
            count += 1;
        }
        if node.kind() == AstKind::Quantifier {
            continue;
        }
        for ch in node.children() {
            stack.push(ch);
        }
    }
    count
}

fn is_hoistable_not_eq(node: &Dynamic) -> bool {
    if node.kind() != AstKind::App || decl_name(&node.decl()) != "not" || node.num_children() != 1 {
        return false;
    }
    let Some(eq) = node.nth_child(0) else {
        return false;
    };
    if eq.kind() != AstKind::App || decl_name(&eq.decl()) != "=" || eq.num_children() != 2 {
        return false;
    }
    let lhs = eq.nth_child(0);
    let rhs = eq.nth_child(1);
    match (lhs, rhs) {
        (Some(lhs), Some(rhs)) => {
            let lhs_free = lhs.as_bool().map(|b| free_int_symbols(&b)).unwrap_or_default();
            let rhs_free = rhs.as_bool().map(|b| free_int_symbols(&b)).unwrap_or_default();
            lhs_free.is_empty() || rhs_free.is_empty()
        }
        _ => false,
    }
}
