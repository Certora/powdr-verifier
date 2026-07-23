use z3::ast::{Ast, Bool};
use z3::{AstKind, DeclKind};

fn peel_annotation(b: &Bool) -> Bool {
    if b.kind() == AstKind::App && b.decl().name() == "!" && b.num_children() == 1 {
        if let Some(inner) = b.nth_child(0).and_then(|c| c.as_bool()) {
            return peel_annotation(&inner);
        }
    }
    b.clone()
}

pub fn or_body_parts(b: &Bool) -> Option<Vec<Bool>> {
    let b = peel_annotation(b);
    if b.kind() == AstKind::App && b.decl().kind() == DeclKind::Or {
        return Some(
            b.children()
                .into_iter()
                .filter_map(|c| c.as_bool())
                .collect(),
        );
    }
    None
}

/// Flatten every assertion through top-level `And` into a flat conjunct list.
/// `(assert (and a b c))` contributes `a`, `b`, `c` individually, recursively.
fn flatten_conjuncts(asserts: &[Bool]) -> Vec<Bool> {
    let mut conjuncts: Vec<Bool> = Vec::new();
    let mut stack: Vec<Bool> = asserts.iter().cloned().collect();
    while let Some(f) = stack.pop() {
        let f = peel_annotation(&f);
        if f.kind() == AstKind::App && f.decl().kind() == DeclKind::And {
            for c in f.children().into_iter().filter_map(|c| c.as_bool()) {
                stack.push(c);
            }
        } else {
            conjuncts.push(f);
        }
    }
    conjuncts
}

/// Find the largest `Or` to split the check on, returning
/// `(context_without_goal, goal_disjuncts)`. Assertions are flattened through
/// `And` first, so a goal `Or` nested inside a top-level `(assert (and ...))`
/// (the usual VC shape `And(before.C, Or(¬after ∨ ¬io))`) is found and split,
/// not just a bare top-level `(assert (or ...))`.
pub fn find_largest_or_goal(asserts: &[Bool]) -> Option<(Vec<Bool>, Vec<Bool>)> {
    let conjuncts = flatten_conjuncts(asserts);
    let mut best: Option<(usize, Vec<Bool>)> = None;
    for (i, c) in conjuncts.iter().enumerate() {
        let Some(parts) = or_body_parts(c) else {
            continue;
        };
        if parts.len() < 2 {
            continue;
        }
        if best.as_ref().map(|(_, p)| parts.len() > p.len()).unwrap_or(true) {
            best = Some((i, parts));
        }
    }
    let (goal_idx, disjuncts) = best?;
    let context: Vec<Bool> = conjuncts
        .into_iter()
        .enumerate()
        .filter_map(|(i, c)| (i != goal_idx).then_some(c))
        .collect();
    Some((context, disjuncts))
}
