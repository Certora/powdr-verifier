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

pub fn find_largest_or_goal(asserts: &[Bool]) -> Option<(usize, Vec<Bool>)> {
    let mut best: Option<(usize, Vec<Bool>)> = None;
    for (i, b) in asserts.iter().enumerate() {
        let Some(parts) = or_body_parts(b) else {
            continue;
        };
        if parts.len() < 2 {
            continue;
        }
        if best.as_ref().map(|(_, p)| parts.len() > p.len()).unwrap_or(true) {
            best = Some((i, parts));
        }
    }
    best
}
