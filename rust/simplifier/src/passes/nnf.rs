//! NNF conversion (Python ``NNFConverter`` parity; preserves ``=`` / iff).

use smt2::{
    flatten_and, flatten_or, is_implies, is_not, map_asserts_opt, map_bool_children_opt,
    strip_annotations_opt, Script,
};
use z3::ast::Bool;

pub fn apply(script: &Script) -> Result<(Script, serde_json::Value), String> {
    let mut changed = 0usize;
    let out = map_asserts_opt(script, |b| {
        let nnf = convert_to_nnf_opt(b);
        if nnf.is_some() {
            changed += 1;
        }
        Ok(nnf)
    })?;
    let stats = serde_json::json!({
        "commands": script.commands.len(),
        "commands_changed": changed,
    });
    Ok((out, stats))
}

fn convert_to_nnf(b: &Bool) -> Bool {
    convert_to_nnf_opt(b).unwrap_or_else(|| b.clone())
}

/// Identity-preserving NNF conversion: returns ``None`` when ``b`` is already in
/// NNF (no annotations, no negation/implication to push), so callers avoid
/// rebuilding and re-hashing unchanged subtrees.
fn convert_to_nnf_opt(b: &Bool) -> Option<Bool> {
    let stripped_opt = strip_annotations_opt(b);
    let stripped = stripped_opt.as_ref().unwrap_or(b);
    if let Some(inner) = is_not(stripped) {
        return Some(negate(&inner));
    }
    if let Some((a, c)) = is_implies(stripped) {
        return Some(flatten_or(vec![negate(&a), convert_to_nnf(&c)]));
    }
    match map_bool_children_opt(stripped, &mut convert_to_nnf_opt) {
        Some(rebuilt) => Some(rebuilt),
        None => stripped_opt,
    }
}

fn negate(b: &Bool) -> Bool {
    let peeled = strip_annotations_opt(b);
    let b = peeled.as_ref().unwrap_or(b);
    if let Some(inner) = is_not(b) {
        return convert_to_nnf(&inner);
    }
    if let Some(parts) = smt2::and_parts(b) {
        let args: Vec<Bool> = parts.iter().map(negate).collect();
        return flatten_or(args);
    }
    if let Some(parts) = smt2::or_parts(b) {
        let args: Vec<Bool> = parts.iter().map(negate).collect();
        return flatten_and(args);
    }
    if let Some((a, c)) = is_implies(b) {
        return flatten_and(vec![convert_to_nnf(&a), negate(&c)]);
    }
    b.not()
}

#[cfg(test)]
mod tests {
    use super::*;
    use smt2::ParseCtx;

    fn parse_assert(s: &str) -> Bool {
        let mut ctx = ParseCtx::new();
        smt2::parse_bool_formula(&mut ctx, s).unwrap()
    }

    #[test]
    fn implies() {
        let t = parse_assert("(=> a b)");
        assert_eq!(convert_to_nnf(&t).to_string(), "(or (not a) b)");
    }

    #[test]
    fn demorgan() {
        let t = parse_assert("(not (and a b))");
        assert_eq!(convert_to_nnf(&t).to_string(), "(or (not a) (not b))");
    }

    #[test]
    fn demorgan_nested_under_or() {
        let t = parse_assert("(or a (not (or b c)))");
        assert_eq!(convert_to_nnf(&t).to_string(), "(or a (and (not b) (not c)))");
    }

    #[test]
    fn negated_implies() {
        let t = parse_assert("(not (=> a b))");
        assert_eq!(convert_to_nnf(&t).to_string(), "(and a (not b))");
    }

    #[test]
    fn preserves_iff() {
        let t = parse_assert("(= a b)");
        assert_eq!(convert_to_nnf(&t).to_string(), "(= a b)");
    }

    #[test]
    fn preserves_negated_ite() {
        let t = parse_assert("(not (ite c a b))");
        assert_eq!(convert_to_nnf(&t).to_string(), "(not (ite c a b))");
    }

    #[test]
    fn strips_quantifier_body_annotation() {
        let script = Script::parse(
            "(declare-fun a () Bool)\n\
             (declare-fun b () Bool)\n\
             (assert (forall ((x Int)) (! (or a b) :pattern ((or a b)))))\n\
             (check-sat)\n",
        )
        .unwrap();
        let (out, _) = apply(&script).unwrap();
        let s = smt2::dump_string(&out);
        assert!(!s.contains("(!"), "nnf output must not retain annotations: {s}");
    }
}
