//! NNF conversion (Python ``NNFConverter`` parity; preserves ``=`` / iff).

use smt2::{
    flatten_and, flatten_or, is_implies, is_not, map_asserts, map_bool_children, strip_annotations,
    strip_annotations_deep, Script,
};
use z3::ast::Bool;

pub fn apply(script: &Script) -> Result<(Script, serde_json::Value), String> {
    let total = smt2::assert_commands(script).len();
    let mut changed = 0usize;
    let out = map_asserts(script, |b| {
        let nnf = strip_annotations_deep(&convert_to_nnf(b));
        if !nnf.ast_eq(b) {
            changed += 1;
        }
        Ok(nnf)
    })?;
    let stats = serde_json::json!({
        "asserts": total,
        "asserts_changed": changed,
    });
    Ok((out, stats))
}

fn convert_to_nnf(b: &Bool) -> Bool {
    let stripped = strip_annotations(b);
    if let Some(inner) = is_not(&stripped) {
        return negate(&inner);
    }
    if let Some((a, c)) = is_implies(&stripped) {
        return flatten_or(vec![negate(&a), c]);
    }
    map_bool_children(&stripped, &mut |child| convert_to_nnf(child))
}

fn negate(b: &Bool) -> Bool {
    if let Some(inner) = is_not(b) {
        return inner.clone();
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
        return flatten_and(vec![a.clone(), negate(&c)]);
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
