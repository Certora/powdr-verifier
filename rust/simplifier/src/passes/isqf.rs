//! Quantifier-freedom check on asserts (mirrors PySMT ``QuantifierOracle``).

use smt2::{has_quantifier, Script};

pub fn apply(script: &Script) -> Result<(Script, serde_json::Value), String> {
    let is_qf = script_is_quantifier_free(script)?;
    let result = if is_qf { "qf" } else { "not-qf" };
    let stats = serde_json::json!({
        "expected": "qf",
        "result": result,
    });
    Ok((script.clone(), stats))
}

fn script_is_quantifier_free(script: &Script) -> Result<bool, String> {
    for cmd in &script.commands {
        if let Some(b) = cmd.assert_bool() {
            if has_quantifier(b) {
                return Ok(false);
            }
        }
    }
    Ok(true)
}

#[cfg(test)]
mod tests {
    use super::*;
    use smt2::Script;

    #[test]
    fn qf_formula() {
        let script = Script::parse(
            "(declare-fun x () Int)\n(assert (= x 1))\n(check-sat)\n",
        )
        .unwrap();
        let (_, stats) = apply(&script).unwrap();
        assert_eq!(stats["result"], "qf");
    }

    #[test]
    fn not_qf_formula() {
        let script = Script::parse(
            "(declare-fun x () Int)\n(assert (forall ((x Int)) (= x 0)))\n(check-sat)\n",
        )
        .unwrap();
        let (_, stats) = apply(&script).unwrap();
        assert_eq!(stats["result"], "not-qf");
    }

    #[test]
    fn forall_hidden_in_let_is_detected() {
        let script = Script::parse(
            "(declare-fun y () Int)\n(assert (let ((a!1 y)) (forall ((x Int)) (= x a!1))))\n(check-sat)\n",
        )
        .unwrap();
        let (_, stats) = apply(&script).unwrap();
        assert_eq!(stats["result"], "not-qf");
    }
}
