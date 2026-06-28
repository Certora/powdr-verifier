//! Quantifier-freedom check on asserts (mirrors PySMT ``QuantifierOracle``).

use smt2::{term::assert_body, Script, Term};

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
        if cmd.name() != "assert" {
            continue;
        }
        let Some(body) = assert_body(&cmd.raw) else {
            continue;
        };
        let term = Term::parse(&body)?;
        if term_has_quantifier(&term) {
            return Ok(false);
        }
    }
    Ok(true)
}

fn term_has_quantifier(term: &Term) -> bool {
    match term {
        Term::List(items) if !items.is_empty() => {
            if let Term::Atom(head) = &items[0] {
                if head == "forall" || head == "exists" {
                    return true;
                }
            }
            items.iter().any(term_has_quantifier)
        }
        _ => false,
    }
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
}
