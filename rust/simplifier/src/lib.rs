//! Simplifier pass registry and pipeline runner.

pub mod passes;
pub mod tactic;

use std::io::{self, Write};

use smt2::Script;

use crate::passes::{bitwise, bounds, demod, domain_probe, evaluator, isqf, lift, mod_inv, nnf, normalize, pretty, skolem, witness, z3};
use crate::tactic::split_tactic;

#[derive(Debug)]
pub struct StepResult {
    pub pass: String,
    pub stats: serde_json::Value,
}

pub fn apply_pass(raw_tactic: &str, script: &Script) -> Result<(Script, StepResult), String> {
    let parts = split_tactic(raw_tactic);
    let (out, stats) = match parts.base.as_str() {
        "z3" => z3::apply(script, &parts.suffix)?,
        "nnf" => nnf::apply(script)?,
        "evaluator" => evaluator::apply(script)?,
        "demod" => demod::apply(script)?,
        "normalize" => normalize::apply(script)?,
        "skolem" => skolem::apply(script)?,
        "lift" => lift::apply(script)?,
        "witness" => witness::apply(script)?,
        "bounds" => bounds::apply(script)?,
        "bitwise" => bitwise::apply(script)?,
        "mod_inv" => mod_inv::apply(script)?,
        "domain_probe" => domain_probe::apply(script)?,
        "isqf" => isqf::apply(script)?,
        "pretty" | "p" => pretty::apply(script)?,
        other => {
            return Err(format!("unknown or unsupported rust tactic: {other}"));
        }
    };
    Ok((
        out,
        StepResult {
            pass: raw_tactic.to_string(),
            stats,
        },
    ))
}

pub fn run_pipeline(
    script: &Script,
    tactics: &[String],
) -> Result<(Script, Vec<StepResult>), String> {
    let mut cur = script.clone();
    let mut steps = Vec::new();
    for raw in tactics {
        let (next, step) = apply_pass(raw, &cur)?;
        cur = next;
        steps.push(step);
    }
    Ok((cur, steps))
}

pub fn write_step_stats(stderr: &mut impl Write, step: &StepResult) -> io::Result<()> {
    let mut obj = step.stats.as_object().cloned().unwrap_or_default();
    obj.insert("pass".to_string(), serde_json::Value::String(step.pass.clone()));
    writeln!(stderr, "{}", serde_json::Value::Object(obj))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn has_z3() -> bool {
        std::process::Command::new("pkg-config")
            .args(["--exists", "z3"])
            .status()
            .map(|s| s.success())
            .unwrap_or(false)
    }

    #[test]
    fn evaluator_folds_constants() {
        let script = Script::parse(
            "(declare-fun x () Int)\n(assert (or (not (= 0 0)) (= x 1)))\n(check-sat)\n",
        )
        .unwrap();
        let (out, step) = apply_pass("evaluator", &script).unwrap();
        let s = smt2::dump_string(&out);
        assert!(s.contains("(= x 1)"));
        assert_eq!(step.stats["asserts_changed"], 1);
    }

    #[test]
    fn z3_simplify_fold() {
        if !has_z3() {
            return;
        }
        let script = Script::parse(
            "(declare-fun x () Int)\n(assert (or (not (= 0 0)) (= x 1)))\n(check-sat)\n",
        )
        .unwrap();
        let (out, _) = apply_pass("z3-simplify", &script).unwrap();
        let s = smt2::dump_string(&out);
        assert!(s.contains("(= x 1)"));
    }
}
