//! Simplifier pass registry and pipeline runner.

pub mod budget;
pub mod expr_util;
pub mod fold;
pub mod passes;
pub mod poly_factor;
pub mod tactic;

use std::io::{self, Write};
use std::sync::mpsc;
use std::thread;
use std::time::{Duration, Instant};

use smt2::{ensure_declarations_for_asserts, Script};

use crate::budget::Budget;
use crate::passes::{bitwise, bounds, demod, domain_probe, evaluator, isqf, lift, mod_inv, nnf, normalize, pretty, rewrite, skolem, witness, z3};
use crate::tactic::split_tactic;

#[derive(Debug)]
pub struct StepResult {
    pub pass: String,
    pub stats: serde_json::Value,
}

enum PassWait {
    Timeout,
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
        "rewrite" => rewrite::apply(script)?,
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

fn skipped_step(raw: &str, reason: &str) -> StepResult {
    StepResult {
        pass: raw.to_string(),
        stats: serde_json::json!({
            "result": "skipped",
            "reason": reason,
            "running_time": 0.0,
        }),
    }
}

fn timed_out_step(raw: &str, running_time: f64) -> StepResult {
    StepResult {
        pass: raw.to_string(),
        stats: serde_json::json!({
            "result": "timeout",
            "running_time": running_time,
        }),
    }
}

fn step_with_time(step: StepResult, running_time: f64) -> StepResult {
    let mut stats = step.stats;
    if let Some(obj) = stats.as_object_mut() {
        obj.insert("running_time".into(), serde_json::json!(running_time));
    }
    StepResult {
        pass: step.pass,
        stats,
    }
}

enum ThreadPassResult {
    Ok(String, StepResult),
    Err(String),
}

fn run_pass_with_timeout(
    raw: &str,
    script: &Script,
    limit: Duration,
) -> Result<Result<(Script, StepResult), String>, PassWait> {
    let raw = raw.to_string();
    let smt = smt2::dump_string(script);
    let (tx, rx) = mpsc::sync_channel(1);
    thread::spawn(move || {
        let msg = match Script::parse(&smt) {
            Ok(script) => match apply_pass(&raw, &script) {
                Ok((out, step)) => ThreadPassResult::Ok(smt2::dump_string(&out), step),
                Err(e) => ThreadPassResult::Err(e),
            },
            Err(e) => ThreadPassResult::Err(e.to_string()),
        };
        let _ = tx.send(msg);
    });
    match rx.recv_timeout(limit) {
        Ok(ThreadPassResult::Ok(out, step)) => match Script::parse(&out) {
            Ok(script) => Ok(Ok((script, step))),
            Err(e) => Ok(Err(e.to_string())),
        },
        Ok(ThreadPassResult::Err(e)) => Ok(Err(e)),
        Err(mpsc::RecvTimeoutError::Timeout) | Err(mpsc::RecvTimeoutError::Disconnected) => {
            Err(PassWait::Timeout)
        }
    }
}

enum TimedPassResult {
    Ok((Script, StepResult)),
    Timeout,
    Err(String),
}

fn run_timed_pass(raw: &str, cur: &Script, limit: Option<Duration>) -> TimedPassResult {
    match limit {
        None => match apply_pass(raw, cur) {
            Ok(v) => TimedPassResult::Ok(v),
            Err(e) => TimedPassResult::Err(e),
        },
        Some(limit) if limit.is_zero() => TimedPassResult::Timeout,
        Some(limit) => match run_pass_with_timeout(raw, cur, limit) {
            Ok(Ok(v)) => TimedPassResult::Ok(v),
            Ok(Err(e)) => TimedPassResult::Err(e),
            Err(PassWait::Timeout) => TimedPassResult::Timeout,
        },
    }
}

pub fn run_pipeline(
    script: &Script,
    tactics: &[String],
    budget: Budget,
) -> Result<(Script, Vec<StepResult>), String> {
    let mut cur = script.clone();
    let mut steps = Vec::new();
    for raw in tactics {
        if !budget.has_budget() {
            steps.push(skipped_step(raw, "no-budget"));
            continue;
        }

        let backup = cur.clone();
        let t0 = Instant::now();
        match run_timed_pass(raw, &cur, budget.remaining_for_pass()) {
            TimedPassResult::Ok((next, step)) => {
                cur = ensure_declarations_for_asserts(&next)?;
                steps.push(step_with_time(step, t0.elapsed().as_secs_f64()));
            }
            TimedPassResult::Timeout => {
                cur = backup;
                steps.push(timed_out_step(raw, t0.elapsed().as_secs_f64()));
            }
            TimedPassResult::Err(e) => return Err(e),
        }
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

    #[test]
    fn zero_budget_skips_all_passes() {
        let script = Script::parse(
            "(declare-fun x () Int)\n(assert (= x 1))\n(check-sat)\n",
        )
        .unwrap();
        let tactics = vec!["evaluator".to_string(), "nnf".to_string()];
        let budget = Budget::from_timeout_secs(0.0);
        let (out, steps) = run_pipeline(&script, &tactics, budget).unwrap();
        assert_eq!(smt2::dump_string(&out), smt2::dump_string(&script));
        assert_eq!(steps.len(), 2);
        assert_eq!(steps[0].stats["result"], "skipped");
        assert_eq!(steps[0].stats["reason"], "no-budget");
        assert_eq!(steps[1].stats["result"], "skipped");
    }
}
