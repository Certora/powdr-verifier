//! Simplifier pass registry and pipeline runner.

pub mod budget;
pub mod expr_util;
pub mod fold;
pub mod passes;
pub mod poly_factor;
pub mod tactic;

use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use smt2::{dump_string, ensure_declarations_for_asserts, pretty_print_script, Script};

use crate::budget::Budget;
use crate::passes::{bitwise, bounds, demod, domain_probe, evaluator, isqf, lift, mod_inv, nnf, normalize, pretty, rewrite, skolem, witness, z3};
use crate::tactic::split_tactic;

#[derive(Debug)]
pub struct StepResult {
    pub pass: String,
    pub stats: serde_json::Value,
}

#[derive(Debug, Clone)]
pub struct DumpStepsConfig {
    pub output: PathBuf,
    pub pretty: bool,
    pub step_offset: usize,
}

fn dump_step_path(output: &Path, step_index: usize, tactic: &str) -> PathBuf {
    let stem = output
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("out");
    let parent = output.parent().unwrap_or_else(|| Path::new("."));
    parent.join(format!("{stem}.{step_index:02}.{tactic}.smt2"))
}

fn write_script_to_path(script: &Script, path: &Path, pretty: bool) -> Result<(), String> {
    let out_script = if pretty {
        pretty_print_script(script)?
    } else {
        script.clone()
    };
    std::fs::write(path, dump_string(&out_script).as_bytes()).map_err(|e| e.to_string())
}

pub fn dump_step_script(
    script: &Script,
    config: &DumpStepsConfig,
    step_index: usize,
    tactic: &str,
) -> Result<(), String> {
    let path = dump_step_path(&config.output, step_index, tactic);
    eprintln!("dumping intermediate formula to {}", path.display());
    write_script_to_path(script, &path, config.pretty)
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

enum TimedPassResult {
    Ok((Script, StepResult)),
    Timeout,
    Err(String),
}

fn run_timed_pass(raw: &str, cur: &Script, limit: Option<Duration>) -> TimedPassResult {
    if matches!(limit, Some(limit) if limit.is_zero()) {
        return TimedPassResult::Timeout;
    }
    let t0 = Instant::now();
    match apply_pass(raw, cur) {
        Ok(v) => {
            if limit.is_some_and(|limit| t0.elapsed() > limit) {
                TimedPassResult::Timeout
            } else {
                TimedPassResult::Ok(v)
            }
        }
        Err(e) => TimedPassResult::Err(e),
    }
}

pub fn run_pipeline(
    script: &Script,
    tactics: &[String],
    budget: Budget,
    dump_steps: Option<&DumpStepsConfig>,
) -> Result<(Script, Vec<StepResult>), String> {
    let mut cur = script.clone();
    let mut steps = Vec::new();
    for (i, raw) in tactics.iter().enumerate() {
        if !budget.has_budget() {
            steps.push(skipped_step(raw, "no-budget"));
        } else {
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

        if let Some(cfg) = dump_steps {
            dump_step_script(&cur, cfg, cfg.step_offset + i + 1, raw)?;
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
        let (out, steps) = run_pipeline(&script, &tactics, budget, None).unwrap();
        assert_eq!(smt2::dump_string(&out), smt2::dump_string(&script));
        assert_eq!(steps.len(), 2);
        assert_eq!(steps[0].stats["result"], "skipped");
        assert_eq!(steps[0].stats["reason"], "no-budget");
        assert_eq!(steps[1].stats["result"], "skipped");
    }

    #[test]
    fn dump_steps_writes_per_pass_files() {
        let dir = std::env::temp_dir().join(format!("simplifier-dump-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let output = dir.join("out.smt2");
        let script = Script::parse(
            "(declare-fun x () Int)\n(assert (= x 1))\n(check-sat)\n",
        )
        .unwrap();
        let tactics = vec!["evaluator".to_string()];
        let cfg = DumpStepsConfig {
            output: output.clone(),
            pretty: false,
            step_offset: 2,
        };
        let (_, steps) = run_pipeline(&script, &tactics, Budget::unlimited(), Some(&cfg)).unwrap();
        assert_eq!(steps.len(), 1);
        let dump = dir.join("out.03.evaluator.smt2");
        assert!(dump.is_file(), "missing {}", dump.display());
        let _ = std::fs::remove_dir_all(&dir);
    }
}
