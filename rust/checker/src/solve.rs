use std::collections::BTreeMap;
use std::time::Instant;

use serde_json::{json, Map, Value};
use z3::ast::Bool;
use z3::{Params, SatResult, Solver};

use crate::model::nice_model;
use crate::report::Action;

pub const SOLVER_NAME: &str = "z3";

#[derive(Clone, Debug)]
pub struct SolverConfig {
    pub options: BTreeMap<String, String>,
}

pub fn solver_configs(check_timeout: Option<f64>) -> Vec<SolverConfig> {
    if let Some(secs) = check_timeout {
        return vec![SolverConfig {
            options: BTreeMap::from([
                ("timeout".into(), format!("{}", (secs * 1000.0) as u32)),
                ("smt.random_seed".into(), "0".into()),
                ("sat.random_seed".into(), "0".into()),
            ]),
        }];
    }
    let mut out = Vec::new();
    for k in 0..4 {
        out.push(SolverConfig {
            options: BTreeMap::from([
                ("timeout".into(), "5000".into()),
                ("smt.random_seed".into(), k.to_string()),
                ("sat.random_seed".into(), k.to_string()),
                (
                    "smt.array.weak".into(),
                    if k % 2 == 0 { "false" } else { "true" }.into(),
                ),
            ]),
        });
    }
    out.push(SolverConfig {
        options: BTreeMap::from([
            ("timeout".into(), "40000".into()),
            ("smt.random_seed".into(), "4".into()),
            ("sat.random_seed".into(), "4".into()),
        ]),
    });
    out
}

pub fn config_label(config: &SolverConfig) -> String {
    let opts = config
        .options
        .iter()
        .map(|(k, v)| format!("{k}={v}"))
        .collect::<Vec<_>>()
        .join(", ");
    format!("{SOLVER_NAME} ({opts})")
}

fn apply_params(solver: &Solver, options: &BTreeMap<String, String>) {
    let mut params = Params::new();
    for (k, v) in options {
        match k.as_str() {
            "timeout" => {
                if let Ok(ms) = v.parse::<u32>() {
                    params.set_u32("timeout", ms);
                }
            }
            "smt.random_seed" | "sat.random_seed" => {
                if let Ok(n) = v.parse::<u32>() {
                    params.set_u32(k.as_str(), n);
                }
            }
            "smt.array.weak" => {
                params.set_bool("smt.array.weak", v == "true");
            }
            _ => {
                if v == "true" || v == "false" {
                    params.set_bool(k.as_str(), v == "true");
                } else if let Ok(n) = v.parse::<u32>() {
                    params.set_u32(k.as_str(), n);
                } else {
                    params.set_symbol(k.as_str(), v.as_str());
                }
            }
        }
    }
    solver.set_params(&params);
}

fn result_from_check(solver: &Solver) -> String {
    match solver.check() {
        SatResult::Sat => "sat".into(),
        SatResult::Unsat => "unsat".into(),
        SatResult::Unknown => match solver.get_reason_unknown() {
            Some(r) if !r.is_empty() => format!("unknown-{r}"),
            _ => "unknown".into(),
        },
    }
}

fn options_json(options: &BTreeMap<String, String>) -> Value {
    let mut m = Map::new();
    for (k, v) in options {
        if let Ok(n) = v.parse::<u64>() {
            m.insert(k.clone(), Value::Number(n.into()));
        } else if v == "true" {
            m.insert(k.clone(), Value::Bool(true));
        } else if v == "false" {
            m.insert(k.clone(), Value::Bool(false));
        } else {
            m.insert(k.clone(), Value::String(v.clone()));
        }
    }
    Value::Object(m)
}

pub fn run_solver_config(z3_prefix: &str, config: &SolverConfig) -> Action {
    let start = Instant::now();
    let mut attempt = Action::new("check-attempt");
    attempt.set("solver", json!(SOLVER_NAME));
    attempt.set(
        "solver_options",
        options_json(&config.options),
    );

    let solver = Solver::new();
    solver.from_string(z3_prefix.as_bytes());
    apply_params(&solver, &config.options);
    let result = result_from_check(&solver);
    attempt.set("result", json!(result));
    if result == "sat" {
        if let Some(model) = solver.get_model() {
            attempt.set("model", json!(nice_model(&model)));
        }
    }
    attempt.running_time = Some(start.elapsed().as_secs_f64());
    attempt
}

pub fn check_script(
    z3_prefix: &str,
    action: &mut Action,
    log_key: &str,
    check_timeout: Option<f64>,
) -> String {
    let mut last_attempt: Option<Action> = None;
    for config in solver_configs(check_timeout) {
        let label = config_label(&config);
        eprintln!("check {log_key} with {label}");
        let attempt = run_solver_config(z3_prefix, &config);
        let res = attempt
            .get_str("result")
            .unwrap_or("unknown")
            .to_string();
        action.push(attempt.clone());
        last_attempt = Some(attempt);
        if res == "sat" || res == "unsat" {
            break;
        }
        eprintln!("check {log_key} with {label} returned {res}, trying next config");
    }
    let res = last_attempt
        .as_ref()
        .and_then(|a| a.get_str("result").map(str::to_string))
        .unwrap_or_else(|| "unknown".into());
    if res == "sat" {
        if let Some(model) = last_attempt.as_ref().and_then(|a| a.get("model").cloned()) {
            action.set("model", model);
        }
    }
    res
}

pub fn check_script_disjuncts(
    _prefix: &str,
    context: &[Bool],
    disjuncts: &[Bool],
    log_key: &str,
) -> Action {
    let start = Instant::now();
    let mut attempt = Action::new("check-attempt");
    let options = BTreeMap::from([
        ("timeout".into(), "60000".into()),
        ("smt.random_seed".into(), "0".into()),
        ("sat.random_seed".into(), "0".into()),
    ]);
    attempt.set("solver", json!(SOLVER_NAME));
    attempt.set("solver_options", options_json(&options));
    eprintln!(
        "check {log_key} (disjuncts) with {}",
        config_label(&SolverConfig {
            options: options.clone()
        })
    );

    let solver = Solver::new();
    for a in context {
        solver.assert(a);
    }
    apply_params(&solver, &options);
    let mut final_result = "unsat".to_string();
    for (k, disjunct) in disjuncts.iter().enumerate() {
        solver.push();
        solver.assert(disjunct);
        let result = result_from_check(&solver);
        if result == "sat" {
            final_result = "sat".into();
            attempt.set("disjunct_index", json!(k));
            if let Some(model) = solver.get_model() {
                attempt.set("model", json!(nice_model(&model)));
            }
            solver.pop(1);
            break;
        }
        solver.pop(1);
        if result != "unsat" {
            final_result = result;
            attempt.set("disjunct_index", json!(k));
            break;
        }
        solver.assert(&disjunct.not());
    }
    attempt.set("result", json!(final_result));
    attempt.running_time = Some(start.elapsed().as_secs_f64());
    attempt
}
