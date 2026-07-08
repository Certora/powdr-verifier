mod ast;
mod input;
mod model;
mod report;
mod solve;

use std::fs;
use std::path::PathBuf;
use std::time::Instant;

use serde_json::json;

pub use ast::{find_largest_or_goal, or_body_parts};
pub use input::{display_path, extract_expected_status, load_script, z3_feed_prefix, LoadedScript};
pub use report::{classify_expected_vs_result, dump_action, log_expected_mismatch, Action};
pub use solve::{check_script, check_script_disjuncts, solver_configs};

pub struct CheckOptions {
    pub input: PathBuf,
    pub dump_model: Option<PathBuf>,
    pub solve_chunked: bool,
    pub timeout: Option<f64>,
}

pub fn run_check(opts: &CheckOptions) -> Result<Action, String> {
    let text = input::read_input(
        opts.input
            .to_str()
            .ok_or_else(|| "invalid input path".to_string())?,
    )?;
    let log_key = display_path(Some(&opts.input));

    let mut root = Action::new("check");
    root.set("inputs", json!([opts.input.display().to_string()]));

    let parse_start = Instant::now();
    let loaded = load_script(&text)?;
    let mut parse_action = Action::new("parse");
    parse_action.running_time = Some(parse_start.elapsed().as_secs_f64());
    root.push(parse_action);

    if let Some(expected) = &loaded.expected {
        root.set("expected", json!(expected));
    }

    let solve_start = Instant::now();
    let mut solve_action = Action::new("solve");
    if let Some(expected) = &loaded.expected {
        solve_action.set("expected", json!(expected));
    }

    let result = if opts.solve_chunked {
        if let Some((goal_idx, disjuncts)) = find_largest_or_goal(&loaded.assertions) {
            let attempt = check_script_disjuncts(
                &loaded.prefix,
                &loaded.assertions,
                goal_idx,
                &disjuncts,
                &log_key,
            );
            let res = attempt
                .get_str("result")
                .unwrap_or("unknown")
                .to_string();
            solve_action.push(attempt);
            res
        } else {
            eprintln!("no splittable Or-disjunction found, checking entire script");
            check_script(
                &loaded.z3_prefix,
                &mut solve_action,
                &log_key,
                opts.timeout,
            )
        }
    } else {
        check_script(
            &loaded.z3_prefix,
            &mut solve_action,
            &log_key,
            opts.timeout,
        )
    };

    solve_action.set("result", json!(result));
    solve_action.running_time = Some(solve_start.elapsed().as_secs_f64());
    root.push(solve_action);
    root.set("result", json!(result));

    if result == "sat" {
        let model = root.actions.last().and_then(|solve| {
            solve
                .get("model")
                .cloned()
                .or_else(|| solve.actions.last().and_then(|a| a.get("model").cloned()))
        });
        if let Some(model) = model {
            root.set("model", model.clone());
            if let Some(path) = &opts.dump_model {
                let s = serde_json::to_string_pretty(&model).map_err(|e| e.to_string())?;
                fs::write(path, s).map_err(|e| e.to_string())?;
                eprintln!("dumping model to {}", path.display());
            }
        }
    }

    if let Some(expected) = &loaded.expected {
        log_expected_mismatch(expected, &result);
    }

    Ok(root)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn z3_feed_prefix_strips_status() {
        let prefix = "(declare-fun x () Int)\n(set-info :status unsat)\n(assert (= x 1))\n";
        assert!(!z3_feed_prefix(prefix).contains(":status"));
        assert!(z3_feed_prefix(prefix).contains("(assert"));
    }

    #[test]
    fn extract_status_unquoted() {
        let text = "(set-info :status unsat)\n(check-sat)\n";
        assert_eq!(extract_expected_status(text).as_deref(), Some("unsat"));
    }

    #[test]
    fn find_largest_or_picks_bigger() {
        let smt = "\
(set-logic ALL)
(declare-fun x () Int)
(assert (or (= x 1) (= x 2)))
(assert (or (= x 3) (= x 4) (= x 5)))
(check-sat)\n";
        let loaded = load_script(smt).unwrap();
        let (idx, parts) = find_largest_or_goal(&loaded.assertions).unwrap();
        assert_eq!(idx, 1);
        assert_eq!(parts.len(), 3);
    }

    fn test_smt_path(name: &str) -> PathBuf {
        let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target");
        let _ = std::fs::create_dir_all(&dir);
        dir.join(format!("{name}-{}.smt2", std::process::id()))
    }

    #[test]
    fn load_unsat_has_two_assertions() {
        let smt = "\
(set-logic ALL)
(declare-fun x () Int)
(assert (= x 1))
(assert (= x 2))
(set-info :status unsat)
(check-sat)\n";
        let loaded = load_script(smt).unwrap();
        assert_eq!(loaded.assertions.len(), 2);
    }

    #[test]
    fn check_unsat_tiny() {
        let smt = "\
(set-logic ALL)
(declare-fun x () Int)
(assert (= x 1))
(assert (= x 2))
(set-info :status unsat)
(check-sat)\n";
        let path = test_smt_path("checker-test");
        std::fs::write(&path, smt).unwrap();
        let action = run_check(&CheckOptions {
            input: path.clone(),
            dump_model: None,
            solve_chunked: false,
            timeout: Some(5.0),
        })
        .unwrap();
        assert_eq!(action.get_str("result"), Some("unsat"));
        let _ = std::fs::remove_file(path);
    }

    #[test]
    fn check_sat_tiny() {
        let smt = "\
(set-logic ALL)
(declare-fun x () Int)
(assert (= x 1))
(set-info :status sat)
(check-sat)\n";
        let path = test_smt_path("checker-test-sat");
        std::fs::write(&path, smt).unwrap();
        let action = run_check(&CheckOptions {
            input: path.clone(),
            dump_model: None,
            solve_chunked: false,
            timeout: Some(5.0),
        })
        .unwrap();
        assert_eq!(action.get_str("result"), Some("sat"));
        let _ = std::fs::remove_file(path);
    }
}
