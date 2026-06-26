//! Z3 tactic simplification over SMT-LIB scripts.

use std::io::{self, Write};

use smt2::{dump_string, load_reader, splice_z3_result, Script};
use z3::{SatResult, Tactic};

const DEFAULT_TACTICS: &[&str] = &[
    "propagate-values",
    "elim-term-ite",
    "propagate-ineqs",
    "solve-eqs",
    "ctx-simplify",
];

const REPEAT_MAX: u32 = 1024;

#[derive(Debug)]
pub struct Stats {
    pub z3_check: String,
    pub asserts_in: usize,
    pub asserts_out: usize,
    pub extra_declarations: usize,
    pub tactic_args: Option<Vec<String>>,
}

pub fn build_tactic(tactic_args: &[String]) -> Tactic {
    let base = match tactic_args {
        [] => {
            let mut chain = Tactic::new(DEFAULT_TACTICS[0]);
            for name in &DEFAULT_TACTICS[1..] {
                let next = Tactic::new(name);
                chain = chain.and_then(&next);
            }
            Tactic::repeat(&chain, REPEAT_MAX)
        }
        [single] => Tactic::new(single),
        many => {
            let mut chain = Tactic::new(&many[0]);
            for name in &many[1..] {
                let next = Tactic::new(name);
                chain = chain.and_then(&next);
            }
            chain
        }
    };
    base
}

fn sat_result_str(r: SatResult) -> &'static str {
    match r {
        SatResult::Sat => "sat",
        SatResult::Unsat => "unsat",
        SatResult::Unknown => "unknown",
    }
}

pub fn simplify_script(script: &Script, tactic_args: &[String]) -> Result<(Script, Stats), String> {
    let parts = script.split_at_check_sat()?;
    let asserts_in = parts.asserts_in();
    let z3_input = parts.z3_input_string();

    let tactic = build_tactic(tactic_args);
    let solver = tactic.solver();
    solver.from_string(z3_input.as_bytes());
    let z3_check = solver.check();

    let processed_str = solver.to_string();
    let processed = Script::parse(&processed_str)?;

    let prefix_names = smt2::declared_symbol_names(&parts.prefix);
    let extra = smt2::extra_declarations(&processed.commands, &prefix_names);
    let new_asserts = smt2::asserts_excluding_true(&processed.commands);

    let out = splice_z3_result(&parts, &processed.commands);
    let stats = Stats {
        z3_check: sat_result_str(z3_check).to_string(),
        asserts_in,
        asserts_out: new_asserts.len(),
        extra_declarations: extra.len(),
        tactic_args: if tactic_args.is_empty() {
            None
        } else {
            Some(tactic_args.to_vec())
        },
    };
    Ok((out, stats))
}

pub fn write_stats(stderr: &mut impl Write, stats: &Stats) -> io::Result<()> {
    let tactic_json = match &stats.tactic_args {
        None => "null".to_string(),
        Some(args) => {
            let items: Vec<String> = args
                .iter()
                .map(|a| format!("\"{}\"", a.replace('\\', "\\\\").replace('"', "\\\"")))
                .collect();
            format!("[{}]", items.join(","))
        }
    };
    writeln!(
        stderr,
        "{{\"z3_check\":\"{}\",\"asserts_in\":{},\"asserts_out\":{},\"extra_declarations\":{},\"tactic_args\":{}}}",
        stats.z3_check,
        stats.asserts_in,
        stats.asserts_out,
        stats.extra_declarations,
        tactic_json,
    )
}

pub fn simplify_reader<R: io::Read>(
    reader: R,
    tactic_args: &[String],
) -> Result<(String, Stats), String> {
    let script = load_reader(reader)?;
    let (out, stats) = simplify_script(&script, tactic_args)?;
    Ok((dump_string(&out), stats))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    fn has_z3() -> bool {
        std::process::Command::new("pkg-config")
            .args(["--exists", "z3"])
            .status()
            .map(|s| s.success())
            .unwrap_or(false)
    }

    #[test]
    fn folds_not_equal_constants() {
        if !has_z3() {
            return;
        }
        let input = "\
(declare-fun x () Int)
(assert (or (not (= 0 0)) (= x 1)))
(check-sat)
";
        let (out, stats) = simplify_reader(Cursor::new(input), &["simplify".to_string()])
            .expect("simplify");
        assert_eq!(stats.asserts_out, 1);
        assert!(out.contains("(= x 1)"));
    }
}
