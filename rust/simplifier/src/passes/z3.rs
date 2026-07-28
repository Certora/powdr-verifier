//! Z3 tactic simplification over SMT-LIB scripts.

use smt2::{
    declared_symbol_names, ensure_declarations_for_asserts, strip_annotations_deep, Script,
    SmtCommand,
};
use z3::{SatResult, Tactic};

const DEFAULT_TACTICS: &[&str] = &[
    "propagate-values",
    "elim-term-ite",
    "propagate-ineqs",
    "solve-eqs",
    "ctx-simplify",
];

const REPEAT_MAX: u32 = 1024;

/// Tactic by name. `solve-eqs` is ALWAYS built with `:eliminate_mod false`,
/// disabling the `solve_mod` rewrite `(= (mod u P) y) => u := P*mod!k + y` that
/// mints `mod!` quotient witnesses. Those witnesses are nonlinear and blow up
/// the arithmetic check, so we never want the mod-eliminating variant. Mirrors
/// `_mk_tactic` in `src/simplify/z3.py`.
fn mk_tactic(name: &str) -> Tactic {
    let t = Tactic::new(name);
    if name == "solve-eqs" {
        let mut params = z3::Params::new();
        params.set_bool("eliminate_mod", false);
        t.with(&params)
    } else {
        t
    }
}

pub fn build_tactic(tactic_args: &[String]) -> Tactic {
    let base = match tactic_args {
        [] => {
            let mut chain = mk_tactic(DEFAULT_TACTICS[0]);
            for name in &DEFAULT_TACTICS[1..] {
                let next = mk_tactic(name);
                chain = chain.and_then(&next);
            }
            Tactic::repeat(&chain, REPEAT_MAX)
        }
        [single] => mk_tactic(single),
        many => {
            let mut chain = mk_tactic(&many[0]);
            for name in &many[1..] {
                let next = mk_tactic(name);
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

fn processed_asserts(solver: &z3::Solver) -> Vec<SmtCommand> {
    solver
        .get_assertions()
        .into_iter()
        .map(|b| strip_annotations_deep(&b))
        .filter(|b| b.as_bool() != Some(true))
        .map(SmtCommand::new_assert)
        .collect()
}

fn assemble_output(
    parts: &smt2::ScriptParts,
    new_asserts: Vec<SmtCommand>,
    source: &str,
) -> Result<Script, String> {
    let mut commands = parts.prefix.clone();
    commands.extend(new_asserts);
    commands.push(parts.check_sat.clone());
    commands.extend(parts.suffix.iter().cloned());
    ensure_declarations_for_asserts(&Script::from_commands(source, commands))
}

pub fn apply(script: &Script, tactic_args: &[String]) -> Result<(Script, serde_json::Value), String> {
    let parts = script.split_at_check_sat()?;
    let asserts_in = parts.asserts_in();

    let tactic = build_tactic(tactic_args);
    let solver = tactic.solver();

    let decls = parts.z3_declarations_string(&script.source);
    if !decls.is_empty() {
        solver.from_string(decls.as_bytes());
    }
    for cmd in &parts.z3_feed {
        if let Some(b) = cmd.assert_bool() {
            solver.assert(b);
        }
    }

    let z3_check = solver.check();
    let new_asserts = processed_asserts(&solver);
    let prefix_names = declared_symbol_names(&parts.prefix);

    let out = if new_asserts.is_empty() && asserts_in > 0 && z3_check == SatResult::Sat {
        // Z3 reported SAT after reducing every assert to true — keep the input
        // fragment so later passes (and the final check) still see constraints.
        let mut commands = parts.prefix.clone();
        commands.extend(parts.z3_feed.iter().cloned());
        commands.push(parts.check_sat.clone());
        commands.extend(parts.suffix.iter().cloned());
        Script::from_commands(&script.source, commands)
    } else {
        assemble_output(&parts, new_asserts, &script.source)?
    };

    let extra_declarations = out
        .commands
        .iter()
        .filter(|c| c.name() == "declare-fun")
        .filter(|c| {
            smt2::declare_fun_name_cmd(c)
                .map(|sym| !prefix_names.contains(&sym))
                .unwrap_or(false)
        })
        .count();

    let asserts_out = out
        .commands
        .iter()
        .take_while(|c| c.name() != "check-sat")
        .filter(|c| c.name() == "assert")
        .count();

    let stats = serde_json::json!({
        "backend": "rust",
        "z3_version": z3::full_version(),
        "z3_check": sat_result_str(z3_check),
        "asserts_in": asserts_in,
        "asserts_out": asserts_out,
        "extra_declarations": extra_declarations,
        "ensured_declarations": 0,
        "tactic_args": if tactic_args.is_empty() { serde_json::Value::Null } else { serde_json::json!(tactic_args) },
    });
    Ok((out, stats))
}
