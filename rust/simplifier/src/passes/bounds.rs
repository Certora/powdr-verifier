//! Inject field-range axioms for bounded integer symbols (``@<digits>`` suffix).

use std::collections::HashSet;

use smt2::{declare_fun_name_cmd, int_from_i128, map_asserts, Script, SmtCommand};
use z3::ast::{Bool, Int};

use crate::expr_util::{rebuild_script, AssertBuildCtx};
use crate::passes::skolem::ast_build::field_mod;

pub fn apply(script: &Script) -> Result<(Script, serde_json::Value), String> {
    let field = field_mod().ok_or("SIMPLIFIER_FIELD_MOD not set")?;
    let sorts = collect_symbol_sorts(script);
    let mut bounded: HashSet<String> = HashSet::new();

    let _ = map_asserts(script, |b| {
        for sym in smt2::free_int_symbols(b) {
            if is_bounded_int_symbol(&sym, &sorts) {
                bounded.insert(sym);
            }
        }
        Ok(b.clone())
    })?;

    if bounded.is_empty() {
        return Ok((
            script.clone(),
            serde_json::json!({
                "bounded_symbols": 0,
                "range_asserts_added": 0,
            }),
        ));
    }

    let mut bound_names: Vec<String> = bounded.into_iter().collect();
    bound_names.sort();

    let bound_asserts: Vec<Bool> = bound_names
        .iter()
        .map(|name| field_symbol(name, field))
        .collect();
    let n_bound = bound_names.len();

    let mut ctx = AssertBuildCtx::from_script(script)?;
    let mut out: Vec<SmtCommand> = Vec::new();
    let mut inserted = false;
    for cmd in &script.commands {
        if !inserted && cmd.assert_bool().is_some() {
            for b in &bound_asserts {
                ctx.push_assert(&mut out, b)?;
            }
            inserted = true;
        }
        if let Some(b) = cmd.assert_bool() {
            ctx.push_assert(&mut out, b)?;
        } else {
            ctx.push_raw(&mut out, &cmd.to_smtlib(&script.source))?;
        }
    }

    Ok((
        rebuild_script(&script.source, out),
        serde_json::json!({
            "bounded_symbols": n_bound,
            "range_asserts_added": n_bound,
        }),
    ))
}

fn needs_basic_range_axiom(name: &str) -> bool {
    let Some(at) = name.rfind('@') else {
        return false;
    };
    let suffix = &name[at + 1..];
    !suffix.is_empty() && suffix.chars().all(|c| c.is_ascii_digit())
}

fn is_bounded_int_symbol(name: &str, sorts: &SymbolSorts) -> bool {
    if !needs_basic_range_axiom(name) {
        return false;
    }
    if sorts.non_int.contains(name) {
        return false;
    }
    sorts.int.contains(name) || !sorts.known.contains(name)
}

struct SymbolSorts {
    int: HashSet<String>,
    non_int: HashSet<String>,
    known: HashSet<String>,
}

fn collect_symbol_sorts(script: &Script) -> SymbolSorts {
    let mut int = HashSet::new();
    let mut non_int = HashSet::new();
    let mut known = HashSet::new();
    for cmd in &script.commands {
        if cmd.name() != "declare-fun" {
            continue;
        }
        let Some(name) = declare_fun_name_cmd(cmd) else {
            continue;
        };
        known.insert(name.clone());
        if is_int_decl(&cmd.to_smtlib(&script.source)) {
            int.insert(name);
        } else {
            non_int.insert(name);
        }
    }
    SymbolSorts {
        int,
        non_int,
        known,
    }
}

fn is_int_decl(raw: &str) -> bool {
    let lower = raw.to_ascii_lowercase();
    lower.contains(" int") || lower.ends_with(" int)") || lower.contains("(int ")
}

fn field_symbol(name: &str, field: i128) -> Bool {
    let sym = Int::new_const(name);
    let lo = int_from_i128(0).le(&sym);
    let hi = sym.lt(&int_from_i128(field));
    Bool::and(&[&lo, &hi])
}

#[cfg(test)]
mod tests {
    use super::*;

    fn field() -> i128 {
        field_mod().unwrap_or(2013265921)
    }

    #[test]
    fn adds_top_level_asserts_for_matching_free_vars() {
        let f = field();
        std::env::set_var("SIMPLIFIER_FIELD_MOD", f.to_string());
        let script = Script::parse(&format!(
            "(assert (= x@0 y))\n(check-sat)\n"
        ))
        .unwrap();
        let (out, stats) = apply(&script).unwrap();
        assert_eq!(stats["bounded_symbols"], 1);
        assert_eq!(stats["range_asserts_added"], 1);
        let s = smt2::dump_string(&out);
        assert!(s.contains("(assert (and (<= 0 x@0) (< x@0"));
        assert!(s.contains("(assert (= x@0 y))"));
        let first_assert = s
            .lines()
            .find(|l| l.starts_with("(assert"))
            .unwrap();
        assert!(first_assert.contains("x@0"));
        assert!(!first_assert.contains("= x@0 y"));
    }

    #[test]
    fn leaves_quantifiers_unchanged() {
        let f = field();
        std::env::set_var("SIMPLIFIER_FIELD_MOD", f.to_string());
        let script = Script::parse(&format!(
            "(assert (forall ((x@0 Int)) (= x@0 y@0)))\n(check-sat)\n"
        ))
        .unwrap();
        let (out, stats) = apply(&script).unwrap();
        assert_eq!(stats["bounded_symbols"], 1);
        let s = smt2::dump_string(&out);
        assert!(s.contains("(forall ((x@0 Int))"));
        assert!(s.contains("(assert (and (<= 0 y@0)"));
        assert!(!s.contains("(=>"));
    }
}
