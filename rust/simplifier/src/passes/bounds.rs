//! Inject field-range axioms for bounded integer symbols (``@<digits>`` suffix).

use std::collections::HashSet;

use smt2::{declare_fun_name_cmd, decl_name, free_int_nodes, int_from_i128, map_asserts, symbol_id_from_name, Script, SmtCommand, SymbolId};
use z3::ast::{Ast, Bool, Dynamic, Int};

use crate::expr_util::{rebuild_script, AssertBuildCtx};
use crate::passes::skolem::ast_build::field_mod;

pub fn apply(script: &Script) -> Result<(Script, serde_json::Value), String> {
    let field = field_mod().ok_or("SIMPLIFIER_FIELD_MOD not set")?;
    let sorts = collect_symbol_sorts(script);
    let mut bounded: HashSet<Int> = HashSet::new();

    let _ = map_asserts(script, |b| {
        for sym in free_int_nodes(b) {
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

    let mut bound_syms: Vec<Int> = bounded.into_iter().collect();
    bound_syms.sort_by_cached_key(|i| decl_name(&Dynamic::from_ast(i).decl()));

    let bound_asserts: Vec<Bool> = bound_syms
        .iter()
        .map(|sym| field_symbol(sym, field))
        .collect();
    let n_bound = bound_syms.len();

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
            out.push(cmd.clone());
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

fn is_bounded_int_symbol(sym: &Int, sorts: &SymbolSorts) -> bool {
    let name = decl_name(&Dynamic::from_ast(sym).decl());
    if !needs_basic_range_axiom(&name) {
        return false;
    }
    let id = symbol_id_from_name(&name);
    if sorts.non_int.contains(&id) {
        return false;
    }
    sorts.int.contains(&id) || !sorts.known.contains(&id)
}

struct SymbolSorts {
    int: HashSet<SymbolId>,
    non_int: HashSet<SymbolId>,
    known: HashSet<SymbolId>,
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
        let id = symbol_id_from_name(&name);
        known.insert(id);
        if is_int_decl(&cmd.to_smtlib(&script.source)) {
            int.insert(id);
        } else {
            non_int.insert(id);
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

fn field_symbol(sym: &Int, field: i128) -> Bool {
    let lo = int_from_i128(0).le(sym);
    let hi = sym.lt(&int_from_i128(field));
    Bool::and(&[&lo, &hi])
}

#[cfg(test)]
mod tests {
    use super::*;
    use smt2::Script;

    fn field() -> i128 {
        field_mod().unwrap_or(2013265921)
    }

    #[test]
    fn adds_top_level_asserts_for_matching_free_vars() {
        let f = field();
        std::env::set_var("SIMPLIFIER_FIELD_MOD", f.to_string());
        let script = Script::parse("(assert (= x@0 y))\n(check-sat)\n").unwrap();
        let (out, stats) = apply(&script).unwrap();
        assert_eq!(stats["bounded_symbols"], 1);
        assert_eq!(stats["range_asserts_added"], 1);
        let s = smt2::dump_string(&out);
        assert!(s.contains("(assert (and (<= 0 x@0) (< x@0"));
        assert!(s.contains("(assert (= x@0 y))"));
        let first_assert = s.lines().find(|l| l.starts_with("(assert")).unwrap();
        assert!(first_assert.contains("x@0"));
        assert!(!first_assert.contains("= x@0 y"));
    }

    #[test]
    fn preserves_declare_fun_commands() {
        let f = field();
        std::env::set_var("SIMPLIFIER_FIELD_MOD", f.to_string());
        let script = Script::parse(
            "(declare-fun x@0 () Int)\n(declare-fun flag () Bool)\n(assert (= x@0 1))\n(check-sat)\n",
        )
        .unwrap();
        let (out, _) = apply(&script).unwrap();
        let s = smt2::dump_string(&out);
        assert!(s.contains("(declare-fun x@0 () Int)"));
        assert!(s.contains("(declare-fun flag () Bool)"));
    }
}
