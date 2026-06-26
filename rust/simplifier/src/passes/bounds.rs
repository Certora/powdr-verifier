//! Inject field-range axioms for bounded integer symbols (``@<digits>`` suffix).

use std::collections::HashSet;

use smt2::{Script, Term};
use smt2::parse::Command;

use crate::passes::skolem::term_util::{atom, field_mod, is_symbol, list, symbol_name};
use crate::passes::skolem::utils::declare_fun_name;

pub fn apply(script: &Script) -> Result<(Script, serde_json::Value), String> {
    let field = field_mod().ok_or("SIMPLIFIER_FIELD_MOD not set")?;
    let sorts = collect_symbol_sorts(script);
    let mut bounded: HashSet<String> = HashSet::new();

    for cmd in &script.commands {
        if cmd.name() != "assert" {
            continue;
        }
        let body = smt2::term::assert_body(&cmd.raw)
            .ok_or_else(|| format!("malformed assert: {}", cmd.raw))?;
        let term = Term::parse(&body)?;
        for sym in scoped_free_variables(&term, &HashSet::new()) {
            if is_bounded_int_symbol(&sym, &sorts) {
                bounded.insert(sym);
            }
        }
    }

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

    let bound_asserts: Vec<Command> = bound_names
        .iter()
        .map(|name| Command::new(format!("(assert {})", field_symbol(name, field))))
        .collect();
    let n_bound = bound_names.len();

    let mut out = Vec::new();
    let mut inserted = false;
    for cmd in &script.commands {
        if !inserted && cmd.name() == "assert" {
            out.extend(bound_asserts.iter().cloned());
            inserted = true;
        }
        out.push(cmd.clone());
    }

    Ok((
        Script::from_commands(out),
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
        let Some(name) = declare_fun_name(&cmd.raw) else {
            continue;
        };
        known.insert(name.clone());
        if is_int_decl(&cmd.raw) {
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

fn field_symbol(name: &str, field: i128) -> String {
    list(
        "and",
        vec![
            list("<=", vec![atom("0"), atom(name)]),
            list("<", vec![atom(name), atom(&field.to_string())]),
        ],
    )
    .to_string()
}

fn scoped_free_variables(term: &Term, bound: &HashSet<String>) -> HashSet<String> {
    if let Some(name) = symbol_name(term) {
        if is_symbol(term) && !bound.contains(name) {
            return HashSet::from([name.to_string()]);
        }
        return HashSet::new();
    }
    let Term::List(items) = term else {
        return HashSet::new();
    };
    if items.is_empty() {
        return HashSet::new();
    }
    if matches!(items.first(), Some(Term::Atom(s)) if s == "forall" || s == "exists") && items.len() >= 3
    {
        let mut new_bound = bound.clone();
        new_bound.extend(quantifier_var_names(&items[1]));
        return scoped_free_variables(&items[2], &new_bound);
    }
    items[1..]
        .iter()
        .flat_map(|a| scoped_free_variables(a, bound))
        .collect()
}

fn quantifier_var_names(decls: &Term) -> HashSet<String> {
    let Term::List(items) = decls else {
        return HashSet::new();
    };
    items
        .iter()
        .filter_map(|d| match d {
            Term::List(pair) if !pair.is_empty() => symbol_name(&pair[0]).map(str::to_string),
            Term::Atom(name) => Some(name.clone()),
            _ => None,
        })
        .collect()
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
