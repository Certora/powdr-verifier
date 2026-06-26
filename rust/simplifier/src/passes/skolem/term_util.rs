use std::collections::HashSet;

use smt2::Term;

use super::types::SortKind;

pub fn field_mod() -> Option<i128> {
    std::env::var("SIMPLIFIER_FIELD_MOD")
        .ok()
        .and_then(|s| s.parse().ok())
}

pub fn atom(s: &str) -> Term {
    Term::Atom(s.to_string())
}

pub fn list(head: &str, args: Vec<Term>) -> Term {
    let mut items = vec![atom(head)];
    items.extend(args);
    Term::List(items)
}

pub fn term_key(t: &Term) -> String {
    t.to_string()
}

pub fn int_literal(t: &Term) -> Option<i128> {
    match t {
        Term::Atom(s) => smt2::term::parse_int_literal(s),
        _ => None,
    }
}

pub fn is_symbol(t: &Term) -> bool {
    match t {
        Term::Atom(s) => {
            s != "true"
                && s != "false"
                && smt2::term::parse_int_literal(s).is_none()
        }
        _ => false,
    }
}

pub fn symbol_name(t: &Term) -> Option<&str> {
    match t {
        Term::Atom(s) => Some(s.as_str()),
        _ => None,
    }
}

pub fn strip_prefix(name: &str) -> &str {
    for prefix in ["before-", "after-"] {
        if let Some(rest) = name.strip_prefix(prefix) {
            return rest;
        }
    }
    name
}

pub fn swap_prefix(name: &str) -> Option<String> {
    if let Some(rest) = name.strip_prefix("before-") {
        return Some(format!("after-{rest}"));
    }
    if let Some(rest) = name.strip_prefix("after-") {
        return Some(format!("before-{rest}"));
    }
    None
}

pub fn is_program_variable(name: &str) -> bool {
    strip_prefix(name).contains('@')
}

pub fn iter_nodes(f: &Term) -> Vec<Term> {
    let mut out = Vec::new();
    walk(f, &mut out);
    out
}

fn walk(f: &Term, out: &mut Vec<Term>) {
    out.push(f.clone());
    if let Term::List(items) = f {
        for a in &items[1..] {
            walk(a, out);
        }
    }
}

pub fn flatten_op(head: &str, f: &Term) -> Vec<Term> {
    if let Term::List(items) = f {
        if matches!(items.first(), Some(Term::Atom(s)) if s == head) {
            return items[1..]
                .iter()
                .flat_map(|a| flatten_op(head, a))
                .collect();
        }
    }
    vec![f.clone()]
}

pub fn split_product(f: &Term, p: i128) -> (i128, Vec<Term>) {
    let mut coeff = 1i128;
    let mut factors = Vec::new();
    for a in flatten_op("*", f) {
        if let Some(c) = int_literal(&a) {
            coeff = (coeff * c).rem_euclid(p);
        } else {
            factors.push(a.clone());
        }
    }
    (coeff, factors)
}

pub fn unwrap_zero_mod_eq(f: &Term, field: i128) -> Option<Term> {
    let Term::List(items) = f else {
        return None;
    };
    if !matches!(items.first(), Some(Term::Atom(s)) if s == "=") || items.len() != 3 {
        return None;
    }
    let (lhs, rhs) = (&items[1], &items[2]);
    let inner = if int_literal(rhs) == Some(0) {
        lhs
    } else if int_literal(lhs) == Some(0) {
        rhs
    } else {
        return None;
    };
    let Term::List(mod_items) = inner else {
        return None;
    };
    if !matches!(mod_items.first(), Some(Term::Atom(s)) if s == "mod") || mod_items.len() != 3 {
        return None;
    }
    if int_literal(&mod_items[2]) != Some(field) {
        return None;
    }
    Some(mod_items[1].clone())
}

pub fn free_variables(f: &Term) -> HashSet<String> {
    let mut out = HashSet::new();
    collect_free(f, &mut out);
    out
}

fn collect_free(f: &Term, out: &mut HashSet<String>) {
    if is_symbol(f) {
        out.insert(symbol_name(f).unwrap().to_string());
        return;
    }
    if let Term::List(items) = f {
        for a in &items[1..] {
            collect_free(a, out);
        }
    }
}

pub fn wrap_mod_expr(expr: Term, p: i128) -> Term {
    list("mod", vec![expr, atom(&p.to_string())])
}

pub fn sort_from_decl(raw: &str) -> SortKind {
    if raw.contains("(Array") || raw.contains(" Array ") {
        SortKind::Array
    } else if raw.contains("Bool") {
        SortKind::Bool
    } else if raw.contains("Int") {
        SortKind::Int
    } else {
        SortKind::Other
    }
}

pub fn symbol_sort(name: &str, sorts: &std::collections::HashMap<String, SortKind>) -> SortKind {
    sorts.get(name).copied().unwrap_or(SortKind::Other)
}