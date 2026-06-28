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
        Term::List(items) if items.len() == 2 => {
            if matches!(items.first(), Some(Term::Atom(s)) if s == "-") {
                int_literal(&items[1]).map(|v| -v)
            } else {
                None
            }
        }
        _ => None,
    }
}

pub fn is_symbol(t: &Term) -> bool {
    match t {
        Term::Atom(s) => {
            s != "true"
                && s != "false"
                && !smt2::term::is_int_literal_string(s)
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

pub fn substitute_symbol(term: &Term, name: &str, replacement: &Term) -> Term {
    if let Some(sym) = symbol_name(term) {
        if sym == name {
            return replacement.clone();
        }
        return term.clone();
    }
    let Term::List(items) = term else {
        return term.clone();
    };
    if matches!(items.first(), Some(Term::Atom(s)) if s == "forall" || s == "exists")
        && items.len() >= 3
    {
        let bound = quantifier_var_names(&items[1]);
        if bound.contains(name) {
            return term.clone();
        }
        return Term::List(vec![
            items[0].clone(),
            items[1].clone(),
            substitute_symbol(&items[2], name, replacement),
        ]);
    }
    Term::List(
        std::iter::once(items[0].clone())
            .chain(
                items[1..]
                    .iter()
                    .map(|arg| substitute_symbol(arg, name, replacement)),
            )
            .collect(),
    )
}

/// Inline ``(let ((x t) ...) body)`` bindings for term collection / rewriting.
pub fn expand_lets(term: &Term) -> Term {
    let Term::List(items) = term else {
        return term.clone();
    };
    if matches!(items.first(), Some(Term::Atom(s)) if s == "let") && items.len() >= 3 {
        let mut body = expand_lets(&items[2]);
        if let Term::List(binders) = &items[1] {
            for binder in binders.iter().rev() {
                let Term::List(pair) = binder else {
                    continue;
                };
                if pair.len() < 2 {
                    continue;
                }
                let Some(name) = symbol_name(&pair[0]).map(str::to_string) else {
                    continue;
                };
                let val = expand_lets(&pair[1]);
                body = substitute_symbol(&body, &name, &val);
            }
        }
        return body;
    }
    Term::List(
        std::iter::once(items[0].clone())
            .chain(items[1..].iter().map(expand_lets))
            .collect(),
    )
}

pub fn free_variables(f: &Term) -> HashSet<String> {
    scoped_free_variables(f, &HashSet::new())
}

pub fn scoped_free_variables(term: &Term, bound: &HashSet<String>) -> HashSet<String> {
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
    if matches!(items.first(), Some(Term::Atom(s)) if s == "let") && items.len() >= 3 {
        let mut new_bound = bound.clone();
        if let Term::List(binders) = &items[1] {
            for binder in binders {
                let Term::List(pair) = binder else {
                    continue;
                };
                if let Some(name) = symbol_name(&pair[0]) {
                    new_bound.insert(name.to_string());
                }
            }
        }
        let mut free = HashSet::new();
        if let Term::List(binders) = &items[1] {
            for binder in binders {
                let Term::List(pair) = binder else {
                    continue;
                };
                if pair.len() >= 2 {
                    free.extend(scoped_free_variables(&pair[1], bound));
                }
            }
        }
        free.extend(scoped_free_variables(&items[2], &new_bound));
        return free;
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scoped_free_variables_skips_let_binders() {
        let term = Term::parse("(let ((a!1 x)) (= a!1 y))").unwrap();
        let free = scoped_free_variables(&term, &HashSet::new());
        assert!(free.contains("x"));
        assert!(free.contains("y"));
        assert!(!free.contains("a!1"));
    }

    #[test]
    fn big_int_literals_are_not_free_variables() {
        let term = Term::parse("(= x 32561662554329978067493305279605223446198353920)").unwrap();
        let free = free_variables(&term);
        assert_eq!(free, HashSet::from(["x".to_string()]));
    }
}