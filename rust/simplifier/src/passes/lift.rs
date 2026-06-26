//! Hoist ``Not(= q expr)`` skolem disjuncts from ``forall`` bodies to top-level asserts.

use std::collections::{HashMap, HashSet};

use smt2::{Script, Term};
use smt2::parse::Command;

use crate::passes::skolem::term_util::{atom, free_variables, is_symbol, list, symbol_name};
use crate::passes::skolem::utils::declare_fun_name;

pub fn apply(script: &Script) -> Result<(Script, serde_json::Value), String> {
    let qvar_sorts = collect_qvar_sort_strings(script);
    let declared_sorts = collect_declared_sorts(script);
    let mut declared: HashSet<String> = declared_sorts.keys().cloned().collect();
    let mut lifted: HashMap<String, Term> = HashMap::new();

    let mut prefix = Vec::new();
    let mut suffix = Vec::new();
    let mut in_prefix = true;

    for cmd in &script.commands {
        if cmd.name() == "declare-fun" {
            if let Some(name) = declare_fun_name(&cmd.raw) {
                declared.insert(name);
            }
        }
        if cmd.name() == "assert" {
            in_prefix = false;
            let body = smt2::term::assert_body(&cmd.raw).ok_or_else(|| {
                format!("malformed assert: {}", cmd.raw)
            })?;
            let term = Term::parse(&body)?;
            let new_body = walk_term(&term, &mut lifted);
            let new_raw = smt2::term::replace_assert_body(&cmd.raw, &new_body.to_string());
            suffix.push(Command::new(new_raw));
        } else if in_prefix {
            prefix.push(cmd.clone());
        } else {
            suffix.push(cmd.clone());
        }
    }

    let mut to_declare: HashMap<String, String> = HashMap::new();
    for q in lifted.keys() {
        if let Some(sort) = qvar_sorts.get(q).or_else(|| declared_sorts.get(q)) {
            to_declare.insert(q.clone(), sort.clone());
        }
    }
    for eq in lifted.values() {
        for sym in free_variables(eq) {
            if declared.contains(&sym) || to_declare.contains_key(&sym) {
                continue;
            }
            if let Some(sort) = qvar_sorts.get(&sym).or_else(|| declared_sorts.get(&sym)) {
                to_declare.insert(sym, sort.clone());
            }
        }
    }

    let mut inserts = Vec::new();
    for (name, sort) in &to_declare {
        if declared.contains(name) {
            continue;
        }
        inserts.push(Command::new(format!("(declare-fun {name} () {sort})")));
        declared.insert(name.clone());
    }
    let n_decl = inserts.len();
    for eq in lifted.values() {
        inserts.push(Command::new(format!("(assert {})", eq.to_string())));
    }
    let n_pin = inserts.len() - n_decl;

    let mut commands = prefix;
    commands.extend(inserts);
    commands.extend(suffix);

    let stats = serde_json::json!({
        "pins_lifted": lifted.len(),
        "new_declarations": n_decl,
        "hoisted_pin_asserts": n_pin,
    });
    Ok((Script::from_commands(commands), stats))
}

fn walk_term(term: &Term, lifted: &mut HashMap<String, Term>) -> Term {
    if is_forall(term) {
        return lift_forall(term, lifted);
    }
    match term {
        Term::List(items) if !items.is_empty() => {
            let head = items[0].clone();
            if matches!(&head, Term::Atom(s) if s == "exists") {
                return term.clone();
            }
            Term::List(
                std::iter::once(head)
                    .chain(items[1..].iter().map(|a| walk_term(a, lifted)))
                    .collect(),
            )
        }
        _ => term.clone(),
    }
}

fn is_forall(term: &Term) -> bool {
    matches!(term, Term::List(items) if matches!(items.first(), Some(Term::Atom(s)) if s == "forall") && items.len() >= 3)
}

fn lift_forall(term: &Term, lifted: &mut HashMap<String, Term>) -> Term {
    let Term::List(items) = term else {
        return term.clone();
    };
    let qvar_list = parse_qvar_decls_raw(&items[1]);
    let body = &items[2];

    let Term::List(body_items) = body else {
        return term.clone();
    };
    if !matches!(body_items.first(), Some(Term::Atom(s)) if s == "or") {
        return term.clone();
    }

    let mut qvars: HashSet<String> = qvar_list.iter().map(|(n, _)| n.clone()).collect();
    let qvar_order: Vec<String> = qvar_list.iter().map(|(n, _)| n.clone()).collect();
    let mut candidates: HashSet<String> = body_items[1..]
        .iter()
        .filter(|d| is_potential_lift_pair(d))
        .map(|d| d.to_string())
        .collect();
    let candidate_terms: HashMap<String, Term> = body_items[1..]
        .iter()
        .filter(|d| is_potential_lift_pair(d))
        .map(|d| (d.to_string(), d.clone()))
        .collect();

    let mut lifted_disjuncts: HashSet<String> = HashSet::new();
    let mut progressed = true;
    while progressed {
        progressed = false;
        let mut keys: Vec<String> = candidates.iter().cloned().collect();
        keys.sort();
        for key in keys {
            let Some(d) = candidate_terms.get(&key) else {
                continue;
            };
            if let Some((q, eq)) = match_lift_pair(d, &qvars) {
                candidates.remove(&key);
                lifted.insert(q.clone(), eq);
                lifted_disjuncts.insert(key);
                qvars.remove(&q);
                progressed = true;
            }
        }
    }

    let remaining: Vec<Term> = body_items[1..]
        .iter()
        .filter(|a| !lifted_disjuncts.contains(&a.to_string()))
        .cloned()
        .collect();

    let body_out = if remaining.is_empty() {
        atom("false")
    } else if remaining.len() == 1 {
        remaining[0].clone()
    } else {
        list("or", remaining)
    };

    if qvar_order.iter().any(|q| qvars.contains(q)) {
        let decls = rebuild_qvar_decls(&qvar_order, &qvar_list, &qvars);
        return list("forall", vec![decls, body_out]);
    }
    body_out
}

fn parse_qvar_decls_raw(decls: &Term) -> Vec<(String, Term)> {
    let Term::List(items) = decls else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for d in items {
        match d {
            Term::List(pair) if pair.len() == 2 => {
                let name = match &pair[0] {
                    Term::Atom(s) => s.clone(),
                    _ => continue,
                };
                out.push((name, pair[1].clone()));
            }
            Term::Atom(name) => out.push((name.clone(), atom("Int"))),
            _ => {}
        }
    }
    out
}

fn rebuild_qvar_decls(
    order: &[String],
    qvar_list: &[(String, Term)],
    remaining: &HashSet<String>,
) -> Term {
    let decls: Vec<Term> = order
        .iter()
        .filter(|q| remaining.contains(*q))
        .filter_map(|q| {
            let sort = qvar_list.iter().find(|(n, _)| n == q).map(|(_, s)| s.clone())?;
            Some(Term::List(vec![Term::Atom(q.clone()), sort]))
        })
        .collect();
    Term::List(decls)
}

fn is_potential_lift_pair(d: &Term) -> bool {
    let Term::List(items) = d else {
        return false;
    };
    if !matches!(items.first(), Some(Term::Atom(s)) if s == "not") || items.len() != 2 {
        return false;
    }
    is_hoistable_eq(&items[1])
}

fn is_hoistable_eq(eq: &Term) -> bool {
    let Term::List(items) = eq else {
        return false;
    };
    matches!(items.first(), Some(Term::Atom(s)) if s == "=" || s == "iff")
}

fn match_lift_pair(d: &Term, qvars: &HashSet<String>) -> Option<(String, Term)> {
    let Term::List(items) = d else {
        return None;
    };
    match_hoistable_eq(&items[1], qvars)
}

fn match_hoistable_eq(eq: &Term, qvars: &HashSet<String>) -> Option<(String, Term)> {
    let Term::List(items) = eq else {
        return None;
    };
    if !matches!(items.first(), Some(Term::Atom(s)) if s == "=" || s == "iff") || items.len() != 3 {
        return None;
    }
    for (vside, expr) in [(&items[1], &items[2]), (&items[2], &items[1])] {
        if !is_symbol(vside) {
            continue;
        }
        let name = symbol_name(vside)?.to_string();
        if !qvars.contains(&name) {
            continue;
        }
        if !free_variables(expr).is_disjoint(qvars) {
            continue;
        }
        return Some((name, eq.clone()));
    }
    None
}

fn collect_qvar_sort_strings(script: &Script) -> HashMap<String, String> {
    let mut out = HashMap::new();
    for cmd in &script.commands {
        if cmd.name() != "assert" {
            continue;
        }
        if let Some(body) = smt2::term::assert_body(&cmd.raw) {
            if let Ok(term) = Term::parse(&body) {
                collect_qvar_sorts_term(&term, &mut out);
            }
        }
    }
    out
}

fn collect_qvar_sorts_term(term: &Term, out: &mut HashMap<String, String>) {
    if let Term::List(items) = term {
        if matches!(items.first(), Some(Term::Atom(s)) if s == "forall") && items.len() >= 3 {
            for (name, sort) in parse_qvar_decls_raw(&items[1]) {
                out.insert(name, sort_term_to_string(&sort));
            }
            collect_qvar_sorts_term(&items[2], out);
        } else {
            for a in &items[1..] {
                collect_qvar_sorts_term(a, out);
            }
        }
    }
}

fn sort_term_to_string(sort: &Term) -> String {
    match sort {
        Term::Atom(s) => s.clone(),
        Term::List(items) => {
            let inner: Vec<String> = items.iter().map(sort_term_to_string).collect();
            format!("({})", inner.join(" "))
        }
    }
}

fn collect_declared_sorts(script: &Script) -> HashMap<String, String> {
    let mut out = HashMap::new();
    for cmd in &script.commands {
        if cmd.name() != "declare-fun" {
            continue;
        }
        if let Some((name, sort)) = parse_declare_fun_sort(&cmd.raw) {
            out.insert(name, sort);
        }
    }
    out
}


fn parse_declare_fun_sort(raw: &str) -> Option<(String, String)> {
    let name = declare_fun_name(raw)?;
    let inner = raw.trim().strip_prefix('(')?.trim().strip_suffix(')')?;
    let rest = inner.strip_prefix("declare-fun")?.trim();
    let after_name = rest.strip_prefix(&name)?.trim();
    let after_name = after_name.strip_prefix("()")?.trim();
    Some((name, after_name.to_string()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lifts_single_var() {
        let script = Script::parse(
            "(assert (forall ((lx Int)) (or (not (= lx 7)) (< lx 0))))\n(check-sat)\n",
        )
        .unwrap();
        let (out, stats) = apply(&script).unwrap();
        let s = smt2::dump_string(&out);
        assert!(s.contains("(assert (= lx 7))"));
        assert!(s.contains("(< lx 0)"));
        assert!(!s.contains("(forall"));
        assert_eq!(stats["pins_lifted"], 1);
    }

    #[test]
    fn lifts_two_vars_in_sequence() {
        let script = Script::parse(
            "(assert (forall ((lx2 Int) (ly2 Int)) (or (not (= lx2 1)) (not (= ly2 2)) (< ly2 lx2))))\n(check-sat)\n",
        )
        .unwrap();
        let (out, _) = apply(&script).unwrap();
        let s = smt2::dump_string(&out);
        assert!(s.contains("(assert (= lx2 1))"));
        assert!(s.contains("(assert (= ly2 2))"));
        assert!(s.contains("(< ly2 lx2)"));
        assert!(!s.contains("(forall"));
    }

    #[test]
    fn skips_when_expr_mentions_other_qvar() {
        let script = Script::parse(
            "(assert (forall ((lsx Int) (lsy Int)) (or (not (= lsx lsy)) (< lsx 0))))\n(check-sat)\n",
        )
        .unwrap();
        let (out, _) = apply(&script).unwrap();
        let s = smt2::dump_string(&out);
        assert!(s.contains("(forall"));
        assert!(!s.contains("(assert (= lsx lsy))"));
    }

    #[test]
    fn removes_lifted_disjunct() {
        let script = Script::parse(
            "(assert (forall ((lift_x Int)) (or (not (= lift_x 0)) (> lift_x 1))))\n(check-sat)\n",
        )
        .unwrap();
        let (out, _) = apply(&script).unwrap();
        let s = smt2::dump_string(&out);
        assert!(s.contains("(assert (= lift_x 0))"));
        assert!(s.contains("(> lift_x 1)"));
        assert!(!s.contains("(or"));
    }
}
