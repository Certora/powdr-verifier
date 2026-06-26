//! Collapsed/expanded witness substitution in ``forall`` bodies (Python ``witness.py`` parity).

use std::collections::{HashMap, HashSet};

use smt2::{Script, Term};
use smt2::parse::Command;

use crate::passes::skolem::term_util::{
    atom, field_mod, flatten_op, is_symbol, iter_nodes, list, split_product, strip_prefix,
    symbol_name, unwrap_zero_mod_eq,
};

type WitnessCandidate = (HashSet<String>, String, Term);

pub fn apply(script: &Script) -> Result<(Script, serde_json::Value), String> {
    let field = field_mod().ok_or("SIMPLIFIER_FIELD_MOD not set")?;
    let candidates = collect_candidates(script, field);
    let n_cand = candidates.len();
    if candidates.is_empty() {
        return Ok((
            script.clone(),
            serde_json::json!({ "witness_candidates": 0 }),
        ));
    }

    let mut commands = Vec::new();
    for cmd in &script.commands {
        if cmd.name() == "assert" {
            let body = smt2::term::assert_body(&cmd.raw)
                .ok_or_else(|| format!("malformed assert: {}", cmd.raw))?;
            let term = Term::parse(&body)?;
            let new_body = walk_term(&term, &candidates, field);
            let new_raw = smt2::term::replace_assert_body(&cmd.raw, &new_body.to_string());
            commands.push(Command::new(new_raw));
        } else {
            commands.push(cmd.clone());
        }
    }

    Ok((
        Script::from_commands(commands),
        serde_json::json!({ "witness_candidates": n_cand }),
    ))
}

fn collect_candidates(script: &Script, field: i128) -> Vec<WitnessCandidate> {
    let mut candidates = Vec::new();
    for cmd in &script.commands {
        if cmd.name() != "assert" {
            continue;
        }
        if let Some(body) = smt2::term::assert_body(&cmd.raw) {
            if let Ok(term) = Term::parse(&body) {
                for node in iter_nodes(&term) {
                    if let Some(m) = match_collapsed(&node, field) {
                        candidates.push(m);
                    }
                }
            }
        }
    }
    candidates
}

fn symbol_key(f: &Term) -> Option<String> {
    symbol_name(f).map(|s| strip_prefix(s).to_string())
}

fn split_symbol_times_sum(parts: &[Term]) -> Option<(Term, HashSet<String>)> {
    if parts.len() != 2 {
        return None;
    }
    for (sym_idx, sum_idx) in [(0, 1), (1, 0)] {
        if !is_symbol(&parts[sym_idx]) {
            continue;
        }
        let sum_terms = flatten_op("+", &parts[sum_idx]);
        if sum_terms.len() < 2 {
            continue;
        }
        let names: Vec<String> = sum_terms.iter().filter_map(symbol_key).collect();
        if names.len() != sum_terms.len() {
            continue;
        }
        let factors: HashSet<String> = names.into_iter().collect();
        if symbol_key(&parts[sym_idx])
            .map(|s| factors.contains(&s))
            .unwrap_or(false)
        {
            continue;
        }
        return Some((parts[sym_idx].clone(), factors));
    }
    None
}

fn match_collapsed(f: &Term, field: i128) -> Option<WitnessCandidate> {
    let lhs = unwrap_zero_mod_eq(f, field)?;
    let mut free_var = None;
    let mut factors = None;
    let mut cmp = None;
    for term in flatten_op("+", &lhs) {
        let (coeff, parts) = split_product(&term, field);
        if coeff == 0 || parts.is_empty() {
            continue;
        }
        if (coeff == 1 || coeff == field - 1) && parts.len() == 1 {
            if let Some(name) = symbol_key(&parts[0]) {
                if cmp.is_some() {
                    return None;
                }
                cmp = Some(name);
                continue;
            }
        }
        if coeff != 1 {
            return None;
        }
        let m = split_symbol_times_sum(&parts)?;
        if factors.is_some() {
            return None;
        }
        free_var = Some(m.0);
        factors = Some(m.1);
    }
    let free_var = free_var?;
    let factors = factors?;
    let cmp = cmp?;
    if symbol_key(&free_var).as_deref() == Some(cmp.as_str()) {
        return None;
    }
    Some((factors, cmp, free_var))
}

fn match_expanded(
    f: &Term,
    qvars: &HashSet<String>,
    candidates: &[WitnessCandidate],
    field: i128,
) -> Option<HashMap<String, Term>> {
    let lhs = unwrap_zero_mod_eq(f, field)?;
    let mut cmp = None;
    let mut factors: HashSet<String> = HashSet::new();
    let mut qmap: HashMap<String, String> = HashMap::new();
    for term in flatten_op("+", &lhs) {
        let (coeff, parts) = split_product(&term, field);
        if coeff == 0 || parts.is_empty() {
            continue;
        }
        if (coeff == 1 || coeff == field - 1) && parts.len() == 1 {
            if let Some(name) = symbol_key(&parts[0]) {
                if is_symbol(&parts[0]) && qvars.contains(symbol_name(&parts[0]).unwrap()) {
                    continue;
                }
                if cmp.is_some() {
                    return None;
                }
                cmp = Some(name);
                continue;
            }
        }
        if coeff != 1 || parts.len() != 2 {
            return None;
        }
        let (left, right) = (&parts[0], &parts[1]);
        let qvar = if is_symbol(left) && qvars.contains(symbol_name(left).unwrap_or("")) {
            symbol_name(left)?.to_string()
        } else if is_symbol(right) && qvars.contains(symbol_name(right).unwrap_or("")) {
            symbol_name(right)?.to_string()
        } else {
            return None;
        };
        let fac_sym = if qvar == symbol_name(left).unwrap_or("") {
            right
        } else {
            left
        };
        let factor = symbol_key(fac_sym)?;
        factors.insert(factor.clone());
        qmap.insert(qvar, factor);
    }
    let cmp = cmp?;
    if qmap.len() < 2 {
        return None;
    }
    for (candidate_factors, candidate_cmp, free_var) in candidates {
        if cmp == *candidate_cmp && factors == *candidate_factors {
            return Some(
                qmap
                    .keys()
                    .map(|q| (q.clone(), free_var.clone()))
                    .collect(),
            );
        }
    }
    None
}

fn not_inner_or_self(node: &Term) -> &Term {
    if let Term::List(items) = node {
        if matches!(items.first(), Some(Term::Atom(s)) if s == "not") && items.len() == 2 {
            return &items[1];
        }
    }
    node
}

fn walk_term(term: &Term, candidates: &[WitnessCandidate], field: i128) -> Term {
    if is_forall(term) {
        return walk_forall(term, candidates, field);
    }
    match term {
        Term::List(items) if !items.is_empty() => Term::List(
            std::iter::once(items[0].clone())
                .chain(items[1..].iter().map(|a| walk_term(a, candidates, field)))
                .collect(),
        ),
        _ => term.clone(),
    }
}

fn is_forall(term: &Term) -> bool {
    matches!(
        term,
        Term::List(items)
            if matches!(items.first(), Some(Term::Atom(s)) if s == "forall")
                && items.len() >= 3
    )
}

fn walk_forall(term: &Term, candidates: &[WitnessCandidate], field: i128) -> Term {
    let Term::List(items) = term else {
        return term.clone();
    };
    let qvar_list = parse_qvar_decls_raw(&items[1]);
    let body = &items[2];
    let qvars: HashSet<String> = qvar_list.iter().map(|(n, _)| n.clone()).collect();
    let qvar_order: Vec<String> = qvar_list.iter().map(|(n, _)| n.clone()).collect();

    let mut substitutions: HashMap<String, Term> = HashMap::new();
    for node in iter_nodes(body) {
        let target = not_inner_or_self(&node);
        if let Some(map) = match_expanded(target, &qvars, candidates, field) {
            substitutions.extend(map);
        }
    }
    if substitutions.is_empty() {
        return term.clone();
    }

    let new_body = substitute(body, &substitutions);
    let remaining: HashSet<String> = qvar_order
        .iter()
        .filter(|q| !substitutions.contains_key(*q))
        .cloned()
        .collect();
    if remaining.is_empty() {
        return new_body;
    }
    let decls = rebuild_qvar_decls(&qvar_order, &qvar_list, &remaining);
    list("forall", vec![decls, new_body])
}

fn substitute(term: &Term, map: &HashMap<String, Term>) -> Term {
    if let Some(name) = symbol_name(term) {
        if let Some(repl) = map.get(name) {
            return repl.clone();
        }
    }
    match term {
        Term::List(items) => Term::List(items.iter().map(|a| substitute(a, map)).collect()),
        _ => term.clone(),
    }
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

#[cfg(test)]
mod tests {
    use super::*;

    fn field() -> i128 {
        field_mod().unwrap_or(2013265921)
    }

    #[test]
    fn maps_expanded_markers_to_collapsed_free_var() {
        let f = field();
        std::env::set_var("SIMPLIFIER_FIELD_MOD", f.to_string());
        let script = Script::parse(&format!(
            "(assert (= (mod (+ (* after-w@3 (+ after-a__0@0 after-a__1@1)) (* (- 1) after-cmp@2)) {f}) 0))\n\
             (assert (forall ((before-u@4 Int)(before-v@5 Int)) \
             (or (not (= (mod (+ (* before-a__0@0 before-u@4) (* before-a__1@1 before-v@5) \
             (* (- 1) before-cmp@2)) {f}) 0)) (= before-cmp@2 after-cmp@2))))\n\
             (check-sat)\n"
        ))
        .unwrap();
        let (out, stats) = apply(&script).unwrap();
        assert_eq!(stats["witness_candidates"], 1);
        let s = smt2::dump_string(&out);
        assert!(!s.contains("(forall"));
        assert!(s.contains("after-w@3"));
        assert!(!s.contains("before-u@4"));
        assert!(!s.contains("before-v@5"));
    }
}
