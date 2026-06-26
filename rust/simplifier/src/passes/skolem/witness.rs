use std::collections::HashSet;

use smt2::{Script, Term};

use super::map::SkolemMap;
use super::term_util::{
    flatten_op, int_literal, is_symbol, iter_nodes, split_product, strip_prefix, symbol_name,
    unwrap_zero_mod_eq,
};

pub type WitnessCandidate = (HashSet<String>, String, Term);

pub fn collect_candidates(script: &Script, field: i128) -> Vec<WitnessCandidate> {
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
    if is_symbol(f) {
        symbol_name(f).map(|s| strip_prefix(s).to_string())
    } else {
        None
    }
}

fn split_symbol_times_sum(parts: &[Term]) -> Option<(Term, HashSet<String>)> {
    if parts.len() != 2 {
        return None;
    }
    for (sym, sum_expr) in [(0, 1), (1, 0)] {
        if !is_symbol(&parts[sym]) {
            continue;
        }
        let sum_terms = flatten_op("+", &parts[sum_expr]);
        if sum_terms.len() < 2 {
            continue;
        }
        let names: Vec<String> = sum_terms
            .iter()
            .filter_map(symbol_key)
            .collect();
        if names.len() != sum_terms.len() {
            continue;
        }
        let factors: HashSet<String> = names.into_iter().collect();
        if symbol_key(&parts[sym]).map(|s| factors.contains(&s)).unwrap_or(false) {
            continue;
        }
        return Some((parts[sym].clone(), factors));
    }
    None
}

fn is_uncollapsed_diff_inv_marker_product(term: &Term, field: i128) -> bool {
    let (coeff, parts) = split_product(term, field);
    if coeff != 1 || parts.len() != 2 {
        return false;
    }
    for (prod_a, prod_b) in [(&parts[0], &parts[1]), (&parts[1], &parts[0])] {
        let Some(bname) = symbol_name(prod_b) else {
            continue;
        };
        if !bname.contains("diff_inv_marker") {
            continue;
        }
        let Term::List(items) = prod_a else {
            continue;
        };
        if !matches!(items.first(), Some(Term::Atom(s)) if s == "+") {
            continue;
        }
        let sum_terms = flatten_op("+", prod_a);
        if sum_terms.len() != 2 {
            continue;
        }
        let n_int = sum_terms.iter().filter(|t| int_literal(t).is_some()).count();
        let n_sym = sum_terms.iter().filter(|t| is_symbol(t)).count();
        if n_int == 1 && n_sym == 1 {
            return true;
        }
    }
    false
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
        if is_uncollapsed_diff_inv_marker_product(&term, field) {
            continue;
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

pub fn contribute(map: &mut SkolemMap, body: &Term, candidates: &[WitnessCandidate], field: i128) {
    if candidates.is_empty() {
        return;
    }
    let unpinned: HashSet<String> = map
        .qvars
        .iter()
        .filter(|q| !map.is_pinned(q))
        .cloned()
        .collect();

    for node in iter_nodes(body) {
        let target = if let Term::List(items) = &node {
            if matches!(items.first(), Some(Term::Atom(s)) if s == "not") && items.len() == 2 {
                &items[1]
            } else {
                &node
            }
        } else {
            &node
        };
        let Some(lhs) = unwrap_zero_mod_eq(target, field) else {
            continue;
        };
        let mut cmp = None;
        let mut factors: HashSet<String> = HashSet::new();
        let mut matched_qvars: Vec<String> = Vec::new();
        let mut ok = true;
        for term in flatten_op("+", &lhs) {
            let (coeff, parts) = split_product(&term, field);
            if coeff == 0 || parts.is_empty() {
                continue;
            }
            if (coeff == 1 || coeff == field - 1) && parts.len() == 1 {
                if let Some(name) = symbol_key(&parts[0]) {
                    if cmp.is_some() {
                        ok = false;
                        break;
                    }
                    cmp = Some(name);
                    continue;
                }
            }
            if coeff == 1 && parts.len() == 2 && is_uncollapsed_diff_inv_marker_product(&term, field) {
                continue;
            }
            if coeff != 1 || parts.len() != 2 {
                ok = false;
                break;
            }
            let (left, right) = (&parts[0], &parts[1]);
            let (qvar, fac_sym) = if is_symbol(left) && is_symbol(right) {
                let ln = symbol_name(left).unwrap_or("");
                let rn = symbol_name(right).unwrap_or("");
                let mk_l = ln.contains("diff_inv_marker");
                let mk_r = rn.contains("diff_inv_marker");
                if mk_r && !mk_l && unpinned.contains(ln) {
                    (ln.to_string(), left.clone())
                } else if mk_l && !mk_r && unpinned.contains(rn) {
                    (rn.to_string(), right.clone())
                } else {
                    ok = false;
                    break;
                }
            } else if is_symbol(left) && unpinned.contains(symbol_name(left).unwrap_or("")) {
                (symbol_name(left).unwrap().to_string(), right.clone())
            } else if is_symbol(right) && unpinned.contains(symbol_name(right).unwrap_or("")) {
                (symbol_name(right).unwrap().to_string(), left.clone())
            } else {
                ok = false;
                break;
            };
            let Some(factor) = symbol_key(&fac_sym) else {
                ok = false;
                break;
            };
            factors.insert(factor);
            matched_qvars.push(qvar);
        }
        if !ok || cmp.is_none() || matched_qvars.len() < 2 {
            continue;
        }
        let cmp = cmp.unwrap();
        for (candidate_factors, candidate_cmp, free_var) in candidates {
            if cmp == *candidate_cmp && factors == *candidate_factors {
                for qvar in matched_qvars {
                    map.pin(&qvar, free_var.clone(), "witness");
                }
                break;
            }
        }
    }
}
