use std::collections::HashSet;

use smt2::ast_build::split_product_int;
use smt2::ast_util::{decl_name, int_value_dyn, unwrap_zero_mod_eq};
use smt2::{iter_nodes_dyn, strip_prefix, symbol_name_dyn, Script};
use z3::ast::{Ast, AstKind, Bool, Dynamic, Int};

use super::map::SkolemMap;

pub type WitnessCandidate = (HashSet<String>, String, Dynamic);

pub fn collect_candidates(script: &Script, field: i128) -> Vec<WitnessCandidate> {
    let mut candidates = Vec::new();
    for cmd in &script.commands {
        if let Some(body) = cmd.assert_bool() {
            for node in iter_nodes_dyn(&Dynamic::from_ast(body)) {
                if let Some(node_b) = node.as_bool() {
                    if let Some(m) = match_collapsed(&node_b, field) {
                        candidates.push(m);
                    }
                }
            }
        }
    }
    candidates
}

fn symbol_key(f: &Dynamic) -> Option<String> {
    if is_symbol_int(f) {
        symbol_name_dyn(f).map(|s| strip_prefix(&s).to_string())
    } else {
        None
    }
}

fn split_symbol_times_sum(parts: &[Int]) -> Option<(Dynamic, HashSet<String>)> {
    if parts.len() != 2 {
        return None;
    }
    for (sym, sum_expr) in [(0, 1), (1, 0)] {
        if !is_symbol_int(&Dynamic::from_ast(&parts[sym])) {
            continue;
        }
        let sum_terms = flatten_add(&parts[sum_expr]);
        if sum_terms.len() < 2 {
            continue;
        }
        let names: Vec<String> = sum_terms
            .iter()
            .filter_map(|t| symbol_key(&Dynamic::from_ast(t)))
            .collect();
        if names.len() != sum_terms.len() {
            continue;
        }
        let factors: HashSet<String> = names.into_iter().collect();
        if symbol_key(&Dynamic::from_ast(&parts[sym]))
            .map(|s| factors.contains(&s))
            .unwrap_or(false)
        {
            continue;
        }
        return Some((Dynamic::from_ast(&parts[sym]), factors));
    }
    None
}

fn is_uncollapsed_diff_inv_marker_product(term: &Int, field: i128) -> bool {
    let (coeff, parts) = split_product_int(term, field);
    if coeff != 1 || parts.len() != 2 {
        return false;
    }
    for (prod_a, prod_b) in [(&parts[0], &parts[1]), (&parts[1], &parts[0])] {
        let Some(bname) = symbol_name_dyn(&Dynamic::from_ast(prod_b)) else {
            continue;
        };
        if !bname.contains("diff_inv_marker") {
            continue;
        }
        if decl_name(&Dynamic::from_ast(prod_a).decl()) != "+" {
            continue;
        }
        let sum_terms = flatten_add(prod_a);
        if sum_terms.len() != 2 {
            continue;
        }
        let n_int = sum_terms
            .iter()
            .filter(|t| int_value_dyn(&Dynamic::from_ast(*t)).is_some())
            .count();
        let n_sym = sum_terms
            .iter()
            .filter(|t| is_symbol_int(&Dynamic::from_ast(*t)))
            .count();
        if n_int == 1 && n_sym == 1 {
            return true;
        }
    }
    false
}

fn match_collapsed(f: &Bool, field: i128) -> Option<WitnessCandidate> {
    let lhs = unwrap_zero_mod_eq(f, field)?;
    let mut free_var = None;
    let mut factors = None;
    let mut cmp = None;
    for term in flatten_add(&lhs) {
        let (coeff, parts) = split_product_int(&term, field);
        if coeff == 0 || parts.is_empty() {
            continue;
        }
        if (coeff == 1 || coeff == field - 1) && parts.len() == 1 {
            if let Some(name) = symbol_key(&Dynamic::from_ast(&parts[0])) {
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

pub fn contribute(map: &mut SkolemMap, body: &Bool, candidates: &[WitnessCandidate], field: i128) {
    if candidates.is_empty() {
        return;
    }
    let unpinned: HashSet<String> = map
        .qvars
        .iter()
        .filter(|q| !map.is_pinned(q))
        .cloned()
        .collect();

    for node in iter_nodes_dyn(&Dynamic::from_ast(body)) {
        let Some(node_b) = node.as_bool() else {
            continue;
        };
        let target = if decl_name(&Dynamic::from_ast(&node_b).decl()) == "not" {
            Dynamic::from_ast(&node_b)
                .nth_child(0)
                .and_then(|c| c.as_bool())
                .unwrap_or(node_b.clone())
        } else {
            node_b
        };
        let Some(lhs) = unwrap_zero_mod_eq(&target, field) else {
            continue;
        };
        let mut cmp = None;
        let mut factors: HashSet<String> = HashSet::new();
        let mut matched_qvars: Vec<String> = Vec::new();
        let mut ok = true;
        for term in flatten_add(&lhs) {
            let (coeff, parts) = split_product_int(&term, field);
            if coeff == 0 || parts.is_empty() {
                continue;
            }
            if (coeff == 1 || coeff == field - 1) && parts.len() == 1 {
                if let Some(name) = symbol_key(&Dynamic::from_ast(&parts[0])) {
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
            let left_dyn = Dynamic::from_ast(left);
            let right_dyn = Dynamic::from_ast(right);
            let (qvar, fac_sym) = if is_symbol_int(&left_dyn) && is_symbol_int(&right_dyn) {
                let ln = symbol_name_dyn(&left_dyn).unwrap_or_default();
                let rn = symbol_name_dyn(&right_dyn).unwrap_or_default();
                let mk_l = ln.contains("diff_inv_marker");
                let mk_r = rn.contains("diff_inv_marker");
                if mk_r && !mk_l && unpinned.contains(&ln) {
                    (ln, left_dyn)
                } else if mk_l && !mk_r && unpinned.contains(&rn) {
                    (rn, right_dyn)
                } else {
                    ok = false;
                    break;
                }
            } else if is_symbol_int(&left_dyn)
                && unpinned.contains(&symbol_name_dyn(&left_dyn).unwrap_or_default())
            {
                (symbol_name_dyn(&left_dyn).unwrap_or_default(), right_dyn)
            } else if is_symbol_int(&right_dyn)
                && unpinned.contains(&symbol_name_dyn(&right_dyn).unwrap_or_default())
            {
                (symbol_name_dyn(&right_dyn).unwrap_or_default(), left_dyn)
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
        let cmp = cmp.unwrap_or_default();
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

fn is_symbol_int(ast: &Dynamic) -> bool {
    ast.kind() == AstKind::App
        && ast.as_int().is_some()
        && int_value_dyn(ast).is_none()
        && symbol_name_dyn(ast).is_some()
}

fn flatten_add(ast: &Int) -> Vec<Int> {
    let d = Dynamic::from_ast(ast);
    if d.kind() == AstKind::App && decl_name(&d.decl()) == "+" {
        let mut out = Vec::new();
        for i in 0..d.num_children() {
            if let Some(ch) = d.nth_child(i).and_then(|c| c.as_int()) {
                out.extend(flatten_add(&ch));
            }
        }
        out
    } else {
        vec![ast.clone()]
    }
}
