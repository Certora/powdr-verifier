use std::collections::HashSet;

use smt2::ast_build::split_product_int;
use smt2::ast_util::{int_value_dyn, is_not, symbol_id_dyn, symbol_id_from_name, symbol_name_for_id, unwrap_zero_mod_eq, SymbolId};
use smt2::{iter_nodes_dyn, strip_prefix, symbol_name_dyn, Script};
use z3::ast::{Ast, AstKind, Bool, Dynamic, Int};
use z3::DeclKind;

use super::map::SkolemMap;

pub type WitnessCandidate = (HashSet<Int>, Int, Dynamic);

pub fn collect_candidates(script: &Script, field: i128) -> Vec<WitnessCandidate> {
    let mut candidates = Vec::new();
    for cmd in &script.commands {
        if let Some(body) = cmd.assert_bool() {
            for node in iter_nodes_dyn(&Dynamic::from_ast(body)) {
                if node.kind() != AstKind::App {
                    continue;
                }
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

fn symbol_key(f: &Dynamic) -> Option<Int> {
    if is_symbol_int(f) {
        f.as_int()
    } else {
        None
    }
}

fn split_symbol_times_sum(parts: &[Int]) -> Option<(Dynamic, HashSet<Int>)> {
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
        let factors: HashSet<Int> = sum_terms
            .iter()
            .filter_map(|t| symbol_key(&Dynamic::from_ast(t)))
            .collect();
        if factors.len() != sum_terms.len() {
            continue;
        }
        let sym_node = Dynamic::from_ast(&parts[sym]);
        if let Some(s) = symbol_key(&sym_node) {
            if factors.contains(&s) {
                continue;
            }
        }
        return Some((sym_node, factors));
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
        if Dynamic::from_ast(prod_a).decl().kind() != DeclKind::Add {
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
            if let Some(sym) = symbol_key(&Dynamic::from_ast(&parts[0])) {
                if cmp.is_some() {
                    return None;
                }
                cmp = Some(sym);
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
    if symbol_key(&free_var).is_some_and(|s| s.ast_eq(&cmp)) {
        return None;
    }
    Some((factors, cmp, free_var))
}

#[cfg(test)]
pub fn match_collapsed_for_test(f: &Bool, field: i128) -> Option<WitnessCandidate> {
    match_collapsed(f, field)
}

pub fn contribute(map: &mut SkolemMap, body: &Bool, candidates: &[WitnessCandidate], field: i128) {
    if candidates.is_empty() {
        return;
    }
    let witness_before = map
        .sources
        .values()
        .filter(|s| s.as_str() == "witness")
        .count();
    contribute_from_body(map, body, candidates, field);
    if map
        .sources
        .values()
        .filter(|s| s.as_str() == "witness")
        .count()
        == witness_before
    {
        contribute_from_candidate_bundles(map, candidates);
    }
}

fn bundle_id(sym: &Int) -> Option<String> {
    let name = symbol_name_dyn(&Dynamic::from_ast(sym))?;
    let stripped = strip_prefix(&name);
    let (_, tail) = stripped.rsplit_once('_')?;
    tail.split('@').next().map(str::to_string)
}

fn contribute_from_candidate_bundles(map: &mut SkolemMap, candidates: &[WitnessCandidate]) {
    for (factors, cmp, free_var) in candidates {
        let bundle_ids: HashSet<String> = factors.iter().filter_map(bundle_id).collect();
        if bundle_ids.len() != 1 {
            continue;
        }
        let bundle = bundle_ids.into_iter().next().unwrap();
        let Some(cmp_name) = symbol_name_dyn(&Dynamic::from_ast(cmp))
            .map(|s| strip_prefix(&s).to_string())
        else {
            continue;
        };
        let cmp_id = symbol_id_from_name(&cmp_name);
        if !map.qvars.contains(&cmp_id) {
            continue;
        }
        let markers: Vec<SymbolId> = map
            .qvars
            .iter()
            .copied()
            .filter(|q| !map.is_pinned(*q))
            .filter(|q| {
                symbol_name_for_id(*q).is_some_and(|name| {
                    let s = strip_prefix(&name);
                    s.contains("diff_inv_marker") && bundle_id_from_name(&name) == Some(bundle.clone())
                })
            })
            .collect();
        if markers.len() < 2 {
            continue;
        }
        for qvar in markers {
            map.pin(qvar, free_var.clone(), "witness");
        }
    }
}

fn bundle_id_from_name(name: &str) -> Option<String> {
    let stripped = strip_prefix(name);
    let (_, tail) = stripped.rsplit_once('_')?;
    tail.split('@').next().map(str::to_string)
}

fn contribute_from_body(map: &mut SkolemMap, body: &Bool, candidates: &[WitnessCandidate], field: i128) {
    let unpinned: HashSet<SymbolId> = map
        .qvars
        .iter()
        .copied()
        .filter(|q| !map.is_pinned(*q))
        .collect();

    for node in iter_nodes_dyn(&Dynamic::from_ast(body)) {
        if node.kind() != AstKind::App {
            continue;
        }
        let Some(node_b) = node.as_bool() else {
            continue;
        };
        let target = is_not(&node_b).unwrap_or_else(|| node_b.clone());
        let Some(lhs) = unwrap_zero_mod_eq(&target, field) else {
            continue;
        };
        let mut cmp = None;
        let mut factors: HashSet<Int> = HashSet::new();
        let mut matched_qvars: Vec<SymbolId> = Vec::new();
        let mut ok = true;
        for term in flatten_add(&lhs) {
            let (coeff, parts) = split_product_int(&term, field);
            if coeff == 0 || parts.is_empty() {
                continue;
            }
            if (coeff == 1 || coeff == field - 1) && parts.len() == 1 {
                if let Some(sym) = symbol_key(&Dynamic::from_ast(&parts[0])) {
                    if cmp.is_some() {
                        ok = false;
                        break;
                    }
                    cmp = Some(sym);
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
                let Some(l_id) = symbol_id_dyn(&left_dyn) else {
                    ok = false;
                    break;
                };
                let Some(r_id) = symbol_id_dyn(&right_dyn) else {
                    ok = false;
                    break;
                };
                let ln = symbol_name_dyn(&left_dyn).unwrap_or_default();
                let rn = symbol_name_dyn(&right_dyn).unwrap_or_default();
                let mk_l = ln.contains("diff_inv_marker");
                let mk_r = rn.contains("diff_inv_marker");
                if mk_r && !mk_l && unpinned.contains(&l_id) {
                    (l_id, left_dyn)
                } else if mk_l && !mk_r && unpinned.contains(&r_id) {
                    (r_id, right_dyn)
                } else {
                    ok = false;
                    break;
                }
            } else if is_symbol_int(&left_dyn) {
                let Some(l_id) = symbol_id_dyn(&left_dyn) else {
                    ok = false;
                    break;
                };
                if unpinned.contains(&l_id) {
                    (l_id, right_dyn)
                } else {
                    ok = false;
                    break;
                }
            } else if is_symbol_int(&right_dyn) {
                let Some(r_id) = symbol_id_dyn(&right_dyn) else {
                    ok = false;
                    break;
                };
                if unpinned.contains(&r_id) {
                    (r_id, left_dyn)
                } else {
                    ok = false;
                    break;
                }
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
            if cmp.ast_eq(candidate_cmp) && factors == *candidate_factors {
                for qvar in matched_qvars {
                    map.pin(qvar, free_var.clone(), "witness");
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
    if d.kind() == AstKind::App && d.decl().kind() == DeclKind::Add {
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
