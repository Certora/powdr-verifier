use std::collections::{HashMap, HashSet};

use smt2::ast_util::bound_var_index;
use smt2::{and_parts, free_variables_bool, iter_nodes_dyn};
use z3::ast::{Ast, Bool, Dynamic, Int as ZInt};
use z3::{SatResult, Solver};

use super::map::SkolemMap;
use super::ast_build::{field_mod, symbol_sort};
use super::types::SortKind;

pub fn contribute(
    map: &mut SkolemMap,
    body: &Bool,
    sorts: &HashMap<String, SortKind>,
    decl_block: &str,
    bound_order: &[String],
) {
    let unpinned: Vec<String> = map
        .qvars
        .iter()
        .filter(|q| {
            !map.is_pinned(q)
                && matches!(symbol_sort(q, sorts), SortKind::Int | SortKind::Bool)
        })
        .cloned()
        .collect();
    let Some(items) = smt2::or_body_parts(body) else {
        return;
    };

    let cand: HashSet<String> = unpinned.into_iter().collect();
    if cand.is_empty() {
        return;
    }

    let mut parent: HashMap<String, String> = cand.iter().map(|q| (q.clone(), q.clone())).collect();

    fn find(parent: &mut HashMap<String, String>, x: &str) -> String {
        let parent_x = parent.get(x).cloned().unwrap_or_else(|| x.to_string());
        if parent_x != x {
            let root = find(parent, &parent_x);
            parent.insert(x.to_string(), root.clone());
            root
        } else {
            x.to_string()
        }
    }

    fn union(parent: &mut HashMap<String, String>, a: &str, b: &str) {
        let ra = find(parent, a);
        let rb = find(parent, b);
        if ra != rb {
            parent.insert(ra, rb);
        }
    }

    let mut tainted: HashSet<String> = HashSet::new();
    let mut disj_cands: Vec<(Vec<String>, Bool)> = Vec::new();

    for d in items {
        let mentioned = qvars_mentioned_in(&d, &cand, bound_order);
        let cset: Vec<String> = mentioned.into_iter().collect();
        if cset.is_empty() {
            continue;
        }
        let rel_parts = qvar_conjuncts(&d, &cand, bound_order);
        let rel_fv: HashSet<String> = rel_parts
            .iter()
            .flat_map(|c| {
                let mut vars = free_variables_bool(c);
                vars.extend(qvars_mentioned_in(c, &map.qvars, bound_order));
                vars
            })
            .collect();
        let relevant = if rel_parts.len() == 1 {
            rel_parts[0].clone()
        } else {
            Bool::and(&rel_parts.iter().collect::<Vec<_>>())
        };
        disj_cands.push((cset.clone(), relevant));
        for other in &cset[1..] {
            union(&mut parent, &cset[0], other);
        }
        if !rel_fv.is_subset(&cand) {
            tainted.extend(cset);
        }
    }

    if disj_cands.is_empty() {
        return;
    }

    let field = field_mod();
    let mut members_by_root: HashMap<String, HashSet<String>> = HashMap::new();
    let mut disjuncts_by_root: HashMap<String, Vec<Bool>> = HashMap::new();
    for q in &cand {
        let root = find(&mut parent, q);
        members_by_root.entry(root).or_default().insert(q.clone());
    }
    for (cset, d) in disj_cands {
        let root = find(&mut parent, &cset[0]);
        disjuncts_by_root.entry(root).or_default().push(d);
    }
    let tainted_roots: HashSet<String> = tainted.iter().map(|q| find(&mut parent, q)).collect();

    for (root, disjuncts) in disjuncts_by_root {
        if tainted_roots.contains(&root) {
            continue;
        }
        let Some(members) = members_by_root.get(&root) else {
            continue;
        };
        let falsify: Vec<Bool> = disjuncts.iter().map(|d| d.not()).collect();
        let model = solve_island(&falsify, members, sorts, decl_block, field);
        for q in members {
            let val = model
                .as_ref()
                .and_then(|m| m.get(q))
                .cloned()
                .unwrap_or_else(|| default_value(q, sorts));
            map.pin(q, val, "isolate");
        }
    }
}

fn qvars_mentioned_in(d: &Bool, cand: &HashSet<String>, bound_order: &[String]) -> HashSet<String> {
    let mut out = HashSet::new();
    for node in iter_nodes_dyn(&Dynamic::from_ast(d)) {
        if let Some(name) = smt2::symbol_name_dyn(&node) {
            if cand.contains(&name) {
                out.insert(name);
            }
        } else if let Some(idx) = bound_var_index(&node) {
            if let Some(name) = bound_order.get(idx) {
                if cand.contains(name) {
                    out.insert(name.clone());
                }
            }
        }
    }
    out
}

fn qvar_conjuncts(d: &Bool, cand: &HashSet<String>, bound_order: &[String]) -> Vec<Bool> {
    let conjs = and_parts(d).unwrap_or_else(|| vec![d.clone()]);
    conjs
        .into_iter()
        .filter(|c| !qvars_mentioned_in(c, cand, bound_order).is_empty())
        .collect()
}

fn default_value(q: &str, sorts: &HashMap<String, SortKind>) -> Dynamic {
    match symbol_sort(q, sorts) {
        SortKind::Bool => Dynamic::from_ast(&Bool::from_bool(false)),
        _ => Dynamic::from_ast(&ZInt::from_i64(0)),
    }
}

fn sort_kind_to_smt(sort: SortKind) -> &'static str {
    match sort {
        SortKind::Bool => "Bool",
        SortKind::Int => "Int",
        SortKind::Array => "(Array Int Int)",
        SortKind::Other => "Int",
    }
}

fn solve_island(
    falsify: &[Bool],
    members: &HashSet<String>,
    sorts: &HashMap<String, SortKind>,
    decl_block: &str,
    field: Option<i128>,
) -> Option<HashMap<String, Dynamic>> {
    let mut input = decl_block.to_string();
    for m in members {
        let sort = symbol_sort(m, sorts);
        input.push_str(&format!(
            "(declare-fun {m} () {})\n",
            sort_kind_to_smt(sort)
        ));
        if let Some(p) = field {
            if sort == SortKind::Int {
                input.push_str(&format!("(assert (and (<= 0 {m}) (< {m} {p})))\n"));
            }
        }
    }
    for f in falsify {
        input.push_str(&format!("(assert {})\n", f));
    }
    input.push_str("(check-sat)\n");

    let solver = Solver::new();
    solver.from_string(input.as_bytes());
    let sat = solver.check();
    if sat != SatResult::Sat {
        return None;
    }
    let model = solver.get_model()?;
    let mut out = HashMap::new();
    for m in members {
        match symbol_sort(m, sorts) {
            SortKind::Int => {
                let sym = ZInt::new_const(m.as_str());
                if let Some(val) = model.get_const_interp(&sym) {
                    out.insert(m.clone(), Dynamic::from_ast(&val));
                }
            }
            SortKind::Bool => {
                let sym = Bool::new_const(m.as_str());
                if let Some(val) = model.get_const_interp(&sym) {
                    out.insert(m.clone(), Dynamic::from_ast(&val));
                }
            }
            _ => {}
        }
    }
    Some(out)
}
