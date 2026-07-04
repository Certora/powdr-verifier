use std::collections::{HashMap, HashSet};

use smt2::ast_util::{bound_var_index, free_symbol_ids_bool, symbol_id_dyn, symbol_name_for_id, SymbolId};
use smt2::{and_parts, iter_nodes_dyn};
use z3::ast::{Bool, Dynamic, Int as ZInt};
use z3::{SatResult, Solver};

use super::map::SkolemMap;
use super::ast_build::{field_mod, symbol_sort};
use super::types::SortKind;

pub fn contribute(
    map: &mut SkolemMap,
    body: &Bool,
    sorts: &HashMap<String, SortKind>,
    decl_block: &str,
    bound_order: &[SymbolId],
) {
    let unpinned: Vec<SymbolId> = map
        .qvars
        .iter()
        .copied()
        .filter(|q| {
            !map.is_pinned(*q)
                && symbol_name_for_id(*q)
                    .map(|n| symbol_sort(&n, sorts))
                    .is_some_and(|s| matches!(s, SortKind::Int | SortKind::Bool))
        })
        .collect();
    let Some(items) = smt2::or_body_parts(body) else {
        return;
    };

    let cand: HashSet<SymbolId> = unpinned.into_iter().collect();
    if cand.is_empty() {
        return;
    }

    let mut parent: HashMap<SymbolId, SymbolId> =
        cand.iter().map(|q| (*q, *q)).collect();

    fn find(parent: &mut HashMap<SymbolId, SymbolId>, x: SymbolId) -> SymbolId {
        let parent_x = parent.get(&x).copied().unwrap_or(x);
        if parent_x != x {
            let root = find(parent, parent_x);
            parent.insert(x, root);
            root
        } else {
            x
        }
    }

    fn union(parent: &mut HashMap<SymbolId, SymbolId>, a: SymbolId, b: SymbolId) {
        let ra = find(parent, a);
        let rb = find(parent, b);
        if ra != rb {
            parent.insert(ra, rb);
        }
    }

    let mut tainted: HashSet<SymbolId> = HashSet::new();
    let mut disj_cands: Vec<(Vec<SymbolId>, Bool)> = Vec::new();

    for d in items {
        let mentioned = qvars_mentioned_in(&d, &cand, bound_order);
        let cset: Vec<SymbolId> = mentioned.into_iter().collect();
        if cset.is_empty() {
            continue;
        }
        let rel_parts = qvar_conjuncts(&d, &cand, bound_order);
        let rel_fv: HashSet<SymbolId> = rel_parts
            .iter()
            .flat_map(|c| free_symbol_ids_bool(c))
            .collect();
        let relevant = if rel_parts.len() == 1 {
            rel_parts[0].clone()
        } else {
            Bool::and(&rel_parts.iter().collect::<Vec<_>>())
        };
        disj_cands.push((cset.clone(), relevant));
        for other in &cset[1..] {
            union(&mut parent, cset[0], *other);
        }
        if !rel_fv.is_subset(&cand) {
            tainted.extend(cset);
        }
    }

    if disj_cands.is_empty() {
        return;
    }

    let field = field_mod();
    let mut members_by_root: HashMap<SymbolId, HashSet<SymbolId>> = HashMap::new();
    let mut disjuncts_by_root: HashMap<SymbolId, Vec<Bool>> = HashMap::new();
    for q in &cand {
        let root = find(&mut parent, *q);
        members_by_root.entry(root).or_default().insert(*q);
    }
    for (cset, d) in disj_cands {
        let root = find(&mut parent, cset[0]);
        disjuncts_by_root.entry(root).or_default().push(d);
    }
    let tainted_roots: HashSet<SymbolId> = tainted.iter().map(|q| find(&mut parent, *q)).collect();

    for (root, disjuncts) in disjuncts_by_root {
        if tainted_roots.contains(&root) {
            continue;
        }
        let Some(members) = members_by_root.get(&root) else {
            continue;
        };
        let falsify: Vec<Bool> = disjuncts.iter().map(|d| d.not()).collect();
        let Some(model) = solve_island(&falsify, members, sorts, decl_block, field) else {
            continue;
        };
        for q in members {
            let Some(val) = model.get(q).cloned() else {
                continue;
            };
            map.pin(*q, val, "isolate");
        }
    }
}

fn qvars_mentioned_in(
    d: &Bool,
    cand: &HashSet<SymbolId>,
    bound_order: &[SymbolId],
) -> HashSet<SymbolId> {
    let mut out = HashSet::new();
    for node in iter_nodes_dyn(&Dynamic::from_ast(d)) {
        if let Some(id) = symbol_id_dyn(&node) {
            if cand.contains(&id) {
                out.insert(id);
            }
        } else if let Some(idx) = bound_var_index(&node) {
            if let Some(id) = bound_order.get(idx) {
                if cand.contains(id) {
                    out.insert(*id);
                }
            }
        }
    }
    out
}

fn qvar_conjuncts(
    d: &Bool,
    cand: &HashSet<SymbolId>,
    bound_order: &[SymbolId],
) -> Vec<Bool> {
    let conjs = and_parts(d).unwrap_or_else(|| vec![d.clone()]);
    conjs
        .into_iter()
        .filter(|c| !qvars_mentioned_in(c, cand, bound_order).is_empty())
        .collect()
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
    members: &HashSet<SymbolId>,
    sorts: &HashMap<String, SortKind>,
    decl_block: &str,
    field: Option<i128>,
) -> Option<HashMap<SymbolId, Dynamic>> {
    let mut input = decl_block.to_string();
    for m in members {
        let Some(name) = symbol_name_for_id(*m) else {
            continue;
        };
        let sort = symbol_sort(&name, sorts);
        input.push_str(&format!(
            "(declare-fun {name} () {})\n",
            sort_kind_to_smt(sort)
        ));
        if let Some(p) = field {
            if sort == SortKind::Int {
                input.push_str(&format!("(assert (and (<= 0 {name}) (< {name} {p})))\n"));
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
        let Some(name) = symbol_name_for_id(*m) else {
            continue;
        };
        match symbol_sort(&name, sorts) {
            SortKind::Int => {
                let sym = ZInt::new_const(name.as_str());
                if let Some(val) = model.get_const_interp(&sym) {
                    out.insert(*m, Dynamic::from_ast(&val));
                }
            }
            SortKind::Bool => {
                let sym = Bool::new_const(name.as_str());
                if let Some(val) = model.get_const_interp(&sym) {
                    out.insert(*m, Dynamic::from_ast(&val));
                }
            }
            _ => {}
        }
    }
    Some(out)
}
