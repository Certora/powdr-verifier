use std::collections::{HashMap, HashSet};

use smt2::Term;
use z3::ast::{Bool, Int as ZInt};
use z3::{SatResult, Solver};

use super::map::SkolemMap;
use super::term_util::{atom, field_mod, free_variables, list, symbol_sort};
use super::types::SortKind;

pub fn contribute(
    map: &mut SkolemMap,
    body: &Term,
    sorts: &HashMap<String, SortKind>,
    decl_block: &str,
) {
    let Term::List(items) = body else {
        return;
    };
    if !matches!(items.first(), Some(Term::Atom(s)) if s == "or") {
        return;
    }

    let cand: HashSet<String> = map
        .qvars
        .iter()
        .filter(|q| {
            !map.is_pinned(q)
                && matches!(symbol_sort(q, sorts), SortKind::Int | SortKind::Bool)
        })
        .cloned()
        .collect();
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
    let mut disj_cands: Vec<(Vec<String>, Term)> = Vec::new();

    for d in &items[1..] {
        let cset: Vec<String> = cand
            .iter()
            .filter(|q| free_variables(d).contains(*q))
            .cloned()
            .collect();
        if cset.is_empty() {
            continue;
        }
        let rel_parts = qvar_conjuncts(d, &cand);
        let rel_fv: HashSet<String> = rel_parts.iter().flat_map(free_variables).collect();
        let relevant = if rel_parts.len() == 1 {
            rel_parts[0].clone()
        } else {
            list("and", rel_parts)
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
    let mut disjuncts_by_root: HashMap<String, Vec<Term>> = HashMap::new();
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
        let falsify: Vec<Term> = disjuncts.iter().map(|d| list("not", vec![d.clone()])).collect();
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

fn qvar_conjuncts(d: &Term, cand: &HashSet<String>) -> Vec<Term> {
    let conjs = if let Term::List(items) = d {
        if matches!(items.first(), Some(Term::Atom(s)) if s == "and") {
            items[1..].to_vec()
        } else {
            vec![d.clone()]
        }
    } else {
        vec![d.clone()]
    };
    conjs
        .into_iter()
        .filter(|c| !free_variables(c).is_disjoint(cand))
        .collect()
}

fn default_value(q: &str, sorts: &HashMap<String, SortKind>) -> Term {
    match symbol_sort(q, sorts) {
        SortKind::Bool => atom("false"),
        _ => atom("0"),
    }
}

fn solve_island(
    falsify: &[Term],
    members: &HashSet<String>,
    sorts: &HashMap<String, SortKind>,
    decl_block: &str,
    field: Option<i128>,
) -> Option<HashMap<String, Term>> {
    let mut input = decl_block.to_string();
    if let Some(p) = field {
        for m in members {
            if symbol_sort(m, sorts) == SortKind::Int {
                input.push_str(&format!("(assert (and (<= 0 {m}) (< {m} {p})))\n"));
            }
        }
    }
    for f in falsify {
        input.push_str(&format!("(assert {})\n", f.to_string()));
    }
    input.push_str("(check-sat)\n");

    let solver = Solver::new();
    solver.from_string(input.as_bytes());
    if solver.check() != SatResult::Sat {
        return None;
    }
    let model = solver.get_model()?;
    let mut out = HashMap::new();
    for m in members {
        match symbol_sort(m, sorts) {
            SortKind::Int => {
                let sym = ZInt::new_const(m.as_str());
                if let Some(val) = model.get_const_interp(&sym) {
                    out.insert(m.clone(), ast_to_term(&val.to_string(), Some(SortKind::Int)));
                }
            }
            SortKind::Bool => {
                let sym = Bool::new_const(m.as_str());
                if let Some(val) = model.get_const_interp(&sym) {
                    out.insert(m.clone(), ast_to_term(&val.to_string(), Some(SortKind::Bool)));
                }
            }
            _ => {}
        }
    }
    Some(out)
}

fn ast_to_term(s: &str, sort: Option<SortKind>) -> Term {
    if s == "true" || s == "false" {
        return atom(s);
    }
    if let Ok(t) = Term::parse(s) {
        return t;
    }
    match sort {
        Some(SortKind::Bool) => atom("false"),
        _ => atom("0"),
    }
}
