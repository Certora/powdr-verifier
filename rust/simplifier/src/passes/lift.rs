//! Hoist ``Not(= q expr)`` skolem disjuncts from ``forall`` bodies to top-level asserts.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use smt2::ast_util::{
    ast_hash_bool, bound_var_index, decl_name, flatten_or, is_forall, or_body_parts,
    quantifier_body_bool, quantifier_body_deps, quantifier_bound_names, quantifier_bound_symbol_ids,
    quantifier_bounds_de_bruijn, rebuild_forall_dyn, substitute_bound_vars_dyn,
    contains_bound_var_dyn, de_bruijn_bound_symbol_id,
    free_symbol_ids_bool, symbol_id_dyn, symbol_id_from_name, symbol_name_for_id, SymbolId,
};
use smt2::ast_build::{iter_nodes_dyn, symbol_name_dyn};
use smt2::{declare_fun_name_cmd, map_bool_children, parse_single_command, Script, SExpr, SmtCommand};
use z3::ast::{Ast, AstKind, Bool, Dynamic, Int};

use crate::expr_util::AssertBuildCtx;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum DeclSort {
    Int,
    Bool,
    Array,
}

fn sort_kind_to_smt(sort: DeclSort) -> &'static str {
    match sort {
        DeclSort::Bool => "Bool",
        DeclSort::Array => "(Array Int Int)",
        DeclSort::Int => "Int",
    }
}

/// Classify a declared sort by inspecting the s-expression, not its rendered
/// text: ``Bool`` / ``(Array …)`` / everything else as ``Int``.
fn sort_from_sexpr(sort: &SExpr) -> DeclSort {
    match sort {
        SExpr::Atom(a) if a == "Bool" => DeclSort::Bool,
        SExpr::List(_) if sort.head() == Some("Array") => DeclSort::Array,
        _ => DeclSort::Int,
    }
}

/// Sort of a ``(declare-fun name () Sort)`` command from its s-expression args
/// (``[name, params, sort]``); defaults to ``Int`` if the shape is unexpected.
fn declare_fun_sort(cmd: &SmtCommand) -> DeclSort {
    cmd.spanned_form()
        .and_then(|form| form.node.args())
        .and_then(|args| args.get(2))
        .map(|sort| sort_from_sexpr(&sort.node))
        .unwrap_or(DeclSort::Int)
}

fn collect_symbol_sorts(script: &Script) -> HashMap<SymbolId, DeclSort> {
    let mut out = HashMap::new();
    for cmd in &script.commands {
        if let Some(name) = declare_fun_name_cmd(cmd) {
            out.insert(symbol_id_from_name(&name), declare_fun_sort(cmd));
        }
    }
    out
}

fn dyn_sort(ast: &Dynamic) -> DeclSort {
    match ast.get_sort().kind() {
        z3::SortKind::Bool => DeclSort::Bool,
        z3::SortKind::Array => DeclSort::Array,
        _ => DeclSort::Int,
    }
}

fn symbol_sort_in_eq(id: SymbolId, eq: &Bool) -> Option<DeclSort> {
    let ast = Dynamic::from_ast(eq);
    for node in iter_nodes_dyn(&ast) {
        if symbol_id_dyn(&node) == Some(id) {
            return Some(dyn_sort(&node));
        }
    }
    None
}

fn infer_symbol_sort(
    id: SymbolId,
    sorts: &HashMap<SymbolId, DeclSort>,
    eq_hint: Option<&Bool>,
) -> DeclSort {
    if let Some(sort) = sorts.get(&id) {
        return *sort;
    }
    if let Some(eq) = eq_hint {
        if let Some(sort) = symbol_sort_in_eq(id, eq) {
            return sort;
        }
    }
    DeclSort::Int
}

struct LiftWalker {
    lifted: BTreeMap<SymbolId, Bool>,
    sorts: HashMap<SymbolId, DeclSort>,
    unused_qvars_dropped: usize,
}

impl LiftWalker {
    fn new(sorts: HashMap<SymbolId, DeclSort>) -> Self {
        Self {
            lifted: BTreeMap::new(),
            sorts,
            unused_qvars_dropped: 0,
        }
    }

    fn record_bound_sort(&mut self, id: SymbolId, sort: DeclSort) {
        self.sorts.entry(id).or_insert(sort);
    }

    fn walk_bool(&mut self, b: &Bool) -> Bool {
        let ast = Dynamic::from_ast(b);
        if ast.kind() == AstKind::Quantifier {
            if is_forall(&ast) {
                return self.process_forall(b);
            }
            return b.clone();
        }
        map_bool_children(b, &mut |child| self.walk_bool(child))
    }

    fn process_forall(&mut self, b: &Bool) -> Bool {
        let ast = Dynamic::from_ast(b);
        let all_bounds = quantifier_bounds_de_bruijn(&ast);
        let bound_order: Vec<SymbolId> = quantifier_bound_symbol_ids(&ast);
        for de_bruijn_idx in 0..all_bounds.len() {
            let bound = &all_bounds[de_bruijn_idx];
            if let Some(id) = de_bruijn_bound_symbol_id(&bound_order, de_bruijn_idx) {
                let sort = if bound.as_bool().is_some() {
                    DeclSort::Bool
                } else if bound.as_int().is_some() {
                    DeclSort::Int
                } else {
                    DeclSort::Array
                };
                self.record_bound_sort(id, sort);
            }
        }

        let n_bounds = bound_order.len();
        let mut qvar_live = vec![true; n_bounds];
        let body = match quantifier_body_bool(&ast) {
            Some(body) => body,
            None => return b.clone(),
        };
        let Some(disjuncts) = or_body_parts(&body) else {
            return b.clone();
        };

        // Single-pass dependency-driven lift. Bound variables are identified by
        // their de Bruijn index (``0..n_bounds``) rather than by name: a qvar
        // reference in a body is a ``Var`` node, so liveness, per-side targets and
        // dependencies are all tracked as indices and a name is materialized only
        // at the moment of hoisting. Each candidate is (re)examined via ``rev``
        // when a qvar it references lifts, so it is touched O(degree) times. The
        // lift order is incidental; we only require determinism and prefer smaller
        // expressions, so the ready set is keyed by ``(expr_size, hash, cand_idx)``.
        let mut cands: Vec<LiftCand> = Vec::new();
        for d in &disjuncts {
            let Some(eq) = is_not_eq(d) else { continue };
            let eq_ast = Dynamic::from_ast(&eq);
            let (Some(lhs), Some(rhs)) = (eq_ast.nth_child(0), eq_ast.nth_child(1)) else {
                continue;
            };
            let (l_idx, l_resolvable) = side_qvar(&lhs, n_bounds);
            let (r_idx, r_resolvable) = side_qvar(&rhs, n_bounds);
            let deps_rhs = body_bound_refs(&rhs, n_bounds);
            let deps_lhs = body_bound_refs(&lhs, n_bounds);
            // Size of the side most likely hoisted (the non-target side); a soft
            // "prefer smaller" preference only, never affecting correctness.
            let expr_size = if l_resolvable {
                iter_nodes_dyn(&rhs).len()
            } else {
                iter_nodes_dyn(&lhs).len()
            };
            cands.push(LiftCand {
                d: d.clone(),
                hash: ast_hash_bool(d),
                expr_size,
                l_idx,
                r_idx,
                l_resolvable,
                r_resolvable,
                lhs_expr: lhs,
                rhs_expr: rhs,
                deps_rhs,
                deps_lhs,
            });
        }

        // ``unlifted_*[i] == |deps ∩ live qvars|``; decremented as deps lift.
        let mut unlifted_rhs: Vec<usize> = cands.iter().map(|c| c.deps_rhs.len()).collect();
        let mut unlifted_lhs: Vec<usize> = cands.iter().map(|c| c.deps_lhs.len()).collect();
        // ``rev[q]`` lists candidates to re-check when bound var ``q`` lifts.
        let mut rev: Vec<Vec<usize>> = vec![Vec::new(); n_bounds];
        for (i, c) in cands.iter().enumerate() {
            for &q in c
                .deps_rhs
                .iter()
                .chain(c.deps_lhs.iter())
                .chain(c.l_idx.iter())
                .chain(c.r_idx.iter())
            {
                rev[q].push(i);
            }
        }
        for js in rev.iter_mut() {
            js.sort_unstable();
            js.dedup();
        }

        // Ready set ordered by ``(expr_size, hash, cand_idx)``: prefer hoisting
        // smaller expressions, with ``hash``/``cand_idx`` giving a deterministic
        // total order.
        let mut ready: BTreeSet<(usize, u64, usize)> = cands
            .iter()
            .enumerate()
            .map(|(i, c)| (c.expr_size, c.hash, i))
            .collect();
        let mut resolved = vec![false; cands.len()];
        let mut lifted_flags = vec![false; cands.len()];

        while let Some((_, _, ci)) = ready.pop_first() {
            if resolved[ci] {
                continue;
            }
            let Some((q_idx, expr)) =
                try_lift_cand(&cands[ci], &qvar_live, unlifted_rhs[ci], unlifted_lhs[ci])
            else {
                // Blocked for now; re-added via ``rev`` when a referenced qvar lifts.
                continue;
            };
            resolved[ci] = true;
            let Some(id) = de_bruijn_bound_symbol_id(&bound_order, q_idx) else {
                continue;
            };
            if self.lifted.contains_key(&id) {
                continue;
            }
            let Ok(named_expr) = name_debruijn_dyn_with(&expr, &all_bounds) else {
                continue;
            };
            let Some(name) = symbol_name_for_id(id) else {
                continue;
            };
            let sort = self.sorts.get(&id).copied().unwrap_or(DeclSort::Int);
            let hoisted = match sort {
                DeclSort::Bool => match named_expr.as_bool() {
                    Some(rhs) => Bool::new_const(name.as_str()).eq(&rhs),
                    None => continue,
                },
                _ => match named_expr.as_int() {
                    Some(rhs) => Int::new_const(name.as_str()).eq(&rhs),
                    None => continue,
                },
            };
            self.lifted.insert(id, hoisted);
            qvar_live[q_idx] = false;
            lifted_flags[ci] = true;
            // Lifting ``q_idx`` removes it from the live qvars: refresh dependents'
            // counters and requeue them for another readiness check.
            for &j in &rev[q_idx] {
                if resolved[j] {
                    continue;
                }
                if cands[j].deps_rhs.contains(&q_idx) {
                    unlifted_rhs[j] -= 1;
                }
                if cands[j].deps_lhs.contains(&q_idx) {
                    unlifted_lhs[j] -= 1;
                }
                ready.insert((cands[j].expr_size, cands[j].hash, j));
            }
        }

        let lifted_disjuncts: Vec<Bool> = cands
            .iter()
            .zip(&lifted_flags)
            .filter(|(_, &lifted)| lifted)
            .map(|(c, _)| c.d.clone())
            .collect();

        if lifted_disjuncts.is_empty() {
            return b.clone();
        }

        // Hash-bucket the lifted disjuncts so dropping them from the body is
        // ``O(disjuncts)`` instead of ``O(disjuncts * lifted)`` ``ast_eq`` calls.
        let mut lifted_by_hash: HashMap<u64, Vec<Bool>> = HashMap::new();
        for lifted in &lifted_disjuncts {
            lifted_by_hash
                .entry(ast_hash_bool(lifted))
                .or_default()
                .push(lifted.clone());
        }
        let remaining: Vec<Bool> = disjuncts
            .iter()
            .filter(|d| match lifted_by_hash.get(&ast_hash_bool(d)) {
                Some(bucket) => !bucket.iter().any(|lifted| d.ast_eq(lifted)),
                None => true,
            })
            .cloned()
            .collect();
        let body_out = if remaining.is_empty() {
            Bool::from_bool(false)
        } else {
            flatten_or(remaining)
        };
        let named_body = match name_debruijn_dyn_with(&Dynamic::from_ast(&body_out), &all_bounds)
            .ok()
            .and_then(|d| d.as_bool())
        {
            Some(b) => b,
            None => return b.clone(),
        };

        // After de Bruijn naming the still-live qvars are free named symbols in
        // ``named_body``. Iterate ``bound_order`` (declaration order) so the
        // rebuilt quantifier keeps that order; map position to de Bruijn index.
        let body_fv = free_symbol_ids_bool(&named_body);
        let mut qvars_remaining: Vec<Dynamic> = Vec::new();
        for (pos, id) in bound_order.iter().enumerate() {
            let q_idx = n_bounds - 1 - pos;
            if !qvar_live[q_idx] {
                continue;
            }
            if !body_fv.contains(id) {
                self.unused_qvars_dropped += 1;
                continue;
            }
            let Some(name) = symbol_name_for_id(*id) else {
                continue;
            };
            let sort = self.sorts.get(id).copied().unwrap_or(DeclSort::Int);
            qvars_remaining.push(match sort {
                DeclSort::Bool => Dynamic::from_ast(&Bool::new_const(name.as_str())),
                _ => Dynamic::from_ast(&Int::new_const(name.as_str())),
            });
        }

        if qvars_remaining.is_empty() {
            self.walk_bool(&named_body)
        } else {
            let rebuilt = rebuild_forall_dyn(&qvars_remaining, &named_body);
            self.walk_bool(&rebuilt)
        }
    }
}

pub fn apply(script: &Script) -> Result<(Script, serde_json::Value), String> {
    let sorts = collect_symbol_sorts(script);
    let mut walker = LiftWalker::new(sorts);

    let mut prefix = Vec::new();
    let mut suffix = Vec::new();
    let mut in_prefix = true;
    let mut declared: HashSet<SymbolId> = script
        .commands
        .iter()
        .filter_map(declare_fun_name_cmd)
        .map(|n| symbol_id_from_name(&n))
        .collect();

    for cmd in &script.commands {
        if let Some(name) = declare_fun_name_cmd(cmd) {
            declared.insert(symbol_id_from_name(&name));
        }
        if cmd.assert_bool().is_some() {
            in_prefix = false;
        }
        if in_prefix {
            prefix.push(cmd.clone());
        } else if let Some(b) = cmd.assert_bool() {
            let new_b = walker.walk_bool(b);
            suffix.push(SmtCommand::new_assert(new_b));
        } else {
            suffix.push(cmd.clone());
        }
    }

    let mut hoisted_decls = 0usize;
    let mut hoisted_asserts = 0usize;
    let mut insert = Vec::new();
    if !walker.lifted.is_empty() {
        let mut ctx = AssertBuildCtx::from_script(script)?;
        let mut to_declare: BTreeMap<SymbolId, DeclSort> = BTreeMap::new();
        for (id, eq) in &walker.lifted {
            if let Some(sort) = walker.sorts.get(id) {
                to_declare.entry(*id).or_insert(*sort);
            }
            for sym in free_symbol_ids_bool(eq) {
                if !declared.contains(&sym) {
                    let sort = infer_symbol_sort(sym, &walker.sorts, Some(eq));
                    to_declare.entry(sym).or_insert(sort);
                }
            }
        }
        for (id, sort) in to_declare {
            if declared.contains(&id) {
                continue;
            }
            let Some(name) = symbol_name_for_id(id) else {
                continue;
            };
            let raw = format!("(declare-fun {name} () {})", sort_kind_to_smt(sort));
            let cmd = parse_single_command(&raw, ctx.parse())?;
            insert.push(cmd);
            declared.insert(id);
            hoisted_decls += 1;
        }
        for eq in walker.lifted.values() {
            ctx.push_assert(&mut insert, eq)?;
            hoisted_asserts += 1;
        }
    }

    let mut commands = prefix;
    commands.extend(insert);
    commands.extend(suffix);

    let stats = serde_json::json!({
        "pins_lifted": walker.lifted.len(),
        "new_declarations": hoisted_decls,
        "hoisted_pin_asserts": hoisted_asserts,
        "candidates_seen": walker.lifted.len(),
        "unused_qvars_dropped": walker.unused_qvars_dropped,
    });
    Ok((Script::from_commands(&script.source, commands), stats))
}

fn name_debruijn_dyn(d: &Dynamic, quant: &Dynamic) -> Result<Dynamic, String> {
    if !contains_bound_var_dyn(d) {
        return Ok(d.clone());
    }
    let replacements = quantifier_bounds_de_bruijn(quant);
    name_debruijn_dyn_with(d, &replacements)
}

/// De Bruijn naming with a precomputed replacement vector. Callers naming many
/// terms against the same quantifier should compute the vector once (it is
/// ``O(bound vars)``) rather than per term via [`name_debruijn_dyn`].
fn name_debruijn_dyn_with(d: &Dynamic, replacements: &[Dynamic]) -> Result<Dynamic, String> {
    if !contains_bound_var_dyn(d) {
        return Ok(d.clone());
    }
    let out = substitute_bound_vars_dyn(d, replacements);
    if contains_bound_var_dyn(&out) {
        return Err("substitute_bound_vars_dyn left bound variables".into());
    }
    Ok(out)
}

pub(crate) fn name_debruijn_bool(b: &Bool, quant: &Dynamic) -> Result<Bool, String> {
    name_debruijn_dyn(&Dynamic::from_ast(b), quant)?
        .as_bool()
        .ok_or_else(|| "expected bool after de Bruijn naming".into())
}

/// Precomputed lift metadata for one `(not (= lhs rhs))` disjunct. Bound vars are
/// referred to by de Bruijn index; ``*_resolvable`` records whether a side is a
/// bound var or named symbol (i.e. a possible lift target at all).
struct LiftCand {
    d: Bool,
    hash: u64,
    expr_size: usize,
    l_idx: Option<usize>,
    r_idx: Option<usize>,
    l_resolvable: bool,
    r_resolvable: bool,
    lhs_expr: Dynamic,
    rhs_expr: Dynamic,
    deps_rhs: Vec<usize>,
    deps_lhs: Vec<usize>,
}

/// Readiness check mirroring [`match_lift_pair`] with precomputed indices and
/// remaining-dependency counters (``unlifted_rhs``/``unlifted_lhs`` track
/// ``|deps ∩ live qvars|``). Returns the de Bruijn index to lift and the opposite
/// side to hoist. Prefers the lhs side, falling back to rhs; an unresolvable side
/// short-circuits to ``None``, matching the original ``?`` behavior.
fn try_lift_cand(
    c: &LiftCand,
    qvar_live: &[bool],
    unlifted_rhs: usize,
    unlifted_lhs: usize,
) -> Option<(usize, Dynamic)> {
    if !c.l_resolvable {
        return None;
    }
    if let Some(i) = c.l_idx {
        if qvar_live[i] && unlifted_rhs == 0 {
            return Some((i, c.rhs_expr.clone()));
        }
    }
    if !c.r_resolvable {
        return None;
    }
    if let Some(i) = c.r_idx {
        if qvar_live[i] && unlifted_lhs == 0 {
            return Some((i, c.lhs_expr.clone()));
        }
    }
    None
}

/// Classify one equality side: ``(our-bound de Bruijn index, resolvable)``.
/// ``resolvable`` mirrors ``resolve_bound_or_free_name(..).is_some()`` (a bound
/// var of any depth or a named symbol); the index is ``Some`` only when the side
/// is one of this quantifier's ``n_bounds`` variables.
fn side_qvar(side: &Dynamic, n_bounds: usize) -> (Option<usize>, bool) {
    if let Some(i) = bound_var_index(side) {
        let ours = i < n_bounds;
        return (ours.then_some(i), ours);
    }
    (None, symbol_name_dyn(side).is_some())
}

/// Sorted, deduplicated de Bruijn indices of this quantifier's bound vars that
/// occur free in ``expr`` (nested quantifiers are opaque, as in
/// ``quantifier_body_deps``).
fn body_bound_refs(expr: &Dynamic, n_bounds: usize) -> Vec<usize> {
    let mut out = Vec::new();
    let mut stack = vec![expr.clone()];
    while let Some(node) = stack.pop() {
        if node.kind() == AstKind::Quantifier {
            continue;
        }
        if let Some(idx) = bound_var_index(&node) {
            if idx < n_bounds {
                out.push(idx);
            }
            continue;
        }
        for ch in node.children() {
            stack.push(ch);
        }
    }
    out.sort_unstable();
    out.dedup();
    out
}

fn is_not_eq(d: &Bool) -> Option<Bool> {
    let ast = Dynamic::from_ast(d);
    if ast.kind() != AstKind::App || decl_name(&ast.decl()) != "not" || ast.num_children() != 1 {
        return None;
    }
    let inner = ast.nth_child(0)?;
    if inner.kind() != AstKind::App || decl_name(&inner.decl()) != "=" || inner.num_children() != 2 {
        return None;
    }
    inner.as_bool()
}

/// Reference implementation of the per-disjunct lift check, retained for tests;
/// the hot path uses [`try_lift_cand`] with precomputed dependency counters.
#[allow(dead_code)]
fn match_lift_pair(
    d: &Bool,
    bound_order: &[String],
    qvars: &HashSet<String>,
) -> Option<(String, Dynamic)> {
    let eq = is_not_eq(d)?;
    let ast = Dynamic::from_ast(&eq);
    let lhs = ast.nth_child(0)?;
    let rhs = ast.nth_child(1)?;
    for (vside, expr) in [(lhs.clone(), rhs.clone()), (rhs, lhs)] {
        let name = resolve_bound_or_free_name(&vside, bound_order)?;
        if !qvars.contains(&name) {
            continue;
        }
        if bound_var_index(&vside).is_none() && smt2::symbol_name_dyn(&vside).is_none() {
            continue;
        }
        let deps = quantifier_body_deps(&expr, bound_order, qvars);
        if deps.is_empty() {
            return Some((name, expr));
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    fn script_assert(raw: &str) -> Script {
        Script::parse(&format!("(assert {raw})\n(check-sat)\n")).unwrap()
    }

    fn top_asserts(script: &Script) -> Vec<String> {
        script
            .commands
            .iter()
            .filter_map(|c| c.assert_bool().map(|b| b.to_string()))
            .collect()
    }

    #[test]
    fn debug_forall_body() {
        let script = script_assert("(forall ((x Int)) (or (not (= x 7)) (< x 0)))");
        let b = script.commands[0].assert_bool().unwrap();
        let ast = Dynamic::from_ast(b);
        let bound_order = quantifier_bound_names(&ast);
        let body = quantifier_body_bool(&ast).unwrap();
        let disjuncts = or_body_parts(&body).unwrap();
        let qvars: HashSet<String> = bound_order.iter().cloned().collect();
        assert!(match_lift_pair(&disjuncts[0], &bound_order, &qvars).is_some());
    }

    #[test]
    fn lift_mod_pin_repro() {
        let raw = r#"(declare-fun before-a__3_1@58 () Int)
(assert (forall ((before-writes_aux__prev_data__3_5@199 Int))
  (or (not (= before-writes_aux__prev_data__3_5@199 (mod before-a__3_1@58 2013265921)))
      false)))
(check-sat)
"#;
        let script = Script::parse(raw).unwrap();
        let (out, stats) = apply(&script).unwrap();
        assert_eq!(stats["pins_lifted"], 1);
        let asserts = top_asserts(&out);
        assert!(
            asserts.iter().any(|a| a.contains("before-a__3_1@58")),
            "pins: {:?}",
            asserts
        );
        assert!(!asserts.iter().any(|a| a.contains("(mod 0")));
    }

    #[test]
    fn lift_ordered_dependencies() {
        let script = Script::parse(
            "(assert (forall ((x Int) (y Int)) (or (not (= y 5)) (not (= x (mod y 10))))))\n(check-sat)\n",
        )
        .unwrap();
        let (out, stats) = apply(&script).unwrap();
        assert_eq!(stats["pins_lifted"], 2);
        let asserts = top_asserts(&out);
        assert!(asserts.iter().any(|a| a == "(= y 5)"), "{asserts:?}");
        assert!(asserts.iter().any(|a| a == "(= x (mod y 10))"), "{asserts:?}");
    }

    #[test]
    fn lift_single_var() {
        let script = script_assert("(forall ((x Int)) (or (not (= x 7)) (< x 0)))");
        let (out, stats) = apply(&script).unwrap();
        assert_eq!(stats["pins_lifted"], 1);
        let asserts = top_asserts(&out);
        assert!(asserts.iter().any(|a| a == "(= x 7)"));
        assert!(asserts.iter().any(|a| a == "(< x 0)"));
        assert!(!asserts.iter().any(|a| a.contains("forall")));
    }

    #[test]
    fn drops_unused_qvar_after_lift() {
        let script = script_assert(
            "(forall ((x Int) (y Int)) (or (not (= x 7)) (< x 0)))",
        );
        let (out, stats) = apply(&script).unwrap();
        assert_eq!(stats["pins_lifted"], 1);
        assert_eq!(stats["unused_qvars_dropped"], 1);
        let asserts = top_asserts(&out);
        assert!(!asserts.iter().any(|a| a.contains("forall")), "{asserts:?}");
    }

    #[test]
    fn skips_when_expr_mentions_other_qvar() {
        let script = script_assert("(forall ((x Int) (y Int)) (or (not (= x y)) (< x 0)))");
        let (out, stats) = apply(&script).unwrap();
        assert_eq!(stats["pins_lifted"], 0);
        assert_eq!(out.commands.len(), script.commands.len());
    }
}
