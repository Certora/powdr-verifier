//! SMT-backed strengthening for small finite integer domains (choice/or-eq).
//!
//! Probes run as one-shot `z3` subprocesses on the connected component of the
//! choice-only assertion slice, not as incremental `push`/`pop` on the linked
//! `z3::Solver`. Two hard-won reasons: (1) under an open push scope z3 weakens
//! its tactic (`solve-eqs` cannot eliminate variables) and returns `unknown` on
//! the nonlinear-mod selector goals a fresh one-shot solve discharges in well
//! under a second; (2) the linked z3 is older/weaker than the `z3-nightly`
//! binary the rest of the pipeline uses. See src/check/sliced.py for the same
//! lesson. Kept in sync with src/simplify/domain_probe.py.

use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

use smt2::ast_util::{ast_children, bool_decl_kind};
use smt2::{
    and_parts, decl_name, free_int_nodes, int_from_i128, int_value_dyn, is_int_const, is_not,
    or_parts, unwrap_zero_mod_eq, Script, SmtCommand,
};
use z3::ast::{Ast, AstKind, Bool, Dynamic, Int};
use z3::DeclKind;

use crate::expr_util::{rebuild_script, AssertBuildCtx};
use crate::passes::skolem::ast_build::field_mod;

const MAX_VALUES: usize = 3;
// Bound the whole pass so easy solver steps (nothing forced) never pay much: a
// per-probe soft timeout and a total wall-clock budget across all components.
// The useful pins on the hard blocks land in a few seconds each (incremental
// hints make later probes cheap); the wall budget caps the wasted work.
const PROBE_BUDGET_S: u32 = 8;
const TOTAL_WALL_S: f64 = 20.0;
const MAX_COMPONENT_VARS: usize = 40;
const MAX_COMPONENT_ASSERTS: usize = 400;

static PROBE_FILE_SEQ: AtomicU64 = AtomicU64::new(0);

pub fn apply(script: &Script) -> Result<(Script, serde_json::Value), String> {
    let assertions = collect_assert_terms(script);
    let mut stats = serde_json::json!({
        "base_asserts": assertions.len(),
    });

    if assertions.is_empty() {
        stats["choice_symbols"] = 0.into();
        stats["clusters_probed"] = 0.into();
        stats["added_facts"] = 0.into();
        return Ok((script.clone(), stats));
    }

    let choices = collect_choices(&assertions, MAX_VALUES);
    stats["choice_symbols"] = choices.len().into();
    if choices.is_empty() {
        stats["clusters_probed"] = 0.into();
        stats["added_facts"] = 0.into();
        return Ok((script.clone(), stats));
    }

    let prefix = declare_block(script);
    let pinned = const_pinned(&assertions);
    let mut components = selector_components(&assertions, &choices, &pinned);
    // Probe smaller components first: they resolve fast and their pins can feed
    // the field bound / opcode-decode context for the larger ones.
    components.sort_by_key(|c| c.len());

    let deadline = Instant::now() + Duration::from_secs_f64(TOTAL_WALL_S);
    let mut symbols_probed = 0usize;
    let mut clusters_probed = 0usize;
    let mut flag_vars_total = 0usize;
    let mut flag_local_total = 0usize;
    let mut batch: Vec<Bool> = Vec::new();
    let mut cluster_stats = Vec::new();

    for component in &components {
        if Instant::now() > deadline {
            break;
        }
        let component_choices: HashMap<Int, Vec<i128>> = component
            .iter()
            .filter_map(|s| choices.get(s).map(|v| (s.clone(), v.clone())))
            .collect();
        if component_choices.is_empty() {
            continue;
        }

        let rel = component_slice(&assertions, component, &pinned);
        if component.len() > MAX_COMPONENT_VARS || rel.len() > MAX_COMPONENT_ASSERTS {
            continue;
        }
        clusters_probed += 1;
        symbols_probed += component_choices.len();
        flag_vars_total += component.len();
        flag_local_total += rel.len();

        let outcomes = probe_component(&prefix, &rel, &component_choices, &mut batch, deadline);
        cluster_stats.push(serde_json::json!({
            "index": clusters_probed,
            "n_vars": component_choices.len(),
            "n_flag_vars": component.len(),
            "n_asserts": rel.len(),
            "probes_sat": outcomes.probes_sat,
            "probes_unsat": outcomes.probes_unsat,
            "probes_unknown": outcomes.probes_unknown,
            "pinned": outcomes.pinned,
        }));
    }

    stats["pairs_probed"] = symbols_probed.into();
    stats["clusters_probed"] = clusters_probed.into();
    stats["flag_vars"] = flag_vars_total.into();
    stats["flag_local_asserts"] = flag_local_total.into();
    stats["clusters"] = serde_json::Value::Array(cluster_stats);

    let added = batch.len();
    stats["added_facts"] = added.into();

    if batch.is_empty() {
        return Ok((script.clone(), stats));
    }

    let mut ctx = AssertBuildCtx::from_script(script)?;
    let mut commands: Vec<SmtCommand> = Vec::new();
    let mut inserted = false;
    for cmd in &script.commands {
        if !inserted && cmd.name() == "check-sat" {
            for fact in &batch {
                ctx.push_assert(&mut commands, fact)?;
            }
            inserted = true;
        }
        if let Some(b) = cmd.assert_bool() {
            ctx.push_assert(&mut commands, b)?;
        } else {
            commands.push(cmd.clone());
        }
    }
    if !inserted {
        for fact in &batch {
            ctx.push_assert(&mut commands, fact)?;
        }
    }

    Ok((rebuild_script(&script.source, commands), stats))
}

fn collect_assert_terms(script: &Script) -> Vec<Bool> {
    script
        .commands
        .iter()
        .filter_map(|c| c.assert_bool().cloned())
        .collect()
}

fn declare_block(script: &Script) -> String {
    let mut out = String::new();
    out.push_str("(set-logic ALL)\n");
    for cmd in &script.commands {
        if cmd.name() == "declare-fun" {
            out.push_str(&cmd.to_smtlib(&script.source));
            out.push('\n');
        }
    }
    out
}

// ---------------------------------------------------------------------------
// Choice detection
// ---------------------------------------------------------------------------

fn collect_choices(assertions: &[Bool], max_n: usize) -> HashMap<Int, Vec<i128>> {
    let mut raw: HashMap<Int, Vec<i128>> = HashMap::new();
    let add = |raw: &mut HashMap<Int, Vec<i128>>, sym: Int, vals: &[i128]| {
        let cur = raw.entry(sym).or_default();
        for &v in vals {
            if !cur.contains(&v) {
                cur.push(v);
            }
        }
        cur.sort();
    };
    for a in assertions {
        for (sym, _, vals) in choices_in_assertion(a) {
            add(&mut raw, sym, &vals);
        }
    }
    // Range/bound-derived small domains (selectors, booleans, ...): these have no
    // or-of-equalities form, only integer bounds, so they are invisible to the
    // parser above. A symbol seen both ways keeps the union of candidate values;
    // over-approximating the domain only adds probes and is sound either way.
    for (sym, vals) in bound_choices(assertions, max_n) {
        add(&mut raw, sym, &vals);
    }
    if let Some(field) = field_mod() {
        for (sym, vals) in poly_choices(assertions, max_n, field) {
            add(&mut raw, sym, &vals);
        }
    }
    raw.into_iter()
        .filter(|(_, vals)| vals.len() > 1 && vals.len() <= max_n)
        .collect()
}

fn choices_in_assertion(f: &Bool) -> Vec<(Int, Bool, Vec<i128>)> {
    if let Some((sym, vals)) = parse_or_equalities(f) {
        return vec![(sym, f.clone(), vals)];
    }
    let Some(and_terms) = and_parts(f) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for arg in and_terms {
        if let Some((sym, vals)) = parse_or_equalities(&arg) {
            out.push((sym, arg.clone(), vals));
        }
    }
    out
}

fn parse_or_equalities(f: &Bool) -> Option<(Int, Vec<i128>)> {
    let parts = or_parts(f)?;
    let mut sym: Option<Int> = None;
    let mut vals = Vec::new();
    for d in parts {
        let (s, v) = eq_symbol_int(&d)?;
        if let Some(existing) = &sym {
            if !existing.ast_eq(&s) {
                return None;
            }
        } else {
            sym = Some(s);
        }
        vals.push(v);
    }
    let sym = sym?;
    if vals.is_empty() {
        return None;
    }
    vals.sort();
    vals.dedup();
    Some((sym, vals))
}

fn eq_symbol_int(term: &Bool) -> Option<(Int, i128)> {
    let ast = Dynamic::from_ast(term);
    if ast.kind() != AstKind::App || ast.num_children() != 2 || ast.decl().kind() != DeclKind::Eq {
        return None;
    }
    let lhs = ast.nth_child(0)?;
    let rhs = ast.nth_child(1)?;
    if let Some(sym) = lhs.as_int() {
        if is_int_const(&lhs) {
            if let Some(v) = int_value_dyn(&rhs) {
                return Some((sym, v));
            }
        }
    }
    if let Some(sym) = rhs.as_int() {
        if is_int_const(&rhs) {
            if let Some(v) = int_value_dyn(&lhs) {
                return Some((sym, v));
            }
        }
    }
    None
}

fn int_sym(d: &Dynamic) -> Option<Int> {
    if is_int_const(d) {
        d.as_int()
    } else {
        None
    }
}

fn tighten(
    bounds: &mut HashMap<Int, (Option<i128>, Option<i128>)>,
    sym: &Int,
    lo: Option<i128>,
    hi: Option<i128>,
) {
    let entry = bounds.entry(sym.clone()).or_insert((None, None));
    if let Some(lo) = lo {
        entry.0 = Some(entry.0.map_or(lo, |c| c.max(lo)));
    }
    if let Some(hi) = hi {
        entry.1 = Some(entry.1.map_or(hi, |c| c.min(hi)));
    }
}

/// Apply the inequality `a <= b` (strict: `a < b`) to per-symbol integer bounds.
fn apply_ineq(
    a: &Dynamic,
    b: &Dynamic,
    strict: bool,
    bounds: &mut HashMap<Int, (Option<i128>, Option<i128>)>,
) {
    let ca = int_value_dyn(a);
    let cb = int_value_dyn(b);
    let sa = int_sym(a);
    let sb = int_sym(b);
    if let (Some(sa), Some(cb)) = (&sa, cb) {
        tighten(bounds, sa, None, Some(if strict { cb - 1 } else { cb }));
    }
    if let (Some(ca), Some(sb)) = (ca, &sb) {
        tighten(bounds, sb, Some(if strict { ca + 1 } else { ca }), None);
    }
}

/// Collect per-symbol integer bounds from `<=` / `<` / `>=` / `>` atoms.
///
/// Recurses through top-level `and` and `not`. `>=`/`>` are canonicalized to
/// swapped `<=`/`<`; negation swaps operands and flips strictness.
fn bounds_from_atom(
    f: &Bool,
    bounds: &mut HashMap<Int, (Option<i128>, Option<i128>)>,
    negated: bool,
) {
    if let Some(inner) = is_not(f) {
        bounds_from_atom(&inner, bounds, !negated);
        return;
    }
    if !negated {
        if let Some(parts) = and_parts(f) {
            for p in parts {
                bounds_from_atom(&p, bounds, false);
            }
            return;
        }
    }
    let Some(kind) = bool_decl_kind(f) else {
        return;
    };
    if f.num_children() != 2 {
        return;
    }
    let (Some(c0), Some(c1)) = (f.nth_child(0), f.nth_child(1)) else {
        return;
    };
    // Canonicalize to `a <= b` / `a < b`.
    let (a, b, strict) = match kind {
        DeclKind::Le => (c0, c1, false),
        DeclKind::Lt => (c0, c1, true),
        DeclKind::Ge => (c1, c0, false),
        DeclKind::Gt => (c1, c0, true),
        _ => return,
    };
    // not(a <= b) => b < a ; not(a < b) => b <= a.
    let (a, b, strict) = if negated { (b, a, !strict) } else { (a, b, strict) };
    apply_ineq(&a, &b, strict, bounds);
}

fn bound_choices(assertions: &[Bool], max_n: usize) -> HashMap<Int, Vec<i128>> {
    let mut bounds: HashMap<Int, (Option<i128>, Option<i128>)> = HashMap::new();
    for a in assertions {
        bounds_from_atom(a, &mut bounds, false);
    }
    let mut out = HashMap::new();
    for (sym, (lo, hi)) in bounds {
        let (Some(lo), Some(hi)) = (lo, hi) else {
            continue;
        };
        if lo > hi {
            continue;
        }
        let size = (hi - lo + 1) as usize;
        if size > 1 && size <= max_n {
            out.insert(sym, (lo..=hi).collect());
        }
    }
    out
}

/// Evaluate an integer polynomial `node` (in the single symbol `sym`) at `v`.
fn eval_univariate(node: &Dynamic, sym: &Int, v: i128) -> Option<i128> {
    if let Some(c) = int_value_dyn(node) {
        return Some(c);
    }
    if is_int_const(node) {
        let i = node.as_int()?;
        return if i.ast_eq(sym) { Some(v) } else { None };
    }
    let kind = node.decl().kind();
    let ch = ast_children(node);
    match kind {
        DeclKind::Add => {
            let mut total = 0i128;
            for c in &ch {
                total = total.checked_add(eval_univariate(c, sym, v)?)?;
            }
            Some(total)
        }
        DeclKind::Mul => {
            let mut prod = 1i128;
            for c in &ch {
                prod = prod.checked_mul(eval_univariate(c, sym, v)?)?;
            }
            Some(prod)
        }
        DeclKind::Sub if ch.len() == 2 => {
            Some(eval_univariate(&ch[0], sym, v)?.checked_sub(eval_univariate(&ch[1], sym, v)?)?)
        }
        DeclKind::Sub | DeclKind::Uminus if ch.len() == 1 => {
            Some(0i128.checked_sub(eval_univariate(&ch[0], sym, v)?)?)
        }
        _ => None,
    }
}

/// Small integer roots of a univariate `(= (mod POLY P) 0)` domain constraint.
///
/// Selector booleanity survives `normalize` as an expanded modular polynomial
/// (`x(x-1)(x-2) = 0 mod P` for a ternary flag), not a range. Root-finding over
/// `[0, max_n]` recovers the `{0, 1, 2}` domain. Only the candidate set matters
/// for soundness -- the forced-value pin is re-confirmed independently -- so a
/// missed large root just means no pin, never an unsound one.
fn poly_domain(f: &Bool, max_n: usize, field: i128) -> Option<(Int, Vec<i128>)> {
    let poly = unwrap_zero_mod_eq(f, field)?;
    let vars = free_int_nodes(f);
    if vars.len() != 1 {
        return None;
    }
    let sym = vars.into_iter().next()?;
    let poly_dyn = Dynamic::from_ast(&poly);
    let mut roots = Vec::new();
    for v in 0..=(max_n as i128) {
        if eval_univariate(&poly_dyn, &sym, v)?.rem_euclid(field) == 0 {
            roots.push(v);
        }
    }
    if roots.len() <= 1 {
        return None;
    }
    Some((sym, roots))
}

fn poly_choices(assertions: &[Bool], max_n: usize, field: i128) -> HashMap<Int, Vec<i128>> {
    let mut out = HashMap::new();
    for a in assertions {
        if let Some((sym, roots)) = poly_domain(a, max_n, field) {
            out.entry(sym).or_insert(roots);
        }
    }
    out
}

// ---------------------------------------------------------------------------
// Components
// ---------------------------------------------------------------------------

fn const_pinned_in(f: &Bool) -> HashSet<Int> {
    if let Some((sym, _)) = eq_symbol_int(f) {
        return HashSet::from([sym]);
    }
    if let Some(parts) = and_parts(f) {
        return parts.iter().flat_map(const_pinned_in).collect();
    }
    HashSet::new()
}

fn const_pinned(assertions: &[Bool]) -> HashSet<Int> {
    assertions.iter().flat_map(const_pinned_in).collect()
}

fn uf_find(parent: &mut HashMap<Int, Int>, x: &Int) -> Int {
    let mut cur = x.clone();
    loop {
        let p = parent.get(&cur).cloned().unwrap_or_else(|| cur.clone());
        if p.ast_eq(&cur) {
            return cur;
        }
        // path halving
        let pp = parent.get(&p).cloned().unwrap_or_else(|| p.clone());
        parent.insert(cur.clone(), pp.clone());
        cur = p;
    }
}

fn uf_union(parent: &mut HashMap<Int, Int>, a: &Int, b: &Int) {
    let ra = uf_find(parent, a);
    let rb = uf_find(parent, b);
    if !ra.ast_eq(&rb) {
        parent.insert(ra, rb);
    }
}

/// Connected components of choice symbols linked by *narrow* assertions.
///
/// A narrow assertion is one whose free variables are all either choice symbols
/// or constant-pinned auxiliaries (booleanity, one-hot sum, decode-constant
/// link). Its choice symbols get unioned. Constant-pinned aux vars (an opcode
/// concretized to a literal, a zeroed column) are known values, so pulling them
/// and their defining assertions into the slice keeps it self-contained without
/// dragging in wide data columns. The component is the self-contained slice that
/// forces a selector -- a bare per-row cluster is generally too small.
fn selector_components(
    assertions: &[Bool],
    choices: &HashMap<Int, Vec<i128>>,
    pinned: &HashSet<Int>,
) -> Vec<HashSet<Int>> {
    let choice_syms: HashSet<Int> = choices.keys().cloned().collect();
    let allowed: HashSet<Int> = choice_syms.union(pinned).cloned().collect();
    let mut parent: HashMap<Int, Int> = choice_syms.iter().map(|s| (s.clone(), s.clone())).collect();

    for a in assertions {
        let fvs = free_int_nodes(a);
        if fvs.is_empty() || !fvs.is_subset(&allowed) {
            continue;
        }
        let cs: Vec<Int> = fvs.iter().filter(|v| choice_syms.contains(v)).cloned().collect();
        for other in cs.iter().skip(1) {
            uf_union(&mut parent, &cs[0], other);
        }
    }

    let mut groups: HashMap<Int, HashSet<Int>> = HashMap::new();
    for s in &choice_syms {
        let r = uf_find(&mut parent, s);
        groups.entry(r).or_default().insert(s.clone());
    }
    groups.into_values().collect()
}

fn component_slice(
    assertions: &[Bool],
    component: &HashSet<Int>,
    pinned: &HashSet<Int>,
) -> Vec<Bool> {
    let allowed: HashSet<Int> = component.union(pinned).cloned().collect();
    let narrow: Vec<Bool> = assertions
        .iter()
        .filter(|a| {
            let fvs = free_int_nodes(a);
            !fvs.is_empty() && fvs.is_subset(&allowed) && !fvs.is_disjoint(component)
        })
        .cloned()
        .collect();
    let used_pinned: HashSet<Int> = narrow
        .iter()
        .flat_map(free_int_nodes)
        .filter(|v| pinned.contains(v))
        .collect();
    let mut rel = narrow;
    for a in assertions {
        let fvs = free_int_nodes(a);
        if !fvs.is_empty() && fvs.is_subset(&used_pinned) && !rel.iter().any(|x| x.ast_eq(a)) {
            rel.push(a.clone());
        }
    }
    rel
}

// ---------------------------------------------------------------------------
// One-shot probing
// ---------------------------------------------------------------------------

struct ProbeOutcomes {
    probes_sat: usize,
    probes_unsat: usize,
    probes_unknown: usize,
    pinned: usize,
}

/// One-shot `z3` subprocess. Returns `Some(true)`=sat, `Some(false)`=unsat,
/// `None`=unknown/error. Not incremental: a fresh solve keeps z3's full tactic.
fn oneshot(prefix: &str, formulas: &[Bool], budget_s: u32) -> Option<bool> {
    let mut body = String::with_capacity(prefix.len() + 64 * formulas.len());
    body.push_str(prefix);
    for f in formulas {
        body.push_str("(assert ");
        body.push_str(&f.to_string());
        body.push_str(")\n");
    }
    body.push_str("(check-sat)\n");

    let seq = PROBE_FILE_SEQ.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "domain_probe_{}_{}.smt2",
        std::process::id(),
        seq
    ));
    if std::fs::write(&path, body.as_bytes()).is_err() {
        return None;
    }
    let solver = std::env::var("SIMPLIFIER_SOLVER").unwrap_or_else(|_| "z3-nightly".to_string());
    let output = std::process::Command::new(&solver)
        .arg(format!("-T:{budget_s}"))
        .arg("smt.random_seed=0")
        .arg("sat.random_seed=0")
        .arg(&path)
        .output();
    let _ = std::fs::remove_file(&path);

    let out = output.ok()?;
    let stdout = String::from_utf8_lossy(&out.stdout);
    let mut result = None;
    for line in stdout.lines() {
        match line.trim() {
            "unsat" => return Some(false),
            "sat" => result = Some(true),
            _ => {}
        }
    }
    result
}

fn batch_contains(batch: &[Bool], fact: &Bool) -> bool {
    batch.iter().any(|b| b.ast_eq(fact))
}

/// Probe each selector's candidate values against the component slice `rel`.
///
/// Proven exclusions and pins accumulate in `extra` and feed back into later
/// probes of the same component (an earlier pin often makes a later one cheap).
/// Only forced-value *pins* are emitted to `batch`: they get substituted by the
/// downstream `z3-propagate-values` and collapse the selector-gated cubics.
/// Exclusions are kept only as internal hints -- emitting the `(not (= v c))`
/// inequalities would perturb otherwise-easy formulas without collapsing
/// anything. Every emitted pin is still entailed by `rel` (a subset of the
/// assertions), so the exclusion hints do not affect soundness.
fn probe_component(
    prefix: &str,
    rel: &[Bool],
    component_choices: &HashMap<Int, Vec<i128>>,
    batch: &mut Vec<Bool>,
    deadline: Instant,
) -> ProbeOutcomes {
    let mut out = ProbeOutcomes {
        probes_sat: 0,
        probes_unsat: 0,
        probes_unknown: 0,
        pinned: 0,
    };
    let mut extra: Vec<Bool> = Vec::new();

    let mut syms: Vec<_> = component_choices.iter().collect();
    syms.sort_by_cached_key(|(s, _)| decl_name(&s.decl()));
    for (sym, vals) in syms {
        if Instant::now() > deadline {
            break;
        }
        let mut sat_vals: Vec<i128> = Vec::new();
        let mut unsat_vals: Vec<i128> = Vec::new();
        for v in vals {
            if Instant::now() > deadline {
                break;
            }
            let eq = sym.eq(&int_from_i128(*v));
            let mut formulas: Vec<Bool> = rel.to_vec();
            formulas.extend(extra.iter().cloned());
            formulas.push(eq.clone());
            match oneshot(prefix, &formulas, PROBE_BUDGET_S) {
                Some(true) => {
                    out.probes_sat += 1;
                    sat_vals.push(*v);
                }
                Some(false) => {
                    out.probes_unsat += 1;
                    unsat_vals.push(*v);
                    extra.push(eq.not()); // internal hint only
                }
                None => out.probes_unknown += 1,
            }
        }
        // Forced value: every candidate but one refuted. The surviving value is
        // then entailed by the slice -- confirm it directly (refute sym != v) so
        // soundness never relies on the probed domain being exhaustive, and emit
        // the equality.
        if sat_vals.len() == 1 && unsat_vals.len() == vals.len() - 1 && Instant::now() <= deadline {
            let survivor = sat_vals[0];
            let eqp = sym.eq(&int_from_i128(survivor));
            if !batch_contains(batch, &eqp) {
                let mut formulas: Vec<Bool> = rel.to_vec();
                formulas.extend(extra.iter().cloned());
                formulas.push(eqp.not());
                if oneshot(prefix, &formulas, PROBE_BUDGET_S) == Some(false) {
                    batch.push(eqp.clone());
                    extra.push(eqp);
                    out.pinned += 1;
                }
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn has_solver() -> bool {
        let solver = std::env::var("SIMPLIFIER_SOLVER").unwrap_or_else(|_| "z3-nightly".to_string());
        std::process::Command::new(&solver)
            .arg("--version")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
    }

    fn int_const(name: &str) -> Int {
        Int::new_const(name)
    }

    #[test]
    fn component_slice_drops_wide_columns() {
        let script = Script::parse(
            "(assert (or (= opcode_and_flag 0) (= opcode_and_flag 1)))\n\
             (assert (= (* opcode_and_flag a__0_0) a__0_0))\n\
             (check-sat)\n",
        )
        .unwrap();
        let asserts = collect_assert_terms(&script);
        let flag_dom = asserts[0].clone();
        let choices = collect_choices(&asserts, 3);
        let pinned = const_pinned(&asserts);
        let components = selector_components(&asserts, &choices, &pinned);
        assert_eq!(components.len(), 1);
        assert!(components[0].contains(&int_const("opcode_and_flag")));
        assert!(!components[0].contains(&int_const("a__0_0")));
        let sliced = component_slice(&asserts, &components[0], &pinned);
        assert_eq!(sliced.len(), 1);
        assert!(sliced[0].ast_eq(&flag_dom));
    }

    #[test]
    fn component_links_pinned_aux_vars() {
        let script = Script::parse(
            "(assert (and (or (= x 0) (= x 1)) (= y 0)))\n(check-sat)\n",
        )
        .unwrap();
        let asserts = collect_assert_terms(&script);
        let choices = collect_choices(&asserts, 3);
        let pinned = const_pinned(&asserts);
        assert!(pinned.contains(&int_const("y")));
        let components = selector_components(&asserts, &choices, &pinned);
        assert_eq!(components, vec![HashSet::from([int_const("x")])]);
        let sliced = component_slice(&asserts, &HashSet::from([int_const("x")]), &pinned);
        assert!(sliced.iter().any(|a| a.ast_eq(&asserts[0])));
    }

    #[test]
    fn pins_forced_value_via_bounds() {
        if !has_solver() {
            return;
        }
        std::env::set_var("SIMPLIFIER_FIELD_MOD", "2013265921");
        let script = Script::parse(
            "(declare-fun x () Int)\n(assert (and (or (= x 0) (= x 1)) (<= 1 x) (<= x 1)))\n(check-sat)\n",
        )
        .unwrap();
        let (out, stats) = apply(&script).unwrap();
        assert!(stats["added_facts"].as_u64().unwrap() >= 1);
        let s = smt2::dump_string(&out);
        assert!(s.contains("(= x 1)"));
    }

    #[test]
    fn binary_disjunction_no_facts() {
        if !has_solver() {
            return;
        }
        let script = Script::parse(
            "(declare-fun x () Int)\n(assert (or (= x 0) (= x 1)))\n(check-sat)\n",
        )
        .unwrap();
        let (_out, stats) = apply(&script).unwrap();
        assert_eq!(stats["added_facts"], 0);
    }
}
