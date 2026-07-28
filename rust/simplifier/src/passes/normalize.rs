//! Polynomial Int relation normalization (Python ``simplify_normalize`` parity).

use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};

use smt2::command::SmtCommand;
use smt2::{
    assert_commands, ast_hash_dyn, ast_hash_int, debug_assert_direct_int_operand,
    declared_symbol_ids, ensure_free_symbols_declared, int_from_i128,
    int_value, int_value_dyn, map_bool_children, parse_single_command, seed_parser_context,
    symbol_id_dyn, IntTermSet, ParseCtx, Script,
};
use smt2::ast_build::{substitute_dyn, symbol_name_dyn};
use z3::ast::{Ast, AstKind, Bool, Dynamic, Int};
use z3::{DeclKind, SortKind};

type Monomial = Vec<u32>;
type Poly = HashMap<Monomial, i128>;

pub fn apply(script: &Script) -> Result<(Script, serde_json::Value), String> {
    let p = field_mod();
    let var_terms = collect_variables(script, p);
    let ctx = NormalizeCtx {
        var_terms: &var_terms,
        field_mod: p,
    };

    let total = assert_commands(script).len();
    let mut changed = 0usize;
    let mut parse_ctx = ParseCtx::new();
    seed_parser_context(&mut parse_ctx, script)?;
    let mut declared = declared_symbol_ids(&script.commands);
    let mut commands = Vec::with_capacity(script.commands.len());
    for cmd in &script.commands {
        match cmd {
            SmtCommand::Assert { bool: b, span, .. } => {
                let new_b = normalize_term(b, &ctx);
                if !new_b.ast_eq(b) {
                    ensure_free_symbols_declared(&new_b, &mut parse_ctx, &mut declared)?;
                    changed += 1;
                    commands.push(SmtCommand::Assert {
                        bool: new_b,
                        span: *span,
                        term_text: None,
                    });
                } else {
                    commands.push(cmd.clone());
                }
            }
            _ => commands.push(cmd.clone()),
        }
    }
    let out = Script::from_commands(&script.source, commands);

    let stats = serde_json::json!({
        "asserts": total,
        "asserts_changed": changed,
        "int_vars": var_terms.len(),
    });
    Ok((out, stats))
}

pub fn field_mod() -> Option<i128> {
    std::env::var("SIMPLIFIER_FIELD_MOD")
        .ok()
        .and_then(|s| s.parse().ok())
}

struct NormalizeCtx<'a> {
    var_terms: &'a IntTermSet,
    field_mod: Option<i128>,
}

fn int_literal_mod(t: &Int, modulo: Option<i128>) -> Option<i128> {
    let m = modulo?;
    int_value(t).map(|v| coeff_mod(v, m))
}

fn collect_variables(script: &Script, field_mod: Option<i128>) -> IntTermSet {
    let mut terms = IntTermSet::new();
    let mut seen: HashSet<u64> = HashSet::new();

    fn visit(
        n: &Dynamic,
        field_mod: Option<i128>,
        terms: &mut IntTermSet,
        seen: &mut HashSet<u64>,
    ) {
        if !seen.insert(ast_hash_dyn(n)) {
            return;
        }

        if int_value_dyn(n).is_some() {
            return;
        }

        if n.kind() == AstKind::Var {
            return;
        }

        if symbol_id_dyn(n).is_some() && n.get_sort().kind() == SortKind::Bool {
            return;
        }

        if n.kind() == AstKind::Quantifier {
            if let Some(body) = smt2::quantifier_body(n) {
                visit(&body, field_mod, terms, seen);
            }
            return;
        }

        if let Some(int_n) = n.as_int() {
            if n.kind() == AstKind::App {
                if let Some(p) = field_mod {
                    if n.decl().kind() == DeclKind::Mod
                        && n.num_children() == 2
                        && n
                            .nth_child(1)
                            .and_then(|m| int_value_dyn(&m))
                            .map(|m| m == p)
                            .unwrap_or(false)
                    {
                        if let Some(body) = n.nth_child(0) {
                            visit(&body, field_mod, terms, seen);
                        }
                        return;
                    }
                }
                if is_combinator_kind(n.decl().kind()) {
                    for i in 0..n.num_children() {
                        if let Some(ch) = n.nth_child(i) {
                            visit(&ch, field_mod, terms, seen);
                        }
                    }
                    return;
                }
            }
            debug_assert!(
                n.get_sort().kind() != SortKind::Bool,
                "polynomial generator must not be Bool-sorted"
            );
            terms.insert(int_n);
            return;
        }

        if n.kind() == AstKind::App {
            if is_bool_or_relation_kind(n.decl().kind()) {
                for i in 0..n.num_children() {
                    if let Some(ch) = n.nth_child(i) {
                        visit(&ch, field_mod, terms, seen);
                    }
                }
                return;
            }
        }
        for i in 0..n.num_children() {
            if let Some(ch) = n.nth_child(i) {
                visit(&ch, field_mod, terms, seen);
            }
        }
    }

    for cmd in assert_commands(script) {
        if let Some(b) = cmd.assert_bool() {
            visit(&Dynamic::from_ast(b), field_mod, &mut terms, &mut seen);
        }
    }

    sort_terms(terms)
}

fn term_sort_key(t: &Int) -> (u8, String) {
    let dyn_ = Dynamic::from_ast(t);
    if let Some(name) = smt2::symbol_name_dyn(&dyn_) {
        (0, name)
    } else {
        (1, format!("{:016x}", ast_hash_int(t)))
    }
}

fn sort_terms(terms: IntTermSet) -> IntTermSet {
    let mut keyed: Vec<((u8, String), Int)> = terms
        .into_terms()
        .into_iter()
        .map(|t| (term_sort_key(&t), t))
        .collect();
    keyed.sort_by(|a, b| a.0.cmp(&b.0));
    IntTermSet::from_sorted_unique(keyed.into_iter().map(|(_, t)| t).collect())
}

fn is_combinator_kind(kind: DeclKind) -> bool {
    matches!(kind, DeclKind::Add | DeclKind::Sub | DeclKind::Mul)
}

fn is_bool_or_relation_kind(kind: DeclKind) -> bool {
    matches!(
        kind,
        DeclKind::And
            | DeclKind::Or
            | DeclKind::Not
            | DeclKind::Implies
            | DeclKind::Ite
            | DeclKind::Eq
            | DeclKind::Lt
            | DeclKind::Le
            | DeclKind::Gt
            | DeclKind::Ge
            | DeclKind::Distinct
    )
}

fn field_mod_wrap(t: &Int, p: i128) -> bool {
    t.kind() == AstKind::App
        && t.decl().kind() == DeclKind::Mod
        && t.num_children() == 2
        && t
            .nth_child(1)
            .and_then(|m| int_value_dyn(&m))
            .map(|m| m == p)
            .unwrap_or(false)
}

fn unwrap_field_mod_body(t: &Int, p: i128) -> Int {
    if !field_mod_wrap(t, p) {
        return t.clone();
    }
    t.nth_child(0)
        .and_then(|c| c.as_int())
        .unwrap_or_else(|| t.clone())
}

fn mono_degree(m: &Monomial) -> usize {
    m.len()
}

fn compare_monomials(e1: &Monomial, e2: &Monomial) -> Ordering {
    let d1 = mono_degree(e1);
    let d2 = mono_degree(e2);
    if d1 != d2 {
        return d1.cmp(&d2);
    }
    let mut i1 = 0;
    let mut i2 = 0;
    while i1 < e1.len() {
        let idx1 = e1[i1];
        let idx2 = e2[i2];
        if idx1 < idx2 {
            return Ordering::Greater;
        }
        if idx2 < idx1 {
            return Ordering::Less;
        }
        let idx = idx1;
        let mut j1 = i1;
        while j1 < e1.len() && e1[j1] == idx {
            j1 += 1;
        }
        let mut j2 = i2;
        while j2 < e2.len() && e2[j2] == idx {
            j2 += 1;
        }
        let c1 = j1 - i1;
        let c2 = j2 - i2;
        if c1 != c2 {
            return c1.cmp(&c2);
        }
        i1 = j1;
        i2 = j2;
    }
    Ordering::Equal
}

fn mono_mul(e1: &Monomial, e2: &Monomial) -> Monomial {
    if e1.is_empty() {
        return e2.clone();
    }
    if e2.is_empty() {
        return e1.clone();
    }
    let mut out = e1.clone();
    out.extend_from_slice(e2);
    out.sort_unstable();
    out
}

fn lead_exp(poly: &Poly) -> Option<&Monomial> {
    poly.keys().max_by(|a, b| compare_monomials(a, b))
}

fn coeff_mod(v: i128, m: i128) -> i128 {
    v.rem_euclid(m)
}

fn poly_add(mut a: Poly, b: &Poly, scale_b: i128, modulo: Option<i128>) -> Poly {
    for (e, &cb) in b {
        *a.entry(e.clone()).or_insert(0) += scale_b * cb;
    }
    if let Some(m) = modulo {
        for v in a.values_mut() {
            *v = coeff_mod(*v, m);
        }
    }
    a.retain(|_, v| *v != 0);
    a
}

fn poly_mul(a: &Poly, b: &Poly, modulo: Option<i128>) -> Poly {
    let mut out = Poly::new();
    for (e1, c1) in a {
        for (e2, c2) in b {
            let e = mono_mul(e1, e2);
            let v = out.get(&e).copied().unwrap_or(0) + c1 * c2;
            let v = if let Some(m) = modulo {
                coeff_mod(v, m)
            } else {
                v
            };
            if v != 0 {
                out.insert(e, v);
            } else {
                out.remove(&e);
            }
        }
    }
    out
}

fn relation_modular(lhs: &Int, rhs: &Int, p: i128) -> Option<bool> {
    let lhs_m = field_mod_wrap(lhs, p);
    let rhs_m = field_mod_wrap(rhs, p);
    if lhs_m == rhs_m {
        return Some(lhs_m);
    }
    if lhs_m && int_value(rhs).is_some() {
        return Some(true);
    }
    if rhs_m && int_value(lhs).is_some() {
        return Some(true);
    }
    None
}

fn expr_to_poly(n: &Int, var_terms: &IntTermSet, modulo: Option<i128>) -> Option<Poly> {
    if let Some(m) = int_literal_mod(n, modulo).or_else(|| int_value(n)) {
        return if m == 0 {
            Some(Poly::new())
        } else {
            Some(HashMap::from([(Vec::new(), m)]))
        };
    }

    if n.kind() == AstKind::App {
        match n.decl().kind() {
            DeclKind::Add => {
                let mut acc = Poly::new();
                for i in 0..n.num_children() {
                    let q = expr_to_poly(&n.nth_child(i)?.as_int()?, var_terms, modulo)?;
                    acc = poly_add(acc, &q, 1, modulo);
                }
                Some(acc)
            }
            DeclKind::Uminus if n.num_children() == 1 => {
                let ch = n.nth_child(0)?.as_int()?;
                expr_to_poly(&ch, var_terms, modulo).map(|mut p| {
                    for v in p.values_mut() {
                        *v = -*v;
                        if let Some(m) = modulo {
                            *v = coeff_mod(*v, m);
                        }
                    }
                    p.retain(|_, v| *v != 0);
                    p
                })
            }
            DeclKind::Sub if n.num_children() == 2 => {
                let pa = expr_to_poly(&n.nth_child(0)?.as_int()?, var_terms, modulo)?;
                let pb = expr_to_poly(&n.nth_child(1)?.as_int()?, var_terms, modulo)?;
                Some(poly_add(pa, &pb, -1, modulo))
            }
            DeclKind::Mul => {
                let mut acc = Poly::from([(Vec::new(), 1i128)]);
                for i in 0..n.num_children() {
                    let q = expr_to_poly(&n.nth_child(i)?.as_int()?, var_terms, modulo)?;
                    acc = poly_mul(&acc, &q, modulo);
                }
                Some(acc)
            }
            _ => {
                let idx = var_terms.index_of(n)?;
                Some(HashMap::from([(vec![idx as u32], 1)]))
            }
        }
    } else {
        let idx = var_terms.index_of(n)?;
        Some(HashMap::from([(vec![idx as u32], 1)]))
    }
}

fn int_mul(args: &[&Int]) -> Int {
    for a in args {
        debug_assert_direct_int_operand(a);
    }
    match args {
        [] => int_from_i128(1),
        [a] => (*a).clone(),
        _ => Int::mul(args),
    }
}

fn int_add(args: &[Int]) -> Int {
    for a in args {
        debug_assert_direct_int_operand(a);
    }
    match args {
        [] => int_from_i128(0),
        [a] => a.clone(),
        _ => Int::add(args),
    }
}

fn poly_to_expr(poly: &Poly, var_terms: &IntTermSet) -> Int {
    if poly.is_empty() {
        return int_from_i128(0);
    }
    let mut items: Vec<(&Monomial, i128)> = poly.iter().map(|(k, v)| (k, *v)).collect();
    items.sort_by(|a, b| compare_monomials(b.0, a.0));

    let mut terms = Vec::new();
    for (e, c) in items {
        if c == 0 {
            continue;
        }
        let mono_factors: Vec<&Int> = e
            .iter()
            .map(|&idx| var_terms.get(idx as usize).unwrap())
            .collect();
        let term = if e.is_empty() {
            int_from_i128(c)
        } else if c == 1 {
            int_mul(&mono_factors)
        } else if c == -1 {
            Int::unary_minus(&int_mul(&mono_factors))
        } else {
            let coeff = int_from_i128(c);
            let mut factors: Vec<&Int> = Vec::with_capacity(mono_factors.len() + 1);
            factors.push(&coeff);
            factors.extend_from_slice(&mono_factors);
            int_mul(&factors)
        };
        terms.push(term);
    }

    if terms.is_empty() {
        int_from_i128(0)
    } else {
        int_add(&terms)
    }
}

fn poly_diff_poly(
    la: &Int,
    lb: &Int,
    var_terms: &IntTermSet,
    modulo: Option<i128>,
) -> Option<Poly> {
    let pla = expr_to_poly(la, var_terms, modulo)?;
    let plb = expr_to_poly(lb, var_terms, modulo)?;
    Some(poly_add(pla, &plb, -1, modulo))
}

fn gcd_i128(mut a: i128, mut b: i128) -> i128 {
    a = a.abs();
    b = b.abs();
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

fn mod_inverse(a: i128, m: i128) -> Option<i128> {
    let a = coeff_mod(a, m);
    if a == 0 {
        return None;
    }
    let (mut t, mut newt) = (0i128, 1i128);
    let (mut r, mut newr) = (m, a);
    while newr != 0 {
        let q = r / newr;
        (t, newt) = (newt, t - q * newt);
        (r, newr) = (newr, r - q * newr);
    }
    if r != 1 {
        return None;
    }
    Some(coeff_mod(t, m))
}

fn rescale_monic(poly: &Poly, modulo: i128) -> Option<Poly> {
    let lead = lead_exp(poly)?;
    let lc = coeff_mod(poly[lead], modulo);
    if lc == 0 {
        return Some(Poly::new());
    }
    let inv = mod_inverse(lc, modulo)?;
    Some(
        poly.iter()
            .filter_map(|(e, &c)| {
                let v = coeff_mod(c * inv, modulo);
                if v != 0 { Some((e.clone(), v)) } else { None }
            })
            .collect(),
    )
}

fn rescale_gcd(poly: Poly) -> Poly {
    if poly.is_empty() {
        return poly;
    }
    let mut g = 0i128;
    for c in poly.values() {
        g = gcd_i128(g, c.abs());
    }
    if g == 0 {
        return Poly::new();
    }
    let lc = lead_exp(&poly).map(|l| poly[l]).unwrap_or(0);
    if lc < 0 {
        g = -g;
    }
    poly.into_iter()
        .filter_map(|(e, c)| {
            let v = c / g;
            if v != 0 { Some((e, v)) } else { None }
        })
        .collect()
}

/// Divide all coefficients by their (positive) gcd, preserving the sign.
///
/// Unlike [`rescale_gcd`], this never negates the polynomial. Sign is a unit
/// for `= 0` (so `rescale_gcd` may flip it there), but it is load-bearing for
/// `<` / `<=`: dividing `diff < 0` by a *negative* value would flip the
/// relation to `diff' > 0`. Inequalities must divide by the positive gcd only.
fn rescale_gcd_keep_sign(poly: Poly) -> Poly {
    if poly.is_empty() {
        return poly;
    }
    let mut g = 0i128;
    for c in poly.values() {
        g = gcd_i128(g, c.abs());
    }
    if g == 0 {
        return Poly::new();
    }
    poly.into_iter()
        .filter_map(|(e, c)| {
            let v = c / g;
            if v != 0 { Some((e, v)) } else { None }
        })
        .collect()
}

fn relation_poly_diff_plain(
    lhs: &Int,
    rhs: &Int,
    ctx: &NormalizeCtx<'_>,
) -> Option<(Poly, bool)> {
    let Some(p) = ctx.field_mod else {
        let diff = poly_diff_poly(lhs, rhs, ctx.var_terms, None)?;
        return Some((diff, false));
    };
    if relation_modular(lhs, rhs, p)? {
        let la = unwrap_field_mod_body(lhs, p);
        let lb = unwrap_field_mod_body(rhs, p);
        let diff = poly_diff_poly(&la, &lb, ctx.var_terms, Some(p))?;
        Some((diff, true))
    } else {
        let diff = poly_diff_poly(lhs, rhs, ctx.var_terms, None)?;
        Some((diff, false))
    }
}

fn wrap_mod_expr(rep: Int, p: i128) -> Int {
    rep.modulo(int_from_i128(p))
}

fn field_eq(rep: Int, p: i128) -> Bool {
    wrap_mod_expr(rep, p).eq(int_from_i128(0))
}

fn normalize_int_rel_gcd(
    lhs: &Int,
    rhs: &Int,
    ctx: &NormalizeCtx<'_>,
) -> Option<Int> {
    let (diff, modular) = relation_poly_diff_plain(lhs, rhs, ctx)?;
    // Field reduction (mod P) preserves "= 0" but NOT order, so we must not
    // build a modular representative for `<` / `<=`: `(mod _ P)` is never
    // negative, which would make every modular inequality unconditionally
    // false (the guest-keccak 2102932 034->035 vacuous-unsat bug). Decline and
    // leave the encoder's comparison intact.
    if modular {
        return None;
    }
    if diff.is_empty() {
        return Some(int_from_i128(0));
    }
    Some(poly_to_expr(&rescale_gcd_keep_sign(diff), ctx.var_terms))
}

fn normalize_equals(
    lhs: &Int,
    rhs: &Int,
    ctx: &NormalizeCtx<'_>,
) -> Option<Bool> {
    let (diff, modular) = relation_poly_diff_plain(lhs, rhs, ctx)?;
    let rep = if diff.is_empty() {
        int_from_i128(0)
    } else if modular {
        let p = ctx.field_mod?;
        let scaled = rescale_monic(&diff, p).unwrap_or_else(|| rescale_gcd(diff));
        poly_to_expr(&scaled, ctx.var_terms)
    } else {
        poly_to_expr(&rescale_gcd(diff), ctx.var_terms)
    };
    if modular {
        Some(field_eq(rep, ctx.field_mod?))
    } else {
        Some(rep.eq(int_from_i128(0)))
    }
}

fn normalize_term(term: &Bool, ctx: &NormalizeCtx<'_>) -> Bool {
    let ast = Dynamic::from_ast(term);
    if ast.kind() == AstKind::Quantifier {
        let bounds = smt2::quantifier_bounds(&ast);
        let is_forall = smt2::is_forall(&ast);
        let body = smt2::quantifier_body_bool(&ast).expect("quantifier body");
        let new_body = normalize_term(&body, ctx);
        return smt2::rebuild_quantifier_dyn(is_forall, &bounds, &new_body);
    }
    if term.kind() == AstKind::App && term.num_children() == 2 {
        let lhs = term.nth_child(0).and_then(|c| c.as_int());
        let rhs = term.nth_child(1).and_then(|c| c.as_int());
        if let (Some(lhs), Some(rhs)) = (lhs, rhs) {
            match term.decl().kind() {
                DeclKind::Eq => {
                    if let Some(rep) = normalize_equals(&lhs, &rhs, ctx) {
                        return rep;
                    }
                }
                DeclKind::Lt => {
                    if let Some(rep) = normalize_int_rel_gcd(&lhs, &rhs, ctx) {
                        return rep.lt(&int_from_i128(0));
                    }
                }
                DeclKind::Le => {
                    if let Some(rep) = normalize_int_rel_gcd(&lhs, &rhs, ctx) {
                        return rep.le(&int_from_i128(0));
                    }
                }
                _ => {}
            }
        }
    }
    map_bool_children(term, &mut |a| normalize_term(a, ctx))
}

// ---------------------------------------------------------------------------
// diff_vars pass: substitute ``x -> y + d`` for pairs ``(x, y)`` that occur only
// as the difference ``x - y`` in the nonlinear (mod) constraints. Colocated here
// to reuse this module's polynomial machinery. Sound (invertible change of
// variables); collapses ``(x - y)^2`` quadratics that z3 nlsat times out on.
// ---------------------------------------------------------------------------

fn coeff2(poly: &Poly, a: u32, b: u32, p: i128) -> i128 {
    let mut m = vec![a, b];
    m.sort();
    coeff_mod(*poly.get(&m).unwrap_or(&0), p)
}

/// ``(x, y)`` occur only as ``x - y`` in ``poly``'s quadratic part: the ``(x-y)^2``
/// diagonal plus ``coeff(x·k) = -coeff(y·k)`` for every other ``k``.
fn pair_reduces(poly: &Poly, i: u32, j: u32, p: i128) -> (bool, bool) {
    let cii = coeff2(poly, i, i, p);
    if cii != coeff2(poly, j, j, p) || coeff2(poly, i, j, p) != coeff_mod(-2 * cii, p) {
        return (false, false);
    }
    let ks: HashSet<u32> = poly
        .keys()
        .flat_map(|m| m.iter().copied())
        .filter(|&k| k != i && k != j)
        .collect();
    for k in ks {
        if coeff2(poly, i, k, p) != coeff_mod(-coeff2(poly, j, k, p), p) {
            return (false, false);
        }
    }
    (true, cii != 0)
}

fn detect_pairs(rels: &[Poly], p: i128) -> Vec<(u32, u32)> {
    let mut squared: Vec<u32> = rels
        .iter()
        .flat_map(|poly| poly.keys())
        .filter(|m| m.len() == 2 && m[0] == m[1])
        .map(|m| m[0])
        .collect();
    squared.sort_unstable();
    squared.dedup();
    let squared_set: HashSet<u32> = squared.iter().copied().collect();

    // Inverted index + co-occurrence, over squared vars only. A viable difference
    // pair ``(i, j)`` must reduce in *every* relation, but in a relation where
    // neither appears in a degree-2 monomial ``pair_reduces`` holds trivially (all
    // coeffs 0) -- so we only ever verify the union of the two vars' relation lists
    // (``var_rels``). And the two vars must co-occur in some relation, else the lone
    // var's squared/cross term breaks the symmetry -- so candidates are restricted to
    // co-occurring pairs (``cooccur``). Both cut the scan from O(S^2 * R) down to the
    // handful of relations each squared var actually touches. Since ``squared`` stays
    // sorted and the greedy ``used`` filter is unchanged, the chosen set is identical
    // to the exhaustive scan; only the wasted work on absent/non-co-occurring pairs
    // is removed.
    let mut var_rels: HashMap<u32, Vec<usize>> = HashMap::new();
    let mut cooccur: HashSet<(u32, u32)> = HashSet::new();
    for (r, poly) in rels.iter().enumerate() {
        let mut sq: Vec<u32> = poly
            .keys()
            .filter(|m| m.len() == 2)
            .flat_map(|m| m.iter().copied())
            .filter(|v| squared_set.contains(v))
            .collect();
        sq.sort_unstable();
        sq.dedup();
        for &v in &sq {
            var_rels.entry(v).or_default().push(r);
        }
        for a in 0..sq.len() {
            for b in (a + 1)..sq.len() {
                cooccur.insert((sq[a], sq[b]));
            }
        }
    }

    let mut chosen = Vec::new();
    let mut used: HashSet<u32> = HashSet::new();
    for a in 0..squared.len() {
        for b in (a + 1)..squared.len() {
            let (i, j) = (squared[a], squared[b]);
            if used.contains(&i) || used.contains(&j) {
                continue;
            }
            if !cooccur.contains(&(i, j)) {
                continue;
            }
            let mut check: Vec<usize> = Vec::new();
            if let Some(ri) = var_rels.get(&i) {
                check.extend_from_slice(ri);
            }
            if let Some(rj) = var_rels.get(&j) {
                check.extend_from_slice(rj);
            }
            check.sort_unstable();
            check.dedup();
            let mut all_ok = true;
            let mut coupled = false;
            for &r in &check {
                let (ok, has_sq) = pair_reduces(&rels[r], i, j, p);
                if !ok {
                    all_ok = false;
                    break;
                }
                coupled |= has_sq;
            }
            if all_ok && coupled {
                used.insert(i);
                used.insert(j);
                chosen.push((i, j));
            }
        }
    }
    chosen
}

fn collect_quad_rels(term: &Bool, ctx: &NormalizeCtx<'_>, out: &mut Vec<Poly>) {
    // Quantifier nodes are not apps; ``num_children()``/``nth_child()`` panic on
    // them in z3-rs. Soundness VCs can stay quantified (not-qf), so recurse into
    // the body instead of the child loop below.
    if term.kind() == AstKind::Quantifier {
        if let Some(body) = smt2::quantifier_body_bool(&Dynamic::from_ast(term)) {
            collect_quad_rels(&body, ctx, out);
        }
        return;
    }
    if term.kind() == AstKind::App && term.num_children() == 2 && term.decl().kind() == DeclKind::Eq
    {
        let lhs = term.nth_child(0).and_then(|c| c.as_int());
        let rhs = term.nth_child(1).and_then(|c| c.as_int());
        if let (Some(lhs), Some(rhs)) = (lhs, rhs) {
            if let Some((diff, true)) = relation_poly_diff_plain(&lhs, &rhs, ctx) {
                let quad: Poly = diff.into_iter().filter(|(m, _)| m.len() == 2).collect();
                if !quad.is_empty() {
                    out.push(quad);
                }
            }
        }
    }
    // Only applications expose children via `Z3_to_app`; quantifier and
    // bound-variable nodes are not apps, so `nth_child` on them panics inside
    // the z3 binding. diff_vars runs after quantifier elimination, so there is
    // nothing to collect under a quantifier -- skip rather than crash.
    if term.kind() != AstKind::App {
        return;
    }
    for k in 0..term.num_children() {
        if let Some(child) = term.nth_child(k).and_then(|c| c.as_bool()) {
            collect_quad_rels(&child, ctx, out);
        }
    }
}

pub fn diff_vars_apply(script: &Script) -> Result<(Script, serde_json::Value), String> {
    let p = field_mod();
    let mut var_terms = collect_variables(script, p);

    // Detect pairs on the original variables (before introducing d).
    let pairs = {
        let ctx = NormalizeCtx {
            var_terms: &var_terms,
            field_mod: p,
        };
        let mut rels = Vec::new();
        for cmd in &script.commands {
            if let SmtCommand::Assert { bool: b, .. } = cmd {
                collect_quad_rels(b, &ctx, &mut rels);
            }
        }
        match p {
            Some(pm) => detect_pairs(&rels, pm),
            None => Vec::new(),
        }
    };

    let noop = || Ok((script.clone(), serde_json::json!({"pairs": 0})));
    if pairs.is_empty() {
        return noop();
    }

    // Introduce a fresh ``d`` per pair and substitute ``x -> y + d`` uniformly
    // across every assert body (all constraint kinds, not just the modular
    // equalities). The following ``normalize`` pass re-expands ``(y + d)`` and
    // cancels ``y`` from the nonlinear part.
    let mut defs: Vec<(u32, u32, u32)> = Vec::new(); // (i, j, dgen)
    let mut subs: Vec<(String, Dynamic)> = Vec::new(); // (x name, replacement y + d)
    let mut d_names: Vec<String> = Vec::new();
    let mut names: Vec<String> = Vec::new();
    for &(i, j) in pairs.iter() {
        let xt = var_terms.get(i as usize).unwrap().clone();
        // Only symbol generators can be substituted/declared by name.
        let Some(xname) = symbol_name_dyn(&Dynamic::from_ast(&xt)) else {
            continue;
        };
        let yt = var_terms.get(j as usize).unwrap().clone();
        let yname = symbol_name_dyn(&Dynamic::from_ast(&yt)).unwrap_or_default();
        // Name the difference variable exactly as the Python pass does
        // (``<x>!diff``). z3's nlsat variable ordering is name-sensitive, so a
        // divergent name here alone flips solve<->timeout on these VCs.
        let d_name = format!("{xname}!diff");
        let d = Int::new_const(d_name.as_str());
        let dgen = var_terms.insert(d.clone()) as u32;
        subs.push((xname.clone(), Dynamic::from_ast(&int_add(&[yt, d]))));
        defs.push((i, j, dgen));
        d_names.push(d_name);
        names.push(format!("{xname}<-{yname}"));
    }
    if defs.is_empty() {
        return noop();
    }

    let mut parse_ctx = ParseCtx::new();
    seed_parser_context(&mut parse_ctx, script)?;

    let mut commands: Vec<SmtCommand> = Vec::new();
    let mut inserted_decls = false;
    for cmd in &script.commands {
        if !inserted_decls && matches!(cmd, SmtCommand::Assert { .. }) {
            // ``d`` must be declared before the asserts that reference it.
            // Declare unquoted to match the ``Int::new_const(d_name)`` used in
            // the substitution: ``@``/``!`` are valid simple-symbol chars, and
            // a quoted decl interns a *different* symbol id, so the pipeline's
            // ``ensure_declarations_for_asserts`` would re-declare it (duplicate).
            for d_name in &d_names {
                commands.push(parse_single_command(
                    &format!("(declare-fun {d_name} () Int)"),
                    &mut parse_ctx,
                )?);
            }
            inserted_decls = true;
        }
        match cmd {
            SmtCommand::Assert { bool: b, span, .. } => {
                let mut cur = Dynamic::from_ast(b);
                for (name, repl) in &subs {
                    cur = substitute_dyn(&cur, name, repl);
                }
                let nb = cur
                    .as_bool()
                    .ok_or("diff_vars: assert body not Bool after substitution")?;
                commands.push(SmtCommand::Assert {
                    bool: nb,
                    span: *span,
                    term_text: None,
                });
            }
            SmtCommand::CheckSat => {
                // Pin ``x = y + d`` so the change of variables is equisatisfiable
                // and ``x`` still appears in counterexample models.
                for (i, j, dgen) in &defs {
                    let x = var_terms.get(*i as usize).unwrap();
                    let y = var_terms.get(*j as usize).unwrap().clone();
                    let d = var_terms.get(*dgen as usize).unwrap().clone();
                    commands.push(SmtCommand::new_assert(x.eq(int_add(&[y, d]))));
                }
                commands.push(cmd.clone());
            }
            _ => commands.push(cmd.clone()),
        }
    }

    let out = Script::from_commands(&script.source, commands);
    let stats = serde_json::json!({ "pairs": defs.len(), "pair_vars": names });
    Ok((out, stats))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn p() -> i128 {
        field_mod().unwrap_or(2_147_483_647)
    }

    #[test]
    fn field_monic_scales_coeffs() {
        let _field_env = crate::field_env_guard();
        let p = p();
        std::env::set_var("SIMPLIFIER_FIELD_MOD", p.to_string());
        let script = Script::parse(&format!(
            "(declare-fun x () Int)\n\
             (declare-fun y () Int)\n\
             (assert (= (mod (+ (* 2 x) (* 4 y)) {p}) 0))\n\
             (check-sat)\n"
        ))
        .unwrap();
        let (out, _) = apply(&script).unwrap();
        let s = smt2::dump_string(&out);
        assert!(s.contains("(= (mod (+ x (* 2 y))"));
        assert!(s.contains(" 0)"));
    }

    #[test]
    fn orders_terms_grlex() {
        let _field_env = crate::field_env_guard();
        let p = p();
        std::env::set_var("SIMPLIFIER_FIELD_MOD", p.to_string());
        let script = Script::parse(&format!(
            "(declare-fun x () Int)\n\
             (declare-fun y () Int)\n\
             (assert (= (mod (+ y x) {p}) 0))\n\
             (check-sat)\n"
        ))
        .unwrap();
        let (out, _) = apply(&script).unwrap();
        let s = smt2::dump_string(&out);
        assert!(s.contains("(= (mod (+ x y)"));
    }

    #[test]
    fn collects_vars_under_bool_connectives() {
        let script = Script::parse(
            "(declare-fun x () Int)\n\
             (declare-fun y () Int)\n\
             (declare-fun a () Bool)\n\
             (assert (and a (= (+ x y) 0)))\n\
             (check-sat)\n",
        )
        .unwrap();
        let (_out, stats) = apply(&script).unwrap();
        assert_eq!(stats["int_vars"], 2);
    }

    #[test]
    fn skips_bool_equalities() {
        let script = Script::parse(
            "(declare-fun a () Bool)\n\
             (declare-fun b () Bool)\n\
             (assert (= a b))\n\
             (check-sat)\n",
        )
        .unwrap();
        let (out, _) = apply(&script).unwrap();
        let s = smt2::dump_string(&out);
        assert!(s.contains("(assert (= a b))"));
        assert!(!s.contains("(* -1"));
    }

    #[test]
    fn skips_int_bool_products() {
        let _field_env = crate::field_env_guard();
        let p = 2013265921i128;
        std::env::set_var("SIMPLIFIER_FIELD_MOD", p.to_string());
        let script = Script::parse(&format!(
            "(declare-fun x () Int)\n\
             (declare-fun flag () Bool)\n\
             (assert (= (mod (+ (* x flag) 1) {p}) 0))\n\
             (check-sat)\n"
        ))
        .unwrap();
        let (out, stats) = apply(&script).unwrap();
        assert_eq!(stats["asserts_changed"], 0);
        let s = smt2::dump_string(&out);
        assert!(s.contains("flag"));
        assert!(!s.contains("(* -1"));
    }

    #[test]
    fn skips_quantifier_bound_int_relations() {
        let _field_env = crate::field_env_guard();
        let p = 2013265921i128;
        std::env::set_var("SIMPLIFIER_FIELD_MOD", p.to_string());
        let script = Script::parse(&format!(
            "(assert (forall ((x Int) (flag Bool))
              (and (<= 131072 (mod x {p}))
                   (<= 4096 (mod (* 15360 x) {p}))
                   (not flag))))\n\
             (check-sat)\n"
        ))
        .unwrap();
        let (out, _) = apply(&script).unwrap();
        let s = smt2::dump_string(&out);
        assert!(s.contains("forall"));
        assert!(s.contains("(mod x"));
        assert!(s.contains("(not flag)"));
        assert!(!s.contains("(mod flag"));
        assert!(!s.contains("(* 15360 flag)"));
    }

    #[test]
    fn field_monic_negative_leading_coeff() {
        let _field_env = crate::field_env_guard();
        let p = 2013265921i128;
        std::env::set_var("SIMPLIFIER_FIELD_MOD", p.to_string());
        let script = Script::parse(&format!(
            "(declare-fun before-from_state__timestamp_1@37 () Int)\n\
             (declare-fun before-from_state__timestamp_2@73 () Int)\n\
             (declare-fun before-writes_aux__base__timestamp_lt_aux__lower_decomp__0_2@85 () Int)\n\
             (declare-fun before-writes_aux__base__timestamp_lt_aux__lower_decomp__1_2@86 () Int)\n\
             (assert (= (mod (+ 1 (* (- 1) before-from_state__timestamp_1@37) \
             before-from_state__timestamp_2@73 \
             (* (- 1) before-writes_aux__base__timestamp_lt_aux__lower_decomp__0_2@85) \
             (* (- 131072) before-writes_aux__base__timestamp_lt_aux__lower_decomp__1_2@86)) {p}) 0))\n\
             (check-sat)\n"
        ))
        .unwrap();
        apply(&script).unwrap();
    }

    #[test]
    fn weak_eq_divides_coeff_gcd() {
        let script = Script::parse(
            "(declare-fun x () Int)\n\
             (declare-fun y () Int)\n\
             (assert (= (+ (* 2 x) (* 4 y)) 0))\n\
             (check-sat)\n",
        )
        .unwrap();
        let (out, _) = apply(&script).unwrap();
        let s = smt2::dump_string(&out);
        assert!(s.contains("(= (+ x (* 2 y)) 0)"));
    }

    #[test]
    fn weak_lt_moves_to_diff() {
        let script = Script::parse(
            "(declare-fun x () Int)\n\
             (declare-fun y () Int)\n\
             (assert (< (+ y x) x))\n\
             (check-sat)\n",
        )
        .unwrap();
        let (out, _) = apply(&script).unwrap();
        let s = smt2::dump_string(&out);
        assert!(s.contains("(< y 0)"));
    }

    #[test]
    fn skips_non_field_mod() {
        let script = Script::parse(
            "(declare-fun x () Int)\n\
             (assert (= (mod x 7) 0))\n\
             (check-sat)\n",
        )
        .unwrap();
        let (out, _) = apply(&script).unwrap();
        let s = smt2::dump_string(&out);
        assert!(s.contains("(mod x 7)"));
    }

    #[test]
    fn zero_equals_zero() {
        let script = Script::parse("(assert (= 0 0))\n(check-sat)\n").unwrap();
        let (out, _) = apply(&script).unwrap();
        let s = smt2::dump_string(&out);
        assert!(s.contains("(= 0 0)"));
    }

    #[test]
    fn modular_lt_left_intact() {
        let _field_env = crate::field_env_guard();
        // (mod (y+x) P) < (mod x P): a genuine modular comparison. The old code
        // rewrote it to the always-false (mod y P) < 0 -- the guest-keccak
        // 2102932 034->035 vacuous-unsat bug. It must be left intact, because
        // field reduction (mod P) does not preserve order.
        let p = 2013265921i128;
        std::env::set_var("SIMPLIFIER_FIELD_MOD", p.to_string());
        let script = Script::parse(&format!(
            "(declare-fun x () Int)\n\
             (declare-fun y () Int)\n\
             (assert (< (mod (+ y x) {p}) (mod x {p})))\n\
             (check-sat)\n"
        ))
        .unwrap();
        let (out, stats) = apply(&script).unwrap();
        assert_eq!(stats["asserts_changed"], 0); // declined -> unchanged
        let s = smt2::dump_string(&out);
        assert!(s.contains(&format!("(mod x {p})"))); // RHS still a residue, not 0
    }

    #[test]
    fn modular_le_range_check_left_intact() {
        let _field_env = crate::field_env_guard();
        // (mod (x+y) P) <= 255 is a range check; the old code folded it into
        // the equality x+y == 255 (mod P). It must be left intact.
        let p = 2013265921i128;
        std::env::set_var("SIMPLIFIER_FIELD_MOD", p.to_string());
        let script = Script::parse(&format!(
            "(declare-fun x () Int)\n\
             (declare-fun y () Int)\n\
             (assert (<= (mod (+ y x) {p}) 255))\n\
             (check-sat)\n"
        ))
        .unwrap();
        let (out, stats) = apply(&script).unwrap();
        assert_eq!(stats["asserts_changed"], 0); // declined -> unchanged
        let s = smt2::dump_string(&out);
        assert!(s.contains("255")); // bound preserved, not folded into "= 0"
    }

    #[test]
    fn nonmodular_lt_preserves_sign() {
        // (3x < 5x) <=> x > 0. diff = -2x has a negative leading coeff; the old
        // gcd rescale negated it, flipping the relation to the unsound (< x 0).
        // Sign must be preserved on the non-modular path: expect (< (* -1 x) 0).
        let script = Script::parse(
            "(declare-fun x () Int)\n\
             (assert (< (* 3 x) (* 5 x)))\n\
             (check-sat)\n",
        )
        .unwrap();
        let (out, _) = apply(&script).unwrap();
        let s = smt2::dump_string(&out);
        // -x < 0  <=>  x > 0, equivalent to 3x < 5x. The buggy sign-flip would
        // have produced (< x 0) instead. Unary minus serializes as (- x).
        assert!(s.contains("(< (- x) 0)"), "sign must be preserved as (- x): {s}");
        assert!(!s.contains("(< x 0)"));
    }
}
