//! Equality rewrites for modular products via FLINT polynomial factorization.

use std::collections::{BTreeSet, HashMap, HashSet};

use smt2::{int_from_i128, int_value, is_int_numeral, map_asserts, map_bool_children_opt, unwrap_zero_mod_eq, Script};
use z3::ast::{Ast, AstKind, Dynamic, Int};
use z3::ast::Bool;
use z3::{SortKind, DeclKind};

use crate::passes::normalize::field_mod;
use crate::poly_factor::{factor, FactorError};

const MAX_REWRITE_COUNT: usize = 5;

#[derive(Default)]
struct RewriteStats {
    rewrites: usize,
    factor_calls: usize,
}

pub fn apply(script: &Script) -> Result<(Script, serde_json::Value), String> {
    let field = field_mod().ok_or("SIMPLIFIER_FIELD_MOD not set")?;
    let total = smt2::assert_commands(script).len();
    let mut changed = 0usize;
    let mut global = RewriteStats::default();

    // Selector vars whose root-product cross-multiplies another selector: for
    // those we emit only the range bound, never the disjunction (see
    // `roots_with_range`).
    let coupled = coupled_selectors(script, field);

    let out = map_asserts(script, |b: &Bool| {
        let mut stats = RewriteStats::default();
        let rewritten = rewrite_formula(b, field, &coupled, &mut stats);
        global.rewrites += stats.rewrites;
        global.factor_calls += stats.factor_calls;
        let new = match rewritten {
            Some(new) => {
                changed += 1;
                new
            }
            None => b.clone(),
        };
        Ok(new)
    })?;

    Ok((
        out,
        serde_json::json!({
            "asserts": total,
            "asserts_changed": changed,
            "rewrites": global.rewrites,
            "factor_calls": global.factor_calls,
        }),
    ))
}

fn rewrite_formula(
    term: &Bool,
    p: i128,
    coupled: &HashSet<Int>,
    stats: &mut RewriteStats,
) -> Option<Bool> {
    let mut cur: Option<Bool> = None;
    for _ in 0..MAX_REWRITE_COUNT {
        let base = cur.as_ref().unwrap_or(term);
        match rewrite_once(base, p, coupled, stats) {
            Some(next) => cur = Some(next),
            None => break,
        }
    }
    cur
}

/// Returns ``Some`` only when a rewrite occurred; ``None`` leaves ``term`` untouched.
fn rewrite_once(
    term: &Bool,
    p: i128,
    coupled: &HashSet<Int>,
    stats: &mut RewriteStats,
) -> Option<Bool> {
    if let Some(rewritten) = try_rewrite_equality(term, p, coupled, stats) {
        return Some(rewritten);
    }
    map_bool_children_opt(term, &mut |child| rewrite_once(child, p, coupled, stats))
}

fn try_rewrite_equality(
    term: &Bool,
    p: i128,
    coupled: &HashSet<Int>,
    stats: &mut RewriteStats,
) -> Option<Bool> {
    let expr = unwrap_zero_mod_eq(term, p)?;
    if total_degree(&expr) < 2 {
        return None;
    }
    let rewritten = rewrite_choice(&expr, p, coupled, stats)?;
    stats.rewrites += 1;
    Some(rewritten)
}

fn total_degree(e: &Int) -> usize {
    let dyn_ = Dynamic::from_ast(e);
    if is_int_numeral(&dyn_) {
        return 0;
    }
    match arithmetic_op(&dyn_) {
        Some(ArithOp::Add) | Some(ArithOp::Sub) => dyn_
            .children()
            .into_iter()
            .filter_map(|c| c.as_int())
            .map(|c| total_degree(&c))
            .max()
            .unwrap_or(0),
        Some(ArithOp::Neg) => dyn_
            .children()
            .into_iter()
            .next()
            .and_then(|c| c.as_int())
            .map(|c| total_degree(&c))
            .unwrap_or(0),
        Some(ArithOp::Mul) => dyn_
            .children()
            .into_iter()
            .filter_map(|c| c.as_int())
            .map(|c| total_degree(&c))
            .sum(),
        None => 1,
    }
}

fn rewrite_choice(
    expr: &Int,
    p: i128,
    coupled: &HashSet<Int>,
    stats: &mut RewriteStats,
) -> Option<Bool> {
    stats.factor_calls += 1;
    let fac = match factor(expr, p as u64) {
        Ok(f) => f,
        Err(FactorError::BuildFailed) | Err(FactorError::FactorFailed) => {
            return rewrite_quadratic(expr, p, coupled);
        }
    };

    let mut flat = Vec::new();
    for (f, exp) in fac.factors {
        for _ in 0..exp {
            flat.push(f.clone());
        }
    }

    if flat.is_empty() {
        return Some(Bool::from_bool(false));
    }
    if flat.len() >= 2 {
        if let Some((var, roots)) = solved_roots(&flat, p) {
            return Some(roots_with_range(&var, &roots, p, coupled));
        }
        let parts: Vec<Bool> = flat
            .iter()
            .map(|f| mod_zero_eq(f, p))
            .collect();
        return Some(or_terms(parts));
    }
    rewrite_quadratic(expr, p, coupled)
}

fn rewrite_quadratic(expr: &Int, p: i128, coupled: &HashSet<Int>) -> Option<Bool> {
    let (var, roots) = solved_quadratic(expr, p)?;
    if roots.is_empty() {
        return Some(Bool::from_bool(false));
    }
    Some(roots_with_range(&var, &roots, p, coupled))
}

fn mod_zero_eq(expr: &Int, p: i128) -> Bool {
    expr.modulo(int_from_i128(p)).eq(int_from_i128(0))
}

fn or_terms(mut parts: Vec<Bool>) -> Bool {
    if parts.len() == 1 {
        return parts.pop().unwrap();
    }
    Bool::or(&parts.iter().collect::<Vec<_>>())
}

fn and_terms(mut parts: Vec<Bool>) -> Bool {
    if parts.len() == 1 {
        return parts.pop().unwrap();
    }
    Bool::and(&parts.iter().collect::<Vec<_>>())
}

fn roots_with_range(var: &Int, values: &BTreeSet<i128>, p: i128, coupled: &HashSet<Int>) -> Bool {
    // `poly ≡ 0 (mod P)` with roots {rᵢ} ⟺ `(mod var P) ∈ {rᵢ}`. Wrap `var` in
    // `mod P` so the exact root equalities and the `[min,max]` range constrain
    // the field residue -- always in `[0,P)` -- rather than `var` itself, which
    // need not lie in `[0,P)` (diff vars are `a - b`, unbounded). On the raw
    // var the exact-equality + range dropped the mod-periodic solutions and, under
    // a negation, admitted spurious models (a spurious `sat` on 2099672 solver
    // soundness). On the residue it is an equivalence -- sound under any polarity
    // -- while still carrying the bound (range on the reduced value).
    let vr = var.modulo(&int_from_i128(p));
    let min_v = *values.iter().next().unwrap();
    let max_v = *values.iter().next_back().unwrap();
    let lo = int_from_i128(min_v).le(&vr);
    let hi = vr.le(&int_from_i128(max_v));
    // Structural bound-vs-factor choice: when this selector cross-multiplies
    // another selector (coupled), factoring its root-product would explode into
    // the Cartesian product of the coupled selectors' roots (e.g. the four
    // ternary `flags` in 009_rule_based -> 3^4 branches) and z3 times out. Emit
    // the interval only -- it lets z3 bound-propagate the cross-terms without
    // enumerating. Sound only for a full contiguous root range {min..max}: then
    // `min <= vr <= max` <=> `vr in {roots}` over integers in [0,P).
    let contiguous = max_v - min_v + 1 == values.len() as i128;
    if contiguous && coupled.contains(var) {
        return and_terms(vec![lo, hi]);
    }
    let disj = or_terms(values.iter().map(|v| vr.eq(&int_from_i128(*v))).collect());
    and_terms(vec![disj, lo, hi])
}

/// Selector vars whose root-product co-occurs in a product with another
/// selector. A "selector" here is a var carrying a single-variable root-product
/// `(mod P(x) P) = 0` (degree ≥ 2 in `x` alone) -- booleanity `x²-x`, ternary
/// `x(x-1)(x-2)`, etc. Coupling = two distinct selectors share a `(* ...)` term.
fn coupled_selectors(script: &Script, p: i128) -> HashSet<Int> {
    let mut selectors: HashSet<Int> = HashSet::new();
    for cmd in &script.commands {
        if let Some(b) = cmd.assert_bool() {
            collect_selectors(&b, p, &mut selectors);
        }
    }
    let mut coupled: HashSet<Int> = HashSet::new();
    if selectors.len() < 2 {
        return coupled;
    }
    for cmd in &script.commands {
        if let Some(b) = cmd.assert_bool() {
            collect_coupled(&Dynamic::from_ast(b), &selectors, &mut coupled);
        }
    }
    coupled
}

fn collect_selectors(term: &Bool, p: i128, out: &mut HashSet<Int>) {
    if let Some(expr) = unwrap_zero_mod_eq(term, p) {
        if total_degree(&expr) >= 2 {
            let syms = free_z3_symbols(&expr);
            if syms.len() == 1 {
                out.insert(syms.into_iter().next().unwrap());
            }
        }
        return;
    }
    let d = Dynamic::from_ast(term);
    if d.kind() == AstKind::App && d.decl().kind() == DeclKind::And {
        for ch in d.children() {
            if let Some(cb) = ch.as_bool() {
                collect_selectors(&cb, p, out);
            }
        }
    }
}

fn collect_coupled(d: &Dynamic, selectors: &HashSet<Int>, coupled: &mut HashSet<Int>) {
    if let (Some(ArithOp::Mul), Some(i)) = (arithmetic_op(d), d.as_int()) {
        let sels: Vec<Int> = free_z3_symbols(&i)
            .into_iter()
            .filter(|s| selectors.contains(s))
            .collect();
        if sels.len() >= 2 {
            coupled.extend(sels);
        }
    }
    for ch in d.children() {
        collect_coupled(&ch, selectors, coupled);
    }
}

fn solved_roots(factors: &[Int], p: i128) -> Option<(Int, BTreeSet<i128>)> {
    let mut var: Option<Int> = None;
    let mut values = BTreeSet::new();
    for f in factors {
        let (sym, a, b) = linear_form_z3(f, p)?;
        if a == 0 {
            if b % p == 0 {
                return None;
            }
            continue;
        }
        if var.is_none() {
            var = Some(sym);
        } else if !var.as_ref().unwrap().ast_eq(&sym) {
            return None;
        }
        values.insert((-b * mod_inv(a, p)?).rem_euclid(p));
    }
    let var = var?;
    if values.is_empty() {
        return None;
    }
    Some((var, values))
}

fn solved_quadratic(expr: &Int, p: i128) -> Option<(Int, BTreeSet<i128>)> {
    let syms = free_z3_symbols(expr);
    if syms.len() != 1 {
        return None;
    }
    let var = syms.into_iter().next().unwrap();
    let coeffs = poly_in_var_z3(expr, &var, p, 2)?;
    if coeffs.len() != 3 || coeffs[2] % p == 0 {
        return None;
    }
    let c0 = coeffs[0];
    let c1 = coeffs[1];
    let a = coeffs[2];
    let roots = quadratic_roots_mod(a, c1, c0, p);
    Some((var, roots))
}

fn quadratic_roots_mod(a: i128, b: i128, c: i128, p: i128) -> BTreeSet<i128> {
    let a = a.rem_euclid(p);
    let b = b.rem_euclid(p);
    let c = c.rem_euclid(p);
    if a == 0 {
        return BTreeSet::new();
    }
    let disc = (b * b - 4 * a * c).rem_euclid(p);
    let inv_2a = match mod_inv((2 * a).rem_euclid(p), p) {
        Some(v) => v,
        None => return BTreeSet::new(),
    };
    if disc == 0 {
        return BTreeSet::from([(-b * inv_2a).rem_euclid(p)]);
    }
    let sqrt_disc = match mod_sqrt(disc, p) {
        Some(v) => v,
        None => return BTreeSet::new(),
    };
    BTreeSet::from([
        ((-b + sqrt_disc) * inv_2a).rem_euclid(p),
        ((-b - sqrt_disc) * inv_2a).rem_euclid(p),
    ])
}

fn mod_sqrt(n: i128, p: i128) -> Option<i128> {
    let n = n.rem_euclid(p);
    if n == 0 {
        return Some(0);
    }
    if mod_pow(n, (p - 1) / 2, p) != 1 {
        return None;
    }
    if p % 4 == 3 {
        return Some(mod_pow(n, (p + 1) / 4, p));
    }
    let mut q = p - 1;
    let mut s = 0i128;
    while q % 2 == 0 {
        q /= 2;
        s += 1;
    }
    let mut z = 2i128;
    while mod_pow(z, (p - 1) / 2, p) != p - 1 {
        z += 1;
    }
    let mut m = s;
    let mut c = mod_pow(z, q, p);
    let mut t = mod_pow(n, q, p);
    let mut r = mod_pow(n, (q + 1) / 2, p);
    while t != 1 {
        let mut i = 1i128;
        let mut t2 = (t * t) % p;
        while t2 != 1 {
            t2 = (t2 * t2) % p;
            i += 1;
            if i == m {
                return None;
            }
        }
        let b = mod_pow(c, 1 << (m - i - 1), p);
        m = i;
        c = (b * b) % p;
        t = (t * c) % p;
        r = (r * b) % p;
    }
    Some(r)
}

fn mod_pow(mut base: i128, mut exp: i128, p: i128) -> i128 {
    let mut result = 1i128;
    base %= p;
    while exp > 0 {
        if exp % 2 == 1 {
            result = (result * base) % p;
        }
        exp /= 2;
        base = (base * base) % p;
    }
    result
}

fn mod_inv(a: i128, p: i128) -> Option<i128> {
    let mut t = 0i128;
    let mut newt = 1i128;
    let mut r = p;
    let mut newr = a.rem_euclid(p);
    while newr != 0 {
        let quotient = r / newr;
        (t, newt) = (newt, t - quotient * newt);
        (r, newr) = (newr, r - quotient * newr);
    }
    if r != 1 {
        return None;
    }
    Some(if t < 0 { t + p } else { t })
}

fn linear_form_z3(e: &Int, p: i128) -> Option<(Int, i128, i128)> {
    let mut terms: HashMap<Int, i128> = HashMap::new();
    let mut const_ = 0i128;
    if !linear_add(1, e, p, &mut terms, &mut const_) {
        return None;
    }
    terms.retain(|_, v| *v % p != 0);
    if terms.len() > 1 {
        return None;
    }
    if terms.is_empty() {
        return Some((int_from_i128(0), 0, const_));
    }
    let (sym, a) = terms.into_iter().next().unwrap();
    Some((sym, a.rem_euclid(p), const_.rem_euclid(p)))
}

fn linear_add(
    c: i128,
    e: &Int,
    p: i128,
    terms: &mut HashMap<Int, i128>,
    const_: &mut i128,
) -> bool {
    let dyn_ = Dynamic::from_ast(e);
    if is_int_numeral(&dyn_) {
        *const_ += c * int_value(e).unwrap_or(0);
        return true;
    }
    if is_int_var(&dyn_) {
        *terms.entry(e.clone()).or_insert(0) += c;
        return true;
    }
    if let Some(op) = arithmetic_op(&dyn_) {
        return match op {
            ArithOp::Add => dyn_
                .children()
                .into_iter()
                .all(|ch| linear_add(c, &ch.as_int().unwrap(), p, terms, const_)),
            ArithOp::Neg => {
                let ch = dyn_.children().into_iter().next().unwrap();
                linear_add(-c, &ch.as_int().unwrap(), p, terms, const_)
            }
            ArithOp::Sub => {
                let kids = dyn_.children();
                linear_add(c, &kids[0].as_int().unwrap(), p, terms, const_)
                    && linear_add(-c, &kids[1].as_int().unwrap(), p, terms, const_)
            }
            ArithOp::Mul => {
                let kids = dyn_.children();
                let mut coeff = 1i128;
                let mut rest: Option<Int> = None;
                for ch in kids {
                    let ch_int = ch.as_int().unwrap();
                    if is_int_numeral(&Dynamic::from_ast(&ch_int)) {
                        coeff = (coeff * int_value(&ch_int).unwrap_or(0)).rem_euclid(p);
                    } else if rest.is_none() {
                        rest = Some(ch_int);
                    } else {
                        return false;
                    }
                }
                if let Some(r) = rest {
                    linear_add(c * coeff, &r, p, terms, const_)
                } else {
                    *const_ = (*const_ + c * coeff).rem_euclid(p);
                    true
                }
            }
        };
    }
    false
}

fn poly_in_var_z3(e: &Int, var: &Int, p: i128, max_deg: usize) -> Option<Vec<i128>> {
    let dyn_ = Dynamic::from_ast(e);
    if is_int_numeral(&dyn_) {
        return Some(vec![int_value(e).unwrap_or(0).rem_euclid(p)]);
    }
    if is_int_var(&dyn_) {
        return if e.ast_eq(var) {
            Some(vec![0, 1])
        } else {
            None
        };
    }
    if let Some(op) = arithmetic_op(&dyn_) {
        return match op {
            ArithOp::Add => {
                let mut acc = vec![0];
                for ch in dyn_.children() {
                    let pa = poly_in_var_z3(&ch.as_int().unwrap(), var, p, max_deg)?;
                    acc = poly_add(acc, pa, p);
                }
                Some(acc)
            }
            ArithOp::Neg => {
                let ch = dyn_.children().into_iter().next().unwrap();
                poly_in_var_z3(&ch.as_int().unwrap(), var, p, max_deg)
                    .map(|pa| pa.into_iter().map(|c| (-c).rem_euclid(p)).collect())
            }
            ArithOp::Sub => {
                let kids = dyn_.children();
                let pa = poly_in_var_z3(&kids[0].as_int().unwrap(), var, p, max_deg)?;
                let pb = poly_in_var_z3(&kids[1].as_int().unwrap(), var, p, max_deg)?;
                Some(poly_add(
                    pa,
                    pb.into_iter().map(|c| (-c).rem_euclid(p)).collect(),
                    p,
                ))
            }
            ArithOp::Mul => {
                let mut acc = vec![1];
                for ch in dyn_.children() {
                    let pa = poly_in_var_z3(&ch.as_int().unwrap(), var, p, max_deg)?;
                    acc = poly_mul(acc, pa, p, max_deg)?;
                }
                Some(acc)
            }
        };
    }
    None
}

fn poly_add(mut a: Vec<i128>, b: Vec<i128>, p: i128) -> Vec<i128> {
    if a.len() < b.len() {
        a.resize(b.len(), 0);
    }
    for (i, c) in b.into_iter().enumerate() {
        a[i] = (a[i] + c).rem_euclid(p);
    }
    while a.len() > 1 && a.last().copied() == Some(0) {
        a.pop();
    }
    a
}

fn poly_mul(a: Vec<i128>, b: Vec<i128>, p: i128, max_deg: usize) -> Option<Vec<i128>> {
    if a.is_empty() || b.is_empty() {
        return Some(vec![0]);
    }
    let deg = a.len() + b.len() - 2;
    if deg > max_deg {
        return None;
    }
    let mut out = vec![0i128; deg + 1];
    for (i, ca) in a.iter().enumerate() {
        for (j, cb) in b.iter().enumerate() {
            out[i + j] = (out[i + j] + ca * cb).rem_euclid(p);
        }
    }
    while out.len() > 1 && out.last().copied() == Some(0) {
        out.pop();
    }
    Some(out)
}

fn free_z3_symbols(e: &Int) -> HashSet<Int> {
    let mut out = HashSet::new();
    collect_z3_symbols(e, &mut out);
    out
}

fn collect_z3_symbols(e: &Int, out: &mut HashSet<Int>) {
    let dyn_ = Dynamic::from_ast(e);
    if is_int_var(&dyn_) {
        out.insert(e.clone());
        return;
    }
    if arithmetic_op(&dyn_).is_some() {
        for ch in dyn_.children() {
            if let Some(ch_int) = ch.as_int() {
                collect_z3_symbols(&ch_int, out);
            }
        }
    }
}

enum ArithOp {
    Add,
    Mul,
    Neg,
    Sub,
}

fn arithmetic_op(ast: &Dynamic) -> Option<ArithOp> {
    if ast.kind() != AstKind::App {
        return None;
    }
    let decl = ast.decl();
    if decl.arity() == 0 {
        return None;
    }
    match decl.kind() {
        DeclKind::Add => Some(ArithOp::Add),
        DeclKind::Mul => Some(ArithOp::Mul),
        DeclKind::Uminus => Some(ArithOp::Neg),
        DeclKind::Sub => Some(ArithOp::Sub),
        _ => None,
    }
}
fn is_int_var(ast: &Dynamic) -> bool {
    ast.kind() == AstKind::App
        && ast.is_const()
        && ast.get_sort().kind() == SortKind::Int
        && !is_int_numeral(ast)
}

#[cfg(test)]
mod tests {
    use super::*;
    use smt2::Script;

    fn field() -> i128 {
        2_013_265_921
    }

    fn with_field(f: impl FnOnce()) {
        let _field_env = crate::field_env_guard();
        std::env::set_var("SIMPLIFIER_FIELD_MOD", field().to_string());
        f();
    }

    fn rewrite_assert(body: &str) -> Bool {
        let script = Script::parse(&format!("(assert {body})\n(check-sat)\n")).unwrap();
        let term = script.commands[0].assert_bool().unwrap().clone();
        let coupled = coupled_selectors(&script, field());
        let mut stats = RewriteStats::default();
        rewrite_formula(&term, field(), &coupled, &mut stats).unwrap_or(term)
    }

    #[test]
    fn coupled_selector_drops_disjunction() {
        with_field(|| {
            let p = field();
            let m1 = p - 1;
            // Two boolean selectors x, y that cross-multiply (x*y => coupled).
            // Rewriting x^2 - x = 0 must yield just the [0,1] bound, no disjunction.
            let script = Script::parse(&format!(
                "(declare-fun x () Int)\n(declare-fun y () Int)\n\
                 (assert (= (mod (+ (* x x) (* {m1} x)) {p}) 0))\n\
                 (assert (= (mod (+ (* y y) (* {m1} y)) {p}) 0))\n\
                 (assert (= (mod (* x y) {p}) 0))\n(check-sat)\n"
            ))
            .unwrap();
            let coupled = coupled_selectors(&script, p);
            assert_eq!(coupled.len(), 2, "x and y should be coupled");
            let target = script.commands[2].assert_bool().unwrap().clone();
            let mut stats = RewriteStats::default();
            let out = rewrite_formula(&target, p, &coupled, &mut stats).unwrap_or(target);
            let s = out.to_string();
            assert!(!s.contains("or"), "coupled selector must be bound-only, no disjunction: {s}");
            assert!(s.contains("<="), "must still carry the interval bound: {s}");
        });
    }

    #[test]
    fn uncoupled_selector_keeps_disjunction() {
        with_field(|| {
            let p = field();
            // Isolated ternary selector (no cross-product): keep disjunction+range.
            let out = rewrite_assert(&format!(
                "(= (mod (* (* x (+ x {m1})) (+ x {m2})) {p}) 0)",
                m1 = p - 1,
                m2 = p - 2
            ));
            let s = out.to_string();
            assert!(s.contains("or"), "uncoupled selector should keep the disjunction: {s}");
        });
    }

    #[test]
    fn splits_non_atomic_product() {
        with_field(|| {
            let p = field();
            let out = rewrite_assert(&format!(
                "(= (mod (* (+ x 1) (+ x 2)) {p}) 0)"
            ));
            let s = out.to_string();
            // Roots on the field residue `(mod x P)`: disjunction + range, all
            // over the reduced value (sound for vars not in [0,P)).
            assert!(s.contains("or"), "{s}");
            assert!(s.contains("mod"), "roots must be on the residue (mod x P): {s}");
            assert!(s.contains("<="), "should still carry the range bound: {s}");
        });
    }

    #[test]
    fn keeps_multivar_as_congruences() {
        with_field(|| {
            let p = field();
            let out = rewrite_assert(&format!("(= (mod (* mx my) {p}) 0)"));
            let s = out.to_string();
            assert!(s.starts_with("(or"), "{s}");
        });
    }

    #[test]
    fn solves_quadratic_sum_form() {
        with_field(|| {
            let p = field();
            let out = rewrite_assert(&format!(
                "(= (mod (+ (+ (* x x) (* 3 x)) 2) {p}) 0)"
            ));
            let s = out.to_string();
            // x^2+3x+2 = (x+1)(x+2): roots on the residue `(mod x P)`.
            assert!(s.contains("or"), "{s}");
            assert!(s.contains("mod"), "roots must be on the residue (mod x P): {s}");
            assert!(s.contains("<="), "should still carry the range bound: {s}");
        });
    }

    #[test]
    fn apply_pass_counts_changes() {
        with_field(|| {
            let p = field();
            let script = Script::parse(&format!(
                "(declare-fun x () Int)\n(assert (= (mod (* (+ x 1) (+ x 2)) {p}) 0))\n(check-sat)\n"
            ))
            .unwrap();
            let (out, stats) = apply(&script).unwrap();
            assert_eq!(stats["asserts_changed"], 1);
            let s = smt2::dump_string(&out);
            assert!(s.contains("or"), "{s}");
        });
    }
}
