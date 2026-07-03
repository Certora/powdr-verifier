//! Equality rewrites for modular products via FLINT polynomial factorization.

use std::collections::{BTreeSet, HashMap};

use smt2::{int_from_i128, int_value, is_int_numeral, map_asserts, map_bool_children_opt, unwrap_zero_mod_eq, Script};
use z3::ast::{Ast, AstKind, Dynamic, Int};
use z3::ast::Bool;
use z3::{FuncDecl, SortKind};

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

    let out = map_asserts(script, |b: &Bool| {
        let mut stats = RewriteStats::default();
        let rewritten = rewrite_formula(b, field, &mut stats);
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

fn rewrite_formula(term: &Bool, p: i128, stats: &mut RewriteStats) -> Option<Bool> {
    let mut cur: Option<Bool> = None;
    for _ in 0..MAX_REWRITE_COUNT {
        let base = cur.as_ref().unwrap_or(term);
        match rewrite_once(base, p, stats) {
            Some(next) => cur = Some(next),
            None => break,
        }
    }
    cur
}

/// Returns ``Some`` only when a rewrite occurred; ``None`` leaves ``term`` untouched.
fn rewrite_once(term: &Bool, p: i128, stats: &mut RewriteStats) -> Option<Bool> {
    if let Some(rewritten) = try_rewrite_equality(term, p, stats) {
        return Some(rewritten);
    }
    map_bool_children_opt(term, &mut |child| rewrite_once(child, p, stats))
}

fn try_rewrite_equality(term: &Bool, p: i128, stats: &mut RewriteStats) -> Option<Bool> {
    let expr = unwrap_zero_mod_eq(term, p)?;
    if total_degree(&expr) < 2 {
        return None;
    }
    let rewritten = rewrite_choice(&expr, p, stats)?;
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

fn rewrite_choice(expr: &Int, p: i128, stats: &mut RewriteStats) -> Option<Bool> {
    stats.factor_calls += 1;
    let fac = match factor(expr) {
        Ok(f) => f,
        Err(FactorError::BuildFailed) | Err(FactorError::FactorFailed) => {
            return rewrite_quadratic(expr, p);
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
            return Some(roots_with_range(&var, &roots, p));
        }
        let parts: Vec<Bool> = flat
            .iter()
            .map(|f| mod_zero_eq(f, p))
            .collect();
        return Some(or_terms(parts));
    }
    rewrite_quadratic(expr, p)
}

fn rewrite_quadratic(expr: &Int, p: i128) -> Option<Bool> {
    let (var, roots) = solved_quadratic(expr, p)?;
    if roots.is_empty() {
        return Some(Bool::from_bool(false));
    }
    Some(roots_with_range(&var, &roots, p))
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

fn roots_with_range(var: &str, values: &BTreeSet<i128>, _p: i128) -> Bool {
    let min_v = *values.iter().next().unwrap();
    let max_v = *values.iter().next_back().unwrap();
    let sym = Int::new_const(var);
    let disj = or_terms(
        values
            .iter()
            .map(|v| sym.eq(int_from_i128(*v)))
            .collect(),
    );
    and_terms(vec![
        disj,
        int_from_i128(min_v).le(&sym),
        sym.le(&int_from_i128(max_v)),
    ])
}

fn solved_roots(factors: &[Int], p: i128) -> Option<(String, BTreeSet<i128>)> {
    let mut var: Option<String> = None;
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
        } else if var.as_ref() != Some(&sym) {
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

fn solved_quadratic(expr: &Int, p: i128) -> Option<(String, BTreeSet<i128>)> {
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

fn linear_form_z3(e: &Int, p: i128) -> Option<(String, i128, i128)> {
    let mut terms: HashMap<String, i128> = HashMap::new();
    let mut const_ = 0i128;
    if !linear_add(1, e, p, &mut terms, &mut const_) {
        return None;
    }
    terms.retain(|_, v| *v % p != 0);
    if terms.len() > 1 {
        return None;
    }
    if terms.is_empty() {
        return Some((String::new(), 0, const_));
    }
    let (sym, a) = terms.into_iter().next().unwrap();
    Some((sym, a.rem_euclid(p), const_.rem_euclid(p)))
}

fn linear_add(
    c: i128,
    e: &Int,
    p: i128,
    terms: &mut HashMap<String, i128>,
    const_: &mut i128,
) -> bool {
    let dyn_ = Dynamic::from_ast(e);
    if is_int_numeral(&dyn_) {
        *const_ += c * int_value(e).unwrap_or(0);
        return true;
    }
    if is_int_var(&dyn_) {
        let name = z3_symbol_name(e);
        *terms.entry(name).or_insert(0) += c;
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

fn poly_in_var_z3(e: &Int, var: &str, p: i128, max_deg: usize) -> Option<Vec<i128>> {
    let dyn_ = Dynamic::from_ast(e);
    if is_int_numeral(&dyn_) {
        return Some(vec![int_value(e).unwrap_or(0).rem_euclid(p)]);
    }
    if is_int_var(&dyn_) {
        return if z3_symbol_name(e) == var {
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

fn free_z3_symbols(e: &Int) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    collect_z3_symbols(e, &mut out);
    out
}

fn collect_z3_symbols(e: &Int, out: &mut BTreeSet<String>) {
    let dyn_ = Dynamic::from_ast(e);
    if is_int_var(&dyn_) {
        out.insert(z3_symbol_name(e));
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
    match decl_name(&decl).as_str() {
        "+" => Some(ArithOp::Add),
        "*" => Some(ArithOp::Mul),
        "-" if decl.arity() == 1 => Some(ArithOp::Neg),
        "-" if decl.arity() == 2 => Some(ArithOp::Sub),
        _ => None,
    }
}

fn decl_name(decl: &FuncDecl) -> String {
    decl.name().as_str().to_string()
}

fn is_int_var(ast: &Dynamic) -> bool {
    ast.kind() == AstKind::App
        && ast.is_const()
        && ast.get_sort().kind() == SortKind::Int
        && !is_int_numeral(ast)
}

fn z3_symbol_name(e: &Int) -> String {
    Dynamic::from_ast(e).decl().name().as_str().to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use smt2::Script;

    fn field() -> i128 {
        2_013_265_921
    }

    fn with_field(f: impl FnOnce()) {
        std::env::set_var("SIMPLIFIER_FIELD_MOD", field().to_string());
        f();
    }

    fn rewrite_assert(body: &str) -> Bool {
        let script = Script::parse(&format!("(assert {body})\n(check-sat)\n")).unwrap();
        let term = script.commands[0].assert_bool().unwrap().clone();
        let mut stats = RewriteStats::default();
        rewrite_formula(&term, field(), &mut stats).unwrap_or(term)
    }

    #[test]
    fn splits_non_atomic_product() {
        with_field(|| {
            let p = field();
            let out = rewrite_assert(&format!(
                "(= (mod (* (+ x 1) (+ x 2)) {p}) 0)"
            ));
            let s = out.to_string();
            assert!(s.contains("or"), "{s}");
            assert!(s.contains("and"), "{s}");
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
            assert!(s.contains("or"), "{s}");
            assert!(s.contains("and"), "{s}");
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
