//! Demodulation / mod rewrites on Z3 AST.

use std::collections::HashMap;

use smt2::ast_util::{int_from_i128, int_value_dyn, rebuild_app};
use smt2::{assert_commands, is_int_const, map_asserts, Script};
use z3::ast::{Ast, AstKind, Bool, Dynamic, Int};
use z3::DeclKind;

#[derive(Default)]
struct DemodStats {
    eqmod_asserts_changed: usize,
    const_eval: usize,
    into_ite: usize,
    elim_by_range: usize,
}

pub fn field_mod() -> Option<i128> {
    std::env::var("SIMPLIFIER_FIELD_MOD")
        .ok()
        .and_then(|s| s.parse().ok())
}

pub fn apply(script: &Script) -> Result<(Script, serde_json::Value), String> {
    let field_mod = field_mod();
    let total = assert_commands(script).len();
    let mut changed = 0usize;
    let mut stats = DemodStats::default();
    let out = map_asserts(script, |b| match rewrite_bool(b, field_mod, &mut stats) {
        Some(next) => {
            changed += 1;
            Ok(next)
        }
        None => Ok(b.clone()),
    })?;
    let stats_json = serde_json::json!({
        "asserts_total": total,
        "asserts_changed": changed,
        "range_symbols": 0,
        "protected_range_constraints": 0,
        "eqmod_asserts_changed": stats.eqmod_asserts_changed,
        "const_eval": stats.const_eval,
        "into_ite": stats.into_ite,
        "elim_by_range": stats.elim_by_range,
    });
    Ok((out, stats_json))
}

/// Returns ``Some`` only when a rewrite changed the term; ``None`` leaves it
/// untouched so the original AST node is reused (no rebuild/hashconsing).
fn rewrite_bool(b: &Bool, field_mod: Option<i128>, stats: &mut DemodStats) -> Option<Bool> {
    let d = Dynamic::from_ast(b);
    if d.kind() == AstKind::Quantifier {
        return None;
    }
    if d.kind() == AstKind::App && d.num_children() == 2 && d.decl().kind() == DeclKind::Eq {
        let lhs = d.nth_child(0).and_then(|c| c.as_int());
        let rhs = d.nth_child(1).and_then(|c| c.as_int());
        if let (Some(lhs), Some(rhs)) = (lhs, rhs) {
            if let Some(eq) = demod_rewrite_eqmod_zero_equals(&lhs, &rhs, field_mod) {
                stats.eqmod_asserts_changed += 1;
                return Some(eq);
            }
        }
    }
    if d.kind() != AstKind::App {
        return None;
    }
    let (args, any) = rewrite_children(&d, field_mod, stats, true);
    if !any {
        return None;
    }
    let refs: Vec<&dyn Ast> = args.iter().map(|a| a as &dyn Ast).collect();
    rebuild_app(&d.decl(), &refs).as_bool()
}

fn rewrite_dynamic(ast: &Dynamic, field_mod: Option<i128>, stats: &mut DemodStats) -> Option<Dynamic> {
    if ast.kind() == AstKind::Quantifier {
        return None;
    }
    if let Some(i) = ast.as_int() {
        return rewrite_int(&i, field_mod, stats).map(|x| Dynamic::from_ast(&x));
    }
    if ast.kind() != AstKind::App {
        return None;
    }
    let (args, any) = rewrite_children(ast, field_mod, stats, false);
    if !any {
        return None;
    }
    let refs: Vec<&dyn Ast> = args.iter().map(|a| a as &dyn Ast).collect();
    Some(rebuild_app(&ast.decl(), &refs))
}

/// Rewrite all children, returning them (originals reused where unchanged) and
/// whether any child changed. When ``bool_aware``, Bool children recurse through
/// [`rewrite_bool`].
fn rewrite_children(
    d: &Dynamic,
    field_mod: Option<i128>,
    stats: &mut DemodStats,
    bool_aware: bool,
) -> (Vec<Dynamic>, bool) {
    let n = d.num_children();
    // Defer allocation until the first change: unchanged nodes (the common case)
    // pay no Vec allocation and no child clones.
    let mut args: Vec<Dynamic> = Vec::new();
    for i in 0..n {
        let Some(ch) = d.nth_child(i) else { continue };
        let rewritten = if bool_aware {
            if let Some(cb) = ch.as_bool() {
                rewrite_bool(&cb, field_mod, stats).map(|x| Dynamic::from_ast(&x))
            } else {
                rewrite_dynamic(&ch, field_mod, stats)
            }
        } else {
            rewrite_dynamic(&ch, field_mod, stats)
        };
        match rewritten {
            Some(x) => {
                if args.is_empty() {
                    args.reserve(n);
                    for j in 0..i {
                        if let Some(orig) = d.nth_child(j) {
                            args.push(orig);
                        }
                    }
                }
                args.push(x);
            }
            None if !args.is_empty() => args.push(ch),
            None => {}
        }
    }
    let any = !args.is_empty();
    (args, any)
}

fn rewrite_int(e: &Int, field_mod: Option<i128>, stats: &mut DemodStats) -> Option<Int> {
    let d = Dynamic::from_ast(e);
    if d.kind() != AstKind::App {
        return None;
    }
    if d.decl().kind() == DeclKind::Mod && d.num_children() == 2 {
        let c0 = d.nth_child(0).and_then(|c| c.as_int());
        let c1 = d.nth_child(1).and_then(|c| c.as_int());
        let expr_r = c0.as_ref().and_then(|i| rewrite_int(i, field_mod, stats));
        let modulus_r = c1.as_ref().and_then(|i| rewrite_int(i, field_mod, stats));
        let expr = expr_r
            .clone()
            .or_else(|| c0.clone())
            .unwrap_or_else(|| e.clone());
        let modulus = modulus_r
            .clone()
            .or_else(|| c1.clone())
            .unwrap_or_else(|| int_from_i128(1));
        if let Some(m) = int_lit(&Dynamic::from_ast(&modulus)) {
            if m > 0 {
                if let Some(v) = int_lit(&Dynamic::from_ast(&expr)) {
                    stats.const_eval += 1;
                    return Some(int_from_i128(v.rem_euclid(m)));
                }
                let ed = Dynamic::from_ast(&expr);
                if ed.kind() == AstKind::App && ed.num_children() == 3 && ed.decl().kind() == DeclKind::Ite {
                    let c = ed.nth_child(0).and_then(|x| x.as_bool());
                    let t = ed.nth_child(1).and_then(|x| x.as_int());
                    let f = ed.nth_child(2).and_then(|x| x.as_int());
                    if let (Some(c), Some(t), Some(f)) = (c, t, f) {
                        stats.into_ite += 1;
                        return Some(c.ite(&t.modulo(&modulus), &f.modulo(&modulus)));
                    }
                }
            }
        }
        if expr_r.is_none() && modulus_r.is_none() {
            return None;
        }
        return Some(expr.modulo(&modulus));
    }
    let (args, any) = rewrite_children(&d, field_mod, stats, false);
    if !any {
        return None;
    }
    let refs: Vec<&dyn Ast> = args.iter().map(|a| a as &dyn Ast).collect();
    rebuild_app(&d.decl(), &refs).as_int()
}

fn int_lit(ast: &Dynamic) -> Option<i128> {
    if let Some(v) = int_value_dyn(ast) {
        return Some(v);
    }
    if ast.kind() == AstKind::App && ast.num_children() == 1 && ast.decl().kind() == DeclKind::Uminus {
        return ast.nth_child(0).and_then(|c| int_value_dyn(&c)).map(|v| -v);
    }
    None
}

fn mod_parts_int(t: &Int) -> Option<(Int, i128)> {
    let d = Dynamic::from_ast(t);
    if d.kind() != AstKind::App || d.num_children() != 2 || d.decl().kind() != DeclKind::Mod {
        return None;
    }
    let expr = d.nth_child(0)?.as_int()?;
    let modulus = int_lit(&d.nth_child(1)?)?;
    Some((expr, modulus))
}

fn demod_rewrite_eqmod_zero_equals(lhs: &Int, rhs: &Int, field_mod: Option<i128>) -> Option<Bool> {
    let (expr, modulus) = mod_parts_int(lhs)?;
    if int_lit(&Dynamic::from_ast(rhs)) != Some(0) {
        return None;
    }
    if let Some(p) = field_mod {
        if modulus != p {
            return None;
        }
    }
    let p = modulus;
    if p <= 0 {
        return None;
    }
    let (mut terms, const_) = linear_form(&expr)?;
    terms.retain(|_, a| {
        let r = a.rem_euclid(p);
        *a = r;
        r != 0
    });
    if terms.len() != 1 {
        return None;
    }
    let (var, a) = terms.into_iter().next()?;
    if a == 0 {
        return None;
    }
    let inv = mod_inverse(a, p)?;
    let val = (-const_ * inv).rem_euclid(p);
    Some(var.eq(int_from_i128(val)))
}

fn linear_form(e: &Int) -> Option<(HashMap<Int, i128>, i128)> {
    let mut terms = HashMap::new();
    let mut const_ = 0i128;
    if linear_add(1, e, &mut terms, &mut const_) {
        Some((terms, const_))
    } else {
        None
    }
}

fn linear_add(c: i128, e: &Int, terms: &mut HashMap<Int, i128>, const_: &mut i128) -> bool {
    let d = Dynamic::from_ast(e);
    if let Some(v) = int_lit(&d) {
        *const_ += c * v;
        return true;
    }
    if is_int_const(&d) {
        if let Some(var) = d.as_int() {
            *terms.entry(var).or_insert(0) += c;
            return true;
        }
    }
    if d.kind() != AstKind::App {
        return false;
    }
    match d.decl().kind() {
        DeclKind::Add => d
            .children()
            .into_iter()
            .all(|ch| ch.as_int().map(|i| linear_add(c, &i, terms, const_)).unwrap_or(false)),
        DeclKind::Uminus if d.num_children() == 1 => d
            .nth_child(0)
            .and_then(|ch| ch.as_int())
            .map(|i| linear_add(-c, &i, terms, const_))
            .unwrap_or(false),
        DeclKind::Sub if d.num_children() == 2 => {
            let a = d.nth_child(0).and_then(|ch| ch.as_int());
            let b = d.nth_child(1).and_then(|ch| ch.as_int());
            match (a, b) {
                (Some(a), Some(b)) => {
                    linear_add(c, &a, terms, const_) && linear_add(-c, &b, terms, const_)
                }
                _ => false,
            }
        }
        DeclKind::Mul => {
            let mut k = 1i128;
            let mut rest: Option<Int> = None;
            for ch in d.children() {
                if let Some(v) = int_lit(&ch) {
                    k *= v;
                    continue;
                }
                if let Some(i) = ch.as_int() {
                    if rest.is_some() {
                        return false;
                    }
                    rest = Some(i);
                } else {
                    return false;
                }
            }
            if let Some(r) = rest {
                linear_add(c * k, &r, terms, const_)
            } else {
                *const_ += c * k;
                true
            }
        }
        _ => false,
    }
}

fn mod_inverse(a: i128, m: i128) -> Option<i128> {
    let (mut t, mut newt) = (0i128, 1i128);
    let (mut r, mut newr) = (m, a.rem_euclid(m));
    while newr != 0 {
        let q = r / newr;
        (t, newt) = (newt, t - q * newt);
        (r, newr) = (newr, r - q * newr);
    }
    if r != 1 {
        return None;
    }
    Some(t.rem_euclid(m))
}
