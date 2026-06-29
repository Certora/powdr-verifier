//! Demodulation / mod rewrites on Z3 AST.

use std::collections::HashMap;

use smt2::ast_util::{decl_name, int_from_i128, int_value_dyn, rebuild_app};
use smt2::{assert_commands, map_asserts, Script};
use z3::ast::{Ast, AstKind, Bool, Dynamic, Int};

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
    let out = map_asserts(script, |b| {
        let next = rewrite_bool(b, field_mod, &mut stats);
        if next.to_string() != b.to_string() {
            changed += 1;
        }
        Ok(next)
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

fn rewrite_bool(b: &Bool, field_mod: Option<i128>, stats: &mut DemodStats) -> Bool {
    let d = Dynamic::from_ast(b);
    if d.kind() == AstKind::Quantifier {
        return b.clone();
    }
    if d.kind() == AstKind::App && decl_name(&d.decl()) == "=" && d.num_children() == 2 {
        let lhs = d.nth_child(0).and_then(|c| c.as_int());
        let rhs = d.nth_child(1).and_then(|c| c.as_int());
        if let (Some(lhs), Some(rhs)) = (lhs, rhs) {
            if let Some(eq) = demod_rewrite_eqmod_zero_equals(&lhs, &rhs, field_mod) {
                stats.eqmod_asserts_changed += 1;
                return eq;
            }
        }
    }
    rewrite_dynamic(&d, field_mod, stats)
        .as_bool()
        .unwrap_or_else(|| b.clone())
}

fn rewrite_dynamic(ast: &Dynamic, field_mod: Option<i128>, stats: &mut DemodStats) -> Dynamic {
    if let Some(b) = ast.as_bool() {
        return Dynamic::from_ast(&rewrite_bool(&b, field_mod, stats));
    }
    if ast.kind() == AstKind::Quantifier {
        return ast.clone();
    }
    if let Some(i) = ast.as_int() {
        return Dynamic::from_ast(&rewrite_int(&i, field_mod, stats));
    }
    if ast.kind() != AstKind::App {
        return ast.clone();
    }
    let args: Vec<Dynamic> = ast
        .children()
        .into_iter()
        .map(|ch| rewrite_dynamic(&ch, field_mod, stats))
        .collect();
    let refs: Vec<&dyn Ast> = args.iter().map(|a| a as &dyn Ast).collect();
    rebuild_app(&ast.decl(), &refs)
}

fn rewrite_int(e: &Int, field_mod: Option<i128>, stats: &mut DemodStats) -> Int {
    let d = Dynamic::from_ast(e);
    if d.kind() != AstKind::App {
        return e.clone();
    }
    let op = decl_name(&d.decl());
    if op == "mod" && d.num_children() == 2 {
        let expr = d
            .nth_child(0)
            .and_then(|c| c.as_int())
            .map(|i| rewrite_int(&i, field_mod, stats))
            .unwrap_or_else(|| e.clone());
        let modulus = d
            .nth_child(1)
            .and_then(|c| c.as_int())
            .map(|i| rewrite_int(&i, field_mod, stats))
            .unwrap_or_else(|| int_from_i128(1));
        if let Some(m) = int_lit(&Dynamic::from_ast(&modulus)) {
            if m > 0 {
                if let Some(v) = int_lit(&Dynamic::from_ast(&expr)) {
                    stats.const_eval += 1;
                    return int_from_i128(v.rem_euclid(m));
                }
                let ed = Dynamic::from_ast(&expr);
                if ed.kind() == AstKind::App && decl_name(&ed.decl()) == "ite" && ed.num_children() == 3 {
                    let c = ed.nth_child(0).and_then(|x| x.as_bool());
                    let t = ed.nth_child(1).and_then(|x| x.as_int());
                    let f = ed.nth_child(2).and_then(|x| x.as_int());
                    if let (Some(c), Some(t), Some(f)) = (c, t, f) {
                        stats.into_ite += 1;
                        return c.ite(&t.modulo(&modulus), &f.modulo(&modulus));
                    }
                }
            }
        }
        return expr.modulo(&modulus);
    }
    let args: Vec<Dynamic> = d
        .children()
        .into_iter()
        .map(|ch| rewrite_dynamic(&ch, field_mod, stats))
        .collect();
    let refs: Vec<&dyn Ast> = args.iter().map(|a| a as &dyn Ast).collect();
    rebuild_app(&d.decl(), &refs).as_int().unwrap_or_else(|| e.clone())
}

fn int_lit(ast: &Dynamic) -> Option<i128> {
    if let Some(v) = int_value_dyn(ast) {
        return Some(v);
    }
    if ast.kind() == AstKind::App && decl_name(&ast.decl()) == "-" && ast.num_children() == 1 {
        return ast.nth_child(0).and_then(|c| int_value_dyn(&c)).map(|v| -v);
    }
    None
}

fn is_symbol_int(ast: &Dynamic) -> Option<String> {
    if ast.kind() == AstKind::App && ast.is_const() && ast.as_int().is_some() {
        let name = decl_name(&ast.decl());
        if name != "true" && name != "false" {
            return Some(name);
        }
    }
    None
}

fn mod_parts_int(t: &Int) -> Option<(Int, i128)> {
    let d = Dynamic::from_ast(t);
    if d.kind() != AstKind::App || decl_name(&d.decl()) != "mod" || d.num_children() != 2 {
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
    let (sym, a) = terms.into_iter().next()?;
    if a == 0 {
        return None;
    }
    let inv = mod_inverse(a, p)?;
    let val = (-const_ * inv).rem_euclid(p);
    Some(Int::new_const(sym.as_str()).eq(int_from_i128(val)))
}

fn linear_form(e: &Int) -> Option<(HashMap<String, i128>, i128)> {
    let mut terms = HashMap::new();
    let mut const_ = 0i128;
    if linear_add(1, e, &mut terms, &mut const_) {
        Some((terms, const_))
    } else {
        None
    }
}

fn linear_add(c: i128, e: &Int, terms: &mut HashMap<String, i128>, const_: &mut i128) -> bool {
    let d = Dynamic::from_ast(e);
    if let Some(v) = int_lit(&d) {
        *const_ += c * v;
        return true;
    }
    if let Some(name) = is_symbol_int(&d) {
        *terms.entry(name).or_insert(0) += c;
        return true;
    }
    if d.kind() != AstKind::App {
        return false;
    }
    let head = decl_name(&d.decl());
    match head.as_str() {
        "+" => d
            .children()
            .into_iter()
            .all(|ch| ch.as_int().map(|i| linear_add(c, &i, terms, const_)).unwrap_or(false)),
        "-" if d.num_children() == 1 => d
            .nth_child(0)
            .and_then(|ch| ch.as_int())
            .map(|i| linear_add(-c, &i, terms, const_))
            .unwrap_or(false),
        "-" if d.num_children() == 2 => {
            let a = d.nth_child(0).and_then(|ch| ch.as_int());
            let b = d.nth_child(1).and_then(|ch| ch.as_int());
            match (a, b) {
                (Some(a), Some(b)) => {
                    linear_add(c, &a, terms, const_) && linear_add(-c, &b, terms, const_)
                }
                _ => false,
            }
        }
        "*" => {
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
