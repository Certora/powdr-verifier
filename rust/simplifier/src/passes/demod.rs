//! Demodulation / mod rewrites on Z3 AST.

use std::collections::HashMap;

use smt2::ast_util::{int_from_i128, int_value_dyn, rebuild_app};
use smt2::{assert_commands, is_int_const, map_asserts, Script, SmtCommand};
use z3::ast::{Ast, AstKind, Bool, Dynamic, Int};
use z3::DeclKind;

/// Per-symbol closed integer interval `[lo, hi]` learned from top-level facts.
/// `i128::MIN` / `i128::MAX` act as -inf / +inf.
type Ranges = HashMap<Int, (i128, i128)>;
const NEG_INF: i128 = i128::MIN;
const POS_INF: i128 = i128::MAX;

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
    // Learn per-symbol integer ranges from all top-level asserted facts first,
    // then use them to eliminate `mod(x, m)` where `0 <= x < m` is proven
    // (mirrors demod.py's extract_symbol_ranges + elim_by_range).
    let ranges = collect_ranges(script);
    let out = map_asserts(script, |b| {
        // A `x = mod(x, m)` witness is left verbatim: it is the justification for
        // x's learned [0, m) range, so stripping its own mod would remove the
        // fact that licenses eliminating x's other mods.
        if self_mod_witness(b).is_some() {
            return Ok(b.clone());
        }
        match rewrite_bool(b, field_mod, &ranges, &mut stats) {
            Some(next) => {
                changed += 1;
                Ok(next)
            }
            None => Ok(b.clone()),
        }
    })?;
    let stats_json = serde_json::json!({
        "asserts_total": total,
        "asserts_changed": changed,
        "range_symbols": ranges.len(),
        "protected_range_constraints": 0,
        "eqmod_asserts_changed": stats.eqmod_asserts_changed,
        "const_eval": stats.const_eval,
        "into_ite": stats.into_ite,
        "elim_by_range": stats.elim_by_range,
    });
    Ok((out, stats_json))
}

/// `Some((x, m))` if `b` is `x = mod(x, m)` / `mod(x, m) = x` with `m > 0`.
fn self_mod_witness(b: &Bool) -> Option<(Int, i128)> {
    let d = Dynamic::from_ast(b);
    if d.kind() != AstKind::App || d.decl().kind() != DeclKind::Eq || d.num_children() != 2 {
        return None;
    }
    let a = d.nth_child(0)?;
    let c = d.nth_child(1)?;
    for (sym_d, mod_d) in [(&a, &c), (&c, &a)] {
        if !is_int_const(sym_d) {
            continue;
        }
        if mod_d.kind() == AstKind::App
            && mod_d.decl().kind() == DeclKind::Mod
            && mod_d.num_children() == 2
        {
            let inner = mod_d.nth_child(0)?.as_int()?;
            let sym = sym_d.as_int()?;
            if let Some(m) = int_lit(&mod_d.nth_child(1)?) {
                if m > 0 && inner == sym {
                    return Some((sym, m));
                }
            }
        }
    }
    None
}

fn intersect(ranges: &mut Ranges, sym: Int, lo: i128, hi: i128) {
    let e = ranges.entry(sym).or_insert((NEG_INF, POS_INF));
    if lo > e.0 {
        e.0 = lo;
    }
    if hi < e.1 {
        e.1 = hi;
    }
}

/// Collect per-symbol ranges from top-level asserted facts (descending only
/// top-level conjunctions, so every fact is unconditional).
fn collect_ranges(script: &Script) -> Ranges {
    let mut ranges = Ranges::new();
    for cmd in &script.commands {
        if let SmtCommand::Assert { bool: b, .. } = cmd {
            collect_from_bool(b, &mut ranges);
        }
    }
    ranges
}

fn collect_from_bool(b: &Bool, ranges: &mut Ranges) {
    let d = Dynamic::from_ast(b);
    if d.kind() != AstKind::App {
        return;
    }
    if d.decl().kind() == DeclKind::And {
        for i in 0..d.num_children() {
            if let Some(ch) = d.nth_child(i).and_then(|c| c.as_bool()) {
                collect_from_bool(&ch, ranges);
            }
        }
        return;
    }
    if let Some((sym, m)) = self_mod_witness(b) {
        intersect(ranges, sym, 0, m - 1);
        return;
    }
    // Push a top-level negation inward, mirroring demod.py's _normalized_relation.
    let (neg, rel) = if d.decl().kind() == DeclKind::Not && d.num_children() == 1 {
        match d.nth_child(0) {
            Some(inner) => (true, inner),
            None => return,
        }
    } else {
        (false, d.clone())
    };
    if rel.kind() != AstKind::App || rel.num_children() != 2 {
        return;
    }
    let (Some(a), Some(b2)) = (rel.nth_child(0), rel.nth_child(1)) else {
        return;
    };
    let op = match (rel.decl().kind(), neg) {
        (DeclKind::Eq, false) => "=",
        (DeclKind::Lt, false) | (DeclKind::Ge, true) => "<",
        (DeclKind::Le, false) | (DeclKind::Gt, true) => "<=",
        (DeclKind::Gt, false) | (DeclKind::Le, true) => ">",
        (DeclKind::Ge, false) | (DeclKind::Lt, true) => ">=",
        _ => return,
    };
    let ac = int_lit(&a);
    let bc = int_lit(&b2);
    let a_sym = is_int_const(&a);
    let b_sym = is_int_const(&b2);
    match op {
        "=" => {
            if a_sym {
                if let Some(v) = bc {
                    if let Some(s) = a.as_int() {
                        intersect(ranges, s, v, v);
                    }
                }
            }
            if b_sym {
                if let Some(v) = ac {
                    if let Some(s) = b2.as_int() {
                        intersect(ranges, s, v, v);
                    }
                }
            }
        }
        "<=" => {
            if b_sym {
                if let (Some(v), Some(s)) = (ac, b2.as_int()) {
                    intersect(ranges, s, v, POS_INF);
                }
            }
            if a_sym {
                if let (Some(v), Some(s)) = (bc, a.as_int()) {
                    intersect(ranges, s, NEG_INF, v);
                }
            }
        }
        "<" => {
            if b_sym {
                if let (Some(v), Some(s)) = (ac, b2.as_int()) {
                    intersect(ranges, s, v + 1, POS_INF);
                }
            }
            if a_sym {
                if let (Some(v), Some(s)) = (bc, a.as_int()) {
                    intersect(ranges, s, NEG_INF, v - 1);
                }
            }
        }
        ">=" => {
            if a_sym {
                if let (Some(v), Some(s)) = (bc, a.as_int()) {
                    intersect(ranges, s, v, POS_INF);
                }
            }
            if b_sym {
                if let (Some(v), Some(s)) = (ac, b2.as_int()) {
                    intersect(ranges, s, NEG_INF, v);
                }
            }
        }
        ">" => {
            if a_sym {
                if let (Some(v), Some(s)) = (bc, a.as_int()) {
                    intersect(ranges, s, v + 1, POS_INF);
                }
            }
            if b_sym {
                if let (Some(v), Some(s)) = (ac, b2.as_int()) {
                    intersect(ranges, s, NEG_INF, v - 1);
                }
            }
        }
        _ => {}
    }
}

/// Returns ``Some`` only when a rewrite changed the term; ``None`` leaves it
/// untouched so the original AST node is reused (no rebuild/hashconsing).
fn rewrite_bool(b: &Bool, field_mod: Option<i128>, ranges: &Ranges, stats: &mut DemodStats) -> Option<Bool> {
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
    let (args, any) = rewrite_children(&d, field_mod, ranges, stats, true);
    if !any {
        return None;
    }
    let refs: Vec<&dyn Ast> = args.iter().map(|a| a as &dyn Ast).collect();
    rebuild_app(&d.decl(), &refs).as_bool()
}

fn rewrite_dynamic(ast: &Dynamic, field_mod: Option<i128>, ranges: &Ranges, stats: &mut DemodStats) -> Option<Dynamic> {
    if ast.kind() == AstKind::Quantifier {
        return None;
    }
    if let Some(i) = ast.as_int() {
        return rewrite_int(&i, field_mod, ranges, stats).map(|x| Dynamic::from_ast(&x));
    }
    if ast.kind() != AstKind::App {
        return None;
    }
    let (args, any) = rewrite_children(ast, field_mod, ranges, stats, false);
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
    ranges: &Ranges,
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
                rewrite_bool(&cb, field_mod, ranges, stats).map(|x| Dynamic::from_ast(&x))
            } else {
                rewrite_dynamic(&ch, field_mod, ranges, stats)
            }
        } else {
            rewrite_dynamic(&ch, field_mod, ranges, stats)
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

fn rewrite_int(e: &Int, field_mod: Option<i128>, ranges: &Ranges, stats: &mut DemodStats) -> Option<Int> {
    let d = Dynamic::from_ast(e);
    if d.kind() != AstKind::App {
        return None;
    }
    if d.decl().kind() == DeclKind::Mod && d.num_children() == 2 {
        let c0 = d.nth_child(0).and_then(|c| c.as_int());
        let c1 = d.nth_child(1).and_then(|c| c.as_int());
        let expr_r = c0.as_ref().and_then(|i| rewrite_int(i, field_mod, ranges, stats));
        let modulus_r = c1.as_ref().and_then(|i| rewrite_int(i, field_mod, ranges, stats));
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
                // elim_by_range: drop `mod(x, m)` when a learned top-level fact
                // proves `0 <= x < m` for the symbol x.
                if is_int_const(&ed) {
                    if let Some(&(lo, hi)) = ranges.get(&expr) {
                        if lo >= 0 && hi <= m - 1 {
                            stats.elim_by_range += 1;
                            return Some(expr);
                        }
                    }
                }
            }
        }
        if expr_r.is_none() && modulus_r.is_none() {
            return None;
        }
        return Some(expr.modulo(&modulus));
    }
    let (args, any) = rewrite_children(&d, field_mod, ranges, stats, false);
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
