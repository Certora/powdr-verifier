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
    elim_eqmod_range: usize,
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
    // Iterate to a fixpoint: a reduction can pin a variable to a constant
    // (e.g. `demod_rewrite_eqmod_zero_equals` turning `mod(a*x, p) = 0` into
    // `x = c`), which tightens `collect_ranges` on the next round and unlocks
    // range-based eliminations that were out of reach before. A single pass
    // therefore leaves reducible mods behind; re-collecting ranges after each
    // round and repeating drains them. Capped so a pathological non-converging
    // input can't loop forever.
    const MAX_ITERS: usize = 8;
    let mut cur = script.clone();
    let mut range_symbols = 0usize;
    let mut iters = 0usize;
    for _ in 0..MAX_ITERS {
        iters += 1;
        // Learn per-symbol integer ranges from all top-level asserted facts
        // first, then use them to eliminate `mod(x, m)` where `0 <= x < m` is
        // proven (mirrors demod.py's extract_symbol_ranges + elim_by_range).
        let ranges = collect_ranges(&cur);
        range_symbols = ranges.len();
        let mut round_changed = 0usize;
        let out = map_asserts(&cur, |b| {
            // A `x = mod(x, m)` witness is left verbatim: it is the
            // justification for x's learned [0, m) range, so stripping its own
            // mod would remove the fact that licenses eliminating x's other mods.
            if self_mod_witness(b).is_some() {
                return Ok(b.clone());
            }
            match rewrite_bool(b, field_mod, &ranges, &mut stats) {
                Some(next) => {
                    round_changed += 1;
                    Ok(next)
                }
                None => Ok(b.clone()),
            }
        })?;
        cur = out;
        changed += round_changed;
        if round_changed == 0 {
            break;
        }
    }
    let out = cur;
    let stats_json = serde_json::json!({
        "asserts_total": total,
        "asserts_changed": changed,
        "iterations": iters,
        "range_symbols": range_symbols,
        "protected_range_constraints": 0,
        "eqmod_asserts_changed": stats.eqmod_asserts_changed,
        "const_eval": stats.const_eval,
        "into_ite": stats.into_ite,
        "elim_by_range": stats.elim_by_range,
        "elim_eqmod_range": stats.elim_eqmod_range,
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
    // Single-variable linear bound: fold `c1*x + c0 <op> 0` into a bound on x.
    // Generalizes bare `x <op> const` to compound-LHS forms — e.g. the timestamp
    // range check `not (4096 - decomp <= 0)` (i.e. `-decomp + 4096 > 0`) yields
    // `decomp <= 4095` — which is what lets elim_by_range discharge those
    // columns' mods. Localized here (not the unused intervals pass).
    let (Some(ai), Some(bi)) = (a.as_int(), b2.as_int()) else {
        return;
    };
    let mut terms: HashMap<Int, i128> = HashMap::new();
    let mut c0: i128 = 0;
    if !linear_add(1, &ai, &mut terms, &mut c0) || !linear_add(-1, &bi, &mut terms, &mut c0) {
        return;
    }
    terms.retain(|_, c| *c != 0);
    if terms.len() != 1 {
        return;
    }
    let (x, c1) = terms.into_iter().next().unwrap();
    // Normalize to c1 > 0 (flipping the relation if needed): x <op> t, t = -c0/c1.
    let (op, c0, c1) = if c1 < 0 {
        let flipped = match op {
            "<=" => ">=",
            ">=" => "<=",
            "<" => ">",
            ">" => "<",
            o => o,
        };
        (flipped, -c0, -c1)
    } else {
        (op, c0, c1)
    };
    let num = -c0; // t = num / c1 with c1 > 0
    let floor = num.div_euclid(c1);
    let ceil = -((-num).div_euclid(c1));
    match op {
        "<=" => intersect(ranges, x, NEG_INF, floor),
        "<" => intersect(ranges, x, NEG_INF, ceil - 1),
        ">=" => intersect(ranges, x, ceil, POS_INF),
        ">" => intersect(ranges, x, floor + 1, POS_INF),
        "=" => {
            if num % c1 == 0 {
                let v = num / c1;
                intersect(ranges, x, v, v);
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
            // Multi-variable, any-residue generalization using learned ranges:
            // `(mod LIN p) = R` collapses to a plain integer equation when the
            // balanced linear form LIN has a unique multiple of p in its range.
            if let Some(eq) = demod_rewrite_eqmod_range(&lhs, &rhs, field_mod, ranges) {
                stats.elim_eqmod_range += 1;
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
        let expr0 = expr_r
            .clone()
            .or_else(|| c0.clone())
            .unwrap_or_else(|| e.clone());
        let modulus = modulus_r
            .clone()
            .or_else(|| c1.clone())
            .unwrap_or_else(|| int_from_i128(1));
        // Flatten nested same-modulus mods: (mod (…(mod E m)…) m) ≡ (mod (…E…) m).
        // Removes the nonlinearity in range-decomposition consistency terms like
        // 2^17 * (mod (15360*(x-2)) P) — where 2^17*15360 ≡ -1 (mod P) — leaving
        // a linear identity z3 folds instead of grinding a nested-mod nonlinear
        // equation.
        let m_opt = int_lit(&Dynamic::from_ast(&modulus)).filter(|&m| m > 0);
        let flat = m_opt.and_then(|m| strip_inner_mods(&expr0, m));
        let expr = flat.clone().unwrap_or(expr0);
        if let Some(m) = m_opt {
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
        if expr_r.is_none() && modulus_r.is_none() && flat.is_none() {
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

/// Under an outer `(mod _ m)`, replace nested same-modulus `(mod E m)` subterms
/// with (the flattened) `E` — sound since `(mod E m) ≡ E (mod m)`. Returns
/// `Some` only when something changed. A different modulus is left intact.
fn strip_inner_mods(e: &Int, m: i128) -> Option<Int> {
    let d = Dynamic::from_ast(e);
    if d.kind() != AstKind::App {
        return None;
    }
    if d.decl().kind() == DeclKind::Mod && d.num_children() == 2 {
        if d.nth_child(1).and_then(|c| int_lit(&c)) == Some(m) {
            let inner = d.nth_child(0)?.as_int()?;
            return Some(strip_inner_mods(&inner, m).unwrap_or(inner));
        }
        return None;
    }
    let mut args: Vec<Dynamic> = Vec::new();
    let mut changed = false;
    for i in 0..d.num_children() {
        let Some(ch) = d.nth_child(i) else { continue };
        match ch.as_int().and_then(|ci| strip_inner_mods(&ci, m)) {
            Some(x) => {
                changed = true;
                args.push(Dynamic::from_ast(&x));
            }
            None => args.push(ch),
        }
    }
    if !changed {
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

/// Balanced residue of `c` modulo `p`: the representative in `(-p/2, p/2]`.
/// Balancing before the range analysis keeps coefficients small (e.g. `p-1`
/// becomes `-1`), which is what makes a linear form's integer range tight
/// enough to admit a unique multiple of `p`.
fn balance(c: i128, p: i128) -> i128 {
    let r = c.rem_euclid(p);
    if r > p / 2 {
        r - p
    } else {
        r
    }
}

/// Multi-variable generalization of [`demod_rewrite_eqmod_zero_equals`].
///
/// `(mod LIN p) = R` (either operand order) with `LIN` a linear form over
/// range-bounded variables is equivalent to `LIN ≡ R (mod p)`. Balancing the
/// coefficients into `(-p/2, p/2]` gives an equivalent form `LIN_bal` (same
/// value mod p) with a tight integer range `[lo, hi]`; the atom then holds iff
/// `LIN_bal` equals one of `{R + m·p}` inside that range. When exactly one such
/// multiple exists the mod disappears entirely, leaving the plain integer
/// equation `LIN_bal = R + m·p` — no quotient for z3 to branch on. When none
/// exists the congruence is unsatisfiable (`false`).
///
/// Reduced-only by design: if two or more multiples fall in range we return
/// `None` rather than emit a disjunction — introducing an `(or ...)` adds a
/// branch that empirically hurts z3 more than the surviving mod.
///
/// Sound because the variable ranges come from top-level asserted facts
/// ([`collect_ranges`]); a variable without a finite bound aborts the rewrite.
fn demod_rewrite_eqmod_range(
    a: &Int,
    b: &Int,
    field_mod: Option<i128>,
    ranges: &Ranges,
) -> Option<Bool> {
    // Orient: one side is `(mod EXPR p)`, the other an integer literal residue.
    let (expr, p, r) = if let Some((e, p)) = mod_parts_int(a) {
        (e, p, int_lit(&Dynamic::from_ast(b))?)
    } else if let Some((e, p)) = mod_parts_int(b) {
        (e, p, int_lit(&Dynamic::from_ast(a))?)
    } else {
        return None;
    };
    if let Some(fp) = field_mod {
        if p != fp {
            return None;
        }
    }
    // A residue equality only makes sense for `0 <= R < p`.
    if p <= 0 || r < 0 || r >= p {
        return None;
    }
    let (terms, const_) = linear_form(&expr)?;

    // Balanced linear form + its integer range from the per-variable bounds.
    let cb = balance(const_, p);
    let mut lo = cb;
    let mut hi = cb;
    let mut bal_terms: Vec<(Int, i128)> = Vec::new();
    for (var, coeff) in terms {
        let c = balance(coeff, p);
        if c == 0 {
            continue;
        }
        let &(vlo, vhi) = ranges.get(&var)?;
        if vlo == NEG_INF || vhi == POS_INF {
            return None;
        }
        let (clo, chi) = if c > 0 { (c * vlo, c * vhi) } else { (c * vhi, c * vlo) };
        lo = lo.checked_add(clo)?;
        hi = hi.checked_add(chi)?;
        bal_terms.push((var, c));
    }

    // Multiples `m` with `R + m·p` in `[lo, hi]`: m in [ceil((lo-R)/p), floor((hi-R)/p)].
    let m_max = (hi - r).div_euclid(p); // floor for p > 0
    let m_min = -((-(lo - r)).div_euclid(p)); // ceil for p > 0
    if m_min > m_max {
        // No achievable value: the congruence is unsatisfiable.
        return Some(Bool::from_bool(false));
    }
    if m_min < m_max {
        // Two or more candidates: skip rather than introduce a disjunction.
        return None;
    }
    let val = r + m_min * p;

    // Rebuild the balanced linear form as an Int term and equate it to `val`.
    let mut parts: Vec<Int> = Vec::new();
    for (var, c) in &bal_terms {
        if *c == 1 {
            parts.push(var.clone());
        } else {
            parts.push(Int::mul(&[&int_from_i128(*c), var]));
        }
    }
    if cb != 0 {
        parts.push(int_from_i128(cb));
    }
    let expr_bal = match parts.len() {
        0 => int_from_i128(0),
        1 => parts.into_iter().next().unwrap(),
        _ => {
            let refs: Vec<&Int> = parts.iter().collect();
            Int::add(&refs)
        }
    };
    Some(expr_bal.eq(&int_from_i128(val)))
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

#[cfg(test)]
mod tests {
    use super::*;

    const P: i128 = 2013265921;

    fn run(src: &str) -> (String, serde_json::Value) {
        let _g = crate::field_env_guard();
        std::env::set_var("SIMPLIFIER_FIELD_MOD", P.to_string());
        let script = Script::parse(src).unwrap();
        let (out, stats) = apply(&script).unwrap();
        (smt2::dump_string(&out), stats)
    }

    #[test]
    fn eqmod_zero_difference_of_bounded_vars_becomes_equality() {
        // a, b in [0, P) via self-mod witnesses; (a - b) ≡ 0 (mod P) has the
        // single multiple 0 in range (-(P-1), P-1), so it collapses to a - b = 0
        // with the mod gone entirely.
        let (dump, stats) = run(&format!(
            "(declare-fun a () Int)\n(declare-fun b () Int)\n\
             (assert (= a (mod a {P})))\n(assert (= b (mod b {P})))\n\
             (assert (= (mod (- a b) {P}) 0))\n(check-sat)\n"
        ));
        assert!(stats["elim_eqmod_range"].as_u64().unwrap() >= 1, "{dump}");
        // the reduced conjunct no longer wraps (a - b) in a mod
        assert!(!dump.contains("(mod (- a b)"), "{dump}");
    }

    #[test]
    fn eqmod_zero_multivar_byte_word_becomes_equality() {
        // A two-byte word (256 x + y) with x, y in [0, 255] ≡ 0 (mod P) ranges
        // over [0, 65535], whose only multiple of P is 0. Two variables, so the
        // single-var modular-inverse path does not apply and the range reducer
        // is what collapses it to 256 x + y = 0 (no quotient for z3).
        let (dump, stats) = run(&format!(
            "(declare-fun x () Int)\n(declare-fun y () Int)\n\
             (assert (>= x 0))\n(assert (<= x 255))\n\
             (assert (>= y 0))\n(assert (<= y 255))\n\
             (assert (= (mod (+ (* 256 x) y) {P}) 0))\n(check-sat)\n"
        ));
        assert!(stats["elim_eqmod_range"].as_u64().unwrap() >= 1, "{dump}");
        assert!(!dump.contains("(mod (+"), "{dump}");
    }

    #[test]
    fn eqmod_two_multiples_in_range_is_left_alone() {
        // a in [0, P); (a - 5) ≡ 0 (mod P) admits a = 5 and a = 5 - P ... but
        // with a in [0,P) only a=5; use a wider form (a + b) with a,b in [0,P)
        // so the range [0, 2P-2] holds two multiples {0, P} -> reduced-only skips.
        let (dump, stats) = run(&format!(
            "(declare-fun a () Int)\n(declare-fun b () Int)\n\
             (assert (= a (mod a {P})))\n(assert (= b (mod b {P})))\n\
             (assert (= (mod (+ a b) {P}) 0))\n(check-sat)\n"
        ));
        assert_eq!(stats["elim_eqmod_range"].as_u64().unwrap(), 0, "{dump}");
        assert!(dump.contains("mod"), "{dump}");
    }
}
