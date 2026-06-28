//! Demodulation / interval-aware mod elimination (Python ``simplify_demod`` parity).

use std::collections::{HashMap, HashSet};

use smt2::{assert_commands, map_asserts, Script, Term};

use crate::passes::skolem::term_util::expand_lets;

#[derive(Clone, Debug, PartialEq, Eq)]
struct IntInterval {
    lo: Option<i128>,
    hi: Option<i128>,
}

impl IntInterval {
    fn top() -> Self {
        Self {
            lo: None,
            hi: None,
        }
    }

    fn const_(v: i128) -> Self {
        Self {
            lo: Some(v),
            hi: Some(v),
        }
    }

    fn intersect(self, other: Self) -> Self {
        let lo = match (self.lo, other.lo) {
            (None, x) | (x, None) => x,
            (Some(a), Some(b)) => Some(a.max(b)),
        };
        let hi = match (self.hi, other.hi) {
            (None, x) | (x, None) => x,
            (Some(a), Some(b)) => Some(a.min(b)),
        };
        Self { lo, hi }
    }

    fn within_0_p(&self, p: i128) -> bool {
        matches!((self.lo, self.hi), (Some(lo), Some(hi)) if lo >= 0 && hi < p)
    }
}

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
    let mut stats = DemodStats::default();

    let mut assert_bodies: Vec<Term> = Vec::new();
    for cmd in assert_commands(script) {
        let body = smt2::term::assert_body(&cmd.raw).ok_or_else(|| {
            format!("malformed assert command: {}", cmd.raw)
        })?;
        let term = Term::parse(&body)?;
        let term = expand_lets(&term);
        let rewritten = eqmod_walk(&term, field_mod);
        if rewritten != term {
            stats.eqmod_asserts_changed += 1;
        }
        assert_bodies.push(rewritten);
    }

    let (ranges, protected) = extract_symbol_ranges(&assert_bodies);

    let mut body_iter = assert_bodies.into_iter();
    let out = map_asserts(script, |_body| {
        let term = body_iter.next().ok_or("assert index mismatch")?;
        let excluded = HashSet::new();
        let mut ctx = DemodCtx {
            ranges: &ranges,
            protected: &protected,
            excluded_qvars: &excluded,
            stats: &mut stats,
        };
        Ok(demod_substitute(&term, &mut ctx).to_string())
    })?;

    let stats_json = serde_json::json!({
        "range_symbols": ranges.len(),
        "protected_range_constraints": protected.len(),
        "eqmod_asserts_changed": stats.eqmod_asserts_changed,
        "const_eval": stats.const_eval,
        "into_ite": stats.into_ite,
        "elim_by_range": stats.elim_by_range,
    });
    Ok((out, stats_json))
}

struct DemodCtx<'a> {
    ranges: &'a HashMap<String, IntInterval>,
    protected: &'a HashSet<Term>,
    excluded_qvars: &'a HashSet<String>,
    stats: &'a mut DemodStats,
}

fn int_constant(t: &Term) -> Option<i128> {
    match t {
        Term::Atom(s) => smt2::term::parse_int_literal(s),
        _ => None,
    }
}

fn int_constant_mod(t: &Term, m: i128) -> Option<i128> {
    if let Some(v) = int_constant(t) {
        return Some(((v % m) + m) % m);
    }
    match t {
        Term::Atom(s) => smt2::term::mod_int_literal_string(s, m)?.parse().ok(),
        _ => None,
    }
}
fn is_symbol(t: &Term) -> bool {
    match t {
        Term::Atom(s) => {
            s != "true"
                && s != "false"
                && !smt2::term::is_int_literal_string(s)
        }
        _ => false,
    }
}

fn symbol_name(t: &Term) -> Option<&str> {
    match t {
        Term::Atom(s) => Some(s.as_str()),
        _ => None,
    }
}

fn atom(s: &str) -> Term {
    Term::Atom(s.to_string())
}

fn list(head: &str, args: Vec<Term>) -> Term {
    let mut items = vec![atom(head)];
    items.extend(args);
    Term::List(items)
}

fn flatten_top_level_constraints(formula: &Term) -> Vec<Term> {
    if let Term::List(items) = formula {
        if matches!(items.first(), Some(Term::Atom(s)) if s == "and") {
            let mut out = Vec::new();
            for arg in &items[1..] {
                out.extend(flatten_top_level_constraints(arg));
            }
            return out;
        }
    }
    vec![formula.clone()]
}

fn intersect_range(ranges: &mut HashMap<String, IntInterval>, sym: &str, interval: IntInterval) {
    let prev = ranges.get(sym).cloned().unwrap_or_else(IntInterval::top);
    ranges.insert(sym.to_string(), prev.intersect(interval));
}

fn self_mod_symbol(formula: &Term) -> Option<(&str, i128)> {
    let Term::List(items) = formula else {
        return None;
    };
    if !matches!(items.first(), Some(Term::Atom(s)) if s == "=") || items.len() != 3 {
        return None;
    }
    let a = &items[1];
    let b = &items[2];
    if is_symbol(a) {
        if let Some((expr, m)) = mod_parts(b) {
            if expr == a {
                return Some((symbol_name(a)?, m));
            }
        }
    }
    if is_symbol(b) {
        if let Some((expr, m)) = mod_parts(a) {
            if expr == b {
                return Some((symbol_name(b)?, m));
            }
        }
    }
    None
}

fn mod_parts(t: &Term) -> Option<(&Term, i128)> {
    let Term::List(items) = t else {
        return None;
    };
    if !matches!(items.first(), Some(Term::Atom(s)) if s == "mod") || items.len() != 3 {
        return None;
    }
    let m = int_constant(&items[2])?;
    Some((&items[1], m))
}

fn normalized_relation(formula: &Term) -> Option<(&'static str, Term, Term)> {
    let (negated, relation) = match formula {
        Term::List(items) if matches!(items.first(), Some(Term::Atom(s)) if s == "not") && items.len() == 2 => {
            (true, &items[1])
        }
        other => (false, other),
    };
    let Term::List(items) = relation else {
        return None;
    };
    let head = match items.first() {
        Some(Term::Atom(s)) => s.as_str(),
        _ => return None,
    };
    if items.len() != 3 {
        return None;
    }
    let a = items[1].clone();
    let b = items[2].clone();
    match head {
        "=" => Some((if negated { "!=" } else { "=" }, a, b)),
        "<" => Some((if negated { ">=" } else { "<" }, a, b)),
        "<=" => Some((if negated { ">" } else { "<=" }, a, b)),
        ">=" if negated => {
            let (ca, cb) = canonicalize_ge_args(&a, &b);
            Some((">", ca, cb))
        }
        ">=" => Some((">=", a, b)),
        ">" if negated => {
            let (ca, cb) = canonicalize_gt_args(&a, &b);
            Some((">=", ca, cb))
        }
        ">" => Some((">", a, b)),
        _ => None,
    }
}

fn canonicalize_ge_args(a: &Term, b: &Term) -> (Term, Term) {
    if is_symbol(a) && int_constant(b).is_some() {
        (b.clone(), a.clone())
    } else {
        (a.clone(), b.clone())
    }
}

fn canonicalize_gt_args(a: &Term, b: &Term) -> (Term, Term) {
    if is_symbol(a) && int_constant(b).is_some() {
        (b.clone(), a.clone())
    } else {
        (a.clone(), b.clone())
    }
}

fn extract_symbol_ranges(
    formulas: &[Term],
) -> (HashMap<String, IntInterval>, HashSet<Term>) {
    let mut ranges: HashMap<String, IntInterval> = HashMap::new();
    let mut protected: HashSet<Term> = HashSet::new();

    for formula in formulas {
        for constraint in flatten_top_level_constraints(formula) {
            if let Some((sym, modulus)) = self_mod_symbol(&constraint) {
                intersect_range(
                    &mut ranges,
                    sym,
                    IntInterval {
                        lo: Some(0),
                        hi: Some(modulus - 1),
                    },
                );
                protected.insert(constraint);
                continue;
            }

            let Some((op, a, b)) = normalized_relation(&constraint) else {
                continue;
            };

            if op == "=" {
                let ac = int_constant(&a);
                let bc = int_constant(&b);
                if is_symbol(&a) {
                    if let Some(v) = bc {
                        intersect_range(&mut ranges, symbol_name(&a).unwrap(), IntInterval::const_(v));
                    }
                }
                if is_symbol(&b) {
                    if let Some(v) = ac {
                        intersect_range(&mut ranges, symbol_name(&b).unwrap(), IntInterval::const_(v));
                    }
                }
                continue;
            }

            let ac = int_constant(&a);
            let bc = int_constant(&b);
            match op {
                "<=" => {
                    if is_symbol(&b) {
                        if let Some(v) = ac {
                            intersect_range(
                                &mut ranges,
                                symbol_name(&b).unwrap(),
                                IntInterval {
                                    lo: Some(v),
                                    hi: None,
                                },
                            );
                        }
                    }
                    if is_symbol(&a) {
                        if let Some(v) = bc {
                            intersect_range(
                                &mut ranges,
                                symbol_name(&a).unwrap(),
                                IntInterval {
                                    lo: None,
                                    hi: Some(v),
                                },
                            );
                        }
                    }
                }
                "<" => {
                    if is_symbol(&b) {
                        if let Some(v) = ac {
                            intersect_range(
                                &mut ranges,
                                symbol_name(&b).unwrap(),
                                IntInterval {
                                    lo: Some(v + 1),
                                    hi: None,
                                },
                            );
                        }
                    }
                    if is_symbol(&a) {
                        if let Some(v) = bc {
                            intersect_range(
                                &mut ranges,
                                symbol_name(&a).unwrap(),
                                IntInterval {
                                    lo: None,
                                    hi: Some(v - 1),
                                },
                            );
                        }
                    }
                }
                ">=" => {
                    if is_symbol(&a) {
                        if let Some(v) = bc {
                            intersect_range(
                                &mut ranges,
                                symbol_name(&a).unwrap(),
                                IntInterval {
                                    lo: Some(v),
                                    hi: None,
                                },
                            );
                        }
                    }
                    if is_symbol(&b) {
                        if let Some(v) = ac {
                            intersect_range(
                                &mut ranges,
                                symbol_name(&b).unwrap(),
                                IntInterval {
                                    lo: None,
                                    hi: Some(v),
                                },
                            );
                        }
                    }
                }
                ">" => {
                    if is_symbol(&a) {
                        if let Some(v) = bc {
                            intersect_range(
                                &mut ranges,
                                symbol_name(&a).unwrap(),
                                IntInterval {
                                    lo: Some(v + 1),
                                    hi: None,
                                },
                            );
                        }
                    }
                    if is_symbol(&b) {
                        if let Some(v) = ac {
                            intersect_range(
                                &mut ranges,
                                symbol_name(&b).unwrap(),
                                IntInterval {
                                    lo: None,
                                    hi: Some(v - 1),
                                },
                            );
                        }
                    }
                }
                _ => {}
            }
        }
    }

    (ranges, protected)
}

fn normalize_arith_under_mod(e: &Term, m: i128) -> Term {
    assert!(m > 0);
    if let Some(k) = int_constant(e) {
        return atom(&(k % m).to_string());
    }
    if let Term::Atom(s) = e {
        if let Some(reduced) = smt2::term::mod_int_literal_string(s, m) {
            return atom(&reduced);
        }
    }
    let Term::List(items) = e else {
        return e.clone();
    };
    let head = match items.first() {
        Some(Term::Atom(s)) => s.as_str(),
        _ => return e.clone(),
    };
    match head {
        "+" => list(
            "+",
            items[1..]
                .iter()
                .map(|a| normalize_arith_under_mod(a, m))
                .collect(),
        ),
        "-" if items.len() == 2 => list("-", vec![normalize_arith_under_mod(&items[1], m)]),
        "-" if items.len() == 3 => {
            let na = normalize_arith_under_mod(&items[1], m);
            let nb = normalize_arith_under_mod(&items[2], m);
            list("+", vec![na, list("*", vec![atom(&(m - 1).to_string()), nb])])
        }
        "*" => list(
            "*",
            items[1..]
                .iter()
                .map(|a| normalize_arith_under_mod(a, m))
                .collect(),
        ),
        "ite" if items.len() == 4 => list(
            "ite",
            vec![
                items[1].clone(),
                normalize_arith_under_mod(&items[2], m),
                normalize_arith_under_mod(&items[3], m),
            ],
        ),
        _ => e.clone(),
    }
}

fn linear_form(e: &Term) -> Option<(HashMap<String, i128>, i128)> {
    let mut terms: HashMap<String, i128> = HashMap::new();
    let mut const_ = 0i128;

    fn add(c: i128, node: &Term, terms: &mut HashMap<String, i128>, const_: &mut i128) -> bool {
        if let Some(v) = int_constant(node) {
            *const_ += c * v;
            return true;
        }
        if is_symbol(node) {
            let name = symbol_name(node).unwrap().to_string();
            *terms.entry(name).or_insert(0) += c;
            return true;
        }
        let Term::List(items) = node else {
            return false;
        };
        let head = match items.first() {
            Some(Term::Atom(s)) => s.as_str(),
            _ => return false,
        };
        match head {
            "+" => items[1..].iter().all(|a| add(c, a, terms, const_)),
            "-" if items.len() == 2 => add(-c, &items[1], terms, const_),
            "-" if items.len() == 3 => {
                add(c, &items[1], terms, const_) && add(-c, &items[2], terms, const_)
            }
            "*" => {
                let mut k = 1i128;
                let mut rest = Vec::new();
                for a in &items[1..] {
                    if let Some(v) = int_constant(a) {
                        k *= v;
                    } else {
                        rest.push(a);
                    }
                }
                if rest.len() == 1 {
                    add(c * k, rest[0], terms, const_)
                } else if rest.is_empty() {
                    *const_ += c * k;
                    true
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    if add(1, e, &mut terms, &mut const_) {
        Some((terms, const_))
    } else {
        None
    }
}

fn mod_inverse(a: i128, m: i128) -> Option<i128> {
    let (mut t, mut newt) = (0i128, 1i128);
    let (mut r, mut newr) = (m, a % m);
    while newr != 0 {
        let q = r / newr;
        (t, newt) = (newt, t - q * newt);
        (r, newr) = (newr, r - q * newr);
    }
    if r != 1 {
        return None;
    }
    let mut t = t % m;
    if t < 0 {
        t += m;
    }
    Some(t)
}

fn wrap_mod(val: i128, field_mod: i128) -> Term {
    list("mod", vec![atom(&val.to_string()), atom(&field_mod.to_string())])
}

fn demod_rewrite_eqmod_zero_equals(lhs: &Term, rhs: &Term, field_mod: i128) -> Option<Term> {
    let (expr, modulus_val) = mod_parts(lhs)?;
    if !matches!(rhs, Term::Atom(s) if s == "0") {
        return None;
    }
    let p = field_mod;
    if modulus_val != p {
        return None;
    }
    let (mut terms, const_) = linear_form(expr)?;
    terms.retain(|_, a| {
        let r = *a % p;
        if r == 0 {
            false
        } else {
            *a = r;
            true
        }
    });
    if terms.len() != 1 {
        return None;
    }
    let (sym, a) = terms.into_iter().next().unwrap();
    if a == 0 || (a == 1 && const_ % p == 0) {
        return None;
    }
    let inv = mod_inverse(a, p)?;
    let val = (-const_ * inv).rem_euclid(p);
    Some(list("=", vec![atom(&sym), wrap_mod(val, p)]))
}

fn eqmod_walk(term: &Term, field_mod: Option<i128>) -> Term {
    let Some(p) = field_mod else {
        return walk_children_eqmod(term, field_mod);
    };
    if let Term::List(items) = term {
        if matches!(items.first(), Some(Term::Atom(s)) if s == "=") && items.len() == 3 {
            if let Some(rep) = demod_rewrite_eqmod_zero_equals(&items[1], &items[2], p) {
                return rep;
            }
            return list(
                "=",
                vec![eqmod_walk(&items[1], field_mod), eqmod_walk(&items[2], field_mod)],
            );
        }
    }
    walk_children_eqmod(term, field_mod)
}

fn walk_children_eqmod(term: &Term, field_mod: Option<i128>) -> Term {
    match term {
        Term::Atom(_) => term.clone(),
        Term::List(items) => {
            let head = items[0].clone();
            Term::List(
                std::iter::once(head)
                    .chain(items[1..].iter().map(|a| eqmod_walk(a, field_mod)))
                    .collect(),
            )
        }
    }
}

fn quantifier_vars(items: &[Term]) -> HashSet<String> {
    let mut out = HashSet::new();
    let Some(Term::List(decls)) = items.get(1) else {
        return out;
    };
    for decl in decls {
        if let Term::List(d) = decl {
            if let Some(Term::Atom(name)) = d.first() {
                out.insert(name.clone());
            }
        } else if let Term::Atom(name) = decl {
            out.insert(name.clone());
        }
    }
    out
}

fn demod_substitute(term: &Term, ctx: &mut DemodCtx<'_>) -> Term {
    if ctx.protected.contains(term) {
        return term.clone();
    }

    if let Term::List(items) = term {
        let head = match &items[0] {
            Term::Atom(s) => s.as_str(),
            _ => return recurse(term, ctx),
        };

        match head {
            "forall" | "exists" if items.len() >= 3 => {
                let qvars = quantifier_vars(items);
                let mut excluded = ctx.excluded_qvars.clone();
                excluded.extend(qvars);
                let body = {
                    let mut inner = DemodCtx {
                        ranges: ctx.ranges,
                        protected: ctx.protected,
                        excluded_qvars: &excluded,
                        stats: ctx.stats,
                    };
                    demod_substitute(&items[2], &mut inner)
                };
                list(head, vec![items[1].clone(), body])
            }
            "mod" if items.len() == 3 => demod_mod(&items[1], &items[2], ctx),
            _ => recurse(term, ctx),
        }
    } else {
        term.clone()
    }
}

fn recurse(term: &Term, ctx: &mut DemodCtx<'_>) -> Term {
    let Term::List(items) = term else {
        return term.clone();
    };
    let head = items[0].clone();
    Term::List(
        std::iter::once(head)
            .chain(items[1..].iter().map(|a| demod_substitute(a, ctx)))
            .collect(),
    )
}

fn demod_mod(expr: &Term, modulus: &Term, ctx: &mut DemodCtx<'_>) -> Term {
    let mut expr = expr.clone();
    if let Some(mc) = int_constant(modulus) {
        if mc > 0 {
            expr = normalize_arith_under_mod(&expr, mc);
        }
    }
    if let Some(mc) = int_constant(modulus) {
        if mc != 0 {
            if let Some(ec) = int_constant_mod(&expr, mc) {
                ctx.stats.const_eval += 1;
                return atom(&ec.to_string());
            }
        }
    }
    if let Term::List(items) = &expr {
        if matches!(items.first(), Some(Term::Atom(s)) if s == "ite") && items.len() == 4 {
            ctx.stats.into_ite += 1;
            let cond = items[1].clone();
            let thn = demod_substitute(&list("mod", vec![items[2].clone(), modulus.clone()]), ctx);
            let els = demod_substitute(&list("mod", vec![items[3].clone(), modulus.clone()]), ctx);
            return list("ite", vec![cond, thn, els]);
        }
    }
    if is_symbol(&expr) {
        if let Some(m) = int_constant(modulus) {
            if let Some(name) = symbol_name(&expr) {
                if ctx.excluded_qvars.contains(name) {
                    return list("mod", vec![expr, modulus.clone()]);
                }
                if let Some(interval) = ctx.ranges.get(name) {
                    if interval.within_0_p(m) {
                        ctx.stats.elim_by_range += 1;
                        return expr;
                    }
                }
            }
        }
    }
    list("mod", vec![expr, modulus.clone()])
}

#[cfg(test)]
mod tests {
    use super::*;

    fn p() -> i128 {
        field_mod().unwrap_or(2_147_483_647)
    }

    #[test]
    fn top_level_bounds_eliminate_mod() {
        let p = p();
        let script = Script::parse(&format!(
            "(declare-fun x () Int)\n\
             (assert (<= 0 x))\n\
             (assert (< x {p}))\n\
             (assert (= (mod x {p}) 0))\n\
             (check-sat)\n"
        ))
        .unwrap();
        std::env::set_var("SIMPLIFIER_FIELD_MOD", p.to_string());
        let (out, _) = apply(&script).unwrap();
        let s = smt2::dump_string(&out);
        assert!(s.contains("(= x 0)"));
    }

    #[test]
    fn self_mod_equality() {
        let p = p();
        let script = Script::parse(&format!(
            "(declare-fun x () Int)\n\
             (assert (= x (mod x {p})))\n\
             (assert (= (mod x {p}) 7))\n\
             (check-sat)\n"
        ))
        .unwrap();
        std::env::set_var("SIMPLIFIER_FIELD_MOD", p.to_string());
        let (out, _) = apply(&script).unwrap();
        let s = smt2::dump_string(&out);
        assert!(s.contains("(= x (mod x"));
        assert!(s.contains("(= x 7)"));
    }

    #[test]
    fn no_elim_without_upper_bound() {
        let p = p();
        let script = Script::parse(&format!(
            "(declare-fun x () Int)\n\
             (assert (<= 0 x))\n\
             (assert (= (mod x {p}) 0))\n\
             (check-sat)\n"
        ))
        .unwrap();
        std::env::set_var("SIMPLIFIER_FIELD_MOD", p.to_string());
        let (out, _) = apply(&script).unwrap();
        let s = smt2::dump_string(&out);
        assert!(s.contains("(mod x"));
    }

    #[test]
    fn actual_modulus_not_field() {
        let script = Script::parse(
            "(declare-fun x () Int)\n\
             (assert (<= 0 x))\n\
             (assert (< x 17))\n\
             (assert (= (mod x 17) 3))\n\
             (check-sat)\n",
        )
        .unwrap();
        let (out, _) = apply(&script).unwrap();
        let s = smt2::dump_string(&out);
        assert!(s.contains("(= x 3)"));
    }

    #[test]
    fn fold_mod_of_constants() {
        let script = Script::parse("(assert (= (mod 17 5) 2))\n(check-sat)\n").unwrap();
        let (out, _) = apply(&script).unwrap();
        let s = smt2::dump_string(&out);
        assert!(s.contains("(= 2 2)"));
    }

    #[test]
    fn eqmod_linear_rewrite() {
        let p = p();
        let a = 3i128;
        let b = 5i128;
        let inv = mod_inverse(a, p).unwrap();
        let x_val = (-b * inv).rem_euclid(p);
        let script = Script::parse(&format!(
            "(declare-fun x () Int)\n\
             (assert (= (mod (+ (* {a} x) {b}) {p}) 0))\n\
             (check-sat)\n"
        ))
        .unwrap();
        std::env::set_var("SIMPLIFIER_FIELD_MOD", p.to_string());
        let (out, _) = apply(&script).unwrap();
        let s = smt2::dump_string(&out);
        assert!(
            s.contains(&format!("(= x {x_val})"))
                || s.contains(&format!("(= x (mod {x_val} {p}))"))
        );
    }

    #[test]
    fn extract_negated_relations() {
        let x = atom("x");
        let y = atom("y");
        let formulas = vec![
            list("not", vec![list("<", vec![x.clone(), atom("0")])]),
            list("not", vec![list(">=", vec![x.clone(), atom("17")])]),
            list("not", vec![list("<=", vec![y.clone(), atom("2")])]),
            list("not", vec![list(">", vec![y.clone(), atom("16")])]),
        ];
        let (ranges, protected) = extract_symbol_ranges(&formulas);
        assert!(protected.is_empty());
        assert_eq!(ranges["x"], IntInterval { lo: Some(0), hi: Some(16) });
        assert_eq!(ranges["y"], IntInterval { lo: Some(3), hi: Some(16) });
    }
}
