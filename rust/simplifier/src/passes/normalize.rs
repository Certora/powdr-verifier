//! Polynomial Int relation normalization (Python ``simplify_normalize`` parity).

use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};

use smt2::{assert_commands, map_asserts, Script, Term};

type Monomial = Vec<u32>;
type Poly = HashMap<Monomial, i128>;

fn declare_fun_symbol(raw: &str) -> Option<String> {
    let inner = raw.trim().strip_prefix('(')?.trim();
    let rest = inner.strip_prefix("declare-fun")?.trim();
    let end = rest.find(|c: char| c.is_whitespace())?;
    Some(rest[..end].to_string())
}

fn declare_fun_sort(raw: &str) -> Option<&str> {
    let body = raw.trim().strip_suffix(')')?.trim();
    body.rsplit_once(' ').map(|(_, sort)| sort)
}

fn collect_bool_symbols(script: &Script) -> HashSet<String> {
    let mut out = HashSet::new();
    for cmd in &script.commands {
        if cmd.name() != "declare-fun" {
            continue;
        }
        if declare_fun_sort(&cmd.raw) != Some("Bool") {
            continue;
        }
        if let Some(sym) = declare_fun_symbol(&cmd.raw) {
            out.insert(sym);
        }
    }
    out
}

fn contains_bool_symbol(t: &Term, bool_symbols: &HashSet<String>) -> bool {
    match t {
        Term::Atom(s) => bool_symbols.contains(s),
        Term::List(items) => items[1..]
            .iter()
            .any(|a| contains_bool_symbol(a, bool_symbols)),
    }
}

pub fn field_mod() -> Option<i128> {
    std::env::var("SIMPLIFIER_FIELD_MOD")
        .ok()
        .and_then(|s| s.parse().ok())
}

pub fn apply(script: &Script) -> Result<(Script, serde_json::Value), String> {
    let p = field_mod();
    let vars = collect_variables(script, p);
    let var_index: HashMap<String, usize> = vars
        .iter()
        .enumerate()
        .map(|(i, v)| (term_key(v), i))
        .collect();
    let bool_symbols = collect_bool_symbols(script);
    let ctx = NormalizeCtx {
        var_index: &var_index,
        vars: &vars,
        field_mod: p,
        bool_symbols: &bool_symbols,
    };

    let total = assert_commands(script).len();
    let mut changed = 0usize;
    let out = map_asserts(script, |body| {
        let term = Term::parse(body)?;
        let new = normalize_term(&term, &ctx);
        let new_body = new.to_string();
        if new_body != body {
            changed += 1;
        }
        Ok(new_body)
    })?;

    let stats = serde_json::json!({
        "asserts": total,
        "asserts_changed": changed,
        "int_vars": vars.len(),
    });
    Ok((out, stats))
}

struct NormalizeCtx<'a> {
    var_index: &'a HashMap<String, usize>,
    vars: &'a [Term],
    field_mod: Option<i128>,
    bool_symbols: &'a HashSet<String>,
}

fn int_literal(t: &Term) -> Option<i128> {
    match t {
        Term::Atom(s) => smt2::term::parse_int_literal(s),
        _ => None,
    }
}

fn int_literal_mod(t: &Term, modulo: Option<i128>) -> Option<i128> {
    let m = modulo?;
    match t {
        Term::Atom(s) => {
            if let Some(v) = smt2::term::parse_int_literal(s) {
                return Some(coeff_mod(v, m));
            }
            smt2::term::mod_int_literal_string(s, m)?.parse().ok()
        }
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

fn term_key(t: &Term) -> String {
    t.to_string()
}

fn is_combinator(head: &str) -> bool {
    matches!(head, "+" | "-" | "*")
}

fn is_bool_or_relation_head(head: &str) -> bool {
    matches!(
        head,
        "and" | "or" | "not" | "=>" | "ite" | "=" | "<" | "<=" | ">" | ">=" | "distinct"
    )
}

fn field_mod_wrap(t: &Term, p: i128) -> bool {
    let Term::List(items) = t else {
        return false;
    };
    matches!(items.first(), Some(Term::Atom(s)) if s == "mod")
        && items.len() == 3
        && int_literal(&items[2]) == Some(p)
}

fn unwrap_field_mod_body(t: &Term, p: i128) -> &Term {
    if field_mod_wrap(t, p) {
        let Term::List(items) = t else {
            return t;
        };
        &items[1]
    } else {
        t
    }
}

fn collect_variables(script: &Script, field_mod: Option<i128>) -> Vec<Term> {
    let mut gens: HashSet<String> = HashSet::new();
    let mut gen_terms: HashMap<String, Term> = HashMap::new();
    let mut seen: HashSet<String> = HashSet::new();

    fn visit(
        n: &Term,
        field_mod: Option<i128>,
        gens: &mut HashSet<String>,
        gen_terms: &mut HashMap<String, Term>,
        seen: &mut HashSet<String>,
    ) {
        let key = term_key(n);
        if seen.contains(&key) {
            return;
        }
        seen.insert(key.clone());

        if int_literal(n).is_some() {
            return;
        }

        let Term::List(items) = n else {
            gens.insert(key.clone());
            gen_terms.insert(key, n.clone());
            return;
        };

        let head = match &items[0] {
            Term::Atom(s) => s.as_str(),
            _ => {
                gens.insert(key.clone());
                gen_terms.insert(key, n.clone());
                return;
            }
        };

        if let Some(p) = field_mod {
            if head == "mod" && items.len() == 3 && int_literal(&items[2]) == Some(p) {
                visit(&items[1], field_mod, gens, gen_terms, seen);
                return;
            }
        }

        if is_combinator(head) {
            for arg in &items[1..] {
                visit(arg, field_mod, gens, gen_terms, seen);
            }
            return;
        }

        if is_bool_or_relation_head(head) {
            for arg in &items[1..] {
                visit(arg, field_mod, gens, gen_terms, seen);
            }
            return;
        }

        gens.insert(key.clone());
        gen_terms.insert(key, n.clone());
    }

    for cmd in assert_commands(script) {
        if let Some(body) = smt2::term::assert_body(&cmd.raw) {
            if let Ok(term) = Term::parse(&body) {
                visit(&term, field_mod, &mut gens, &mut gen_terms, &mut seen);
            }
        }
    }

    let mut keys: Vec<String> = gens.into_iter().collect();
    keys.sort();
    keys.into_iter().map(|k| gen_terms.remove(&k).unwrap()).collect()
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

fn lead_exp(poly: &Poly) -> Monomial {
    poly.keys()
        .max_by(|a, b| compare_monomials(a, b))
        .cloned()
        .unwrap_or_default()
}

fn coeff_mod(v: i128, m: i128) -> i128 {
    v.rem_euclid(m)
}

fn poly_add(a: &Poly, b: &Poly, scale_b: i128, modulo: Option<i128>) -> Poly {
    let mut keys: HashSet<&Monomial> = HashSet::new();
    for k in a.keys() {
        keys.insert(k);
    }
    for k in b.keys() {
        keys.insert(k);
    }
    let mut out = Poly::new();
    for e in keys {
        let mut v = a.get(e).copied().unwrap_or(0) + scale_b * b.get(e).copied().unwrap_or(0);
        if let Some(m) = modulo {
            v = coeff_mod(v, m);
        }
        if v != 0 {
            out.insert(e.clone(), v);
        }
    }
    out
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

fn relation_modular(lhs: &Term, rhs: &Term, p: i128) -> Option<bool> {
    let lhs_m = field_mod_wrap(lhs, p);
    let rhs_m = field_mod_wrap(rhs, p);
    if lhs_m == rhs_m {
        return Some(lhs_m);
    }
    if lhs_m && int_literal(rhs).is_some() {
        return Some(true);
    }
    if rhs_m && int_literal(lhs).is_some() {
        return Some(true);
    }
    None
}

fn expr_to_poly(n: &Term, var_index: &HashMap<String, usize>, modulo: Option<i128>) -> Option<Poly> {
    if let Some(m) = int_literal_mod(n, modulo).or_else(|| int_literal(n)) {
        return if m == 0 {
            Some(Poly::new())
        } else {
            Some(HashMap::from([(Vec::new(), m)]))
        };
    }

    let Term::List(items) = n else {
        let key = term_key(n);
        let idx = *var_index.get(&key)?;
        return Some(HashMap::from([(vec![idx as u32], 1)]));
    };

    let head = match &items[0] {
        Term::Atom(s) => s.as_str(),
        _ => return None,
    };

    match head {
        "+" => {
            let mut acc = Poly::new();
            for a in &items[1..] {
                let q = expr_to_poly(a, var_index, modulo)?;
                acc = poly_add(&acc, &q, 1, modulo);
            }
            Some(acc)
        }
        "-" if items.len() == 2 => expr_to_poly(&items[1], var_index, modulo).map(|mut p| {
            for v in p.values_mut() {
                *v = -*v;
                if let Some(m) = modulo {
                    *v = coeff_mod(*v, m);
                }
            }
            p.retain(|_, v| *v != 0);
            p
        }),
        "-" if items.len() == 3 => {
            let pa = expr_to_poly(&items[1], var_index, modulo)?;
            let pb = expr_to_poly(&items[2], var_index, modulo)?;
            Some(poly_add(&pa, &pb, -1, modulo))
        }
        "*" => {
            let mut acc = Poly::from([(Vec::new(), 1i128)]);
            for a in &items[1..] {
                let q = expr_to_poly(a, var_index, modulo)?;
                acc = poly_mul(&acc, &q, modulo);
            }
            Some(acc)
        }
        _ => None,
    }
}

fn poly_to_expr(poly: &Poly, vars: &[Term]) -> Term {
    if poly.is_empty() {
        return atom("0");
    }
    let mut items: Vec<(&Monomial, i128)> = poly.iter().map(|(k, v)| (k, *v)).collect();
    items.sort_by(|a, b| compare_monomials(b.0, a.0));

    let mut terms = Vec::new();
    for (e, c) in items {
        if c == 0 {
            continue;
        }
        let mono_factors: Vec<Term> = e.iter().map(|&idx| vars[idx as usize].clone()).collect();
        let term = if e.is_empty() {
            atom(&c.to_string())
        } else if c == 1 {
            if mono_factors.len() == 1 {
                mono_factors[0].clone()
            } else {
                list("*", mono_factors)
            }
        } else {
            let mut factors = vec![atom(&c.to_string())];
            factors.extend(mono_factors);
            list("*", factors)
        };
        terms.push(term);
    }

    if terms.is_empty() {
        atom("0")
    } else if terms.len() == 1 {
        terms.into_iter().next().unwrap()
    } else {
        list("+", terms)
    }
}

fn poly_diff_poly(
    la: &Term,
    lb: &Term,
    var_index: &HashMap<String, usize>,
    modulo: Option<i128>,
) -> Option<Poly> {
    let pla = expr_to_poly(la, var_index, modulo)?;
    let plb = expr_to_poly(lb, var_index, modulo)?;
    Some(poly_add(&pla, &plb, -1, modulo))
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

fn rescale_monic(poly: Poly, modulo: i128) -> Option<Poly> {
    let lead = lead_exp(&poly);
    let lc = coeff_mod(poly[&lead], modulo);
    if lc == 0 {
        return Some(Poly::new());
    }
    let inv = mod_inverse(lc, modulo)?;
    Some(
        poly.into_iter()
            .filter_map(|(e, c)| {
                let v = coeff_mod(c * inv, modulo);
                if v != 0 { Some((e, v)) } else { None }
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
    let lc = poly[&lead_exp(&poly)];
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

fn relation_poly_diff_plain(
    lhs: &Term,
    rhs: &Term,
    ctx: &NormalizeCtx<'_>,
) -> Option<(Poly, bool)> {
    if contains_bool_symbol(lhs, ctx.bool_symbols)
        || contains_bool_symbol(rhs, ctx.bool_symbols)
    {
        return None;
    }
    if let Some(p) = ctx.field_mod {
        let modular = relation_modular(lhs, rhs, p)?;
        let modulo = if modular { Some(p) } else { None };
        let la = if modular {
            unwrap_field_mod_body(lhs, p)
        } else {
            lhs
        };
        let lb = if modular {
            unwrap_field_mod_body(rhs, p)
        } else {
            rhs
        };
        let diff = poly_diff_poly(la, lb, ctx.var_index, modulo)?;
        return Some((diff, modular));
    }
    let diff = poly_diff_poly(lhs, rhs, ctx.var_index, None)?;
    Some((diff, false))
}

fn wrap_mod_expr(rep: Term, p: i128) -> Term {
    list("mod", vec![rep, atom(&p.to_string())])
}

fn field_eq(rep: Term, p: i128) -> Term {
    list("=", vec![wrap_mod_expr(rep, p), atom("0")])
}

fn normalize_int_rel_gcd(lhs: &Term, rhs: &Term, ctx: &NormalizeCtx<'_>) -> Option<Term> {
    let (diff, modular) = relation_poly_diff_plain(lhs, rhs, ctx)?;
    let rep = if diff.is_empty() {
        atom("0")
    } else if modular {
        poly_to_expr(&rescale_gcd(diff), ctx.vars)
    } else {
        poly_to_expr(&rescale_gcd(diff), ctx.vars)
    };
    if modular {
        Some(wrap_mod_expr(rep, ctx.field_mod?))
    } else {
        Some(rep)
    }
}

fn normalize_equals(lhs: &Term, rhs: &Term, ctx: &NormalizeCtx<'_>) -> Option<Term> {
    let (diff, modular) = relation_poly_diff_plain(lhs, rhs, ctx)?;
    let rep = if diff.is_empty() {
        atom("0")
    } else if modular {
        let p = ctx.field_mod?;
        let scaled = rescale_monic(diff.clone(), p).unwrap_or_else(|| rescale_gcd(diff));
        poly_to_expr(&scaled, ctx.vars)
    } else {
        poly_to_expr(&rescale_gcd(diff), ctx.vars)
    };
    if modular {
        Some(field_eq(rep, ctx.field_mod?))
    } else {
        Some(list("=", vec![rep, atom("0")]))
    }
}

fn normalize_term(term: &Term, ctx: &NormalizeCtx<'_>) -> Term {
    if let Term::List(items) = term {
        if items.len() == 3 {
            if let Some(Term::Atom(head)) = items.first() {
                match head.as_str() {
                    "=" => {
                        if let Some(rep) = normalize_equals(&items[1], &items[2], ctx) {
                            return rep;
                        }
                    }
                    "<" => {
                        if let Some(rep) = normalize_int_rel_gcd(&items[1], &items[2], ctx) {
                            return list("<", vec![rep, atom("0")]);
                        }
                    }
                    "<=" => {
                        if let Some(rep) = normalize_int_rel_gcd(&items[1], &items[2], ctx) {
                            return list("<=", vec![rep, atom("0")]);
                        }
                    }
                    _ => {}
                }
            }
        }
        let head = items[0].clone();
        Term::List(
            std::iter::once(head)
                .chain(items[1..].iter().map(|a| normalize_term(a, ctx)))
                .collect(),
        )
    } else {
        term.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn p() -> i128 {
        field_mod().unwrap_or(2_147_483_647)
    }

    #[test]
    fn field_monic_scales_coeffs() {
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
    fn field_monic_negative_leading_coeff() {
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
}
