use std::collections::HashMap;
use std::str::FromStr;

use smt2::ast_hash_int;

use z3::ast::{Ast, AstKind, Dynamic, Int};
use z3::{SortKind, DeclKind};
use z3_sys::{Z3_get_numeral_string, Z3_is_numeral_ast};

use super::flint::{
    divides_terms, factor_mpoly, BuiltMpoly, Coeff, Monomial, SparsePoly, TermMap,
};
use super::{FactorError, Factorization};

struct GeneratorMap {
    gens: Vec<Int>,
    key: HashMap<u64, usize>,
}

impl GeneratorMap {
    fn new() -> Self {
        Self {
            gens: Vec::new(),
            key: HashMap::new(),
        }
    }

    fn register(&mut self, ast: &Int) -> usize {
        let id = ast_hash_int(ast);
        if let Some(&i) = self.key.get(&id) {
            if self.gens[i].ast_eq(ast) {
                return i;
            }
        }
        let i = self.gens.len();
        self.gens.push(ast.clone());
        self.key.insert(id, i);
        i
    }
}

pub fn factor(expr: &Int) -> Result<Factorization, FactorError> {
    let mut gens = GeneratorMap::new();
    let built = z3_to_fmpz_mpoly(expr, &mut gens)?;
    let flint = factor_mpoly(built)?;
    flint_to_factorization(flint, &gens)
}

/// True iff `divisor` divides `dividend` as integer polynomials. Returns
/// `Ok(false)` if either is not a plain polynomial in Int variables.
pub fn divides(dividend: &Int, divisor: &Int) -> Result<bool, FactorError> {
    let mut gens = GeneratorMap::new();
    let num = match extract_terms(dividend, &mut gens) {
        Ok(t) => t,
        Err(_) => return Ok(false),
    };
    let den = match extract_terms(divisor, &mut gens) {
        Ok(t) => t,
        Err(_) => return Ok(false),
    };
    if num.is_empty() || den.is_empty() {
        return Ok(false);
    }
    divides_terms(&num, &den, gens.gens.len())
}

fn z3_to_fmpz_mpoly(
    expr: &Int,
    gens: &mut GeneratorMap,
) -> Result<BuiltMpoly, FactorError> {
    let terms = extract_terms(expr, gens)?;
    if terms.is_empty() {
        return Err(FactorError::BuildFailed);
    }
    BuiltMpoly::from_terms(&terms, gens.gens.len())
}

unsafe fn set_fmpz_from_z3(z: *mut super::ffi::fmpz, expr: &Int) -> Result<(), FactorError> {
    use super::ffi::{fmpz_set_si, fmpz_set_str};

    if let Some(v) = expr.as_i64() {
        fmpz_set_si(z, v);
        return Ok(());
    }
    let ctx = expr.get_ctx().get_z3_context();
    let ast = expr.get_z3_ast();
    if !Z3_is_numeral_ast(ctx, ast) {
        return Err(FactorError::BuildFailed);
    }
    let ptr = Z3_get_numeral_string(ctx, ast);
    if ptr.is_null() {
        return Err(FactorError::BuildFailed);
    }
    if fmpz_set_str(z, ptr, 10) != 0 {
        return Err(FactorError::BuildFailed);
    }
    Ok(())
}

fn coeff_from_z3(expr: &Int) -> Result<Coeff, FactorError> {
    if let Some(v) = expr.as_i64() {
        return Ok(Coeff::from_i64(v));
    }
    let dyn_ = Dynamic::from_ast(expr);
    if is_int_numeral(&dyn_) {
        let mut c = Coeff::from_i64(0);
        unsafe {
            set_fmpz_from_z3(c.as_mut_ptr(), expr)?;
        }
        return Ok(c);
    }
    if let Some(op) = arithmetic_op(&dyn_) {
        return coeff_from_z3_op(&dyn_, op);
    }
    Err(FactorError::BuildFailed)
}

fn coeff_from_z3_op(dyn_: &Dynamic, op: ArithOp) -> Result<Coeff, FactorError> {
    match op {
        ArithOp::Add => {
            let mut acc = Coeff::from_i64(0);
            for child in dyn_.children() {
                let ch = child.as_int().ok_or(FactorError::BuildFailed)?;
                acc.add_assign(&coeff_from_z3(&ch)?);
            }
            Ok(acc)
        }
        ArithOp::Mul => {
            let mut acc = Coeff::one();
            for child in dyn_.children() {
                let ch = child.as_int().ok_or(FactorError::BuildFailed)?;
                acc = Coeff::mul(&acc, &coeff_from_z3(&ch)?);
            }
            Ok(acc)
        }
        ArithOp::Neg => {
            let child = dyn_
                .children()
                .into_iter()
                .next()
                .ok_or(FactorError::BuildFailed)?;
            let ch = child.as_int().ok_or(FactorError::BuildFailed)?;
            Ok(Coeff::neg(&coeff_from_z3(&ch)?))
        }
        ArithOp::Sub => {
            let kids = dyn_.children();
            if kids.len() != 2 {
                return Err(FactorError::BuildFailed);
            }
            let a = kids[0].as_int().ok_or(FactorError::BuildFailed)?;
            let b = kids[1].as_int().ok_or(FactorError::BuildFailed)?;
            let mut acc = coeff_from_z3(&a)?;
            acc.add_assign(&Coeff::neg(&coeff_from_z3(&b)?));
            Ok(acc)
        }
    }
}

fn flint_to_factorization(
    flint: super::flint::FlintFactorization,
    gens: &GeneratorMap,
) -> Result<Factorization, FactorError> {
    let factors = flint
        .factors
        .into_iter()
        .map(|(s, exp)| sparse_to_z3(&s, gens).map(|z| (z, exp)))
        .collect::<Result<Vec<_>, FactorError>>()?;
    Ok(Factorization { factors })
}

pub fn build_failure_reason(expr: &Int) -> &'static str {
    let mut gens = GeneratorMap::new();
    let terms = match extract_terms(expr, &mut gens) {
        Ok(t) if t.is_empty() => return "zero polynomial",
        Ok(t) => t,
        Err(FactorError::BuildFailed) => return "non-polynomial Z3 subtree (non-Int in +/−/×)",
        Err(FactorError::FactorFailed) => return "internal error during extract",
    };
    match BuiltMpoly::from_terms(&terms, gens.gens.len()) {
        Ok(built) => match factor_mpoly(built) {
            Ok(flint) => {
                for (s, _) in flint.factors {
                    if sparse_to_z3(&s, &gens).is_err() {
                        return "factor coefficient not a plain integer after FLINT round-trip";
                    }
                }
                "unknown build failure"
            }
            Err(FactorError::BuildFailed) => "empty or invalid FLINT input",
            Err(FactorError::FactorFailed) => "factor_failed",
        },
        Err(FactorError::BuildFailed) => "term coefficient is not a plain integer numeral",
        Err(FactorError::FactorFailed) => "internal error during FLINT build",
    }
}

fn extract_terms(expr: &Int, gens: &mut GeneratorMap) -> Result<TermMap, FactorError> {
    let dyn_ = Dynamic::from_ast(expr);
    if is_int_numeral(&dyn_) {
        return Ok(poly_const(coeff_from_z3(expr)?));
    }
    if is_int_var(&dyn_) {
        let idx = gens.register(expr);
        return Ok(poly_generator(idx));
    }
    if let Some(op) = arithmetic_op(&dyn_) {
        return match op {
            ArithOp::Add => {
                let mut acc = TermMap::new();
                for child in dyn_.children() {
                    let c = child.as_int().ok_or(FactorError::BuildFailed)?;
                    acc = poly_add(acc, extract_terms(&c, gens)?);
                }
                Ok(acc)
            }
            ArithOp::Mul => {
                let mut acc = poly_const(Coeff::one());
                for child in dyn_.children() {
                    let c = child.as_int().ok_or(FactorError::BuildFailed)?;
                    acc = poly_mul(acc, extract_terms(&c, gens)?);
                }
                Ok(acc)
            }
            ArithOp::Neg => {
                let child = dyn_
                    .children()
                    .into_iter()
                    .next()
                    .ok_or(FactorError::BuildFailed)?;
                let c = child.as_int().ok_or(FactorError::BuildFailed)?;
                Ok(poly_neg(extract_terms(&c, gens)?))
            }
            ArithOp::Sub => {
                let kids = dyn_.children();
                if kids.len() != 2 {
                    return Err(FactorError::BuildFailed);
                }
                let a = kids[0].as_int().ok_or(FactorError::BuildFailed)?;
                let b = kids[1].as_int().ok_or(FactorError::BuildFailed)?;
                Ok(poly_add(
                    extract_terms(&a, gens)?,
                    poly_neg(extract_terms(&b, gens)?),
                ))
            }
        };
    }
    Err(FactorError::BuildFailed)
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

fn is_int_numeral(ast: &Dynamic) -> bool {
    ast.kind() == AstKind::Numeral && ast.get_sort().kind() == SortKind::Int
}

fn is_int_var(ast: &Dynamic) -> bool {
    ast.kind() == AstKind::App
        && ast.is_const()
        && ast.get_sort().kind() == SortKind::Int
        && !is_int_numeral(ast)
}

fn poly_const(c: Coeff) -> TermMap {
    if c.is_zero() {
        return TermMap::new();
    }
    let mut p = TermMap::new();
    p.insert(Monomial::new(), c);
    p
}

fn poly_generator(idx: usize) -> TermMap {
    let mut mono = Monomial::new();
    mono.insert(idx, 1);
    let mut p = TermMap::new();
    p.insert(mono, Coeff::one());
    p
}

fn poly_add(mut a: TermMap, b: TermMap) -> TermMap {
    for (m, c) in b {
        match a.get_mut(&m) {
            Some(existing) => {
                existing.add_assign(&c);
                if existing.is_zero() {
                    a.remove(&m);
                }
            }
            None => {
                a.insert(m, c);
            }
        }
    }
    a
}

fn poly_neg(mut a: TermMap) -> TermMap {
    for c in a.values_mut() {
        *c = Coeff::neg(c);
    }
    a
}

fn poly_mul(a: TermMap, b: TermMap) -> TermMap {
    if a.is_empty() || b.is_empty() {
        return TermMap::new();
    }
    let mut out = TermMap::new();
    for (ma, ca) in &a {
        for (mb, cb) in &b {
            let mut m = ma.clone();
            for (g, e) in mb {
                *m.entry(*g).or_insert(0) += e;
            }
            let c = Coeff::mul(ca, cb);
            match out.get_mut(&m) {
                Some(existing) => {
                    existing.add_assign(&c);
                    if existing.is_zero() {
                        out.remove(&m);
                    }
                }
                None => {
                    out.insert(m, c);
                }
            }
        }
    }
    out
}

fn int_from_coeff_str(s: &str) -> Result<Int, FactorError> {
    if let Ok(v) = s.parse::<i64>() {
        return Ok(Int::from_i64(v));
    }
    Int::from_str(s).map_err(|_| FactorError::BuildFailed)
}

fn sparse_to_z3(sparse: &SparsePoly, gens: &GeneratorMap) -> Result<Int, FactorError> {
    let mut terms = Vec::with_capacity(sparse.terms.len());
    for (coeff_str, exp) in &sparse.terms {
        let mut factors = vec![int_from_coeff_str(coeff_str)?];
        for (i, &e) in exp.iter().enumerate() {
            if e == 0 {
                continue;
            }
            let g = gens.gens.get(i).ok_or(FactorError::BuildFailed)?;
            if e == 1 {
                factors.push(g.clone());
            } else {
                let mut power = g.clone();
                for _ in 1..e {
                    power = Int::mul(&[&power, g]);
                }
                factors.push(power);
            }
        }
        terms.push(if factors.len() == 1 {
            factors.pop().unwrap()
        } else {
            Int::mul(&factors)
        });
    }
    if terms.len() == 1 {
        Ok(terms.pop().unwrap())
    } else {
        Ok(Int::add(&terms))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn int_add(a: &Int, b: &Int) -> Int {
        Int::add(&[a, b]).simplify()
    }

    fn int_mul(a: &Int, b: &Int) -> Int {
        Int::mul(&[a, b]).simplify()
    }

    #[test]
    fn factors_univariate() {
        let x = Int::new_const("x");
        let p = int_add(&int_mul(&x, &x), &Int::from_i64(-1));
        let fac = factor(&p).expect("factor");
        assert!(fac.factor_count() >= 2);
    }

    #[test]
    fn factors_product_form() {
        let x = Int::new_const("x");
        let p = int_mul(&x, &Int::sub(&[&x, &Int::from_i64(1)]));
        let fac = factor(&p).expect("factor");
        assert!(fac.factor_count() >= 2);
    }

    #[test]
    fn factors_large_constant_product() {
        let x = Int::new_const("x");
        let c = Int::mul(&[
            &Int::from_str("486388759756013568000").unwrap(),
            &Int::from_str("61847529062400").unwrap(),
        ]);
        let p = int_mul(&c, &x);
        factor(&p).expect("factor large coeff");
    }

    #[test]
    fn factors_nested_constant_product_without_simplify() {
        let x = Int::new_const("x");
        let c = Int::mul(&[
            &Int::from_str("486388759756013568000").unwrap(),
            &Int::from_str("61847529062400").unwrap(),
        ]);
        let p = Int::mul(&[&c, &x]);
        factor(&p).expect("factor nested constant mul");
    }

    #[test]
    fn rejects_non_polynomial_subtrees() {
        let x = Int::new_const("x");
        let g = x.div(&Int::from_i64(2));
        let p = int_add(&int_mul(&g, &x), &Int::from_i64(1));
        assert!(matches!(factor(&p), Err(FactorError::BuildFailed)));
    }
}
