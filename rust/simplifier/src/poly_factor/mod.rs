//! Multivariate polynomial factorization via FLINT, with Z3 expression I/O.

mod ffi;
mod flint;
mod z3_poly;

use z3::ast::Int;

pub use z3_poly::{build_failure_reason, divides, factor};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FactorError {
    BuildFailed,
    FactorFailed,
}

#[derive(Debug, Clone)]
pub struct Factorization {
    pub factors: Vec<(Int, usize)>,
}

impl Factorization {
    pub fn factor_count(&self) -> usize {
        self.factors.iter().map(|(_, m)| m).sum()
    }
}
