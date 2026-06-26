use std::collections::BTreeMap;
use std::mem::MaybeUninit;

use flint_sys::flint::fmpz;
use flint_sys::fmpz::{
    fmpz_add, fmpz_clear, fmpz_get_str, fmpz_init, fmpz_is_zero, fmpz_mul, fmpz_neg, fmpz_set_si,
};
use flint_sys::fmpz_mpoly::{
    fmpz_mpoly_clear, fmpz_mpoly_combine_like_terms, fmpz_mpoly_ctx_clear, fmpz_mpoly_ctx_init,
    fmpz_mpoly_get_term_coeff_fmpz, fmpz_mpoly_get_term_exp_ui, fmpz_mpoly_init,
    fmpz_mpoly_is_zero, fmpz_mpoly_length, fmpz_mpoly_push_term_fmpz_ui, fmpz_mpoly_sort_terms,
    fmpz_mpoly_zero,
};
use flint_sys::fmpz_mpoly_factor::{
    fmpz_mpoly_factor, fmpz_mpoly_factor_clear, fmpz_mpoly_factor_get_base,
    fmpz_mpoly_factor_get_exp_si, fmpz_mpoly_factor_init, fmpz_mpoly_factor_length,
};
use flint_sys::mpoly_types::{fmpz_mpoly_ctx_struct, ordering_t_ORD_LEX};

use super::FactorError;

pub(crate) type Monomial = BTreeMap<usize, u32>;
pub(crate) type TermMap = BTreeMap<Monomial, Coeff>;

pub(crate) struct Coeff {
    z: fmpz,
}

impl Coeff {
    pub(crate) fn from_i64(v: i64) -> Self {
        let mut c = Self::new();
        unsafe {
            fmpz_set_si(&mut c.z, v);
        }
        c
    }

    pub(crate) fn one() -> Self {
        Self::from_i64(1)
    }

    fn new() -> Self {
        let mut z = 0i64;
        unsafe {
            fmpz_init(&mut z);
        }
        Self { z }
    }

    pub(crate) fn as_ptr(&self) -> *const fmpz {
        &self.z
    }

    pub(crate) fn as_mut_ptr(&mut self) -> *mut fmpz {
        &mut self.z
    }

    pub(crate) fn is_zero(&self) -> bool {
        unsafe { fmpz_is_zero(&self.z) != 0 }
    }

    pub(crate) fn add_assign(&mut self, other: &Self) {
        unsafe {
            fmpz_add(&mut self.z, &self.z, &other.z);
        }
    }

    pub(crate) fn mul(a: &Self, b: &Self) -> Self {
        let mut out = Self::new();
        unsafe {
            fmpz_mul(&mut out.z, a.as_ptr(), b.as_ptr());
        }
        out
    }

    pub(crate) fn neg(a: &Self) -> Self {
        let mut out = Self::new();
        unsafe {
            fmpz_neg(&mut out.z, a.as_ptr());
        }
        out
    }
}

impl Drop for Coeff {
    fn drop(&mut self) {
        unsafe {
            fmpz_clear(&mut self.z);
        }
    }
}

pub(crate) struct SparsePoly {
    pub terms: Vec<(String, Vec<u32>)>,
}

pub(crate) struct FlintFactorization {
    pub factors: Vec<(SparsePoly, usize)>,
}

pub(crate) struct BuiltMpoly {
    ctx: ZzCtx,
    poly: MpolyInner,
    pub nvars: usize,
}

struct MpolyInner(flint_sys::fmpz_types::fmpz_mpoly_struct);

impl BuiltMpoly {
    pub fn from_terms(terms: &TermMap, nvars: usize) -> Result<Self, FactorError> {
        if nvars == 0 || terms.is_empty() {
            return Err(FactorError::BuildFailed);
        }
        let ctx = ZzCtx::new(nvars);
        let mut poly = MpolyInner::new(&ctx);
        unsafe {
            build_fmpz_mpoly_from_terms(poly.as_mut(), ctx.as_ptr(), nvars, terms)?;
        }
        Ok(Self {
            ctx,
            poly,
            nvars,
        })
    }

    fn ctx_ptr(&self) -> *const fmpz_mpoly_ctx_struct {
        self.ctx.as_ptr()
    }

    fn poly(&self) -> *const flint_sys::fmpz_types::fmpz_mpoly_struct {
        self.poly.as_ptr()
    }
}

impl Drop for BuiltMpoly {
    fn drop(&mut self) {
        unsafe {
            fmpz_mpoly_clear(self.poly.as_mut(), self.ctx.as_ptr());
        }
    }
}

impl MpolyInner {
    fn new(ctx: &ZzCtx) -> Self {
        let mut poly = MaybeUninit::<flint_sys::fmpz_types::fmpz_mpoly_struct>::uninit();
        unsafe {
            fmpz_mpoly_init(poly.as_mut_ptr(), ctx.as_ptr());
            Self(poly.assume_init())
        }
    }

    fn as_ptr(&self) -> *const flint_sys::fmpz_types::fmpz_mpoly_struct {
        &self.0
    }

    fn as_mut(&mut self) -> *mut flint_sys::fmpz_types::fmpz_mpoly_struct {
        &mut self.0
    }
}

pub(crate) fn factor_mpoly(built: BuiltMpoly) -> Result<FlintFactorization, FactorError> {
    let nvars = built.nvars;
    let ctx_ptr = built.ctx_ptr();
    let poly_ptr = built.poly();
    unsafe {
        let mut fac = MaybeUninit::<flint_sys::fmpz_types::fmpz_mpoly_factor_struct>::uninit();
        fmpz_mpoly_factor_init(fac.as_mut_ptr(), ctx_ptr);
        let mut fac = fac.assume_init();
        if fmpz_mpoly_factor(&mut fac, poly_ptr, ctx_ptr) == 0 {
            fmpz_mpoly_factor_clear(&mut fac, ctx_ptr);
            return Err(FactorError::FactorFailed);
        }
        let out = read_fmpz_mpoly_factor(&fac, ctx_ptr, nvars)?;
        fmpz_mpoly_factor_clear(&mut fac, ctx_ptr);
        Ok(out)
    }
}

struct ZzCtx {
    ctx: fmpz_mpoly_ctx_struct,
}

impl ZzCtx {
    fn new(nvars: usize) -> Self {
        let mut ctx = MaybeUninit::<fmpz_mpoly_ctx_struct>::uninit();
        unsafe {
            fmpz_mpoly_ctx_init(ctx.as_mut_ptr(), nvars as i64, ordering_t_ORD_LEX);
            Self {
                ctx: ctx.assume_init(),
            }
        }
    }

    fn as_ptr(&self) -> *const fmpz_mpoly_ctx_struct {
        &self.ctx
    }
}

impl Drop for ZzCtx {
    fn drop(&mut self) {
        unsafe {
            fmpz_mpoly_ctx_clear(&mut self.ctx);
        }
    }
}

unsafe fn build_fmpz_mpoly_from_terms(
    poly: *mut flint_sys::fmpz_types::fmpz_mpoly_struct,
    ctx: *const fmpz_mpoly_ctx_struct,
    nvars: usize,
    terms: &TermMap,
) -> Result<(), FactorError> {
    fmpz_mpoly_zero(poly, ctx);

    for (mono, coeff) in terms {
        let mut exps = vec![0u64; nvars];
        for (&g, &e) in mono {
            if g >= nvars {
                return Err(FactorError::BuildFailed);
            }
            exps[g] = e as u64;
        }
        fmpz_mpoly_push_term_fmpz_ui(poly, coeff.as_ptr(), exps.as_ptr(), ctx);
    }
    fmpz_mpoly_combine_like_terms(poly, ctx);
    fmpz_mpoly_sort_terms(poly, ctx);
    Ok(())
}

unsafe fn read_fmpz_mpoly_factor(
    fac: &flint_sys::fmpz_types::fmpz_mpoly_factor_struct,
    ctx: *const fmpz_mpoly_ctx_struct,
    nvars: usize,
) -> Result<FlintFactorization, FactorError> {
    let len = fmpz_mpoly_factor_length(fac, ctx);
    let mut factors = Vec::with_capacity(len as usize);
    for i in 0..len {
        let exp = fmpz_mpoly_factor_get_exp_si(fac as *const _ as *mut _, i, ctx).max(0) as usize;
        let mut base = MaybeUninit::<flint_sys::fmpz_types::fmpz_mpoly_struct>::uninit();
        fmpz_mpoly_init(base.as_mut_ptr(), ctx);
        let mut base = base.assume_init();
        fmpz_mpoly_factor_get_base(&mut base, fac, i, ctx);
        let sparse = fmpz_mpoly_to_sparse(&base, ctx, nvars)?;
        fmpz_mpoly_clear(&mut base, ctx);
        factors.push((sparse, exp));
    }
    Ok(FlintFactorization { factors })
}

unsafe fn fmpz_mpoly_to_sparse(
    poly: &flint_sys::fmpz_types::fmpz_mpoly_struct,
    ctx: *const fmpz_mpoly_ctx_struct,
    nvars: usize,
) -> Result<SparsePoly, FactorError> {
    if fmpz_mpoly_is_zero(poly, ctx) != 0 {
        return Ok(SparsePoly { terms: vec![] });
    }
    let n = fmpz_mpoly_length(poly, ctx);
    let mut terms = Vec::with_capacity(n as usize);
    let mut coeff = 0i64;
    fmpz_init(&mut coeff);
    let mut exps = vec![0u64; nvars];
    for i in 0..n {
        fmpz_mpoly_get_term_exp_ui(exps.as_mut_ptr(), poly, i, ctx);
        fmpz_mpoly_get_term_coeff_fmpz(&mut coeff, poly, i, ctx);
        let coeff_str = fmpz_to_string(&coeff);
        let exp: Vec<u32> = exps.iter().map(|&e| e as u32).collect();
        if coeff_str != "0" {
            terms.push((coeff_str, exp));
        }
    }
    fmpz_clear(&mut coeff);
    Ok(SparsePoly { terms })
}

fn fmpz_to_string(x: &fmpz) -> String {
    use std::ffi::CStr;
    unsafe {
        let ptr = fmpz_get_str(std::ptr::null_mut(), 10, x);
        if ptr.is_null() {
            return "0".to_string();
        }
        let s = CStr::from_ptr(ptr).to_string_lossy().into_owned();
        flint_sys::flint::flint_free(ptr as *mut _);
        s
    }
}
