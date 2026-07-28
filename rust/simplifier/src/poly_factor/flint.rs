use std::collections::BTreeMap;
use std::mem::MaybeUninit;

use super::ffi::{
    flint_free, fmpz, fmpz_add, fmpz_clear, fmpz_get_str, fmpz_init, fmpz_is_zero,
    fmpz_mod_mpoly_clear, fmpz_mod_mpoly_combine_like_terms, fmpz_mod_mpoly_ctx_clear,
    fmpz_mod_mpoly_ctx_init, fmpz_mod_mpoly_ctx_struct, fmpz_mod_mpoly_divides,
    fmpz_mod_mpoly_factor, fmpz_mod_mpoly_factor_clear, fmpz_mod_mpoly_factor_get_base,
    fmpz_mod_mpoly_factor_get_exp_si, fmpz_mod_mpoly_factor_init, fmpz_mod_mpoly_factor_length,
    fmpz_mod_mpoly_factor_struct, fmpz_mod_mpoly_get_term_coeff_fmpz,
    fmpz_mod_mpoly_get_term_exp_ui, fmpz_mod_mpoly_init, fmpz_mod_mpoly_is_zero,
    fmpz_mod_mpoly_length, fmpz_mod_mpoly_push_term_fmpz_ui, fmpz_mod_mpoly_sort_terms,
    fmpz_mod_mpoly_struct, fmpz_mod_mpoly_zero, fmpz_mul, fmpz_neg, fmpz_set_si,
    ordering_t_ORD_LEX,
};

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
    ctx: ZpCtx,
    poly: MpolyInner,
    pub nvars: usize,
}

struct MpolyInner(fmpz_mod_mpoly_struct);

impl BuiltMpoly {
    pub fn from_terms(terms: &TermMap, nvars: usize, modulus: u64) -> Result<Self, FactorError> {
        if nvars == 0 || terms.is_empty() {
            return Err(FactorError::BuildFailed);
        }
        let ctx = ZpCtx::new(nvars, modulus);
        let mut poly = MpolyInner::new(&ctx);
        unsafe {
            build_mpoly_from_terms(poly.as_mut(), ctx.as_ptr(), nvars, terms)?;
        }
        Ok(Self { ctx, poly, nvars })
    }

    fn ctx_ptr(&self) -> *const fmpz_mod_mpoly_ctx_struct {
        self.ctx.as_ptr()
    }

    fn poly(&self) -> *const fmpz_mod_mpoly_struct {
        self.poly.as_ptr()
    }
}

impl Drop for BuiltMpoly {
    fn drop(&mut self) {
        unsafe {
            fmpz_mod_mpoly_clear(self.poly.as_mut(), self.ctx.as_ptr());
        }
    }
}

impl MpolyInner {
    fn new(ctx: &ZpCtx) -> Self {
        let mut poly = MaybeUninit::<fmpz_mod_mpoly_struct>::uninit();
        unsafe {
            fmpz_mod_mpoly_init(poly.as_mut_ptr(), ctx.as_ptr());
            Self(poly.assume_init())
        }
    }

    fn as_ptr(&self) -> *const fmpz_mod_mpoly_struct {
        &self.0
    }

    fn as_mut(&mut self) -> *mut fmpz_mod_mpoly_struct {
        &mut self.0
    }
}

/// True iff `divisor` divides `dividend` over GF(`modulus`) (both built in a
/// shared context so generator indices align). Used by the `factor_reduce`
/// pass; divisibility over the field is exactly the `B | Q => Q = 0 (mod P)`
/// implication that pass relies on.
pub(crate) fn divides_terms(
    dividend: &TermMap,
    divisor: &TermMap,
    nvars: usize,
    modulus: u64,
) -> Result<bool, FactorError> {
    if nvars == 0 || dividend.is_empty() || divisor.is_empty() {
        return Err(FactorError::BuildFailed);
    }
    let ctx = ZpCtx::new(nvars, modulus);
    let mut num = MpolyInner::new(&ctx);
    let mut den = MpolyInner::new(&ctx);
    let mut quo = MpolyInner::new(&ctx);
    let divides = unsafe {
        build_mpoly_from_terms(num.as_mut(), ctx.as_ptr(), nvars, dividend)?;
        build_mpoly_from_terms(den.as_mut(), ctx.as_ptr(), nvars, divisor)?;
        let r = fmpz_mod_mpoly_divides(quo.as_mut(), num.as_ptr(), den.as_ptr(), ctx.as_ptr());
        fmpz_mod_mpoly_clear(num.as_mut(), ctx.as_ptr());
        fmpz_mod_mpoly_clear(den.as_mut(), ctx.as_ptr());
        fmpz_mod_mpoly_clear(quo.as_mut(), ctx.as_ptr());
        r != 0
    };
    Ok(divides)
}

pub(crate) fn factor_mpoly(built: BuiltMpoly) -> Result<FlintFactorization, FactorError> {
    let nvars = built.nvars;
    let ctx_ptr = built.ctx_ptr();
    let poly_ptr = built.poly();
    unsafe {
        let mut fac = MaybeUninit::<fmpz_mod_mpoly_factor_struct>::uninit();
        fmpz_mod_mpoly_factor_init(fac.as_mut_ptr(), ctx_ptr);
        let mut fac = fac.assume_init();
        if fmpz_mod_mpoly_factor(&mut fac, poly_ptr, ctx_ptr) == 0 {
            fmpz_mod_mpoly_factor_clear(&mut fac, ctx_ptr);
            return Err(FactorError::FactorFailed);
        }
        let out = read_mpoly_factor(&fac, ctx_ptr, nvars)?;
        fmpz_mod_mpoly_factor_clear(&mut fac, ctx_ptr);
        Ok(out)
    }
}

/// A polynomial context over GF(`modulus`). The modulus must be prime for the
/// factorization to be well-defined (the BabyBear field prime here).
struct ZpCtx {
    ctx: fmpz_mod_mpoly_ctx_struct,
    modulus: fmpz,
}

impl ZpCtx {
    fn new(nvars: usize, modulus: u64) -> Self {
        let mut m: fmpz = 0;
        let mut ctx = MaybeUninit::<fmpz_mod_mpoly_ctx_struct>::uninit();
        unsafe {
            fmpz_init(&mut m);
            // BabyBear P < 2^31, so it fits in an i64.
            fmpz_set_si(&mut m, modulus as i64);
            fmpz_mod_mpoly_ctx_init(ctx.as_mut_ptr(), nvars as i64, ordering_t_ORD_LEX, &m);
            Self {
                ctx: ctx.assume_init(),
                modulus: m,
            }
        }
    }

    fn as_ptr(&self) -> *const fmpz_mod_mpoly_ctx_struct {
        &self.ctx
    }
}

impl Drop for ZpCtx {
    fn drop(&mut self) {
        unsafe {
            fmpz_mod_mpoly_ctx_clear(&mut self.ctx);
            fmpz_clear(&mut self.modulus);
        }
    }
}

unsafe fn build_mpoly_from_terms(
    poly: *mut fmpz_mod_mpoly_struct,
    ctx: *const fmpz_mod_mpoly_ctx_struct,
    nvars: usize,
    terms: &TermMap,
) -> Result<(), FactorError> {
    fmpz_mod_mpoly_zero(poly, ctx);

    for (mono, coeff) in terms {
        let mut exps = vec![0u64; nvars];
        for (&g, &e) in mono {
            if g >= nvars {
                return Err(FactorError::BuildFailed);
            }
            exps[g] = e as u64;
        }
        // Coefficients are plain integers (possibly negative or >= P); the
        // modular context reduces them mod P on insertion, so any coefficient
        // representation of the same GF(P) polynomial factors identically.
        fmpz_mod_mpoly_push_term_fmpz_ui(poly, coeff.as_ptr(), exps.as_ptr(), ctx);
    }
    fmpz_mod_mpoly_combine_like_terms(poly, ctx);
    fmpz_mod_mpoly_sort_terms(poly, ctx);
    Ok(())
}

unsafe fn read_mpoly_factor(
    fac: &fmpz_mod_mpoly_factor_struct,
    ctx: *const fmpz_mod_mpoly_ctx_struct,
    nvars: usize,
) -> Result<FlintFactorization, FactorError> {
    let len = fmpz_mod_mpoly_factor_length(fac, ctx);
    let mut factors = Vec::with_capacity(len as usize);
    for i in 0..len {
        let exp =
            fmpz_mod_mpoly_factor_get_exp_si(fac as *const _ as *mut _, i, ctx).max(0) as usize;
        let mut base = MaybeUninit::<fmpz_mod_mpoly_struct>::uninit();
        fmpz_mod_mpoly_init(base.as_mut_ptr(), ctx);
        let mut base = base.assume_init();
        fmpz_mod_mpoly_factor_get_base(&mut base, fac, i, ctx);
        let sparse = mpoly_to_sparse(&base, ctx, nvars)?;
        fmpz_mod_mpoly_clear(&mut base, ctx);
        factors.push((sparse, exp));
    }
    Ok(FlintFactorization { factors })
}

unsafe fn mpoly_to_sparse(
    poly: &fmpz_mod_mpoly_struct,
    ctx: *const fmpz_mod_mpoly_ctx_struct,
    nvars: usize,
) -> Result<SparsePoly, FactorError> {
    if fmpz_mod_mpoly_is_zero(poly, ctx) != 0 {
        return Ok(SparsePoly { terms: vec![] });
    }
    let n = fmpz_mod_mpoly_length(poly, ctx);
    let mut terms = Vec::with_capacity(n as usize);
    let mut coeff = 0i64;
    fmpz_init(&mut coeff);
    let mut exps = vec![0u64; nvars];
    for i in 0..n {
        fmpz_mod_mpoly_get_term_exp_ui(exps.as_mut_ptr(), poly, i, ctx);
        fmpz_mod_mpoly_get_term_coeff_fmpz(&mut coeff, poly, i, ctx);
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
        flint_free(ptr as *mut _);
        s
    }
}
