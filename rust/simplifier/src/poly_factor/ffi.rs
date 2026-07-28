//! FLINT FFI backend, selected at compile time.
//!
//! Two maintained crates bind the FLINT C library. They expose the *same* C
//! API but organize the Rust bindings differently, and both set
//! `links = "flint"` — so Cargo forbids declaring both at once, and exactly
//! one is a dependency in any given build (see simplifier/Cargo.toml):
//!
//! * default → `flint-sys` 0.9: bindings split across per-header submodules
//!   (`flint_sys::fmpz`, `::fmpz_mpoly`, …). This is the owners' backend and
//!   what Linux/CI builds. It does NOT compile on macOS ARM64: its bindgen
//!   layout tests hard-code the Linux struct layout, and `pthread_mutex_t` is
//!   64 bytes on Darwin vs 40 on Linux (the fields are `libc`-typed so the
//!   real FFI layout is fine — only the baked-in tests are wrong).
//! * `flint3` feature → `flint3-sys` 3.6: a single flat module with no layout
//!   tests; builds on macOS out of the box. Selected by
//!   `patches/flint3-macos.patch` + `--features flint3` (see `just build-osx`).
//!
//! Both crates are ABI-type-compatible for our uses on LP64 targets
//! (`fmpz = slong = c_long = i64`, `ulong = c_ulong = u64`), so the rest of
//! `poly_factor` is backend-agnostic: it imports every symbol from here.

// We factor over GF(P) (prime field), not over Z: `fmpz_mod_mpoly_*` with the
// field modulus. Factoring over Z fails on polynomials whose factorization only
// exists mod P -- e.g. `L*(L-1)` after `normalize` rewrites coefficients to
// positive mod-P residues (`-2` -> `P-2`), which is irreducible over Z.
#[cfg(not(feature = "flint3"))]
pub(crate) use flint_sys::{
    flint::{flint_free, fmpz},
    fmpz::{
        fmpz_add, fmpz_clear, fmpz_get_str, fmpz_init, fmpz_is_zero, fmpz_mul, fmpz_neg,
        fmpz_set_si, fmpz_set_str,
    },
    fmpz_mod_mpoly::{
        fmpz_mod_mpoly_clear, fmpz_mod_mpoly_combine_like_terms, fmpz_mod_mpoly_ctx_clear,
        fmpz_mod_mpoly_ctx_init, fmpz_mod_mpoly_divides, fmpz_mod_mpoly_get_term_coeff_fmpz,
        fmpz_mod_mpoly_get_term_exp_ui, fmpz_mod_mpoly_init, fmpz_mod_mpoly_is_zero,
        fmpz_mod_mpoly_length, fmpz_mod_mpoly_push_term_fmpz_ui, fmpz_mod_mpoly_sort_terms,
        fmpz_mod_mpoly_zero,
    },
    fmpz_mod_mpoly_factor::{
        fmpz_mod_mpoly_factor, fmpz_mod_mpoly_factor_clear, fmpz_mod_mpoly_factor_get_base,
        fmpz_mod_mpoly_factor_get_exp_si, fmpz_mod_mpoly_factor_init,
        fmpz_mod_mpoly_factor_length,
    },
    fmpz_mod_types::{fmpz_mod_mpoly_factor_struct, fmpz_mod_mpoly_struct},
    mpoly_types::{fmpz_mod_mpoly_ctx_struct, ordering_t_ORD_LEX},
};

#[cfg(feature = "flint3")]
pub(crate) use flint3_sys::{
    flint_free, fmpz, fmpz_add, fmpz_clear, fmpz_get_str, fmpz_init, fmpz_is_zero,
    fmpz_mod_mpoly_clear, fmpz_mod_mpoly_combine_like_terms, fmpz_mod_mpoly_ctx_clear,
    fmpz_mod_mpoly_ctx_init, fmpz_mod_mpoly_ctx_struct, fmpz_mod_mpoly_divides,
    fmpz_mod_mpoly_factor, fmpz_mod_mpoly_factor_clear, fmpz_mod_mpoly_factor_get_base,
    fmpz_mod_mpoly_factor_get_exp_si, fmpz_mod_mpoly_factor_init, fmpz_mod_mpoly_factor_length,
    fmpz_mod_mpoly_factor_struct, fmpz_mod_mpoly_get_term_coeff_fmpz,
    fmpz_mod_mpoly_get_term_exp_ui, fmpz_mod_mpoly_init, fmpz_mod_mpoly_is_zero,
    fmpz_mod_mpoly_length, fmpz_mod_mpoly_push_term_fmpz_ui, fmpz_mod_mpoly_sort_terms,
    fmpz_mod_mpoly_struct, fmpz_mod_mpoly_zero, fmpz_mul, fmpz_neg, fmpz_set_si, fmpz_set_str,
    ordering_t_ORD_LEX,
};
