//! FLINT bindings via `flint3-sys` (builds on Linux and macOS, unlike `flint-sys`).

// We factor over GF(P) (prime field), not over Z: `fmpz_mod_mpoly_*` with the
// field modulus. Factoring over Z fails on polynomials whose factorization only
// exists mod P -- e.g. `L*(L-1)` after `normalize` rewrites coefficients to
// positive mod-P residues (`-2` -> `P-2`), which is irreducible over Z.
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
