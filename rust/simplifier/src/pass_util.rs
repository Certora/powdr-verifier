//! Shared non-Z3 helpers for simplifier passes.

use crate::passes::skolem::types::SortKind;

pub fn field_mod() -> Option<i128> {
    std::env::var("SIMPLIFIER_FIELD_MOD")
        .ok()
        .and_then(|s| s.parse().ok())
}

pub fn sort_from_decl(raw: &str) -> SortKind {
    if raw.contains("(Array") || raw.contains(" Array ") {
        SortKind::Array
    } else if raw.contains("Bool") {
        SortKind::Bool
    } else if raw.contains("Int") {
        SortKind::Int
    } else {
        SortKind::Other
    }
}
