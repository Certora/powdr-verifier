use std::collections::HashMap;

use smt2::strip_prefix;

use super::types::SortKind;

pub fn field_mod() -> Option<i128> {
    std::env::var("SIMPLIFIER_FIELD_MOD")
        .ok()
        .and_then(|s| s.parse().ok())
}

pub fn is_program_variable(name: &str) -> bool {
    strip_prefix(name).contains('@')
}

pub fn symbol_sort(name: &str, sorts: &HashMap<String, SortKind>) -> SortKind {
    sorts.get(name).copied().unwrap_or(SortKind::Other)
}
