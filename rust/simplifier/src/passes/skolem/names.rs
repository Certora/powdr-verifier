use std::collections::HashMap;

use smt2::Term;

use super::map::SkolemMap;
use super::term_util::{is_program_variable, strip_prefix, symbol_name};
use super::types::SortKind;

pub fn contribute(map: &mut SkolemMap, declared: &HashMap<String, Term>, sorts: &HashMap<String, SortKind>) {
    for q in map.qvars.clone() {
        if map.is_pinned(&q) {
            continue;
        }
        if !is_program_variable(&q) {
            continue;
        }
        let stripped = strip_prefix(&q).to_string();
        let Some(other) = declared.get(&stripped) else {
            continue;
        };
        let other_name = symbol_name(other).unwrap_or("");
        if other_name == q || map.qvars.contains(other_name) {
            continue;
        }
        let q_sort = sorts.get(&q).copied().unwrap_or(SortKind::Other);
        let o_sort = sorts.get(other_name).copied().unwrap_or(SortKind::Other);
        if q_sort != o_sort {
            continue;
        }
        map.pin(&q, other.clone(), "names");
    }
}
