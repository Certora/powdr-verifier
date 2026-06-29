use std::collections::HashMap;

use z3::ast::{Bool, Dynamic, Int};

use super::map::SkolemMap;
use smt2::strip_prefix;

use super::ast_build::is_program_variable;
use super::types::SortKind;

pub fn contribute(
    map: &mut SkolemMap,
    declared: &HashMap<String, String>,
    sorts: &HashMap<String, SortKind>,
) {
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
        let other_name = other.as_str();
        if other_name == q || map.qvars.contains(other_name) {
            continue;
        }
        let q_sort = sorts.get(&q).copied().unwrap_or(SortKind::Other);
        let o_sort = sorts.get(other_name).copied().unwrap_or(SortKind::Other);
        if q_sort != o_sort {
            continue;
        }
        let pinned = match q_sort {
            SortKind::Bool => Dynamic::from_ast(&Bool::new_const(other_name)),
            _ => Dynamic::from_ast(&Int::new_const(other_name)),
        };
        map.pin(&q, pinned, "names");
    }
}
