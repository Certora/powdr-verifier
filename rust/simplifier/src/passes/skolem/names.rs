use std::collections::HashMap;

use smt2::ast_util::{symbol_id_from_name, symbol_name_for_id};
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
        if map.is_pinned(q) {
            continue;
        }
        let Some(q_name) = symbol_name_for_id(q) else {
            continue;
        };
        if !is_program_variable(&q_name) {
            continue;
        }
        let stripped = strip_prefix(&q_name).to_string();
        let Some(other) = declared.get(&stripped) else {
            continue;
        };
        let other_name = other.as_str();
        if other_name == q_name || map.qvars.contains(&symbol_id_from_name(other_name)) {
            continue;
        }
        let q_sort = sorts.get(&q_name).copied().unwrap_or(SortKind::Other);
        let o_sort = sorts.get(other_name).copied().unwrap_or(SortKind::Other);
        if q_sort != o_sort {
            continue;
        }
        let pinned = match q_sort {
            SortKind::Bool => Dynamic::from_ast(&Bool::new_const(other_name)),
            _ => Dynamic::from_ast(&Int::new_const(other_name)),
        };
        map.pin(q, pinned, "names");
    }
}
