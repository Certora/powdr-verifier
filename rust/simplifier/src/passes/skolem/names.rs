use std::collections::HashMap;

use smt2::ast_util::{swap_prefix, symbol_id_from_name, symbol_name_for_id};
use z3::ast::{Bool, Dynamic, Int};

use super::map::SkolemMap;
use smt2::strip_prefix;

use super::ast_build::is_program_variable;
use super::types::SortKind;

pub fn contribute(
    map: &mut SkolemMap,
    declared: &HashMap<String, Vec<String>>,
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
        let Some(candidates) = declared.get(&stripped) else {
            continue;
        };
        // Prefer the opposite-side copy explicitly: granted membus axioms
        // mention the quantified side's columns at top level, so BOTH sides'
        // symbols can be declared and the qvar's own declaration must not
        // shadow its partner.
        let viable: Vec<&String> = candidates
            .iter()
            .filter(|n| {
                n.as_str() != q_name && !map.qvars.contains(&symbol_id_from_name(n))
            })
            .collect();
        let partner = swap_prefix(&q_name);
        let Some(other) = viable
            .iter()
            .find(|n| Some(n.as_str()) == partner.as_deref())
            .or_else(|| viable.first())
        else {
            continue;
        };
        let other_name = other.as_str();
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
