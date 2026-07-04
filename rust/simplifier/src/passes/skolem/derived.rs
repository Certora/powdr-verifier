use smt2::ast_util::symbol_id_from_name;

use super::map::SkolemMap;
use super::types::SkolemPin;
use super::utils::split_equation;

pub fn contribute(map: &mut SkolemMap, pins: &[SkolemPin]) {
    for pin in pins {
        let Some((var, expr)) = split_equation(&pin.equation) else {
            continue;
        };
        let var_id = symbol_id_from_name(&var);
        if map.qvars.contains(&var_id) && !map.is_pinned(var_id) {
            map.pin(var_id, expr, &pin.kind);
        }
    }
}
