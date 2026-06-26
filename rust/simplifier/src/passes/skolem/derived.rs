use super::map::SkolemMap;
use super::types::SkolemPin;
use super::utils::split_equation;

pub fn contribute(map: &mut SkolemMap, pins: &[SkolemPin]) {
    for pin in pins {
        let Some((var, expr)) = split_equation(&pin.equation) else {
            continue;
        };
        if map.qvars.contains(&var) && !map.is_pinned(&var) {
            map.pin(&var, expr, &pin.kind);
        }
    }
}
