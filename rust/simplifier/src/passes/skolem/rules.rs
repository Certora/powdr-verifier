//! OpenVM ``EqualZeroCheck`` free-variable pins (``contribute_free``).

use std::collections::{HashMap, HashSet};

use smt2::ast_util::{int_from_i128, symbol_id_from_name, symbol_name_for_id, SymbolId};
use smt2::{iter_nodes_dyn, symbol_name_dyn, Script};
use z3::ast::{Bool, Dynamic, Int};

use smt2::{strip_prefix, swap_prefix};

pub fn contribute_free(
    script: &Script,
    qvars: &HashSet<SymbolId>,
    field: i128,
) -> Vec<(String, Dynamic)> {
    let declared = collect_declared(script);
    let free_diff_vals: Vec<String> = declared
        .iter()
        .filter(|name| {
            strip_prefix(name).starts_with("diff_val")
                && !qvars.contains(&symbol_id_from_name(name))
        })
        .cloned()
        .collect();
    if free_diff_vals.is_empty() {
        return Vec::new();
    }

    let qvar_diff_vals: Vec<String> = qvars
        .iter()
        .filter_map(|id| symbol_name_for_id(*id))
        .filter(|name| strip_prefix(name).starts_with("diff_val"))
        .collect();
    if qvar_diff_vals.is_empty() {
        return Vec::new();
    }

    let Some(forall_body) = find_forall_body(script) else {
        return Vec::new();
    };

    let qvar_results = find_and_build_witnesses(&forall_body, &qvar_diff_vals, field);
    let mut stripped_to_match: HashMap<String, MatchBundle> = HashMap::new();
    for (dv, bundle) in qvar_results {
        stripped_to_match.insert(strip_prefix(&dv).to_string(), bundle);
    }

    let mut pins = Vec::new();
    for free_dv in free_diff_vals {
        let stripped = strip_prefix(&free_dv).to_string();
        let Some(bundle) = stripped_to_match.get(&stripped) else {
            continue;
        };
        let free_matches = swap_matches(&bundle.matches, &declared);
        let free_cmp = swap_sym(&bundle.cmp, &declared);
        let skolem = build_skolem(&free_matches, &free_cmp, field);
        pins.push((free_dv, skolem));
        for (dm_var, dm_skolem) in build_marker_skolems(&free_matches) {
            if !qvars.contains(&symbol_id_from_name(&dm_var)) {
                pins.push((dm_var, dm_skolem));
            }
        }
    }
    pins
}

struct MatchBundle {
    matches: HashMap<u32, LimbMatch>,
    cmp: String,
}

struct LimbMatch {
    dm: String,
    data: String,
    data_offset: i128,
    cmp: String,
}

fn collect_declared(script: &Script) -> HashSet<String> {
    let mut out = HashSet::new();
    for cmd in &script.commands {
        if let Some(name) = super::utils::declare_fun_name(cmd, &script.source) {
            out.insert(name);
        }
    }
    out
}

fn find_forall_body(script: &Script) -> Option<Bool> {
    for cmd in &script.commands {
        if let Some(body) = cmd.assert_bool() {
            for node in iter_nodes_dyn(&Dynamic::from_ast(body)) {
                if let Some((_, _, b)) = super::utils::parse_forall(&node) {
                    return Some(b);
                }
            }
        }
    }
    None
}

fn swap_sym(sym: &str, declared: &HashSet<String>) -> String {
    swap_prefix(sym)
        .filter(|s| declared.contains(s))
        .unwrap_or_else(|| sym.to_string())
}

fn swap_matches(
    matches: &HashMap<u32, LimbMatch>,
    declared: &HashSet<String>,
) -> HashMap<u32, LimbMatch> {
    matches
        .iter()
        .map(|(idx, m)| {
            (
                *idx,
                LimbMatch {
                    dm: swap_sym(&m.dm, declared),
                    data: swap_sym(&m.data, declared),
                    data_offset: m.data_offset,
                    cmp: swap_sym(&m.cmp, declared),
                },
            )
        })
        .collect()
}

fn find_and_build_witnesses(
    body: &Bool,
    diff_val_vars: &[String],
    field: i128,
) -> Vec<(String, MatchBundle)> {
    let mut results = Vec::new();
    for dv in diff_val_vars {
        if let Some(bundle) = openvm_bundle_from_named_limbs(body, dv, field) {
            results.push((dv.clone(), bundle));
        }
    }
    results
}

fn openvm_bundle_from_named_limbs(body: &Bool, dv: &str, field: i128) -> Option<MatchBundle> {
    let g = diff_val_gadget(dv)?;
    let row = b_row_suffix(g);
    let cmp_prefix = format!("cmp_result_{g}@");

    let mut cmp_sym = None;
    let mut dms: HashMap<u32, String> = HashMap::new();
    let mut bs: HashMap<u32, String> = HashMap::new();

    for node in iter_nodes_dyn(&Dynamic::from_ast(body)) {
        let Some(name) = symbol_name_dyn(&node) else {
            continue;
        };
        let st = strip_prefix(&name);
        if st.starts_with(&cmp_prefix) {
            cmp_sym = Some(name.clone());
        }
        if let Some(rest) = st.strip_prefix("diff_marker__") {
            if let Some((limb, suffix)) = rest.split_once('_') {
                if suffix.starts_with(&format!("{g}@")) {
                    if let Ok(i) = limb.parse::<u32>() {
                        dms.insert(i, name.clone());
                    }
                }
            }
        }
        if let Some(rest) = st.strip_prefix("b__") {
            if let Some((limb, suffix)) = rest.split_once('_') {
                if suffix.starts_with(&format!("{row}@")) {
                    if let Ok(i) = limb.parse::<u32>() {
                        bs.insert(i, name.clone());
                    }
                }
            }
        }
    }

    let cmp = cmp_sym?;
    if dms.len() != 4 || bs.len() != 4 {
        return None;
    }
    let mut matches = HashMap::new();
    for i in 0..4 {
        let off = if i == 0 { (field - 1).rem_euclid(field) } else { 0 };
        matches.insert(
            i,
            LimbMatch {
                dm: dms[&i].clone(),
                data: bs[&i].clone(),
                data_offset: off,
                cmp: cmp.clone(),
            },
        );
    }
    Some(MatchBundle { matches, cmp })
}

fn diff_val_gadget(sym: &str) -> Option<u32> {
    let n = strip_prefix(sym);
    let start = n.find("diff_val_")?;
    let rest = &n[start + "diff_val_".len()..];
    let digits: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
    digits.parse().ok()
}

fn b_row_suffix(gadget: u32) -> u32 {
    if gadget == 0 {
        0
    } else {
        2 * (gadget - 1)
    }
}

fn build_skolem(matches: &HashMap<u32, LimbMatch>, cmp: &str, p: i128) -> Dynamic {
    let sign = Int::add(&[
        &int_from_i128(p - 1),
        &Int::mul(&[&int_from_i128(2), &Int::new_const(cmp)]),
    ]);
    let mut expr = int_from_i128(0);
    let m0 = &matches[&0];
    expr = Int::new_const(m0.data.as_str()).eq(&int_from_i128(1)).ite(
        &expr,
        &smt2::wrap_mod_expr_int(
            Int::mul(&[
                &Int::add(&[
                    &int_from_i128(1),
                    &Int::mul(&[&int_from_i128(p - 1), &Int::new_const(m0.data.as_str())]),
                ]),
                &sign,
            ]),
            p,
        ),
    );
    for i in 1..=3 {
        let m = &matches[&i];
        expr = Int::new_const(m.data.as_str()).eq(&int_from_i128(0)).ite(
            &expr,
            &smt2::wrap_mod_expr_int(
                Int::mul(&[
                    &int_from_i128(p - 1),
                    &Int::new_const(m.data.as_str()),
                    &sign,
                ]),
                p,
            ),
        );
    }
    Dynamic::from_ast(&smt2::wrap_mod_expr_int(expr, p))
}

fn build_marker_skolems(matches: &HashMap<u32, LimbMatch>) -> Vec<(String, Dynamic)> {
    let b0 = &matches[&0].data;
    let b1 = &matches[&1].data;
    let b2 = &matches[&2].data;
    let b3 = &matches[&3].data;
    let eq3 = Int::new_const(b3.as_str()).eq(&int_from_i128(0));
    let eq2 = Int::new_const(b2.as_str()).eq(&int_from_i128(0));
    let eq1 = Int::new_const(b1.as_str()).eq(&int_from_i128(0));
    let eq0 = Int::new_const(b0.as_str()).eq(&int_from_i128(1));
    let dm3 = eq3.ite(&int_from_i128(0), &int_from_i128(1));
    let dm2 = eq3.ite(
        &int_from_i128(0),
        &eq2.ite(&int_from_i128(0), &int_from_i128(1)),
    );
    let dm1 = eq3.ite(
        &int_from_i128(0),
        &eq2.ite(
            &eq1.ite(&int_from_i128(0), &int_from_i128(1)),
            &int_from_i128(0),
        ),
    );
    let dm0 = eq3.ite(
        &int_from_i128(0),
        &eq2.ite(
            &eq1.ite(
                &eq0.ite(&int_from_i128(0), &int_from_i128(1)),
                &int_from_i128(0),
            ),
            &int_from_i128(0),
        ),
    );
    vec![
        (matches[&0].dm.clone(), Dynamic::from_ast(&dm0)),
        (matches[&1].dm.clone(), Dynamic::from_ast(&dm1)),
        (matches[&2].dm.clone(), Dynamic::from_ast(&dm2)),
        (matches[&3].dm.clone(), Dynamic::from_ast(&dm3)),
    ]
}
