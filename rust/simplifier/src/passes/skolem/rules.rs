//! OpenVM ``EqualZeroCheck`` free-variable pins (``contribute_free``) and
//! ``IsZero`` (``diff_inv_marker``) quantified-witness pins (``contribute``).

use std::collections::{HashMap, HashSet};

use smt2::ast_util::{int_from_i128, symbol_id_from_name, symbol_name_for_id, SymbolId};
use smt2::wrap_mod_expr_int;
use smt2::{iter_nodes_dyn, symbol_name_dyn, Script};
use z3::ast::{Ast, Bool, Dynamic, Int};

use smt2::{strip_prefix, swap_prefix};

use super::map::SkolemMap;

/// Pin OpenVM ``IsZero`` (``diff_inv_marker``) witnesses on ``skolem`` from the
/// forall ``body``.
///
/// powdr's ``FreeVariableCombinationCandidate`` rewrite (see
/// `constraint-solver/src/rule_based_optimizer/rules.rs`) recognises the IsZero
/// constraint ``Σ aᵢ·diff_inv_marker__i_g = cmp_result_g`` — where each
/// ``diff_inv_marker__i_g`` occurs only in this one constraint — and replaces
/// the markers with a single fresh ``free_var = QuotientOrZero(cmp_result, Σaᵢ)``
/// (the after side is pinned via that substitution). On the side that keeps the
/// markers they stay quantified with no same-name / substitution / derived pin,
/// so lifting cannot eliminate the forall and the solver sees a spurious model.
///
/// Because each marker occurs only in that constraint, a valid witness for
/// *every* marker of a gadget is the same ``QuotientOrZero(cmp_result, Σaᵢ)``
/// value — identical to the after ``free_var``.
///
/// We prefer to pin the markers to the after-side ``free_var`` *variable*
/// itself: it survives as a declared, range-bounded variable that the after
/// constraints pin via ``Σ(after-aᵢ)·free_var = after-cmp``. Since the a-limbs
/// and cmp are same-name-pinned (before==after), that makes the before-side
/// constraint ``Σ(before-aᵢ)·marker = before-cmp`` provably hold — with no
/// unconstrained ``uf_mod_inv`` for the solver to exploit. If we cannot locate
/// the after ``free_var`` (e.g. it was substituted away), we fall back to
/// rendering the value directly like the encoder's free_var substitution:
///   ``ite(mod(Σaᵢ)=0, 0, mod(cmp_result)·uf_mod_inv(mod(Σaᵢ)))``
/// Instantiating a universally-quantified variable is always sound, so either
/// witness can only fail to close a case, never cause a false PASS.
pub fn contribute(skolem: &mut SkolemMap, script: &Script, body: &Bool, field: i128) {
    // Names of the quantified diff_inv_marker variables we may witness.
    let marker_names: HashMap<String, SymbolId> = skolem
        .qvars
        .iter()
        .filter_map(|id| symbol_name_for_id(*id).map(|n| (n, *id)))
        .filter(|(n, _)| strip_prefix(n).contains("diff_inv_marker__"))
        .collect();
    if marker_names.is_empty() {
        return;
    }
    let marker_set: HashSet<&String> = marker_names.keys().collect();

    // Find each constraint `(= (mod SUM p) 0)` whose SUM has marker factors;
    // for each, witness every marker in it with QuotientOrZero(-r, factor),
    // where `factor` is the sum of the markers' cofactors and `r` is the rest.
    for node in iter_nodes_dyn(&Dynamic::from_ast(body)) {
        let Some(b) = node.as_bool() else { continue };
        let Some(sum) = smt2::ast_util::unwrap_zero_mod_eq(&b, field) else {
            continue;
        };
        let summands = smt2::ast_build::flatten_op_int("+", &sum);
        let mut factor_terms: Vec<Int> = Vec::new();
        let mut rest_terms: Vec<Int> = Vec::new();
        let mut markers_here: Vec<SymbolId> = Vec::new();
        // a-limb symbol names that each multiply a marker (i.e. products
        // `a__i_g · marker_i` with a single non-marker symbol factor). These
        // let us locate the after-side `free_var` that multiplies the same
        // a-limbs on the constrained side.
        let mut a_limb_names: Vec<String> = Vec::new();
        let mut bail = false;
        for s in &summands {
            let (coeff, factors) = smt2::ast_build::split_product_int(s, field);
            let mut marker_idx = None;
            for (i, f) in factors.iter().enumerate() {
                if let Some(fname) = symbol_name_dyn(&Dynamic::from_ast(f)) {
                    if marker_set.contains(&fname) {
                        if marker_idx.is_some() {
                            bail = true; // two markers in one product: unexpected
                        }
                        marker_idx = Some((i, fname));
                    }
                }
            }
            match marker_idx {
                None => rest_terms.push(s.clone()),
                Some((mi, mname)) => {
                    // cofactor of the marker = coeff * (other factors)
                    let mut cof = int_from_i128(coeff);
                    let mut other_syms: Vec<String> = Vec::new();
                    for (i, f) in factors.iter().enumerate() {
                        if i != mi {
                            cof = Int::mul(&[&cof, f]);
                            if let Some(nm) = symbol_name_dyn(&Dynamic::from_ast(f)) {
                                other_syms.push(nm);
                            }
                        }
                    }
                    // Pure `a__i_g · marker_i`: cofactor is exactly one symbol.
                    if coeff == 1 && factors.len() == 2 && other_syms.len() == 1 {
                        a_limb_names.push(other_syms.into_iter().next().unwrap());
                    }
                    factor_terms.push(cof);
                    if let Some(id) = marker_names.get(&mname) {
                        markers_here.push(*id);
                    }
                }
            }
        }
        if bail || markers_here.is_empty() {
            continue;
        }

        // Prefer the constrained after-side `free_var` variable (no
        // unconstrained inverse). Any a-limb identifies the gadget's free_var,
        // since it multiplies every after-a-limb on the constrained side.
        let free_var = a_limb_names
            .first()
            .and_then(|n| swap_prefix(n))
            .and_then(|after_a| find_after_free_var(script, &after_a, field));

        let (witness, source) = match free_var {
            Some(fv) => (
                Dynamic::from_ast(&Int::new_const(fv.as_str())),
                "rules-inv-marker-freevar",
            ),
            None => {
                let factor = wrap_mod_expr_int(sum_or_zero(&factor_terms), field);
                let r = sum_or_zero(&rest_terms);
                // -r mod p
                let neg_r = wrap_mod_expr_int(Int::sub(&[&int_from_i128(0), &r]), field);
                // QuotientOrZero(-r, factor) = ite(factor==0, 0, (-r)·uf_mod_inv(factor))
                let prod = Int::mul(&[&neg_r, &uf_mod_inv(&factor)]);
                let w = factor.eq(&int_from_i128(0)).ite(&int_from_i128(0), &prod);
                (Dynamic::from_ast(&w), "rules-inv-marker")
            }
        };
        for id in markers_here {
            skolem.pin(id, witness.clone(), source);
        }
    }
}

fn sum_or_zero(terms: &[Int]) -> Int {
    if terms.is_empty() {
        int_from_i128(0)
    } else {
        Int::add(&terms.iter().collect::<Vec<_>>())
    }
}

fn uf_mod_inv(arg: &Int) -> Int {
    let s = arg.get_sort();
    let decl = z3::FuncDecl::new("uf_mod_inv", &[&s], &s);
    decl.apply(&[arg]).as_int().unwrap_or_else(|| arg.clone())
}

/// Find the after-side ``free_var`` symbol introduced by powdr's
/// ``FreeVariableCombinationCandidate`` rewrite for this gadget.
///
/// The rewrite replaces the marker constraint with ``Σ(after-aᵢ)·free_var =
/// after-cmp`` (plus a ``0 ≤ free_var < p`` range bound). We locate that
/// constraint by the given after-a-limb: a product with a single-symbol factor
/// named ``free_var…`` whose remaining factors reference ``a_limb_after``. This
/// matches both the factored ``free_var·(Σ aᵢ)`` shape (raw input) and the
/// distributed ``Σ (aᵢ·free_var)`` shape (post-simplify). Because ``free_var``
/// is genuinely constrained (not a substituted ``uf_mod_inv`` term), pinning the
/// markers to it yields a witness the solver cannot cheat.
fn find_after_free_var(script: &Script, a_limb_after: &str, field: i128) -> Option<String> {
    for cmd in &script.commands {
        let Some(body) = cmd.assert_bool() else {
            continue;
        };
        for node in iter_nodes_dyn(&Dynamic::from_ast(body)) {
            let Some(b) = node.as_bool() else { continue };
            let Some(sum) = smt2::ast_util::unwrap_zero_mod_eq(&b, field) else {
                continue;
            };
            for s in smt2::ast_build::flatten_op_int("+", &sum) {
                let (_coeff, factors) = smt2::ast_build::split_product_int(&s, field);
                // A single-symbol `free_var…` factor.
                let fv = factors.iter().find_map(|f| {
                    symbol_name_dyn(&Dynamic::from_ast(f))
                        .filter(|n| strip_prefix(n).starts_with("free_var"))
                });
                let Some(fv) = fv else { continue };
                // The a-limb must appear somewhere else in this product.
                let refs_a = factors.iter().any(|f| {
                    iter_nodes_dyn(&Dynamic::from_ast(f))
                        .any(|nd| symbol_name_dyn(&nd).as_deref() == Some(a_limb_after))
                });
                if refs_a {
                    return Some(fv);
                }
            }
        }
    }
    None
}

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

    // `rows` maps each gadget to its data (`b__i_row`) row (derived from the
    // constraints, not a fixed formula); `constrained` records which
    // (side, gadget) still carry the comparison gadget's DiffMarkerConstraints.
    let (rows, constrained) = gadget_scan(script, field);

    let qvar_results = find_and_build_witnesses(&forall_body, &qvar_diff_vals, field, &rows);
    let mut stripped_to_match: HashMap<String, MatchBundle> = HashMap::new();
    for (dv, bundle) in qvar_results {
        stripped_to_match.insert(strip_prefix(&dv).to_string(), bundle);
    }

    let mut pins = Vec::new();
    for free_dv in free_diff_vals {
        // Soundness: only witness genuinely-unconstrained *leftover* columns —
        // those whose comparison gadget was rewritten away on this side. The
        // free var is always on the assume side; if its DiffMarkerConstraints
        // are still present there (`constrained`), pinning it to a witness
        // would ADD a constraint to an already-constrained variable and could
        // make the assume side unsatisfiable, i.e. a spurious UNSAT / false
        // PASS. Pinning is sound only for the rewrite's leftovers.
        let Some(g) = diff_val_gadget(&free_dv) else {
            continue;
        };
        if constrained.contains(&(name_prefix(&free_dv).to_string(), g)) {
            continue;
        }
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

/// Prefix (`before-`/`after-`) of a two-circuit column name, or `""`.
fn name_prefix(name: &str) -> &str {
    for p in ["before-", "after-"] {
        if name.starts_with(p) {
            return p;
        }
    }
    ""
}

/// Parse a ``diff_marker__<limb>_<gadget>@id`` name into ``(gadget, limb)``.
fn parse_diff_marker(name: &str) -> Option<(u32, u32)> {
    let rest = strip_prefix(name).strip_prefix("diff_marker__")?;
    let (limb, suffix) = rest.split_once('_')?;
    let g: u32 = suffix.split('@').next()?.parse().ok()?;
    Some((g, limb.parse().ok()?))
}

/// Parse a ``cmp_result_<gadget>@id`` name into ``gadget``.
fn parse_cmp_result(name: &str) -> Option<u32> {
    strip_prefix(name)
        .strip_prefix("cmp_result_")?
        .split('@')
        .next()?
        .parse()
        .ok()
}

/// Parse a ``b__<limb>_<row>@id`` name into ``(limb, row)``.
fn parse_b_limb(name: &str) -> Option<(u32, u32)> {
    let rest = strip_prefix(name).strip_prefix("b__")?;
    let (limb, suffix) = rest.split_once('_')?;
    let row: u32 = suffix.split('@').next()?.parse().ok()?;
    Some((limb.parse().ok()?, row))
}

/// Scan the script for the two facts contribute_free needs:
///   * `rows`: gadget -> data (`b__i_row`) row. Both the comparison gadget's
///     DiffMarkerConstraint and the rewrite's inv_of_sum constraint bind
///     `cmp_result_g` with a single `b__*_row` in one `(= (mod … p) 0)`, so
///     the row is read off that co-occurrence rather than guessed from `g`.
///   * `constrained`: `(prefix, gadget)` pairs whose DiffMarkerConstraints
///     (single `diff_marker` factor) are still present — i.e. NOT a leftover.
fn gadget_scan(script: &Script, field: i128) -> (HashMap<u32, u32>, HashSet<(String, u32)>) {
    let mut rows: HashMap<u32, u32> = HashMap::new();
    let mut constrained: HashSet<(String, u32)> = HashSet::new();
    for cmd in &script.commands {
        let Some(body) = cmd.assert_bool() else {
            continue;
        };
        for node in iter_nodes_dyn(&Dynamic::from_ast(body)) {
            let Some(b) = node.as_bool() else { continue };
            let Some(sum) = smt2::ast_util::unwrap_zero_mod_eq(&b, field) else {
                continue;
            };
            // rows: one gadget's cmp_result + one consistent data row.
            let mut gadget: Option<u32> = None;
            let mut row: Option<u32> = None;
            let mut ok = true;
            for nd in iter_nodes_dyn(&Dynamic::from_ast(&sum)) {
                let Some(nm) = symbol_name_dyn(&nd) else {
                    continue;
                };
                if let Some(g) = parse_cmp_result(&nm) {
                    match gadget {
                        None => gadget = Some(g),
                        Some(x) if x != g => ok = false,
                        _ => {}
                    }
                }
                if let Some((_, r)) = parse_b_limb(&nm) {
                    match row {
                        None => row = Some(r),
                        Some(x) if x != r => ok = false,
                        _ => {}
                    }
                }
            }
            if ok {
                if let (Some(g), Some(r)) = (gadget, row) {
                    rows.entry(g).or_insert(r);
                }
            }
            // constrained: a DiffMarkerConstraint has exactly one diff_marker
            // top-level factor (the boolean `Σdm·(Σdm−1)=0` has them in sums).
            let (_c, factors) = smt2::ast_build::split_product_int(&sum, field);
            let mut marker: Option<(String, u32)> = None;
            let mut count = 0;
            for f in &factors {
                if let Some(nm) = symbol_name_dyn(&Dynamic::from_ast(f)) {
                    if let Some((g, _)) = parse_diff_marker(&nm) {
                        count += 1;
                        marker = Some((name_prefix(&nm).to_string(), g));
                    }
                }
            }
            if count == 1 {
                constrained.insert(marker.unwrap());
            }
        }
    }
    (rows, constrained)
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
    rows: &HashMap<u32, u32>,
) -> Vec<(String, MatchBundle)> {
    let mut results = Vec::new();
    for dv in diff_val_vars {
        if let Some(bundle) = openvm_bundle_from_named_limbs(body, dv, field, rows) {
            results.push((dv.clone(), bundle));
        }
    }
    results
}

fn openvm_bundle_from_named_limbs(
    body: &Bool,
    dv: &str,
    field: i128,
    rows: &HashMap<u32, u32>,
) -> Option<MatchBundle> {
    let g = diff_val_gadget(dv)?;
    let row = *rows.get(&g)?;
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
        if let Some((gg, i)) = parse_diff_marker(&name) {
            if gg == g {
                dms.insert(i, name.clone());
            }
        }
        if let Some((i, r)) = parse_b_limb(&name) {
            if r == row {
                bs.insert(i, name.clone());
            }
        }
    }

    let cmp = cmp_sym?;
    if dms.len() != 4 || bs.len() != 4 {
        return None;
    }
    let mut matches = HashMap::new();
    for i in 0..4 {
        let off = if i == 0 {
            (field - 1).rem_euclid(field)
        } else {
            0
        };
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
