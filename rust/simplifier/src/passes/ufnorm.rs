//! ufnorm: ground mod-P-invariance connection axioms for bitwise-table ufs.
//!
//! ``z3-solve-eqs``'s ``solve_mod`` substitutes ``u := P*mod!k + y`` through
//! uf arguments, so the premise/goal twin applications of an inlining step
//! stop matching syntactically and every congruence step needs an integer
//! quotient side-proof. For each application ``f(a1,..,an)`` of ``uf_xor`` /
//! ``uf_and`` / ``uf_or`` with a non-canonical argument, assert the ground
//! connection axiom::
//!
//!     f(a1,..,an) = f(canon(a1),..,canon(an))
//!
//! where ``canon(a)`` is ``a``'s linear form with coefficients reduced into
//! ``[0,P)`` (dropping P-multiple summands — exactly the ``mod!`` witnesses),
//! atoms sorted, wrapped in ``(mod . P)``. The tables are only consulted on
//! field-reduced values, so mod-P invariance is a granted environment fact
//! (like assume_bytes / TS_BOUND). Congruence closure merges each pair at
//! assert time, and premise- and goal-side applications meet at the SAME
//! canonical term — measured: this alone moves 2100224 completeness from
//! never-closing to ~32s on the plain disjunct checker (axioms-only ablation
//! = full-rewrite performance, so occurrences are left untouched).

use std::collections::{HashMap, HashSet};

use smt2::ast_util::{int_from_i128, int_value_dyn, rebuild_app};
use smt2::{decl_name, is_int_const, Script, SmtCommand};
use z3::ast::{Ast, AstKind, Bool, Dynamic, Int};
use z3::DeclKind;
// DeclKind is used for the arithmetic-node dispatch in atoms_add / canon_arg
// (Add/Sub/Uminus/Mul/Mod); table-uf detection is name-only (see is_table_uf).

use crate::expr_util::{rebuild_script, AssertBuildCtx};
use crate::passes::demod::field_mod;

fn is_table_uf(d: &Dynamic) -> bool {
    // name-only match, like bitwise.rs::uf_binary_dyn — DeclKind does not
    // report Uninterpreted reliably through this binding
    d.kind() == AstKind::App
        && matches!(
            decl_name(&d.decl()).as_str(),
            "uf_xor" | "uf_and" | "uf_or"
        )
}

/// Collect every distinct table-uf application under the given roots.
fn collect_apps(roots: &[Bool]) -> Vec<Dynamic> {
    let mut visited: HashSet<Dynamic> = HashSet::new();
    let mut out: Vec<Dynamic> = Vec::new();
    let mut stack: Vec<Dynamic> = roots.iter().map(|b| Dynamic::from_ast(b)).collect();
    while let Some(n) = stack.pop() {
        if n.kind() == AstKind::Quantifier {
            continue;
        }
        if !visited.insert(n.clone()) {
            continue;
        }
        if is_table_uf(&n) {
            out.push(n.clone());
        }
        for i in 0..n.num_children() {
            if let Some(ch) = n.nth_child(i) {
                stack.push(ch);
            }
        }
    }
    out
}

/// ``e`` as ``({atom: coeff}, const)`` treating non-arithmetic subterms
/// (uf applications, mod terms, symbols, ...) as atoms — the atoms variant
/// of demod's ``linear_form``, which bails on non-arith nodes.
fn linear_atoms(e: &Int) -> Option<(HashMap<Int, i128>, i128)> {
    let mut terms = HashMap::new();
    let mut const_ = 0i128;
    if atoms_add(1, e, &mut terms, &mut const_) {
        Some((terms, const_))
    } else {
        None
    }
}

fn atoms_add(c: i128, e: &Int, terms: &mut HashMap<Int, i128>, const_: &mut i128) -> bool {
    let d = Dynamic::from_ast(e);
    if let Some(v) = int_value_dyn(&d) {
        match c.checked_mul(v).and_then(|cv| const_.checked_add(cv)) {
            Some(x) => {
                *const_ = x;
                return true;
            }
            None => return false,
        }
    }
    if d.kind() != AstKind::App {
        *terms.entry(e.clone()).or_insert(0) += c;
        return true;
    }
    match d.decl().kind() {
        DeclKind::Add => d
            .children()
            .into_iter()
            .all(|ch| ch.as_int().map(|i| atoms_add(c, &i, terms, const_)).unwrap_or(false)),
        DeclKind::Uminus if d.num_children() == 1 => d
            .nth_child(0)
            .and_then(|ch| ch.as_int())
            .map(|i| atoms_add(-c, &i, terms, const_))
            .unwrap_or(false),
        DeclKind::Sub if d.num_children() == 2 => {
            let a = d.nth_child(0).and_then(|ch| ch.as_int());
            let b = d.nth_child(1).and_then(|ch| ch.as_int());
            match (a, b) {
                (Some(a), Some(b)) => {
                    atoms_add(c, &a, terms, const_) && atoms_add(-c, &b, terms, const_)
                }
                _ => false,
            }
        }
        DeclKind::Mul => {
            let mut k = 1i128;
            let mut rest: Option<Int> = None;
            for ch in d.children() {
                if let Some(v) = int_value_dyn(&ch) {
                    k = match k.checked_mul(v) {
                        Some(x) => x,
                        None => return false,
                    };
                    continue;
                }
                if let Some(i) = ch.as_int() {
                    if rest.is_some() {
                        // non-linear product: the whole node is an atom
                        *terms.entry(e.clone()).or_insert(0) += c;
                        return true;
                    }
                    rest = Some(i);
                } else {
                    return false;
                }
            }
            match rest {
                Some(r) => match c.checked_mul(k) {
                    Some(ck) => atoms_add(ck, &r, terms, const_),
                    None => false,
                },
                None => {
                    *const_ += c * k;
                    true
                }
            }
        }
        _ => {
            // atom: uninterpreted application, mod term, ite, ...
            *terms.entry(e.clone()).or_insert(0) += c;
            true
        }
    }
}

/// Canonical form of a uf argument, or ``None`` if already canonical /
/// not canonicalizable. See the module docs.
fn canon_arg(arg: &Int, p: i128) -> Option<Int> {
    let d = Dynamic::from_ast(arg);
    if is_int_const(&d) {
        return None; // bare symbol: canonical as-is
    }
    if let Some(v) = int_value_dyn(&d) {
        let r = v.rem_euclid(p);
        return if r == v { None } else { Some(int_from_i128(r)) };
    }
    if d.kind() != AstKind::App {
        return None;
    }
    let inner: Int = if d.decl().kind() == DeclKind::Mod && d.num_children() == 2 {
        let m = d.nth_child(1).and_then(|c| int_value_dyn(&c));
        if m != Some(p) {
            return None; // foreign modulus: leave alone
        }
        d.nth_child(0)?.as_int()?
    } else {
        arg.clone()
    };
    let (terms, konst) = linear_atoms(&inner)?;
    let mut items: Vec<(Int, i128)> = terms
        .into_iter()
        .filter_map(|(atom, c)| {
            let r = c.rem_euclid(p);
            (r != 0).then_some((atom, r))
        })
        .collect();
    items.sort_by_cached_key(|(atom, _)| atom.to_string());
    let mut parts: Vec<Int> = items
        .into_iter()
        .map(|(atom, c)| {
            if c == 1 {
                atom
            } else {
                Int::mul(&[&int_from_i128(c), &atom])
            }
        })
        .collect();
    let kr = konst.rem_euclid(p);
    if kr != 0 {
        parts.push(int_from_i128(kr));
    }
    let inner_canon = match parts.len() {
        0 => int_from_i128(0),
        1 => parts.pop().unwrap(),
        _ => Int::add(&parts.iter().collect::<Vec<_>>()),
    };
    let canon = inner_canon.modulo(&int_from_i128(p));
    if canon == *arg {
        return None;
    }
    Some(canon)
}

pub fn apply(script: &Script) -> Result<(Script, serde_json::Value), String> {
    let Some(p) = field_mod() else {
        return Err("ufnorm: field modulus not configured".to_string());
    };
    let roots: Vec<Bool> = script
        .commands
        .iter()
        .filter_map(|cmd| cmd.assert_bool().map(|b| b.clone()))
        .collect();
    let apps = collect_apps(&roots);
    let mut axioms: Vec<Bool> = Vec::new();
    let mut canonicalized = 0usize;
    for app in &apps {
        let mut changed = false;
        let mut new_args: Vec<Dynamic> = Vec::new();
        for i in 0..app.num_children() {
            let Some(ch) = app.nth_child(i) else { continue };
            match ch.as_int().and_then(|ci| canon_arg(&ci, p)) {
                Some(c) => {
                    changed = true;
                    new_args.push(Dynamic::from_ast(&c));
                }
                None => new_args.push(ch),
            }
        }
        if !changed {
            continue;
        }
        canonicalized += 1;
        let refs: Vec<&dyn Ast> = new_args.iter().map(|a| a as &dyn Ast).collect();
        let canon_app = rebuild_app(&app.decl(), &refs);
        axioms.push(app._eq(&canon_app));
    }

    let n_apps = apps.len();
    if axioms.is_empty() {
        return Ok((
            script.clone(),
            serde_json::json!({
                "apps_seen": n_apps,
                "apps_canonicalized": 0,
                "connection_axioms_added": 0,
            }),
        ));
    }

    let mut ctx = AssertBuildCtx::from_script(script)?;
    let mut out: Vec<SmtCommand> = Vec::new();
    let mut inserted = false;
    for cmd in &script.commands {
        if !inserted && cmd.assert_bool().is_some() {
            for ax in &axioms {
                ctx.push_assert(&mut out, ax)?;
            }
            inserted = true;
        }
        if let Some(b) = cmd.assert_bool() {
            ctx.push_assert(&mut out, b)?;
        } else {
            out.push(cmd.clone());
        }
    }

    Ok((
        rebuild_script(&script.source, out),
        serde_json::json!({
            "apps_seen": n_apps,
            "apps_canonicalized": canonicalized,
            "connection_axioms_added": axioms.len(),
        }),
    ))
}
