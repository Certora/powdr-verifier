//! Grounded lemmas for ``uf_xor`` / ``uf_and`` / ``uf_or``.

use std::collections::HashSet;

use smt2::ast_util::{ast_hash_bool, decl_name, int_from_i128, int_value_dyn};
use smt2::{map_asserts, IntTermSet, Script};
use z3::ast::{Ast, AstKind, Bool, Dynamic, Int};

use crate::expr_util::AssertBuildCtx;

const UF_XOR: &str = "uf_xor";
const UF_AND: &str = "uf_and";
const UF_OR: &str = "uf_or";

#[derive(Default, Clone)]
struct BitwiseTerms {
    xors: IntTermSet,
    ands: IntTermSet,
    ors: IntTermSet,
}

#[derive(Default)]
struct BitwiseStats {
    seen_xor: usize,
    seen_and: usize,
    seen_or: usize,
    emitted_xor: usize,
    emitted_and: usize,
    emitted_or: usize,
    emitted_link: usize,
}

pub fn apply(script: &Script) -> Result<(Script, serde_json::Value), String> {
    let mut stats = BitwiseStats::default();
    let mut seen_axioms: HashSet<u64> = HashSet::new();
    let mut top_axioms: Vec<Bool> = Vec::new();
    let folded = map_asserts(script, |b| {
        let folded = fold_bitwise_bool(b);
        let terms = collect_bitwise_terms(&folded);
        stats.seen_xor += terms.xors.len();
        stats.seen_and += terms.ands.len();
        stats.seen_or += terms.ors.len();
        for axiom in emit_axioms(&terms, &mut stats) {
            if seen_axioms.insert(ast_hash_bool(&axiom)) {
                top_axioms.push(axiom);
            }
        }
        Ok(folded)
    })?;

    if top_axioms.is_empty() {
        return Ok((
            folded,
            serde_json::json!({
                "top_level_bitwise_axiom_asserts": 0,
                "bitwise_stats": stats_payload(&stats),
            }),
        ));
    }

    let insert_idx = folded
        .commands
        .iter()
        .position(|c| c.name() == "check-sat")
        .unwrap_or(folded.commands.len());
    let mut commands = Vec::with_capacity(folded.commands.len() + top_axioms.len());
    let mut build = AssertBuildCtx::from_script(&folded)?;
    commands.extend(folded.commands[..insert_idx].iter().cloned());
    for axiom in top_axioms.iter() {
        build.push_assert(&mut commands, axiom)?;
    }
    commands.extend(folded.commands[insert_idx..].iter().cloned());

    let top_level = top_axioms.len();
    Ok((
        Script::from_commands(&folded.source, commands),
        serde_json::json!({
            "top_level_bitwise_axiom_asserts": top_level,
            "bitwise_stats": stats_payload(&stats),
        }),
    ))
}

fn stats_payload(stats: &BitwiseStats) -> serde_json::Value {
    serde_json::json!({
        "seen": {
            "xor": stats.seen_xor,
            "and": stats.seen_and,
            "or": stats.seen_or,
        },
        "emitted": {
            "xor": stats.emitted_xor,
            "and": stats.emitted_and,
            "or": stats.emitted_or,
            "link": stats.emitted_link,
        },
    })
}

fn collect_bitwise_terms(formula: &Bool) -> BitwiseTerms {
    let mut out = BitwiseTerms::default();
    let mut stack = vec![Dynamic::from_ast(formula)];
    while let Some(node) = stack.pop() {
        if let Some((name, _, _)) = uf_binary_dyn(&node) {
            if let Some(i) = node.as_int() {
                match name.as_str() {
                    UF_XOR => {
                        out.xors.insert(i);
                    }
                    UF_AND => {
                        out.ands.insert(i);
                    }
                    UF_OR => {
                        out.ors.insert(i);
                    }
                    _ => {}
                }
            }
        }
        if node.kind() == AstKind::Quantifier {
            continue;
        }
        for ch in node.children() {
            stack.push(ch);
        }
    }
    out
}

fn uf_binary_dyn(node: &Dynamic) -> Option<(String, Int, Int)> {
    if node.kind() != AstKind::App || node.num_children() != 2 {
        return None;
    }
    let name = decl_name(&node.decl());
    if name != UF_XOR && name != UF_AND && name != UF_OR {
        return None;
    }
    let x = node.nth_child(0)?.as_int()?;
    let y = node.nth_child(1)?.as_int()?;
    Some((name, x, y))
}

fn fold_bitwise_bool(b: &Bool) -> Bool {
    let d = Dynamic::from_ast(b);
    if d.kind() == AstKind::Quantifier {
        return b.clone();
    }
    rebuild_bool(&d).unwrap_or_else(|| b.clone())
}

fn rebuild_bool(d: &Dynamic) -> Option<Bool> {
    if let Some(b) = d.as_bool() {
        let dd = Dynamic::from_ast(&b);
        if dd.kind() != AstKind::App {
            return Some(b);
        }
        let args: Vec<Dynamic> = dd.children().into_iter().map(|ch| fold_dynamic(&ch)).collect();
        let refs: Vec<&dyn Ast> = args.iter().map(|a| a as &dyn Ast).collect();
        return Some(smt2::ast_util::rebuild_app(&dd.decl(), &refs).as_bool().unwrap_or(b));
    }
    None
}

fn fold_dynamic(node: &Dynamic) -> Dynamic {
    if let Some(i) = node.as_int() {
        return Dynamic::from_ast(&fold_int(&i));
    }
    if let Some(b) = node.as_bool() {
        return Dynamic::from_ast(&fold_bitwise_bool(&b));
    }
    if node.kind() != AstKind::App || node.kind() == AstKind::Quantifier {
        return node.clone();
    }
    let args: Vec<Dynamic> = node.children().into_iter().map(|ch| fold_dynamic(&ch)).collect();
    let refs: Vec<&dyn Ast> = args.iter().map(|a| a as &dyn Ast).collect();
    smt2::ast_util::rebuild_app(&node.decl(), &refs)
}

fn fold_int(i: &Int) -> Int {
    let d = Dynamic::from_ast(i);
    if let Some((name, x, y)) = uf_binary_dyn(&d) {
        let x = fold_int(&x);
        let y = fold_int(&y);
        return match name.as_str() {
            UF_XOR if is_zero(&x) => y,
            UF_XOR if is_zero(&y) => x,
            UF_XOR if x.ast_eq(&y) => int_from_i128(0),
            UF_AND if is_zero(&x) || is_zero(&y) => int_from_i128(0),
            UF_AND if x.ast_eq(&y) => x,
            UF_OR if is_zero(&x) => y,
            UF_OR if is_zero(&y) => x,
            UF_OR if x.ast_eq(&y) => x,
            _ => apply_uf(name.as_str(), x, y),
        };
    }
    if d.kind() != AstKind::App {
        return i.clone();
    }
    let args: Vec<Dynamic> = d.children().into_iter().map(|ch| fold_dynamic(&ch)).collect();
    let refs: Vec<&dyn Ast> = args.iter().map(|a| a as &dyn Ast).collect();
    smt2::ast_util::rebuild_app(&d.decl(), &refs).as_int().unwrap_or_else(|| i.clone())
}

fn apply_uf(name: &str, x: Int, y: Int) -> Int {
    let s = x.get_sort();
    let decl = z3::FuncDecl::new(name, &[&s, &s], &s);
    decl.apply(&[&x, &y]).as_int().unwrap_or(x)
}

fn emit_axioms(terms: &BitwiseTerms, stats: &mut BitwiseStats) -> Vec<Bool> {
    let mut out = Vec::new();
    for term in terms.xors.terms() {
        if let Some((_, x, y)) = uf_binary_dyn(&Dynamic::from_ast(term)) {
            if x.ast_eq(&y) {
                continue;
            }
            let xor = term.clone();
            let and_xy = apply_uf(UF_AND, x.clone(), y.clone());
            let or_xy = apply_uf(UF_OR, x.clone(), y.clone());
            let guard = byte_guard(&x, &y);
            let sum = Int::add(&[&x, &y]);
            let two_and = Int::mul(&[&int_from_i128(2), &and_xy]);
            let rhs = Int::add(&[&xor, &two_and]);
            out.push(guard.implies(&sum.eq(&rhs)));
            let or_rhs = Int::sub(&[&sum, &and_xy]);
            out.push(guard.implies(&or_xy.eq(&or_rhs)));
            stats.emitted_link += 2;
            out.push(x.eq(&y).eq(&xor.eq(&int_from_i128(0))));
            stats.emitted_xor += 1;
        }
    }
    for term in terms.ands.terms() {
        if let Some((_, x, y)) = uf_binary_dyn(&Dynamic::from_ast(term)) {
            out.push(x.eq(&int_from_i128(0)).eq(&term.eq(&int_from_i128(0))));
            out.push(y.eq(&int_from_i128(0)).eq(&term.eq(&int_from_i128(0))));
            stats.emitted_and += 2;
        }
    }
    for term in terms.ors.terms() {
        if let Some((_, x, y)) = uf_binary_dyn(&Dynamic::from_ast(term)) {
            out.push(x.eq(&int_from_i128(0)).eq(&term.eq(&y)));
            out.push(y.eq(&int_from_i128(0)).eq(&term.eq(&x)));
            stats.emitted_or += 2;
        }
    }
    out
}

fn is_zero(t: &Int) -> bool {
    int_value_dyn(&Dynamic::from_ast(t)) == Some(0)
}

fn byte_guard(x: &Int, y: &Int) -> Bool {
    let z = int_from_i128(0);
    let m = int_from_i128(255);
    Bool::and(&[&x.ge(&z), &x.le(&m), &y.ge(&z), &y.le(&m)])
}
