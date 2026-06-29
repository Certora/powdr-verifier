//! Hoist ``Not(= q expr)`` skolem disjuncts from ``forall`` bodies to top-level asserts.

use std::collections::{BTreeMap, HashMap, HashSet};

use smt2::ast_util::{
    decl_name, flatten_or, is_forall, or_parts, quantifier_body_bool, quantifier_body_deps,
    quantifier_bound_names, quantifier_bounds, rebuild_forall_dyn, resolve_bound_or_free_name,
};
use smt2::ast_build::{free_variables_bool, parse_bool_formula};
use smt2::{declare_fun_name_cmd, map_bool_children, parse_single_command, ParseCtx, Script, SmtCommand};
use z3::ast::{Ast, AstKind, Bool, Dynamic};

use crate::expr_util::AssertBuildCtx;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum DeclSort {
    Int,
    Bool,
    Array,
}

fn sort_kind_to_smt(sort: DeclSort) -> &'static str {
    match sort {
        DeclSort::Bool => "Bool",
        DeclSort::Array => "(Array Int Int)",
        DeclSort::Int => "Int",
    }
}

fn sort_from_decl(raw: &str) -> DeclSort {
    if raw.contains("(Array") || raw.contains(" Array ") {
        DeclSort::Array
    } else if raw.contains("Bool") {
        DeclSort::Bool
    } else {
        DeclSort::Int
    }
}

fn collect_symbol_sorts(script: &Script) -> HashMap<String, DeclSort> {
    let mut out = HashMap::new();
    for cmd in &script.commands {
        if let Some(name) = declare_fun_name_cmd(cmd) {
            let raw = cmd.to_smtlib(&script.source);
            out.insert(name, sort_from_decl(&raw));
        }
    }
    out
}

fn infer_symbol_sort(name: &str, sorts: &HashMap<String, DeclSort>) -> DeclSort {
    if let Some(sort) = sorts.get(name) {
        return *sort;
    }
    if name.contains("memory_is") || name.contains("memory_match") {
        return DeclSort::Bool;
    }
    DeclSort::Int
}

struct LiftWalker {
    lifted: BTreeMap<String, Bool>,
    sorts: HashMap<String, DeclSort>,
}

impl LiftWalker {
    fn new(sorts: HashMap<String, DeclSort>) -> Self {
        Self {
            lifted: BTreeMap::new(),
            sorts,
        }
    }

    fn record_bound_sort(&mut self, name: &str, sort: DeclSort) {
        self.sorts.entry(name.to_string()).or_insert(sort);
    }

    fn walk_bool(&mut self, b: &Bool) -> Bool {
        let ast = Dynamic::from_ast(b);
        if ast.kind() == AstKind::Quantifier {
            if is_forall(&ast) {
                return self.process_forall(b);
            }
            return b.clone();
        }
        map_bool_children(b, &mut |child| self.walk_bool(child))
    }

    fn process_forall(&mut self, b: &Bool) -> Bool {
        let ast = Dynamic::from_ast(b);
        let all_bounds = quantifier_bounds(&ast);
        let bound_order: Vec<String> = quantifier_bound_names(&ast);
        for bound in &all_bounds {
            if let Some(name) = resolve_bound_or_free_name(bound, &bound_order) {
                let sort = if bound.as_bool().is_some() {
                    DeclSort::Bool
                } else if bound.as_int().is_some() {
                    DeclSort::Int
                } else {
                    DeclSort::Array
                };
                self.record_bound_sort(&name, sort);
            }
        }

        let mut qvars: HashSet<String> = bound_order.iter().cloned().collect();
        let body = match quantifier_body_bool(&ast) {
            Some(body) => body,
            None => return b.clone(),
        };
        let Some(disjuncts) = or_parts(&body) else {
            return b.clone();
        };

        let mut candidates: Vec<Bool> = disjuncts
            .iter()
            .filter(|d| is_potential_lift_pair(d))
            .cloned()
            .collect();
        let mut lifted_disjuncts: HashSet<String> = HashSet::new();

        let mut progressed = true;
        while progressed {
            progressed = false;
            candidates.sort_by(|a, c| a.to_string().cmp(&c.to_string()));
            let mut next = Vec::new();
            for d in candidates {
                if let Some((lifted_name, eq)) = match_lift_pair(&d, &bound_order, &qvars) {
                    if !self.lifted.contains_key(&lifted_name) {
                        let Ok(named) = name_debruijn_bool(&eq, &bound_order, &all_bounds) else {
                            next.push(d);
                            continue;
                        };
                        self.lifted.insert(lifted_name.clone(), named);
                        qvars.remove(&lifted_name);
                        lifted_disjuncts.insert(d.to_string());
                        progressed = true;
                    }
                } else {
                    next.push(d);
                }
            }
            candidates = next;
        }

        if lifted_disjuncts.is_empty() {
            return b.clone();
        }

        let remaining: Vec<Bool> = disjuncts
            .iter()
            .filter(|d| !lifted_disjuncts.contains(&d.to_string()))
            .cloned()
            .collect();
        let body_out = if remaining.is_empty() {
            Bool::from_bool(false)
        } else {
            flatten_or(remaining)
        };
        let named_body = match name_debruijn_bool(&body_out, &bound_order, &all_bounds) {
            Ok(b) => b,
            Err(_) => return b.clone(),
        };

        let qvars_remaining: Vec<Dynamic> = all_bounds
            .iter()
            .filter(|bound| {
                resolve_bound_or_free_name(bound, &bound_order)
                    .map(|n| qvars.contains(&n))
                    .unwrap_or(false)
            })
            .cloned()
            .collect();

        if qvars_remaining.is_empty() {
            self.walk_bool(&named_body)
        } else {
            let rebuilt = rebuild_forall_dyn(&qvars_remaining, &named_body);
            self.walk_bool(&rebuilt)
        }
    }
}

pub fn apply(script: &Script) -> Result<(Script, serde_json::Value), String> {
    let sorts = collect_symbol_sorts(script);
    let mut walker = LiftWalker::new(sorts);

    let mut prefix = Vec::new();
    let mut suffix = Vec::new();
    let mut in_prefix = true;
    let mut declared: HashSet<String> = script
        .commands
        .iter()
        .filter_map(declare_fun_name_cmd)
        .collect();

    for cmd in &script.commands {
        if let Some(name) = declare_fun_name_cmd(cmd) {
            declared.insert(name);
        }
        if cmd.assert_bool().is_some() {
            in_prefix = false;
        }
        if in_prefix {
            prefix.push(cmd.clone());
        } else if let Some(b) = cmd.assert_bool() {
            let new_b = walker.walk_bool(b);
            suffix.push(SmtCommand::new_assert(new_b));
        } else {
            suffix.push(cmd.clone());
        }
    }

    let mut hoisted_decls = 0usize;
    let mut hoisted_asserts = 0usize;
    let mut insert = Vec::new();
    if !walker.lifted.is_empty() {
        let mut ctx = AssertBuildCtx::from_script(script)?;
        let mut to_declare: BTreeMap<String, DeclSort> = BTreeMap::new();
        for (name, eq) in &walker.lifted {
            if let Some(sort) = walker.sorts.get(name) {
                to_declare.entry(name.clone()).or_insert(*sort);
            }
            for sym in free_variables_bool(eq) {
                if !declared.contains(&sym) {
                    let sort = infer_symbol_sort(&sym, &walker.sorts);
                    to_declare.entry(sym).or_insert(sort);
                }
            }
        }
        for (name, sort) in to_declare {
            if declared.contains(&name) {
                continue;
            }
            let raw = format!("(declare-fun {name} () {})", sort_kind_to_smt(sort));
            let cmd = parse_single_command(&raw, ctx.parse())?;
            insert.push(cmd);
            declared.insert(name);
            hoisted_decls += 1;
        }
        for eq in walker.lifted.values() {
            ctx.push_assert(&mut insert, eq)?;
            hoisted_asserts += 1;
        }
    }

    let mut commands = prefix;
    commands.extend(insert);
    commands.extend(suffix);

    let stats = serde_json::json!({
        "pins_lifted": walker.lifted.len(),
        "new_declarations": hoisted_decls,
        "hoisted_pin_asserts": hoisted_asserts,
        "candidates_seen": walker.lifted.len(),
    });
    Ok((Script::from_commands(&script.source, commands), stats))
}

fn name_debruijn_bool(
    b: &Bool,
    bound_order: &[String],
    bounds: &[Dynamic],
) -> Result<Bool, String> {
    let mut raw = b.to_string();
    for i in (0..bound_order.len()).rev() {
        raw = raw.replace(&format!("(:var {i})"), &bound_order[i]);
    }
    let mut ctx = ParseCtx::new();
    for bound in bounds {
        if let Some(name) = resolve_bound_or_free_name(bound, bound_order) {
            let sort = if bound.as_bool().is_some() {
                "Bool"
            } else if bound.as_int().is_some() {
                "Int"
            } else {
                "(Array Int Int)"
            };
            let _ = ctx.ingest_command(&format!("(declare-fun {name} () {sort})"));
        }
    }
    parse_bool_formula(&mut ctx, &raw)
}

fn is_potential_lift_pair(d: &Bool) -> bool {
    is_not_eq(d).is_some()
}

fn is_not_eq(d: &Bool) -> Option<Bool> {
    let ast = Dynamic::from_ast(d);
    if ast.kind() != AstKind::App || decl_name(&ast.decl()) != "not" || ast.num_children() != 1 {
        return None;
    }
    let inner = ast.nth_child(0)?;
    if inner.kind() != AstKind::App || decl_name(&inner.decl()) != "=" || inner.num_children() != 2 {
        return None;
    }
    inner.as_bool()
}

fn match_lift_pair(
    d: &Bool,
    bound_order: &[String],
    qvars: &HashSet<String>,
) -> Option<(String, Bool)> {
    let eq = is_not_eq(d)?;
    let ast = Dynamic::from_ast(&eq);
    let lhs = ast.nth_child(0)?;
    let rhs = ast.nth_child(1)?;
    for (vside, expr) in [(lhs.clone(), rhs.clone()), (rhs, lhs)] {
        let Some(name) = resolve_bound_or_free_name(&vside, bound_order) else {
            continue;
        };
        if !qvars.contains(&name) {
            continue;
        }
        let deps = quantifier_body_deps(&expr, bound_order, qvars);
        if deps.is_empty() {
            return Some((name, eq));
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    fn script_assert(raw: &str) -> Script {
        Script::parse(&format!("(assert {raw})\n(check-sat)\n")).unwrap()
    }

    fn top_asserts(script: &Script) -> Vec<String> {
        script
            .commands
            .iter()
            .filter_map(|c| c.assert_bool().map(|b| b.to_string()))
            .collect()
    }

    #[test]
    fn debug_forall_body() {
        let script = script_assert("(forall ((x Int)) (or (not (= x 7)) (< x 0)))");
        let b = script.commands[0].assert_bool().unwrap();
        let ast = Dynamic::from_ast(b);
        let bound_order = quantifier_bound_names(&ast);
        let body = quantifier_body_bool(&ast).unwrap();
        let disjuncts = or_parts(&body).unwrap();
        let qvars: HashSet<String> = bound_order.iter().cloned().collect();
        assert!(match_lift_pair(&disjuncts[0], &bound_order, &qvars).is_some());
    }

    #[test]
    fn lift_single_var() {
        let script = script_assert("(forall ((x Int)) (or (not (= x 7)) (< x 0)))");
        let (out, stats) = apply(&script).unwrap();
        assert_eq!(stats["pins_lifted"], 1);
        let asserts = top_asserts(&out);
        assert!(asserts.iter().any(|a| a == "(= x 7)"));
        assert!(asserts.iter().any(|a| a == "(< x 0)"));
        assert!(!asserts.iter().any(|a| a.contains("forall")));
    }

    #[test]
    fn skips_when_expr_mentions_other_qvar() {
        let script = script_assert("(forall ((x Int) (y Int)) (or (not (= x y)) (< x 0)))");
        let (out, stats) = apply(&script).unwrap();
        assert_eq!(stats["pins_lifted"], 0);
        assert_eq!(out.commands.len(), script.commands.len());
    }
}
