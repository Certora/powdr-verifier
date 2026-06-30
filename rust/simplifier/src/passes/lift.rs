//! Hoist ``Not(= q expr)`` skolem disjuncts from ``forall`` bodies to top-level asserts.

use std::collections::{BTreeMap, HashMap, HashSet};

use smt2::ast_util::{
    bound_var_index, decl_name, flatten_or, is_forall, or_parts, quantifier_body_bool,
    quantifier_body_deps, quantifier_bound_names, quantifier_bounds, quantifier_bounds_de_bruijn, rebuild_forall_dyn,
    resolve_bound_or_free_name, substitute_bound_vars_dyn, contains_bound_var_dyn,
    de_bruijn_bound_name,
};
use smt2::ast_build::{free_variables_bool, parse_bool_formula};
use smt2::{declare_fun_name_cmd, map_bool_children, parse_single_command, seed_parser_context, ParseCtx, Script, SmtCommand};
use z3::ast::{Ast, AstKind, Bool, Dynamic, Int};

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
    sorts.get(name).copied().unwrap_or(DeclSort::Int)
}

struct LiftWalker {
    script: Script,
    lifted: BTreeMap<String, Bool>,
    sorts: HashMap<String, DeclSort>,
}

impl LiftWalker {
    fn new(script: Script, sorts: HashMap<String, DeclSort>) -> Self {
        Self {
            script,
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
        let all_bounds = quantifier_bounds_de_bruijn(&ast);
        let bound_order: Vec<String> = quantifier_bound_names(&ast);
        for de_bruijn_idx in 0..all_bounds.len() {
            let bound = &all_bounds[de_bruijn_idx];
            if let Some(name) = de_bruijn_bound_name(&bound_order, de_bruijn_idx) {
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
                if let Some((lifted_name, expr)) = match_lift_pair(&d, &bound_order, &qvars, &self.script) {
                    if !self.lifted.contains_key(&lifted_name) {
                        let Ok(named_expr) = name_debruijn_dyn(&expr, &ast, &self.script) else {
                            next.push(d);
                            continue;
                        };
                        let sort = self.sorts.get(&lifted_name).copied().unwrap_or(DeclSort::Int);
                        let hoisted = match sort {
                            DeclSort::Bool => {
                                let Some(rhs) = named_expr.as_bool() else {
                                    next.push(d);
                                    continue;
                                };
                                Bool::new_const(lifted_name.as_str()).eq(&rhs)
                            }
                            _ => {
                                let Some(rhs) = named_expr.as_int() else {
                                    next.push(d);
                                    continue;
                                };
                                Int::new_const(lifted_name.as_str()).eq(&rhs)
                            }
                        };
                        self.lifted.insert(lifted_name.clone(), hoisted);
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
        let named_body = match name_debruijn_bool(&body_out, &ast, &self.script) {
            Ok(b) => b,
            Err(_) => return b.clone(),
        };

        let qvars_remaining: Vec<Dynamic> = bound_order
            .iter()
            .filter(|name| qvars.contains(*name))
            .map(|name| {
                let sort = self.sorts.get(name).copied().unwrap_or(DeclSort::Int);
                match sort {
                    DeclSort::Bool => Dynamic::from_ast(&Bool::new_const(name.as_str())),
                    _ => Dynamic::from_ast(&Int::new_const(name.as_str())),
                }
            })
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
    let mut walker = LiftWalker::new(script.clone(), sorts);

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

fn refresh_bool_from_text(b: &Bool, script: &Script) -> Result<Bool, String> {
    let mut ctx = ParseCtx::new();
    seed_parser_context(&mut ctx, script)?;
    parse_bool_formula(&mut ctx, &b.to_string())
}

fn parse_named_dyn(raw: &str, hint: &Dynamic, script: &Script) -> Result<Dynamic, String> {
    let mut ctx = ParseCtx::new();
    seed_parser_context(&mut ctx, script)?;
    if hint.as_bool().is_some() {
        return parse_bool_formula(&mut ctx, raw).map(|b| Dynamic::from_ast(&b));
    }
    let eq = format!("(= __lift_parse_tmp__ {raw})");
    let parsed = parse_bool_formula(&mut ctx, &eq)?;
    Dynamic::from_ast(&parsed)
        .nth_child(1)
        .ok_or_else(|| "expected rhs in parsed pin expr".into())
}

fn refresh_dyn_from_text(d: &Dynamic, script: &Script) -> Dynamic {
    parse_named_dyn(&d.to_string(), d, script).unwrap_or_else(|_| d.clone())
}

fn name_debruijn_dyn(d: &Dynamic, quant: &Dynamic, script: &Script) -> Result<Dynamic, String> {
    let d = refresh_dyn_from_text(d, script);
    if !contains_bound_var_dyn(&d) {
        return Ok(d);
    }
    let bound_order = quantifier_bound_names(quant);
    let mut raw = d.to_string();
    if raw.contains("(:var ") {
        for i in (0..bound_order.len()).rev() {
            if let Some(name) = de_bruijn_bound_name(&bound_order, i) {
                raw = raw.replace(&format!("(:var {i})"), &name);
            }
        }
    }
    if let Ok(out) = parse_named_dyn(&raw, &d, script) {
        return Ok(out);
    }
    let replacements = quantifier_bounds_de_bruijn(quant);
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        substitute_bound_vars_dyn(&d, &replacements)
    }))
    .map_err(|_| "substitute_bound_vars_dyn panicked".into())
}

fn name_debruijn_bool(b: &Bool, quant: &Dynamic, script: &Script) -> Result<Bool, String> {
    name_debruijn_dyn(&Dynamic::from_ast(b), quant, script)?
        .as_bool()
        .ok_or_else(|| "expected bool after de Bruijn naming".into())
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

fn disjunct_from_text(d: &Bool, script: &Script) -> Bool {
    refresh_bool_from_text(d, script).unwrap_or_else(|_| d.clone())
}

fn match_lift_pair(
    d: &Bool,
    bound_order: &[String],
    qvars: &HashSet<String>,
    script: &Script,
) -> Option<(String, Dynamic)> {
    let d = disjunct_from_text(d, script);
    let eq = is_not_eq(&d)?;
    let ast = Dynamic::from_ast(&eq);
    let lhs = ast.nth_child(0)?;
    let rhs = ast.nth_child(1)?;
    for (vside, expr) in [(lhs.clone(), rhs.clone()), (rhs, lhs)] {
        let name = resolve_bound_or_free_name(&vside, bound_order)?;
        if !qvars.contains(&name) {
            continue;
        }
        if bound_var_index(&vside).is_none() && smt2::symbol_name_dyn(&vside).is_none() {
            continue;
        }
        let deps = quantifier_body_deps(&expr, bound_order, qvars);
        if deps.is_empty() {
            return Some((name, expr));
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
        assert!(match_lift_pair(&disjuncts[0], &bound_order, &qvars, &script).is_some());
    }

    #[test]
    fn lift_mod_pin_repro() {
        let raw = r#"(declare-fun before-a__3_1@58 () Int)
(assert (forall ((before-writes_aux__prev_data__3_5@199 Int))
  (or (not (= before-writes_aux__prev_data__3_5@199 (mod before-a__3_1@58 2013265921)))
      false)))
(check-sat)
"#;
        let script = Script::parse(raw).unwrap();
        let (out, stats) = apply(&script).unwrap();
        assert_eq!(stats["pins_lifted"], 1);
        let asserts = top_asserts(&out);
        assert!(
            asserts.iter().any(|a| a.contains("before-a__3_1@58")),
            "pins: {:?}",
            asserts
        );
        assert!(!asserts.iter().any(|a| a.contains("(mod 0")));
    }

    #[test]
    #[ignore]
    fn debug_skolem_pin_strings() {
        let text = std::fs::read_to_string("/tmp/skolem.smt2").unwrap();
        let script = Script::parse(&text).unwrap();
        let b = script
            .commands
            .iter()
            .find_map(|c| c.assert_bool())
            .unwrap();
        find_pin_disjunct_str(b);
    }

    fn find_pin_disjunct_str(b: &Bool) {
        let ast = Dynamic::from_ast(b);
        if is_forall(&ast) {
            let body = quantifier_body_bool(&ast).unwrap();
            if let Some(disjuncts) = or_parts(&body) {
                eprintln!("or with {} disjuncts", disjuncts.len());
                for d in disjuncts {
                    let ds = d.to_string();
                    if ds.contains("(:var 0)") && ds.contains("(mod") {
                        eprintln!("z3 d={ds}");
                    }
                }
            }
            find_pin_disjunct_str(&body);
            return;
        }
        if let Some(parts) = smt2::and_parts(b) {
            for p in parts {
                find_pin_disjunct_str(&p);
            }
        }
    }

    #[test]
    fn lift_ordered_dependencies() {
        let script = Script::parse(
            "(assert (forall ((x Int) (y Int)) (or (not (= y 5)) (not (= x (mod y 10))))))\n(check-sat)\n",
        )
        .unwrap();
        let (out, stats) = apply(&script).unwrap();
        assert_eq!(stats["pins_lifted"], 2);
        let asserts = top_asserts(&out);
        assert!(asserts.iter().any(|a| a == "(= y 5)"), "{asserts:?}");
        assert!(asserts.iter().any(|a| a == "(= x (mod y 10))"), "{asserts:?}");
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
