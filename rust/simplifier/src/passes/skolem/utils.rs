use std::collections::HashMap;

use smt2::ast_build::{is_symbol_dyn, iter_nodes_dyn, parse_bool_formula, symbol_name_dyn};
use smt2::ast_util::{decl_name, quantifier_bounds, quantifier_body_bool, strip_prefix};
use smt2::{declare_fun_name_cmd, seed_parser_context, ParseCtx, Script, SmtCommand};
use z3::ast::{Ast, AstKind, Bool, Dynamic};
use z3::SortKind as Z3SortKind;

use super::types::{SkolemPin, SortKind};

const SKOLEM_PREFIX: &str = ":skolem-";

pub fn collect_declared_symbols(script: &Script) -> HashMap<String, String> {
    let mut out = HashMap::new();
    for cmd in &script.commands {
        if let Some(name) = declare_fun_name(cmd, &script.source) {
            out.insert(strip_prefix(&name).to_string(), name);
        }
    }
    out
}

pub fn collect_symbol_sorts(script: &Script) -> HashMap<String, SortKind> {
    let mut out = HashMap::new();
    for cmd in &script.commands {
        if let Some(name) = declare_fun_name(cmd, &script.source) {
            out.insert(name.clone(), sort_from_decl(&cmd.to_smtlib(&script.source)));
        }
    }
    for (name, sort) in collect_forall_qvar_sorts(script) {
        out.entry(name).or_insert(sort);
    }
    out
}

pub fn declare_fun_block(script: &Script) -> String {
    script
        .commands
        .iter()
        .filter(|c| c.name() == "declare-fun")
        .map(|c| format!("{}\n", c.to_smtlib(&script.source)))
        .collect()
}

pub fn declare_fun_name(cmd: &SmtCommand, source: &str) -> Option<String> {
    if let Some(name) = declare_fun_name_cmd(cmd) {
        return Some(name);
    }
    if cmd.name() != "declare-fun" {
        return None;
    }
    let raw = cmd.to_smtlib(source);
    let inner = raw.trim().strip_prefix('(')?.trim();
    let rest = inner.strip_prefix("declare-fun")?.trim();
    let end = rest.find(|c: char| c.is_whitespace())?;
    Some(rest[..end].to_string())
}

fn collect_forall_qvar_sorts(script: &Script) -> Vec<(String, SortKind)> {
    let mut out = Vec::new();
    for cmd in &script.commands {
        if let Some(body) = cmd.assert_bool() {
            collect_qvars_from_bool(body, &mut out);
        }
    }
    out
}

fn collect_qvars_from_bool(term: &Bool, out: &mut Vec<(String, SortKind)>) {
    for node in iter_nodes_dyn(&Dynamic::from_ast(term)) {
        if let Some((qvars, _, _body)) = parse_forall(&node) {
            out.extend(qvars);
        }
    }
}

pub fn parse_forall(term: &Dynamic) -> Option<(Vec<(String, SortKind)>, Vec<Dynamic>, Bool)> {
    if term.kind() != AstKind::Quantifier || !smt2::ast_util::is_forall(term) {
        return None;
    }
    let bounds = quantifier_bounds(term);
    if bounds.is_empty() {
        return None;
    }
    let mut out = Vec::new();
    for b in &bounds {
        let sort = match b.get_sort().kind() {
            Z3SortKind::Int => SortKind::Int,
            Z3SortKind::Bool => SortKind::Bool,
            Z3SortKind::Array => SortKind::Array,
            _ => SortKind::Other,
        };
        let Some(name) = symbol_name_dyn(b) else {
            continue;
        };
        out.push((name, sort));
    }
    Some((out, bounds, quantifier_body_bool(term)?))
}

pub fn split_equation(eq: &Bool) -> Option<(String, Dynamic)> {
    let ast = Dynamic::from_ast(eq);
    if ast.kind() != AstKind::App || decl_name(&ast.decl()) != "=" || ast.num_children() != 2 {
        return None;
    }
    let a = ast.nth_child(0)?;
    let b = ast.nth_child(1)?;
    if is_symbol_dyn(&a) {
        return Some((symbol_name_dyn(&a)?, b));
    }
    if is_symbol_dyn(&b) {
        return Some((symbol_name_dyn(&b)?, a));
    }
    None
}

pub fn load_skolem_setinfos(script: &Script) -> Vec<SkolemPin> {
    let mut out = Vec::new();
    let mut parse = ParseCtx::new();
    if seed_parser_context(&mut parse, script).is_err() {
        return out;
    }
    for cmd in &script.commands {
        if cmd.name() != "set-info" {
            continue;
        }
        let raw = cmd.to_smtlib(&script.source);
        let Some((key, value)) = parse_set_info(&raw) else {
            continue;
        };
        if !key.starts_with(SKOLEM_PREFIX) {
            continue;
        }
        let rest = &key[SKOLEM_PREFIX.len()..];
        let Some(dash) = rest.rfind('-') else {
            continue;
        };
        let kind_slug = &rest[..dash];
        let kind = kind_slug.replace('-', "_");
        if let Ok(eq) = parse_bool_formula(&mut parse, &value) {
            out.push(SkolemPin {
                equation: eq,
                kind,
            });
        }
    }
    out
}

fn parse_set_info(raw: &str) -> Option<(String, String)> {
    let inner = raw.trim().strip_prefix('(')?.trim().strip_suffix(')')?.trim();
    let rest = inner.strip_prefix("set-info")?.trim();
    let key_end = rest.find(|c: char| c.is_whitespace())?;
    let key = rest[..key_end].to_string();
    let value = strip_set_info_value(rest[key_end..].trim());
    Some((key, value))
}

/// PySMT strips ``|...|`` on ``set-info`` parse-in; mirror that before Z3 parse.
fn strip_set_info_value(value: &str) -> String {
    let v = value.trim();
    if v.len() >= 2 && v.starts_with('|') && v.ends_with('|') {
        return v[1..v.len() - 1].trim().to_string();
    }
    v.to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn set_info_value_strips_pipe_quotes() {
        let raw = "(set-info :skolem-substitution-0 |(= before-a__0_8@299 before-a__0_7@272)|)";
        let (_, value) = parse_set_info(raw).unwrap();
        assert_eq!(value, "(= before-a__0_8@299 before-a__0_7@272)");
        let script = Script::parse(
            "(declare-fun before-a__0_8@299 () Int)\n(declare-fun before-a__0_7@272 () Int)\n(check-sat)\n",
        )
        .unwrap();
        let mut parse = ParseCtx::new();
        seed_parser_context(&mut parse, &script).unwrap();
        assert!(parse_bool_formula(&mut parse, &value).is_ok());
    }
}

fn sort_from_decl(raw: &str) -> SortKind {
    if raw.contains("(Array") || raw.contains(" Array ") {
        SortKind::Array
    } else if raw.contains("Bool") {
        SortKind::Bool
    } else if raw.contains("Int") {
        SortKind::Int
    } else {
        SortKind::Other
    }
}
