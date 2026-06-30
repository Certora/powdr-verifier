use std::collections::{HashMap, HashSet};

use smt2::ast_build::{int_literal_dyn, iter_nodes_dyn, parse_bool_formula, symbol_name_dyn};
use smt2::ast_util::{decl_name, quantifier_bounds, quantifier_body_bool, strip_prefix};
use smt2::{declare_fun_name_cmd, free_variables_bool, seed_parser_context, ParseCtx, Script, SmtCommand};
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

fn equation_var_symbol(ast: &Dynamic) -> Option<String> {
    if ast.kind() != AstKind::App || !ast.is_const() || int_literal_dyn(ast).is_some() {
        return None;
    }
    let name = symbol_name_dyn(ast)?;
    if name == "true" || name == "false" {
        return None;
    }
    Some(name)
}

pub fn split_equation(eq: &Bool) -> Option<(String, Dynamic)> {
    let ast = Dynamic::from_ast(eq);
    if ast.kind() != AstKind::App || decl_name(&ast.decl()) != "=" || ast.num_children() != 2 {
        return None;
    }
    let a = ast.nth_child(0)?;
    let b = ast.nth_child(1)?;
    if let Some(name) = equation_var_symbol(&a) {
        return Some((name, b));
    }
    if let Some(name) = equation_var_symbol(&b) {
        return Some((name, a));
    }
    None
}

fn sort_kind_to_smt(sort: SortKind) -> &'static str {
    match sort {
        SortKind::Bool => "Bool",
        SortKind::Int => "Int",
        SortKind::Array => "(Array Int Int)",
        SortKind::Other => "Int",
    }
}

const PIN_SKIP: &[&str] = &[
    "ite", "not", "and", "or", "xor", "true", "false", "Int", "Bool", "Real", "mod", "div", "abs",
    "select", "store", "distinct", "=>", "implies", "forall", "exists", "let", "as", "const",
];

fn collect_pin_tokens(value: &str) -> Vec<String> {
    let mut out = Vec::new();
    let bytes = value.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i].is_ascii_alphabetic() || bytes[i] == b'_' {
            let start = i;
            i += 1;
            while i < bytes.len()
                && (bytes[i].is_ascii_alphanumeric()
                    || bytes[i] == b'_'
                    || bytes[i] == b'@'
                    || bytes[i] == b'.'
                    || bytes[i] == b'-')
            {
                i += 1;
            }
            out.push(value[start..i].to_string());
        } else {
            i += 1;
        }
    }
    out
}

fn seed_parser_for_skolem_pins(
    parse: &mut ParseCtx,
    script: &Script,
    declared: &mut HashSet<String>,
) -> Result<(), String> {
    seed_parser_context(parse, script)?;
    for cmd in &script.commands {
        if let Some(name) = declare_fun_name(cmd, &script.source) {
            declared.insert(name);
        }
    }
    for (name, sort) in collect_forall_qvar_sorts(script) {
        if !declared.insert(name.clone()) {
            continue;
        }
        parse.ingest_command(&format!(
            "(declare-fun {} () {})",
            name,
            sort_kind_to_smt(sort)
        ))?;
    }
    Ok(())
}

fn prebind_pin_identifiers(
    parse: &mut ParseCtx,
    value: &str,
    sorts: &HashMap<String, SortKind>,
    declared: &mut HashSet<String>,
) {
    for tok in collect_pin_tokens(value) {
        if PIN_SKIP.contains(&tok.as_str()) || declared.contains(&tok) {
            continue;
        }
        let smt_sort = sorts
            .get(&tok)
            .map(|s| sort_kind_to_smt(*s))
            .unwrap_or(if tok.contains('@') { "Int" } else { "Bool" });
        if parse
            .ingest_command(&format!("(declare-fun {tok} () {smt_sort})"))
            .is_ok()
        {
            declared.insert(tok);
        }
    }
}

fn is_nullary_declare_fun(raw: &str) -> bool {
    raw.contains("()")
}

fn collect_function_symbols(script: &Script) -> HashSet<String> {
    let mut out = HashSet::new();
    for cmd in &script.commands {
        if cmd.name() != "declare-fun" {
            continue;
        }
        let raw = cmd.to_smtlib(&script.source);
        if is_nullary_declare_fun(&raw) {
            continue;
        }
        if let Some(name) = declare_fun_name(cmd, &script.source) {
            out.insert(name);
        }
    }
    out
}

pub fn collect_assert_symbols(script: &Script) -> HashSet<String> {
    let mut out = HashSet::new();
    for cmd in &script.commands {
        if let Some(body) = cmd.assert_bool() {
            collect_symbols_from_bool(body, &mut out);
        }
    }
    out
}

fn collect_symbols_from_bool(term: &Bool, out: &mut HashSet<String>) {
    for node in iter_nodes_dyn(&Dynamic::from_ast(term)) {
        if let Some(name) = symbol_name_dyn(&node) {
            if name != "true" && name != "false" && int_literal_dyn(&node).is_none() {
                out.insert(name);
            }
        }
        if let Some((qvars, _, _)) = parse_forall(&node) {
            for (n, _) in qvars {
                out.insert(n);
            }
        }
    }
}

fn filter_live_pins(pins: Vec<SkolemPin>, script: &Script) -> (Vec<SkolemPin>, usize) {
    let live = collect_assert_symbols(script);
    let ufs = collect_function_symbols(script);
    let mut out = Vec::with_capacity(pins.len());
    let mut dropped = 0usize;
    for pin in pins {
        let vars: HashSet<String> = free_variables_bool(&pin.equation)
            .into_iter()
            .filter(|n| n != "true" && n != "false" && !ufs.contains(n))
            .collect();
        if vars.is_empty() {
            dropped += 1;
            continue;
        }
        if vars.iter().all(|n| live.contains(n)) {
            out.push(pin);
        } else {
            dropped += 1;
        }
    }
    (out, dropped)
}

pub fn load_skolem_setinfos(script: &Script) -> (Vec<SkolemPin>, usize) {
    let sorts = collect_symbol_sorts(script);
    let mut out = Vec::new();
    let mut parse = ParseCtx::new();
    let mut declared = HashSet::new();
    if seed_parser_for_skolem_pins(&mut parse, script, &mut declared).is_err() {
        return (out, 0);
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
        prebind_pin_identifiers(&mut parse, &value, &sorts, &mut declared);
        if let Ok(eq) = parse_bool_formula(&mut parse, &value) {
            out.push(SkolemPin {
                equation: eq,
                kind: kind.clone(),
            });
        }
    }
    let (filtered, dropped) = filter_live_pins(out, script);
    if dropped > 0 {
        eprintln!(
            "skolem: dropped {dropped} set-info pins (symbols not live in asserts), kept {}",
            filtered.len()
        );
    }
    (filtered, dropped)
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
    fn split_loaded_memory_bus_pin() {
        let script = Script::parse(
            "(declare-fun after-memory_isinput_0 () Bool)\n\
             (set-info :skolem-memory-bus-0 |(= before-memory_isinput_0 after-memory_isinput_0)|)\n\
             (assert (forall ((before-memory_isinput_0 Bool)) \
               (= before-memory_isinput_0 after-memory_isinput_0)))\n\
             (check-sat)\n",
        )
        .unwrap();
        let (pins, dropped) = load_skolem_setinfos(&script);
        assert_eq!(dropped, 0);
        assert_eq!(pins.len(), 1);
        let split = split_equation(&pins[0].equation);
        assert_eq!(
            split.as_ref().map(|(v, _)| v.as_str()),
            Some("before-memory_isinput_0")
        );
        let body = script
            .commands
            .iter()
            .find_map(|c| c.assert_bool())
            .unwrap();
        let forall = Dynamic::from_ast(body);
        let (qvars, _, _) = parse_forall(&forall).unwrap();
        let qnames: HashSet<String> = qvars.iter().map(|(n, _)| n.clone()).collect();
        assert!(qnames.contains("before-memory_isinput_0"));
    }

    #[test]
    fn load_memory_bus_pins_with_forall_qvars() {
        let script = Script::parse(
            "(declare-fun after-memory_isinput_0 () Bool)\n\
             (set-info :skolem-memory-bus-0 |(= before-memory_isinput_0 after-memory_isinput_0)|)\n\
             (assert (forall ((before-memory_isinput_0 Bool)) \
               (= before-memory_isinput_0 after-memory_isinput_0)))\n\
             (check-sat)\n",
        )
        .unwrap();
        let (pins, dropped) = load_skolem_setinfos(&script);
        assert_eq!(dropped, 0);
        assert_eq!(pins.len(), 1);
        assert_eq!(pins[0].kind, "memory_bus");
    }

    #[test]
    fn load_skolem_setinfos_drops_pins_with_ghost_symbols() {
        let script = Script::parse(
            "(set-info :skolem-memory-bus-0 |(= before-memory_isdisabled_0 false)|)\n\
             (set-info :skolem-memory-bus-1 |(= before-memory_isinput_0 after-memory_isinput_0)|)\n\
             (declare-fun after-memory_isinput_0 () Bool)\n\
             (assert (forall ((before-memory_isinput_0 Bool)) \
               (= before-memory_isinput_0 after-memory_isinput_0)))\n\
             (check-sat)\n",
        )
        .unwrap();
        let (pins, dropped) = load_skolem_setinfos(&script);
        assert_eq!(dropped, 1);
        assert_eq!(pins.len(), 1);
        assert_eq!(pins[0].kind, "memory_bus");
    }

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
