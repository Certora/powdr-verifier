use std::collections::{HashMap, HashSet};

use smt2::ast_build::{int_literal_dyn, iter_nodes_dyn, parse_bool_formula, symbol_name_dyn};
use smt2::ast_util::{
    free_symbol_ids_bool, int_value_dyn, quantifier_bounds, quantifier_body_bool, strip_prefix,
    swap_prefix, symbol_id_dyn, symbol_id_from_name, symbol_name_for_id, SymbolId,
};
use smt2::{declare_fun_name_cmd, seed_parser_context, ParseCtx, Script, SmtCommand};
use z3::ast::{Ast, AstKind, Bool, Dynamic};
use z3::DeclKind;
use z3::SortKind as Z3SortKind;

use super::types::{SkolemPin, SortKind};

const SKOLEM_PREFIX: &str = ":skolem-";

pub fn collect_declared_symbols(script: &Script) -> HashMap<String, Vec<String>> {
    let mut out: HashMap<String, Vec<String>> = HashMap::new();
    for cmd in &script.commands {
        if let Some(name) = declare_fun_name(cmd, &script.source) {
            out.entry(strip_prefix(&name).to_string()).or_default().push(name);
        }
    }
    out
}

fn build_symbol_sorts(
    mut sorts: HashMap<String, SortKind>,
    qvar_sorts: &[(String, SortKind)],
) -> HashMap<String, SortKind> {
    for (name, sort) in qvar_sorts {
        sorts.entry(name.clone()).or_insert(*sort);
    }
    sorts
}

/// One declare-fun pass yielding both the per-symbol sort map and the set of
/// non-nullary (function) symbols. Replaces the separate `collect_symbol_sorts`
/// declare walk and `collect_function_symbols`.
fn declare_fun_sorts_and_ufs(script: &Script) -> (HashMap<String, SortKind>, HashSet<SymbolId>) {
    let mut sorts = HashMap::new();
    let mut ufs = HashSet::new();
    for cmd in &script.commands {
        let Some(name) = declare_fun_name(cmd, &script.source) else {
            continue;
        };
        let raw = cmd.to_smtlib(&script.source);
        sorts.insert(name.clone(), sort_from_decl(&raw));
        if !is_nullary_declare_fun(&raw) {
            ufs.insert(symbol_id_from_name(&name));
        }
    }
    (sorts, ufs)
}

pub struct AssertScan {
    pub live_symbols: HashSet<SymbolId>,
    pub qvar_sorts: Vec<(String, SortKind)>,
}

/// Single walk over all asserts producing (a) live symbol names (including
/// forall bound-variable names) and (b) forall bound-variable sorts. Replaces
/// the separate `collect_assert_symbols` and `collect_forall_qvar_sorts` walks.
pub fn scan_asserts(script: &Script) -> AssertScan {
    let mut live = HashSet::new();
    let mut qvar_sorts = Vec::new();
    for cmd in &script.commands {
        let Some(body) = cmd.assert_bool() else {
            continue;
        };
        for node in iter_nodes_dyn(&Dynamic::from_ast(body)) {
            if let Some(id) = symbol_id_dyn(&node) {
                if int_value_dyn(&node).is_none()
                    && !node.as_bool().and_then(|b| b.as_bool()).is_some()
                {
                    live.insert(id);
                }
            }
            if let Some((qvars, _, _)) = parse_forall(&node) {
                for (n, s) in qvars {
                    live.insert(symbol_id_from_name(&n));
                    qvar_sorts.push((n, s));
                }
            }
        }
    }
    AssertScan {
        live_symbols: live,
        qvar_sorts,
    }
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
    if eq.kind() != AstKind::App || eq.decl().kind() != DeclKind::Eq || eq.num_children() != 2 {
        return None;
    }
    let a = eq.nth_child(0)?;
    let b = eq.nth_child(1)?;
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
    qvar_sorts: &[(String, SortKind)],
) -> Result<(), String> {
    seed_parser_context(parse, script)?;
    for cmd in &script.commands {
        if let Some(name) = declare_fun_name(cmd, &script.source) {
            declared.insert(name);
        }
    }
    for (name, sort) in qvar_sorts {
        if !declared.insert(name.clone()) {
            continue;
        }
        parse.ingest_command(&format!(
            "(declare-fun {} () {})",
            name,
            sort_kind_to_smt(*sort)
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

fn filter_live_pins(
    pins: Vec<SkolemPin>,
    live: &HashSet<SymbolId>,
    ufs: &HashSet<SymbolId>,
) -> (Vec<SkolemPin>, usize) {
    // A var counts as live if it, OR its before-/after- prefix-swapped
    // counterpart, is live. A rule_based rewrite can define a gadget column
    // (diff_marker, …) as derived on one side while the *other* side keeps it a
    // live constrained witness; the derived pin `<other>-X = expr` is then needed
    // to witness the checked-side `<swap>-X` (via cross_side) even though
    // `<other>-X` is not itself live. Dropping it leaves the checked column
    // unwitnessed => spurious sat.
    let live_or_swapped = |id: SymbolId| -> bool {
        live.contains(&id)
            || symbol_name_for_id(id)
                .and_then(|n| swap_prefix(&n))
                .map(|s| live.contains(&symbol_id_from_name(&s)))
                .unwrap_or(false)
    };
    let mut out = Vec::with_capacity(pins.len());
    let mut dropped = 0usize;
    for pin in pins {
        let vars: HashSet<SymbolId> = free_symbol_ids_bool(&pin.equation)
            .into_iter()
            .filter(|id| !ufs.contains(id))
            .collect();
        if vars.is_empty() {
            dropped += 1;
            continue;
        }
        if vars.iter().all(|id| live_or_swapped(*id)) {
            out.push(pin);
        } else {
            dropped += 1;
        }
    }
    (out, dropped)
}

/// Prepare all script-derived skolem inputs with a single shared assert scan and
/// a single declare-fun pass: symbol sorts, parsed set-info pins, and the count
/// of pins dropped as not-live.
pub fn prepare_skolem_inputs(
    script: &Script,
) -> (HashMap<String, SortKind>, Vec<SkolemPin>, usize) {
    let scan = scan_asserts(script);
    let (decl_sorts, ufs) = declare_fun_sorts_and_ufs(script);
    let sorts = build_symbol_sorts(decl_sorts, &scan.qvar_sorts);
    let (pins, dropped) = load_skolem_setinfos_shared(
        script,
        &sorts,
        &scan.qvar_sorts,
        &scan.live_symbols,
        &ufs,
    );
    (sorts, pins, dropped)
}

#[cfg(test)]
pub fn load_skolem_setinfos(script: &Script) -> (Vec<SkolemPin>, usize) {
    let (_, pins, dropped) = prepare_skolem_inputs(script);
    (pins, dropped)
}

fn load_skolem_setinfos_shared(
    script: &Script,
    sorts: &HashMap<String, SortKind>,
    qvar_sorts: &[(String, SortKind)],
    live: &HashSet<SymbolId>,
    ufs: &HashSet<SymbolId>,
) -> (Vec<SkolemPin>, usize) {
    let mut out = Vec::new();
    let mut parse = ParseCtx::new();
    let mut declared = HashSet::new();
    if seed_parser_for_skolem_pins(&mut parse, script, &mut declared, qvar_sorts).is_err() {
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
        prebind_pin_identifiers(&mut parse, &value, sorts, &mut declared);
        if let Ok(eq) = parse_bool_formula(&mut parse, &value) {
            out.push(SkolemPin {
                equation: eq,
                kind: kind.clone(),
            });
        }
    }
    let (filtered, dropped) = filter_live_pins(out, live, ufs);
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
