use std::collections::HashMap;

use smt2::{Script, Term};

use super::term_util::{is_symbol, sort_from_decl, symbol_name};
use super::types::{SkolemPin, SortKind};

const SKOLEM_PREFIX: &str = ":skolem-";

pub fn collect_declared_symbols(script: &Script) -> HashMap<String, Term> {
    let mut out = HashMap::new();
    for cmd in &script.commands {
        if cmd.name() != "declare-fun" {
            continue;
        }
        if let Some(name) = declare_fun_name(&cmd.raw) {
            out.insert(super::term_util::strip_prefix(&name).to_string(), Term::Atom(name));
        }
    }
    out
}

pub fn collect_symbol_sorts(script: &Script) -> HashMap<String, SortKind> {
    let mut out = HashMap::new();
    for cmd in &script.commands {
        if cmd.name() != "declare-fun" {
            continue;
        }
        if let Some(name) = declare_fun_name(&cmd.raw) {
            out.insert(name.clone(), sort_from_decl(&cmd.raw));
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
        .map(|c| format!("{}\n", c.raw))
        .collect()
}

pub fn declare_fun_name(raw: &str) -> Option<String> {
    let inner = raw.trim().strip_prefix('(')?.trim();
    let rest = inner.strip_prefix("declare-fun")?.trim();
    let end = rest.find(|c: char| c.is_whitespace())?;
    Some(rest[..end].to_string())
}

fn collect_forall_qvar_sorts(script: &Script) -> Vec<(String, SortKind)> {
    let mut out = Vec::new();
    for cmd in &script.commands {
        if cmd.name() != "assert" {
            continue;
        }
        if let Some(body) = smt2::term::assert_body(&cmd.raw) {
            if let Ok(term) = Term::parse(&body) {
                collect_qvars_from_term(&term, &mut out);
            }
        }
    }
    out
}

fn collect_qvars_from_term(term: &Term, out: &mut Vec<(String, SortKind)>) {
    for node in super::term_util::iter_nodes(term) {
        if let Some((qvars, _body)) = parse_forall(&node) {
            out.extend(qvars);
        }
    }
}

pub fn parse_forall(term: &Term) -> Option<(Vec<(String, SortKind)>, Term)> {
    let Term::List(items) = term else {
        return None;
    };
    if !matches!(items.first(), Some(Term::Atom(s)) if s == "forall") || items.len() < 3 {
        return None;
    }
    let qvars = parse_qvar_decls(&items[1])?;
    Some((qvars, items[2].clone()))
}

fn parse_qvar_decls(decls: &Term) -> Option<Vec<(String, SortKind)>> {
    let Term::List(items) = decls else {
        return None;
    };
    let mut out = Vec::new();
    for d in items {
        match d {
            Term::List(pair) if pair.len() == 2 => {
                let name = match &pair[0] {
                    Term::Atom(s) => s.clone(),
                    _ => continue,
                };
                let sort = match &pair[1] {
                    Term::Atom(s) if s == "Int" => SortKind::Int,
                    Term::Atom(s) if s == "Bool" => SortKind::Bool,
                    Term::Atom(s) if s.starts_with("(") => SortKind::Array,
                    Term::List(_) => SortKind::Array,
                    _ => SortKind::Other,
                };
                out.push((name, sort));
            }
            Term::Atom(name) => out.push((name.clone(), SortKind::Int)),
            _ => {}
        }
    }
    Some(out)
}

pub fn split_equation(eq: &Term) -> Option<(String, Term)> {
    let Term::List(items) = eq else {
        return None;
    };
    if !matches!(items.first(), Some(Term::Atom(s)) if s == "=") || items.len() != 3 {
        return None;
    }
    let a = &items[1];
    let b = &items[2];
    if is_symbol(a) {
        return Some((symbol_name(a)?.to_string(), b.clone()));
    }
    if is_symbol(b) {
        return Some((symbol_name(b)?.to_string(), a.clone()));
    }
    None
}

pub fn load_skolem_setinfos(script: &Script) -> Vec<SkolemPin> {
    let mut out = Vec::new();
    for cmd in &script.commands {
        if cmd.name() != "set-info" {
            continue;
        }
        let Some((key, value)) = parse_set_info(&cmd.raw) else {
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
        if let Ok(eq) = Term::parse(&value) {
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
    let value = rest[key_end..].trim();
    Some((key, value.to_string()))
}
