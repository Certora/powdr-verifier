mod derived;
mod isolate;
mod map;
mod names;
mod rules;
pub(crate) mod term_util;
pub(crate) mod types;
pub(crate) mod utils;
mod witness;

use std::collections::{HashMap, HashSet};

use smt2::{map_asserts, Script, Term};

use self::map::SkolemMap;
use self::term_util::{field_mod, list};
use self::types::SortKind;
use self::utils::{
    collect_declared_symbols, collect_symbol_sorts, declare_fun_block, load_skolem_setinfos,
    parse_forall,
};

const SKOLEM_SETINFO_PREFIX: &str = ":skolem-";

pub fn apply(script: &Script) -> Result<(Script, serde_json::Value), String> {
    let field = field_mod();
    let declared = collect_declared_symbols(script);
    let sorts = collect_symbol_sorts(script);
    let pins = load_skolem_setinfos(script);
    let candidates = field
        .map(|p| witness::collect_candidates(script, p))
        .unwrap_or_default();
    let decl_block = declare_fun_block(script);

    let mut applied: HashMap<String, usize> = HashMap::new();
    let mut qvar_sets: Vec<HashSet<String>> = Vec::new();

    let out = map_asserts(script, |body| {
        let term = Term::parse(body)?;
        Ok(walk_assert(&term, &declared, &sorts, &pins, &candidates, &decl_block, field, &mut applied, &mut qvar_sets).to_string())
    })?;

    let all_qvars: HashSet<String> = qvar_sets.iter().flatten().cloned().collect();
    let free_pins = if let Some(p) = field {
        rules::contribute_free(&out, &all_qvars, p)
    } else {
        Vec::new()
    };
    if !free_pins.is_empty() {
        applied.insert("rules-free".to_string(), free_pins.len());
    }

    let mut commands = out.commands;
    if !free_pins.is_empty() {
        let insert_idx = commands
            .iter()
            .position(|c| c.name() == "check-sat")
            .unwrap_or(commands.len());
        let mut new_cmds = Vec::with_capacity(commands.len() + free_pins.len());
        new_cmds.extend(commands[..insert_idx].iter().cloned());
        for (var, expr) in free_pins {
            new_cmds.push(smt2::parse::Command::new(format!(
                "(assert (= {var} {}))",
                expr.to_string()
            )));
        }
        new_cmds.extend(commands[insert_idx..].iter().cloned());
        commands = new_cmds;
    }

    commands.retain(|cmd| {
        if cmd.name() != "set-info" {
            return true;
        }
        !cmd.raw.contains(SKOLEM_SETINFO_PREFIX)
    });

    let out = smt2::Script::from_commands(commands);

    let stats = serde_json::json!({
        "pins_by_source": applied,
        "free_value_asserts": applied.get("rules-free").copied().unwrap_or(0),
    });
    Ok((out, stats))
}

fn walk_assert(
    term: &Term,
    declared: &HashMap<String, Term>,
    sorts: &HashMap<String, SortKind>,
    pins: &[types::SkolemPin],
    candidates: &[witness::WitnessCandidate],
    decl_block: &str,
    field: Option<i128>,
    applied: &mut HashMap<String, usize>,
    qvar_sets: &mut Vec<HashSet<String>>,
) -> Term {
    match term {
        Term::List(items) if matches!(items.first(), Some(Term::Atom(s)) if s == "forall") => {
            walk_forall(items, declared, sorts, pins, candidates, decl_block, field, applied, qvar_sets)
        }
        Term::List(items) => {
            let head = items[0].clone();
            Term::List(
                std::iter::once(head)
                    .chain(items[1..].iter().map(|a| {
                        walk_assert(a, declared, sorts, pins, candidates, decl_block, field, applied, qvar_sets)
                    }))
                    .collect(),
            )
        }
        _ => term.clone(),
    }
}

fn walk_forall(
    items: &[Term],
    declared: &HashMap<String, Term>,
    sorts: &HashMap<String, SortKind>,
    pins: &[types::SkolemPin],
    candidates: &[witness::WitnessCandidate],
    decl_block: &str,
    field: Option<i128>,
    applied: &mut HashMap<String, usize>,
    qvar_sets: &mut Vec<HashSet<String>>,
) -> Term {
    let Some((qvars, body)) = parse_forall(&Term::List(items.to_vec())) else {
        return Term::List(items.to_vec());
    };
    qvar_sets.push(qvars.iter().map(|(n, _)| n.clone()).collect());

    let mut skolem = SkolemMap::new(&qvars);
    names::contribute(&mut skolem, declared, sorts);
    derived::contribute(&mut skolem, pins);
    if let Some(p) = field {
        witness::contribute(&mut skolem, &body, candidates, p);
    }
    isolate::contribute(&mut skolem, &body, sorts, decl_block);

    for src in skolem.sources.values() {
        *applied.entry(src.clone()).or_insert(0) += 1;
    }

    let disjuncts = skolem.emit_disjuncts();
    if disjuncts.is_empty() {
        return Term::List(items.to_vec());
    }

    let new_body = if let Term::List(bitems) = &body {
        if matches!(bitems.first(), Some(Term::Atom(s)) if s == "or") {
            let mut args = bitems[1..].to_vec();
            args.extend(disjuncts);
            list("or", args)
        } else {
            list("or", std::iter::once(body.clone()).chain(disjuncts).collect())
        }
    } else {
        list("or", std::iter::once(body.clone()).chain(disjuncts).collect())
    };

    Term::List(vec![items[0].clone(), items[1].clone(), new_body])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pins_same_name_program_var() {
        let script = Script::parse(
            "(declare-fun before-x@0 () Int)\n\
             (declare-fun after-x@0 () Int)\n\
             (assert (forall ((before-x@0 Int)) (or (= before-x@0 0))))\n\
             (check-sat)\n",
        )
        .unwrap();
        std::env::set_var("SIMPLIFIER_FIELD_MOD", "2147483647");
        let (out, stats) = apply(&script).unwrap();
        let s = smt2::dump_string(&out);
        assert!(s.contains("(not (= before-x@0"));
        assert!(stats["pins_by_source"]["names"].as_u64().unwrap_or(0) >= 1);
    }
}
