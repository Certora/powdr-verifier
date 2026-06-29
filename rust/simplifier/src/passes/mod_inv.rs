//! Interpret ``uf_mod_inv`` as field inverse constraints.

use std::collections::{HashMap, HashSet};

use smt2::{Script, Term};
use smt2::parse::Command;

use crate::passes::skolem::term_util::{
    atom, field_mod, flatten_op, int_literal, is_symbol, list, wrap_mod_expr,
};
use crate::passes::skolem::utils::declare_fun_name;

const UF_MOD_INV: &str = "uf_mod_inv";

pub fn apply(script: &Script) -> Result<(Script, serde_json::Value), String> {
    let field = field_mod().ok_or("SIMPLIFIER_FIELD_MOD not set")?;
    if !contains_mod_inv(script) {
        return Ok((
            script.clone(),
            serde_json::json!({
                "definition_folds": 0,
                "fallback_asserts": 0,
                "fallback_inverse_constraints": 0,
                "fallback_fresh_symbols": 0,
            }),
        ));
    }

    let mut declared: HashSet<String> = script
        .commands
        .iter()
        .filter(|c| c.name() == "declare-fun")
        .filter_map(|c| declare_fun_name(&c.raw))
        .collect();

    let mut definition_folds = 0usize;
    let mut fallback_asserts = 0usize;
    let mut fallback_constraints = 0usize;
    let mut fallback_fresh_symbols = 0usize;
    let mut out = Vec::new();

    for cmd in &script.commands {
        if cmd.name() != "assert" {
            out.push(cmd.clone());
            continue;
        }
        let body = smt2::term::assert_body(&cmd.raw)
            .ok_or_else(|| format!("malformed assert: {}", cmd.raw))?;
        let term = Term::parse(&body)?;

        if let Some((var, t, c, p)) = match_mod_inv_definition(&term) {
            definition_folds += 1;
            let zero = atom("0");
            let mod_t = wrap_mod_expr(t.clone(), field);
            out.push(Command::new(format!(
                "(assert {})",
                list("=>", vec![list("=", vec![mod_t.clone(), zero.clone()]), list("=", vec![var.clone(), zero.clone()])]).to_string()
            )));
            let mod_tv = wrap_mod_expr(list("*", vec![t, var]), field);
            let mod_c = if structurally_equal(&p, &atom(&field.to_string())) {
                wrap_mod_expr(c, field)
            } else {
                list("mod", vec![c, p])
            };
            out.push(Command::new(format!(
                "(assert {})",
                list(
                    "=>",
                    vec![
                        list("not", vec![list("=", vec![mod_t, zero])]),
                        list("=", vec![mod_tv, mod_c]),
                    ],
                )
                .to_string()
            )));
            continue;
        }

        let mut rewriter = FallbackRewriter::new(field);
        let rewritten = rewriter.rewrite(&term);
        if rewriter.touched {
            fallback_asserts += 1;
            fallback_constraints += rewriter.constraints.len();
            fallback_fresh_symbols += rewriter.new_symbols.len();
            for name in &rewriter.new_symbols {
                if declared.contains(name) {
                    continue;
                }
                out.push(Command::new(format!("(declare-fun {name} () Int)")));
                declared.insert(name.clone());
            }
            out.push(Command::new(format!(
                "(assert {})",
                rewritten.to_string()
            )));
            for c in &rewriter.constraints {
                out.push(Command::new(format!("(assert {})", c.to_string())));
            }
        } else {
            out.push(cmd.clone());
        }
    }

    Ok((
        Script::from_commands(out),
        serde_json::json!({
            "definition_folds": definition_folds,
            "fallback_asserts": fallback_asserts,
            "fallback_inverse_constraints": fallback_constraints,
            "fallback_fresh_symbols": fallback_fresh_symbols,
        }),
    ))
}

fn contains_mod_inv(script: &Script) -> bool {
    for cmd in &script.commands {
        if cmd.name() != "assert" {
            continue;
        }
        if let Some(body) = smt2::term::assert_body(&cmd.raw) {
            if let Ok(term) = Term::parse(&body) {
                if contains_mod_inv_term(&term) {
                    return true;
                }
            }
        }
    }
    false
}

fn contains_mod_inv_term(term: &Term) -> bool {
    for node in iter_nodes(term) {
        if uf_mod_inv_arg(&node).is_some() {
            return true;
        }
    }
    false
}

fn iter_nodes(f: &Term) -> Vec<Term> {
    let mut out = Vec::new();
    walk_nodes(f, &mut out);
    out
}

fn walk_nodes(f: &Term, out: &mut Vec<Term>) {
    out.push(f.clone());
    if let Term::List(items) = f {
        for a in &items[1..] {
            walk_nodes(a, out);
        }
    }
}

fn structurally_equal(a: &Term, b: &Term) -> bool {
    a.to_string() == b.to_string()
}

fn unwrap_mod(term: &Term) -> Option<(Term, Term)> {
    let Term::List(items) = term else {
        return None;
    };
    if !matches!(items.first(), Some(Term::Atom(s)) if s == "mod") || items.len() != 3 {
        return None;
    }
    Some((items[1].clone(), items[2].clone()))
}

fn is_ite(term: &Term) -> Option<(Term, Term, Term)> {
    let Term::List(items) = term else {
        return None;
    };
    if !matches!(items.first(), Some(Term::Atom(s)) if s == "ite") || items.len() != 4 {
        return None;
    }
    Some((items[1].clone(), items[2].clone(), items[3].clone()))
}

fn eq_zero_side(eq: &Term) -> Option<Term> {
    let Term::List(items) = eq else {
        return None;
    };
    if !matches!(items.first(), Some(Term::Atom(s)) if s == "=") || items.len() != 3 {
        return None;
    }
    if int_literal(&items[1]) == Some(0) {
        return Some(items[2].clone());
    }
    if int_literal(&items[2]) == Some(0) {
        return Some(items[1].clone());
    }
    None
}

fn strip_mod_var(t: &Term, p: &mut Option<Term>) -> Option<Term> {
    if let Some((inner, mod_p)) = unwrap_mod(t) {
        if let Some(existing) = p {
            if !structurally_equal(existing, &mod_p) {
                return None;
            }
        } else {
            *p = Some(mod_p);
        }
        Some(inner)
    } else {
        Some(t.clone())
    }
}

fn match_mod_inv_definition(formula: &Term) -> Option<(Term, Term, Term, Term)> {
    let Term::List(items) = formula else {
        return None;
    };
    if !matches!(items.first(), Some(Term::Atom(s)) if s == "=") || items.len() != 3 {
        return None;
    }
    if !is_symbol(&items[1]) {
        return None;
    }
    let var = items[1].clone();

    let mut p: Option<Term> = None;
    let rhs = if let Some((inner, mod_p)) = unwrap_mod(&items[2]) {
        p = Some(mod_p);
        inner
    } else {
        items[2].clone()
    };

    let (cond, then_br, else_br) = is_ite(&rhs)?;
    if int_literal(&then_br) != Some(0) {
        return None;
    }
    let t_raw = eq_zero_side(&cond)?;
    let t_var = strip_mod_var(&t_raw, &mut p)?;

    let (factors, inv_idx) = parse_inv_product(&else_br)?;
    let inv_of_raw = uf_mod_inv_arg(&factors[inv_idx])?;
    let inv_of = strip_mod_var(&inv_of_raw, &mut p)?;
    if !structurally_equal(&inv_of, &t_var) {
        return None;
    }
    let p = p?;
    let others: Vec<Term> = factors
        .iter()
        .enumerate()
        .filter(|(i, _)| *i != inv_idx)
        .map(|(_, t)| t.clone())
        .collect();
    let c = if others.is_empty() {
        atom("1")
    } else if others.len() == 1 {
        others[0].clone()
    } else {
        list("*", others)
    };
    Some((var, t_var, c, p))
}

fn uf_mod_inv_arg(term: &Term) -> Option<Term> {
    let Term::List(items) = term else {
        return None;
    };
    if !matches!(items.first(), Some(Term::Atom(s)) if s == UF_MOD_INV) || items.len() != 2 {
        return None;
    }
    Some(items[1].clone())
}

fn parse_inv_product(term: &Term) -> Option<(Vec<Term>, usize)> {
    if uf_mod_inv_arg(term).is_some() {
        return Some((vec![term.clone()], 0));
    }
    let factors = flatten_op("*", term);
    if factors.len() <= 1 {
        return None;
    }
    for (i, f) in factors.iter().enumerate() {
        if uf_mod_inv_arg(f).is_some() {
            return Some((factors, i));
        }
    }
    None
}

struct FallbackRewriter {
    field: i128,
    fresh_counter: usize,
    replacement_by_term: HashMap<String, Term>,
    pub new_symbols: Vec<String>,
    pub constraints: Vec<Term>,
    pub touched: bool,
}

impl FallbackRewriter {
    fn new(field: i128) -> Self {
        Self {
            field,
            fresh_counter: 0,
            replacement_by_term: HashMap::new(),
            new_symbols: Vec::new(),
            constraints: Vec::new(),
            touched: false,
        }
    }

    fn fresh_symbol(&mut self) -> Term {
        let name = format!("__mod_inv_{}", self.fresh_counter);
        self.fresh_counter += 1;
        self.new_symbols.push(name.clone());
        atom(&name)
    }

    fn rewrite(&mut self, formula: &Term) -> Term {
        self.rewrite_node(formula)
    }

    fn rewrite_node(&mut self, node: &Term) -> Term {
        if is_quantifier(node) {
            return node.clone();
        }
        if let Some(arg) = uf_mod_inv_arg(node) {
            let t = self.rewrite_node(&arg);
            let key = format!("(uf_mod_inv {})", t.to_string());
            if let Some(repl) = self.replacement_by_term.get(&key) {
                return repl.clone();
            }
            let replacement = self.fresh_symbol();
            let mod_t = wrap_mod_expr(t.clone(), self.field);
            let zero = atom("0");
            let one = atom("1");
            self.constraints.push(list(
                "=>",
                vec![
                    list("not", vec![list("=", vec![mod_t, zero])]),
                    list(
                        "=",
                        vec![
                            wrap_mod_expr(list("*", vec![replacement.clone(), t]), self.field),
                            one,
                        ],
                    ),
                ],
            ));
            self.replacement_by_term.insert(key, replacement.clone());
            self.touched = true;
            return replacement;
        }
        let Term::List(items) = node else {
            return node.clone();
        };
        let head = items[0].clone();
        let rewritten: Vec<Term> = items[1..]
            .iter()
            .map(|a| self.rewrite_node(a))
            .collect();
        Term::List(std::iter::once(head).chain(rewritten).collect())
    }
}

fn is_quantifier(term: &Term) -> bool {
    matches!(
        term,
        Term::List(items)
            if matches!(items.first(), Some(Term::Atom(s)) if s == "forall" || s == "exists")
                && items.len() >= 3
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn replaces_uf_with_fresh_symbol() {
        std::env::set_var("SIMPLIFIER_FIELD_MOD", "2013265921");
        let script = Script::parse(
            "(declare-fun uf_mod_inv (Int) Int)\n(declare-fun x () Int)\n(assert (= (uf_mod_inv x) 7))\n(check-sat)\n",
        )
        .unwrap();
        let (out, stats) = apply(&script).unwrap();
        assert_eq!(stats["fallback_asserts"], 1);
        let s = smt2::dump_string(&out);
        assert!(s.contains("__mod_inv_0"));
        assert!(s.contains("(declare-fun __mod_inv_0 () Int)"));
        assert!(s.contains("(mod (* __mod_inv_0 x) 2013265921) 1"));
    }

    #[test]
    fn noop_without_uf() {
        std::env::set_var("SIMPLIFIER_FIELD_MOD", "2013265921");
        let script = Script::parse("(declare-fun x () Int)\n(assert (= x 1))\n(check-sat)\n").unwrap();
        let (out, stats) = apply(&script).unwrap();
        assert_eq!(stats["definition_folds"], 0);
        assert_eq!(stats["fallback_asserts"], 0);
        assert_eq!(smt2::dump_string(&out), smt2::dump_string(&script));
    }

    #[test]
    fn skips_quantifier_body() {
        std::env::set_var("SIMPLIFIER_FIELD_MOD", "2013265921");
        let script = Script::parse(
            "(declare-fun uf_mod_inv (Int) Int)\n(declare-fun y () Int)\n(assert (forall ((x Int)) (= (uf_mod_inv x) y)))\n(check-sat)\n",
        )
        .unwrap();
        let (out, stats) = apply(&script).unwrap();
        assert_eq!(stats["fallback_asserts"], 0);
        let s = smt2::dump_string(&out);
        assert!(s.contains("(uf_mod_inv x)"));
        assert!(!s.contains("__mod_inv_"));
    }
}
