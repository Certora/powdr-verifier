//! Interpret ``uf_mod_inv`` as field inverse constraints.

use std::collections::{HashMap, HashSet};

use smt2::ast_util::{decl_name, rebuild_app};
use smt2::{Script, SmtCommand};
use z3::ast::{Ast, AstKind, Bool, Dynamic, Int};
use crate::expr_util::AssertBuildCtx;

const UF_MOD_INV: &str = "uf_mod_inv";

pub fn apply(script: &Script) -> Result<(Script, serde_json::Value), String> {
    let field = std::env::var("SIMPLIFIER_FIELD_MOD")
        .ok()
        .and_then(|s| s.parse::<i128>().ok())
        .ok_or("SIMPLIFIER_FIELD_MOD not set")?;
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

    let mut ctx = AssertBuildCtx::from_script(script)?;
    let mut out = Vec::new();
    let mut fallback_asserts = 0usize;
    let mut fallback_constraints = 0usize;
    let mut fallback_fresh_symbols = 0usize;
    let mut declared_fresh = HashSet::<String>::new();

    for cmd in &script.commands {
        let Some(b) = cmd.assert_bool() else {
            out.push(cmd.clone());
            continue;
        };
        let mut rw = FallbackRewriter::new(field);
        let rewritten = rw.rewrite_bool(b);
        if !rw.touched {
            out.push(cmd.clone());
            continue;
        }
        fallback_asserts += 1;
        fallback_constraints += rw.constraints.len();
        for name in rw.new_symbols {
            if declared_fresh.insert(name.clone()) {
                fallback_fresh_symbols += 1;
                ctx.push_raw(&mut out, &format!("(declare-fun {name} () Int)"))?;
            }
        }
        ctx.push_assert(&mut out, &rewritten)?;
        for c in rw.constraints {
            ctx.push_assert(&mut out, &c)?;
        }
    }

    Ok((
        Script::from_commands(&script.source, out),
        serde_json::json!({
            "definition_folds": 0,
            "fallback_asserts": fallback_asserts,
            "fallback_inverse_constraints": fallback_constraints,
            "fallback_fresh_symbols": fallback_fresh_symbols,
        }),
    ))
}

fn contains_mod_inv(script: &Script) -> bool {
    script
        .commands
        .iter()
        .filter_map(SmtCommand::assert_bool)
        .any(contains_mod_inv_bool)
}

fn contains_mod_inv_bool(b: &Bool) -> bool {
    let mut stack = vec![Dynamic::from_ast(b)];
    while let Some(node) = stack.pop() {
        if node.kind() == AstKind::App && decl_name(&node.decl()) == UF_MOD_INV {
            return true;
        }
        if node.kind() == AstKind::Quantifier {
            continue;
        }
        for ch in node.children() {
            stack.push(ch);
        }
    }
    false
}

struct FallbackRewriter {
    field: i128,
    fresh_counter: usize,
    replacement_by_term: HashMap<String, Int>,
    new_symbols: Vec<String>,
    constraints: Vec<Bool>,
    touched: bool,
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

    fn fresh_symbol(&mut self) -> Int {
        let name = format!("__mod_inv_{}", self.fresh_counter);
        self.fresh_counter += 1;
        self.new_symbols.push(name.clone());
        Int::new_const(name.as_str())
    }

    fn rewrite_bool(&mut self, b: &Bool) -> Bool {
        self.rewrite_dynamic(&Dynamic::from_ast(b))
            .as_bool()
            .unwrap_or_else(|| b.clone())
    }

    fn rewrite_dynamic(&mut self, node: &Dynamic) -> Dynamic {
        if node.kind() == AstKind::Quantifier {
            return node.clone();
        }
        if node.kind() == AstKind::App && decl_name(&node.decl()) == UF_MOD_INV && node.num_children() == 1 {
            if let Some(arg) = node.nth_child(0).and_then(|c| c.as_int()) {
                let t = self.rewrite_int(&arg);
                let key = format!("(uf_mod_inv {t})");
                if let Some(repl) = self.replacement_by_term.get(&key) {
                    return Dynamic::from_ast(repl);
                }
                let replacement = self.fresh_symbol();
                let p = Int::from_i64(self.field as i64);
                let zero = Int::from_i64(0);
                let one = Int::from_i64(1);
                let mod_t = t.modulo(&p);
                let premise = mod_t.eq(&zero).not();
                let concl = Int::mul(&[&replacement, &t]).modulo(&p).eq(&one);
                self.constraints.push(premise.implies(&concl));
                self.replacement_by_term.insert(key, replacement.clone());
                self.touched = true;
                return Dynamic::from_ast(&replacement);
            }
        }
        if node.kind() != AstKind::App {
            return node.clone();
        }
        let args: Vec<Dynamic> = node
            .children()
            .into_iter()
            .map(|ch| self.rewrite_dynamic(&ch))
            .collect();
        let refs: Vec<&dyn Ast> = args.iter().map(|a| a as &dyn Ast).collect();
        rebuild_app(&node.decl(), &refs)
    }

    fn rewrite_int(&mut self, i: &Int) -> Int {
        self.rewrite_dynamic(&Dynamic::from_ast(i))
            .as_int()
            .unwrap_or_else(|| i.clone())
    }
}
