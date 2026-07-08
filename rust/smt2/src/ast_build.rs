//! Z3 AST construction and traversal (replaces the old `Term` IR).

use std::collections::HashSet;

use z3::ast::{Ast, AstKind, Bool, Dynamic, Int};
use z3::{DeclKind, FuncDecl, Sort};

use crate::ast_util::{
    ast_children, decl_name, free_symbol_ids_bool, int_from_i128, is_int_const, parse_int_literal,
    quantifier_body, quantifier_bound_names, rebuild_app, rebuild_quantifier_dyn,
    scoped_free_symbol_ids, symbol_id_from_name, symbol_name_for_id, SymbolId,
};

pub fn int_atom(s: &str) -> Int {
    if let Some(v) = parse_int_literal(s) {
        return int_from_i128(v);
    }
    Int::new_const(s)
}

pub fn bool_atom(s: &str) -> Bool {
    match s {
        "true" => Bool::from_bool(true),
        "false" => Bool::from_bool(false),
        _ => Bool::new_const(s),
    }
}

pub fn list_int(head: &str, args: Vec<Int>) -> Int {
    let int_sort = Sort::int();
    let arg_sorts: Vec<&Sort> = (0..args.len()).map(|_| &int_sort).collect();
    let decl = FuncDecl::new(head, &arg_sorts, &int_sort);
    let refs: Vec<&dyn Ast> = args.iter().map(|a| a as &dyn Ast).collect();
    match head {
        "+" if !args.is_empty() => Int::add(&args.iter().collect::<Vec<_>>()),
        "*" if !args.is_empty() => Int::mul(&args.iter().collect::<Vec<_>>()),
        "-" if args.len() == 1 => Int::unary_minus(&args[0]),
        "-" if args.len() == 2 => Int::sub(&[&args[0], &args[1]]),
        "mod" if args.len() == 2 => args[0].modulo(&args[1]),
        _ => decl
            .apply(&refs)
            .as_int()
            .unwrap_or_else(|| args[0].clone()),
    }
}

pub fn list_bool(head: &str, args: Vec<Bool>) -> Bool {
    match (head, args.len()) {
        ("not", 1) => args[0].not(),
        ("and", _) if !args.is_empty() => Bool::and(&args.iter().collect::<Vec<_>>()),
        ("or", _) if !args.is_empty() => Bool::or(&args.iter().collect::<Vec<_>>()),
        ("=>", 2) => args[0].implies(&args[1]),
        ("ite", 3) => args[0].ite(&args[1], &args[2]),
        ("=", 2) => args[0].eq(&args[1]),
        _ => {
            let bool_sort = Sort::bool();
            let decl = FuncDecl::new(head, &[], &bool_sort);
            let refs: Vec<&dyn Ast> = args.iter().map(|a| a as &dyn Ast).collect();
            decl.apply(&refs).as_bool().expect("bool app")
        }
    }
}

pub fn int_literal_dyn(ast: &Dynamic) -> Option<i128> {
    if ast.kind() == AstKind::Numeral && ast.get_sort().kind() == z3::SortKind::Int {
        return ast.as_int().and_then(|i| crate::ast_util::int_value(&i));
    }
    if ast.kind() == AstKind::App
        && ast.num_children() == 1
        && ast.decl().kind() == DeclKind::Uminus
    {
        return ast.nth_child(0).and_then(|c| int_literal_dyn(&c).map(|v| -v));
    }
    None
}

pub fn symbol_name_dyn(ast: &Dynamic) -> Option<String> {
    if is_int_const(ast) || (ast.kind() == AstKind::App && ast.is_const()) {
        return Some(decl_name(&ast.decl()));
    }
    None
}

pub fn is_symbol_dyn(ast: &Dynamic) -> bool {
    symbol_name_dyn(ast).is_some()
        && ast.as_bool().is_none()
        && int_literal_dyn(ast).is_none()
}

pub struct DynNodes<'a> {
    stack: Vec<Dynamic>,
    _root: std::marker::PhantomData<&'a Dynamic>,
}

impl<'a> DynNodes<'a> {
    fn new(ast: &'a Dynamic) -> Self {
        Self {
            stack: vec![ast.clone()],
            _root: std::marker::PhantomData,
        }
    }
}

impl Iterator for DynNodes<'_> {
    type Item = Dynamic;

    fn next(&mut self) -> Option<Self::Item> {
        let ast = self.stack.pop()?;
        if ast.kind() == AstKind::Quantifier {
            if let Some(body) = quantifier_body(&ast) {
                self.stack.push(body);
            }
        } else {
            for ch in ast_children(&ast).into_iter().rev() {
                self.stack.push(ch);
            }
        }
        Some(ast)
    }
}

/// Pre-order DFS over ``ast`` and its descendants (quantifier bodies only; no binder walk).
pub fn iter_nodes_dyn(ast: &Dynamic) -> DynNodes<'_> {
    DynNodes::new(ast)
}

pub fn count_nodes_dyn(ast: &Dynamic) -> usize {
    iter_nodes_dyn(ast).count()
}

pub fn flatten_op_int(head: &str, ast: &Int) -> Vec<Int> {
    if ast.kind() == AstKind::App {
        let kind = ast.decl().kind();
        let matches = match head {
            "+" => kind == DeclKind::Add,
            "*" => kind == DeclKind::Mul,
            _ => decl_name(&ast.decl()) == head,
        };
        if matches {
            let mut out = Vec::new();
            for i in 0..ast.num_children() {
                if let Some(ch) = ast.nth_child(i).and_then(|c| c.as_int()) {
                    out.extend(flatten_op_int(head, &ch));
                }
            }
            return out;
        }
    }
    vec![ast.clone()]
}

pub fn split_product_int(f: &Int, p: i128) -> (i128, Vec<Int>) {
    let mut coeff = 1i128;
    let mut factors = Vec::new();
    for a in flatten_op_int("*", f) {
        if let Some(c) = int_literal_dyn(&Dynamic::from_ast(&a)) {
            coeff = (coeff * c).rem_euclid(p);
        } else {
            factors.push(a);
        }
    }
    (coeff, factors)
}

pub fn substitute_int(ast: &Int, name: &str, replacement: &Int) -> Int {
    if let Some(sym) = symbol_name_dyn(&Dynamic::from_ast(ast)) {
        if sym == name {
            return replacement.clone();
        }
        return ast.clone();
    }
    if ast.kind() == AstKind::App {
        let args: Vec<Int> = (0..ast.num_children())
            .filter_map(|i| {
                ast.nth_child(i)
                    .and_then(|c| c.as_int())
                    .map(|ch| substitute_int(&ch, name, replacement))
            })
            .collect();
        match ast.decl().kind() {
            DeclKind::Mod if args.len() == 2 => return args[0].modulo(&args[1]),
            DeclKind::Add if !args.is_empty() => return Int::add(&args.iter().collect::<Vec<_>>()),
            DeclKind::Mul if !args.is_empty() => return Int::mul(&args.iter().collect::<Vec<_>>()),
            DeclKind::Uminus if args.len() == 1 => return Int::unary_minus(&args[0]),
            DeclKind::Sub if args.len() == 2 => {
                return Int::sub(&[&args[0], &args[1]]);
            }
            _ => {
                let refs: Vec<&dyn Ast> = args.iter().map(|a| a as &dyn Ast).collect();
                return rebuild_app(&ast.decl(), &refs)
                    .as_int()
                    .unwrap_or_else(|| ast.clone());
            }
        }
    }
    ast.clone()
}

pub fn substitute_dyn(ast: &Dynamic, name: &str, replacement: &Dynamic) -> Dynamic {
    if let Some(sym) = symbol_name_dyn(ast) {
        if sym == name {
            return replacement.clone();
        }
        return ast.clone();
    }
    if ast.kind() == AstKind::Quantifier {
        let bound: HashSet<String> = quantifier_bound_names(ast).into_iter().collect();
        if bound.contains(name) {
            return ast.clone();
        }
        let is_forall = crate::ast_util::is_forall(ast);
        let bounds = crate::ast_util::quantifier_bounds(ast);
        let body = quantifier_body(ast).expect("body").as_bool().expect("bool body");
        let rep_b = replacement.as_bool().expect("bool replacement");
        let new_body = substitute_bool(&body, name, &rep_b);
        return Dynamic::from_ast(&rebuild_quantifier_dyn(is_forall, &bounds, &new_body));
    }
    if ast.kind() == AstKind::App {
        let args: Vec<Dynamic> = (0..ast.num_children())
            .filter_map(|i| {
                ast.nth_child(i)
                    .map(|ch| substitute_dyn(&ch, name, replacement))
            })
            .collect();
        let refs: Vec<&dyn Ast> = args.iter().map(|a| a as &dyn Ast).collect();
        return rebuild_app(&ast.decl(), &refs);
    }
    ast.clone()
}

pub fn substitute_bool(b: &Bool, name: &str, replacement: &Bool) -> Bool {
    substitute_dyn(
        &Dynamic::from_ast(b),
        name,
        &Dynamic::from_ast(replacement),
    )
    .as_bool()
    .expect("bool")
}

pub fn free_variables_bool(b: &Bool) -> HashSet<String> {
    free_symbol_ids_bool(b)
        .into_iter()
        .filter_map(|id| symbol_name_for_id(id))
        .collect()
}

pub fn scoped_free_variables_dyn(ast: &Dynamic, bound: &HashSet<String>) -> HashSet<String> {
    let bound_ids: HashSet<SymbolId> = bound.iter().map(|n| symbol_id_from_name(n)).collect();
    scoped_free_symbol_ids(ast, &bound_ids)
        .into_iter()
        .filter_map(|id| symbol_name_for_id(id))
        .collect()
}

pub fn wrap_mod_expr_int(expr: Int, p: i128) -> Int {
    expr.modulo(&int_from_i128(p))
}

pub fn eq_int(a: &Int, b: &Int) -> Bool {
    a.eq(b)
}

pub fn parse_int_or_const(s: &str) -> Int {
    int_atom(s)
}

pub fn parse_bool_formula(ctx: &mut crate::ParseCtx, raw: &str) -> Result<Bool, String> {
    let cmd = format!("(assert {raw})");
    if let Some(b) = ctx.ingest_command(&cmd)? {
        return Ok(b);
    }
    let (form, _) = crate::sexpr::SExpr::read_form(&cmd)?;
    crate::command::parse_assert(&cmd, form.span, ctx)
}
