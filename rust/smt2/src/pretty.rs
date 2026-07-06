use crate::command::SmtCommand;
use crate::script::Script;
use crate::ast_util::{
    bound_var_index, decl_name, de_bruijn_bound_name, is_forall, numeral_smtlib_string,
    quantifier_body, quantifier_bound_names, quantifier_bounds, smtlib_decl_name, z3_if_to_ite,
};
use z3::ast::{Ast, AstKind, Bool, Dynamic};
use z3::SortKind;

const INDENT: &str = "    ";

pub fn pretty_print_bool_in_script(b: &Bool) -> String {
    let mut out = String::new();
    print_top_level(&mut out, &Dynamic::from_ast(b), 0, false, true, &[]);
    z3_if_to_ite(&out)
}

pub fn pretty_print_bool(b: &Bool) -> String {
    let mut out = String::new();
    print_term(&mut out, &Dynamic::from_ast(b), 0, false, &[]);
    z3_if_to_ite(&out)
}

pub fn pretty_print_command(cmd: &SmtCommand) -> Result<SmtCommand, String> {
    match cmd {
        SmtCommand::Assert { bool: b, span, .. } => {
            let pretty = pretty_print_bool_in_script(b);
            Ok(SmtCommand::Assert {
                bool: b.clone(),
                span: *span,
                term_text: Some(pretty),
            })
        }
        other => Ok(other.clone()),
    }
}

pub fn pretty_print_script(script: &Script) -> Result<Script, String> {
    let commands = script
        .commands
        .iter()
        .map(pretty_print_command)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Script::from_commands(&script.source, commands))
}

const COLLAPSE_SIZE: usize = 10;

fn is_collapsible(ast: &Dynamic) -> bool {
    match ast.kind() {
        AstKind::Numeral => true,
        AstKind::App if ast.is_const() => true,
        AstKind::App if ast.num_children() == 1 && decl_name(&ast.decl()) == "-" => ast
            .nth_child(0)
            .is_some_and(|c| c.kind() == AstKind::Numeral),
        _ => false,
    }
}

fn should_collapse(ast: &Dynamic, depth: usize, is_collapsed: bool) -> bool {
    is_collapsed
        || depth > 10
        || ast_size_lt(ast, COLLAPSE_SIZE)
        || (ast.kind() == AstKind::App
            && ast.num_children() > 0
            && (0..ast.num_children()).all(|i| {
                ast.nth_child(i).is_some_and(|c| is_collapsible(&c))
            }))
}

fn print_top_level(
    out: &mut String,
    ast: &Dynamic,
    depth: usize,
    is_collapsed: bool,
    in_script: bool,
    bound_order: &[String],
) {
    if in_script && !should_collapse(ast, depth, is_collapsed) {
        out.push('\n');
        print_term(out, ast, depth + 1, is_collapsed, bound_order);
        out.push('\n');
    } else {
        print_term(out, ast, depth, is_collapsed, bound_order);
    }
}

fn print_term(
    out: &mut String,
    ast: &Dynamic,
    depth: usize,
    is_collapsed: bool,
    bound_order: &[String],
) {
    match ast.kind() {
        AstKind::Var => {
            if !is_collapsed {
                write_indent(out, depth);
            }
            if let Some(idx) = bound_var_index(ast) {
                if let Some(name) = de_bruijn_bound_name(bound_order, idx) {
                    out.push_str(&name);
                    return;
                }
            }
            out.push_str(&ast.to_string());
        }
        AstKind::App if ast.is_const() => {
            if !is_collapsed {
                write_indent(out, depth);
            }
            out.push_str(&decl_name(&ast.decl()));
        }
        AstKind::Numeral => {
            if !is_collapsed {
                write_indent(out, depth);
            }
            match numeral_smtlib_string(ast) {
                Some(s) => out.push_str(&s),
                None => out.push_str(&ast.to_string()),
            }
        }
        AstKind::App => print_app(out, ast, depth, is_collapsed, bound_order),
        AstKind::Quantifier => print_quantifier_node(out, ast, depth, is_collapsed, bound_order),
        _ => {
            if !is_collapsed {
                write_indent(out, depth);
            }
            out.push_str(&ast.to_string());
        }
    }
}

fn ast_children_slice(ast: &Dynamic) -> Vec<Dynamic> {
    (0..ast.num_children())
        .filter_map(|i| ast.nth_child(i))
        .collect()
}

fn print_app(
    out: &mut String,
    ast: &Dynamic,
    depth: usize,
    is_collapsed: bool,
    bound_order: &[String],
) {
    let head = smtlib_decl_name(&ast.decl());
    let children = ast_children_slice(ast);

    if matches!(head.as_str(), "forall" | "exists") && children.len() >= 2 {
        print_quantifier(out, &head, &children[0], &children[1], depth, is_collapsed, bound_order);
        return;
    }

    if should_collapse(ast, depth, is_collapsed) {
        if !is_collapsed {
            write_indent(out, depth);
        }
        out.push('(');
        out.push_str(&head);
        for ch in &children {
            out.push(' ');
            print_term(out, ch, depth, true, bound_order);
        }
        out.push(')');
    } else {
        write_indent(out, depth);
        out.push('(');
        out.push_str(&head);
        out.push('\n');
        for ch in &children {
            print_term(out, ch, depth + 1, is_collapsed, bound_order);
            out.push('\n');
        }
        write_indent(out, depth);
        out.push(')');
    }
}

fn print_quantifier_node(
    out: &mut String,
    ast: &Dynamic,
    depth: usize,
    is_collapsed: bool,
    bound_order: &[String],
) {
    let op = if is_forall(ast) { "forall" } else { "exists" };
    let body = quantifier_body(ast).expect("quantifier body");
    let binders = quantifier_binder_strings(ast);
    let bound_names = quantifier_bound_names(ast);
    print_quantifier_formatted(
        out,
        op,
        &binders,
        &body,
        &bound_names,
        bound_order,
        depth,
        is_collapsed,
    );
}

fn print_quantifier(
    out: &mut String,
    op: &str,
    binders: &Dynamic,
    body: &Dynamic,
    depth: usize,
    is_collapsed: bool,
    bound_order: &[String],
) {
    let binder_strs = quantifier_binder_strings_from_app(binders);
    let bound_names = quantifier_bound_names_from_app(binders);
    print_quantifier_formatted(
        out,
        op,
        &binder_strs,
        body,
        &bound_names,
        bound_order,
        depth,
        is_collapsed,
    );
}

fn quantifier_binder_string(bound: &Dynamic) -> Option<String> {
    let name = crate::ast_build::symbol_name_dyn(bound)?;
    let sort = match bound.get_sort().kind() {
        SortKind::Bool => "Bool",
        _ => "Int",
    };
    Some(format!("({name} {sort})"))
}

fn quantifier_binder_strings_from_app(binders: &Dynamic) -> Vec<String> {
    let mut out = Vec::new();
    if binders.kind() == AstKind::App && decl_name(&binders.decl()) == "and" {
        for ch in ast_children_slice(binders) {
            out.push(binder_string_from_dyn(&ch));
        }
    } else {
        out.push(binder_string_from_dyn(binders));
    }
    out.sort();
    out
}

fn quantifier_binder_strings(ast: &Dynamic) -> Vec<String> {
    let mut binders = if ast.kind() == AstKind::Quantifier {
        quantifier_bounds(ast)
            .iter()
            .filter_map(|b| quantifier_binder_string(b))
            .collect()
    } else {
        quantifier_binder_strings_from_app(ast)
    };
    binders.sort();
    binders
}

fn quantifier_bound_names_from_app(binders: &Dynamic) -> Vec<String> {
    if binders.kind() == AstKind::App && decl_name(&binders.decl()) == "and" {
        ast_children_slice(binders)
            .iter()
            .filter_map(|ch| crate::ast_build::symbol_name_dyn(ch))
            .collect()
    } else {
        crate::ast_build::symbol_name_dyn(binders).into_iter().collect()
    }
}

fn binder_string_from_dyn(ch: &Dynamic) -> String {
    quantifier_binder_string(ch).unwrap_or_else(|| ch.to_string())
}

fn print_quantifier_formatted(
    out: &mut String,
    op: &str,
    binders: &[String],
    body: &Dynamic,
    bound_names: &[String],
    bound_order: &[String],
    depth: usize,
    is_collapsed: bool,
) {
    let binders_len: usize = binders.iter().map(|s| s.len()).sum::<usize>() + binders.len();
    let mut body_bound_order: Vec<String> = bound_order.to_vec();
    body_bound_order.extend_from_slice(bound_names);

    write_indent(out, depth);
    out.push('(');
    out.push_str(op);

    if binders_len < 50 {
        out.push_str(" (");
        for b in binders {
            out.push_str(b);
            out.push(' ');
        }
        out.push_str(")\n");
    } else {
        out.push('\n');
        write_indent(out, depth + 1);
        out.push_str("(\n");
        for b in binders {
            write_indent(out, depth + 2);
            out.push_str(b);
            out.push('\n');
        }
        write_indent(out, depth + 1);
        out.push_str(")\n");
    }

    print_term(out, body, depth + 1, is_collapsed, &body_bound_order);
    out.push('\n');
    write_indent(out, depth);
    out.push(')');
}

fn write_indent(out: &mut String, depth: usize) {
    for _ in 0..depth {
        out.push_str(INDENT);
    }
}

/// Whether ``ast``'s node count is below ``limit``. Stops walking once the
/// limit is reached, so this is O(limit) rather than O(subtree).
fn ast_size_lt(ast: &Dynamic, limit: usize) -> bool {
    let mut count = 0usize;
    accumulate_size(ast, limit, &mut count);
    count < limit
}

fn accumulate_size(ast: &Dynamic, limit: usize, count: &mut usize) {
    if *count >= limit {
        return;
    }
    if ast.kind() == AstKind::App {
        if ast.num_children() == 1 && decl_name(&ast.decl()) == "-" {
            if let Some(ch) = ast.nth_child(0) {
                if ch.kind() == AstKind::Numeral {
                    *count += 1;
                    return;
                }
            }
        }
        *count += 1;
        for i in 0..ast.num_children() {
            if *count >= limit {
                return;
            }
            if let Some(ch) = ast.nth_child(i) {
                accumulate_size(&ch, limit, count);
            }
        }
    } else {
        *count += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ParseCtx;

    fn has_z3() -> bool {
        std::process::Command::new("pkg-config")
            .args(["--exists", "z3"])
            .status()
            .map(|s| s.success())
            .unwrap_or(false)
    }

    #[test]
    fn small_and_collapsed() {
        if !has_z3() {
            return;
        }
        let mut ctx = ParseCtx::new();
        let b = ctx
            .ingest_command("(assert (and a b))")
            .unwrap()
            .unwrap();
        assert_eq!(pretty_print_bool(&b), "(and a b)");
    }

    #[test]
    fn not_le_expands() {
        if !has_z3() {
            return;
        }
        let mut ctx = ParseCtx::new();
        ctx.ingest_command("(declare-fun a () Int)").unwrap();
        ctx.ingest_command("(declare-fun b () Int)").unwrap();
        let b = ctx
            .ingest_command("(assert (not (<= (+ a b) 0)))")
            .unwrap()
            .unwrap();
        let s = pretty_print_bool_in_script(&b);
        assert!(s.contains('\n'), "expected multiline pretty-print: {s}");
        assert!(s.contains("(not\n"));
    }

    #[test]
    fn quantifier_short_sorted() {
        if !has_z3() {
            return;
        }
        let mut ctx = ParseCtx::new();
        ctx.ingest_command("(declare-fun a () Bool)").unwrap();
        let b = ctx
            .ingest_command("(assert (forall ((x Int) (flag Bool)) (or (not flag) (= x 0))))")
            .unwrap()
            .unwrap();
        let s = pretty_print_bool_in_script(&b);
        assert!(s.contains("(forall ( (flag Bool) (x Int) )"), "got: {s}");
        assert!(s.contains("(or (not flag) (= x 0))"));
    }

    #[test]
    fn quantifier_long_multiline_binders() {
        if !has_z3() {
            return;
        }
        let mut ctx = ParseCtx::new();
        for i in 0..20 {
            ctx.ingest_command(&format!("(declare-fun v{i} () Int)"))
                .unwrap();
        }
        let bounds = (0..20)
            .map(|i| format!("(v{i} Int)"))
            .collect::<Vec<_>>()
            .join(" ");
        let b = ctx
            .ingest_command(&format!("(assert (forall ({bounds}) (= v0 v1)))"))
            .unwrap()
            .unwrap();
        let s = pretty_print_bool_in_script(&b);
        assert!(s.contains("(forall\n"), "expected forall on its own line: {s}");
        assert!(s.contains("\n                (v0 Int)\n"), "got: {s}");
    }

    #[test]
    fn quantifier_body_uses_binder_names() {
        if !has_z3() {
            return;
        }
        let mut ctx = ParseCtx::new();
        let b = ctx
            .ingest_command("(assert (forall ((x Int)) (= x x)))")
            .unwrap()
            .unwrap();
        let s = pretty_print_bool_in_script(&b);
        assert!(!s.contains(":var"), "pretty-print must not emit de Bruijn vars: {s}");
        assert!(s.contains("(= x x)"), "got: {s}");
    }

    #[test]
    fn nested_quantifier_body_uses_outer_binder_names() {
        if !has_z3() {
            return;
        }
        let mut ctx = ParseCtx::new();
        let b = ctx
            .ingest_command("(assert (forall ((x Int)) (forall ((y Int)) (= x y))))")
            .unwrap()
            .unwrap();
        let s = pretty_print_bool_in_script(&b);
        assert!(!s.contains(":var"), "pretty-print must not emit de Bruijn vars: {s}");
        assert!(s.contains("(= x y)"), "got: {s}");
    }

    #[test]
    fn pretty_assert_command() {
        if !has_z3() {
            return;
        }
        let mut ctx = ParseCtx::new();
        let b = ctx
            .ingest_command("(assert (and a b))")
            .unwrap()
            .unwrap();
        let cmd = SmtCommand::new_assert(b);
        let out = pretty_print_command(&cmd).unwrap();
        assert!(matches!(out, SmtCommand::Assert { term_text: Some(_), .. }));
    }
}
