use crate::command::SmtCommand;
use crate::script::Script;
use crate::ast_util::{decl_name, numeral_smtlib_string, quantifier_body, quantifier_bound_names, smtlib_decl_name, z3_if_to_ite};
use z3::ast::{Ast, AstKind, Bool, Dynamic};

const INDENT: &str = "    ";

pub fn pretty_print_bool_in_script(b: &Bool) -> String {
    let mut out = String::new();
    print_top_level(&mut out, &Dynamic::from_ast(b), 0, false, true);
    z3_if_to_ite(&out)
}

pub fn pretty_print_bool(b: &Bool) -> String {
    let mut out = String::new();
    print_term(&mut out, &Dynamic::from_ast(b), 0, false);
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

fn should_collapse(ast: &Dynamic, depth: usize, is_collapsed: bool) -> bool {
    is_collapsed
        || depth > 10
        || ast_size_lt(ast, COLLAPSE_SIZE)
        || (ast.kind() == AstKind::App
            && ast.num_children() > 0
            && (1..ast.num_children()).all(|i| {
                ast.nth_child(i)
                    .is_some_and(|c| c.kind() == AstKind::App && c.is_const())
            }))
}

fn print_top_level(out: &mut String, ast: &Dynamic, depth: usize, is_collapsed: bool, in_script: bool) {
    if in_script && !should_collapse(ast, depth, is_collapsed) {
        out.push('\n');
        print_term(out, ast, depth + 1, is_collapsed);
        out.push('\n');
    } else {
        print_term(out, ast, depth, is_collapsed);
    }
}

fn print_term(out: &mut String, ast: &Dynamic, depth: usize, is_collapsed: bool) {
    match ast.kind() {
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
        AstKind::App => print_app(out, ast, depth, is_collapsed),
        AstKind::Quantifier => print_quantifier_node(out, ast, depth, is_collapsed),
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

fn print_app(out: &mut String, ast: &Dynamic, depth: usize, is_collapsed: bool) {
    let head = smtlib_decl_name(&ast.decl());
    let children = ast_children_slice(ast);

    if matches!(head.as_str(), "forall" | "exists") && children.len() >= 2 {
        print_quantifier(out, &head, &children[0], &children[1], depth, is_collapsed);
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
            print_term(out, ch, depth, true);
        }
        out.push(')');
    } else {
        write_indent(out, depth);
        out.push('(');
        out.push_str(&head);
        out.push('\n');
        for ch in &children {
            print_term(out, ch, depth + 1, is_collapsed);
            out.push('\n');
        }
        write_indent(out, depth);
        out.push(')');
    }
}

fn print_quantifier_node(out: &mut String, ast: &Dynamic, depth: usize, is_collapsed: bool) {
    let op = if crate::ast_util::is_forall(ast) {
        "forall"
    } else {
        "exists"
    };
    let body = quantifier_body(ast).expect("quantifier body");
    let names = quantifier_bound_names(ast);
    let binders: Vec<String> = names
        .into_iter()
        .map(|n| format!("({n} Int)"))
        .collect();
    let binders_ast = Dynamic::from_ast(&Bool::from_bool(true));
    let _ = binders_ast;
    write_indent(out, depth);
    out.push('(');
    out.push_str(op);
    out.push_str(" (");
    out.push_str(&binders.join(" "));
    out.push_str(")\n");
    print_term(out, &body, depth + 1, is_collapsed);
    out.push('\n');
    write_indent(out, depth);
    out.push(')');
}

fn print_quantifier(
    out: &mut String,
    op: &str,
    binders: &Dynamic,
    body: &Dynamic,
    depth: usize,
    is_collapsed: bool,
) {
    let mut binder_strs: Vec<String> = Vec::new();
    if binders.kind() == AstKind::App && decl_name(&binders.decl()) == "and" {
        for ch in ast_children_slice(binders) {
            binder_strs.push(ch.to_string());
        }
    } else {
        binder_strs.push(binders.to_string());
    }
    binder_strs.sort();
    write_indent(out, depth);
    out.push('(');
    out.push_str(op);
    out.push_str(" (");
    out.push_str(&binder_strs.join(" "));
    out.push_str(")\n");
    print_term(out, body, depth + 1, is_collapsed);
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
