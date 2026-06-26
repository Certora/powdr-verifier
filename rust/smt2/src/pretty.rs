//! S-expression pretty-printing (Python ``SMTPrettyPrinter`` parity).

use crate::parse::Command;
use crate::script::Script;
use crate::term::{assert_body, Term};

const INDENT: &str = "    ";

/// Pretty-print a formula for use inside an ``assert`` command.
pub fn pretty_print_term_in_script(term: &Term) -> String {
    let mut out = String::new();
    print_top_level(&mut out, term, 0, false, true);
    out
}

/// Pretty-print a formula.
pub fn pretty_print_term(term: &Term) -> String {
    let mut out = String::new();
    print_term(&mut out, term, 0, false);
    out
}

/// Rewrite ``assert`` commands to pretty-printed form; other commands unchanged.
pub fn pretty_print_command(cmd: &Command) -> Result<Command, String> {
    if cmd.name() != "assert" {
        return Ok(cmd.clone());
    }
    let body = assert_body(&cmd.raw).ok_or_else(|| format!("malformed assert: {}", cmd.raw))?;
    let term = Term::parse(&body)?;
    let pretty = pretty_print_term_in_script(&term);
    let trimmed = pretty.trim_end();
    let raw = if trimmed.starts_with('\n') {
        format!("(assert {trimmed}\n)")
    } else {
        format!("(assert {trimmed})")
    };
    Ok(Command::new(raw))
}

pub fn pretty_print_script(script: &Script) -> Result<Script, String> {
    let commands = script
        .commands
        .iter()
        .map(pretty_print_command)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Script::from_commands(commands))
}

fn should_collapse(term: &Term, depth: usize, is_collapsed: bool) -> bool {
    is_collapsed
        || depth > 10
        || term_size(term) < 10
        || matches!(term, Term::List(items) if items.len() > 1 && all_collapsible(&items[1..]))
}

fn print_top_level(out: &mut String, term: &Term, depth: usize, is_collapsed: bool, in_script: bool) {
    if in_script && !should_collapse(term, depth, is_collapsed) {
        out.push('\n');
        print_term(out, term, depth + 1, is_collapsed);
        out.push('\n');
    } else {
        print_term(out, term, depth, is_collapsed);
    }
}

fn print_term(out: &mut String, term: &Term, depth: usize, is_collapsed: bool) {
    match term {
        Term::Atom(a) => {
            if !is_collapsed {
                write_indent(out, depth);
            }
            out.push_str(a);
        }
        Term::List(items) if items.is_empty() => {
            if !is_collapsed {
                write_indent(out, depth);
            }
            out.push_str("()");
        }
        Term::List(items) => print_list(out, items, depth, is_collapsed),
    }
}

fn print_list(out: &mut String, items: &[Term], depth: usize, is_collapsed: bool) {
    let head = match &items[0] {
        Term::Atom(s) => s.as_str(),
        _ => {
            if !is_collapsed {
                write_indent(out, depth);
            }
            out.push('(');
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    out.push(' ');
                }
                print_term(out, item, depth, true);
            }
            out.push(')');
            return;
        }
    };

    if matches!(head, "forall" | "exists") && items.len() >= 3 {
        print_quantifier(out, head, &items[1], &items[2], depth, is_collapsed);
        return;
    }

    let list = Term::List(items.to_vec());
    if should_collapse(&list, depth, is_collapsed) {
        if !is_collapsed {
            write_indent(out, depth);
        }
        out.push('(');
        out.push_str(head);
        for arg in &items[1..] {
            out.push(' ');
            print_term(out, arg, depth, true);
        }
        out.push(')');
    } else {
        write_indent(out, depth);
        out.push('(');
        out.push_str(head);
        out.push('\n');
        for arg in &items[1..] {
            print_term(out, arg, depth + 1, is_collapsed);
            out.push('\n');
        }
        write_indent(out, depth);
        out.push(')');
    }
}

fn print_quantifier(
    out: &mut String,
    op: &str,
    binders: &Term,
    body: &Term,
    depth: usize,
    is_collapsed: bool,
) {
    let sorted = sorted_quantifier_binders(binders);
    let binders_str: String = sorted
        .iter()
        .map(|b| b.to_string())
        .collect::<Vec<_>>()
        .join(" ");
    write_indent(out, depth);
    out.push('(');
    out.push_str(op);
    if binders_str.len() < 50 {
        out.push_str(" (");
        print_binder_group(out, &sorted, depth + 1, true);
        out.push_str(")\n");
    } else {
        out.push('\n');
        write_indent(out, depth + 1);
        out.push_str("(\n");
        for b in &sorted {
            write_indent(out, depth + 2);
            print_term(out, b, depth + 2, true);
            out.push('\n');
        }
        write_indent(out, depth + 1);
        out.push_str(")\n");
    }
    print_term(out, body, depth + 1, is_collapsed);
    out.push('\n');
    write_indent(out, depth);
    out.push(')');
}

fn sorted_quantifier_binders(binders: &Term) -> Vec<Term> {
    let mut items = match binders {
        Term::List(items) => items.clone(),
        other => return vec![other.clone()],
    };
    items.sort_by(|a, b| a.to_string().cmp(&b.to_string()));
    items
}

fn print_binder_group(out: &mut String, binders: &[Term], depth: usize, collapsed: bool) {
    for (i, b) in binders.iter().enumerate() {
        if i > 0 {
            out.push(' ');
        }
        print_term(out, b, depth, collapsed);
    }
}

fn write_indent(out: &mut String, depth: usize) {
    for _ in 0..depth {
        out.push_str(INDENT);
    }
}

fn term_size(term: &Term) -> usize {
    match term {
        Term::Atom(_) => 1,
        Term::List(items) if is_unary_int_negation(items) => 1,
        Term::List(items) => 1 + items[1..].iter().map(term_size).sum::<usize>(),
    }
}

fn is_unary_int_negation(items: &[Term]) -> bool {
    matches!(
        items,
        [Term::Atom(op), Term::Atom(n)]
            if op == "-" && is_int_literal(n)
    )
}

fn is_int_literal(atom: &str) -> bool {
    if atom.starts_with("#x") || atom.starts_with("#b") {
        return true;
    }
    atom.parse::<i128>().is_ok()
}

fn all_collapsible(args: &[Term]) -> bool {
    args.iter().all(|t| matches!(t, Term::Atom(_)))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn small_and_collapsed() {
        let t = Term::parse("(and a b)").unwrap();
        assert_eq!(pretty_print_term(&t), "(and a b)");
    }

    #[test]
    fn large_and_multiline() {
        let t = Term::parse("(and (= (+ x 1) 2) (= (+ y 3) 4) (= (+ z 5) 6))").unwrap();
        let s = pretty_print_term(&t);
        assert!(s.contains("(and\n"));
        assert!(s.contains("\n    (= "));
    }

    #[test]
    fn assert_in_script_wraps_large_formula() {
        let t = Term::parse("(and (= (+ x 1) 2) (= (+ y 3) 4) (= (+ z 5) 6))").unwrap();
        let s = pretty_print_term_in_script(&t);
        assert!(s.starts_with('\n'));
        assert!(s.ends_with('\n'));
    }

    #[test]
    fn pretty_assert_command() {
        let cmd = Command::new("(assert (and a b))");
        let out = pretty_print_command(&cmd).unwrap();
        assert_eq!(out.raw, "(assert (and a b))");
    }

    #[test]
    fn eq_mod_collapses_like_python() {
        let t = Term::parse(
            "(= (mod (- (* before-rs2_as_0@5 2013265920) (- 1)) 2013265921) 0)",
        )
        .unwrap();
        assert_eq!(term_size(&t), 9);
        assert_eq!(
            pretty_print_term(&t),
            "(= (mod (- (* before-rs2_as_0@5 2013265920) (- 1)) 2013265921) 0)"
        );
    }
}
