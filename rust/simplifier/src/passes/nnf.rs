//! NNF conversion (Python ``NNFConverter`` parity; preserves ``=`` / iff).

use smt2::{map_asserts, Script, Term};

pub fn apply(script: &Script) -> Result<(Script, serde_json::Value), String> {
    let total = smt2::assert_commands(script).len();
    let mut changed = 0usize;
    let out = map_asserts(script, |body| {
        let term = Term::parse(body)?;
        let nnf = convert_to_nnf(&term);
        let new_body = nnf.to_string();
        if new_body != body {
            changed += 1;
        }
        Ok(new_body)
    })?;
    let stats = serde_json::json!({
        "asserts": total,
        "asserts_changed": changed,
    });
    Ok((out, stats))
}

fn convert_to_nnf(term: &Term) -> Term {
    match term {
        Term::Atom(_) => term.clone(),
        Term::List(items) if items.is_empty() => term.clone(),
        Term::List(items) => {
            let head = match &items[0] {
                Term::Atom(s) => s.as_str(),
                _ => return rebuild_with_children(items, convert_to_nnf),
            };
            let args: Vec<Term> = items[1..].iter().map(convert_to_nnf).collect();
            match head {
                "and" => flatten_and(args),
                "or" => flatten_or(args),
                "not" if args.len() == 1 => negate(&args[0]),
                "=>" if args.len() == 2 => flatten_or(vec![negate(&args[0]), args[1].clone()]),
                _ => {
                    let mut out = vec![items[0].clone()];
                    out.extend(args);
                    Term::List(out)
                }
            }
        }
    }
}

fn rebuild_with_children(items: &[Term], f: impl FnMut(&Term) -> Term) -> Term {
    Term::List(items.iter().map(f).collect())
}

fn flatten_and(args: Vec<Term>) -> Term {
    let mut flat = Vec::new();
    for a in args {
        if let Term::List(items) = &a {
            if matches!(items.first(), Some(Term::Atom(s)) if s == "and") {
                flat.extend(items[1..].iter().cloned());
                continue;
            }
        }
        flat.push(a);
    }
    match flat.len() {
        0 => atom("true"),
        1 => flat.into_iter().next().unwrap(),
        _ => Term::List(std::iter::once(atom("and")).chain(flat).collect()),
    }
}

fn flatten_or(args: Vec<Term>) -> Term {
    let mut flat = Vec::new();
    for a in args {
        if let Term::List(items) = &a {
            if matches!(items.first(), Some(Term::Atom(s)) if s == "or") {
                flat.extend(items[1..].iter().cloned());
                continue;
            }
        }
        flat.push(a);
    }
    match flat.len() {
        0 => atom("false"),
        1 => flat.into_iter().next().unwrap(),
        _ => Term::List(std::iter::once(atom("or")).chain(flat).collect()),
    }
}

fn negate(term: &Term) -> Term {
    if let Term::List(items) = term {
        if let Some(Term::Atom(head)) = items.first() {
            match head.as_str() {
                "not" if items.len() == 2 => return items[1].clone(),
                "ite" => {
                    return Term::List(vec![atom("not"), term.clone()]);
                }
                "and" => {
                    let args: Vec<Term> = items[1..].iter().map(negate).collect();
                    return flatten_or(args);
                }
                "or" => {
                    let args: Vec<Term> = items[1..].iter().map(negate).collect();
                    return flatten_and(args);
                }
                _ => {}
            }
        }
    }
    Term::List(vec![atom("not"), term.clone()])
}

fn atom(s: &str) -> Term {
    Term::Atom(s.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn implies() {
        let t = Term::parse("(=> a b)").unwrap();
        assert_eq!(convert_to_nnf(&t).to_string(), "(or (not a) b)");
    }

    #[test]
    fn demorgan() {
        let t = Term::parse("(not (and a b))").unwrap();
        assert_eq!(convert_to_nnf(&t).to_string(), "(or (not a) (not b))");
    }

    #[test]
    fn preserves_iff() {
        let t = Term::parse("(= a b)").unwrap();
        assert_eq!(convert_to_nnf(&t).to_string(), "(= a b)");
    }

    #[test]
    fn preserves_negated_ite() {
        let t = Term::parse("(not (ite c a b))").unwrap();
        assert_eq!(convert_to_nnf(&t).to_string(), "(not (ite c a b))");
    }
}
