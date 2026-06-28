//! S-expression term parse / constant-fold / print (evaluator pass).

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Term {
    Atom(String),
    List(Vec<Term>),
}

impl Term {
    pub fn parse(input: &str) -> Result<Self, String> {
        let tokens = tokenize(input)?;
        parse_term(&tokens, &mut 0)
    }

    pub fn to_string(&self) -> String {
        match self {
            Term::Atom(a) => a.clone(),
            Term::List(items) => {
                let mut out = String::from("(");
                for (i, t) in items.iter().enumerate() {
                    if i > 0 {
                        out.push(' ');
                    }
                    out.push_str(&t.to_string());
                }
                out.push(')');
                out
            }
        }
    }
}

pub fn fold_constants(term: &Term, field_mod: Option<u64>) -> Term {
    match term {
        Term::List(items) if !items.is_empty() => {
            let head = match &items[0] {
                Term::Atom(s) => s.as_str(),
                _ => return rebuild_list(items, field_mod),
            };
            let folded_args: Vec<Term> = items[1..]
                .iter()
                .map(|t| fold_constants(t, field_mod))
                .collect();
            if let Some(folded) = try_fold(head, &folded_args, field_mod) {
                return folded;
            }
            let mut out = vec![items[0].clone()];
            out.extend(folded_args);
            Term::List(out)
        }
        _ => term.clone(),
    }
}

pub fn fold_constants_fixpoint(term: &Term, field_mod: Option<u64>, max_iters: usize) -> Term {
    let mut cur = term.clone();
    for _ in 0..max_iters {
        let next = fold_constants(&cur, field_mod);
        if next == cur {
            break;
        }
        cur = next;
    }
    cur
}

fn rebuild_list(items: &[Term], field_mod: Option<u64>) -> Term {
    Term::List(
        items
            .iter()
            .map(|t| fold_constants(t, field_mod))
            .collect(),
    )
}

fn bool_not(arg: Term) -> Option<Term> {
    bool_arg(&arg).map(|b| bool_atom(!b))
}

fn try_fold(head: &str, args: &[Term], field_mod: Option<u64>) -> Option<Term> {
    match head {
        "not" if args.len() == 1 => bool_not(args[0].clone()),
        "and" => fold_nary_bool(args, "and", |vals| vals.iter().all(|&b| b)),
        "or" => fold_nary_bool(args, "or", |vals| vals.iter().any(|&b| b)),
        "=" if args.len() == 2 => fold_eq(args[0].clone(), args[1].clone()),
        "distinct" if args.len() == 2 => {
            fold_eq(args[0].clone(), args[1].clone()).map(|t| match t {
                Term::Atom(s) if s == "true" => atom("false"),
                Term::Atom(s) if s == "false" => atom("true"),
                other => other,
            })
        }
        "ite" if args.len() == 3 => fold_ite(&args[0], args[1].clone(), args[2].clone()),
        "+" => fold_nary_int_mixed("+", args, |vals| vals.iter().sum(), field_mod),
        "-" if args.len() == 1 => int_arg(&args[0]).map(|v| int_atom(-v, field_mod)),
        "-" if args.len() == 2 => {
            let a = int_arg(&args[0])?;
            let b = int_arg(&args[1])?;
            Some(int_atom(a - b, field_mod))
        }
        "*" => fold_nary_int_mixed("*", args, |vals| vals.iter().product(), field_mod),
        "div" if args.len() == 2 => {
            let a = int_arg(&args[0])?;
            let b = int_arg(&args[1])?;
            if b == 0 {
                return None;
            }
            Some(int_atom(a / b, field_mod))
        }
        "mod" if args.len() == 2 => {
            let a = int_arg(&args[0])?;
            let b = int_arg(&args[1])?;
            if b == 0 {
                return None;
            }
            Some(int_atom(a % b, field_mod))
        }
        _ => None,
    }
}

fn fold_nary_bool<F>(args: &[Term], op: &str, f: F) -> Option<Term>
where
    F: Fn(&[bool]) -> bool,
{
    if args.is_empty() {
        return None;
    }
    let mut consts = Vec::new();
    let mut symbolic = Vec::new();
    for a in args {
        if let Some(b) = bool_arg(a) {
            consts.push(b);
        } else {
            symbolic.push(a.clone());
        }
    }
    if consts.is_empty() {
        return None;
    }
    let folded = f(&consts);
    if op == "and" && !folded {
        return Some(atom("false"));
    }
    if op == "or" && folded {
        return Some(atom("true"));
    }
    if symbolic.is_empty() {
        return Some(bool_atom(folded));
    }
    let mut out = vec![Term::Atom(op.to_string())];
    if op == "and" && folded {
        out.extend(symbolic);
    } else if op == "or" && !folded {
        out.extend(symbolic);
    } else {
        out.push(bool_atom(folded));
        out.extend(symbolic);
    }
    Some(Term::List(out))
}

fn fold_nary_int_mixed<F>(
    op: &str,
    args: &[Term],
    f: F,
    field_mod: Option<u64>,
) -> Option<Term>
where
    F: Fn(&[i128]) -> i128,
{
    if args.is_empty() {
        return None;
    }
    let mut int_acc: Vec<i128> = Vec::new();
    let mut symbolic = Vec::new();
    for a in args {
        if let Some(v) = int_arg(a) {
            int_acc.push(v);
        } else {
            symbolic.push(a.clone());
        }
    }
    if int_acc.is_empty() {
        return None;
    }
    let folded = int_atom(f(&int_acc), field_mod);
    if symbolic.is_empty() {
        return Some(folded);
    }
    let mut out = vec![Term::Atom(op.to_string())];
    out.extend(symbolic);
    if folded != int_atom(if op == "*" { 1 } else { 0 }, field_mod) {
        out.push(folded);
    }
    if out.len() == 2 {
        return Some(out[1].clone());
    }
    Some(Term::List(out))
}


fn fold_eq(a: Term, b: Term) -> Option<Term> {
    if let (Some(x), Some(y)) = (bool_arg(&a), bool_arg(&b)) {
        return Some(bool_atom(x == y));
    }
    if let (Some(x), Some(y)) = (int_arg(&a), int_arg(&b)) {
        return Some(bool_atom(x == y));
    }
    None
}

fn fold_ite(cond: &Term, then_b: Term, else_b: Term) -> Option<Term> {
    let c = bool_arg(cond)?;
    Some(if c { then_b } else { else_b })
}

fn bool_arg(t: &Term) -> Option<bool> {
    match t {
        Term::Atom(s) => match s.as_str() {
            "true" => Some(true),
            "false" => Some(false),
            _ => None,
        },
        _ => None,
    }
}

fn int_arg(t: &Term) -> Option<i128> {
    match t {
        Term::Atom(s) => parse_int_literal(s),
        _ => None,
    }
}

pub fn parse_int_literal(s: &str) -> Option<i128> {
    if let Some(hex) = s.strip_prefix("#x") {
        return u128::from_str_radix(hex, 16).ok().map(|v| v as i128);
    }
    if let Some(bin) = s.strip_prefix("#b") {
        return u128::from_str_radix(bin, 2).ok().map(|v| v as i128);
    }
    s.parse::<i128>().ok()
}

/// True for SMT-LIB integer literals (including values outside ``i128``).
pub fn is_int_literal_string(s: &str) -> bool {
    if s.starts_with("#x") || s.starts_with("#b") {
        return s.len() > 2;
    }
    let digits = s.strip_prefix('-').unwrap_or(s);
    !digits.is_empty() && digits.chars().all(|c| c.is_ascii_digit())
}

fn normalized_mod(v: i128, m: i128) -> i128 {
    ((v % m) + m) % m
}

/// Reduce an integer literal modulo ``m`` (decimal literals may exceed ``i128``).
pub fn mod_int_literal_string(s: &str, modulus: i128) -> Option<String> {
    if modulus <= 0 {
        return None;
    }
    if let Some(v) = parse_int_literal(s) {
        return Some(normalized_mod(v, modulus).to_string());
    }
    if !is_int_literal_string(s) {
        return None;
    }
    let neg = s.starts_with('-');
    let digits = s.strip_prefix('-').unwrap_or(s);
    let mut rem: i128 = 0;
    for d in digits.as_bytes() {
        if !d.is_ascii_digit() {
            return None;
        }
        rem = (rem * 10 + i128::from(*d - b'0')) % modulus;
    }
    if neg {
        rem = normalized_mod(-rem, modulus);
    } else {
        rem = normalized_mod(rem, modulus);
    }
    Some(rem.to_string())
}

fn atom(s: &str) -> Term {
    Term::Atom(s.to_string())
}

fn bool_atom(v: bool) -> Term {
    atom(if v { "true" } else { "false" })
}

fn int_atom(v: i128, field_mod: Option<u64>) -> Term {
    let v = match field_mod {
        Some(m) if m > 0 => {
            let m = m as i128;
            ((v % m) + m) % m
        }
        _ => v,
    };
    Term::Atom(v.to_string())
}

fn tokenize(input: &str) -> Result<Vec<String>, String> {
    let mut tokens = Vec::new();
    let bytes = input.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        while i < bytes.len() && bytes[i].is_ascii_whitespace() {
            i += 1;
        }
        if i >= bytes.len() {
            break;
        }
        match bytes[i] {
            b'(' => {
                tokens.push("(".to_string());
                i += 1;
            }
            b')' => {
                tokens.push(")".to_string());
                i += 1;
            }
            b'"' => {
                let start = i;
                i += 1;
                while i < bytes.len() {
                    if bytes[i] == b'"' {
                        i += 1;
                        break;
                    }
                    if bytes[i] == b'\\' && i + 1 < bytes.len() {
                        i += 2;
                    } else {
                        i += 1;
                    }
                }
                tokens.push(String::from_utf8_lossy(&bytes[start..i]).to_string());
            }
            b';' => {
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
            }
            b'|' => {
                i += 1;
                let start = i;
                while i < bytes.len() && bytes[i] != b'|' {
                    i += 1;
                }
                let sym = String::from_utf8_lossy(&bytes[start..i]).to_string();
                if i < bytes.len() {
                    i += 1;
                }
                tokens.push(format!("|{sym}|"));
            }
            _ => {
                let start = i;
                while i < bytes.len()
                    && !bytes[i].is_ascii_whitespace()
                    && !matches!(bytes[i], b'(' | b')' | b'"' | b';' | b'|')
                {
                    i += 1;
                }
                tokens.push(String::from_utf8_lossy(&bytes[start..i]).to_string());
            }
        }
    }
    Ok(tokens)
}

fn parse_term(tokens: &[String], pos: &mut usize) -> Result<Term, String> {
    if *pos >= tokens.len() {
        return Err("unexpected end of input".into());
    }
    match tokens[*pos].as_str() {
        "(" => {
            *pos += 1;
            let mut items = Vec::new();
            while *pos < tokens.len() && tokens[*pos] != ")" {
                items.push(parse_term(tokens, pos)?);
            }
            if *pos >= tokens.len() || tokens[*pos] != ")" {
                return Err("unbalanced parentheses".into());
            }
            *pos += 1;
            Ok(Term::List(items))
        }
        ")" => Err("unexpected ')'".into()),
        atom => {
            *pos += 1;
            Ok(Term::Atom(atom.to_string()))
        }
    }
}

pub fn assert_body(raw: &str) -> Option<String> {
    let inner = raw.trim().strip_prefix('(')?.trim();
    let rest = inner.strip_prefix("assert")?.trim();
    if rest.is_empty() {
        return None;
    }
    if rest.starts_with('(') {
        return Some(rest.to_string());
    }
    Some(rest.strip_suffix(')').unwrap_or(rest).trim().to_string())
}

pub fn replace_assert_body(raw: &str, new_body: &str) -> String {
    let trimmed = raw.trim();
    if let Some(inner) = trimmed.strip_prefix('(').and_then(|s| s.strip_suffix(')')) {
        let inner = inner.trim();
        if let Some(after) = inner.strip_prefix("assert") {
            let _ = after;
            return format!("(assert {new_body})");
        }
    }
    format!("(assert {new_body})")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn folds_add() {
        let t = Term::parse("(+ 1 2 3)").unwrap();
        let f = fold_constants(&t, None);
        assert_eq!(f, Term::Atom("6".to_string()));
    }

    #[test]
    fn folds_not_zero_eq() {
        let t = Term::parse("(not (= 0 0))").unwrap();
        let f = fold_constants(&t, None);
        assert_eq!(f, Term::Atom("false".to_string()));
    }

    #[test]
    fn preserves_symbolic() {
        let t = Term::parse("(+ x 1 2)").unwrap();
        let f = fold_constants(&t, None);
        assert_eq!(f.to_string(), "(+ x 3)");
    }

    #[test]
    fn mod_int_literal_string_reduces_beyond_i128() {
        let p = 2_013_265_921_i128;
        let huge = "32561662554329978067493305279605223446198353920";
        let reduced = mod_int_literal_string(huge, p).unwrap();
        assert_eq!(reduced, "1069547521");
    }

}
