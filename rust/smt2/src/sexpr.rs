//! S-expression parse / print with source spans.

use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Spanned<T> {
    pub node: T,
    pub span: Span,
}

impl<T> Spanned<T> {
    pub fn new(node: T, span: Span) -> Self {
        Self { node, span }
    }

    pub fn text<'a>(&self, input: &'a str) -> &'a str {
        &input[self.span.start..self.span.end]
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SExpr {
    Atom(String),
    List(Vec<Spanned<SExpr>>),
}

impl SExpr {
    /// Parse one top-level form from `input`; return the tree and unconsumed suffix.
    pub fn read_form(input: &str) -> Result<(Spanned<SExpr>, &str), String> {
        let (start, pos) = skip_ws_comments(input, 0)?;
        if pos >= input.len() {
            return Err("unexpected end of input".into());
        }
        let (node, end) = parse_form(input, pos)?;
        let rest = &input[end..];
        Ok((Spanned::new(node, Span { start, end }), rest))
    }

    /// Parse all top-level forms from `input`.
    pub fn read_all(input: &str) -> Result<Vec<Spanned<SExpr>>, String> {
        let mut forms = Vec::new();
        let mut rest = input;
        let mut base = 0usize;
        loop {
            let (_, pos) = skip_ws_comments(rest, 0)?;
            if pos >= rest.len() {
                break;
            }
            let (form, remaining) = Self::read_form(rest)?;
            let abs_start = base + form.span.start;
            let abs_end = base + form.span.end;
            forms.push(Spanned::new(form.node, Span { start: abs_start, end: abs_end }));
            let consumed = rest.len() - remaining.len();
            base += consumed;
            rest = remaining;
        }
        Ok(forms)
    }

    pub fn head(&self) -> Option<&str> {
        match self {
            SExpr::Atom(s) => Some(s.as_str()),
            SExpr::List(items) => items.first().and_then(|i| i.node.head()),
        }
    }

    pub fn args(&self) -> Option<&[Spanned<SExpr>]> {
        match self {
            SExpr::List(items) if !items.is_empty() => Some(&items[1..]),
            _ => None,
        }
    }

    pub fn as_atom(&self) -> Option<&str> {
        match self {
            SExpr::Atom(s) => Some(s.as_str()),
            _ => None,
        }
    }

    /// Drop ``(! inner attr…)`` wrappers recursively.
    pub fn strip_annotations(self) -> SExpr {
        match self {
            SExpr::List(items)
                if items
                    .first()
                    .and_then(|h| h.node.as_atom())
                    .is_some_and(|a| a == "!")
                    && items.len() >= 2 =>
            {
                items[1].node.clone().strip_annotations()
            }
            SExpr::List(items) => SExpr::List(
                items
                    .into_iter()
                    .map(|sp| Spanned::new(sp.node.strip_annotations(), sp.span))
                    .collect(),
            ),
            SExpr::Atom(a) => SExpr::Atom(a),
        }
    }

    pub fn to_string(&self) -> String {
        match self {
            SExpr::Atom(a) => a.clone(),
            SExpr::List(items) => {
                let mut out = String::from("(");
                for (i, t) in items.iter().enumerate() {
                    if i > 0 {
                        out.push(' ');
                    }
                    out.push_str(&t.node.to_string());
                }
                out.push(')');
                out
            }
        }
    }
}

/// Remove SMT-LIB annotation wrappers from a single expression string.
pub fn strip_smtlib_annotations(expr: &str) -> String {
    if !expr.contains("(!") {
        return expr.to_string();
    }
    let Ok((form, rest)) = SExpr::read_form(expr) else {
        return expr.to_string();
    };
    if !rest.trim().is_empty() {
        return expr.to_string();
    }
    form.node.strip_annotations().to_string()
}

impl fmt::Display for SExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.to_string())
    }
}

fn skip_ws_comments(input: &str, mut pos: usize) -> Result<(usize, usize), String> {
    let bytes = input.as_bytes();
    loop {
        while pos < bytes.len() && bytes[pos].is_ascii_whitespace() {
            pos += 1;
        }
        if pos < bytes.len() && bytes[pos] == b';' {
            while pos < bytes.len() && bytes[pos] != b'\n' {
                pos += 1;
            }
            continue;
        }
        return Ok((pos, pos));
    }
}

fn parse_form(input: &str, start: usize) -> Result<(SExpr, usize), String> {
    let bytes = input.as_bytes();
    if start >= bytes.len() {
        return Err("unexpected end of input".into());
    }
    if bytes[start] == b'(' {
        let mut items = Vec::new();
        let mut pos = start + 1;
        loop {
            let (_, p) = skip_ws_comments(input, pos)?;
            pos = p;
            if pos >= bytes.len() {
                return Err("unbalanced parentheses".into());
            }
            if bytes[pos] == b')' {
                pos += 1;
                break;
            }
            let item_start = pos;
            let (node, item_end) = parse_form(input, pos)?;
            items.push(Spanned::new(node, Span { start: item_start, end: item_end }));
            pos = item_end;
        }
        Ok((SExpr::List(items), pos))
    } else {
        let atom_start = start;
        let atom_end = scan_atom_end(input, start)?;
        let atom = input[atom_start..atom_end].to_string();
        Ok((SExpr::Atom(atom), atom_end))
    }
}

fn scan_atom_end(input: &str, start: usize) -> Result<usize, String> {
    let bytes = input.as_bytes();
    let mut pos = start;
    if pos >= bytes.len() {
        return Err("unexpected end of input".into());
    }
    if bytes[pos] == b'"' {
        pos += 1;
        while pos < bytes.len() {
            if bytes[pos] == b'"' {
                return Ok(pos + 1);
            }
            if bytes[pos] == b'\\' && pos + 1 < bytes.len() {
                pos += 2;
            } else {
                pos += 1;
            }
        }
        return Err("unterminated string".into());
    }
    if bytes[pos] == b'|' {
        pos += 1;
        while pos < bytes.len() && bytes[pos] != b'|' {
            pos += 1;
        }
        if pos >= bytes.len() {
            return Err("unterminated symbol".into());
        }
        return Ok(pos + 1);
    }
    while pos < bytes.len()
        && !bytes[pos].is_ascii_whitespace()
        && !matches!(bytes[pos], b'(' | b')' | b'"' | b';')
    {
        pos += 1;
    }
    if pos == start {
        return Err(format!("expected atom at byte {start}"));
    }
    Ok(pos)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_multiple_forms() {
        let forms = SExpr::read_all(
            "(declare-fun x () Int)\n; comment\n(assert (= x 0))\n(check-sat)\n",
        )
        .unwrap();
        assert_eq!(forms.len(), 3);
        assert_eq!(forms[0].node.head(), Some("declare-fun"));
        assert_eq!(forms[1].node.head(), Some("assert"));
        assert_eq!(forms[2].node.head(), Some("check-sat"));
    }

    #[test]
    fn preserves_span_text() {
        let input = "(assert (= x 0))";
        let (form, rest) = SExpr::read_form(input).unwrap();
        assert_eq!(form.text(input), input);
        assert!(rest.is_empty());
    }

    #[test]
    fn strips_bang_annotation() {
        let stripped = strip_smtlib_annotations("(! (or a b) :weight 0)");
        assert_eq!(stripped, "(or a b)");
    }
}
