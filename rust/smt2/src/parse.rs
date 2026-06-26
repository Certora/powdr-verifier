//! Balanced-paren scan of top-level SMT-LIB forms.

use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Command {
    pub raw: String,
}

impl Command {
    pub fn new(raw: impl Into<String>) -> Self {
        Self { raw: raw.into() }
    }

    pub fn name(&self) -> &str {
        command_name(&self.raw)
    }
}

impl fmt::Display for Command {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.raw)
    }
}

/// Extract the first token (command name) from an SMT-LIB form.
pub fn command_name(raw: &str) -> &str {
    let s = raw.trim();
    if !s.starts_with('(') {
        return "";
    }
    let inner = s[1..].trim_start();
    let end = inner
        .find(|c: char| c.is_whitespace() || c == ')')
        .unwrap_or(inner.len());
    &inner[..end]
}

/// Split `input` into top-level parenthesized commands, skipping comments and blanks.
pub fn parse_commands(input: &str) -> Result<Vec<Command>, String> {
    let mut commands = Vec::new();
    let bytes = input.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        while i < bytes.len() && bytes[i].is_ascii_whitespace() {
            i += 1;
        }
        if i >= bytes.len() {
            break;
        }
        if bytes[i] == b';' {
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
            continue;
        }
        if bytes[i] != b'(' {
            return Err(format!("expected '(' at byte {i}"));
        }
        let start = i;
        let mut depth = 0;
        let mut in_string = false;
        while i < bytes.len() {
            let c = bytes[i];
            if in_string {
                if c == b'"' {
                    in_string = false;
                } else if c == b'\\' && i + 1 < bytes.len() {
                    i += 1;
                }
            } else if c == b'"' {
                in_string = true;
            } else if c == b'(' {
                depth += 1;
            } else if c == b')' {
                depth -= 1;
                if depth == 0 {
                    i += 1;
                    break;
                }
            }
            i += 1;
        }
        if depth != 0 {
            return Err("unbalanced parentheses".into());
        }
        let raw = input[start..i].trim().to_string();
        if !raw.is_empty() {
            commands.push(Command::new(raw));
        }
    }
    Ok(commands)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_multiple_commands() {
        let cmds = parse_commands(
            "(declare-fun x () Int)\n; comment\n(assert (= x 0))\n(check-sat)\n",
        )
        .unwrap();
        assert_eq!(cmds.len(), 3);
        assert_eq!(cmds[0].name(), "declare-fun");
        assert_eq!(cmds[1].name(), "assert");
        assert_eq!(cmds[2].name(), "check-sat");
    }

    #[test]
    fn handles_strings_with_parens() {
        let cmds = parse_commands(r#"(set-info :source "| (not a form) |")"#).unwrap();
        assert_eq!(cmds.len(), 1);
        assert_eq!(cmds[0].name(), "set-info");
    }
}
