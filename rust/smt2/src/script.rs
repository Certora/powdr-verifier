//! Script representation, split/splice, and command helpers.

use crate::parse::{parse_commands, Command};

const PREFIX_CMDS: &[&str] = &[
    "set-info",
    "set-logic",
    "set-option",
    "declare-fun",
    "get-model",
    "get-unsat-core",
    "echo",
];

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Script {
    pub commands: Vec<Command>,
}

impl Script {
    pub fn from_commands(commands: Vec<Command>) -> Self {
        Self { commands }
    }

    pub fn parse(input: &str) -> Result<Self, String> {
        Ok(Self::from_commands(parse_commands(input)?))
    }

    /// Split at the first `check-sat`, mirroring Python `simplify_z3` scan logic.
    pub fn split_at_check_sat(&self) -> Result<ScriptParts, String> {
        let mut prefix = Vec::new();
        let mut z3_feed = Vec::new();
        let mut check_sat: Option<Command> = None;
        let mut suffix = Vec::new();
        let mut phase = Phase::BeforeCheckSat;

        for cmd in &self.commands {
            match phase {
                Phase::BeforeCheckSat => match cmd.name() {
                    "check-sat" => {
                        check_sat = Some(cmd.clone());
                        phase = Phase::Suffix;
                    }
                    "assert" => z3_feed.push(cmd.clone()),
                    name if PREFIX_CMDS.contains(&name) => prefix.push(cmd.clone()),
                    _ => {
                        return Err(format!("unexpected command before check-sat: {}", cmd.name()));
                    }
                },
                Phase::Suffix => suffix.push(cmd.clone()),
            }
        }

        let check_sat = check_sat.ok_or("missing check-sat")?;
        Ok(ScriptParts {
            prefix,
            z3_feed,
            check_sat,
            suffix,
        })
    }
}

#[derive(Clone, Debug)]
enum Phase {
    BeforeCheckSat,
    Suffix,
}

#[derive(Clone, Debug)]
pub struct ScriptParts {
    pub prefix: Vec<Command>,
    pub z3_feed: Vec<Command>,
    pub check_sat: Command,
    pub suffix: Vec<Command>,
}

impl ScriptParts {
    /// Build the SMT-LIB fragment fed to Z3: prefix `declare-fun` + all `assert`s.
    pub fn z3_input_string(&self) -> String {
        let mut out = String::new();
        for cmd in &self.prefix {
            if cmd.name() == "declare-fun" {
                out.push_str(&cmd.raw);
                out.push('\n');
            }
        }
        for cmd in &self.z3_feed {
            out.push_str(&cmd.raw);
            out.push('\n');
        }
        out
    }

    pub fn asserts_in(&self) -> usize {
        self.z3_feed.iter().filter(|c| c.name() == "assert").count()
    }
}

/// Symbol names from `declare-fun` commands.
pub fn declared_symbol_names(commands: &[Command]) -> Vec<String> {
    commands
        .iter()
        .filter(|c| c.name() == "declare-fun")
        .filter_map(|c| declare_fun_symbol(&c.raw))
        .collect()
}

fn declare_fun_symbol(raw: &str) -> Option<String> {
    let inner = raw.trim().strip_prefix('(')?.trim();
    let rest = inner.strip_prefix("declare-fun")?.trim();
    let end = rest.find(|c: char| c.is_whitespace())?;
    Some(rest[..end].to_string())
}

/// `declare-fun` in `processed` not already in `prefix_names`.
pub fn extra_declarations(processed: &[Command], prefix_names: &[String]) -> Vec<Command> {
    let mut seen: std::collections::HashSet<String> = prefix_names.to_vec().into_iter().collect();
    let mut out = Vec::new();
    for cmd in processed {
        if cmd.name() != "declare-fun" {
            continue;
        }
        if let Some(sym) = declare_fun_symbol(&cmd.raw) {
            if seen.insert(sym) {
                out.push(cmd.clone());
            }
        }
    }
    out
}

/// Assert commands whose body is not literal `true`.
pub fn asserts_excluding_true(processed: &[Command]) -> Vec<Command> {
    processed
        .iter()
        .filter(|c| c.name() == "assert" && !is_assert_true(&c.raw))
        .cloned()
        .collect()
}

fn is_assert_true(raw: &str) -> bool {
    let inner = raw.trim().strip_prefix('(').unwrap_or(raw).trim();
    let rest = inner.strip_prefix("assert").unwrap_or("").trim();
    let body = rest.strip_suffix(')').unwrap_or(rest).trim();
    body == "true" || body == "(true)"
}

/// Reassemble after Z3 processing.
pub fn splice_z3_result(
    parts: &ScriptParts,
    processed: &[Command],
) -> Script {
    let prefix_names = declared_symbol_names(&parts.prefix);
    let extra = extra_declarations(processed, &prefix_names);
    let new_asserts = asserts_excluding_true(processed);

    let mut commands = Vec::new();
    commands.extend(parts.prefix.iter().cloned());
    commands.extend(extra);
    commands.extend(new_asserts);
    commands.push(parts.check_sat.clone());
    commands.extend(parts.suffix.iter().cloned());
    Script::from_commands(commands)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn split_at_check_sat() {
        let script = Script::parse(
            "(declare-fun x () Int)\n(assert (= x 1))\n(check-sat)\n(get-model)\n",
        )
        .unwrap();
        let parts = script.split_at_check_sat().unwrap();
        assert_eq!(parts.prefix.len(), 1);
        assert_eq!(parts.z3_feed.len(), 1);
        assert_eq!(parts.suffix.len(), 1);
        assert_eq!(parts.suffix[0].name(), "get-model");
    }

    #[test]
    fn extra_declarations_skips_known() {
        let processed = Script::parse(
            "(declare-fun x () Int)\n(declare-fun mod!0 () Int)\n(assert (= mod!0 0))\n",
        )
        .unwrap()
        .commands;
        let extra = extra_declarations(&processed, &["x".to_string()]);
        assert_eq!(extra.len(), 1);
        assert_eq!(declare_fun_symbol(&extra[0].raw).as_deref(), Some("mod!0"));
    }

    #[test]
    fn drops_assert_true() {
        let processed = Script::parse("(assert true)\n(assert (= x 1))\n").unwrap().commands;
        let asserts = asserts_excluding_true(&processed);
        assert_eq!(asserts.len(), 1);
    }
}
