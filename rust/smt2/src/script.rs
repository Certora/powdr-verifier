//! Script representation, split/splice, and command helpers.

use std::collections::{BTreeMap, HashSet};

use z3::ast::Bool;

use crate::ast_util::{free_int_symbols, free_uf_function_symbols};
use crate::command::{declare_fun_name_cmd, parse_single_command, SmtCommand};
use crate::sexpr::SExpr;
use crate::z3_parse::ParseCtx;

const PREFIX_CMDS: &[&str] = &[
    "set-info",
    "set-logic",
    "set-option",
    "declare-fun",
    "get-model",
    "get-unsat-core",
    "echo",
];

#[derive(Clone, Debug, Default)]
pub struct Script {
    pub source: String,
    pub commands: Vec<SmtCommand>,
}

impl Script {
    pub fn from_commands(source: impl Into<String>, commands: Vec<SmtCommand>) -> Self {
        Self {
            source: source.into(),
            commands,
        }
    }

    pub fn parse(input: &str) -> Result<Self, String> {
        let spans = SExpr::read_command_spans(input)?;
        let mut ctx = ParseCtx::new();
        let mut commands = Vec::with_capacity(spans.len());
        for span in spans {
            let slice = &input[span.start..span.end];
            commands.push(SmtCommand::from_slice(span, slice, &mut ctx)?);
        }
        Ok(Self::from_commands(input, commands))
    }

    /// Split at the first `check-sat`, mirroring Python `simplify_z3` scan logic.
    pub fn split_at_check_sat(&self) -> Result<ScriptParts, String> {
        let mut prefix = Vec::new();
        let mut z3_feed = Vec::new();
        let mut check_sat: Option<SmtCommand> = None;
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
    pub prefix: Vec<SmtCommand>,
    pub z3_feed: Vec<SmtCommand>,
    pub check_sat: SmtCommand,
    pub suffix: Vec<SmtCommand>,
}

impl ScriptParts {
    /// Prefix `declare-fun` commands as SMT-LIB (for Z3 `from_string`).
    pub fn z3_declarations_string(&self, source: &str) -> String {
        let mut out = String::new();
        for cmd in &self.prefix {
            if cmd.name() == "declare-fun" {
                out.push_str(&cmd.to_smtlib(source));
                out.push('\n');
            }
        }
        out
    }

    pub fn asserts_in(&self) -> usize {
        self.z3_feed.iter().filter(|c| c.name() == "assert").count()
    }
}

/// Symbol names from `declare-fun` commands.
pub fn declared_symbol_names(commands: &[SmtCommand]) -> Vec<String> {
    commands
        .iter()
        .filter_map(declare_fun_name_cmd)
        .collect()
}

/// `declare-fun` in `processed` not already in `prefix_names`.
pub fn extra_declarations(
    processed: &[SmtCommand],
    prefix_names: &[String],
) -> Vec<SmtCommand> {
    let mut seen: HashSet<String> = prefix_names.to_vec().into_iter().collect();
    let mut out = Vec::new();
    for cmd in processed {
        if cmd.name() != "declare-fun" {
            continue;
        }
        if let Some(sym) = declare_fun_name_cmd(cmd) {
            if seen.insert(sym) {
                out.push(cmd.clone());
            }
        }
    }
    out
}

/// Assert commands whose body is not literal `true`.
pub fn asserts_excluding_true(processed: &[SmtCommand]) -> Vec<SmtCommand> {
    processed
        .iter()
        .filter(|c| {
            c.name() == "assert"
                && c.assert_bool()
                    .map(|b| b.as_bool() != Some(true))
                    .unwrap_or(true)
        })
        .cloned()
        .collect()
}

/// Assert commands in `script` (before `check-sat`).
pub fn assert_commands(script: &Script) -> Vec<&SmtCommand> {
    script
        .commands
        .iter()
        .take_while(|c| c.name() != "check-sat")
        .filter(|c| c.name() == "assert")
        .collect()
}

/// Ingest prefix commands into a Z3 parser context.
pub fn seed_parser_context(ctx: &mut ParseCtx, script: &Script) -> Result<(), String> {
    for cmd in &script.commands {
        if cmd.name() == "check-sat" {
            break;
        }
        if cmd.name() == "assert" {
            continue;
        }
        let raw = cmd.to_smtlib(&script.source);
        ctx.ingest_command(&raw)?;
    }
    Ok(())
}

pub fn ensure_free_symbols_declared(
    b: &Bool,
    ctx: &mut ParseCtx,
    declared: &mut HashSet<String>,
) -> Result<(), String> {
    for sym in free_int_symbols(b) {
        if !declared.insert(sym.clone()) {
            continue;
        }
        ctx.ingest_command(&format!("(declare-fun {sym} () Int)"))?;
    }
    for (sym, arity) in free_uf_function_symbols(b) {
        if !declared.insert(sym.clone()) {
            continue;
        }
        let args = (0..arity).map(|_| "Int").collect::<Vec<_>>().join(" ");
        ctx.ingest_command(&format!("(declare-fun {sym} ({args}) Int)"))?;
    }
    Ok(())
}

/// Insert ``declare-fun`` for symbols free in asserts but missing from the script prefix.
pub fn ensure_declarations_for_asserts(script: &Script) -> Result<Script, String> {
    let declared: HashSet<String> = declared_symbol_names(&script.commands).into_iter().collect();
    let mut missing_int = BTreeMap::<String, ()>::new();
    let mut missing_uf = BTreeMap::<String, usize>::new();
    for cmd in &script.commands {
        let Some(b) = cmd.assert_bool() else {
            continue;
        };
        for sym in free_int_symbols(b) {
            if !declared.contains(&sym) {
                missing_int.insert(sym, ());
            }
        }
        for (sym, arity) in free_uf_function_symbols(b) {
            if !declared.contains(&sym) {
                missing_uf.insert(sym, arity);
            }
        }
    }
    if missing_int.is_empty() && missing_uf.is_empty() {
        return Ok(script.clone());
    }
    let Some(first_assert) = script
        .commands
        .iter()
        .position(|c| c.name() == "assert")
    else {
        return Ok(script.clone());
    };

    let mut ctx = ParseCtx::new();
    seed_parser_context(&mut ctx, script)?;
    let mut decls = Vec::new();
    for sym in missing_int.keys() {
        decls.push(parse_single_command(
            &format!("(declare-fun {sym} () Int)"),
            &mut ctx,
        )?);
    }
    for (sym, arity) in &missing_uf {
        let args = (0..*arity).map(|_| "Int").collect::<Vec<_>>().join(" ");
        decls.push(parse_single_command(
            &format!("(declare-fun {sym} ({args}) Int)"),
            &mut ctx,
        )?);
    }

    let mut commands = Vec::with_capacity(script.commands.len() + decls.len());
    commands.extend_from_slice(&script.commands[..first_assert]);
    commands.extend(decls);
    commands.extend_from_slice(&script.commands[first_assert..]);
    Ok(Script::from_commands(&script.source, commands))
}

/// Transform each assert formula; other commands unchanged.
pub fn map_asserts(
    script: &Script,
    mut f: impl FnMut(&Bool) -> Result<Bool, String>,
) -> Result<Script, String> {
    map_asserts_opt(script, |b| {
        let new_b = f(b)?;
        Ok(if new_b.ast_eq(b) { None } else { Some(new_b) })
    })
}

/// Identity-preserving variant of [`map_asserts`].
///
/// ``f`` returns ``None`` for an unchanged assert, letting callers avoid cloning
/// (and re-declaring) when a pass leaves an assert untouched; the original
/// command is reused as-is.
pub fn map_asserts_opt(
    script: &Script,
    mut f: impl FnMut(&Bool) -> Result<Option<Bool>, String>,
) -> Result<Script, String> {
    let mut ctx = ParseCtx::new();
    seed_parser_context(&mut ctx, script)?;
    let mut declared: HashSet<String> = declared_symbol_names(&script.commands).into_iter().collect();

    let mut commands = Vec::with_capacity(script.commands.len());
    for cmd in &script.commands {
        match cmd {
            SmtCommand::Assert { bool: b, span, .. } => match f(b)? {
                Some(new_b) => {
                    ensure_free_symbols_declared(&new_b, &mut ctx, &mut declared)?;
                    commands.push(SmtCommand::Assert {
                        bool: new_b,
                        span: *span,
                        term_text: None,
                    });
                }
                None => commands.push(cmd.clone()),
            },
            _ => commands.push(cmd.clone()),
        }
    }
    Ok(Script::from_commands(&script.source, commands))
}

/// Reassemble after Z3 processing.
pub fn splice_z3_result(parts: &ScriptParts, processed: &[SmtCommand], source: &str) -> Script {
    let prefix_names = declared_symbol_names(&parts.prefix);
    let extra = extra_declarations(processed, &prefix_names);
    let new_asserts = asserts_excluding_true(processed);

    let mut commands = Vec::new();
    commands.extend(parts.prefix.iter().cloned());
    commands.extend(extra);
    commands.extend(new_asserts);
    commands.push(parts.check_sat.clone());
    commands.extend(parts.suffix.iter().cloned());
    Script::from_commands(source, commands)
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
        assert_eq!(declare_fun_name_cmd(&extra[0]).as_deref(), Some("mod!0"));
    }

    #[test]
    fn drops_assert_true() {
        let processed = Script::parse(
            "(declare-fun x () Int)\n(assert true)\n(assert (= x 1))\n",
        )
        .unwrap()
        .commands;
        let asserts = asserts_excluding_true(&processed);
        assert_eq!(asserts.len(), 1);
    }

    #[test]
    fn parse_assert_without_declare() {
        let script = Script::parse("(assert (= x@0 y))\n(check-sat)\n").unwrap();
        assert!(script.commands[0].assert_bool().is_some());
    }

    #[test]
    fn ensure_declarations_adds_uf_and() {
        let mut ctx = ParseCtx::new();
        ctx.ingest_command("(declare-fun uf_xor (Int Int) Int)")
            .unwrap();
        ctx.ingest_command("(declare-fun x () Int)").unwrap();
        ctx.ingest_command("(declare-fun y () Int)").unwrap();
        ctx.ingest_command("(declare-fun uf_and (Int Int) Int)")
            .unwrap();
        let b = crate::ast_build::parse_bool_formula(&mut ctx, "(= (uf_and x y) 0)").unwrap();
        let script = Script::from_commands(
            "",
            vec![
                parse_single_command("(declare-fun uf_xor (Int Int) Int)", &mut ParseCtx::new())
                    .unwrap(),
                parse_single_command("(declare-fun x () Int)", &mut ParseCtx::new()).unwrap(),
                parse_single_command("(declare-fun y () Int)", &mut ParseCtx::new()).unwrap(),
                SmtCommand::new_assert(b),
                SmtCommand::CheckSat,
            ],
        );
        let fixed = ensure_declarations_for_asserts(&script).unwrap();
        let s = crate::dump_string(&fixed);
        assert!(s.contains("(declare-fun uf_and (Int Int) Int)"));
        assert!(Script::parse(&s).is_ok());
    }
}
