//! Assert transforms on Z3 `Bool` AST.

use std::collections::HashSet;

use smt2::{
    ast_util::free_int_symbols, declare_fun_name_cmd, declared_symbol_names, map_asserts,
    parse_single_command, ParseCtx, Script, SmtCommand,
};
use z3::ast::Bool;

pub struct AssertBuildCtx {
    parse: ParseCtx,
    declared: HashSet<String>,
}

impl AssertBuildCtx {
    pub fn from_script(script: &Script) -> Result<Self, String> {
        let mut parse = ParseCtx::new();
        seed_parser_context(&mut parse, script)?;
        Ok(Self {
            parse,
            declared: declared_names(script),
        })
    }

    pub fn push_assert(&mut self, commands: &mut Vec<SmtCommand>, b: &Bool) -> Result<(), String> {
        ensure_free_symbols_declared(b, &mut self.parse, &mut self.declared)?;
        commands.push(SmtCommand::new_assert(b.clone()));
        Ok(())
    }

    pub fn push_raw(&mut self, commands: &mut Vec<SmtCommand>, raw: &str) -> Result<(), String> {
        if let Some(name) = parse_declare_fun_name(raw) {
            if self.declared.contains(&name) {
                return Ok(());
            }
        }
        let cmd = parse_single_command(raw, &mut self.parse)?;
        if let Some(name) = declare_fun_name_cmd(&cmd) {
            self.declared.insert(name);
        }
        commands.push(cmd);
        Ok(())
    }

    pub fn ensure_declare_fun(&mut self, raw: &str) -> Result<(), String> {
        if let Some(name) = parse_declare_fun_name(raw) {
            if self.declared.contains(&name) {
                return Ok(());
            }
        }
        let cmd = parse_single_command(raw, &mut self.parse)?;
        if let Some(name) = declare_fun_name_cmd(&cmd) {
            self.declared.insert(name);
        }
        Ok(())
    }
}

fn parse_declare_fun_name(raw: &str) -> Option<String> {
    let inner = raw.trim().strip_prefix('(')?.trim();
    let rest = inner.strip_prefix("declare-fun")?.trim();
    let end = rest.find(|c: char| c.is_whitespace())?;
    Some(rest[..end].to_string())
}

pub fn map_asserts_with_decl(
    script: &Script,
    mut f: impl FnMut(&Bool) -> Result<Bool, String>,
) -> Result<Script, String> {
    let mut parse = ParseCtx::new();
    seed_parser_context(&mut parse, script)?;
    let mut declared = declared_names(script);
    map_asserts(script, |b| {
        let new_b = f(b)?;
        ensure_free_symbols_declared(&new_b, &mut parse, &mut declared)?;
        Ok(new_b)
    })
}

pub fn seed_parser_context(ctx: &mut ParseCtx, script: &Script) -> Result<(), String> {
    smt2::seed_parser_context(ctx, script)
}

pub fn declared_names(script: &Script) -> HashSet<String> {
    declared_symbol_names(
        &script
            .commands
            .iter()
            .filter(|c| c.name() == "declare-fun")
            .cloned()
            .collect::<Vec<_>>(),
    )
    .into_iter()
    .collect()
}

pub(crate) fn ensure_free_symbols_declared(
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
    Ok(())
}

pub fn is_true(b: &Bool) -> bool {
    b.as_bool() == Some(true)
}

pub fn push_assert_bool(
    commands: &mut Vec<SmtCommand>,
    b: Bool,
    ctx: &mut ParseCtx,
    declared: &mut HashSet<String>,
) -> Result<(), String> {
    ensure_free_symbols_declared(&b, ctx, declared)?;
    commands.push(SmtCommand::new_assert(b));
    Ok(())
}

pub fn push_command_raw(
    commands: &mut Vec<SmtCommand>,
    raw: &str,
    ctx: &mut ParseCtx,
    declared: &mut HashSet<String>,
) -> Result<(), String> {
    let cmd = parse_single_command(raw, ctx)?;
    if let Some(name) = declare_fun_name_cmd(&cmd) {
        declared.insert(name);
    }
    commands.push(cmd);
    Ok(())
}

pub fn rebuild_script(source: &str, commands: Vec<SmtCommand>) -> Script {
    Script::from_commands(source, commands)
}
