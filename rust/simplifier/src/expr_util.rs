//! Assert transforms on Z3 `Bool` AST.

use std::collections::HashSet;

use smt2::{
    declare_fun_symbol_id, declared_symbol_ids,
    ensure_free_symbols_declared, map_asserts, parse_single_command, seed_parser_context,
    symbol_id_from_name, ParseCtx, Script, SmtCommand, SymbolId,
};
use z3::ast::Bool;

pub struct AssertBuildCtx {
    parse: ParseCtx,
    declared: HashSet<SymbolId>,
}

impl AssertBuildCtx {
    pub fn from_script(script: &Script) -> Result<Self, String> {
        let mut parse = ParseCtx::new();
        seed_parser_context(&mut parse, script)?;
        Ok(Self {
            parse,
            declared: declared_ids(script),
        })
    }

    pub fn push_assert(&mut self, commands: &mut Vec<SmtCommand>, b: &Bool) -> Result<(), String> {
        ensure_free_symbols_declared(b, &mut self.parse, &mut self.declared)?;
        commands.push(SmtCommand::new_assert(b.clone()));
        Ok(())
    }

    pub fn push_raw(&mut self, commands: &mut Vec<SmtCommand>, raw: &str) -> Result<(), String> {
        if let Some(name) = parse_declare_fun_name(raw) {
            if self.declared.contains(&symbol_id_from_name(&name)) {
                return Ok(());
            }
        }
        let cmd = parse_single_command(raw, &mut self.parse)?;
        if let Some(id) = declare_fun_symbol_id(&cmd) {
            self.declared.insert(id);
        }
        commands.push(cmd);
        Ok(())
    }

    pub fn ensure_declare_fun(&mut self, raw: &str) -> Result<(), String> {
        if let Some(name) = parse_declare_fun_name(raw) {
            if self.declared.contains(&symbol_id_from_name(&name)) {
                return Ok(());
            }
        }
        let cmd = parse_single_command(raw, &mut self.parse)?;
        if let Some(id) = declare_fun_symbol_id(&cmd) {
            self.declared.insert(id);
        }
        Ok(())
    }

    pub fn parse(&mut self) -> &mut ParseCtx {
        &mut self.parse
    }

    pub fn declared(&self) -> &HashSet<SymbolId> {
        &self.declared
    }

    pub fn declared_mut(&mut self) -> &mut HashSet<SymbolId> {
        &mut self.declared
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
    f: impl FnMut(&Bool) -> Result<Bool, String>,
) -> Result<Script, String> {
    map_asserts(script, f)
}

pub fn declared_ids(script: &Script) -> HashSet<SymbolId> {
    declared_symbol_ids(&script.commands)
}

pub fn is_true(b: &Bool) -> bool {
    b.as_bool() == Some(true)
}

pub fn push_assert_bool(
    commands: &mut Vec<SmtCommand>,
    b: Bool,
    ctx: &mut ParseCtx,
    declared: &mut HashSet<SymbolId>,
) -> Result<(), String> {
    ensure_free_symbols_declared(&b, ctx, declared)?;
    commands.push(SmtCommand::new_assert(b));
    Ok(())
}

pub fn push_command_raw(
    commands: &mut Vec<SmtCommand>,
    raw: &str,
    ctx: &mut ParseCtx,
    declared: &mut HashSet<SymbolId>,
) -> Result<(), String> {
    let cmd = parse_single_command(raw, ctx)?;
    if let Some(id) = declare_fun_symbol_id(&cmd) {
        declared.insert(id);
    }
    commands.push(cmd);
    Ok(())
}

pub fn rebuild_script(source: &str, commands: Vec<SmtCommand>) -> Script {
    Script::from_commands(source, commands)
}
