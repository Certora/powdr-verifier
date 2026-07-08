use std::fs;
use std::io::{self, Read};
use std::path::Path;

use regex::Regex;
use z3::ast::Bool;
use z3::Solver;

pub const STATUS_HEADER_BYTES: usize = 64 * 1024;

pub struct LoadedScript {
    pub prefix: String,
    pub z3_prefix: String,
    pub expected: Option<String>,
    pub assertions: Vec<Bool>,
}

pub fn read_input(path: &str) -> Result<String, String> {
    if path == "-" {
        let mut buf = String::new();
        io::stdin()
            .read_to_string(&mut buf)
            .map_err(|e| e.to_string())?;
        return Ok(buf);
    }
    fs::read_to_string(path).map_err(|e| e.to_string())
}

pub fn split_prefix(text: &str) -> Result<&str, String> {
    let idx = text
        .find("(check-sat)")
        .ok_or_else(|| "missing check-sat".to_string())?;
    Ok(&text[..idx])
}

pub fn extract_expected_status(text: &str) -> Option<String> {
    static RE: std::sync::OnceLock<Regex> = std::sync::OnceLock::new();
    let re = RE.get_or_init(|| Regex::new(r"\(set-info\s+:status\s+(\S+)").unwrap());
    let head = &text[..text.len().min(STATUS_HEADER_BYTES)];
    re.captures(head).map(|c| {
        c[1].trim_matches('"')
            .trim_end_matches(')')
            .to_string()
    })
}

/// Strip ``(set-info :status ...)`` before feeding Z3 (mirrors ``checker.py``).
pub fn z3_feed_prefix(prefix: &str) -> String {
    static RE: std::sync::OnceLock<Regex> = std::sync::OnceLock::new();
    let re = RE.get_or_init(|| Regex::new(r"\(set-info\s+:status\s+[^\n)]+\)\s*\n?").unwrap());
    re.replace_all(prefix, "").to_string()
}

pub fn load_script(text: &str) -> Result<LoadedScript, String> {
    let prefix = split_prefix(text)?.to_string();
    let expected = extract_expected_status(text);
    let z3_prefix = z3_feed_prefix(&prefix);
    let loader = Solver::new();
    loader.from_string(z3_prefix.as_bytes());
    let assertions = loader.get_assertions();
    Ok(LoadedScript {
        prefix,
        z3_prefix,
        expected,
        assertions,
    })
}

pub fn display_path(path: Option<&Path>) -> String {
    match path {
        None => "<memory>".to_string(),
        Some(p) => {
            let resolved = p.canonicalize().unwrap_or_else(|_| p.to_path_buf());
            if let Some(grandparent) = resolved.parent().and_then(|x| x.parent()) {
                if let Ok(rel) = resolved.strip_prefix(grandparent) {
                    return rel.display().to_string();
                }
            }
            resolved.display().to_string()
        }
    }
}
