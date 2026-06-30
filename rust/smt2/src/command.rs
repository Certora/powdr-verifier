//! Typed SMT-LIB commands.

use std::collections::HashMap;

use z3::ast::Bool;

use crate::ast_util::z3_if_to_ite;
use crate::sexpr::{SExpr, Span, Spanned};
use crate::z3_parse::ParseCtx;

const Z3_CMDS: &[&str] = &[
    "assert",
    "declare-fun",
    "declare-sort",
    "define-fun",
    "set-logic",
    "set-option",
];

#[derive(Clone, Debug)]
pub enum SmtCommand {
    SetInfo(Spanned<SExpr>),
    SetLogic(Spanned<SExpr>),
    SetOption(Spanned<SExpr>),
    DeclareFun(Spanned<SExpr>),
    Assert {
        bool: Bool,
        span: Option<Span>,
        term_text: Option<String>,
    },
    CheckSat,
    GetModel,
    GetUnsatCore,
    Echo(Spanned<SExpr>),
    Raw(Spanned<SExpr>),
}

impl SmtCommand {
    pub fn from_spanned(
        form: Spanned<SExpr>,
        input: &str,
        ctx: &mut ParseCtx,
    ) -> Result<Self, String> {
        let slice = form.text(input);
        let head = form.node.head().ok_or("empty command")?;
        match head {
            "set-info" => Ok(SmtCommand::SetInfo(form)),
            "set-logic" => {
                ctx.ingest_command(slice)?;
                Ok(SmtCommand::SetLogic(form))
            }
            "set-option" => {
                ctx.ingest_command(slice)?;
                Ok(SmtCommand::SetOption(form))
            }
            "declare-fun" => {
                ctx.ingest_command(slice)?;
                Ok(SmtCommand::DeclareFun(form))
            }
            "assert" => {
                let b = parse_assert(&form, slice, ctx)?;
                Ok(SmtCommand::Assert {
                    bool: b,
                    span: Some(form.span),
                    term_text: None,
                })
            }
            "check-sat" => Ok(SmtCommand::CheckSat),
            "get-model" => Ok(SmtCommand::GetModel),
            "get-unsat-core" => Ok(SmtCommand::GetUnsatCore),
            "echo" => Ok(SmtCommand::Echo(form)),
            "declare-sort" | "define-fun" => {
                ctx.ingest_command(slice)?;
                Ok(SmtCommand::Raw(form))
            }
            other if Z3_CMDS.contains(&other) => {
                ctx.ingest_command(slice)?;
                Ok(SmtCommand::Raw(form))
            }
            _ => Ok(SmtCommand::Raw(form)),
        }
    }

    pub fn name(&self) -> &str {
        match self {
            SmtCommand::SetInfo(_) => "set-info",
            SmtCommand::SetLogic(_) => "set-logic",
            SmtCommand::SetOption(_) => "set-option",
            SmtCommand::DeclareFun(_) => "declare-fun",
            SmtCommand::Assert { .. } => "assert",
            SmtCommand::CheckSat => "check-sat",
            SmtCommand::GetModel => "get-model",
            SmtCommand::GetUnsatCore => "get-unsat-core",
            SmtCommand::Echo(_) => "echo",
            SmtCommand::Raw(f) => f.node.head().unwrap_or("raw"),
        }
    }

    pub fn span(&self) -> Option<Span> {
        match self {
            SmtCommand::SetInfo(f)
            | SmtCommand::SetLogic(f)
            | SmtCommand::SetOption(f)
            | SmtCommand::DeclareFun(f)
            | SmtCommand::Echo(f)
            | SmtCommand::Raw(f) => Some(f.span),
            SmtCommand::Assert { .. } | SmtCommand::CheckSat | SmtCommand::GetModel | SmtCommand::GetUnsatCore => None,
        }
    }

    pub fn spanned_form(&self) -> Option<&Spanned<SExpr>> {
        match self {
            SmtCommand::SetInfo(f)
            | SmtCommand::SetLogic(f)
            | SmtCommand::SetOption(f)
            | SmtCommand::DeclareFun(f)
            | SmtCommand::Echo(f)
            | SmtCommand::Raw(f) => Some(f),
            _ => None,
        }
    }

    pub fn assert_bool(&self) -> Option<&Bool> {
        match self {
            SmtCommand::Assert { bool: b, .. } => Some(b),
            _ => None,
        }
    }

    pub fn assert_span(&self) -> Option<Span> {
        match self {
            SmtCommand::Assert { span, .. } => *span,
            _ => None,
        }
    }

    pub fn new_assert(bool: Bool) -> Self {
        SmtCommand::Assert {
            bool,
            span: None,
            term_text: None,
        }
    }

    pub fn new_assert_from_term(bool: Bool, term_text: String) -> Self {
        SmtCommand::Assert {
            bool,
            span: None,
            term_text: Some(term_text),
        }
    }

    fn spanned_text(f: &Spanned<SExpr>, source: &str) -> String {
        if f.span.end <= source.len() {
            let slice = f.text(source);
            if form_matches_source_slice(&f.node, slice) {
                return slice.to_string();
            }
        }
        f.node.to_string()
    }

    pub fn to_smtlib(&self, source: &str) -> String {
        match self {
            SmtCommand::Assert {
                term_text: Some(t),
                ..
            } => format!("(assert {t})"),
            SmtCommand::Assert { bool: b, .. } => {
                let raw = z3_if_to_ite(&b.to_string());
                format!("(assert {})", crate::sexpr::strip_smtlib_annotations(&raw))
            }
            SmtCommand::CheckSat => "(check-sat)".into(),
            SmtCommand::GetModel => "(get-model)".into(),
            SmtCommand::GetUnsatCore => "(get-unsat-core)".into(),
            SmtCommand::SetInfo(f)
            | SmtCommand::SetLogic(f)
            | SmtCommand::SetOption(f)
            | SmtCommand::DeclareFun(f)
            | SmtCommand::Echo(f)
            | SmtCommand::Raw(f) => Self::spanned_text(f, source),
        }
    }
}

pub fn declare_fun_symbol(form: &SExpr) -> Option<String> {
    let args = form.args()?;
    args.first()?.node.as_atom().map(|s| s.to_string())
}

pub fn parse_single_command(input: &str, ctx: &mut ParseCtx) -> Result<SmtCommand, String> {
    let (form, _) = crate::sexpr::SExpr::read_form(input)?;
    SmtCommand::from_spanned(form, input, ctx)
}

pub fn declare_fun_name_cmd(cmd: &SmtCommand) -> Option<String> {
    match cmd {
        SmtCommand::DeclareFun(f) => declare_fun_symbol(&f.node),
        _ => cmd
            .spanned_form()
            .and_then(|f| if cmd.name() == "declare-fun" { declare_fun_symbol(&f.node) } else { None }),
    }
}

pub fn command_text<'a>(cmd: &SmtCommand, source: &'a str) -> &'a str {
    match cmd {
        SmtCommand::Assert { bool: b, .. } => {
            // not applicable - caller should handle
            let _ = b;
            ""
        }
        SmtCommand::CheckSat => "(check-sat)",
        SmtCommand::GetModel => "(get-model)",
        SmtCommand::GetUnsatCore => "(get-unsat-core)",
        SmtCommand::SetInfo(f)
        | SmtCommand::SetLogic(f)
        | SmtCommand::SetOption(f)
        | SmtCommand::DeclareFun(f)
        | SmtCommand::Echo(f)
        | SmtCommand::Raw(f) => f.text(source),
    }
}

pub(crate) fn parse_assert(form: &Spanned<SExpr>, slice: &str, ctx: &mut ParseCtx) -> Result<Bool, String> {
    if let Some(b) = ctx.ingest_command(slice)? {
        return Ok(b);
    }
    let body = form
        .node
        .args()
        .and_then(|a| a.first())
        .ok_or_else(|| format!("malformed assert: `{slice}`"))?;
    for (sym, is_bool) in infer_sexpr_symbol_sorts(&body.node) {
        let sort = if is_bool {
            "Bool"
        } else if sym.contains("memory_is") || sym.contains("memory_match") {
            "Bool"
        } else {
            "Int"
        };
        let _ = ctx.ingest_command(&format!("(declare-fun {sym} () {sort})"));
    }
    let body_text = body.node.to_string();
    ctx.ingest_command(&format!("(assert {body_text})"))?
        .ok_or_else(|| format!("assert produced no formula in `{slice}`"))
}

fn infer_sexpr_symbol_sorts(expr: &SExpr) -> HashMap<String, bool> {
    let mut sorts: HashMap<String, bool> = HashMap::new();
    infer_sorts(expr, &[], false, &mut sorts);
    sorts
}

fn infer_sorts(expr: &SExpr, bound: &[&str], bool_ctx: bool, sorts: &mut HashMap<String, bool>) {
    match expr {
        SExpr::Atom(s) => {
            if is_sexpr_symbol(s) && !bound.contains(&s.as_str()) {
                sorts
                    .entry(s.clone())
                    .and_modify(|b| *b = *b && bool_ctx)
                    .or_insert(bool_ctx);
            }
        }
        SExpr::List(items) if !items.is_empty() => {
            let head = items[0].node.head().unwrap_or("");
            if (head == "forall" || head == "exists") && items.len() >= 3 {
                let mut new_bound: Vec<String> = bound.iter().map(|s| s.to_string()).collect();
                if let SExpr::List(decls) = &items[1].node {
                    for d in decls {
                        let name = d
                            .node
                            .as_atom()
                            .or_else(|| d.node.args()?.first()?.node.as_atom());
                        if let Some(name) = name {
                            new_bound.push(name.to_string());
                        }
                    }
                }
                let bound_refs: Vec<&str> = new_bound.iter().map(|s| s.as_str()).collect();
                infer_sorts(&items[2].node, &bound_refs, false, sorts);
                return;
            }
            if head == "let" && items.len() >= 3 {
                let mut new_bound: Vec<String> = bound.iter().map(|s| s.to_string()).collect();
                if let SExpr::List(binders) = &items[1].node {
                    for binder in binders {
                        if let Some(pair) = binder.node.args() {
                            if let Some(name) = pair.first().and_then(|p| p.node.as_atom()) {
                                new_bound.push(name.to_string());
                            }
                            if pair.len() >= 2 {
                                infer_sorts(&pair[1].node, bound, false, sorts);
                            }
                        }
                    }
                }
                let bound_refs: Vec<&str> = new_bound.iter().map(|s| s.as_str()).collect();
                infer_sorts(&items[2].node, &bound_refs, bool_ctx, sorts);
                return;
            }
            let arith = matches!(head, "+" | "-" | "*" | "mod" | "<" | "<=" | ">" | ">=");
            let bool_op = matches!(head, "not" | "and" | "or" | "=>" | "ite");
            if head == "=" && items.len() >= 3 {
                let lhs_arith = is_arithish(&items[1].node);
                let rhs_arith = is_arithish(&items[2].node);
                let int_eq = lhs_arith || rhs_arith;
                infer_sorts(&items[1].node, bound, !int_eq && bool_ctx, sorts);
                infer_sorts(&items[2].node, bound, !int_eq && bool_ctx, sorts);
                return;
            }
            let child_bool = bool_op || bool_ctx;
            let child_int = arith;
            for item in &items[1..] {
                infer_sorts(
                    &item.node,
                    bound,
                    if child_int {
                        false
                    } else {
                        child_bool
                    },
                    sorts,
                );
            }
        }
        _ => {}
    }
}

fn is_arithish(expr: &SExpr) -> bool {
    match expr {
        SExpr::Atom(s) => is_sexpr_symbol(s) || crate::ast_util::is_int_literal_string(s),
        SExpr::List(items) if !items.is_empty() => {
            let head = items[0].node.head().unwrap_or("");
            matches!(head, "+" | "-" | "*" | "mod" | "<" | "<=" | ">" | ">=")
                || items[1..].iter().any(|i| is_arithish(&i.node))
        }
        _ => false,
    }
}

fn is_sexpr_symbol(s: &str) -> bool {
    if s == "true" || s == "false" {
        return false;
    }
    if crate::ast_util::is_int_literal_string(s) {
        return false;
    }
    const KEYWORDS: &[&str] = &[
        "Int", "Bool", "Real", "Array", "Select", "Store", "and", "or", "not", "=>", "ite",
        "forall", "exists", "let", "=", "distinct", "mod", "+", "-", "*", "<", "<=", ">", ">=",
    ];
    !KEYWORDS.contains(&s)
}

fn form_matches_source_slice(node: &SExpr, slice: &str) -> bool {
    let Ok((parsed, rest)) = SExpr::read_form(slice) else {
        return false;
    };
    if !rest.trim().is_empty() {
        return false;
    }
    parsed.node == *node
}
