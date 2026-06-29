//! Typed SMT-LIB commands.

use z3::ast::Bool;

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
                let b = ctx
                    .ingest_command(slice)?
                    .ok_or_else(|| format!("assert produced no formula in `{slice}`"))?;
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
            SmtCommand::Assert { bool: b, .. } => format!("(assert {b})"),
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

fn form_matches_source_slice(node: &SExpr, slice: &str) -> bool {
    let Ok((parsed, rest)) = SExpr::read_form(slice) else {
        return false;
    };
    if !rest.trim().is_empty() {
        return false;
    }
    parsed.node == *node
}
