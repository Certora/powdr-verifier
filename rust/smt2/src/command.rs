//! Typed SMT-LIB commands.

use std::collections::HashMap;

use z3::ast::Bool;
use z3::{FuncDecl, Sort, SortKind};

use crate::ast_util::{symbol_id_dyn, symbol_id_from_name, z3_if_to_ite, SymbolId};
use crate::sexpr::{command_head, SExpr, Span, Spanned};
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
    DeclareFun {
        form: Spanned<SExpr>,
        /// Cached Z3 symbol identity for ``declare-fun`` (set at parse after ingest).
        symbol_id: Option<SymbolId>,
        /// Cached Z3 range sort for ``declare-fun``.
        sort_kind: Option<SortKind>,
    },
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
    pub fn from_slice(span: Span, slice: &str, ctx: &mut ParseCtx) -> Result<Self, String> {
        let head = command_head(slice).ok_or("empty command")?;
        match head {
            "set-info" => {
                let (form, rest) = SExpr::read_form(slice)?;
                if !rest.trim().is_empty() {
                    return Err(format!("trailing input after command: `{slice}`"));
                }
                Ok(SmtCommand::SetInfo(form))
            }
            "set-logic" => {
                ctx.ingest_command(slice)?;
                let (form, rest) = SExpr::read_form(slice)?;
                if !rest.trim().is_empty() {
                    return Err(format!("trailing input after command: `{slice}`"));
                }
                Ok(SmtCommand::SetLogic(form))
            }
            "set-option" => {
                ctx.ingest_command(slice)?;
                let (form, rest) = SExpr::read_form(slice)?;
                if !rest.trim().is_empty() {
                    return Err(format!("trailing input after command: `{slice}`"));
                }
                Ok(SmtCommand::SetOption(form))
            }
            "declare-fun" => {
                ctx.ingest_command(slice)?;
                let (form, rest) = SExpr::read_form(slice)?;
                if !rest.trim().is_empty() {
                    return Err(format!("trailing input after command: `{slice}`"));
                }
                Ok(new_declare_fun(form))
            }
            "assert" => {
                let b = parse_assert(slice, span, ctx)?;
                Ok(SmtCommand::Assert {
                    bool: b,
                    span: Some(span),
                    term_text: None,
                })
            }
            "check-sat" => Ok(SmtCommand::CheckSat),
            "get-model" => Ok(SmtCommand::GetModel),
            "get-unsat-core" => Ok(SmtCommand::GetUnsatCore),
            "echo" => {
                let (form, rest) = SExpr::read_form(slice)?;
                if !rest.trim().is_empty() {
                    return Err(format!("trailing input after command: `{slice}`"));
                }
                Ok(SmtCommand::Echo(form))
            }
            "declare-sort" | "define-fun" => {
                ctx.ingest_command(slice)?;
                let (form, rest) = SExpr::read_form(slice)?;
                if !rest.trim().is_empty() {
                    return Err(format!("trailing input after command: `{slice}`"));
                }
                Ok(SmtCommand::Raw(form))
            }
            other if Z3_CMDS.contains(&other) => {
                ctx.ingest_command(slice)?;
                let (form, rest) = SExpr::read_form(slice)?;
                if !rest.trim().is_empty() {
                    return Err(format!("trailing input after command: `{slice}`"));
                }
                Ok(SmtCommand::Raw(form))
            }
            _ => {
                let (form, rest) = SExpr::read_form(slice)?;
                if !rest.trim().is_empty() {
                    return Err(format!("trailing input after command: `{slice}`"));
                }
                Ok(SmtCommand::Raw(form))
            }
        }
    }

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
                Ok(new_declare_fun(form))
            }
            "assert" => {
                let b = parse_assert(slice, form.span, ctx)?;
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
            SmtCommand::DeclareFun { .. } => "declare-fun",
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
            | SmtCommand::Echo(f)
            | SmtCommand::Raw(f) => Some(f.span),
            SmtCommand::DeclareFun { form, .. } => Some(form.span),
            SmtCommand::Assert { .. } | SmtCommand::CheckSat | SmtCommand::GetModel | SmtCommand::GetUnsatCore => None,
        }
    }

    pub fn spanned_form(&self) -> Option<&Spanned<SExpr>> {
        match self {
            SmtCommand::SetInfo(f)
            | SmtCommand::SetLogic(f)
            | SmtCommand::SetOption(f)
            | SmtCommand::Echo(f)
            | SmtCommand::Raw(f) => Some(f),
            SmtCommand::DeclareFun { form, .. } => Some(form),
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
                if crate::ast_util::has_quantifier(b) {
                    let pretty = crate::pretty::pretty_print_bool_in_script(b);
                    format!("(assert {})", crate::ast_util::z3_uminus_to_mul(&pretty))
                } else {
                    let raw = crate::ast_util::z3_uminus_to_mul(&z3_if_to_ite(&b.to_string()));
                    format!("(assert {})", crate::sexpr::strip_smtlib_annotations(&raw))
                }
            }
            SmtCommand::CheckSat => "(check-sat)".into(),
            SmtCommand::GetModel => "(get-model)".into(),
            SmtCommand::GetUnsatCore => "(get-unsat-core)".into(),
            SmtCommand::SetInfo(f)
            | SmtCommand::SetLogic(f)
            | SmtCommand::SetOption(f)
            | SmtCommand::Echo(f)
            | SmtCommand::Raw(f) => Self::spanned_text(f, source),
            SmtCommand::DeclareFun { form, .. } => Self::spanned_text(form, source),
        }
    }
}

pub fn declare_fun_symbol(form: &SExpr) -> Option<String> {
    declare_fun_symbol_name_from_form(form).map(|s| s.to_string())
}

fn declare_fun_symbol_name_from_form(form: &SExpr) -> Option<&str> {
    form.args()?.first()?.node.as_atom()
}

pub fn parse_single_command(input: &str, ctx: &mut ParseCtx) -> Result<SmtCommand, String> {
    let (form, _) = crate::sexpr::SExpr::read_form(input)?;
    SmtCommand::from_spanned(form, input, ctx)
}

pub fn declare_fun_name_cmd(cmd: &SmtCommand) -> Option<String> {
    match cmd {
        SmtCommand::DeclareFun { form, .. } => declare_fun_symbol(&form.node),
        _ => cmd
            .spanned_form()
            .and_then(|f| if cmd.name() == "declare-fun" { declare_fun_symbol(&f.node) } else { None }),
    }
}

fn declare_fun_form(cmd: &SmtCommand) -> Option<&SExpr> {
    match cmd {
        SmtCommand::DeclareFun { form, .. } => Some(&form.node),
        _ => cmd
            .spanned_form()
            .filter(|_| cmd.name() == "declare-fun")
            .map(|f| &f.node),
    }
}

fn nullary_declare_fun_params(params: &SExpr) -> bool {
    matches!(params, SExpr::List(items) if items.is_empty())
}

fn sort_atom_names(sort: &Sort, atom: &str) -> bool {
    atom == sort.to_string().as_str()
}

fn sexpr_to_z3_sort(sort: &SExpr) -> Sort {
    match sort {
        SExpr::List(items) if items.first().and_then(|h| h.node.head()) == Some("Array") => {
            let dom = items
                .get(1)
                .map(|s| sexpr_to_z3_sort(&s.node))
                .unwrap_or_else(Sort::int);
            let rng = items
                .get(2)
                .map(|s| sexpr_to_z3_sort(&s.node))
                .unwrap_or_else(Sort::int);
            Sort::array(&dom, &rng)
        }
        SExpr::Atom(atom) => {
            let bool_sort = Sort::bool();
            let int_sort = Sort::int();
            if sort_atom_names(&bool_sort, atom) {
                bool_sort
            } else if sort_atom_names(&int_sort, atom) {
                int_sort
            } else {
                int_sort
            }
        }
        _ => Sort::int(),
    }
}

fn nullary_declare_fun_meta(form: &SExpr) -> Option<(SymbolId, SortKind)> {
    let args = form.args()?;
    let name = args.first()?.node.as_atom()?;
    if !nullary_declare_fun_params(&args.get(1)?.node) {
        return None;
    }
    let sort = sexpr_to_z3_sort(&args.get(2)?.node);
    let kind = sort.kind();
    let ast = FuncDecl::new(name, &[], &sort).apply(&[]);
    let id = symbol_id_dyn(&ast)?;
    Some((id, kind))
}

fn int_only_param_arity(params: &SExpr) -> Option<usize> {
    let items = match params {
        SExpr::List(items) => items,
        _ => return None,
    };
    for p in items {
        match &p.node {
            SExpr::Atom(a) if a == "Int" => {}
            _ => return None,
        }
    }
    Some(items.len())
}

/// Symbol metadata for nullary and ``Int``-returning UF ``declare-fun`` forms.
fn declare_fun_meta(form: &SExpr) -> Option<(SymbolId, SortKind)> {
    if let Some(meta) = nullary_declare_fun_meta(form) {
        return Some(meta);
    }
    let args = form.args()?;
    let name = args.first()?.node.as_atom()?;
    int_only_param_arity(&args.get(1)?.node)?;
    let ret = sexpr_to_z3_sort(&args.get(2)?.node);
    if ret.kind() != SortKind::Int {
        return None;
    }
    Some((symbol_id_from_name(name), SortKind::Int))
}

fn new_declare_fun(form: Spanned<SExpr>) -> SmtCommand {
    let meta = declare_fun_meta(&form.node);
    let (symbol_id, sort_kind) = match meta {
        Some((id, kind)) => (Some(id), Some(kind)),
        None => (None, None),
    };
    SmtCommand::DeclareFun {
        form,
        symbol_id,
        sort_kind,
    }
}

/// Cached ``declare-fun`` symbol identity (see [`SmtCommand::DeclareFun`]).
pub fn declare_fun_symbol_id(cmd: &SmtCommand) -> Option<SymbolId> {
    match cmd {
        SmtCommand::DeclareFun { symbol_id, .. } => *symbol_id,
        _ => declare_fun_form(cmd)
            .and_then(declare_fun_meta)
            .map(|(id, _)| id),
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
        | SmtCommand::Echo(f)
        | SmtCommand::Raw(f) => f.text(source),
        SmtCommand::DeclareFun { form, .. } => form.text(source),
    }
}

pub(crate) fn parse_assert(slice: &str, _span: Span, ctx: &mut ParseCtx) -> Result<Bool, String> {
    if let Some(b) = ctx.ingest_command(slice)? {
        return Ok(b);
    }
    let (form, rest) = SExpr::read_form(slice)?;
    if !rest.trim().is_empty() {
        return Err(format!("trailing input after assert: `{slice}`"));
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
