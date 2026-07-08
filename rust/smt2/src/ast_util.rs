//! Thin Z3 AST helpers (domain-specific; generic ops use `z3::ast` directly).

use std::collections::{BTreeMap, HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::str::FromStr;

use z3::ast::{Ast, AstKind, Bool, Dynamic, Int};
use z3::{Context, DeclKind, FuncDecl, SortKind};
use z3_sys::*;

pub fn decl_name(decl: &FuncDecl) -> String {
    decl.name()
}

/// Z3 names integer if-then-else ``if``; SMT-LIB and PySMT expect ``ite``.
pub fn smtlib_decl_name(decl: &FuncDecl) -> String {
    let name = decl_name(decl);
    if name == "if" {
        "ite".into()
    } else {
        name
    }
}

/// Rewrite Z3's non-standard ``(if ...)`` nodes to ``(ite ...)`` in serialized text.
pub fn z3_if_to_ite(s: &str) -> String {
    if s.contains("(if ") {
        s.replace("(if ", "(ite ")
    } else {
        s.to_string()
    }
}

pub fn is_int_numeral(ast: &Dynamic) -> bool {
    ast.kind() == AstKind::Numeral && ast.get_sort().kind() == SortKind::Int
}

pub fn is_bool_const(ast: &Dynamic) -> bool {
    ast.as_bool().and_then(|b| b.as_bool()).is_some()
}

pub fn is_int_const(ast: &Dynamic) -> bool {
    ast.kind() == AstKind::App
        && ast.is_const()
        && ast.get_sort().kind() == SortKind::Int
        && !is_int_numeral(ast)
}

pub fn int_const_name(ast: &Dynamic) -> Option<String> {
    if is_int_const(ast) {
        Some(decl_name(&ast.decl()))
    } else {
        None
    }
}

pub fn ast_hash_dyn(ast: &Dynamic) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    ast.hash(&mut hasher);
    hasher.finish()
}

pub fn ast_hash_bool(b: &Bool) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    b.hash(&mut hasher);
    hasher.finish()
}

pub fn ast_hash_int(i: &Int) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    i.hash(&mut hasher);
    hasher.finish()
}

/// Deduplicated Int terms with structural lookup.
///
/// ``Int`` implements ``Hash`` (``Z3_get_ast_hash``) and ``Eq`` (``Z3_is_eq_ast``),
/// so a ``HashMap`` keyed on the term itself gives O(1) structural dedup with
/// proper collision handling. ``terms`` retains a stable index -> term mapping.
#[derive(Clone)]
pub struct IntTermSet {
    terms: Vec<Int>,
    idx: HashMap<Int, usize>,
}

impl IntTermSet {
    pub fn new() -> Self {
        Self {
            terms: Vec::new(),
            idx: HashMap::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.terms.len()
    }

    pub fn is_empty(&self) -> bool {
        self.terms.is_empty()
    }

    pub fn terms(&self) -> &[Int] {
        &self.terms
    }

    pub fn contains(&self, term: &Int) -> bool {
        self.idx.contains_key(term)
    }

    pub fn index_of(&self, term: &Int) -> Option<usize> {
        self.idx.get(term).copied()
    }

    pub fn from_sorted_unique(terms: Vec<Int>) -> Self {
        let mut idx = HashMap::with_capacity(terms.len());
        for (i, t) in terms.iter().enumerate() {
            idx.insert(t.clone(), i);
        }
        Self { terms, idx }
    }

    /// Returns the index of ``term`` (existing or newly inserted).
    pub fn insert(&mut self, term: Int) -> usize {
        if let Some(&i) = self.idx.get(&term) {
            return i;
        }
        let i = self.terms.len();
        self.idx.insert(term.clone(), i);
        self.terms.push(term);
        i
    }

    pub fn get(&self, index: usize) -> Option<&Int> {
        self.terms.get(index)
    }

    /// Consume the set, yielding the owned term vector without cloning.
    pub fn into_terms(self) -> Vec<Int> {
        self.terms
    }
}

impl Default for IntTermSet {
    fn default() -> Self {
        Self::new()
    }
}

pub fn int_value(e: &Int) -> Option<i128> {
    if let Some(v) = e.as_i64() {
        return Some(v as i128);
    }
    if e.kind() != AstKind::Numeral || e.get_sort().kind() != SortKind::Int {
        return None;
    }
    unsafe {
        let ctx = e.get_ctx().get_z3_context();
        let ast = e.get_z3_ast();
        if !Z3_is_numeral_ast(ctx, ast) {
            return None;
        }
        let ptr = Z3_get_numeral_string(ctx, ast);
        if ptr.is_null() {
            return None;
        }
        let s = std::ffi::CStr::from_ptr(ptr).to_string_lossy();
        parse_int_literal(&s)
    }
}

pub fn int_value_dyn(ast: &Dynamic) -> Option<i128> {
    ast.as_int().and_then(|i| int_value(&i))
}

/// SMT-LIB rendering of an integer numeral, bypassing Z3's `ast_smt_pp`
/// (`smt_renaming`) printer. Negatives become `(- k)`; rationals return `None`.
pub fn numeral_smtlib_string(ast: &Dynamic) -> Option<String> {
    if ast.kind() != AstKind::Numeral {
        return None;
    }
    unsafe {
        let ctx = ast.get_ctx().get_z3_context();
        let a = ast.get_z3_ast();
        if !Z3_is_numeral_ast(ctx, a) {
            return None;
        }
        let ptr = Z3_get_numeral_string(ctx, a);
        if ptr.is_null() {
            return None;
        }
        let s = std::ffi::CStr::from_ptr(ptr).to_string_lossy();
        if s.contains('/') {
            return None;
        }
        match s.strip_prefix('-') {
            Some(mag) => Some(format!("(- {mag})")),
            None => Some(s.into_owned()),
        }
    }
}

pub fn parse_int_literal(s: &str) -> Option<i128> {
    if let Some(hex) = s.strip_prefix("#x") {
        return u128::from_str_radix(hex, 16).ok().map(|v| v as i128);
    }
    if let Some(bin) = s.strip_prefix("#b") {
        return u128::from_str_radix(bin, 2).ok().map(|v| v as i128);
    }
    s.parse::<i128>().ok()
}

pub fn is_int_literal_string(s: &str) -> bool {
    if s.starts_with("#x") || s.starts_with("#b") {
        return s.len() > 2;
    }
    let digits = s.strip_prefix('-').unwrap_or(s);
    !digits.is_empty() && digits.chars().all(|c| c.is_ascii_digit())
}

fn normalized_mod(v: i128, m: i128) -> i128 {
    ((v % m) + m) % m
}

pub fn mod_int_literal_string(s: &str, modulus: i128) -> Option<String> {
    if modulus <= 0 {
        return None;
    }
    if let Some(v) = parse_int_literal(s) {
        return Some(normalized_mod(v, modulus).to_string());
    }
    if !is_int_literal_string(s) {
        return None;
    }
    let neg = s.starts_with('-');
    let digits = s.strip_prefix('-').unwrap_or(s);
    let mut rem: i128 = 0;
    for d in digits.as_bytes() {
        if !d.is_ascii_digit() {
            return None;
        }
        rem = (rem * 10 + i128::from(*d - b'0')) % modulus;
    }
    if neg {
        rem = normalized_mod(-rem, modulus);
    } else {
        rem = normalized_mod(rem, modulus);
    }
    Some(rem.to_string())
}

pub fn strip_prefix(name: &str) -> &str {
    for prefix in ["before-", "after-"] {
        if let Some(rest) = name.strip_prefix(prefix) {
            return rest;
        }
    }
    name
}

pub fn swap_prefix(name: &str) -> Option<String> {
    if let Some(rest) = name.strip_prefix("before-") {
        return Some(format!("after-{rest}"));
    }
    if let Some(rest) = name.strip_prefix("after-") {
        return Some(format!("before-{rest}"));
    }
    None
}

pub fn is_program_variable(name: &str) -> bool {
    strip_prefix(name).contains('@')
}

pub fn free_int_symbols(b: &Bool) -> HashSet<String> {
    free_int_nodes(b)
        .into_iter()
        .map(|i| decl_name(&Dynamic::from_ast(&i).decl()))
        .collect()
}

/// Free ``Int`` constant nodes in ``b`` (hash-consed; suitable as map/set keys).
pub fn free_int_nodes(b: &Bool) -> HashSet<Int> {
    let mut out = HashSet::new();
    collect_free_int_nodes(&Dynamic::from_ast(b), &HashSet::new(), &mut out);
    out
}

pub fn scoped_free_int_nodes(ast: &Dynamic, bound: &HashSet<SymbolId>) -> HashSet<Int> {
    let mut out = HashSet::new();
    collect_free_int_nodes(ast, bound, &mut out);
    out
}

/// Free symbol identities in ``b`` (any sort), excluding literals and binders.
pub fn free_symbol_ids_bool(b: &Bool) -> HashSet<SymbolId> {
    let mut out = HashSet::new();
    collect_free_symbol_ids(&Dynamic::from_ast(b), &HashSet::new(), &mut out);
    out
}

pub fn scoped_free_symbol_ids(ast: &Dynamic, bound: &HashSet<SymbolId>) -> HashSet<SymbolId> {
    let mut out = HashSet::new();
    collect_free_symbol_ids(ast, bound, &mut out);
    out
}

fn is_free_named_symbol(ast: &Dynamic) -> bool {
    if int_value_dyn(ast).is_some() {
        return false;
    }
    if ast.as_bool().and_then(|b| b.as_bool()).is_some() {
        return false;
    }
    symbol_id_dyn(ast).is_some()
}

fn collect_free_int_nodes(ast: &Dynamic, bound: &HashSet<SymbolId>, out: &mut HashSet<Int>) {
    match ast.kind() {
        AstKind::Var => {}
        AstKind::Quantifier => {
            let mut next_bound = bound.clone();
            next_bound.extend(quantifier_bound_symbol_ids(ast));
            if let Some(body) = quantifier_body(ast) {
                collect_free_int_nodes(&body, &next_bound, out);
            }
        }
        AstKind::App if is_int_const(ast) => {
            if let Some(id) = symbol_id_dyn(ast) {
                if !bound.contains(&id) {
                    if let Some(i) = ast.as_int() {
                        out.insert(i);
                    }
                }
            }
        }
        AstKind::App => {
            for i in 0..ast.num_children() {
                if let Some(ch) = ast.nth_child(i) {
                    collect_free_int_nodes(&ch, bound, out);
                }
            }
        }
        _ => {}
    }
}

fn collect_free_symbol_ids(ast: &Dynamic, bound: &HashSet<SymbolId>, out: &mut HashSet<SymbolId>) {
    if is_free_named_symbol(ast) {
        if let Some(id) = symbol_id_dyn(ast) {
            if !bound.contains(&id) {
                out.insert(id);
            }
        }
        return;
    }
    if ast.kind() == AstKind::Quantifier {
        let mut next_bound = bound.clone();
        next_bound.extend(quantifier_bound_symbol_ids(ast));
        if let Some(body) = quantifier_body(ast) {
            collect_free_symbol_ids(&body, &next_bound, out);
        }
        return;
    }
    if ast.kind() == AstKind::App {
        for i in 0..ast.num_children() {
            if let Some(ch) = ast.nth_child(i) {
                collect_free_symbol_ids(&ch, bound, out);
            }
        }
    }
}

/// Uninterpreted ``Int``-returning function symbols used in a formula (e.g. ``uf_and``).
pub fn free_uf_function_symbols(b: &Bool) -> BTreeMap<String, usize> {
    let mut out = BTreeMap::new();
    collect_uf_function_symbols(&Dynamic::from_ast(b), &HashSet::new(), &mut out);
    out
}

fn is_builtin_int_decl_kind(kind: DeclKind) -> bool {
    matches!(
        kind,
        DeclKind::Add
            | DeclKind::Sub
            | DeclKind::Mul
            | DeclKind::Mod
            | DeclKind::Div
            | DeclKind::Rem
            | DeclKind::Uminus
            | DeclKind::ToInt
            | DeclKind::Ite
            | DeclKind::And
            | DeclKind::Or
            | DeclKind::Not
            | DeclKind::Eq
            | DeclKind::Lt
            | DeclKind::Le
            | DeclKind::Gt
            | DeclKind::Ge
            | DeclKind::Distinct
            | DeclKind::Implies
            | DeclKind::Anum
            | DeclKind::Agnum
    )
}

fn collect_uf_function_symbols(
    ast: &Dynamic,
    bound: &HashSet<String>,
    out: &mut BTreeMap<String, usize>,
) {
    match ast.kind() {
        AstKind::Var => {}
        AstKind::Quantifier => {
            let mut next_bound = bound.clone();
            for name in quantifier_bound_names(ast) {
                next_bound.insert(name);
            }
            if let Some(body) = quantifier_body(ast) {
                collect_uf_function_symbols(&body, &next_bound, out);
            }
        }
        AstKind::App => {
            let decl = ast.decl();
            let name = decl_name(&decl);
            let arity = decl.arity();
            if arity > 0
                && ast.get_sort().kind() == SortKind::Int
                && !is_builtin_int_decl_kind(decl.kind())
                && !bound.contains(&name)
            {
                out.entry(name).or_insert(arity);
            }
            for i in 0..ast.num_children() {
                if let Some(ch) = ast.nth_child(i) {
                    collect_uf_function_symbols(&ch, bound, out);
                }
            }
        }
        _ => {}
    }
}

pub fn scoped_free_int_symbols(ast: &Dynamic, bound: &HashSet<String>) -> HashSet<String> {
    let bound_ids: HashSet<SymbolId> = bound.iter().map(|n| symbol_id_from_name(n)).collect();
    scoped_free_int_nodes(ast, &bound_ids)
        .into_iter()
        .map(|i| decl_name(&Dynamic::from_ast(&i).decl()))
        .collect()
}

pub fn has_quantifier(b: &Bool) -> bool {
    has_quantifier_dyn(&Dynamic::from_ast(b))
}

fn has_quantifier_dyn(ast: &Dynamic) -> bool {
    if ast.kind() == AstKind::Quantifier {
        return true;
    }
    if ast.kind() == AstKind::App {
        for i in 0..ast.num_children() {
            if let Some(ch) = ast.nth_child(i) {
                if has_quantifier_dyn(&ch) {
                    return true;
                }
            }
        }
    }
    false
}

pub fn quantifier_body(ast: &Dynamic) -> Option<Dynamic> {
    if ast.kind() != AstKind::Quantifier {
        return None;
    }
    let ctx = ast.get_ctx();
    unsafe {
        let z3 = ctx.get_z3_context();
        let body = Z3_get_quantifier_body(z3, ast.get_z3_ast())?;
        Some(Dynamic::wrap(ctx, body))
    }
}

pub fn ast_children(ast: &Dynamic) -> Vec<Dynamic> {
    match ast.kind() {
        AstKind::Quantifier => quantifier_body(ast).into_iter().collect(),
        AstKind::App => {
            let mut out = Vec::new();
            for i in 0..ast.num_children() {
                if let Some(c) = ast.nth_child(i) {
                    out.push(c);
                }
            }
            out
        }
        _ => Vec::new(),
    }
}

pub fn quantifier_bound_names(ast: &Dynamic) -> Vec<String> {
    if ast.kind() != AstKind::Quantifier {
        return Vec::new();
    }
    let ctx = ast.get_ctx();
    unsafe {
        let z3 = ctx.get_z3_context();
        let n = Z3_get_quantifier_num_bound(z3, ast.get_z3_ast());
        let mut out = Vec::with_capacity(n as usize);
        for i in 0..n {
            let sym = Z3_get_quantifier_bound_name(z3, ast.get_z3_ast(), i).unwrap();
            out.push(z3_symbol_to_string(ctx, sym));
        }
        out
    }
}

/// Interned Z3 symbol identity. Z3 interns symbol names per manager, so pointer
/// equality of the underlying ``Z3_symbol`` is name equality — usable for
/// string-free name comparisons within one context.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct SymbolId(usize);

/// Binder name identities of a quantifier (declaration order), without materializing strings.
pub fn quantifier_bound_symbol_ids(ast: &Dynamic) -> Vec<SymbolId> {
    if ast.kind() != AstKind::Quantifier {
        return Vec::new();
    }
    let ctx = ast.get_ctx();
    unsafe {
        let z3 = ctx.get_z3_context();
        let n = Z3_get_quantifier_num_bound(z3, ast.get_z3_ast());
        let mut out = Vec::with_capacity(n as usize);
        for i in 0..n {
            let sym = Z3_get_quantifier_bound_name(z3, ast.get_z3_ast(), i).unwrap();
            out.push(SymbolId(sym.as_ptr() as usize));
        }
        out
    }
}

/// Z3 range sorts of quantifier binders (declaration order).
pub fn quantifier_bound_sort_kinds(ast: &Dynamic) -> Vec<SortKind> {
    if ast.kind() != AstKind::Quantifier {
        return Vec::new();
    }
    let ctx = ast.get_ctx();
    unsafe {
        let z3 = ctx.get_z3_context();
        let n = Z3_get_quantifier_num_bound(z3, ast.get_z3_ast());
        let mut out = Vec::with_capacity(n as usize);
        for i in 0..n {
            let sort = Z3_get_quantifier_bound_sort(z3, ast.get_z3_ast(), i).unwrap();
            out.push(Z3_get_sort_kind(z3, sort));
        }
        out
    }
}

/// Name identity of a free constant/symbol node, without materializing a string.
/// Mirrors the predicate of [`crate::ast_build::symbol_name_dyn`].
pub fn symbol_id_dyn(ast: &Dynamic) -> Option<SymbolId> {
    if !(is_int_const(ast) || (ast.kind() == AstKind::App && ast.is_const())) {
        return None;
    }
    unsafe {
        let z3 = ast.get_ctx().get_z3_context();
        let app = Z3_to_app(z3, ast.get_z3_ast())?;
        let decl = Z3_get_app_decl(z3, app)?;
        let sym = Z3_get_decl_name(z3, decl)?;
        Some(SymbolId(sym.as_ptr() as usize))
    }
}

/// Intern ``name`` and return its [`SymbolId`]. Z3 interns symbols per manager,
/// so the result matches [`symbol_id_dyn`] / [`quantifier_bound_symbol_ids`] for
/// any node carrying the same name in the thread-local context.
pub fn symbol_id_from_name(name: &str) -> SymbolId {
    let ctx = Context::thread_local();
    let cname = std::ffi::CString::new(name).expect("symbol name contains NUL");
    unsafe {
        let sym = Z3_mk_string_symbol(ctx.get_z3_context(), cname.as_ptr()).unwrap();
        SymbolId(sym.as_ptr() as usize)
    }
}

/// Printable name for an interned symbol (declare/output paths only).
pub fn symbol_name_for_id(id: SymbolId) -> Option<String> {
    let ctx = Context::thread_local();
    unsafe {
        let sym = std::ptr::NonNull::new_unchecked(id.0 as *mut z3_sys::_Z3_symbol);
        let ptr = Z3_get_symbol_string(ctx.get_z3_context(), sym);
        if ptr.is_null() {
            return None;
        }
        Some(std::ffi::CStr::from_ptr(ptr).to_string_lossy().into_owned())
    }
}

pub fn is_forall(ast: &Dynamic) -> bool {
    quantifier_is_forall(ast)
}

pub fn is_exists(ast: &Dynamic) -> bool {
    quantifier_is_exists(ast)
}

fn quantifier_is_forall(ast: &Dynamic) -> bool {
    if ast.kind() != AstKind::Quantifier {
        return false;
    }
    unsafe {
        let z3 = ast.get_ctx().get_z3_context();
        Z3_is_quantifier_forall(z3, ast.get_z3_ast())
    }
}

fn quantifier_is_exists(ast: &Dynamic) -> bool {
    if ast.kind() != AstKind::Quantifier {
        return false;
    }
    unsafe {
        let z3 = ast.get_ctx().get_z3_context();
        !Z3_is_quantifier_forall(z3, ast.get_z3_ast())
    }
}

pub fn quantifier_body_bool(ast: &Dynamic) -> Option<Bool> {
    quantifier_body(ast)?.as_bool()
}

pub fn bound_var_index(ast: &Dynamic) -> Option<usize> {
    if ast.kind() != AstKind::Var {
        return None;
    }
    unsafe {
        let z3 = ast.get_ctx().get_z3_context();
        Some(Z3_get_index_value(z3, ast.get_z3_ast()) as usize)
    }
}

pub fn contains_bound_var_dyn(ast: &Dynamic) -> bool {
    if bound_var_index(ast).is_some() {
        return true;
    }
    if ast.kind() == AstKind::Quantifier {
        return false;
    }
    for ch in ast.children() {
        if contains_bound_var_dyn(&ch) {
            return true;
        }
    }
    false
}

pub fn de_bruijn_bound_name(bound_order: &[String], idx: usize) -> Option<String> {
    let pos = bound_order.len().checked_sub(1)?.checked_sub(idx)?;
    bound_order.get(pos).cloned()
}

pub fn de_bruijn_bound_symbol_id(bound_order: &[SymbolId], idx: usize) -> Option<SymbolId> {
    let pos = bound_order.len().checked_sub(1)?.checked_sub(idx)?;
    bound_order.get(pos).copied()
}

pub fn resolve_bound_or_free_name(ast: &Dynamic, bound_order: &[String]) -> Option<String> {
    if let Some(idx) = bound_var_index(ast) {
        return de_bruijn_bound_name(bound_order, idx);
    }
    crate::ast_build::symbol_name_dyn(ast)
}

pub fn substitute_bound_vars_dyn(ast: &Dynamic, bounds: &[Dynamic]) -> Dynamic {
    if let Some(idx) = bound_var_index(ast) {
        if let Some(repl) = bounds.get(idx) {
            return repl.clone();
        }
        return ast.clone();
    }
    if ast.kind() == AstKind::Quantifier {
        return ast.clone();
    }
    if ast.kind() == AstKind::App {
        let args: Vec<Dynamic> = (0..ast.num_children())
            .filter_map(|i| {
                ast.nth_child(i)
                    .map(|ch| substitute_bound_vars_dyn(&ch, bounds))
            })
            .collect();
        let refs: Vec<&dyn Ast> = args.iter().map(|a| a as &dyn Ast).collect();
        return rebuild_app(&ast.decl(), &refs);
    }
    ast.clone()
}

pub fn quantifier_body_deps(
    expr: &Dynamic,
    bound_order: &[String],
    qvars: &HashSet<String>,
) -> HashSet<String> {
    let mut out = HashSet::new();
    let mut stack = vec![expr.clone()];
    while let Some(node) = stack.pop() {
        if node.kind() == AstKind::Quantifier {
            continue;
        }
        if let Some(idx) = bound_var_index(&node) {
            if let Some(name) = de_bruijn_bound_name(bound_order, idx) {
                if qvars.contains(&name) {
                    out.insert(name);
                }
            }
            continue;
        }
        if let Some(name) = crate::ast_build::symbol_name_dyn(&node) {
            if qvars.contains(&name) {
                out.insert(name);
            }
            continue;
        }
        for ch in node.children() {
            stack.push(ch);
        }
    }
    out
}

pub fn rebuild_forall(bounds: &[Int], body: &Bool) -> Bool {
    use z3::ast::forall_const;
    let bound_refs: Vec<&dyn Ast> = bounds.iter().map(|i| i as &dyn Ast).collect();
    forall_const(&bound_refs, &[], body)
}

pub fn rebuild_exists(bounds: &[Int], body: &Bool) -> Bool {
    use z3::ast::exists_const;
    let bound_refs: Vec<&dyn Ast> = bounds.iter().map(|i| i as &dyn Ast).collect();
    exists_const(&bound_refs, &[], body)
}

/// Heuristic correction when SMT-LIB binds Bool symbols with the wrong sort.
pub fn quantifier_bound_sort_is_bool(_name: &str, z3_sk: SortKind) -> bool {
    z3_sk == SortKind::Bool
}

/// ``Var`` nodes and nullary ``App`` symbols whose Z3 sort is ``Bool``.
pub fn has_bool_sort_leaf_dyn(ast: &Dynamic) -> bool {
    crate::ast_build::iter_nodes_dyn(ast).any(|n| {
        n.get_sort().kind() == SortKind::Bool
            && matches!(n.kind(), AstKind::Var | AstKind::App if n.is_const())
    })
}

/// Debug-only: a direct ``Int`` arithmetic operand must not be Bool-sorted.
pub fn debug_assert_direct_int_operand(n: &Int) {
    debug_assert!(
        n.get_sort().kind() != SortKind::Bool,
        "Bool variable used as direct Int arithmetic operand: {n}"
    );
}

/// Bound constants in declaration order (outermost first), matching ``forall_const`` / Z3 text order.
pub fn quantifier_bounds(ast: &Dynamic) -> Vec<Dynamic> {
    if ast.kind() != AstKind::Quantifier {
        return Vec::new();
    }
    let ctx = ast.get_ctx();
    unsafe {
        let z3 = ctx.get_z3_context();
        let n = Z3_get_quantifier_num_bound(z3, ast.get_z3_ast()) as usize;
        let mut out = Vec::with_capacity(n);
        for i in 0..n {
            let sym = Z3_get_quantifier_bound_name(z3, ast.get_z3_ast(), i as u32).unwrap();
            let sort = Z3_get_quantifier_bound_sort(z3, ast.get_z3_ast(), i as u32).unwrap();
            let name = z3_symbol_to_string(ctx, sym);
            let bound: Dynamic = if quantifier_bound_sort_is_bool(&name, Z3_get_sort_kind(z3, sort)) {
                Dynamic::from_ast(&Bool::new_const(name.as_str()))
            } else {
                Dynamic::from_ast(&Int::new_const(name.as_str()))
            };
            out.push(bound);
        }
        out
    }
}

pub fn rebuild_forall_dyn(bounds: &[Dynamic], body: &Bool) -> Bool {
    use z3::ast::forall_const;
    let bound_refs: Vec<&dyn Ast> = bounds.iter().map(|d| d as &dyn Ast).collect();
    forall_const(&bound_refs, &[], body)
}

pub fn rebuild_exists_dyn(bounds: &[Dynamic], body: &Bool) -> Bool {
    use z3::ast::exists_const;
    let bound_refs: Vec<&dyn Ast> = bounds.iter().map(|d| d as &dyn Ast).collect();
    exists_const(&bound_refs, &[], body)
}

/// Bound constants indexed by de Bruijn level: ``bounds[i]`` replaces ``(:var i)`` (innermost at ``0``).
pub fn quantifier_bounds_de_bruijn(ast: &Dynamic) -> Vec<Dynamic> {
    let mut bounds = quantifier_bounds(ast);
    bounds.reverse();
    bounds
}

pub fn quantifier_bounds_int(ast: &Dynamic) -> Vec<Int> {
    quantifier_bound_names(ast)
        .into_iter()
        .map(|name| Int::new_const(name.as_str()))
        .collect()
}

pub fn rebuild_quantifier(is_forall: bool, bounds: &[Int], body: &Bool) -> Bool {
    if is_forall {
        rebuild_forall(bounds, body)
    } else {
        rebuild_exists(bounds, body)
    }
}

pub fn rebuild_quantifier_dyn(is_forall: bool, bounds: &[Dynamic], body: &Bool) -> Bool {
    if is_forall {
        rebuild_forall_dyn(bounds, body)
    } else {
        rebuild_exists_dyn(bounds, body)
    }
}

pub fn unwrap_zero_mod_eq(b: &Bool, field: i128) -> Option<Int> {
    if b.kind() != AstKind::App || b.decl().kind() != DeclKind::Eq || b.num_children() != 2 {
        return None;
    }
    let lhs = b.nth_child(0)?;
    let rhs = b.nth_child(1)?;
    let inner = if int_value_dyn(&rhs) == Some(0) {
        lhs
    } else if int_value_dyn(&lhs) == Some(0) {
        rhs
    } else {
        return None;
    };
    unwrap_mod_expr_dyn(&inner, field)
}

fn unwrap_mod_expr_dyn(ast: &Dynamic, field: i128) -> Option<Int> {
    if ast.kind() != AstKind::App
        || ast.decl().kind() != DeclKind::Mod
        || ast.num_children() != 2
    {
        return None;
    }
    let modulus = ast.nth_child(1)?;
    if int_value_dyn(&modulus) != Some(field) {
        return None;
    }
    ast.nth_child(0)?.as_int()
}

pub fn bool_decl_kind(b: &Bool) -> Option<DeclKind> {
    if b.kind() == AstKind::App {
        Some(b.decl().kind())
    } else {
        None
    }
}

pub fn bool_decl_name(b: &Bool) -> Option<String> {
    bool_decl_kind(b).map(|_| decl_name(&b.decl()))
}

pub fn bool_children(b: &Bool) -> Vec<Bool> {
    (0..b.num_children())
        .filter_map(|i| b.nth_child(i).and_then(|c| c.as_bool()))
        .collect()
}

pub fn and_parts(b: &Bool) -> Option<Vec<Bool>> {
    if b.kind() == AstKind::App && b.decl().kind() == DeclKind::And {
        return Some(bool_children(b));
    }
    None
}

pub fn or_parts(b: &Bool) -> Option<Vec<Bool>> {
    if b.kind() == AstKind::App && b.decl().kind() == DeclKind::Or {
        return Some(bool_children(b));
    }
    None
}

fn peel_annotation(b: &Bool) -> Bool {
    peel_annotation_opt(b).unwrap_or_else(|| b.clone())
}

/// Peel ``(! inner attr…)`` wrappers, returning ``None`` (no clone) when ``b``
/// carries no top-level annotation.
fn peel_annotation_opt(b: &Bool) -> Option<Bool> {
    if b.kind() == AstKind::App && decl_name(&b.decl()) == "!" && b.num_children() == 1 {
        if let Some(inner) = b.nth_child(0).and_then(|c| c.as_bool()) {
            return Some(peel_annotation_opt(&inner).unwrap_or(inner));
        }
    }
    None
}

pub fn flatten_and(children: Vec<Bool>) -> Bool {
    let mut flat = Vec::new();
    for c in children {
        if let Some(parts) = and_parts(&c) {
            flat.extend(parts);
        } else {
            flat.push(c);
        }
    }
    match flat.len() {
        0 => Bool::from_bool(true),
        1 => flat.into_iter().next().unwrap(),
        _ => Bool::and(&flat.iter().collect::<Vec<_>>()),
    }
}

pub fn flatten_or(children: Vec<Bool>) -> Bool {
    let mut flat = Vec::new();
    for c in children {
        if let Some(parts) = or_parts(&c) {
            flat.extend(parts);
        } else {
            flat.push(c);
        }
    }
    match flat.len() {
        0 => Bool::from_bool(false),
        1 => flat.into_iter().next().unwrap(),
        _ => Bool::or(&flat.iter().collect::<Vec<_>>()),
    }
}

/// Drop SMT-LIB ``(! inner attr…)`` wrappers (Z3 pattern / weight annotations).
pub fn strip_annotations(b: &Bool) -> Bool {
    peel_annotation(b)
}

/// Identity-preserving [`strip_annotations`]: ``None`` (no clone) when unannotated.
pub fn strip_annotations_opt(b: &Bool) -> Option<Bool> {
    peel_annotation_opt(b)
}

/// Recursively remove annotation wrappers, including inside quantifier bodies.
pub fn strip_annotations_deep(b: &Bool) -> Bool {
    if b.kind() == AstKind::App && decl_name(&b.decl()) == "!" && b.num_children() == 1 {
        if let Some(inner) = b.nth_child(0).and_then(|c| c.as_bool()) {
            return strip_annotations_deep(&inner);
        }
    }
    if b.kind() == AstKind::Quantifier {
        let ast = Dynamic::from_ast(b);
        let bounds = quantifier_bounds(&ast);
        let is_forall = quantifier_is_forall(&ast);
        let body = quantifier_body_bool(&ast).expect("quantifier body");
        let new_body = strip_annotations_deep(&peel_annotation(&body));
        return rebuild_quantifier_dyn(is_forall, &bounds, &new_body);
    }
    map_bool_children(b, &mut strip_annotations_deep)
}

/// Like :func:`or_parts`, but unwraps SMT-LIB ``(! inner attr)`` around the body.
pub fn or_body_parts(b: &Bool) -> Option<Vec<Bool>> {
    or_parts(&peel_annotation(b))
}

pub fn is_implies(b: &Bool) -> Option<(Bool, Bool)> {
    if b.kind() != AstKind::App || b.decl().kind() != DeclKind::Implies || b.num_children() != 2 {
        return None;
    }
    let a = b.nth_child(0)?.as_bool()?;
    let c = b.nth_child(1)?.as_bool()?;
    Some((a, c))
}

pub fn is_not(b: &Bool) -> Option<Bool> {
    if b.kind() != AstKind::App || b.decl().kind() != DeclKind::Not || b.num_children() != 1 {
        return None;
    }
    b.nth_child(0)?.as_bool()
}

pub fn is_ite(b: &Bool) -> Option<(Bool, Bool, Bool)> {
    if b.kind() != AstKind::App || b.decl().kind() != DeclKind::Ite || b.num_children() != 3 {
        return None;
    }
    let cond = b.nth_child(0)?.as_bool()?;
    let then_b = b.nth_child(1)?.as_bool()?;
    let else_b = b.nth_child(2)?.as_bool()?;
    Some((cond, then_b, else_b))
}

pub fn int_from_i128(v: i128) -> Int {
    if v >= i64::MIN as i128 && v <= i64::MAX as i128 {
        Int::from_i64(v as i64)
    } else {
        Int::from_str(&v.to_string()).expect("invalid int literal")
    }
}

pub fn map_bool_children(b: &Bool, f: &mut impl FnMut(&Bool) -> Bool) -> Bool {
    if b.kind() == AstKind::Quantifier {
        let ast = Dynamic::from_ast(b);
        let orig_names = quantifier_bound_names(&ast);
        let bounds = quantifier_bounds(&ast);
        let is_forall = quantifier_is_forall(&ast);
        let body = quantifier_body_bool(&ast).expect("quantifier body");
        let new_body = f(&body);
        let rebuilt = rebuild_quantifier_dyn(is_forall, &bounds, &new_body);
        debug_assert_eq!(
            quantifier_bound_names(&Dynamic::from_ast(&rebuilt)),
            orig_names,
            "quantifier rebuild changed bound variable order"
        );
        return rebuilt;
    }
    if b.kind() == AstKind::App {
        match b.decl().kind() {
            DeclKind::And => {
                let args: Vec<Bool> = bool_children(b).into_iter().map(|c| f(&c)).collect();
                return flatten_and(args);
            }
            DeclKind::Or => {
                let args: Vec<Bool> = bool_children(b).into_iter().map(|c| f(&c)).collect();
                return flatten_or(args);
            }
            DeclKind::Not if b.num_children() == 1 => {
                if let Some(inner) = is_not(b) {
                    return f(&inner).not();
                }
            }
            DeclKind::Implies if b.num_children() == 2 => {
                if let Some((a, c)) = is_implies(b) {
                    let na = f(&a);
                    let nc = f(&c);
                    return na.implies(&nc);
                }
            }
            DeclKind::Ite if b.num_children() == 3 => {
                if let Some((cond, then_b, else_b)) = is_ite(b) {
                    let nc = f(&cond);
                    let nt = f(&then_b);
                    let ne = f(&else_b);
                    return nc.ite(&nt, &ne);
                }
            }
            _ => {}
        }
    }
    b.clone()
}

/// Identity-preserving variant of [`map_bool_children`].
///
/// ``f`` returns ``None`` for an unchanged child. This function returns ``None``
/// when no descendant changed, so callers can skip rebuilding (and re-hashing)
/// large unchanged subtrees entirely.
pub fn map_bool_children_opt(
    b: &Bool,
    f: &mut impl FnMut(&Bool) -> Option<Bool>,
) -> Option<Bool> {
    if b.kind() == AstKind::Quantifier {
        let ast = Dynamic::from_ast(b);
        let bounds = quantifier_bounds(&ast);
        let is_forall = quantifier_is_forall(&ast);
        let body = quantifier_body_bool(&ast).expect("quantifier body");
        let new_body = f(&body)?;
        return Some(rebuild_quantifier_dyn(is_forall, &bounds, &new_body));
    }
    if b.kind() == AstKind::App {
        match b.decl().kind() {
            DeclKind::And | DeclKind::Or => {
                let is_and = b.decl().kind() == DeclKind::And;
                let children = bool_children(b);
                let mut changed = false;
                let args: Vec<Bool> = children
                    .iter()
                    .map(|c| match f(c) {
                        Some(nc) => {
                            changed = true;
                            nc
                        }
                        None => c.clone(),
                    })
                    .collect();
                if !changed {
                    return None;
                }
                return Some(if is_and {
                    flatten_and(args)
                } else {
                    flatten_or(args)
                });
            }
            DeclKind::Not if b.num_children() == 1 => {
                if let Some(inner) = is_not(b) {
                    return Some(f(&inner)?.not());
                }
            }
            DeclKind::Implies if b.num_children() == 2 => {
                if let Some((a, c)) = is_implies(b) {
                    let na = f(&a);
                    let nc = f(&c);
                    if na.is_none() && nc.is_none() {
                        return None;
                    }
                    let na = na.unwrap_or(a);
                    let nc = nc.unwrap_or(c);
                    return Some(na.implies(&nc));
                }
            }
            DeclKind::Ite if b.num_children() == 3 => {
                if let Some((cond, then_b, else_b)) = is_ite(b) {
                    let nc = f(&cond);
                    let nt = f(&then_b);
                    let ne = f(&else_b);
                    if nc.is_none() && nt.is_none() && ne.is_none() {
                        return None;
                    }
                    let nc = nc.unwrap_or(cond);
                    let nt = nt.unwrap_or(then_b);
                    let ne = ne.unwrap_or(else_b);
                    return Some(nc.ite(&nt, &ne));
                }
            }
            _ => {}
        }
    }
    None
}

pub fn rebuild_app(decl: &FuncDecl, args: &[&dyn Ast]) -> Dynamic {
    decl.apply(args)
}

unsafe fn z3_symbol_to_string(ctx: &Context, sym: Z3_symbol) -> String {
    let z3 = ctx.get_z3_context();
    let ptr = Z3_get_symbol_string(z3, sym);
    if !ptr.is_null() {
        return std::ffi::CStr::from_ptr(ptr).to_string_lossy().into_owned();
    }
    Z3_get_symbol_int(z3, sym).to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ParseCtx;

    fn has_z3() -> bool {
        std::process::Command::new("pkg-config")
            .args(["--exists", "z3"])
            .status()
            .map(|s| s.success())
            .unwrap_or(false)
    }

    #[test]
    fn free_int_symbols_basic() {
        if !has_z3() {
            return;
        }
        let mut ctx = ParseCtx::new();
        ctx.ingest_command("(declare-fun x () Int)").unwrap();
        let b = ctx
            .ingest_command("(assert (= x 1))")
            .unwrap()
            .unwrap();
        let free = free_int_symbols(&b);
        assert_eq!(free, HashSet::from(["x".to_string()]));
    }

    #[test]
    fn has_quantifier_detects_forall() {
        if !has_z3() {
            return;
        }
        let mut ctx = ParseCtx::new();
        let b = ctx
            .ingest_command("(assert (forall ((x Int)) (= x 0)))")
            .unwrap()
            .unwrap();
        assert!(has_quantifier(&b));
    }

    #[test]
    fn quantifier_rebuild_preserves_bound_names() {
        if !has_z3() {
            return;
        }
        let mut ctx = ParseCtx::new();
        let b = ctx
            .ingest_command(
                "(assert (forall ((x Int) (flag Bool)) (or (not flag) (= x 0))))",
            )
            .unwrap()
            .unwrap();
        let ast = Dynamic::from_ast(&b);
        let bounds = quantifier_bounds(&ast);
        let names: Vec<String> = bounds
            .iter()
            .filter_map(|d| crate::ast_build::symbol_name_dyn(d))
            .collect();
        assert_eq!(names, vec!["x", "flag"]);
        let body = quantifier_body_bool(&ast).expect("body");
        let rebuilt = rebuild_quantifier_dyn(true, &bounds, &body);
        let rebuilt_ast = Dynamic::from_ast(&rebuilt);
        assert_eq!(quantifier_bound_names(&rebuilt_ast), vec!["x", "flag"]);
        assert_eq!(rebuilt.to_string(), b.to_string());
    }

    #[test]
    fn map_bool_children_preserves_quantifier_body_symbols() {
        if !has_z3() {
            return;
        }
        let mut ctx = ParseCtx::new();
        let b = ctx
            .ingest_command(
                "(assert (forall ((x Int) (flag Bool))
                  (or (not flag)
                      (not (< (mod x 2013265921) 131072)))))",
            )
            .unwrap()
            .unwrap();
        let mapped = map_bool_children(&b, &mut |c| c.clone());
        let s = mapped.to_string();
        assert!(s.contains("(mod x"));
        assert!(!s.contains("(mod flag"));
    }

    #[test]
    fn mod_int_literal_string_reduces_beyond_i128() {
        let p = 2_013_265_921_i128;
        let huge = "32561662554329978067493305279605223446198353920";
        let reduced = mod_int_literal_string(huge, p).unwrap();
        assert_eq!(reduced, "1069547521");
    }
}
