//! Constant folding on Z3 AST (evaluator pass).

use smt2::ast_util::{
    debug_assert_direct_int_operand, int_from_i128, int_value, int_value_dyn, rebuild_app,
};
use z3::ast::{Ast, AstKind, Bool, Dynamic, Int};
use z3::DeclKind;

pub fn fold_constants_fixpoint(b: &Bool, field_mod: Option<u64>, max_iters: usize) -> Bool {
    let mut cur = b.clone();
    for _ in 0..max_iters {
        let next = fold_bool(&cur, field_mod);
        if next.ast_eq(&cur) {
            break;
        }
        cur = next;
    }
    cur
}

fn fold_bool(b: &Bool, field_mod: Option<u64>) -> Bool {
    if b.kind() == AstKind::Quantifier {
        return b.clone();
    }
    if let Some(v) = b.as_bool() {
        return Bool::from_bool(v);
    }
    if b.kind() == AstKind::App {
        let kind = b.decl().kind();
        match kind {
            DeclKind::Not if b.num_children() == 1 => {
                if let Some(inner) = b.nth_child(0).and_then(|c| c.as_bool()) {
                    let folded = fold_bool(&inner, field_mod);
                    if let Some(v) = folded.as_bool() {
                        return Bool::from_bool(!v);
                    }
                    return folded.not();
                }
            }
            DeclKind::And | DeclKind::Or => {
                let is_and = kind == DeclKind::And;
                let mut consts = Vec::new();
                let mut symbolic = Vec::new();
                for i in 0..b.num_children() {
                    if let Some(cb) = b.nth_child(i).and_then(|c| c.as_bool()) {
                        let folded = fold_bool(&cb, field_mod);
                        if let Some(v) = folded.as_bool() {
                            consts.push(v);
                        } else {
                            symbolic.push(folded);
                        }
                    }
                }
                if consts.is_empty() {
                    return b.clone();
                }
                let folded = if is_and {
                    consts.iter().all(|&x| x)
                } else {
                    consts.iter().any(|&x| x)
                };
                if is_and && !folded {
                    return Bool::from_bool(false);
                }
                if !is_and && folded {
                    return Bool::from_bool(true);
                }
                if symbolic.is_empty() {
                    return Bool::from_bool(folded);
                }
                let refs: Vec<&Bool> = symbolic.iter().collect();
                return if is_and {
                    Bool::and(&refs)
                } else {
                    Bool::or(&refs)
                };
            }
            DeclKind::Eq if b.num_children() == 2 => {
                let a = b.nth_child(0);
                let c = b.nth_child(1);
                if let (Some(a), Some(c)) = (a, c) {
                    if let (Some(ab), Some(cb)) = (a.as_bool(), c.as_bool()) {
                        if let (Some(x), Some(y)) = (ab.as_bool(), cb.as_bool()) {
                            return Bool::from_bool(x == y);
                        }
                    }
                    if let (Some(ai), Some(ci)) = (a.as_int(), c.as_int()) {
                        if let (Some(x), Some(y)) = (int_value(&ai), int_value(&ci)) {
                            return Bool::from_bool(x == y);
                        }
                    }
                }
            }
            DeclKind::Distinct if b.num_children() == 2 => {
                let a = b.nth_child(0);
                let c = b.nth_child(1);
                if let (Some(a), Some(c)) = (a, c) {
                    if let (Some(ai), Some(ci)) = (a.as_int(), c.as_int()) {
                        if let (Some(x), Some(y)) = (int_value(&ai), int_value(&ci)) {
                            return Bool::from_bool(x != y);
                        }
                    }
                }
            }
            DeclKind::Ite if b.num_children() == 3 => {
                if let Some(cond) = b.nth_child(0).and_then(|c| c.as_bool()) {
                    if let Some(c) = cond.as_bool() {
                        let branch = if c {
                            b.nth_child(1).and_then(|c| c.as_bool())
                        } else {
                            b.nth_child(2).and_then(|c| c.as_bool())
                        };
                        if let Some(branch) = branch {
                            return fold_bool(&branch, field_mod);
                        }
                    }
                }
            }
            _ => {}
        }
    }
    map_bool_children_default(b, field_mod)
}

fn map_bool_children_default(b: &Bool, field_mod: Option<u64>) -> Bool {
    if b.kind() != AstKind::App {
        return b.clone();
    }
    if b.decl().kind() == DeclKind::Not && b.num_children() == 1 {
        if let Some(inner) = b.nth_child(0).and_then(|c| c.as_bool()) {
            return fold_bool(&inner, field_mod).not();
        }
    }
    let kids: Vec<Dynamic> = (0..b.num_children())
        .filter_map(|i| b.nth_child(i))
        .map(|ch| fold_dynamic(&ch, field_mod))
        .collect();
    let refs: Vec<&dyn Ast> = kids.iter().map(|k| k as &dyn Ast).collect();
    rebuild_app(&b.decl(), &refs).as_bool().unwrap_or_else(|| b.clone())
}

fn fold_dynamic(ast: &Dynamic, field_mod: Option<u64>) -> Dynamic {
    if let Some(b) = ast.as_bool() {
        return Dynamic::from_ast(&fold_bool(&b, field_mod));
    }
    if let Some(i) = ast.as_int() {
        return Dynamic::from_ast(&fold_int(&i, field_mod));
    }
    if ast.kind() != AstKind::App {
        return ast.clone();
    }
    let kids: Vec<Dynamic> = ast
        .children()
        .into_iter()
        .map(|ch| fold_dynamic(&ch, field_mod))
        .collect();
    let refs: Vec<&dyn Ast> = kids.iter().map(|k| k as &dyn Ast).collect();
    rebuild_app(&ast.decl(), &refs)
}

fn fold_int(e: &Int, field_mod: Option<u64>) -> Int {
    if int_value(e).is_some() {
        return e.clone();
    }
    if e.kind() != AstKind::App {
        return e.clone();
    }
    let p = field_mod.map(|m| m as i128);
    match e.decl().kind() {
        DeclKind::Add => return fold_nary_int(e, |vals| vals.iter().sum(), p),
        DeclKind::Mul => return fold_nary_int(e, |vals| vals.iter().product(), p),
        DeclKind::Uminus if e.num_children() == 1 => {
            if let Some(v) = int_value_dyn(&e.nth_child(0).unwrap()) {
                return int_atom(-v, p);
            }
        }
        DeclKind::Sub if e.num_children() == 2 => {
            let a = int_value_dyn(&e.nth_child(0).unwrap());
            let b = int_value_dyn(&e.nth_child(1).unwrap());
            if let (Some(x), Some(y)) = (a, b) {
                return int_atom(x - y, p);
            }
        }
        DeclKind::Div if e.num_children() == 2 => {
            let a = int_value_dyn(&e.nth_child(0).unwrap());
            let b = int_value_dyn(&e.nth_child(1).unwrap());
            if let (Some(x), Some(y)) = (a, b) {
                if y != 0 {
                    return int_atom(x / y, p);
                }
            }
        }
        DeclKind::Mod if e.num_children() == 2 => {
            let a = int_value_dyn(&e.nth_child(0).unwrap());
            let b = int_value_dyn(&e.nth_child(1).unwrap());
            if let (Some(x), Some(y)) = (a, b) {
                if y != 0 {
                    return int_atom(x % y, p);
                }
            }
        }
        _ => {}
    }
    let kids: Vec<Dynamic> = (0..e.num_children())
        .filter_map(|i| e.nth_child(i))
        .map(|ch| fold_dynamic(&ch, field_mod))
        .collect();
    let refs: Vec<&dyn Ast> = kids.iter().map(|k| k as &dyn Ast).collect();
    rebuild_app(&e.decl(), &refs)
        .as_int()
        .unwrap_or_else(|| e.clone())
}

fn fold_nary_int(ast: &Int, f: fn(&[i128]) -> i128, field_mod: Option<i128>) -> Int {
    let is_mul = ast.decl().kind() == DeclKind::Mul;
    let mut int_acc = Vec::new();
    let mut symbolic = Vec::new();
    for i in 0..ast.num_children() {
        let Some(ch) = ast.nth_child(i) else { continue };
        if let Some(v) = int_value_dyn(&ch) {
            int_acc.push(v);
        } else if let Some(i) = ch.as_int() {
            symbolic.push(fold_int(&i, field_mod.map(|m| m as u64)));
        }
    }
    if int_acc.is_empty() {
        return ast.clone();
    }
    let folded = int_atom(f(&int_acc), field_mod);
    if symbolic.is_empty() {
        return folded;
    }
    let mut args: Vec<Int> = symbolic;
    let identity = if is_mul { 1 } else { 0 };
    if int_value(&folded) != Some(identity) {
        args.push(folded);
    }
    if args.len() == 1 {
        return args.into_iter().next().unwrap();
    }
    let refs: Vec<&Int> = args.iter().collect();
    for a in &args {
        debug_assert_direct_int_operand(a);
    }
    if is_mul {
        Int::mul(&refs)
    } else {
        Int::add(&refs)
    }
}

fn int_atom(v: i128, field_mod: Option<i128>) -> Int {
    let v = match field_mod {
        Some(m) if m > 0 => ((v % m) + m) % m,
        _ => v,
    };
    int_from_i128(v)
}
