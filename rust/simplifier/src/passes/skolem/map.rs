use std::collections::{HashMap, HashSet};

use smt2::ast_util::int_from_i128;
use smt2::wrap_mod_expr_int;
use z3::ast::{Bool, Dynamic, Int};

use super::ast_build::field_mod;
use super::types::SortKind;

pub struct SkolemMap {
    pub qvars: HashSet<String>,
    qvar_sorts: HashMap<String, SortKind>,
    pins: HashMap<String, Dynamic>,
    pub sources: HashMap<String, String>,
}

impl SkolemMap {
    pub fn new(qvars: &[(String, SortKind)]) -> Self {
        let mut qset = HashSet::new();
        let mut sorts = HashMap::new();
        for (name, sort) in qvars {
            qset.insert(name.clone());
            sorts.insert(name.clone(), *sort);
        }
        Self {
            qvars: qset,
            qvar_sorts: sorts,
            pins: HashMap::new(),
            sources: HashMap::new(),
        }
    }

    pub fn pin(&mut self, q: &str, expr: Dynamic, source: &str) -> bool {
        if !self.qvars.contains(q) || self.pins.contains_key(q) {
            return false;
        }
        self.pins.insert(q.to_string(), expr);
        self.sources.insert(q.to_string(), source.to_string());
        true
    }

    pub fn is_pinned(&self, q: &str) -> bool {
        self.pins.contains_key(q)
    }

    pub fn emit_disjuncts(&self) -> Vec<Bool> {
        let p = field_mod();
        let mut out = Vec::new();
        for (q, expr) in &self.pins {
            let sort = self.qvar_sorts.get(q).copied().unwrap_or(SortKind::Other);
            match sort {
                SortKind::Bool => {
                    let Some(rhs) = expr.as_bool() else {
                        continue;
                    };
                    out.push(Bool::new_const(q.as_str()).eq(&rhs).not());
                }
                _ => {
                    let rhs = if let Some(i) = expr.as_int() {
                        i
                    } else if let Some(b) = expr.as_bool() {
                        b.ite(&int_from_i128(1), &int_from_i128(0))
                    } else {
                        continue;
                    };
                    let rhs = if sort == SortKind::Int {
                        if let Some(m) = p {
                            wrap_mod_expr_int(rhs, m)
                        } else {
                            rhs
                        }
                    } else {
                        rhs
                    };
                    out.push(Int::new_const(q.as_str()).eq(&rhs).not());
                }
            }
        }
        out
    }
}