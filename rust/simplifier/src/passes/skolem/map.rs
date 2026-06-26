use std::collections::{HashMap, HashSet};

use smt2::Term;

use super::term_util::{field_mod, list, wrap_mod_expr};
use super::types::SortKind;

pub struct SkolemMap {
    pub qvars: HashSet<String>,
    qvar_sorts: HashMap<String, SortKind>,
    pins: HashMap<String, Term>,
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

    pub fn pin(&mut self, q: &str, expr: Term, source: &str) -> bool {
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

    pub fn emit_disjuncts(&self) -> Vec<Term> {
        let p = field_mod();
        let mut out = Vec::new();
        for (q, expr) in &self.pins {
            let sort = self.qvar_sorts.get(q).copied().unwrap_or(SortKind::Other);
            let rhs = if sort == SortKind::Int {
                if let Some(m) = p {
                    wrap_mod_expr(expr.clone(), m)
                } else {
                    expr.clone()
                }
            } else {
                expr.clone()
            };
            let qterm = Term::Atom(q.clone());
            out.push(list("not", vec![list("=", vec![qterm, rhs])]));
        }
        out
    }
}