use std::collections::{HashMap, HashSet};

use smt2::ast_util::{int_from_i128, symbol_id_from_name, symbol_name_for_id, SymbolId};
use smt2::wrap_mod_expr_int;
use z3::ast::{Bool, Dynamic, Int};

use super::ast_build::field_mod;
use super::types::SortKind;

pub struct SkolemMap {
    pub qvars: HashSet<SymbolId>,
    qvar_sorts: HashMap<SymbolId, SortKind>,
    pins: HashMap<SymbolId, Dynamic>,
    pub sources: HashMap<SymbolId, String>,
}

impl SkolemMap {
    pub fn new(qvars: &[(String, SortKind)]) -> Self {
        let mut qset = HashSet::new();
        let mut sorts = HashMap::new();
        for (name, sort) in qvars {
            let id = symbol_id_from_name(name);
            qset.insert(id);
            sorts.insert(id, *sort);
        }
        Self {
            qvars: qset,
            qvar_sorts: sorts,
            pins: HashMap::new(),
            sources: HashMap::new(),
        }
    }

    pub fn pin(&mut self, q: SymbolId, expr: Dynamic, source: &str) -> bool {
        if !self.qvars.contains(&q) || self.pins.contains_key(&q) {
            return false;
        }
        self.pins.insert(q, expr);
        self.sources.insert(q, source.to_string());
        true
    }

    pub fn is_pinned(&self, q: SymbolId) -> bool {
        self.pins.contains_key(&q)
    }

    pub fn emit_disjuncts(&self) -> Vec<Bool> {
        let p = field_mod();
        let mut pinned: Vec<(SymbolId, &Dynamic)> =
            self.pins.iter().map(|(q, e)| (*q, e)).collect();
        pinned.sort_by(|(a, _), (b, _)| {
            let na = symbol_name_for_id(*a).unwrap_or_default();
            let nb = symbol_name_for_id(*b).unwrap_or_default();
            na.cmp(&nb)
        });
        let mut out = Vec::new();
        for (q, expr) in pinned {
            let Some(name) = symbol_name_for_id(q) else {
                continue;
            };
            let sort = self.qvar_sorts.get(&q).copied().unwrap_or(SortKind::Other);
            match sort {
                SortKind::Bool => {
                    let Some(rhs) = expr.as_bool() else {
                        continue;
                    };
                    out.push(Bool::new_const(name.as_str()).eq(&rhs).not());
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
                    out.push(Int::new_const(name.as_str()).eq(&rhs).not());
                }
            }
        }
        out
    }
}

#[cfg(test)]
mod emit_tests {
    use super::*;
    use smt2::ast_util::symbol_id_from_name;

    #[test]
    fn emit_disjuncts_sorted_by_target_name() {
        std::env::set_var("SIMPLIFIER_FIELD_MOD", "2013265921");
        let mut m = SkolemMap::new(&[
            ("before-b@0".to_string(), SortKind::Int),
            ("before-a@0".to_string(), SortKind::Int),
        ]);
        m.pin(
            symbol_id_from_name("before-b@0"),
            Dynamic::from_ast(&Int::new_const("after-b@0")),
            "test",
        );
        m.pin(
            symbol_id_from_name("before-a@0"),
            Dynamic::from_ast(&Int::new_const("after-a@0")),
            "test",
        );
        let disjuncts = m.emit_disjuncts();
        assert_eq!(disjuncts.len(), 2);
        assert!(disjuncts[0].to_string().contains("before-a@0"));
        assert!(disjuncts[1].to_string().contains("before-b@0"));
    }
}
