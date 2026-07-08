use std::collections::BTreeMap;

use serde_json::Value;
use z3::ast::{Bool, Int};
use z3::{Model, SortKind};

pub fn nice_model(model: &Model) -> BTreeMap<String, Value> {
    let mut out = BTreeMap::new();
    for decl in model.iter() {
        if decl.arity() != 0 {
            continue;
        }
        if decl.range() == SortKind::Array {
            continue;
        }
        let name = decl.name().to_string();
        match decl.range() {
            SortKind::Bool => {
                let sym = Bool::new_const(decl.name());
                if let Some(v) = model.get_const_interp(&sym).and_then(|b| b.as_bool()) {
                    out.insert(name, Value::Bool(v));
                }
            }
            SortKind::Int => {
                let sym = Int::new_const(decl.name());
                if let Some(v) = model.get_const_interp(&sym) {
                    if let Some(json) = int_to_json(&v) {
                        out.insert(name, json);
                    }
                }
            }
            _ => {}
        }
    }
    out
}

fn int_to_json(i: &Int) -> Option<Value> {
    let s = i.to_string();
    if let Ok(n) = s.parse::<i64>() {
        return Some(Value::Number(n.into()));
    }
    s.parse::<u64>().ok().map(|n| Value::Number(n.into()))
}
