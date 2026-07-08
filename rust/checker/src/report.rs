use serde_json::{json, Map, Value};

#[derive(Clone, Debug, Default)]
pub struct Action {
    pub name: String,
    pub props: Map<String, Value>,
    pub actions: Vec<Action>,
    pub running_time: Option<f64>,
}

impl Action {
    pub fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
            ..Default::default()
        }
    }

    pub fn set(&mut self, key: &str, value: Value) {
        self.props.insert(key.to_string(), value);
    }

    pub fn get(&self, key: &str) -> Option<&Value> {
        self.props.get(key)
    }

    pub fn get_str(&self, key: &str) -> Option<&str> {
        self.get(key).and_then(|v| v.as_str())
    }

    pub fn push(&mut self, child: Action) {
        self.actions.push(child);
    }

    pub fn to_value(&self) -> Value {
        let mut m = self.props.clone();
        m.insert("name".to_string(), json!(self.name));
        if let Some(t) = self.running_time {
            m.insert("running_time".to_string(), json!(t));
        }
        m.insert(
            "actions".to_string(),
            Value::Array(self.actions.iter().map(Action::to_value).collect()),
        );
        Value::Object(m)
    }
}

pub fn classify_expected_vs_result(expected: &str, result: &str) -> &'static str {
    if result == "sat" || result == "unsat" {
        return if result == expected {
            "success"
        } else {
            "wrong"
        };
    }
    if let Some(reason) = result.strip_prefix("unknown-") {
        let r = reason.to_lowercase();
        if r.contains("timeout")
            || r.contains("time out")
            || r.contains("resource limit")
            || r.contains("resource limits")
        {
            return "timeout";
        }
    }
    "error"
}

pub fn log_expected_mismatch(expected: &str, result: &str) {
    let outcome = classify_expected_vs_result(expected, result);
    match outcome {
        "wrong" => eprintln!("expected {expected} but got {result}"),
        "timeout" => eprintln!("expected {expected}; solver timed out (result {result})"),
        "success" => {}
        _ => eprintln!("expected {expected} but got {result}"),
    }
}

pub fn dump_action(action: &Action) -> String {
    serde_json::to_string_pretty(&json!({ "__Action": action.to_value() })).unwrap()
}
