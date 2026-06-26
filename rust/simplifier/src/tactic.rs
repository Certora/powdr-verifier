//! Split tactic names like Python ``_split_tactic``.

pub fn split_tactic(raw: &str) -> (String, Vec<String>) {
    if let Some(inner) = raw.strip_prefix("r#") {
        if let Some((base, suffix)) = inner.split_once('-') {
            return (format!("r#{base}"), vec![suffix.to_string()]);
        }
        return (format!("r#{inner}"), Vec::new());
    }
    if let Some((base, suffix)) = raw.split_once('-') {
        return (base.to_string(), vec![suffix.to_string()]);
    }
    (raw.to_string(), Vec::new())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rust_z3_suffix() {
        assert_eq!(
            split_tactic("r#z3-propagate-values"),
            ("r#z3".to_string(), vec!["propagate-values".to_string()])
        );
    }

    #[test]
    fn plain_nnf() {
        assert_eq!(split_tactic("nnf"), ("nnf".to_string(), Vec::new()));
    }
}
