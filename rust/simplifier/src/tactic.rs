//! Split tactic names into pass base and dash suffix.

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TacticParts {
    pub base: String,
    pub suffix: Vec<String>,
}

impl TacticParts {
    pub fn raw(&self) -> String {
        if self.suffix.is_empty() {
            self.base.clone()
        } else {
            format!("{}-{}", self.base, self.suffix.join("-"))
        }
    }
}

pub fn split_tactic(raw: &str) -> TacticParts {
    if let Some((base, suffix)) = raw.split_once('-') {
        return TacticParts {
            base: base.to_string(),
            suffix: vec![suffix.to_string()],
        };
    }
    TacticParts {
        base: raw.to_string(),
        suffix: Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn z3_suffix() {
        assert_eq!(
            split_tactic("z3-propagate-values"),
            TacticParts {
                base: "z3".to_string(),
                suffix: vec!["propagate-values".to_string()],
            }
        );
    }

    #[test]
    fn plain_nnf() {
        assert_eq!(
            split_tactic("nnf"),
            TacticParts {
                base: "nnf".to_string(),
                suffix: Vec::new(),
            }
        );
    }
}
