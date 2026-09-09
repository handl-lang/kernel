//! Eval scheme fragment definitions (arrow-calculus kernel, ADR-0052).

use serde::{Deserialize, Serialize};

use crate::fragment::Fragment;
use crate::term::Term;

/// A mapping from an AST node kind to its evaluation [`Term`].
///
/// Holds an arrow-calculus [`Term`] (the six arrow primitives). Used by
/// engines that consume schemes directly.
///
/// Identity key: `node_kind` (see ADR-0044 §5). Collision without `replaces`
/// is an error.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct EvalSchemeDef {
    /// Stable identifier (e.g. `"eval.binary.add"`).
    pub id: String,
    /// The AST node kind this scheme evaluates.
    pub node_kind: String,
    /// The evaluation scheme describing *what* to evaluate.
    pub scheme: Term,
    /// ids this fragment declares it replaces.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub replaces: Vec<String>,
    /// ids this fragment hard-requires.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub requires: Vec<String>,
}

impl EvalSchemeDef {
    /// Create a new eval scheme definition.
    pub fn new(id: impl Into<String>, node_kind: impl Into<String>, scheme: Term) -> Self {
        Self {
            id: id.into(),
            node_kind: node_kind.into(),
            scheme,
            replaces: Vec::new(),
            requires: Vec::new(),
        }
    }

    /// Attach a `replaces` list.
    pub fn with_replaces(mut self, replaces: Vec<String>) -> Self {
        self.replaces = replaces;
        self
    }

    /// Attach a `requires` list.
    pub fn with_requires(mut self, requires: Vec<String>) -> Self {
        self.requires = requires;
        self
    }
}

impl Fragment for EvalSchemeDef {
    fn id(&self) -> &str {
        &self.id
    }
    fn replaces(&self) -> &[String] {
        &self.replaces
    }
    fn requires(&self) -> &[String] {
        &self.requires
    }
    fn identity_key(&self) -> String {
        self.node_kind.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::Value;

    #[test]
    fn construct_and_accessors() {
        let def = EvalSchemeDef::new(
            "eval.binary.add",
            "binary.add",
            Term::arr_native(
                "add",
                vec![
                    Term::arr_native_lit("proj_child", vec![], Value::from(0u64)),
                    Term::arr_native_lit("proj_child", vec![], Value::from(1u64)),
                ],
            ),
        )
        .with_replaces(vec!["eval.add.old".into()])
        .with_requires(vec!["token.plus".into()]);
        assert_eq!(def.id(), "eval.binary.add");
        assert_eq!(def.node_kind, "binary.add");
        assert_eq!(def.replaces(), &["eval.add.old".to_string()]);
        assert_eq!(def.requires(), &["token.plus".to_string()]);
        assert_eq!(def.identity_key(), "binary.add");
    }

    #[test]
    fn serde_roundtrip() {
        let def = EvalSchemeDef::new(
            "eval.lit",
            "lit",
            Term::arr_native_lit("const", vec![], Value::from(42)),
        );
        let j = serde_json::to_string(&def).unwrap();
        let back: EvalSchemeDef = serde_json::from_str(&j).unwrap();
        assert_eq!(def, back);
    }

    #[test]
    fn equality() {
        let a = EvalSchemeDef::new("a", "k", Term::arr_native("id", vec![]));
        let b = EvalSchemeDef::new("a", "k", Term::arr_native("id", vec![]));
        assert_eq!(a, b);
    }
}
