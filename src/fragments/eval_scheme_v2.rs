//! Eval scheme fragment definitions (v2 arrow-calculus kernel, ADR-0052).
//!
//! The v2 equivalent of [`EvalSchemeDef`](super::eval_scheme::EvalSchemeDef).
//! Holds an arrow-calculus [`SchemeV2`](crate::SchemeV2) instead of a v1
//! [`Scheme`](crate::Scheme). Used by v2 engines that consume v2 schemes
//! directly (without v1→v2 lowering at runtime).

use serde::{Deserialize, Serialize};

use crate::fragment::Fragment;
use crate::scheme_v2::SchemeV2;

/// A mapping from an AST node kind to its evaluation [`SchemeV2`].
///
/// The v2 equivalent of [`EvalSchemeDef`](super::eval_scheme::EvalSchemeDef).
/// Holds an arrow-calculus [`SchemeV2`] instead of a v1 [`Scheme`](crate::Scheme).
/// Used by v2 engines that consume v2 schemes directly (without v1→v2
/// lowering at runtime).
///
/// Identity key: `node_kind` (same as [`EvalSchemeDef`]). Collision without
/// `replaces` is an error.
///
/// [`EvalSchemeDef`]: super::eval_scheme::EvalSchemeDef
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct EvalSchemeDefV2 {
    /// Stable identifier (e.g. `"eval.binary.add"`).
    pub id: String,
    /// The AST node kind this scheme evaluates.
    pub node_kind: String,
    /// The v2 evaluation scheme describing *what* to evaluate.
    pub scheme: SchemeV2,
    /// ids this fragment declares it replaces.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub replaces: Vec<String>,
    /// ids this fragment hard-requires.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub requires: Vec<String>,
}

impl EvalSchemeDefV2 {
    /// Create a new v2 eval scheme definition.
    pub fn new(id: impl Into<String>, node_kind: impl Into<String>, scheme: SchemeV2) -> Self {
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

impl Fragment for EvalSchemeDefV2 {
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
        let def = EvalSchemeDefV2::new(
            "eval.binary.add",
            "binary.add",
            SchemeV2::arr_native(
                "add",
                vec![
                    SchemeV2::arr_native_lit("proj_child", vec![], Value::from(0u64)),
                    SchemeV2::arr_native_lit("proj_child", vec![], Value::from(1u64)),
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
        let def = EvalSchemeDefV2::new(
            "eval.lit",
            "lit",
            SchemeV2::arr_native_lit("const", vec![], Value::from(42)),
        );
        let j = serde_json::to_string(&def).unwrap();
        let back: EvalSchemeDefV2 = serde_json::from_str(&j).unwrap();
        assert_eq!(def, back);
    }

    #[test]
    fn equality() {
        let a = EvalSchemeDefV2::new("a", "k", SchemeV2::arr_native("id", vec![]));
        let b = EvalSchemeDefV2::new("a", "k", SchemeV2::arr_native("id", vec![]));
        assert_eq!(a, b);
    }
}
