//! AST shape fragment definitions.

use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::fragment::Fragment;

/// A definition of an AST node kind and its payload shape.
///
/// Identity key: `node_kind` (see ADR-0044 §5). The `payload_schema` is a
/// `serde_json::Value` describing the payload shape (e.g. a JSON Schema
/// fragment), kept as opaque data so the crate stays engine-agnostic.
///
/// AST shape declarations are **structural facts** ("this node kind exists
/// with this payload shape"), not behavioral definitions: two emitters
/// declaring the shape for `binary.add` are agreeing it exists, not
/// conflicting. Merge therefore uses **union (idempotent)** semantics —
/// merging a shape whose `node_kind` already exists is a no-op (the first
/// declaration is kept), not an error.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct AstShapeDef {
    /// Stable identifier (e.g. `"ast.binary.add"`).
    pub id: String,
    /// The AST node kind this shape describes.
    pub node_kind: String,
    /// An opaque description of the payload shape (e.g. a JSON Schema).
    #[serde(default = "Value::default", skip_serializing_if = "is_payload_null")]
    pub payload_schema: Value,
    /// ids this fragment declares it replaces.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub replaces: Vec<String>,
    /// ids this fragment hard-requires.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub requires: Vec<String>,
}

fn is_payload_null(v: &Value) -> bool {
    v == &Value::Null
}

impl AstShapeDef {
    /// Create a new AST shape definition with a null payload schema.
    pub fn new(id: impl Into<String>, node_kind: impl Into<String>) -> Self {
        Self {
            id: id.into(),
            node_kind: node_kind.into(),
            payload_schema: Value::Null,
            replaces: Vec::new(),
            requires: Vec::new(),
        }
    }

    /// Attach a payload schema.
    pub fn with_payload_schema(mut self, schema: Value) -> Self {
        self.payload_schema = schema;
        self
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

impl Fragment for AstShapeDef {
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
    /// AST shape declarations merge idempotently (union semantics): two
    /// emitters declaring the shape for the same node kind are agreeing it
    /// exists, not conflicting, so the duplicate is silently dropped (first
    /// wins).
    const UNION: bool = true;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn construct_and_accessors() {
        let def = AstShapeDef::new("ast.binary.add", "binary.add")
            .with_payload_schema(serde_json::json!({"type": "object"}))
            .with_replaces(vec!["ast.add.old".into()])
            .with_requires(vec!["token.plus".into()]);
        assert_eq!(def.id(), "ast.binary.add");
        assert_eq!(def.node_kind, "binary.add");
        assert_eq!(def.payload_schema, serde_json::json!({"type": "object"}));
        assert_eq!(def.replaces(), &["ast.add.old".to_string()]);
        assert_eq!(def.requires(), &["token.plus".to_string()]);
        assert_eq!(def.identity_key(), "binary.add");
    }

    #[test]
    fn serde_roundtrip() {
        let def = AstShapeDef::new("ast.lit", "lit")
            .with_payload_schema(serde_json::json!({"type": "number"}));
        let j = serde_json::to_string(&def).unwrap();
        let back: AstShapeDef = serde_json::from_str(&j).unwrap();
        assert_eq!(def, back);
    }

    #[test]
    fn serde_skips_null_payload() {
        let def = AstShapeDef::new("ast.lit", "lit");
        let j = serde_json::to_string(&def).unwrap();
        assert!(!j.contains("payload_schema"));
    }

    #[test]
    fn equality() {
        let a = AstShapeDef::new("a", "k");
        let b = AstShapeDef::new("a", "k");
        assert_eq!(a, b);
    }

    #[test]
    fn is_union_type() {
        // AST shape declarations are structural facts, so they merge
        // idempotently rather than colliding.
        assert!(AstShapeDef::UNION);
    }

    #[test]
    fn merge_same_node_kind_is_idempotent() {
        use crate::FragmentSet;
        let mut set: FragmentSet<AstShapeDef> = FragmentSet::new();
        let first = AstShapeDef::new("ast.binary.add", "binary.add")
            .with_payload_schema(serde_json::json!({"first": true}));
        let second = AstShapeDef::new("ast.binary.add.dup", "binary.add")
            .with_payload_schema(serde_json::json!({"first": false}));
        set.merge(first.clone()).expect("first merge ok");
        // Merging a second shape for the same node_kind is a no-op (union),
        // NOT a collision — even though the ids differ.
        set.merge(second).expect("duplicate merge is idempotent");
        assert_eq!(set.len(), 1);
        // The first declaration is kept.
        let kept = set.get_by_identity("binary.add").unwrap();
        assert_eq!(kept.id(), "ast.binary.add");
        assert_eq!(kept.payload_schema, serde_json::json!({"first": true}));
    }
}
