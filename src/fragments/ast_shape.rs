//! AST shape fragment definitions.

use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::fragment::Fragment;

/// A specification for a single child of a desugar replacement node
/// (ADR-0053 §7 — data-driven desugar pass).
///
/// A child is either [`AstDesugarChild::Keep`] (reuse the original node's
/// child at the given index, remapped into the output arena),
/// [`AstDesugarChild::KeepPath`] (navigate through descendant children by
/// index path, e.g. `[0, 0]` takes child 0's child 0), or
/// [`AstDesugarChild::Create`] (allocate a fresh node, optionally with its
/// own children — the rewrite is recursive).
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum AstDesugarChild {
    /// Reuse the original node's child at the given index.
    Keep(usize),
    /// Reuse a descendant node by navigating through children by index path.
    /// `KeepPath([0, 0])` takes the original node's child 0, then that
    /// node's child 0, and remaps the final arena index into the output
    /// arena. Used by ADR-0058 to unwrap bracket-computed-key `array`
    /// wrappers during desugar.
    KeepPath(Vec<usize>),
    /// Allocate a new node with the given `kind`, optional `payload`, and
    /// nested `children` (themselves [`AstDesugarChild`]s).
    Create {
        /// The AST node kind of the created node.
        kind: String,
        /// Optional payload for the created node.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        payload: Option<Value>,
        /// Nested children of the created node.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        children: Vec<AstDesugarChild>,
    },
    /// Keep all children from the given index onward (ADR-0060). Unlike
    /// `Keep(i)` which keeps a single child, `KeepRest(N)` expands to all
    /// children from index `N` to the end, each remapped into the output
    /// arena. Used by desugar rules that need to preserve a variable-length
    /// tail of children (e.g. `json{...}(args)` → `json` node with all
    /// original children kept).
    KeepRest(usize),
}

/// A condition that guards whether a desugar rule applies (ADR-0058).
///
/// When present on an [`AstDesugarRule`], the pass only rewrites nodes whose
/// child at `child_index` has the AST node kind `child_kind`. Nodes that
/// don't match pass through unchanged. This lets a single shape carry a
/// desugar rule that only fires for a specific child variant (e.g. only
/// `entry` nodes whose key child is an `array`).
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct AstDesugarCondition {
    /// The index into the original node's `children` array to test.
    pub child_index: usize,
    /// The AST node kind the child must have for the rule to fire.
    pub child_kind: String,
}

/// A data-driven desugar rule (ADR-0053 §7).
///
/// Specifies the `target_kind` to rewrite a node into, plus the list of
/// [`AstDesugarChild`]s that become the rewritten node's children. Attached
/// to an [`AstShapeDef`] via [`AstShapeDef::with_desugar`].
///
/// An optional `when` condition (ADR-0058) gates the rewrite: the rule only
/// fires if the original node's child at `when.child_index` has kind
/// `when.child_kind`. Without `when`, the rule fires unconditionally (the
/// ADR-0053 behavior).
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct AstDesugarRule {
    /// The AST node kind to rewrite into.
    pub target_kind: String,
    /// The children of the rewritten node.
    pub children: Vec<AstDesugarChild>,
    /// Optional condition gating the rewrite (ADR-0058). When present, the
    /// rule only fires if the original node's child at `child_index` has
    /// kind `child_kind`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub when: Option<AstDesugarCondition>,
}

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
    /// Optional data-driven desugar rule (ADR-0053 §7). When present, the
    /// desugar pass rewrites nodes of this kind into `desugar.target_kind`
    /// with the specified children before evaluation.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub desugar: Option<AstDesugarRule>,
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
            desugar: None,
            replaces: Vec::new(),
            requires: Vec::new(),
        }
    }

    /// Attach a payload schema.
    pub fn with_payload_schema(mut self, schema: Value) -> Self {
        self.payload_schema = schema;
        self
    }

    /// Attach a data-driven desugar rule (ADR-0053 §7).
    pub fn with_desugar(mut self, rule: AstDesugarRule) -> Self {
        self.desugar = Some(rule);
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
