//! Grammar row fragment definitions.

use serde::{Deserialize, Serialize};

use crate::fragment::Fragment;

/// The position a grammar rule occupies in a Pratt parser.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum GrammarPosition {
    /// A prefix (null-denotation) rule: `prefix(token) -> ast`.
    Prefix,
    /// An infix (left-denotation) rule: `left infix(token) -> ast`.
    Infix,
}

impl GrammarPosition {
    /// A stable string representation used in identity keys.
    pub fn as_str(self) -> &'static str {
        match self {
            GrammarPosition::Prefix => "prefix",
            GrammarPosition::Infix => "infix",
        }
    }
}

/// A reference to an [`AstShapeDef`](crate::AstShapeDef) describing the child
/// shape a grammar row produces.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct AstShapeRef {
    /// The node kind this row produces (keyed to `AstShapeDef::node_kind`).
    pub node_kind: String,
    /// The number of children the produced node expects.
    pub arity: usize,
}

impl AstShapeRef {
    /// Create a new shape reference.
    pub fn new(node_kind: impl Into<String>, arity: usize) -> Self {
        Self {
            node_kind: node_kind.into(),
            arity,
        }
    }
}

/// One row of a Pratt grammar table.
///
/// Identity key: `(token, position)` (see ADR-0044 §5). Carries enough data
/// for a Pratt engine to read: prefix/infix position, binding powers, and the
/// child shape to produce.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct GrammarRow {
    /// Stable identifier (e.g. `"grammar.add.infix"`).
    pub id: String,
    /// The token this row matches.
    pub token: String,
    /// Whether this is a prefix or infix rule.
    pub position: GrammarPosition,
    /// Binding powers `(left, right)` for precedence handling.
    ///
    /// For a prefix rule, `left` is the right binding power of the prefix.
    /// For an infix rule, `left` is the left binding power and `right` the
    /// right binding power.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub binding_power: Option<(u8, u8)>,
    /// The child shape this row produces.
    pub child_shape: AstShapeRef,
    /// ids this fragment declares it replaces.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub replaces: Vec<String>,
    /// ids this fragment hard-requires.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub requires: Vec<String>,
}

impl GrammarRow {
    /// Create a new grammar row.
    pub fn new(
        id: impl Into<String>,
        token: impl Into<String>,
        position: GrammarPosition,
        child_shape: AstShapeRef,
    ) -> Self {
        Self {
            id: id.into(),
            token: token.into(),
            position,
            binding_power: None,
            child_shape,
            replaces: Vec::new(),
            requires: Vec::new(),
        }
    }

    /// Attach binding powers.
    pub fn with_binding_power(mut self, left: u8, right: u8) -> Self {
        self.binding_power = Some((left, right));
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

    /// The identity key for this row: `token@position`.
    pub fn identity_key_str(&self) -> String {
        format!("{}@{}", self.token, self.position.as_str())
    }
}

impl Fragment for GrammarRow {
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
        self.identity_key_str()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn construct_and_accessors() {
        let row = GrammarRow::new(
            "grammar.add.infix",
            "token.plus",
            GrammarPosition::Infix,
            AstShapeRef::new("binary.add", 2),
        )
        .with_binding_power(10, 11)
        .with_replaces(vec!["grammar.add.old".into()])
        .with_requires(vec!["token.plus".into()]);
        assert_eq!(row.id(), "grammar.add.infix");
        assert_eq!(row.token, "token.plus");
        assert_eq!(row.position, GrammarPosition::Infix);
        assert_eq!(row.binding_power, Some((10, 11)));
        assert_eq!(row.child_shape.arity, 2);
        assert_eq!(row.replaces(), &["grammar.add.old".to_string()]);
        assert_eq!(row.requires(), &["token.plus".to_string()]);
        assert_eq!(row.identity_key(), "token.plus@infix");
    }

    #[test]
    fn prefix_identity_key() {
        let row = GrammarRow::new(
            "grammar.neg",
            "token.minus",
            GrammarPosition::Prefix,
            AstShapeRef::new("unary.neg", 1),
        );
        assert_eq!(row.identity_key(), "token.minus@prefix");
    }

    #[test]
    fn serde_roundtrip() {
        let row = GrammarRow::new(
            "grammar.mul",
            "token.star",
            GrammarPosition::Infix,
            AstShapeRef::new("binary.mul", 2),
        )
        .with_binding_power(20, 21)
        .with_requires(vec!["token.star".into()]);
        let j = serde_json::to_string(&row).unwrap();
        let back: GrammarRow = serde_json::from_str(&j).unwrap();
        assert_eq!(row, back);
    }

    #[test]
    fn equality() {
        let a = GrammarRow::new("a", "t", GrammarPosition::Infix, AstShapeRef::new("k", 1));
        let b = GrammarRow::new("a", "t", GrammarPosition::Infix, AstShapeRef::new("k", 1));
        assert_eq!(a, b);
    }

    #[test]
    fn position_serde() {
        let j = serde_json::to_string(&GrammarPosition::Prefix).unwrap();
        assert_eq!(j, "\"Prefix\"");
        let back: GrammarPosition = serde_json::from_str(&j).unwrap();
        assert_eq!(back, GrammarPosition::Prefix);
    }
}
