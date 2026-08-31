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
    /// When set, the **last** child of this shape is a delimited block (e.g.
    /// the `{ arms }` of `match x { ... }`). The first `arity - 1` children
    /// are parsed as ordinary expressions; the final child is parsed by the
    /// [`DelimitedShape`] descriptor. This generalizes the Pratt engine's
    /// delimited-group support beyond the hardcoded `call(...)` case.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub delimited: Option<DelimitedShape>,
}

/// Describes how to parse a delimited block child (the last child of an
/// [`AstShapeRef`] whose `delimited` field is set).
///
/// A delimited block is opened by `open`, contains zero or more elements
/// separated by `separator`, and is closed by `close`. The block is emitted
/// as a container node of `container_kind` whose `children` array holds the
/// parsed element node indices.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct DelimitedShape {
    /// The token kind that opens the block (e.g. `token.lbrace`).
    pub open: String,
    /// The token kind that closes the block (e.g. `token.rbrace`).
    pub close: String,
    /// The token kind separating elements (e.g. `token.comma`). When `None`,
    /// elements are not separated. A trailing separator before `close` is
    /// tolerated.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub separator: Option<String>,
    /// The node kind of the container holding the elements (e.g. `block`).
    pub container_kind: String,
    /// When set, each element is a *pair* `<expr> <pair separator> <expr>`
    /// (e.g. a match arm `pattern : body`), emitted as a node of
    /// [`PairShape::node_kind`] with `children = [lhs, rhs]`. When `None`,
    /// each element is a single expression collected directly.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub pair: Option<PairShape>,
}

/// Describes a pair element inside a delimited block (e.g. a match arm).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct PairShape {
    /// The token kind separating the pair's left and right operands (e.g.
    /// `token.colon` for `pattern : body`).
    pub separator: String,
    /// The node kind emitted for each pair (e.g. `arm`).
    pub node_kind: String,
}

impl AstShapeRef {
    /// Create a new shape reference.
    pub fn new(node_kind: impl Into<String>, arity: usize) -> Self {
        Self {
            node_kind: node_kind.into(),
            arity,
            delimited: None,
        }
    }

    /// Attach a delimited-block descriptor to the last child.
    pub fn with_delimited(mut self, delimited: DelimitedShape) -> Self {
        self.delimited = Some(delimited);
        self
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

    #[test]
    fn delimited_shape_roundtrip() {
        let shape = AstShapeRef::new("match", 2).with_delimited(DelimitedShape {
            open: "token.lbrace".into(),
            close: "token.rbrace".into(),
            separator: Some("token.comma".into()),
            container_kind: "block".into(),
            pair: Some(PairShape {
                separator: "token.colon".into(),
                node_kind: "arm".into(),
            }),
        });
        let row = GrammarRow::new(
            "grammar.match.prefix",
            "token.keyword.match",
            GrammarPosition::Prefix,
            shape,
        );
        let j = serde_json::to_string(&row).unwrap();
        let back: GrammarRow = serde_json::from_str(&j).unwrap();
        assert_eq!(row, back);
        assert!(j.contains("\"delimited\""));
        let plain = GrammarRow::new(
            "g",
            "t",
            GrammarPosition::Infix,
            AstShapeRef::new("k", 1),
        );
        let pj = serde_json::to_string(&plain).unwrap();
        assert!(!pj.contains("delimited"));
    }
}
