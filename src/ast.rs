//! The `Ast` arena and `AstRef` handle, plus a minimal serializable `AstNode`.
//!
//! `AstNode` mirrors the shape of `handl_platform::AstNode` (a `kind`, an
//! optional source `Span`, and an arbitrary JSON `payload`) but is defined
//! locally here rather than re-exported from `handl-platform`. This keeps
//! `handl-language` a low-level data crate with only `serde`/`serde_json`/
//! `thiserror` dependencies — reusing `handl_platform::AstNode` would pull in
//! the typechecker, semver, and toml transitively for a single trivial struct.
//! The two types are structurally identical and interconvertible via serde.

use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::error::LangError;

/// A span of byte offsets in source text.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
pub struct Span {
    /// Inclusive start offset.
    pub start: usize,
    /// Exclusive end offset.
    pub end: usize,
}

/// A single, generic, composable AST node.
///
/// Structurally identical to `handl_platform::AstNode`: a `kind` string keyed
/// to the language's `AstShapeDef`s, an optional source `Span`, and an
/// arbitrary JSON `payload`.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct AstNode {
    /// The node kind, keyed to `AstShapeDef::node_kind`.
    pub kind: String,
    /// Optional source span.
    pub span: Option<Span>,
    /// Arbitrary JSON payload describing the node's data.
    pub payload: Value,
}

impl AstNode {
    /// Create a new node with the given kind, no span, and a null payload.
    pub fn new(kind: impl Into<String>) -> Self {
        Self {
            kind: kind.into(),
            span: None,
            payload: Value::Null,
        }
    }

    /// Attach a span to this node.
    pub fn with_span(mut self, span: Span) -> Self {
        self.span = Some(span);
        self
    }

    /// Attach a payload to this node.
    pub fn with_payload(mut self, payload: Value) -> Self {
        self.payload = payload;
        self
    }
}

/// A stable, `Copy` index into an [`Ast`] arena.
///
/// Serializes as the underlying `usize` index so that `Ast` + `AstRef` graphs
/// round-trip through serde.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct AstRef(
    /// The index into the arena's node vector.
    pub usize,
);

impl AstRef {
    /// Create a new reference wrapping the given index.
    pub fn new(index: usize) -> Self {
        Self(index)
    }

    /// The underlying index.
    pub fn index(self) -> usize {
        self.0
    }
}

/// An arena of [`AstNode`]s addressed by [`AstRef`].
///
/// Nodes are appended and never moved, so `AstRef`s remain valid for the
/// lifetime of the arena. Out-of-bounds access returns
/// [`LangError::AstIndexOutOfBounds`].
#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq)]
pub struct Ast {
    /// The backing node vector.
    nodes: Vec<AstNode>,
}

impl Ast {
    /// Create an empty arena.
    pub fn new() -> Self {
        Self::default()
    }

    /// Append a node and return a reference to it.
    pub fn push(&mut self, node: AstNode) -> AstRef {
        let idx = self.nodes.len();
        self.nodes.push(node);
        AstRef(idx)
    }

    /// Resolve a reference, returning `None` if out of bounds.
    pub fn get(&self, r: AstRef) -> Option<&AstNode> {
        self.nodes.get(r.0)
    }

    /// Resolve a mutable reference, returning `None` if out of bounds.
    pub fn get_mut(&mut self, r: AstRef) -> Option<&mut AstNode> {
        self.nodes.get_mut(r.0)
    }

    /// Resolve a reference, returning an error if out of bounds.
    ///
    /// # Errors
    ///
    /// Returns [`LangError::AstIndexOutOfBounds`] if the index is past the end.
    pub fn at(&self, r: AstRef) -> Result<&AstNode, LangError> {
        self.nodes
            .get(r.0)
            .ok_or(LangError::AstIndexOutOfBounds { index: r.0 })
    }

    /// The number of nodes in the arena.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Whether the arena is empty.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Iterate over the nodes in insertion order.
    pub fn iter(&self) -> impl Iterator<Item = &AstNode> {
        self.nodes.iter()
    }

    /// The backing node slice, for direct indexing.
    pub fn nodes(&self) -> &[AstNode] {
        &self.nodes
    }
}

impl std::ops::Index<AstRef> for Ast {
    type Output = AstNode;

    fn index(&self, r: AstRef) -> &AstNode {
        &self.nodes[r.0]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn node_builders() {
        let n = AstNode::new("lit")
            .with_span(Span { start: 0, end: 3 })
            .with_payload(Value::from(42));
        assert_eq!(n.kind, "lit");
        assert_eq!(n.span, Some(Span { start: 0, end: 3 }));
        assert_eq!(n.payload, Value::from(42));
    }

    #[test]
    fn arena_insert_and_resolve() {
        let mut ast = Ast::new();
        assert!(ast.is_empty());
        let a = ast.push(AstNode::new("a"));
        let b = ast.push(AstNode::new("b"));
        assert_eq!(ast.len(), 2);
        assert_eq!(ast.get(a).unwrap().kind, "a");
        assert_eq!(ast.get(b).unwrap().kind, "b");
        assert_eq!(ast[a].kind, "a");
        assert_eq!(ast[b].kind, "b");
    }

    #[test]
    fn arena_get_mut() {
        let mut ast = Ast::new();
        let r = ast.push(AstNode::new("a"));
        ast.get_mut(r).unwrap().kind = "c".into();
        assert_eq!(ast.get(r).unwrap().kind, "c");
    }

    #[test]
    fn arena_out_of_bounds() {
        let ast = Ast::new();
        assert_eq!(ast.get(AstRef::new(0)), None);
        let err = ast.at(AstRef::new(99)).unwrap_err();
        assert_eq!(err, LangError::AstIndexOutOfBounds { index: 99 });
    }

    #[test]
    fn arena_growth_and_iter() {
        let mut ast = Ast::new();
        for i in 0..50 {
            ast.push(AstNode::new(format!("n{i}")));
        }
        assert_eq!(ast.len(), 50);
        let kinds: Vec<_> = ast.iter().map(|n| n.kind.clone()).collect();
        assert_eq!(kinds[0], "n0");
        assert_eq!(kinds[49], "n49");
    }

    #[test]
    fn astref_index_accessor() {
        let r = AstRef::new(12);
        assert_eq!(r.index(), 12);
    }

    #[test]
    fn ast_nodes_slice() {
        let mut ast = Ast::new();
        ast.push(AstNode::new("a"));
        ast.push(AstNode::new("b"));
        let slice = ast.nodes();
        assert_eq!(slice.len(), 2);
        assert_eq!(slice[1].kind, "b");
    }

    #[test]
    fn astref_serde_roundtrip() {
        let r = AstRef::new(7);
        let j = serde_json::to_string(&r).unwrap();
        assert_eq!(j, "7");
        let back: AstRef = serde_json::from_str(&j).unwrap();
        assert_eq!(back, r);
    }

    #[test]
    fn ast_serde_roundtrip() {
        let mut ast = Ast::new();
        ast.push(AstNode::new("x").with_payload(Value::from(1)));
        ast.push(AstNode::new("y"));
        let j = serde_json::to_string(&ast).unwrap();
        let back: Ast = serde_json::from_str(&j).unwrap();
        assert_eq!(ast, back);
    }
}
