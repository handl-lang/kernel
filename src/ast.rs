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

/// Payload keys (besides `children`) whose integer value is an **arena
/// reference** — a `usize` index into the same [`Ast`] arena the node lives
/// in. [`Ast::subtree`] remaps these alongside `payload["children"]` so an
/// extracted subtree is genuinely standalone (ADR-0106 item 2 step 2a).
///
/// Evidence for the list (audited against the tree):
///
/// - `body` — the closure/function form `{"params": [...], "body": <idx>}`
///   (and its hand-built `data`/`rec` counterparts). Read as an arena index
///   by every engine: `plugin-engine-exec-tree-walk/src/lib.rs` (closure
///   arm), `plugin-engine-exec-bytecode/src/{compile.rs,vm.rs}`,
///   `plugin-engine-exec-cranelift/src/lib.rs`, and
///   `plugin-engine-transform-rewrite/src/native/desugar.rs`.
///
/// Everything else a payload carries is data, not a reference: child roles
/// index positionally into `payload["children"]` (ADR-0081), and fields such
/// as `name`, `params`, `elements`, `entries`, `constructors`, `index` and
/// `arms` hold strings, structured records, or numbers that are not arena
/// indices. Shorthands such as `match` arms are lowered into `children`
/// before evaluation, so no engine reads a nested arm as an index.
pub const ARENA_REF_PAYLOAD_KEYS: &[&str] = &["body"];

/// Collect every string occurring anywhere in the payload subtree rooted
/// at `root` — a conservative superset of the subtree's free names.
///
/// Closure-capture filtering uses this to retain only the env bindings a
/// body can actually reference: every env lookup (`proj_env` /
/// `extend_env` `lit: $payload` schemes, assign targets, pattern binders,
/// import names) is spelled as a string somewhere in the subtree, so a
/// name absent from the returned set can never be looked up by the body.
/// Over-collection is harmless — applying an arrow consults its local
/// bindings before the captured env, and callers `retain` only names the
/// env actually contains.
///
/// Child-node references resolve through `payload["children"]` and the
/// audited [`ARENA_REF_PAYLOAD_KEYS`] fields; all other payload data is
/// walked for strings but never dereferenced as an arena index.
///
/// `payload_at` supplies each node's payload (`Ast::get(r).map(|n|
/// n.payload.clone())` for a local arena, or `NativeOpCtx::
/// node_payload_at` inside the shared ops). Returns `None` when any
/// reachable node is unresolvable — the caller then keeps the full
/// captured env rather than risk under-capturing.
pub fn subtree_name_candidates(
    mut payload_at: impl FnMut(AstRef) -> Option<Value>,
    root: AstRef,
) -> Option<std::collections::HashSet<std::rc::Rc<str>>> {
    let mut out = std::collections::HashSet::new();
    let mut visited = std::collections::HashSet::new();
    let mut stack = vec![root];
    while let Some(r) = stack.pop() {
        if !visited.insert(r) {
            continue;
        }
        let payload = payload_at(r)?;
        collect_name_strings(&payload, &mut out, &mut stack);
    }
    Some(out)
}

fn collect_name_strings(
    v: &Value,
    out: &mut std::collections::HashSet<std::rc::Rc<str>>,
    stack: &mut Vec<AstRef>,
) {
    match v {
        Value::String(s) => {
            out.insert(std::rc::Rc::from(s.as_str()));
        }
        Value::Array(items) => {
            for item in items {
                collect_name_strings(item, out, stack);
            }
        }
        Value::Object(map) => {
            for (k, val) in map {
                if k == "children" {
                    if let Some(arr) = val.as_array() {
                        for el in arr {
                            if let Some(i) = el.as_u64() {
                                stack.push(AstRef::new(i as usize));
                            }
                        }
                    }
                } else if ARENA_REF_PAYLOAD_KEYS.contains(&k.as_str()) {
                    if let Some(i) = val.as_u64() {
                        stack.push(AstRef::new(i as usize));
                    }
                } else {
                    collect_name_strings(val, out, stack);
                }
            }
        }
        _ => {}
    }
}

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

    /// Extract the subtree rooted at `root` into a fresh standalone [`Ast`].
    ///
    /// Collects `root` plus every transitively-referenced descendant and
    /// reindexes them into a new arena. Arena references are remapped to the
    /// new arena in **both** places they occur (ADR-0106 item 2 step 2a):
    ///
    /// - `payload["children"]` — the positional child array (ADR-0081); and
    /// - any [`ARENA_REF_PAYLOAD_KEYS`] entry — named references such as the
    ///   closure form's `payload["body"]`.
    ///
    /// The new arena is laid out post-order (children before parents), so
    /// `root` is the last node — matching the Pratt convention used by the
    /// eval engines. Shared children are deduplicated (a node is copied at
    /// most once).
    ///
    /// This is used to bind an unevaluated child to a self-contained
    /// [`Ast`] value that the meta `eval` host function can evaluate
    /// (ADR-0041 §6) and, since ADR-0106 item 2, to mint the self-describing
    /// `body_def` of an arrow value.
    ///
    /// # Errors
    ///
    /// Returns [`LangError::AstIndexOutOfBounds`] if any referenced child
    /// index is out of bounds. A named reference ([`ARENA_REF_PAYLOAD_KEYS`])
    /// that is out of range is left untouched rather than rejected, so
    /// extracting an ancestor of malformed data cannot fail where it
    /// previously succeeded.
    pub fn subtree(&self, root: AstRef) -> Result<Ast, LangError> {
        use std::collections::HashMap;
        // old arena index -> new arena index.
        let mut map: HashMap<usize, usize> = HashMap::new();
        let mut new_nodes: Vec<AstNode> = Vec::new();
        self.subtree_into(root, &mut map, &mut new_nodes)?;
        let mut out = Ast::new();
        // `subtree_into` already appended in post-order; rebuild via push to
        // keep arena indices identical to `new_nodes` positions.
        for n in new_nodes {
            out.push(n);
        }
        Ok(out)
    }

    /// Recursive post-order helper for [`subtree`](Self::subtree).
    fn subtree_into(
        &self,
        root: AstRef,
        map: &mut std::collections::HashMap<usize, usize>,
        new_nodes: &mut Vec<AstNode>,
    ) -> Result<(), LangError> {
        let idx = root.index();
        if map.contains_key(&idx) {
            return Ok(());
        }
        let node = self.at(root)?;
        // Visit children first (post-order: children appended before parent).
        let mut child_new_indices: Vec<u64> = Vec::new();
        if let Some(children) = node.payload.get("children").and_then(|c| c.as_array()) {
            for child_ref in children {
                if let Some(cidx) = child_ref.as_u64() {
                    self.subtree_into(AstRef::new(cidx as usize), map, new_nodes)?;
                    child_new_indices.push(*map.get(&(cidx as usize)).unwrap() as u64);
                }
            }
        }
        // Named arena references in the payload (ADR-0106 item 2 step 2a):
        // e.g. the closure form `{"params": [...], "body": <idx>}`. Only an
        // integer value in range is treated as a reference; anything else
        // (a string, object, or out-of-range number) is left untouched, so
        // non-arena payload data is never rewritten.
        let mut key_new_indices: Vec<(String, u64)> = Vec::new();
        for key in ARENA_REF_PAYLOAD_KEYS {
            if let Some(v) = node.payload.get(*key).and_then(|v| v.as_u64()) {
                let vidx = v as usize;
                if vidx < self.len() {
                    self.subtree_into(AstRef::new(vidx), map, new_nodes)?;
                    key_new_indices.push(((*key).to_string(), *map.get(&vidx).unwrap() as u64));
                }
            }
        }
        // Build the remapped node.
        let mut new_payload = node.payload.clone();
        if let Some(children) = new_payload
            .get_mut("children")
            .and_then(|c| c.as_array_mut())
        {
            for (i, new_idx) in child_new_indices.iter().enumerate() {
                if let Some(slot) = children.get_mut(i) {
                    *slot = Value::from(*new_idx);
                }
            }
        }
        for (key, new_idx) in key_new_indices.iter() {
            if let Some(obj) = new_payload.as_object_mut() {
                obj.insert(key.clone(), Value::from(*new_idx));
            }
        }
        let new_idx = new_nodes.len();
        map.insert(idx, new_idx);
        new_nodes.push(AstNode {
            kind: node.kind.clone(),
            span: node.span,
            payload: new_payload,
        });
        Ok(())
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

    #[test]
    fn subtree_extracts_rooted_subtree() {
        // 0: lit(2), 1: lit(3), 2: binary.add {children:[0,1]}
        let mut ast = Ast::new();
        ast.push(AstNode::new("lit").with_payload(Value::from(2)));
        ast.push(AstNode::new("lit").with_payload(Value::from(3)));
        ast.push(AstNode::new("binary.add").with_payload(serde_json::json!({"children": [0, 1]})));
        let sub = ast.subtree(AstRef::new(2)).unwrap();
        // Root is the last node.
        assert_eq!(sub.len(), 3);
        assert_eq!(sub.nodes()[2].kind, "binary.add");
        // Children indices remapped to the new arena.
        let children = sub.nodes()[2]
            .payload
            .get("children")
            .unwrap()
            .as_array()
            .unwrap();
        assert_eq!(children[0], Value::from(0));
        assert_eq!(children[1], Value::from(1));
        assert_eq!(sub.nodes()[0].payload, Value::from(2));
        assert_eq!(sub.nodes()[1].payload, Value::from(3));
    }

    #[test]
    fn subtree_single_node() {
        let mut ast = Ast::new();
        ast.push(AstNode::new("lit").with_payload(Value::from(42)));
        let sub = ast.subtree(AstRef::new(0)).unwrap();
        assert_eq!(sub.len(), 1);
        assert_eq!(sub.nodes()[0].payload, Value::from(42));
    }

    /// ADR-0106 item 2 step 2a: a named arena reference in the payload
    /// (`body`, the closure form) is remapped too — the extracted arena is
    /// genuinely standalone, not just `children`-complete.
    #[test]
    fn subtree_remaps_named_body_reference() {
        // Arena: 0: lit(1), 1: var(x), 2: binary.add[0,1],
        //        3: closure {params:["x"], body: 2}
        let mut ast = Ast::new();
        ast.push(AstNode::new("lit").with_payload(Value::from(1)));
        ast.push(AstNode::new("var").with_payload(Value::from("x")));
        ast.push(
            AstNode::new("binary.add").with_payload(serde_json::json!({ "children": [0, 1] })),
        );
        ast.push(
            AstNode::new("closure").with_payload(serde_json::json!({ "params": ["x"], "body": 2 })),
        );

        let sub = ast.subtree(AstRef::new(3)).unwrap();
        // Post-order: children of the body first, then the body, then the
        // closure root last.
        assert_eq!(sub.len(), 4);
        assert_eq!(sub.nodes()[3].kind, "closure");

        // The closure's `body` now points at the *extracted* body node, and
        // that node's own `children` point at the extracted operands: every
        // reference resolves inside the new arena.
        let body_new = sub.nodes()[3].payload["body"].as_u64().unwrap() as usize;
        assert!(
            body_new < sub.len(),
            "remapped body index must be in range of the extracted arena",
        );
        assert_eq!(sub.nodes()[body_new].kind, "binary.add");
        let kids = sub.nodes()[body_new].payload["children"]
            .as_array()
            .unwrap();
        for k in kids {
            assert!((k.as_u64().unwrap() as usize) < sub.len());
        }
        assert_eq!(
            sub.nodes()[kids[0].as_u64().unwrap() as usize].payload,
            Value::from(1)
        );
        assert_eq!(
            sub.nodes()[kids[1].as_u64().unwrap() as usize].payload,
            Value::from("x"),
        );
    }

    /// Non-reference payload numbers, and out-of-range `body` values, are
    /// left untouched — the remap must not rewrite unrelated payload data or
    /// fail on malformed ancestors.
    #[test]
    fn subtree_leaves_non_reference_payload_numbers_alone() {
        let mut ast = Ast::new();
        ast.push(AstNode::new("lit").with_payload(Value::from(7)));
        ast.push(AstNode::new("func").with_payload(serde_json::json!({
            "arity": 99,
            "index": 12345,
            "body": 99, // out of range: not a reference in this arena
            "name": "f"
        })));
        let sub = ast.subtree(AstRef::new(1)).unwrap();
        assert_eq!(sub.len(), 1, "only the root is extracted (no children)");
        // Unmatched numeric payload keys survive verbatim.
        assert_eq!(sub.nodes()[0].payload["arity"], Value::from(99));
        assert_eq!(sub.nodes()[0].payload["index"], Value::from(12345));
        assert_eq!(sub.nodes()[0].payload["body"], Value::from(99));
        assert_eq!(sub.nodes()[0].payload["name"], Value::from("f"));
    }

    /// A `body` that is not an integer (some nodes carry structured payload
    /// under that key) is not treated as a reference.
    #[test]
    fn subtree_ignores_non_integer_body_payload() {
        let mut ast = Ast::new();
        ast.push(AstNode::new("func").with_payload(serde_json::json!({
            "params": [],
            "body": { "kind": "lit", "value": 1 }
        })));
        let sub = ast.subtree(AstRef::new(0)).unwrap();
        assert_eq!(sub.len(), 1);
        assert_eq!(sub.nodes()[0].payload["body"]["kind"], Value::from("lit"));
    }
}
