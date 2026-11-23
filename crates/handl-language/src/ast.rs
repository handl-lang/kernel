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
///   by every engine: `hnl-exec-tree-walk/src/lib.rs` (closure
///   arm), `hnl-exec-bytecode/src/{compile.rs,vm.rs}`,
///   `hnl-exec-cranelift/src/lib.rs`, and
///   `hnl-tool-transform-rewrite/src/native/desugar.rs`.
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

/// Names the subtree *references* as variables — payloads of `var`-kind
/// nodes only, not every payload string.
///
/// [`subtree_name_candidates`] is deliberately conservative: it gathers
/// every string in every payload, so a literal like `bytes := "bytes"`
/// (the bare-name/`import * as` lowering) reads as a self-reference and
/// the bound name appears wherever it is merely *mentioned* — record
/// keys, op names, import specs. For a self-recursion check that is a
/// false positive: recursion requires the name to be *referenced*, which
/// the grammar spells as a `var` node.
///
/// A node counts as a variable reference when it plays the `leaf`
/// pattern role and carries its name as the payload — either a bare
/// string or `{"name": <s>}`. `is_var` supplies the predicate (e.g.
/// `lang.pattern_role_is(kind, "leaf")` with a `kind == "var"` fallback,
/// as `instantiate` does); keeping it a parameter leaves the traversal
/// generic over languages that spell the variable leaf differently.
///
/// Returns `None` when any reachable node is unresolvable, matching
/// [`subtree_name_candidates`].
pub fn subtree_var_names(
    mut node_at: impl FnMut(AstRef) -> Option<AstNode>,
    mut is_var: impl FnMut(&AstNode) -> bool,
    root: AstRef,
) -> Option<std::collections::HashSet<std::rc::Rc<str>>> {
    let mut out = std::collections::HashSet::new();
    let mut visited = std::collections::HashSet::new();
    let mut stack = vec![root];
    while let Some(r) = stack.pop() {
        if !visited.insert(r) {
            continue;
        }
        let node = node_at(r)?;
        if is_var(&node) {
            if let Some(name) = node
                .payload
                .as_str()
                .or_else(|| node.payload.get("name").and_then(Value::as_str))
            {
                out.insert(std::rc::Rc::from(name));
            }
        }
        if let Value::Object(map) = &node.payload {
            for (k, val) in map {
                if k == "children" {
                    if let Some(arr) = val.as_array() {
                        for el in arr.iter().filter_map(|e| e.as_u64()) {
                            stack.push(AstRef::new(el as usize));
                        }
                    }
                } else if ARENA_REF_PAYLOAD_KEYS.contains(&k.as_str()) {
                    if let Some(i) = val.as_u64() {
                        stack.push(AstRef::new(i as usize));
                    }
                }
            }
        }
    }
    Some(out)
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
        // DFS stack of nodes currently on the visit path — the cycle guard.
        // Scoped to this call (not thread-local): on error the whole
        // traversal aborts, so error paths never need to unwind it.
        let mut visiting: Vec<usize> = Vec::new();
        self.subtree_into(root, &mut map, &mut new_nodes, &mut visiting)?;
        let mut out = Ast::new();
        // `subtree_into` already appended in post-order; rebuild via push to
        // keep arena indices identical to `new_nodes` positions.
        for n in new_nodes {
            out.push(n);
        }
        Ok(out)
    }

    /// Recursive post-order helper for [`subtree`](Self::subtree).
    ///
    /// `visiting` is the DFS stack of arena indices on the current visit
    /// path; re-entering one means the arena has a reference cycle, which is
    /// reported with the cycle's node path. Entries are popped on success —
    /// on error the whole [`subtree`](Self::subtree) call unwinds, so the
    /// stack is simply abandoned.
    fn subtree_into(
        &self,
        root: AstRef,
        map: &mut std::collections::HashMap<usize, usize>,
        new_nodes: &mut Vec<AstNode>,
        visiting: &mut Vec<usize>,
    ) -> Result<(), LangError> {
        let idx = root.index();
        if map.contains_key(&idx) {
            return Ok(());
        }
        if let Some(pos) = visiting.iter().position(|&x| x == idx) {
            let path = visiting[pos..]
                .iter()
                .chain(std::iter::once(&idx))
                .map(|i| {
                    format!(
                        "{}:{}",
                        i,
                        self.nodes.get(*i).map(|n| n.kind.as_str()).unwrap_or("?")
                    )
                })
                .collect::<Vec<_>>()
                .join(" -> ");
            return Err(LangError::engine(format!(
                "subtree: arena cycle detected: {path}"
            )));
        }
        visiting.push(idx);
        let node = self.at(root)?;
        // Visit children first (post-order: children appended before parent).
        let mut child_new_indices: Vec<u64> = Vec::new();
        if let Some(children) = node.payload.get("children").and_then(|c| c.as_array()) {
            for child_ref in children {
                if let Some(cidx) = child_ref.as_u64() {
                    self.subtree_into(AstRef::new(cidx as usize), map, new_nodes, visiting)?;
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
                    self.subtree_into(AstRef::new(vidx), map, new_nodes, visiting)?;
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
        visiting.pop();
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
#[path = "ast_test.rs"]
mod ast_test;
