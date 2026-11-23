//! Transform rule fragment definitions (ADR-0094 — Generic AST Transform
//! Engine).
//!
//! A *transform* is a pure `Ast → Ast` rewrite: it never evaluates,
//! typechecks, or emits. A *pass* is a named, ordered set of transform rules
//! (e.g. `desugar`, `lower`, `optimize`). A [`TransformDef`] maps a node kind
//! to a rewrite within a pass; the [`Language`](crate::Language) `transforms`
//! fragment set is the dispatch table a transform engine reads.
//!
//! This crate holds only the **data**: [`TransformRule`], [`RewriteStep`],
//! and [`TransformCondition`] are the rewrite *vocabulary* — they are
//! interpreted by transform engines (e.g. `hnl-tool-transform-rewrite`),
//! never executed here. The `Native` rule variant and the
//! `Splice`/`Apply`/`PayloadEq` vocabulary are declared now so the schema is
//! complete; they need no runtime support in this crate.
//!
//! # Serde representation
//!
//! All enums use serde's default **externally tagged** representation —
//! matching every other enum in this crate (`AstDesugarChild`,
//! `LexerPattern`, …). A rule is `{"Declarative": {"target_kind": …,
//! "children": […]}}` or `{"Native": "desugar.while"}`; a step is
//! `{"Keep": 0}` / `{"KeepRole": "target"}` / `{"Create": {…}}`; a condition
//! is `{"KindAt": {…}}` / `{"And": […]}` / etc. JSON and YAML round-trip
//! identically.

use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::fragment::Fragment;
use crate::fragments::ast_shape::{AstDesugarChild, AstDesugarRule};

/// A single transform rule: a pure `Ast → Ast` rewrite dispatched on
/// `(pass, node_kind, priority)` (ADR-0094 §2).
///
/// `pass` names the pass the rule belongs to (`"desugar"`, `"lower"`,
/// `"optimize"`, …); `node_kind` is the dispatch key — the node kind this
/// rule fires on; `priority` orders rules when several are declared for the
/// same pass+kind (lower numbers run first).
///
/// Identity key: `pass:node_kind:priority` — two rules at the same pass,
/// kind, and priority are a merge collision unless one declares `replaces`
/// (same discipline as [`EvalSchemeDef`](crate::EvalSchemeDef)).
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct TransformDef {
    /// Stable identifier (e.g. `"transform.desugar.nullish"`).
    pub id: String,
    /// The pass this rule belongs to (`"desugar"`, `"lower"`, …).
    pub pass: String,
    /// The AST node kind this rule rewrites (the dispatch key).
    pub node_kind: String,
    /// Ordering when several rules share a pass+kind: lower fires first.
    /// Defaults to `0` and is skipped on the wire when `0`.
    #[serde(default, skip_serializing_if = "is_zero")]
    pub priority: i32,
    /// Optional condition gating the rewrite. When absent the rule fires
    /// unconditionally; when present a transform engine only applies `rule`
    /// to nodes satisfying the condition.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub when: Option<TransformCondition>,
    /// The rewrite to apply.
    pub rule: TransformRule,
    /// ids this fragment declares it replaces.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub replaces: Vec<String>,
    /// ids this fragment hard-requires.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub requires: Vec<String>,
}

fn is_zero(i: &i32) -> bool {
    *i == 0
}

/// The payload marker a [`RewriteStep::Create`] `payload` (or a
/// [`TransformRule::Declarative`] `payload` patch) uses to copy an
/// attribute value off a node of the *matched* subtree into the
/// rewritten node — the attr_rhs half of the mlopt law bridge.
///
/// A payload value of the form `{"$attr_of": {"path": […], "attr":
/// "name"}}` resolves, at rewrite time, to the `payload["attrs"][name]`
/// value of the descendant reached by child-index `path` below the
/// matched node (empty `path` = the matched node itself). Resolution
/// is recursive through objects and arrays; an unresolvable marker is
/// an error, never a silently fabricated value.
pub const PAYLOAD_ATTR_OF: &str = "$attr_of";

/// The rewrite a [`TransformDef`] applies (ADR-0094 §3).
///
/// - [`TransformRule::Declarative`] rewrites the matched node into a new node
///   of `target_kind` whose children are produced by interpreting each
///   [`RewriteStep`] against the original node. `payload`, when present, is a
///   **shallow patch**: provided keys overwrite, absent keys are preserved
///   from the original node's payload.
/// - [`TransformRule::Replace`] rewrites the matched node *by* an existing
///   descendant instead of allocating a node: the result **is** the node at
///   child-index `path`. It is a [`RewriteStep::KeepPath`] promoted to the
///   rule level, and it is what expresses a *root-eliminating* law (one whose
///   right-hand side is a subterm).
/// - [`TransformRule::Native`] is the disciplined escape hatch: dispatch
///   stays in `TransformDef` data, only the implementation is Rust. The name
///   (e.g. `"desugar.while"`) is resolved against the native-rewrite registry
///   a transform engine is wired with — this crate only carries the data.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum TransformRule {
    /// A data-driven rewrite into a node of `target_kind`.
    Declarative {
        /// The AST node kind to rewrite into.
        target_kind: String,
        /// The steps producing the rewritten node's children.
        children: Vec<RewriteStep>,
        /// Optional shallow payload patch merged into the new node.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        payload: Option<Value>,
    },
    /// Replace the matched node *by* an existing descendant (ADR-0127).
    ///
    /// The rewritten node **is** the node at child-index `path` below the
    /// matched node, remapped into the output arena — no node is created.
    /// This is [`RewriteStep::KeepPath`] promoted to the rule level: where
    /// [`Declarative`](Self::Declarative) always allocates a node of
    /// `target_kind` (and therefore cannot express a law that *eliminates
    /// its root*), `Replace` returns one that already exists. A
    /// root-eliminating law such as `double_neg: neg(neg(a)) → a` is exactly
    /// `Replace { path: [0, 0] }`.
    ///
    /// `path` is interpreted exactly as [`RewriteStep::KeepPath`]'s: a
    /// non-empty sequence of child indices starting at the matched node. A
    /// path that does not resolve to an existing descendant is an **error**,
    /// never a silently fabricated node.
    Replace {
        /// Child-index path from the matched node to the result node.
        path: Vec<usize>,
    },
    /// A named native rewrite (e.g. `"desugar.while"`), interpreted by the
    /// native-rewrite registry of whichever transform engine runs the pass.
    Native(String),
}

/// One step producing (part of) a rewritten node's children (ADR-0094 §3).
///
/// `Keep`/`KeepPath`/`KeepRest`/`Create` generalize
/// [`AstDesugarChild`](crate::AstDesugarChild) with identical semantics;
/// `KeepRole` is the ADR-0081-native role-resolved form; `Splice` and
/// `Apply` are declared for vocabulary completeness and interpreted by
/// transform engines.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum RewriteStep {
    /// Reuse the original node's child at the given index (positional —
    /// the role-less fallback; prefer [`RewriteStep::KeepRole`] when the
    /// shape declares roles).
    Keep(usize),
    /// Reuse the original node's child occupying the named role, resolved
    /// to a positional index via
    /// [`AstShapeDef::role_index`](crate::AstShapeDef::role_index)
    /// (ADR-0081).
    KeepRole(String),
    /// Reuse a descendant node by navigating through children by index path
    /// (`KeepPath([0, 0])` takes child 0's child 0).
    KeepPath(Vec<usize>),
    /// Keep all children from the given index onward (ADR-0060) — each is
    /// remapped into the output arena.
    KeepRest(usize),
    /// Lift the indexed child's own children into the rewritten node's
    /// child list (declared for vocabulary completeness; interpreted by
    /// transform engines).
    Splice(usize),
    /// Allocate a new node with the given `kind`, optional `payload`, and
    /// nested `children` (themselves [`RewriteStep`]s — the rewrite is
    /// recursive).
    Create {
        /// The AST node kind of the created node.
        kind: String,
        /// Optional payload for the created node.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        payload: Option<Value>,
        /// Nested children of the created node.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        children: Vec<RewriteStep>,
    },
    /// Apply another transform rule to the indexed child first, then keep
    /// the result (declared for vocabulary completeness; interpreted by
    /// transform engines).
    Apply {
        /// The id of the [`TransformDef`] to apply to the child.
        rule_id: String,
        /// The index of the child to transform.
        index: usize,
    },
    /// Allocate a fresh `var` leaf with a unique, non-colliding name.
    ///
    /// The `hint` is used only to make the generated name readable and to
    /// share a single generated variable when the same hint appears multiple
    /// times within one rule application. Freshness is guaranteed by a
    /// per-rewrite counter.
    Fresh(String),
}

/// A condition gating whether a [`TransformDef`] fires (ADR-0094 §3).
///
/// `KindAt` generalizes [`AstDesugarCondition`](crate::AstDesugarCondition)
/// to test a child by positional index or named role; `PayloadEq`,
/// `ChildCount`, and the boolean combinators are declared for vocabulary
/// completeness and interpreted by transform engines.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum TransformCondition {
    /// The node must have a child of `kind` at the given position — by
    /// positional `index`, by named `role` (resolved via
    /// [`AstShapeDef::role_index`](crate::AstShapeDef::role_index)), or both
    /// (role resolved, falling back to index for role-less shapes).
    KindAt {
        /// The positional child index to test (role-less fallback).
        #[serde(default, skip_serializing_if = "Option::is_none")]
        index: Option<usize>,
        /// The named child role to test (ADR-0081).
        #[serde(default, skip_serializing_if = "Option::is_none")]
        role: Option<String>,
        /// The AST node kind the resolved child must have.
        kind: String,
    },
    /// The node must have *some* child of `kind`, at any position. This is
    /// the shape-agnostic companion to `KindAt` for variable-arity children
    /// — e.g. a `block` holding a bare `type-annot` statement.
    AnyChildKind {
        /// The AST node kind at least one child must have.
        kind: String,
    },
    /// The node's payload at `path` must equal `value`.
    PayloadEq {
        /// The payload path to test (interpretation is engine-defined).
        path: String,
        /// The value the payload at `path` must equal.
        value: Value,
    },
    /// The payload of one of the node's children must equal `value` at
    /// `path`. The child is resolved by named `role` (via
    /// [`AstShapeDef::role_index`](crate::AstShapeDef::role_index), ADR-0081),
    /// falling back to positional `index` for role-less shapes. An empty
    /// `path` tests the child's payload itself.
    ChildPayloadEq {
        /// The positional child index to test (role-less fallback).
        #[serde(default, skip_serializing_if = "Option::is_none")]
        index: Option<usize>,
        /// The named child role to test (ADR-0081).
        #[serde(default, skip_serializing_if = "Option::is_none")]
        role: Option<String>,
        /// The payload path to test on the resolved child (empty = the
        /// payload itself).
        #[serde(default, skip_serializing_if = "String::is_empty")]
        path: String,
        /// The value the payload at `path` must equal.
        value: Value,
    },
    /// The node must have exactly this many children.
    ChildCount(usize),
    /// An attribute guard for data-driven nodes whose op attrs ride in
    /// `payload["attrs"]` (the mlopt bridge's encoding — ADR-0094
    /// vocabulary extension for law guards).
    ///
    /// The node reached by child-index `path` below the matched node
    /// (empty = the node itself) must carry `attr` in its
    /// `payload["attrs"]` map; when `value` is present the attr must
    /// equal it, when absent presence alone satisfies the condition
    /// (a bound attr *metavariable* — mlopt requires the attr to exist
    /// but its value is unconstrained). An unresolvable path or a
    /// missing `attrs` map evaluates to `false`, never panics.
    AttrEq {
        /// Child-index path to the attr-carrying node (empty = self).
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        path: Vec<usize>,
        /// The attr name inside the node's `payload["attrs"]` map.
        attr: String,
        /// Literal the attr must equal; absent = presence only.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        value: Option<Value>,
    },
    /// Two attribute locations must hold equal values — the handl
    /// spelling of a *repeated attr metavariable* in a law lhs: mlopt's
    /// matcher binds the metavar once, so every occurrence beyond the
    /// first is an equality constraint between the attr values at the
    /// recorded positions. Both sides resolve like
    /// [`TransformCondition::AttrEq`]; either side missing its attr
    /// evaluates to `false`.
    SameAttr {
        /// Child-index path to the first attr-carrying node.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        path_a: Vec<usize>,
        /// The attr name inside that node's `payload["attrs"]` map.
        attr_a: String,
        /// Child-index path to the second attr-carrying node.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        path_b: Vec<usize>,
        /// The attr name inside that node's `payload["attrs"]` map.
        attr_b: String,
    },
    /// All sub-conditions must hold.
    And(Vec<TransformCondition>),
    /// At least one sub-condition must hold.
    Or(Vec<TransformCondition>),
    /// The sub-condition must not hold.
    Not(Box<TransformCondition>),
}

impl TransformDef {
    /// Create a new transform rule with `priority` 0, no `when` condition,
    /// and empty `replaces`/`requires`.
    pub fn new(
        id: impl Into<String>,
        pass: impl Into<String>,
        node_kind: impl Into<String>,
        rule: TransformRule,
    ) -> Self {
        Self {
            id: id.into(),
            pass: pass.into(),
            node_kind: node_kind.into(),
            priority: 0,
            when: None,
            rule,
            replaces: Vec::new(),
            requires: Vec::new(),
        }
    }

    /// Set the rule's `priority` (ordering within a pass+kind).
    pub fn with_priority(mut self, priority: i32) -> Self {
        self.priority = priority;
        self
    }

    /// Attach a `when` condition gating the rewrite.
    pub fn with_when(mut self, when: TransformCondition) -> Self {
        self.when = Some(when);
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

impl Fragment for TransformDef {
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
        format!("{}:{}:{}", self.pass, self.node_kind, self.priority)
    }
}

/// Lower an [`AstDesugarRule`] (the `desugar:` field on an
/// [`AstShapeDef`](crate::AstShapeDef), ADR-0053 §7) into a first-class
/// [`TransformDef`] in the `"desugar"` pass (ADR-0094 §6).
///
/// The synthesized rule has `id = "transform.desugar.<node_kind>"`,
/// `priority` 0, and a [`TransformRule::Declarative`] whose children are the
/// `AstDesugarChild` steps converted one-to-one into [`RewriteStep`]s. A
/// `when` condition lowers to [`TransformCondition::KindAt`] on the
/// positional child index.
pub(crate) fn lower_desugar_rule(node_kind: &str, rule: &AstDesugarRule) -> TransformDef {
    let children = rule.children.iter().map(lower_desugar_child).collect();
    let when = rule.when.as_ref().map(|c| TransformCondition::KindAt {
        index: Some(c.child_index),
        role: None,
        kind: c.child_kind.clone(),
    });
    TransformDef {
        id: format!("transform.desugar.{}", node_kind),
        pass: "desugar".to_string(),
        node_kind: node_kind.to_string(),
        priority: 0,
        when,
        rule: TransformRule::Declarative {
            target_kind: rule.target_kind.clone(),
            children,
            payload: None,
        },
        replaces: Vec::new(),
        requires: Vec::new(),
    }
}

/// Convert an [`AstDesugarChild`] into the equivalent [`RewriteStep`]
/// (recursive for `Create`).
fn lower_desugar_child(child: &AstDesugarChild) -> RewriteStep {
    match child {
        AstDesugarChild::Keep(i) => RewriteStep::Keep(*i),
        AstDesugarChild::KeepPath(path) => RewriteStep::KeepPath(path.clone()),
        AstDesugarChild::KeepRest(i) => RewriteStep::KeepRest(*i),
        AstDesugarChild::Create {
            kind,
            payload,
            children,
        } => RewriteStep::Create {
            kind: kind.clone(),
            payload: payload.clone(),
            children: children.iter().map(lower_desugar_child).collect(),
        },
    }
}

#[cfg(test)]
#[path = "transform_def_test.rs"]
mod transform_def_test;
