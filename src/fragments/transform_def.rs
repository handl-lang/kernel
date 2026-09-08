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
//! interpreted by transform engines (e.g. `plugin-engine-transform-rewrite`),
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

/// The rewrite a [`TransformDef`] applies (ADR-0094 §3).
///
/// - [`TransformRule::Declarative`] rewrites the matched node into a new node
///   of `target_kind` whose children are produced by interpreting each
///   [`RewriteStep`] against the original node. `payload`, when present, is a
///   **shallow patch**: provided keys overwrite, absent keys are preserved
///   from the original node's payload.
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
    /// The node's payload at `path` must equal `value`.
    PayloadEq {
        /// The payload path to test (interpretation is engine-defined).
        path: String,
        /// The value the payload at `path` must equal.
        value: Value,
    },
    /// The node must have exactly this many children.
    ChildCount(usize),
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
mod tests {
    use super::*;
    use crate::fragment_set::FragmentSet;
    use crate::fragments::ast_shape::AstDesugarCondition;

    fn sample_rule() -> TransformRule {
        TransformRule::Declarative {
            target_kind: "binary.add".into(),
            children: vec![
                RewriteStep::Keep(0),
                RewriteStep::KeepRole("value".into()),
                RewriteStep::Create {
                    kind: "lit".into(),
                    payload: Some(Value::from(1)),
                    children: vec![],
                },
            ],
            payload: None,
        }
    }

    #[test]
    fn construct_and_accessors() {
        let def = TransformDef::new(
            "transform.desugar.nullish",
            "desugar",
            "nullish",
            sample_rule(),
        )
        .with_priority(10)
        .with_when(TransformCondition::ChildCount(2))
        .with_replaces(vec!["transform.desugar.nullish.old".into()])
        .with_requires(vec!["ast.nullish".into()]);
        assert_eq!(def.id(), "transform.desugar.nullish");
        assert_eq!(def.pass, "desugar");
        assert_eq!(def.node_kind, "nullish");
        assert_eq!(def.priority, 10);
        assert_eq!(def.when, Some(TransformCondition::ChildCount(2)));
        assert_eq!(
            def.replaces(),
            &["transform.desugar.nullish.old".to_string()]
        );
        assert_eq!(def.requires(), &["ast.nullish".to_string()]);
        assert_eq!(def.identity_key(), "desugar:nullish:10");
    }

    #[test]
    fn identity_key_includes_pass_kind_priority() {
        let a = TransformDef::new("a", "desugar", "x", TransformRule::Native("n".into()));
        let b = TransformDef::new("b", "lower", "x", TransformRule::Native("n".into()));
        let c = TransformDef::new("c", "desugar", "x", TransformRule::Native("n".into()))
            .with_priority(1);
        assert_eq!(a.identity_key(), "desugar:x:0");
        assert_eq!(b.identity_key(), "lower:x:0");
        assert_eq!(c.identity_key(), "desugar:x:1");
    }

    #[test]
    fn serde_roundtrip_declarative() {
        let def = TransformDef::new("t1", "desugar", "nullish", sample_rule())
            .with_priority(-2)
            .with_when(TransformCondition::And(vec![
                TransformCondition::KindAt {
                    index: Some(0),
                    role: None,
                    kind: "array".into(),
                },
                TransformCondition::Not(Box::new(TransformCondition::PayloadEq {
                    path: "op".into(),
                    value: Value::from("??"),
                })),
            ]));
        let j = serde_json::to_string(&def).unwrap();
        let back: TransformDef = serde_json::from_str(&j).unwrap();
        assert_eq!(def, back);
    }

    #[test]
    fn serde_roundtrip_native_and_all_steps() {
        let def = TransformDef::new(
            "t2",
            "desugar",
            "while",
            TransformRule::Native("desugar.while".into()),
        );
        let j = serde_json::to_string(&def).unwrap();
        let back: TransformDef = serde_json::from_str(&j).unwrap();
        assert_eq!(def, back);

        // Every RewriteStep / TransformCondition variant round-trips.
        let steps = vec![
            RewriteStep::Keep(0),
            RewriteStep::KeepRole("statements".into()),
            RewriteStep::KeepPath(vec![0, 0]),
            RewriteStep::KeepRest(2),
            RewriteStep::Splice(1),
            RewriteStep::Fresh("rec_v".into()),
            RewriteStep::Create {
                kind: "k".into(),
                payload: None,
                children: vec![RewriteStep::Apply {
                    rule_id: "r".into(),
                    index: 0,
                }],
            },
            RewriteStep::Apply {
                rule_id: "r2".into(),
                index: 3,
            },
        ];
        let j = serde_json::to_string(&steps).unwrap();
        let back: Vec<RewriteStep> = serde_json::from_str(&j).unwrap();
        assert_eq!(steps, back);

        let conds = vec![
            TransformCondition::KindAt {
                index: None,
                role: Some("key".into()),
                kind: "array".into(),
            },
            TransformCondition::PayloadEq {
                path: "p".into(),
                value: Value::from(true),
            },
            TransformCondition::ChildCount(0),
            TransformCondition::And(vec![]),
            TransformCondition::Or(vec![TransformCondition::ChildCount(1)]),
            TransformCondition::Not(Box::new(TransformCondition::ChildCount(9))),
        ];
        let j = serde_json::to_string(&conds).unwrap();
        let back: Vec<TransformCondition> = serde_json::from_str(&j).unwrap();
        assert_eq!(conds, back);
    }

    #[test]
    fn serde_skips_defaults() {
        let def = TransformDef::new("t", "desugar", "x", TransformRule::Native("n".into()));
        let j = serde_json::to_string(&def).unwrap();
        assert!(!j.contains("priority"));
        assert!(!j.contains("when"));
        assert!(!j.contains("replaces"));
        assert!(!j.contains("requires"));
        // Deserialize minimal input — defaults fill in.
        let back: TransformDef = serde_json::from_str(&j).unwrap();
        assert_eq!(back.priority, 0);
        assert!(back.when.is_none());
    }

    #[test]
    fn merge_collision_same_pass_kind_priority() {
        let mut set: FragmentSet<TransformDef> = FragmentSet::new();
        set.merge(TransformDef::new(
            "t1",
            "desugar",
            "x",
            TransformRule::Native("a".into()),
        ))
        .unwrap();
        // Same pass+kind+priority, different id → collision.
        let err = set
            .merge(TransformDef::new(
                "t2",
                "desugar",
                "x",
                TransformRule::Native("b".into()),
            ))
            .unwrap_err();
        assert_eq!(
            err,
            crate::LangError::Collision {
                existing: "t1".into(),
                incoming: "t2".into()
            }
        );
        // Different priority → distinct identity key → ok.
        set.merge(
            TransformDef::new("t3", "desugar", "x", TransformRule::Native("c".into()))
                .with_priority(1),
        )
        .unwrap();
        // Different pass → distinct identity key → ok.
        set.merge(TransformDef::new(
            "t4",
            "lower",
            "x",
            TransformRule::Native("d".into()),
        ))
        .unwrap();
        assert_eq!(set.len(), 3);
    }

    #[test]
    fn merge_replaces_overrides() {
        let mut set: FragmentSet<TransformDef> = FragmentSet::new();
        set.merge(TransformDef::new(
            "t1",
            "desugar",
            "x",
            TransformRule::Native("a".into()),
        ))
        .unwrap();
        set.merge(
            TransformDef::new("t2", "desugar", "x", TransformRule::Native("b".into()))
                .with_replaces(vec!["t1".into()]),
        )
        .unwrap();
        assert_eq!(set.len(), 1);
        assert!(set.get_by_id("t1").is_none());
        assert!(set.get_by_id("t2").is_some());
        assert_eq!(set.override_chain(), &[("t2".into(), "t1".into())]);
    }

    #[test]
    fn lower_desugar_rule_converts() {
        let rule = AstDesugarRule {
            target_kind: "binary.eq".into(),
            children: vec![
                AstDesugarChild::Keep(0),
                AstDesugarChild::KeepPath(vec![1, 0]),
                AstDesugarChild::KeepRest(2),
                AstDesugarChild::Create {
                    kind: "lit".into(),
                    payload: Some(Value::from(0)),
                    children: vec![AstDesugarChild::Keep(3)],
                },
            ],
            when: Some(AstDesugarCondition {
                child_index: 0,
                child_kind: "array".into(),
            }),
        };
        let def = lower_desugar_rule("entry", &rule);
        assert_eq!(def.id, "transform.desugar.entry");
        assert_eq!(def.pass, "desugar");
        assert_eq!(def.node_kind, "entry");
        assert_eq!(def.priority, 0);
        assert_eq!(
            def.when,
            Some(TransformCondition::KindAt {
                index: Some(0),
                role: None,
                kind: "array".into()
            })
        );
        match def.rule {
            TransformRule::Declarative {
                target_kind,
                children,
                payload,
            } => {
                assert_eq!(target_kind, "binary.eq");
                assert_eq!(payload, None);
                assert_eq!(
                    children,
                    vec![
                        RewriteStep::Keep(0),
                        RewriteStep::KeepPath(vec![1, 0]),
                        RewriteStep::KeepRest(2),
                        RewriteStep::Create {
                            kind: "lit".into(),
                            payload: Some(Value::from(0)),
                            children: vec![RewriteStep::Keep(3)],
                        },
                    ]
                );
            }
            _ => panic!("expected Declarative"),
        }
    }
}
