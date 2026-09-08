//! Lint rule fragment definitions (ADR-0097 — Lint Rules as Language Data).
//!
//! A *lint rule* maps a check over source or AST to a diagnostic. Rules live
//! in the [`Language`](crate::Language) `lints` fragment set — adding a rule
//! to a language is a data change, never an engine recompile.
//!
//! This crate holds only the **data**: [`LintCheck`] and [`LintFix`] are the
//! rule *vocabulary* — they are interpreted by lint engines (e.g.
//! `plugin-engine-lint`), never executed here. The `Native` check variant is
//! the disciplined escape hatch (same pattern as [`TransformRule::Native`]):
//! dispatch stays in `LintRuleDef` data while the implementation — scope
//! analysis, whole-source checks, host-tool composition — is supplied by a
//! native-lint registry.
//!
//! # Serde representation
//!
//! All enums use serde's default **externally tagged** representation,
//! matching [`TransformRule`](crate::TransformRule) and friends: a check is
//! `{"Match": {"node_kind": …, "when": …}}` or `{"Native": "scope.unbound-wire"}`.
//!
//! [`TransformRule::Native`]: crate::TransformRule::Native

use serde::{Deserialize, Serialize};

use crate::fragment::Fragment;
use crate::fragments::transform_def::TransformCondition;

/// A single lint rule: a check plus the diagnostic it produces
/// (ADR-0097 §2).
///
/// `id` is the fragment identity (`"lint.scope.unbound-wire"`); `name` is
/// the rule name reported on diagnostics (`"unbound-wire"`) — several rules
/// may share a `name` when they are alternative match arms of one logical
/// rule (e.g. a `dead-branch` rule per constant guard value).
///
/// `severity` is one of `"error"`, `"warning"`, `"info"`. `message` is a
/// template: `{name}`-style placeholders are filled from the match context
/// (`{source}`, `{source:<role>}`, `{payload}`) for `Match` checks, or from
/// the argument map a native returns for `Native` checks.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct LintRuleDef {
    /// Stable fragment identifier (e.g. `"lint.dead-branch.if.true"`).
    pub id: String,
    /// The rule name reported on diagnostics (e.g. `"dead-branch"`).
    pub name: String,
    /// Diagnostic severity: `"error"`, `"warning"`, or `"info"`.
    pub severity: String,
    /// Diagnostic message template (`{key}` placeholders).
    pub message: String,
    /// The check detecting violations.
    pub check: LintCheck,
    /// Optional fix attached to each diagnostic this rule emits. For
    /// `Match` checks the fix is computed declaratively from the matched
    /// node; `Native` checks return their fixes directly and ignore this.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub fix: Option<LintFix>,
    /// ids this fragment declares it replaces.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub replaces: Vec<String>,
    /// ids this fragment hard-requires.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub requires: Vec<String>,
}

/// How a [`LintRuleDef`] detects violations (ADR-0097 §3).
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum LintCheck {
    /// Node-local match: the rule fires on every AST node of `node_kind`
    /// that satisfies `when` (a [`TransformCondition`], evaluated against the
    /// node in its arena — the same predicate vocabulary the transform
    /// engine interprets, ADR-0094 §3).
    Match {
        /// The AST node kind to match (the dispatch key).
        node_kind: String,
        /// Optional condition gating the match.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        when: Option<TransformCondition>,
    },
    /// A named native check (e.g. `"scope.unbound-wire"`,
    /// `"source.missing-module-doc"`), resolved against the native-lint
    /// registry the lint engine is wired with. Natives see the whole module —
    /// all parsed statements plus the source text — so they can express
    /// scope analysis and whole-source checks that node-local matching
    /// cannot.
    Native(String),
}

/// How a `Match`-checked [`LintRuleDef`] computes its fix (ADR-0097 §4).
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum LintFix {
    /// Replace the matched node's source text with the source text of one
    /// child, resolved by named `role` (ADR-0081) with positional `index`
    /// fallback. Used for wrapper-removal rules such as `simplify-paren`.
    Unwrap {
        /// The positional child index (role-less fallback).
        #[serde(default, skip_serializing_if = "Option::is_none")]
        index: Option<usize>,
        /// The named child role to unwrap.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        role: Option<String>,
    },
}

impl LintRuleDef {
    /// Create a new lint rule with no fix and empty `replaces`/`requires`.
    pub fn new(
        id: impl Into<String>,
        name: impl Into<String>,
        severity: impl Into<String>,
        message: impl Into<String>,
        check: LintCheck,
    ) -> Self {
        Self {
            id: id.into(),
            name: name.into(),
            severity: severity.into(),
            message: message.into(),
            check,
            fix: None,
            replaces: Vec::new(),
            requires: Vec::new(),
        }
    }

    /// Attach a declarative fix.
    pub fn with_fix(mut self, fix: LintFix) -> Self {
        self.fix = Some(fix);
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

impl Fragment for LintRuleDef {
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
        self.id.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fragment_set::FragmentSet;

    #[test]
    fn serde_roundtrip_match_and_native() {
        let rules = vec![
            LintRuleDef::new(
                "lint.simplify-paren",
                "simplify-paren",
                "warning",
                "redundant parentheses around '{source:body}'",
                LintCheck::Match {
                    node_kind: "paren".into(),
                    when: Some(TransformCondition::ChildCount(1)),
                },
            )
            .with_fix(LintFix::Unwrap {
                index: None,
                role: Some("body".into()),
            }),
            LintRuleDef::new(
                "lint.scope.unbound-wire",
                "unbound-wire",
                "error",
                "reference to unbound name '{name}'",
                LintCheck::Native("scope.unbound-wire".into()),
            ),
        ];
        let j = serde_json::to_string(&rules).unwrap();
        let back: Vec<LintRuleDef> = serde_json::from_str(&j).unwrap();
        assert_eq!(rules, back);
    }

    #[test]
    fn serde_skips_defaults() {
        let def = LintRuleDef::new(
            "lint.x",
            "x",
            "warning",
            "msg",
            LintCheck::Native("n".into()),
        );
        let j = serde_json::to_string(&def).unwrap();
        assert!(!j.contains("fix"));
        assert!(!j.contains("replaces"));
        assert!(!j.contains("requires"));
    }

    #[test]
    fn merge_collision_same_id() {
        let mut set: FragmentSet<LintRuleDef> = FragmentSet::new();
        set.merge(LintRuleDef::new(
            "lint.a",
            "a",
            "warning",
            "m",
            LintCheck::Native("n".into()),
        ))
        .unwrap();
        // A different id is NOT a collision — `id` is the identity key.
        set.merge(LintRuleDef::new(
            "lint.b",
            "b",
            "warning",
            "m",
            LintCheck::Match {
                node_kind: "x".into(),
                when: None,
            },
        ))
        .unwrap();
        // Same id, different content, no `replaces` → collision.
        let err = set
            .merge(LintRuleDef::new(
                "lint.a",
                "a2",
                "warning",
                "m",
                LintCheck::Native("n2".into()),
            ))
            .unwrap_err();
        assert_eq!(
            err,
            crate::LangError::Collision {
                existing: "lint.a".into(),
                incoming: "lint.a".into()
            }
        );
        // `replaces` overrides cleanly.
        set.merge(
            LintRuleDef::new(
                "lint.a.v2",
                "a",
                "warning",
                "m",
                LintCheck::Native("n3".into()),
            )
            .with_replaces(vec!["lint.a".into()]),
        )
        .unwrap();
        assert!(set.get_by_id("lint.a").is_none());
        assert!(set.get_by_id("lint.a.v2").is_some());
    }
}
