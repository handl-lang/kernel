//! Desugar rules — data rewrites that lower surface constructs to core
//! [`Scheme`]s (ADR-0044 §4 "Small core + desugar").
//!
//! A rule matches a node kind and produces a core `Scheme`. Adding a surface
//! construct is adding a rewrite rule (data), not extending the combinator
//! set. This module is a pure data rewrite — no Rust closures.

use crate::scheme::Scheme;

/// A desugar rule: matches a node kind and produces a core [`Scheme`].
#[derive(Debug, Clone, PartialEq)]
pub struct DesugarRule {
    /// The node kind this rule matches.
    pub matches: String,
    /// The core scheme this rule produces.
    pub produces: Scheme,
}

impl DesugarRule {
    /// Create a new desugar rule.
    pub fn new(matches: impl Into<String>, produces: Scheme) -> Self {
        Self {
            matches: matches.into(),
            produces,
        }
    }
}

/// Resolve a node kind to its core [`Scheme`] via the given desugar rules.
///
/// Returns `None` if no rule matches the kind. This is a data rewrite — it
/// performs a linear scan of `rules` and returns the first match.
pub fn desugar(rules: &[DesugarRule], node_kind: &str) -> Option<Scheme> {
    rules
        .iter()
        .find(|r| r.matches == node_kind)
        .map(|r| r.produces.clone())
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::Value;

    #[test]
    fn rule_matches_and_produces() {
        // ternary: cond >>> arr(tag) >>> Choice(then, else)
        let produced_scheme = Scheme::seq(
            Scheme::seq(
                Scheme::arr_native_lit("proj_child", vec![], Value::from(0u64)),
                Scheme::arr_native("tag", vec![]),
            ),
            Scheme::choice(
                Scheme::arr_native_lit("proj_child", vec![], Value::from(1u64)),
                Scheme::arr_native_lit("proj_child", vec![], Value::from(2u64)),
            ),
        );
        let rules = vec![DesugarRule::new("ternary", produced_scheme.clone())];
        let produced = desugar(&rules, "ternary").unwrap();
        assert_eq!(produced, produced_scheme);
    }

    #[test]
    fn unmatched_kind_returns_none() {
        let rules = vec![DesugarRule::new(
            "ternary",
            Scheme::arr_native_lit("const", vec![], Value::Null),
        )];
        assert!(desugar(&rules, "binary.add").is_none());
    }

    #[test]
    fn empty_rules_returns_none() {
        assert!(desugar(&[], "anything").is_none());
    }

    #[test]
    fn first_match_wins() {
        let rules = vec![
            DesugarRule::new("k", Scheme::arr_native_lit("const", vec![], Value::from(1))),
            DesugarRule::new("k", Scheme::arr_native_lit("const", vec![], Value::from(2))),
        ];
        let produced = desugar(&rules, "k").unwrap();
        assert_eq!(
            produced,
            Scheme::arr_native_lit("const", vec![], Value::from(1))
        );
    }
}
