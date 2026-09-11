//! Desugar rules — data rewrites that lower surface constructs to core
//! [`Term`]s (ADR-0044 §4 "Small core + desugar").
//!
//! A rule matches a node kind and produces a core `Term`. Adding a surface
//! construct is adding a rewrite rule (data), not extending the combinator
//! set. This module is a pure data rewrite — no Rust closures.

use crate::term::Term;

/// A desugar rule: matches a node kind and produces a core [`Term`].
#[derive(Debug, Clone, PartialEq)]
pub struct DesugarRule {
    /// The node kind this rule matches.
    pub matches: String,
    /// The core scheme this rule produces.
    pub produces: Term,
}

impl DesugarRule {
    /// Create a new desugar rule.
    pub fn new(matches: impl Into<String>, produces: Term) -> Self {
        Self {
            matches: matches.into(),
            produces,
        }
    }
}

/// Resolve a node kind to its core [`Term`] via the given desugar rules.
///
/// Returns `None` if no rule matches the kind. This is a data rewrite — it
/// performs a linear scan of `rules` and returns the first match.
pub fn desugar(rules: &[DesugarRule], node_kind: &str) -> Option<Term> {
    rules
        .iter()
        .find(|r| r.matches == node_kind)
        .map(|r| r.produces.clone())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::ArrSource;
    use plugin_engine::TermData;
    use serde_json::Value;

    /// Convert `TermData` back to `Term` for APIs that require `Term`.
    fn t(td: TermData) -> Term {
        td.to_term().expect("TermData -> Term conversion")
    }

    /// Native op without a literal payload (mirrors `Term::arr_native`).
    fn op_native(name: &str, args: Vec<TermData>) -> TermData {
        if name == "const" && args.is_empty() {
            TermData::arr(Value::Null)
        } else {
            TermData::op(name, args, &ArrSource::Native, None)
        }
    }

    /// Native op with a literal payload (mirrors `Term::arr_native_lit`).
    fn op_lit(name: &str, args: Vec<TermData>, lit: impl Into<Value>) -> TermData {
        if name == "const" && args.is_empty() {
            TermData::arr(lit.into())
        } else {
            TermData::op(name, args, &ArrSource::Native, Some(lit.into()))
        }
    }

    #[test]
    fn rule_matches_and_produces() {
        // ternary: cond >>> arr(tag) >>> Choice(then, else)
        let produced_scheme = t(TermData::seq(
            TermData::seq(
                op_lit("proj_child", vec![], Value::from(0u64)),
                op_native("tag", vec![]),
            ),
            TermData::choice(
                op_lit("proj_child", vec![], Value::from(1u64)),
                op_lit("proj_child", vec![], Value::from(2u64)),
            ),
        ));
        let rules = vec![DesugarRule::new("ternary", produced_scheme.clone())];
        let produced = desugar(&rules, "ternary").unwrap();
        assert_eq!(produced, produced_scheme);
    }

    #[test]
    fn unmatched_kind_returns_none() {
        let rules = vec![DesugarRule::new(
            "ternary",
            t(op_lit("const", vec![], Value::Null)),
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
            DesugarRule::new("k", t(op_lit("const", vec![], Value::from(1)))),
            DesugarRule::new("k", t(op_lit("const", vec![], Value::from(2)))),
        ];
        let produced = desugar(&rules, "k").unwrap();
        assert_eq!(produced, t(op_lit("const", vec![], Value::from(1))));
    }
}
