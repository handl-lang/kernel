//! Type rule fragment definitions (ADR-0054 — Generic Typecheck Engine).

use serde::{Deserialize, Serialize};

use crate::fragment::Fragment;
use crate::term::Term;

/// A mapping from an AST node kind to its typechecking [`Term`]s.
///
/// A type rule has a **synth** scheme (`Γ ⊢ node ⇒ T` — synthesize the type)
/// and an optional **check** scheme (`Γ ⊢ node ⇐ T` — verify against an
/// expected type). When `check` is `None`, the node falls back to
/// *synthesize-then-unify* against the expected type.
///
/// The schemes reuse the arrow-calculus kernel (`Term`) that `lang.eval`
/// uses, with judgment ops (`synth_child`, `check_child`, `unify`, `extend`,
/// `fresh_meta`, `solve_meta`, `lookup`, `quote`, `normalize`, `construct`,
/// `match_type`) available via `ArrSource::Judgment` (ADR-0054 §1, §2).
///
/// Identity key: `node_kind` (see ADR-0044 §5). Collision without `replaces`
/// is an error — a node kind has exactly one type rule.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct TypeRuleDef {
    /// Stable identifier (e.g. `"type.if"`).
    pub id: String,
    /// The AST node kind this rule typechecks.
    pub node_kind: String,
    /// Synthesis scheme: `Γ ⊢ node ⇒ T` (computes the type value).
    pub synth: Term,
    /// Check scheme: `Γ ⊢ node ⇐ T` (directed checking). `None` ⇒
    /// synth-then-unify against the expected type.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub check: Option<Term>,
    /// ids this fragment declares it replaces.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub replaces: Vec<String>,
    /// ids this fragment hard-requires.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub requires: Vec<String>,
}

impl TypeRuleDef {
    /// Create a new type rule with a synth scheme and no check scheme.
    pub fn new(id: impl Into<String>, node_kind: impl Into<String>, synth: Term) -> Self {
        Self {
            id: id.into(),
            node_kind: node_kind.into(),
            synth,
            check: None,
            replaces: Vec::new(),
            requires: Vec::new(),
        }
    }

    /// Attach a check scheme (builder style).
    pub fn with_check(mut self, check: Term) -> Self {
        self.check = Some(check);
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

impl Fragment for TypeRuleDef {
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
        self.node_kind.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::{ArrSource, Term};
    use plugin_engine::TermData;
    use serde_json::Value;

    /// Convert `TermData` back to `Term` for APIs that require `Term`.
    fn t(td: TermData) -> Term {
        td.to_term().expect("TermData -> Term conversion")
    }

    /// Judgment op without a literal payload (mirrors `TermData::op`).
    fn op_judgment(name: &str, args: Vec<TermData>) -> TermData {
        TermData::op(name, args, &ArrSource::Judgment, None)
    }

    /// Judgment op with a literal payload (mirrors `TermData::op`).
    fn op_judgment_lit(name: &str, args: Vec<TermData>, lit: impl Into<Value>) -> TermData {
        TermData::op(name, args, &ArrSource::Judgment, Some(lit.into()))
    }

    #[test]
    fn construct_and_accessors() {
        let def = TypeRuleDef::new(
            "type.lit",
            "lit",
            t(op_judgment_lit("synth_child", vec![], Value::from(0u64))),
        )
        .with_replaces(vec!["type.lit.old".into()])
        .with_requires(vec!["type.bool".into()]);
        assert_eq!(def.id(), "type.lit");
        assert_eq!(def.node_kind, "lit");
        assert!(def.check.is_none());
        assert_eq!(def.replaces(), &["type.lit.old".to_string()]);
        assert_eq!(def.requires(), &["type.bool".to_string()]);
        assert_eq!(def.identity_key(), "lit");
    }

    #[test]
    fn with_check_sets_check_scheme() {
        let def = TypeRuleDef::new(
            "type.lambda",
            "lambda",
            t(op_judgment("construct", vec![])),
        )
        .with_check(t(op_judgment("check_child", vec![])));
        assert!(def.check.is_some());
    }

    #[test]
    fn serde_roundtrip_synth_only() {
        let def = TypeRuleDef::new(
            "type.lit",
            "lit",
            t(op_judgment_lit("synth_child", vec![], Value::from(0u64))),
        );
        let j = serde_json::to_string(&def).unwrap();
        let back: TypeRuleDef = serde_json::from_str(&j).unwrap();
        assert_eq!(def, back);
    }

    #[test]
    fn serde_roundtrip_with_check() {
        let def = TypeRuleDef::new(
            "type.lambda",
            "lambda",
            t(op_judgment("construct", vec![])),
        )
        .with_check(t(op_judgment("check_child", vec![])));
        let j = serde_json::to_string(&def).unwrap();
        let back: TypeRuleDef = serde_json::from_str(&j).unwrap();
        assert_eq!(def, back);
    }

    #[test]
    fn serde_omits_check_when_none() {
        let def = TypeRuleDef::new("type.lit", "lit", t(op_judgment("id", vec![])));
        let j = serde_json::to_string(&def).unwrap();
        assert!(
            !j.contains("check"),
            "check should be omitted when None: {j}"
        );
    }

    #[test]
    fn equality() {
        let a = TypeRuleDef::new("a", "k", t(op_judgment("id", vec![])));
        let b = TypeRuleDef::new("a", "k", t(op_judgment("id", vec![])));
        assert_eq!(a, b);
    }
}
