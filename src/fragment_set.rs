//! `FragmentSet<T>` — a mergeable collection of fragments with an explicit
//! conflict policy (ADR-0044 §5).
//!
//! Merge distinguishes **override** (a fragment declares `replaces: [id]`) from
//! **collision** (two fragments target the same identity key, neither declares
//! `replaces`). Overrides are allowed and recorded in an auditable
//! `override_chain`; collisions are errors. `CapabilityDecl` uses union
//! (idempotent) semantics instead.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use crate::error::LangError;
use crate::fragment::Fragment;

/// A mergeable collection of fragments of type `T`.
///
/// Fragments are keyed by their per-type **identity key** (see ADR-0044 §5),
/// not by `id`. A separate `id` index supports `replaces` and `requires`
/// resolution. The `override_chain` records every declared override as
/// `(incoming_id, replaced_id)` pairs, making the merge history auditable.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct FragmentSet<T> {
    /// Fragments keyed by identity key.
    by_key: BTreeMap<String, T>,
    /// Index from `id` to identity key, for `replaces`/`requires` resolution.
    id_index: BTreeMap<String, String>,
    /// The auditable override history: `(incoming_id, replaced_id)`.
    override_chain: Vec<(String, String)>,
}

impl<T: Fragment> Default for FragmentSet<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Fragment> FragmentSet<T> {
    /// Create an empty fragment set.
    pub fn new() -> Self {
        Self {
            by_key: BTreeMap::new(),
            id_index: BTreeMap::new(),
            override_chain: Vec::new(),
        }
    }

    /// Merge a fragment into the set.
    ///
    /// - If `fragment.replaces()` is non-empty: each replaced id must be
    ///   present (else [`LangError::UnknownReplace`]); the replaced fragments
    ///   are removed, the new one inserted, and the override recorded in
    ///   [`override_chain`](Self::override_chain). Cyclic `replaces` chains
    ///   yield [`LangError::CyclicReplace`].
    /// - If `replaces` is empty and the identity key is occupied: for union
    ///   types (`CapabilityDecl`) the merge is idempotent (keep one); for all
    ///   others it is a [`LangError::Collision`].
    /// - `requires` is validated against the post-merge id set; any missing id
    ///   yields [`LangError::MissingRequires`].
    ///
    /// # Errors
    ///
    /// Returns the appropriate [`LangError`] variant on failure. On failure no
    /// state is mutated.
    pub fn merge(&mut self, fragment: T) -> Result<(), LangError> {
        let id = fragment.id().to_string();
        let key = fragment.identity_key();
        let replaces = fragment.replaces().to_vec();
        let requires = fragment.requires().to_vec();

        // 1. Validate `replaces`.
        if !replaces.is_empty() {
            for rid in &replaces {
                if !self.id_index.contains_key(rid) {
                    return Err(LangError::UnknownReplace {
                        missing: rid.clone(),
                    });
                }
            }
            if let Some(chain) = self.detect_cycle(&id, &replaces) {
                return Err(LangError::CyclicReplace { chain });
            }
        }

        // 2. Collision / union check (only when not replacing).
        if replaces.is_empty()
            && let Some(existing) = self.by_key.get(&key)
        {
            if T::UNION {
                // Idempotent union: validate requires, then keep existing.
                let missing = self.missing_requires(&id, &replaces, &requires);
                if !missing.is_empty() {
                    return Err(LangError::MissingRequires { missing });
                }
                return Ok(());
            }
            return Err(LangError::Collision {
                existing: existing.id().to_string(),
                incoming: id,
            });
        }

        // 3. Validate `requires` against the post-merge id set.
        let missing = self.missing_requires(&id, &replaces, &requires);
        if !missing.is_empty() {
            return Err(LangError::MissingRequires { missing });
        }

        // 4. Commit.
        if !replaces.is_empty() {
            for rid in &replaces {
                // Safe: every replaced id was validated present above.
                let rkey = self.id_index.remove(rid).unwrap_or_default();
                self.by_key.remove(&rkey);
                self.override_chain.push((id.clone(), rid.clone()));
            }
            self.by_key.insert(key.clone(), fragment);
            self.id_index.insert(id, key);
        } else {
            self.by_key.insert(key.clone(), fragment);
            self.id_index.insert(id, key);
        }
        Ok(())
    }

    /// Compute the ids from `requires` that would be missing after merging
    /// `id` (with the given `replaces`).
    ///
    /// The post-merge id set is `id_index − replaces + {id}`; each
    /// requirement is tested against it directly rather than by
    /// materializing that set. Building the set cloned every fragment id on
    /// every merge, which made assembly quadratic in the fragment count.
    fn missing_requires(&self, id: &str, replaces: &[String], requires: &[String]) -> Vec<String> {
        requires
            .iter()
            .filter(|r| {
                let r = r.as_str();
                r != id && (replaces.iter().any(|rep| rep == r) || !self.id_index.contains_key(r))
            })
            .cloned()
            .collect()
    }

    /// Detect a `replaces` cycle involving the incoming `id`.
    ///
    /// Builds a directed graph from the existing `override_chain` plus the new
    /// `replaces` edges, then searches for a path from `id` back to `id`.
    fn detect_cycle(&self, id: &str, replaces: &[String]) -> Option<Vec<String>> {
        let mut adj: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for (nid, rep) in &self.override_chain {
            adj.entry(nid.clone()).or_default().push(rep.clone());
        }
        adj.entry(id.to_string())
            .or_default()
            .extend(replaces.iter().cloned());

        let mut visited: BTreeSet<String> = BTreeSet::new();
        let mut stack: Vec<(String, Vec<String>)> = vec![(id.to_string(), vec![id.to_string()])];
        while let Some((node, path)) = stack.pop() {
            if let Some(neighbors) = adj.get(&node) {
                for n in neighbors {
                    if n == id {
                        let mut chain = path.clone();
                        chain.push(n.clone());
                        return Some(chain);
                    }
                    if visited.insert(n.clone()) {
                        let mut p = path.clone();
                        p.push(n.clone());
                        stack.push((n.clone(), p));
                    }
                }
            }
        }
        None
    }

    /// Look up a fragment by its `id`.
    pub fn get_by_id(&self, id: &str) -> Option<&T> {
        self.id_index.get(id).and_then(|key| self.by_key.get(key))
    }

    /// Remove a fragment by its `id`, returning it if present.
    ///
    /// Used by [`Language::merge_ast_fragment`](crate::Language::merge_ast_fragment)
    /// to drop a stale synthesized [`TransformDef`](crate::TransformDef) when
    /// an `AstShapeDef` replacement removes a `desugar` rule (ADR-0094 §6).
    pub fn remove_by_id(&mut self, id: &str) -> Option<T> {
        let key = self.id_index.remove(id)?;
        self.by_key.remove(&key)
    }

    /// Look up a fragment by its **identity key** (see ADR-0044 §5).
    ///
    /// This is the per-type key returned by [`Fragment::identity_key`], which
    /// differs from `id` for some fragment types (e.g. `EvalSchemeDef` is keyed
    /// by `node_kind`, `GrammarRow` by `(token, position)`). Engines use this
    /// to resolve a node kind or token+position to its fragment directly,
    /// without iterating.
    ///
    /// Added in Phase 2 to support data-driven engine lookups
    /// (`lang.eval.get_by_identity(node.kind)`).
    pub fn get_by_identity(&self, key: &str) -> Option<&T> {
        self.by_key.get(key)
    }

    /// Iterate over the fragments (in identity-key order).
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.by_key.values()
    }

    /// Iterate over the fragments as a slice-like accessor.
    pub fn fragments(&self) -> impl Iterator<Item = &T> {
        self.by_key.values()
    }

    /// The override chain: `(incoming_id, replaced_id)` pairs.
    pub fn override_chain(&self) -> &[(String, String)] {
        &self.override_chain
    }

    /// The number of fragments in the set.
    pub fn len(&self) -> usize {
        self.by_key.len()
    }

    /// Whether the set is empty.
    pub fn is_empty(&self) -> bool {
        self.by_key.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fragments::grammar::{AstShapeRef, GrammarPosition};
    use crate::fragments::{CapabilityDecl, EvalSchemeDef, GrammarRow, OptionSchema, TokenKindDef};
    use crate::term::{ArrSource, Term};
    use plugin_engine::TermData;
    use serde_json::Value;

    /// Convert `TermData` back to `Term` for APIs that require `Term`.
    fn t(td: TermData) -> Term {
        td.to_term().expect("TermData -> Term conversion")
    }

    /// Native op with a literal payload (mirrors `TermData::op`).
    fn op_lit(name: &str, args: Vec<TermData>, lit: impl Into<Value>) -> TermData {
        if name == "const" && args.is_empty() {
            TermData::arr(lit.into())
        } else {
            TermData::op(name, args, &ArrSource::Native, Some(lit.into()))
        }
    }

    #[test]
    fn empty_set() {
        let set: FragmentSet<TokenKindDef> = FragmentSet::new();
        assert!(set.is_empty());
        assert_eq!(set.len(), 0);
        assert!(set.override_chain().is_empty());
    }

    #[test]
    fn default_is_empty() {
        let set: FragmentSet<TokenKindDef> = FragmentSet::default();
        assert!(set.is_empty());
    }

    #[test]
    fn single_merge() {
        let mut set: FragmentSet<TokenKindDef> = FragmentSet::new();
        set.merge(TokenKindDef::new("token.num")).unwrap();
        assert_eq!(set.len(), 1);
        assert!(set.get_by_id("token.num").is_some());
    }

    #[test]
    fn multi_merge() {
        let mut set: FragmentSet<TokenKindDef> = FragmentSet::new();
        set.merge(TokenKindDef::new("token.num")).unwrap();
        set.merge(TokenKindDef::new("token.str")).unwrap();
        set.merge(TokenKindDef::new("token.op")).unwrap();
        assert_eq!(set.len(), 3);
    }

    #[test]
    fn declared_override_records_chain() {
        let mut set: FragmentSet<TokenKindDef> = FragmentSet::new();
        set.merge(TokenKindDef::new("token.num")).unwrap();
        set.merge(TokenKindDef::new("token.num2").with_replaces(vec!["token.num".into()]))
            .unwrap();
        assert_eq!(set.len(), 1);
        assert!(set.get_by_id("token.num").is_none());
        assert!(set.get_by_id("token.num2").is_some());
        assert_eq!(
            set.override_chain(),
            &[("token.num2".into(), "token.num".into())]
        );
    }

    #[test]
    fn collision_without_replaces_errors() {
        // EvalSchemeDef is a non-union (behavioral) type: two schemes for the
        // same node_kind without `replaces` is a real conflict. (TokenKindDef
        // and AstShapeDef are now union types, so they can't demonstrate the
        // collision path.)
        let mut set: FragmentSet<EvalSchemeDef> = FragmentSet::new();
        set.merge(EvalSchemeDef::new(
            "eval.x",
            "x",
            t(op_lit("proj_child", vec![], Value::from(0u64))),
        ))
        .unwrap();
        // Same identity key (node_kind "x"), different id/content → collision.
        let err = set
            .merge(EvalSchemeDef::new(
                "eval.x2",
                "x",
                t(op_lit("proj_child", vec![], Value::from(1u64))),
            ))
            .unwrap_err();
        assert_eq!(
            err,
            LangError::Collision {
                existing: "eval.x".into(),
                incoming: "eval.x2".into()
            }
        );
        // Original unchanged.
        assert_eq!(set.len(), 1);
        assert!(set.get_by_id("eval.x").is_some());
    }

    #[test]
    fn unknown_replace_errors() {
        let mut set: FragmentSet<TokenKindDef> = FragmentSet::new();
        let err = set
            .merge(TokenKindDef::new("a").with_replaces(vec!["ghost".into()]))
            .unwrap_err();
        assert_eq!(
            err,
            LangError::UnknownReplace {
                missing: "ghost".into()
            }
        );
    }

    #[test]
    fn cyclic_replace_errors() {
        let mut set: FragmentSet<TokenKindDef> = FragmentSet::new();
        // B replaces A.
        set.merge(TokenKindDef::new("a")).unwrap();
        set.merge(TokenKindDef::new("b").with_replaces(vec!["a".into()]))
            .unwrap();
        // Now A (re-added) replaces B → cycle.
        let err = set
            .merge(TokenKindDef::new("a").with_replaces(vec!["b".into()]))
            .unwrap_err();
        assert_eq!(
            err,
            LangError::CyclicReplace {
                chain: vec!["a".into(), "b".into(), "a".into()]
            }
        );
    }

    #[test]
    fn diamond_replaces_no_cycle_revisits_node() {
        // Exercises detect_cycle's visited-revisit (false) and no-neighbors
        // (None) paths without forming a cycle.
        let mut set: FragmentSet<TokenKindDef> = FragmentSet::new();
        set.merge(TokenKindDef::new("d")).unwrap();
        set.merge(TokenKindDef::new("b").with_replaces(vec!["d".into()]))
            .unwrap();
        // Re-add d (it was removed by the replace).
        set.merge(TokenKindDef::new("d")).unwrap();
        set.merge(TokenKindDef::new("c").with_replaces(vec!["d".into()]))
            .unwrap();
        // a replaces [b, c] — diamond shape, no cycle.
        set.merge(TokenKindDef::new("a").with_replaces(vec!["b".into(), "c".into()]))
            .unwrap();
        assert!(set.get_by_id("a").is_some());
        assert!(set.get_by_id("b").is_none());
        assert!(set.get_by_id("c").is_none());
    }

    #[test]
    fn union_already_present_with_missing_requires_errors() {
        let mut set: FragmentSet<CapabilityDecl> = FragmentSet::new();
        set.merge(CapabilityDecl::new("fs.read")).unwrap();
        // Same id (union, occupied) but incoming requires an absent id.
        let err = set
            .merge(CapabilityDecl::new("fs.read").with_requires(vec!["fs.open".into()]))
            .unwrap_err();
        assert_eq!(
            err,
            LangError::MissingRequires {
                missing: vec!["fs.open".into()]
            }
        );
        // Existing unchanged.
        assert_eq!(set.len(), 1);
    }

    #[test]
    fn capability_union_idempotent() {
        let mut set: FragmentSet<CapabilityDecl> = FragmentSet::new();
        set.merge(CapabilityDecl::new("fs.read")).unwrap();
        set.merge(CapabilityDecl::new("fs.read")).unwrap();
        assert_eq!(set.len(), 1);
    }

    #[test]
    fn capability_distinct_ids_merge() {
        let mut set: FragmentSet<CapabilityDecl> = FragmentSet::new();
        set.merge(CapabilityDecl::new("fs.read")).unwrap();
        set.merge(CapabilityDecl::new("fs.write")).unwrap();
        assert_eq!(set.len(), 2);
    }

    #[test]
    fn grammar_identity_key_is_token_position() {
        let mut set: FragmentSet<GrammarRow> = FragmentSet::new();
        set.merge(GrammarRow::new(
            "g1",
            "token.plus",
            GrammarPosition::Infix,
            AstShapeRef::new("binary.add", 2),
        ))
        .unwrap();
        // Same token+position, different id → collision.
        let err = set
            .merge(GrammarRow::new(
                "g2",
                "token.plus",
                GrammarPosition::Infix,
                AstShapeRef::new("binary.add", 2),
            ))
            .unwrap_err();
        assert_eq!(
            err,
            LangError::Collision {
                existing: "g1".into(),
                incoming: "g2".into()
            }
        );
        // Same token, different position → ok.
        set.merge(GrammarRow::new(
            "g3",
            "token.plus",
            GrammarPosition::Prefix,
            AstShapeRef::new("unary.neg", 1),
        ))
        .unwrap();
        assert_eq!(set.len(), 2);
    }

    #[test]
    fn eval_scheme_identity_key_is_node_kind() {
        let mut set: FragmentSet<EvalSchemeDef> = FragmentSet::new();
        set.merge(EvalSchemeDef::new(
            "e1",
            "binary.add",
            t(op_lit("const", vec![], Value::Null)),
        ))
        .unwrap();
        let err = set
            .merge(EvalSchemeDef::new(
                "e2",
                "binary.add",
                t(op_lit("const", vec![], Value::Null)),
            ))
            .unwrap_err();
        assert_eq!(
            err,
            LangError::Collision {
                existing: "e1".into(),
                incoming: "e2".into()
            }
        );
    }

    #[test]
    fn option_identity_key_is_id() {
        let mut set: FragmentSet<OptionSchema> = FragmentSet::new();
        set.merge(OptionSchema::new("opt.x")).unwrap();
        let err = set
            .merge(OptionSchema::new("opt.x").with_default(Value::from(1)))
            .unwrap_err();
        assert_eq!(
            err,
            LangError::Collision {
                existing: "opt.x".into(),
                incoming: "opt.x".into()
            }
        );
    }

    #[test]
    fn requires_absent_errors() {
        let mut set: FragmentSet<TokenKindDef> = FragmentSet::new();
        let err = set
            .merge(TokenKindDef::new("token.call").with_requires(vec!["token.lparen".into()]))
            .unwrap_err();
        assert_eq!(
            err,
            LangError::MissingRequires {
                missing: vec!["token.lparen".into()]
            }
        );
    }

    #[test]
    fn requires_present_succeeds() {
        let mut set: FragmentSet<TokenKindDef> = FragmentSet::new();
        set.merge(TokenKindDef::new("token.lparen")).unwrap();
        set.merge(TokenKindDef::new("token.rparen")).unwrap();
        set.merge(
            TokenKindDef::new("token.call")
                .with_requires(vec!["token.lparen".into(), "token.rparen".into()]),
        )
        .unwrap();
        assert_eq!(set.len(), 3);
    }

    #[test]
    fn missing_optional_merges_successfully() {
        // `optional` is not a Phase 1 field; a fragment with no `requires`
        // for an absent dependency simply merges.
        let mut set: FragmentSet<TokenKindDef> = FragmentSet::new();
        set.merge(TokenKindDef::new("token.call")).unwrap();
        assert_eq!(set.len(), 1);
    }

    #[test]
    fn replace_then_requires_validates_against_post_merge_ids() {
        let mut set: FragmentSet<TokenKindDef> = FragmentSet::new();
        set.merge(TokenKindDef::new("token.lparen")).unwrap();
        set.merge(TokenKindDef::new("old")).unwrap();
        // Replacing `old` and requiring `token.lparen` (present) → ok.
        set.merge(
            TokenKindDef::new("new")
                .with_replaces(vec!["old".into()])
                .with_requires(vec!["token.lparen".into()]),
        )
        .unwrap();
        assert_eq!(set.len(), 2);
    }

    #[test]
    fn replace_removes_required_id_then_requires_fails() {
        let mut set: FragmentSet<TokenKindDef> = FragmentSet::new();
        set.merge(TokenKindDef::new("dep")).unwrap();
        set.merge(TokenKindDef::new("old")).unwrap();
        // Replacing `dep` (removing it) while requiring `dep` → fails.
        let err = set
            .merge(
                TokenKindDef::new("new")
                    .with_replaces(vec!["dep".into()])
                    .with_requires(vec!["dep".into()]),
            )
            .unwrap_err();
        assert_eq!(
            err,
            LangError::MissingRequires {
                missing: vec!["dep".into()]
            }
        );
        // Nothing mutated.
        assert!(set.get_by_id("dep").is_some());
        assert!(set.get_by_id("old").is_some());
    }

    #[test]
    fn union_requires_validated() {
        let mut set: FragmentSet<CapabilityDecl> = FragmentSet::new();
        let err = set
            .merge(CapabilityDecl::new("fs.read").with_requires(vec!["fs.open".into()]))
            .unwrap_err();
        assert_eq!(
            err,
            LangError::MissingRequires {
                missing: vec!["fs.open".into()]
            }
        );
    }

    #[test]
    fn serde_roundtrip() {
        let mut set: FragmentSet<TokenKindDef> = FragmentSet::new();
        set.merge(TokenKindDef::new("a")).unwrap();
        set.merge(TokenKindDef::new("b").with_replaces(vec!["a".into()]))
            .unwrap();
        let j = serde_json::to_string(&set).unwrap();
        let back: FragmentSet<TokenKindDef> = serde_json::from_str(&j).unwrap();
        assert_eq!(set, back);
    }

    #[test]
    fn get_by_identity_resolves_identity_key() {
        let mut set: FragmentSet<EvalSchemeDef> = FragmentSet::new();
        set.merge(EvalSchemeDef::new(
            "e1",
            "binary.add",
            t(op_lit("const", vec![], Value::Null)),
        ))
        .unwrap();
        // Identity key for EvalSchemeDef is node_kind, not id.
        assert!(set.get_by_identity("binary.add").is_some());
        assert!(set.get_by_identity("e1").is_none());
        assert!(set.get_by_identity("missing").is_none());
    }

    #[test]
    fn get_by_identity_resolves_grammar_token_position() {
        let mut set: FragmentSet<GrammarRow> = FragmentSet::new();
        set.merge(GrammarRow::new(
            "g1",
            "token.plus",
            GrammarPosition::Infix,
            AstShapeRef::new("binary.add", 2),
        ))
        .unwrap();
        // Identity key for GrammarRow is "token@position".
        assert!(set.get_by_identity("token.plus@infix").is_some());
        assert!(set.get_by_identity("token.plus@prefix").is_none());
    }
}
