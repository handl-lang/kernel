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
#[path = "fragment_set_test.rs"]
mod fragment_set_test;
