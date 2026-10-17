//! The `Fragment` trait — the common interface every fragment type implements.
//!
//! A fragment is one tiny concern of a `Language`: one token kind, one grammar
//! row, one eval scheme, one capability declaration, one option schema, or one
//! AST shape. Fragments carry an `id`, an optional `replaces` list (declared
//! override, see ADR-0044 §5), and an optional `requires` list (composability,
//! see ADR-0044 §7). Each fragment type also has a per-type **identity key**
//! used by [`FragmentSet`](crate::FragmentSet) to detect collisions.
//!
//! # `requires` vs `optional`
//!
//! Phase 1 models only the hard `requires` check: every id in `requires` must
//! be present after merge or the merge fails. The `optional` dependency
//! concept (silently ignored when absent) is **not** modeled as a field in
//! Phase 1 — a fragment with a missing optional dependency simply merges
//! successfully because it declares no `requires` for it. This keeps the data
//! schema minimal; `optional` may be added in a later phase if needed.

use serde::de::DeserializeOwned;

/// The common interface for all fragment types.
///
/// Every fragment type implements this so that [`FragmentSet`](crate::FragmentSet)
/// can drive merge, override, and `requires` validation generically.
pub trait Fragment:
    Clone + serde::Serialize + DeserializeOwned + PartialEq + std::fmt::Debug
{
    /// The stable identifier of this fragment.
    fn id(&self) -> &str;

    /// The ids this fragment declares it replaces (declared override).
    fn replaces(&self) -> &[String];

    /// The ids this fragment hard-requires to be present after merge.
    fn requires(&self) -> &[String];

    /// The per-type identity key used for collision detection.
    ///
    /// This is *not* necessarily `id` — see ADR-0044 §5 for the per-type table.
    fn identity_key(&self) -> String;

    /// Whether this fragment type uses union (idempotent) merge semantics.
    ///
    /// `CapabilityDecl` overrides this to `true`; all other types default to
    /// `false` (collision is an error without `replaces`).
    const UNION: bool = false;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fragments::CapabilityDecl;

    #[test]
    fn capability_is_union() {
        assert!(CapabilityDecl::UNION);
    }
}
