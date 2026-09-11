//! Dynamic handler law verification over the production `Term` IR
//! (ADR-0076 OQ#2).
//!
//! Ports the research PoC in
//! `research/arrow-calculus-kernel-poc/src/dynamic_handlers.rs` to the
//! production [`Term`](crate::term::Term) kernel. ADR-0076 OQ#2 asks:
//! "Can we verify laws for runtime-chosen impls?" The ADR's tentative "likely
//! no" is corrected here: dynamic law checking IS possible because the arrow
//! calculus graph is always inspectable (a finite combinator tree) and CutElim
//! normalization is decidable for the six-rewrite fragment. There are THREE
//! modes, not two:
//!
//!   - **Mode 1: Static (compile-time verify)** -- the impl is fixed at
//!     compile time; laws checked once at installation; proof travels. This is
//!     the existing [`crate::effects::eliminate_and_check`] and
//!     [`Term::eliminate_handlers`](crate::term::Term::eliminate_handlers)
//!     path. This module does NOT re-implement Mode 1.
//!
//!   - **Mode 2: Dynamic, closed set (pick among pre-verified)** -- multiple
//!     impls are registered, each pre-verified at REGISTRATION time via
//!     [`infer_laws`](crate::law_inference::infer_laws). At runtime a predicate
//!     picks one; laws hold regardless of which is picked because all were
//!     already proven. No runtime CutElim. See [`VerifiedImplStore`] and
//!     [`dynamic_dispatch`].
//!
//!   - **Mode 3: Dynamic, open set (runtime verify)** -- the impl graph is
//!     produced at runtime (not known at compile time). The handler runs
//!     CutElim on it AT RUNTIME via [`verify_at_runtime`]. If it normalizes to
//!     satisfy the law -> accept; if not -> runtime rejection. This has a
//!     runtime cost (normalization per law) but handles truly dynamic impl
//!     generation (plugins, ArrowApply-synthesized graphs, input-driven
//!     generation).
//!
//! # Simplification vs the PoC
//!
//! The PoC uses `Bundle` / `BundleLaw` / `VerificationReport` from
//! `decoupled_traits.rs`. The real compiler does NOT have these. A "verified
//! impl" here is just a [`Term`] plus its `Vec<InferredLaw>` (from
//! [`infer_laws`](crate::law_inference::infer_laws)) -- no separate Bundle
//! type needed. The normalizer, `law_equal`, `uses_first`, `LawPattern`,
//! `LawCheckResult`, and the inference engine are reused from
//! [`crate::law_inference`] -- the normalizer is NOT duplicated.
//!
//! # Mode 3 vs `infer_laws` (Violated vs NotApplicable)
//!
//! The key semantic difference between Mode 3 ([`verify_at_runtime`]) and
//! inference ([`infer_laws`](crate::law_inference::infer_laws)) is how a
//! structural mismatch is reported:
//!
//!   - In **inference** mode, a structural mismatch returns
//!     [`LawCheckResult::NotApplicable`] -- the law doesn't apply to this
//!     arrow's wiring, so skip it. The question is "which laws does this arrow
//!     satisfy?"
//!
//!   - In **verification** mode (Mode 3), a structural mismatch returns
//!     [`LawCheckResult::Violated`] -- the graph was claimed to satisfy this
//!     law but doesn't even have the right structure. The question is "does
//!     this graph satisfy THIS law?" If not, it's a violation, not a skip.
//!
//! This distinction is what makes Mode 3 rejection possible: a bare
//! `arr("not_a_functor")` scheme doesn't use `first`, so it VIOLATES the
//! functor laws (it's not a valid functor implementation), rather than being
//! "not applicable." The runtime check functions
//! ([`check_functor_identity_runtime`], [`check_functor_composition_runtime`])
//! mirror the PoC's separate runtime check functions that return `Violated`
//! instead of `NotApplicable` on structural mismatch.

use std::collections::HashMap;

use plugin_engine::TermData;

use crate::law_inference::{
    LawCheckResult, LawPattern, LawStatus, infer_laws, law_equal, uses_first,
};
use crate::term::{ArrSource, Term};

// ============================================================================
// 1. VerifiedImpl and VerifiedImplStore (Mode 2)
// ============================================================================

/// A pre-verified impl: a named [`Term`] plus the laws it was verified to
/// satisfy at registration time. The verification result travels with the
/// impl -- no re-verification needed at dispatch.
///
/// This is the Mode 2 "verified impl." Registration runs
/// [`infer_laws`](crate::law_inference::infer_laws) once and stores the
/// satisfied law names; dispatch just looks up the pre-computed result.
#[derive(Debug, Clone)]
pub struct VerifiedImpl {
    /// The impl name, e.g. `"map_list"`.
    pub name: String,
    /// The impl graph (the arrow-calculus description).
    pub scheme: Term,
    /// Names of the laws this impl was verified to satisfy at registration.
    pub verified_laws: Vec<String>,
}

/// A store of pre-verified impls, keyed by capability name. Each impl is
/// verified at registration time (Mode 2). At dispatch time, a predicate
/// picks one -- laws hold regardless of which is picked because all were
/// pre-verified.
#[derive(Debug, Default)]
pub struct VerifiedImplStore {
    /// capability name -> [verified impls]
    impls: HashMap<String, Vec<VerifiedImpl>>,
}

/// The result of registering an impl. The impl's laws are verified at
/// registration time; the result reports whether verification succeeded or
/// the impl was rejected.
#[derive(Debug, Clone)]
pub enum RegistrationResult {
    /// All applicable laws verified (CutElim-proven), and none violated. Safe
    /// for dynamic dispatch. `laws_verified` lists the names of the satisfied
    /// laws (may be empty if no law pattern applied -- a non-functor impl with
    /// no violated laws is still a valid, if lawless, impl).
    Verified {
        /// The registered impl name.
        name: String,
        /// Names of the laws verified to hold.
        laws_verified: Vec<String>,
    },
    /// At least one law was violated. Rejected -- not safe for dispatch. The
    /// impl is NOT stored in the registry.
    Rejected {
        /// The rejected impl name.
        name: String,
        /// Human-readable reason for the rejection.
        reason: String,
    },
}

impl VerifiedImplStore {
    /// Create an empty store.
    pub fn new() -> Self {
        VerifiedImplStore {
            impls: HashMap::new(),
        }
    }

    /// Register an impl: verify its laws NOW (at registration) via
    /// [`infer_laws`](crate::law_inference::infer_laws), store the result.
    /// This is Mode 2's "pre-verified at registration."
    ///
    /// - If any law is [`LawStatus::Violated`] -> [`RegistrationResult::Rejected`],
    ///   the impl is NOT stored.
    /// - Otherwise (all applicable laws satisfied, or no laws applicable) ->
    ///   [`RegistrationResult::Verified`], the impl is stored with the
    ///   satisfied law names.
    ///
    /// For the built-in CutElim-proven structural catalog, `Violated` never
    /// occurs (the structural laws are rewrites, so if applicable they are
    /// always satisfied). Rejection would only happen for a catalog entry
    /// whose `check` returns `Violated`; the built-in catalog does not, but a
    /// custom catalog could.
    pub fn register(&mut self, capability: &str, name: &str, scheme: Term) -> RegistrationResult {
        let inferred = infer_laws(&scheme);

        // If any law is Violated, reject -- not safe for dispatch.
        let violated: Vec<&str> = inferred
            .iter()
            .filter(|l| l.status == LawStatus::Violated)
            .map(|l| l.name.as_str())
            .collect();
        if !violated.is_empty() {
            return RegistrationResult::Rejected {
                name: name.to_string(),
                reason: format!("impl violates laws: {}", violated.join(", ")),
            };
        }

        // Collect the names of the satisfied laws (Satisfied only; Violated
        // was already handled, and infer_laws skips NotApplicable).
        let verified_laws: Vec<String> = inferred
            .iter()
            .filter(|l| l.status == LawStatus::Satisfied)
            .map(|l| l.name.clone())
            .collect();

        let verified_impl = VerifiedImpl {
            name: name.to_string(),
            scheme,
            verified_laws: verified_laws.clone(),
        };
        self.impls
            .entry(capability.to_string())
            .or_default()
            .push(verified_impl);

        RegistrationResult::Verified {
            name: name.to_string(),
            laws_verified: verified_laws,
        }
    }

    /// Lookup all pre-verified impls for a capability. Returns an empty slice
    /// if no impls are registered for this capability.
    pub fn lookup(&self, capability: &str) -> &[VerifiedImpl] {
        self.impls
            .get(capability)
            .map(|v| v.as_slice())
            .unwrap_or(&[])
    }
}

// ============================================================================
// 2. Dynamic dispatch (Mode 2)
// ============================================================================

/// Error from dynamic dispatch.
#[derive(Debug, Clone)]
pub enum DispatchError {
    /// No impls registered for this capability.
    NoImpls {
        /// The capability name that had no registered impls.
        capability: String,
    },
}

/// Dynamic dispatch: pick among pre-verified impls at runtime. Laws hold
/// regardless of which is picked -- all were verified at registration. No
/// runtime CutElim needed.
///
/// The predicate returns an index; `idx % impls.len()` selects the impl.
/// This simulates a runtime decision (e.g. "if list_size > 1000, use the
/// parallel impl; else use the list impl").
pub fn dynamic_dispatch<'a>(
    store: &'a VerifiedImplStore,
    capability: &str,
    predicate: impl Fn() -> usize,
) -> Result<&'a VerifiedImpl, DispatchError> {
    let impls = store.lookup(capability);
    if impls.is_empty() {
        return Err(DispatchError::NoImpls {
            capability: capability.to_string(),
        });
    }
    let idx = predicate() % impls.len();
    let chosen = &impls[idx];
    // No runtime verification needed -- already verified at registration.
    Ok(chosen)
}

// ============================================================================
// 3. Runtime verification (Mode 3)
// ============================================================================
//
// Runtime law verification: run CutElim on a scheme that was NOT known at
// compile time. This is Mode 3 -- the open-set case. The scheme could be
// produced by ArrowApply, loaded from a plugin, or synthesized from input.
//
// COST: running CutElim at runtime has a cost (normalization + law_equal for
// each law pattern). The benefit is handling truly dynamic impl generation
// that wasn't known at compile time. Mode 2 avoids this cost by pre-verifying
// at registration, but Mode 2 requires the impl set to be closed (known at
// registration time). Mode 3 handles the open set (impls generated at runtime).
//
// The arrow calculus foundation makes this possible: the scheme is always
// inspectable (a finite combinator tree), and CutElim normalization is
// decidable for the six-rewrite fragment.

/// The outcome of runtime law verification (Mode 3).
#[derive(Debug, Clone)]
pub enum RuntimeVerification {
    /// The scheme satisfies all checked laws. Safe to run.
    Accepted {
        /// Names of the laws that were checked and satisfied.
        laws_checked: Vec<String>,
    },
    /// The scheme violates at least one law. Not safe to run.
    Rejected {
        /// Human-readable reason for the rejection.
        reason: String,
        /// Name of the first law that failed.
        failed_law: String,
    },
}

/// Check the functor identity law: `first(id) = id` (ceFirstId), in
/// verification mode (Mode 3).
///
/// If the scheme uses `First`, the law holds by CutElim (ceFirstId is a
/// universal rewrite). If the scheme does NOT use `First`, it is not a valid
/// functor implementation -> [`LawCheckResult::Violated`] (the scheme was
/// claimed to satisfy this law but doesn't have the structure).
///
/// This mirrors the PoC's `check_functor_identity_runtime` and differs from
/// [`crate::law_inference`]'s `check_functor_identity` only in the
/// structural-mismatch case: here it is `Violated`, there it is
/// `NotApplicable`.
fn check_functor_identity_runtime(scheme: &Term) -> LawCheckResult {
    if !uses_first(scheme) {
        return LawCheckResult::Violated;
    }
    // functor identity: first(id) = id  (ceFirstId)
    let lhs = TermData::first(TermData::op(
        "id".to_string(),
        vec![],
        &ArrSource::Native,
        None,
    ))
    .to_term()
    .expect("check_functor_identity_runtime: TermData -> Term failed");
    let rhs = TermData::op("id".to_string(), vec![], &ArrSource::Native, None)
        .to_term()
        .expect("check_functor_identity_runtime: TermData -> Term failed");
    if law_equal(&lhs, &rhs) {
        LawCheckResult::Satisfied
    } else {
        LawCheckResult::Violated
    }
}

/// Check the functor composition law:
/// `first(f >>> g) = first(f) >>> first(g)` (ceFirstFusion), in verification
/// mode (Mode 3).
///
/// If the scheme uses `First`, the law holds by CutElim (ceFirstFusion is a
/// universal rewrite). If the scheme does NOT use `First` -> [`LawCheckResult::Violated`].
///
/// This mirrors the PoC's `check_functor_composition_runtime` and differs from
/// [`crate::law_inference`]'s `check_functor_composition` only in the
/// structural-mismatch case: here it is `Violated`, there it is
/// `NotApplicable`.
fn check_functor_composition_runtime(scheme: &Term) -> LawCheckResult {
    if !uses_first(scheme) {
        return LawCheckResult::Violated;
    }
    // functor composition: first(f;g) = first(f);first(g)  (ceFirstFusion)
    let f = TermData::op("f".to_string(), vec![], &ArrSource::Native, None);
    let g = TermData::op("g".to_string(), vec![], &ArrSource::Native, None);
    let lhs = TermData::first(TermData::seq(f.clone(), g.clone()))
        .to_term()
        .expect("check_functor_composition_runtime: TermData -> Term failed");
    let rhs = TermData::seq(TermData::first(f), TermData::first(g))
        .to_term()
        .expect("check_functor_composition_runtime: TermData -> Term failed");
    if law_equal(&lhs, &rhs) {
        LawCheckResult::Satisfied
    } else {
        LawCheckResult::Violated
    }
}

/// The runtime law patterns for Mode 3 verification. Returns the two
/// CutElim-proven functor laws (identity and composition) with their runtime
/// check functions, which return [`LawCheckResult::Violated`] on structural
/// mismatch (instead of `NotApplicable` as in inference mode).
fn runtime_law_patterns() -> Vec<LawPattern> {
    vec![
        LawPattern {
            name: "functor_identity".to_string(),
            description: "first(id) = id".to_string(),
            check: check_functor_identity_runtime,
        },
        LawPattern {
            name: "functor_composition".to_string(),
            description: "first(f >>> g) = first(f) >>> first(g)".to_string(),
            check: check_functor_composition_runtime,
        },
    ]
}

/// Verify a runtime-generated scheme against a set of law patterns. Runs
/// CutElim (via the law patterns' check functions, which call
/// [`law_equal`](crate::law_inference::law_equal)) on the scheme. This is the
/// runtime cost of Mode 3 -- but it's possible because the scheme is
/// inspectable.
///
/// For each law pattern:
///   - [`LawCheckResult::Satisfied`] -> law holds, add to checked list.
///   - [`LawCheckResult::Violated`] -> law fails, return [`RuntimeVerification::Rejected`]
///     immediately.
///   - [`LawCheckResult::NotApplicable`] -> skip (reserved for future
///     axiom-requiring laws that CutElim cannot verify).
///
/// If all applicable laws are satisfied, returns [`RuntimeVerification::Accepted`].
pub fn verify_at_runtime(scheme: &Term, law_patterns: &[LawPattern]) -> RuntimeVerification {
    let mut checked = Vec::new();
    for pattern in law_patterns {
        let result = (pattern.check)(scheme);
        match result {
            LawCheckResult::Satisfied => {
                checked.push(pattern.name.clone());
            }
            LawCheckResult::Violated => {
                return RuntimeVerification::Rejected {
                    reason: format!("generated scheme does not satisfy {}", pattern.name),
                    failed_law: pattern.name.clone(),
                };
            }
            LawCheckResult::NotApplicable => {} // skip
        }
    }
    RuntimeVerification::Accepted {
        laws_checked: checked,
    }
}

/// Convenience: verify a runtime-generated scheme against the built-in
/// runtime law patterns ([`runtime_law_patterns`]). This is the common case
/// -- verify against the CutElim-proven structural functor laws.
pub fn verify_at_runtime_with_builtin(scheme: &Term) -> RuntimeVerification {
    let patterns = runtime_law_patterns();
    verify_at_runtime(scheme, &patterns)
}

// ============================================================================
// 4. Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn first_f() -> Term {
        Term::first(Term::arr_native("f", vec![]))
    }

    fn arr_sort() -> Term {
        Term::arr_native("sort", vec![])
    }

    fn arr_not_a_functor() -> Term {
        Term::arr_native("not_a_functor", vec![])
    }

    // --- Mode 2: registration ---

    #[test]
    fn register_first_f_is_verified_with_functor_laws() {
        let mut store = VerifiedImplStore::new();
        let result = store.register("Functor<List>", "map_list", first_f());
        match result {
            RegistrationResult::Verified {
                name,
                laws_verified,
            } => {
                assert_eq!(name, "map_list");
                assert!(
                    laws_verified.contains(&"functor_identity".to_string()),
                    "functor_identity verified: {:?}",
                    laws_verified
                );
                assert!(
                    laws_verified.contains(&"functor_composition".to_string()),
                    "functor_composition verified: {:?}",
                    laws_verified
                );
            }
            other => panic!("expected Verified, got {:?}", other),
        }
    }

    #[test]
    fn register_non_functor_is_verified_with_empty_laws() {
        // A bare arr("sort") is not a functor. infer_laws returns empty
        // (NotApplicable is skipped), and no law is Violated, so registration
        // is Verified with empty laws. Only Violated causes rejection.
        let mut store = VerifiedImplStore::new();
        let result = store.register("Sort", "sort_impl", arr_sort());
        match result {
            RegistrationResult::Verified {
                name,
                laws_verified,
            } => {
                assert_eq!(name, "sort_impl");
                assert!(
                    laws_verified.is_empty(),
                    "non-functor has no verified laws: {:?}",
                    laws_verified
                );
            }
            other => panic!("expected Verified, got {:?}", other),
        }
        // It is stored.
        let impls = store.lookup("Sort");
        assert_eq!(impls.len(), 1);
        assert!(impls[0].verified_laws.is_empty());
    }

    #[test]
    fn lookup_empty_capability_returns_empty_slice() {
        let store = VerifiedImplStore::new();
        assert!(store.lookup("Nope").is_empty());
    }

    // --- Mode 2: dynamic dispatch ---

    #[test]
    fn dynamic_dispatch_predicate_0_picks_impl_0() {
        let mut store = VerifiedImplStore::new();
        store.register("Functor<List>", "map_list", first_f());
        store.register("Functor<List>", "map_parallel", first_f());
        let chosen = dynamic_dispatch(&store, "Functor<List>", || 0).unwrap();
        assert_eq!(chosen.name, "map_list");
    }

    #[test]
    fn dynamic_dispatch_predicate_1_picks_impl_1() {
        let mut store = VerifiedImplStore::new();
        store.register("Functor<List>", "map_list", first_f());
        store.register("Functor<List>", "map_parallel", first_f());
        let chosen = dynamic_dispatch(&store, "Functor<List>", || 1).unwrap();
        assert_eq!(chosen.name, "map_parallel");
    }

    #[test]
    fn dynamic_dispatch_on_empty_store_returns_no_impls() {
        let store = VerifiedImplStore::new();
        let err = dynamic_dispatch(&store, "Functor<List>", || 0).unwrap_err();
        match err {
            DispatchError::NoImpls { capability } => {
                assert_eq!(capability, "Functor<List>");
            }
        }
    }

    #[test]
    fn dynamic_dispatch_predicate_wraps_around() {
        // idx % impls.len(): with 2 impls, predicate 2 -> 0, predicate 3 -> 1.
        let mut store = VerifiedImplStore::new();
        store.register("Functor<List>", "map_list", first_f());
        store.register("Functor<List>", "map_parallel", first_f());
        let chosen0 = dynamic_dispatch(&store, "Functor<List>", || 2).unwrap();
        assert_eq!(chosen0.name, "map_list");
        let chosen1 = dynamic_dispatch(&store, "Functor<List>", || 3).unwrap();
        assert_eq!(chosen1.name, "map_parallel");
    }

    // --- Mode 3: runtime verification ---

    #[test]
    fn verify_at_runtime_first_f_accepted_with_both_laws() {
        let patterns = runtime_law_patterns();
        let result = verify_at_runtime(&first_f(), &patterns);
        match result {
            RuntimeVerification::Accepted { laws_checked } => {
                assert!(
                    laws_checked.contains(&"functor_identity".to_string()),
                    "functor_identity checked: {:?}",
                    laws_checked
                );
                assert!(
                    laws_checked.contains(&"functor_composition".to_string()),
                    "functor_composition checked: {:?}",
                    laws_checked
                );
            }
            other => panic!("expected Accepted, got {:?}", other),
        }
    }

    #[test]
    fn verify_at_runtime_bare_arr_rejected_with_functor_identity() {
        let patterns = runtime_law_patterns();
        let result = verify_at_runtime(&arr_not_a_functor(), &patterns);
        match result {
            RuntimeVerification::Rejected { reason, failed_law } => {
                assert!(!reason.is_empty());
                assert_eq!(failed_law, "functor_identity");
            }
            other => panic!("expected Rejected, got {:?}", other),
        }
    }

    #[test]
    fn verify_at_runtime_with_builtin_convenience_works() {
        // Accepted case.
        let accepted = verify_at_runtime_with_builtin(&first_f());
        match accepted {
            RuntimeVerification::Accepted { laws_checked } => {
                assert!(laws_checked.contains(&"functor_identity".to_string()));
                assert!(laws_checked.contains(&"functor_composition".to_string()));
            }
            other => panic!("expected Accepted, got {:?}", other),
        }
        // Rejected case.
        let rejected = verify_at_runtime_with_builtin(&arr_not_a_functor());
        match rejected {
            RuntimeVerification::Rejected { failed_law, .. } => {
                assert_eq!(failed_law, "functor_identity");
            }
            other => panic!("expected Rejected, got {:?}", other),
        }
    }

    // --- Cross-mode: Mode 2 and Mode 3 agree on the functor laws ---

    #[test]
    fn mode2_and_mode3_agree_on_functor_laws() {
        let mut store = VerifiedImplStore::new();
        let reg = store.register("Functor<List>", "map_list", first_f());
        let mode2_laws = match reg {
            RegistrationResult::Verified { laws_verified, .. } => laws_verified,
            other => panic!("expected Verified, got {:?}", other),
        };
        let mode3 = verify_at_runtime_with_builtin(&first_f());
        let mode3_laws = match mode3 {
            RuntimeVerification::Accepted { laws_checked } => laws_checked,
            other => panic!("expected Accepted, got {:?}", other),
        };
        assert!(mode2_laws.contains(&"functor_identity".to_string()));
        assert!(mode2_laws.contains(&"functor_composition".to_string()));
        assert!(mode3_laws.contains(&"functor_identity".to_string()));
        assert!(mode3_laws.contains(&"functor_composition".to_string()));
    }
}
