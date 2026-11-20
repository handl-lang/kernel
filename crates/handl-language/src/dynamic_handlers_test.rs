use super::*;

fn first_f() -> Term {
    TermData::first(TermData::op("f", vec![], &ArrSource::Native, None))
        .to_term()
        .expect("TermData -> Term")
}

fn arr_sort() -> Term {
    TermData::op("sort", vec![], &ArrSource::Native, None)
        .to_term()
        .expect("TermData -> Term")
}

fn arr_not_a_functor() -> Term {
    TermData::op("not_a_functor", vec![], &ArrSource::Native, None)
        .to_term()
        .expect("TermData -> Term")
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
