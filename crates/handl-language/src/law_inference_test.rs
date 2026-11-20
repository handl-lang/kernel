use super::*;

// --- TermData thin wrappers (ADR-0103 Phase 6 migration) ---

/// Convert `TermData` back to `Term` for APIs that require `Term`.
fn td(t: TermData) -> Term {
    t.to_term().expect("TermData -> Term conversion")
}

/// Native op without a literal payload (mirrors `TermData::op`).
fn op_native(name: &str, args: Vec<TermData>) -> TermData {
    if name == "const" && args.is_empty() {
        TermData::arr(Value::Null)
    } else {
        TermData::op(name, args, &ArrSource::Native, None)
    }
}

/// Native op with a literal payload (mirrors `TermData::op`).
fn op_lit(name: &str, args: Vec<TermData>, lit: impl Into<Value>) -> TermData {
    if name == "const" && args.is_empty() {
        TermData::arr(lit)
    } else {
        TermData::op(name, args, &ArrSource::Native, Some(lit.into()))
    }
}

/// Foreign op (mirrors `TermData::op`).
fn op_foreign(name: &str, args: Vec<TermData>) -> TermData {
    TermData::op(name, args, &ArrSource::Foreign(name.to_string()), None)
}

/// Sequential composition (mirrors `TermData::seq`).
fn seq(fst: TermData, snd: TermData) -> TermData {
    TermData::seq(fst, snd)
}

/// First (mirrors `TermData::first`).
fn first(inner: TermData) -> TermData {
    TermData::first(inner)
}

/// Choice routing (mirrors `TermData::choice`).
fn choice(l: TermData, r: TermData) -> TermData {
    TermData::choice(l, r)
}

/// Loop feedback (mirrors `TermData::loop_feedback`).
fn loop_feedback(body: TermData) -> TermData {
    TermData::loop_feedback(body)
}

fn id() -> TermData {
    op_native("id", vec![])
}
fn f() -> TermData {
    op_native("f", vec![])
}
fn g() -> TermData {
    op_native("g", vec![])
}

#[test]
fn is_id_recognizes_identity_arrow() {
    assert!(is_id(&td(op_native("id", vec![]))));
    // A non-identity op is not the identity arrow.
    assert!(!is_id(&td(op_native("add", vec![]))));
    // An identity with args is not the bare identity arrow.
    assert!(!is_id(&td(op_native("id", vec![op_native("x", vec![])]))));
    // A foreign "id" is not the native identity arrow.
    assert!(!is_id(&td(op_foreign("id", vec![]))));
    // An identity with a literal payload is not the bare identity arrow.
    assert!(!is_id(&td(op_lit("id", vec![], 42))));
}

#[test]
fn normalize_ce_id_left() {
    // Seq(Id, f) ==> f  (ceIdLeft)
    let s = td(seq(id(), f()));
    assert_eq!(normalize(&s, NORMALIZE_FUEL), td(f()));
}

#[test]
fn normalize_ce_id_right() {
    // Seq(f, Id) ==> f  (ceIdRight)
    let s = td(seq(f(), id()));
    assert_eq!(normalize(&s, NORMALIZE_FUEL), td(f()));
}

#[test]
fn normalize_ce_first_id() {
    // First(Id) ==> Id  (ceFirstId)
    let s = td(first(id()));
    assert_eq!(normalize(&s, NORMALIZE_FUEL), td(id()));
}

#[test]
fn normalize_ce_first_fusion() {
    // Seq(First(f), First(g)) ==> First(Seq(f, g))  (ceFirstFusion)
    let s = td(seq(first(f()), first(g())));
    assert_eq!(normalize(&s, NORMALIZE_FUEL), td(first(seq(f(), g()))));
}

#[test]
fn normalize_cascade_completes_in_one_pass() {
    // Seq(First(id), First(id)) -> First(Seq(id, id)) -> First(id) -> id
    let s = td(seq(first(id()), first(id())));
    assert_eq!(normalize(&s, NORMALIZE_FUEL), td(id()));
}

#[test]
fn normalize_is_idempotent_on_normal_form() {
    let s = td(first(seq(f(), g())));
    let once = normalize(&s, NORMALIZE_FUEL);
    let twice = normalize(&once, NORMALIZE_FUEL);
    assert_eq!(once, twice);
}

#[test]
fn law_equal_first_id_equals_id() {
    assert!(law_equal(&td(first(id())), &td(id())));
}

#[test]
fn law_equal_first_fusion() {
    // Seq(First(f), First(g)) === First(Seq(f, g))
    let lhs = td(seq(first(f()), first(g())));
    let rhs = td(first(seq(f(), g())));
    assert!(law_equal(&lhs, &rhs));
}

#[test]
fn law_equal_distinguishes_distinct_arrows() {
    // first(f) is not law_equal to f -- they do not normalize together.
    assert!(!law_equal(&td(first(f())), &td(f())));
}

#[test]
fn uses_first_detects_first() {
    assert!(uses_first(&td(first(f()))));
}

#[test]
fn uses_first_false_for_plain_arr() {
    assert!(!uses_first(&td(op_native("sort", vec![]))));
}

#[test]
fn uses_first_detects_nested() {
    // Seq(First(f), g) uses first (nested, not at root).
    assert!(uses_first(&td(seq(first(f()), g()))));
}

#[test]
fn uses_first_recurses_into_choice_and_loop() {
    assert!(uses_first(&td(choice(first(f()), g()))));
    assert!(uses_first(&td(loop_feedback(first(f())))));
    assert!(!uses_first(&td(choice(f(), g()))));
}

#[test]
fn infer_laws_first_reports_both_functor_laws() {
    let inferred = infer_laws(&td(first(f())));
    // functor_identity (Satisfied) and functor_composition (Satisfied).
    assert_eq!(inferred.len(), 2);
    assert!(
        inferred
            .iter()
            .any(|l| l.name == "functor_identity" && l.status == LawStatus::Satisfied)
    );
    assert!(
        inferred
            .iter()
            .any(|l| l.name == "functor_composition" && l.status == LawStatus::Satisfied)
    );
}

#[test]
fn infer_laws_plain_arr_reports_no_laws() {
    let inferred = infer_laws(&td(op_native("sort", vec![])));
    assert!(inferred.is_empty());
}

#[test]
fn infer_laws_seq_of_firsts_reports_both() {
    let inferred = infer_laws(&td(seq(first(f()), first(g()))));
    assert_eq!(inferred.len(), 2);
    assert!(
        inferred
            .iter()
            .any(|l| l.name == "functor_identity" && l.status == LawStatus::Satisfied)
    );
    assert!(
        inferred
            .iter()
            .any(|l| l.name == "functor_composition" && l.status == LawStatus::Satisfied)
    );
}

#[test]
fn infer_laws_roundtrip_reports_no_laws() {
    // Non-functor laws are NOT inferable: a serialize/deserialize
    // roundtrip is a semantic fact, not a CutElim-proven structural law.
    let s = td(seq(
        op_native("serialize", vec![]),
        op_native("deserialize", vec![]),
    ));
    let inferred = infer_laws(&s);
    assert!(inferred.is_empty());
}

#[test]
fn builtin_law_catalog_has_two_portable_patterns() {
    let catalog = builtin_law_catalog();
    assert_eq!(catalog.len(), 2);
    let names: Vec<&str> = catalog.iter().map(|p| p.name.as_str()).collect();
    assert!(names.contains(&"functor_identity"));
    assert!(names.contains(&"functor_composition"));
    // The coproduct functor laws are NOT in the catalog (no `Left` in
    // `Term`).
    assert!(!names.contains(&"coproduct_functor_identity"));
    assert!(!names.contains(&"coproduct_functor_composition"));
}
