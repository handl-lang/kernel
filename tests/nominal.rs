//! Nominal identity tests for the `handl-value` crate (ADR-0106 §2,
//! Phase 2 kernel primitives).
//!
//! Covers `sym()`/`sym(A)` freshness and identity equality, name-collision
//! semantics (identity is handle-based; names are presentation only), the
//! parent-chain traversal helpers, `sym(A)` errors on non-nominal parents,
//! the `{"__sym__": ...}` JSON round-trip, deep chains, and the
//! diamond-free (single parent) invariant.

use handl_value::{
    eq, has_ancestor, is_descendant_of, is_nominal, nominal_parent, sym, sym_from_parent_value,
    sym_with_parent, tagged_to_value, TaggedValue,
};
use serde_json::json;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

fn hash_of(v: &TaggedValue) -> u64 {
    let mut h = DefaultHasher::new();
    v.hash(&mut h);
    h.finish()
}

// ---------------------------------------------------------------------------
// sym() freshness: two syms unequal; equal to themselves; hash/eq consistency
// ---------------------------------------------------------------------------

#[test]
fn sym_freshness_two_syms_unequal() {
    let a = sym("A");
    let b = sym("A");
    assert!(a != b);
    assert!(!eq(&a, &b));
    // Equal to themselves.
    assert_eq!(a, a);
    assert_eq!(b, b);
    assert!(eq(&a, &a));
}

#[test]
fn sym_freshness_handles_distinct() {
    let a = sym("A");
    let b = sym("A");
    assert_ne!(
        a.as_sym().unwrap().handle(),
        b.as_sym().unwrap().handle(),
        "fresh syms must mint distinct handles"
    );
}

#[test]
fn sym_eq_hash_consistency() {
    let a = sym("A");
    let b = sym("A");
    // Equal values hash equal.
    assert_eq!(hash_of(&a), hash_of(&a));
    // Hashing is by handle (identity): unequal syms hash unequally here
    // (equal hashes are legal, but handles differ so this holds
    // deterministically for these values).
    assert_ne!(hash_of(&a), hash_of(&b));
}

#[test]
fn sym_hash_matches_rebuilt_copy() {
    // A sym rebuilt from the same handle (e.g. via round-trip) hashes the
    // same as the original — equal values, equal hashes.
    let a = sym("A");
    let json = tagged_to_value(&a);
    let copy: TaggedValue = json.into();
    assert_eq!(a, copy);
    assert_eq!(hash_of(&a), hash_of(&copy));
}

// ---------------------------------------------------------------------------
// Name collisions: identity is handle-based, name is presentation only
// ---------------------------------------------------------------------------

#[test]
fn same_name_distinct_syms_unequal() {
    let n1 = sym("Number");
    let n2 = sym("Number");
    assert_ne!(n1, n2);
    assert!(!eq(&n1, &n2));
    // Same name, but identity differs — the name shows in serialization
    // only, never in equality.
    assert_eq!(
        n1.as_sym().unwrap().name(),
        n2.as_sym().unwrap().name(),
        "names are presentation only; identity is the handle"
    );
}

#[test]
fn same_name_different_parents_still_unequal() {
    let root1 = sym("Root");
    let root2 = sym("Root");
    let c1 = sym_with_parent("Child", root1.as_sym().unwrap());
    let c2 = sym_with_parent("Child", root2.as_sym().unwrap());
    assert_ne!(c1, c2);
}

// ---------------------------------------------------------------------------
// sym(A) parent chain: descendants, reverse direction, siblings
// ---------------------------------------------------------------------------

#[test]
fn sym_parent_chain_is_descendant_of() {
    let root = sym("Obj");
    let number = sym_with_parent("Number", root.as_sym().unwrap());
    let float = sym_with_parent("Float", number.as_sym().unwrap());

    let f = float.as_sym().unwrap();
    let n = number.as_sym().unwrap();
    let r = root.as_sym().unwrap();

    // child -> parent: true (strict descendant).
    assert!(f.is_descendant_of(n));
    assert!(f.is_descendant_of(r));
    assert!(n.is_descendant_of(r));
    // parent -> child: false.
    assert!(!n.is_descendant_of(f));
    assert!(!r.is_descendant_of(f));
    assert!(!r.is_descendant_of(n));
    // Siblings are not descendants of each other.
    let number2 = sym_with_parent("Number", root.as_sym().unwrap());
    assert!(!n.is_descendant_of(number2.as_sym().unwrap()));
    assert!(!number2.as_sym().unwrap().is_descendant_of(n));
    // Self is not a strict descendant.
    assert!(!f.is_descendant_of(f));
    // A root has no parent.
    assert!(r.parent().is_none());
}

#[test]
fn has_ancestor_is_inclusive_instanceof_semantics() {
    let root = sym("Obj");
    let number = sym_with_parent("Number", root.as_sym().unwrap());
    let float = sym_with_parent("Float", number.as_sym().unwrap());

    let f = float.as_sym().unwrap();
    let n = number.as_sym().unwrap();
    let r = root.as_sym().unwrap();

    // Inclusive: Float instanceof Float, Float instanceof Number,
    // Float instanceof Obj — but not Number instanceof Float.
    assert!(f.has_ancestor(f));
    assert!(f.has_ancestor(n));
    assert!(f.has_ancestor(r));
    assert!(n.has_ancestor(n));
    assert!(!n.has_ancestor(f));
    assert!(!r.has_ancestor(f));
}

#[test]
fn value_level_helpers_delegate_to_sym() {
    let root = sym("Obj");
    let number = sym_with_parent("Number", root.as_sym().unwrap());
    let float = sym_with_parent("Float", number.as_sym().unwrap());

    assert!(is_nominal(&float));
    assert!(!is_nominal(&TaggedValue::Int(1)));
    assert!(!is_nominal(&TaggedValue::Null));

    // nominal_parent: Some for children, None for roots and non-nominals.
    assert_eq!(
        nominal_parent(&float).map(|p| p.handle()),
        Some(number.as_sym().unwrap().handle())
    );
    assert!(nominal_parent(&root).is_none());
    assert!(nominal_parent(&TaggedValue::Int(1)).is_none());

    // is_descendant_of / has_ancestor over values.
    assert!(is_descendant_of(&float, &number));
    assert!(!is_descendant_of(&number, &float));
    assert!(has_ancestor(&float, &float));
    assert!(has_ancestor(&float, &number));
    assert!(!has_ancestor(&number, &float));
    // Non-nominal operands: false, no error.
    assert!(!has_ancestor(&TaggedValue::Int(1), &float));
    assert!(!has_ancestor(&float, &TaggedValue::Int(1)));
    assert!(!is_descendant_of(&TaggedValue::Int(1), &TaggedValue::Int(2)));
}

#[test]
fn sym_from_parent_value_errors_on_non_nominal() {
    // sym(A) where A is not a nominal -> error.
    for bad in [TaggedValue::Int(42), TaggedValue::Null, TaggedValue::Bool(true)] {
        let err = sym_from_parent_value("Child", &bad).unwrap_err();
        assert!(err.contains("parent is not a nominal object"), "{}", err);
    }
    let bad: TaggedValue = json!({"a": 1}).into();
    let err = sym_from_parent_value("Child", &bad).unwrap_err();
    assert!(err.contains("parent is not a nominal object"), "{}", err);
    // The sym(A) success path.
    let root = sym("A");
    let child = sym_from_parent_value("B", &root).unwrap();
    assert!(child
        .as_sym()
        .unwrap()
        .is_descendant_of(root.as_sym().unwrap()));
}

// ---------------------------------------------------------------------------
// Serialization round-trip: {"__sym__": {handle, name, parent}}
// ---------------------------------------------------------------------------

#[test]
fn sym_json_shape_is_explicit_data() {
    let root = sym("Number");
    let child = sym_with_parent("Float", root.as_sym().unwrap());
    let v = tagged_to_value(&child);
    let inner = v.get("__sym__").expect("__sym__ key");
    assert_eq!(
        inner.get("handle").and_then(|h| h.as_u64()),
        Some(child.as_sym().unwrap().handle())
    );
    assert_eq!(inner.get("name").and_then(|n| n.as_str()), Some("Float"));
    let parent = inner.get("parent").expect("parent key");
    assert_eq!(
        parent
            .get("__sym__")
            .unwrap()
            .get("name")
            .and_then(|n| n.as_str()),
        Some("Number")
    );
    // Root syms encode parent: null.
    let rv = tagged_to_value(&root);
    assert!(rv.get("__sym__").unwrap().get("parent").unwrap().is_null());
}

#[test]
fn sym_round_trip_with_parent_preserves_identity() {
    let root = sym("Obj");
    let number = sym_with_parent("Number", root.as_sym().unwrap());
    let child = sym_with_parent("Float", number.as_sym().unwrap());

    // TaggedValue -> JSON -> TaggedValue.
    let json = tagged_to_value(&child);
    let decoded: TaggedValue = json.into();
    assert!(decoded.is_sym());
    assert_eq!(decoded, child, "round-trip preserves the handle (identity)");

    // The decoded sym's parent chain decodes too.
    let dp = nominal_parent(&decoded).unwrap();
    assert_eq!(dp.handle(), number.as_sym().unwrap().handle());
    assert_eq!(dp.name(), "Number");

    // Deep chain round trip: Float -> Number -> sym(); the whole chain
    // decodes with identical handles.
    let deep_json = tagged_to_value(&child);
    let deep_decoded: TaggedValue = deep_json.into();
    assert!(deep_decoded
        .as_sym()
        .unwrap()
        .has_ancestor(root.as_sym().unwrap()));
    let chain = deep_decoded.as_sym().unwrap().chain();
    assert_eq!(chain.len(), 3);
    assert_eq!(chain[0].name(), "Obj");
    assert_eq!(chain[1].name(), "Number");
    assert_eq!(chain[2].name(), "Float");
}

#[test]
fn sym_malformed_json_falls_back_to_plain_object() {
    // Missing handle/name: falls back to a plain object (lenient style,
    // matching __bytes__).
    let v: TaggedValue = json!({"__sym__": {"name": "X"}}).into();
    assert!(!v.is_sym());
    assert!(v.as_object().is_some());

    // handle = 0 is not a valid handle.
    let v: TaggedValue = json!({"__sym__": {"handle": 0, "name": "X", "parent": null}}).into();
    assert!(!v.is_sym());

    // Non-object parent: rejected -> plain object.
    let v: TaggedValue = json!({"__sym__": {"handle": 1, "name": "X", "parent": 5}}).into();
    assert!(!v.is_sym());

    // Parent that is not a sym encoding: rejected -> plain object.
    let v: TaggedValue = json!({"__sym__": {"handle": 1, "name": "X", "parent": {"a": 1}}}).into();
    assert!(!v.is_sym());
}

// ---------------------------------------------------------------------------
// Deep chains and the diamond-free (single parent) invariant
// ---------------------------------------------------------------------------

#[test]
fn deep_chain_float_number_root() {
    let root = sym("Obj");
    let number = sym_with_parent("Number", root.as_sym().unwrap());
    let float = sym_with_parent("Float", number.as_sym().unwrap());

    // The chain is linear and root-first.
    let chain = float.as_sym().unwrap().chain();
    assert_eq!(chain.len(), 3, "Float -> Number -> Obj is a chain of 3");
    assert_eq!(chain[0].name(), "Obj");
    assert_eq!(chain[1].name(), "Number");
    assert_eq!(chain[2].name(), "Float");
    // Consecutive links are parent/child.
    for (p, c) in chain.iter().zip(chain.iter().skip(1)) {
        assert!(c.is_descendant_of(p));
    }
}

#[test]
fn diamond_free_single_parent_invariant() {
    // Each sym has exactly one parent, fixed at construction: a node
    // reached through the chain has one parent (not a collection), so
    // diamonds cannot exist structurally.
    let root = sym("Root");
    let number = sym_with_parent("Number", root.as_sym().unwrap());
    let float = sym_with_parent("Float", number.as_sym().unwrap());
    let int = sym_with_parent("Int", number.as_sym().unwrap());

    // Two children share a parent, but each child has that single parent.
    assert_eq!(
        float.as_sym().unwrap().parent().map(|p| p.handle()),
        Some(number.as_sym().unwrap().handle())
    );
    assert_eq!(
        int.as_sym().unwrap().parent().map(|p| p.handle()),
        Some(number.as_sym().unwrap().handle())
    );
    // A common ancestor exists (the shared parent) but no node has two
    // parents: walking from any leaf visits each ancestor exactly once
    // (chain length = depth + 1, no repeats).
    let chain = float.as_sym().unwrap().chain();
    let mut handles: Vec<u64> = chain.iter().map(|s| s.handle()).collect();
    handles.sort();
    handles.dedup();
    assert_eq!(handles.len(), chain.len(), "no repeated node in the chain");
    // Parent is a single Option, not a list — the type itself forbids
    // diamonds.
    assert!(int.as_sym().unwrap().parent().is_some());
    assert!(root.as_sym().unwrap().parent().is_none());
}

#[test]
fn sym_in_object_container_equality_is_identity() {
    // A sym nested inside an object participates in identity equality.
    let a = sym("A");
    let obj1 = obj_with("k", a.clone());
    let obj2 = obj_with("k", a.clone());
    assert_eq!(obj1, obj2);
    let b = sym("A");
    let obj3 = obj_with("k", b);
    assert_ne!(
        obj1, obj3,
        "structurally equal objects differ by sym identity"
    );
}

fn obj_with(k: &str, v: TaggedValue) -> TaggedValue {
    let mut m = rustc_hash::FxHashMap::default();
    m.insert(Rc::from(k), v);
    TaggedValue::Obj(Rc::new(m))
}

// ---------------------------------------------------------------------------
// Truthiness & misc
// ---------------------------------------------------------------------------

#[test]
fn sym_is_truthy() {
    assert!(handl_value::truthy(&sym("A")));
}

#[test]
fn sym_display_includes_name_and_handle() {
    let a = sym("A");
    let s = a.as_sym().unwrap();
    let text = format!("{}", s);
    assert!(text.contains("A#"), "{}", text);
    assert!(text.contains(&s.handle().to_string()), "{}", text);
}
