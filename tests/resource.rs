//! Tests for the `Resource` / `ForeignResource` RAII mechanism
//! (ADR-0083 §2.2 — finalizable values, Phase 4 prerequisite).
//!
//! Covers:
//! - A `Resource` with a finalizer calls the finalizer on drop.
//! - A `Resource` without a finalizer drops cleanly.
//! - Double-drop does not happen (the finalizer runs exactly once).
//! - JSON interop: `{"__resource__": {"ptr": N}}` round-trips (with
//!   `finalizer = None` on decode, since function pointers are not
//!   serializable).
//! - Accessor methods and the `resource()` constructor.

use std::ffi::c_void;
use std::sync::atomic::{AtomicUsize, Ordering};

use handl_value::{eq, resource, tagged_to_value, truthy, ForeignResource, TaggedValue};

/// A counter incremented by test finalizers, so tests can observe how many
/// times the finalizer ran.
static FINALIZER_CALLS: AtomicUsize = AtomicUsize::new(0);

/// A test finalizer: increments [`FINALIZER_CALLS`] and does nothing else
/// (the "resource" is a fake pointer in tests).
unsafe fn test_finalizer(_ptr: *mut c_void) {
    FINALIZER_CALLS.fetch_add(1, Ordering::SeqCst);
}

fn reset_counter() -> usize {
    FINALIZER_CALLS.swap(0, Ordering::SeqCst)
}

// ---------------------------------------------------------------------------
// Finalizer runs on drop
// ---------------------------------------------------------------------------

#[test]
fn resource_with_finalizer_calls_it_on_drop() {
    reset_counter();
    {
        let _r = unsafe { resource(0x1000 as *mut c_void, Some(test_finalizer)) };
        // Finalizer has not run yet — the value is still alive.
        assert_eq!(reset_counter(), 0);
    }
    // After the value goes out of scope, the finalizer ran exactly once.
    assert_eq!(FINALIZER_CALLS.load(Ordering::SeqCst), 1);
}

#[test]
fn resource_without_finalizer_drops_cleanly() {
    reset_counter();
    {
        let _r = unsafe { resource(0x2000 as *mut c_void, None) };
    }
    // No finalizer → counter stays at zero, no panic.
    assert_eq!(reset_counter(), 0);
}

// ---------------------------------------------------------------------------
// Double-drop / Rc cloning
// ---------------------------------------------------------------------------

#[test]
fn resource_finalizer_runs_once_even_with_clones() {
    // Cloning a TaggedValue::Resource bumps the Rc refcount; the
    // ForeignResource (and thus the finalizer) should only drop once, when
    // the *last* clone goes away.
    reset_counter();
    let r1 = unsafe { resource(0x3000 as *mut c_void, Some(test_finalizer)) };
    let r2 = r1.clone();
    let r3 = r2.clone();
    // Drop two of the three clones — finalizer must not run yet.
    drop(r1);
    drop(r2);
    assert_eq!(reset_counter(), 0);
    // Drop the last clone — finalizer runs now.
    drop(r3);
    assert_eq!(FINALIZER_CALLS.load(Ordering::SeqCst), 1);
}

#[test]
fn resource_double_drop_guard_prevents_double_free() {
    // The AtomicBool `dropped` guard inside ForeignResource ensures the
    // finalizer runs at most once. We verify this by constructing a
    // resource, observing `is_dropped()` is false, then dropping it and
    // confirming the finalizer ran exactly once (not twice). With `Rc`,
    // the inner `ForeignResource` only drops when the last clone goes
    // away, so this also covers the clone case.
    reset_counter();
    let fr = unsafe { ForeignResource::new(0x4000 as *mut c_void, Some(test_finalizer)) };
    assert!(!fr.is_dropped());
    // Wrap in a Resource and drop it — the finalizer should fire once.
    let r = TaggedValue::Resource(std::rc::Rc::new(fr));
    drop(r);
    assert_eq!(FINALIZER_CALLS.load(Ordering::SeqCst), 1);
}

// ---------------------------------------------------------------------------
// Accessors
// ---------------------------------------------------------------------------

#[test]
fn as_resource_returns_foreign_resource() {
    let r = unsafe { resource(0x5000 as *mut c_void, None) };
    let fr = r.as_resource().expect("should be a Resource");
    assert_eq!(fr.ptr(), 0x5000 as *mut c_void);
    assert!(fr.finalizer.is_none());
    assert!(!fr.is_dropped());

    // Non-resource values return None.
    assert!(TaggedValue::Null.as_resource().is_none());
    assert!(TaggedValue::Int(42).as_resource().is_none());
}

// ---------------------------------------------------------------------------
// Equality and truthiness
// ---------------------------------------------------------------------------

#[test]
fn resource_equality_by_pointer_identity() {
    let a = unsafe { resource(0x6000 as *mut c_void, None) };
    let b = unsafe { resource(0x6000 as *mut c_void, None) };
    let c = unsafe { resource(0x7000 as *mut c_void, None) };
    assert!(eq(&a, &b), "same ptr → equal");
    assert!(!eq(&a, &c), "different ptr → not equal");
}

#[test]
fn resource_is_truthy() {
    let r = unsafe { resource(0x0 as *mut c_void, None) };
    assert!(truthy(&r), "resources are always truthy");
}

// ---------------------------------------------------------------------------
// JSON interop (debug representation)
// ---------------------------------------------------------------------------

#[test]
fn resource_encodes_to_json_debug_form() {
    let r = unsafe { resource(0x1234 as *mut c_void, None) };
    let json = tagged_to_value(&r);
    let obj = json.as_object().expect("should be a JSON object");
    let res = obj.get("__resource__").expect("should have __resource__ key");
    let ptr = res.get("ptr").and_then(|v| v.as_i64());
    assert_eq!(ptr, Some(0x1234));
}

#[test]
fn resource_decodes_from_json_with_no_finalizer() {
    use serde_json::json;
    let json = json!({"__resource__": {"ptr": 0xABCD}});
    let t: TaggedValue = json.into();
    match &t {
        TaggedValue::Resource(r) => {
            assert_eq!(r.ptr(), 0xABCD as *mut c_void);
            assert!(r.finalizer.is_none(), "decoded resource has no finalizer");
        }
        other => panic!("expected Resource variant, got {other:?}"),
    }
}

#[test]
fn resource_json_roundtrips_ptr_address() {
    let original = unsafe { resource(0xDEAD as *mut c_void, None) };
    let encoded = tagged_to_value(&original);
    let decoded: TaggedValue = encoded.into();
    match &decoded {
        TaggedValue::Resource(r) => {
            assert_eq!(r.ptr(), 0xDEAD as *mut c_void);
        }
        other => panic!("expected Resource variant, got {other:?}"),
    }
}
