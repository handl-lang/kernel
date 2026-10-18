//! Tests for the `Tensor` variant — the dense row-major `f64` tensor
//! carried opaquely for host functions (the `{"__tensor__": {"shape",
//! "data", "dtype": "f64"}}` wire form `host-tensor` uses).
//!
//! Covers:
//! - `TensorValue::new` enforces `data.len() == product(shape)`
//!   (including the scalar `shape == []` and zero-extent cases).
//! - Wire round-trip through `{"__tensor__": {...}}`, both with and
//!   without the optional `dtype` field (host-tensor accepts both).
//! - Malformed payloads fall back to plain objects (the lenient
//!   `__bytes__`/`__sym__` convention) and re-encode unchanged.
//! - Equality is structural over shape + data — not pointer identity —
//!   and hashing agrees (`-0.0`/`0.0` hash alike because `0.0 == -0.0`).
//! - Truthiness, accessors, and the `check_portable` boundary check.

use std::hash::{Hash, Hasher};
use std::rc::Rc;

use handl_value::{check_portable, tagged_to_value, tensor, truthy, TaggedValue, TensorValue};
use serde_json::{json, Value};

/// The host-tensor wire form (`host-tensor/src/ops.rs::encode_tensor`).
fn wire(shape: &[i64], data: &[f64]) -> Value {
    json!({"__tensor__": {"shape": shape, "data": data, "dtype": "f64"}})
}

#[test]
fn tensor_new_enforces_the_length_invariant() {
    assert!(TensorValue::new(vec![2, 2], vec![1.0, 2.0, 3.0, 4.0]).is_ok());
    assert!(TensorValue::new(vec![2, 2], vec![1.0]).is_err());
    // A scalar tensor: shape `[]` has product 1.
    assert!(TensorValue::new(vec![], vec![7.0]).is_ok());
    // A zero extent zeroes the product.
    assert!(TensorValue::new(vec![2, 0], vec![]).is_ok());
    // Product overflow is rejected, not wrapping.
    assert!(TensorValue::new(vec![usize::MAX, 2], vec![1.0]).is_err());
}

#[test]
fn tensor_wire_round_trip() {
    let t = tensor(vec![2, 2], vec![1.0, 2.0, 3.0, 4.0]).unwrap();
    let v = tagged_to_value(&t);
    assert_eq!(v, wire(&[2, 2], &[1.0, 2.0, 3.0, 4.0]));
    let back = TaggedValue::from(v);
    assert_eq!(back, t);
    assert!(matches!(back, TaggedValue::Tensor(_)));
}

#[test]
fn tensor_decode_accepts_the_host_tensor_forms() {
    // `dtype` is optional on decode.
    let no_dtype = json!({"__tensor__": {"shape": [1], "data": [7]}});
    let t = TaggedValue::from(no_dtype);
    let tv = t.as_tensor().expect("should decode to Tensor");
    assert_eq!(tv.shape, vec![1]);
    // Integer data elements decode as f64 (the host-tensor contract).
    assert_eq!(tv.data.as_slice(), &[7.0]);
    assert_eq!(tv.rank(), 1);
}

#[test]
fn tensor_decode_falls_back_to_object_on_malformed_payloads() {
    // A `dtype` other than "f64" is not silently relabeled.
    let bad_dtype = json!({"__tensor__": {"shape": [1], "data": [7], "dtype": "i32"}});
    assert!(matches!(TaggedValue::from(bad_dtype), TaggedValue::Obj(_)));
    // Data length must equal product(shape).
    let bad_len = json!({"__tensor__": {"shape": [2], "data": [1]}});
    assert!(matches!(TaggedValue::from(bad_len), TaggedValue::Obj(_)));
    // Negative extents are not valid shapes.
    let bad_shape = json!({"__tensor__": {"shape": [-1], "data": []}});
    assert!(matches!(TaggedValue::from(bad_shape), TaggedValue::Obj(_)));
    // The fallback preserves the wire bytes (it is a plain object).
    let v = json!({"__tensor__": {"shape": [2], "data": [1]}});
    assert_eq!(tagged_to_value(&TaggedValue::from(v.clone())), v);
}

#[test]
fn tensor_eq_is_structural_not_pointer() {
    let a = tensor(vec![2], vec![1.0, 2.0]).unwrap();
    let b = tensor(vec![2], vec![1.0, 2.0]).unwrap();
    let (pa, pb) = match (&a, &b) {
        (TaggedValue::Tensor(x), TaggedValue::Tensor(y)) => {
            (Rc::as_ptr(x) as usize, Rc::as_ptr(y) as usize)
        }
        _ => unreachable!(),
    };
    assert_ne!(pa, pb, "distinct allocations — equality is structural");
    assert_eq!(a, b);
    // 0.0 == -0.0 elementwise, matching `Float` semantics.
    assert_eq!(
        tensor(vec![1], vec![0.0]).unwrap(),
        tensor(vec![1], vec![-0.0]).unwrap()
    );
    // Shape and data both participate.
    assert_ne!(
        tensor(vec![2], vec![1.0, 2.0]).unwrap(),
        tensor(vec![1, 2], vec![1.0, 2.0]).unwrap()
    );
    assert_ne!(
        tensor(vec![2], vec![1.0, 2.0]).unwrap(),
        tensor(vec![2], vec![1.0, 3.0]).unwrap()
    );
    // A tensor never equals a non-tensor.
    assert_ne!(a, TaggedValue::Null);
}

#[test]
fn tensor_hash_agrees_with_eq() {
    fn h(v: &TaggedValue) -> u64 {
        let mut s = std::collections::hash_map::DefaultHasher::new();
        v.hash(&mut s);
        s.finish()
    }
    let a = tensor(vec![2], vec![1.0, 2.0]).unwrap();
    let b = tensor(vec![2], vec![1.0, 2.0]).unwrap();
    assert_eq!(h(&a), h(&b));
    // Equal values hash equally across the 0.0/-0.0 bit divide.
    assert_eq!(
        h(&tensor(vec![1], vec![0.0]).unwrap()),
        h(&tensor(vec![1], vec![-0.0]).unwrap())
    );
}

#[test]
fn tensor_truthy_and_portable() {
    let t = tensor(vec![0], vec![]).unwrap();
    assert!(truthy(&t));
    assert!(t.is_tensor());
    assert!(t.as_i64().is_none());
    // A tensor is self-contained data — portable across a process
    // boundary (unlike `__resource__`).
    assert!(check_portable(&tagged_to_value(&t)).is_ok());
}

#[test]
fn tensor_constructor_rejects_bad_inputs() {
    assert!(tensor(vec![3], vec![1.0, 2.0]).is_err());
    assert!(tensor(vec![2], vec![1.0, 2.0]).unwrap().is_tensor());
}
