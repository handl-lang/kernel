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

use handl_value::{
    check_portable, materialize_tensor_bin, tagged_to_value, tensor, tensor_bin_decode,
    tensor_bin_record, truthy, TaggedValue, TensorValue, TENSOR_BIN_THRESHOLD,
};
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
    assert_eq!(tv.data.to_f64_vec(), &[7.0]);
    assert_eq!(tv.rank(), 1);
}

#[test]
fn tensor_decode_accepts_nonfinite_tags() {
    // `{"__nonfinite__": "nan"|"inf"|"-inf"}` elements decode to the
    // matching f64 — the spelling host-tensor's `codec.rs` emits since
    // commit 0528649 (serde_json has no NaN/±inf literals).
    let v = json!({"__tensor__": {"shape": [4], "data": [
        1.5,
        {"__nonfinite__": "nan"},
        {"__nonfinite__": "inf"},
        {"__nonfinite__": "-inf"},
    ], "dtype": "f64"}});
    let t = TaggedValue::from(v);
    let tv = t.as_tensor().expect("tagged data should decode to Tensor");
    let data = tv.data.to_f64_vec();
    assert_eq!(data[0], 1.5);
    assert!(data[1].is_nan());
    assert_eq!(data[2], f64::INFINITY);
    assert_eq!(data[3], f64::NEG_INFINITY);
}

#[test]
fn tensor_encode_emits_nonfinite_tags() {
    // The encode side mirrors `encode_tensor`: finite elements stay
    // JSON numbers, non-finite elements become the tag objects — so a
    // host result carrying NaN/±inf no longer degrades to `null`.
    let t = tensor(vec![3], vec![f64::NAN, f64::INFINITY, f64::NEG_INFINITY]).unwrap();
    let v = tagged_to_value(&t);
    assert_eq!(
        v["__tensor__"]["data"],
        json!([
            {"__nonfinite__": "nan"},
            {"__nonfinite__": "inf"},
            {"__nonfinite__": "-inf"},
        ])
    );
    // And the emitted form decodes back to the same non-finite values
    // (Tensor equality is structural f64 `==`, so NaN compares unequal
    // — assert on the decoded payload, not `TaggedValue` equality).
    let back = TaggedValue::from(v);
    let tv = back.as_tensor().expect("re-encoded tensor should decode");
    let data = tv.data.to_f64_vec();
    assert!(data[0].is_nan());
    assert_eq!(data[1], f64::INFINITY);
    assert_eq!(data[2], f64::NEG_INFINITY);
}

#[test]
fn tensor_decode_rejects_bad_nonfinite_elements() {
    // An unknown tag spelling is malformed — the payload falls back to
    // a plain object rather than coercing.
    let bad_tag = json!({"__tensor__": {"shape": [1], "data": [{"__nonfinite__": "bogus"}]}});
    assert!(matches!(TaggedValue::from(bad_tag), TaggedValue::Obj(_)));
    // A literal `null` element (the pre-tag serde_json spelling of a
    // non-finite) is rejected too — matching `decode_f64`.
    let null_el = json!({"__tensor__": {"shape": [1], "data": [null]}});
    assert!(matches!(TaggedValue::from(null_el), TaggedValue::Obj(_)));
    // A non-string tag value is malformed.
    let num_tag = json!({"__tensor__": {"shape": [1], "data": [{"__nonfinite__": 1}]}});
    assert!(matches!(TaggedValue::from(num_tag), TaggedValue::Obj(_)));
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

// ---------------------------------------------------------------------------
// ADR-0179 — the binary `__tensor_bin__` wire spelling + TensorData storage
// ---------------------------------------------------------------------------

fn f32_le(xs: &[f32]) -> Vec<u8> {
    xs.iter().flat_map(|x| x.to_le_bytes()).collect()
}

fn f64_le(xs: &[f64]) -> Vec<u8> {
    xs.iter().flat_map(|x| x.to_le_bytes()).collect()
}

/// The `{"__tensor_bin__": "<b64>"}` `data` value inside a bin record.
fn bin_data(v: &Value) -> &Value {
    &v["__tensor__"]["data"]
}

#[test]
fn tensor_bin_decode_f32_preserves_dtype() {
    // dtype "f32" + a 4×f32 LE payload decodes to F32 storage; the
    // widened values are exact (every f32 is an f64).
    let payload = f32_le(&[1.5, -2.25, f32::NAN, 0.0]);
    let rec = tensor_bin_record(&[2, 2], "f32", &payload).unwrap();
    assert!(bin_data(&rec).get("__tensor_bin__").is_some());
    let shape = vec![2, 2];
    let td = tensor_bin_decode(&shape, "f32", bin_data(&rec)).unwrap();
    assert_eq!(td.dtype(), "f32");
    let wide = td.to_f64_vec();
    assert_eq!(wide[0], 1.5);
    assert_eq!(wide[1], -2.25);
    assert!(wide[2].is_nan());
    // -0.0 vs 0.0: raw bits preserved through the bin channel.
    assert_eq!(wide[3].to_bits(), 0.0f64.to_bits());
}

#[test]
fn tensor_bin_decode_f64_and_nonfinite_bits() {
    let payload = f64_le(&[f64::NAN, f64::INFINITY, f64::NEG_INFINITY, -0.0]);
    let rec = tensor_bin_record(&[4], "f64", &payload).unwrap();
    let td = tensor_bin_decode(&[4], "f64", bin_data(&rec)).unwrap();
    assert_eq!(td.dtype(), "f64");
    let wide = td.to_f64_vec();
    assert!(wide[0].is_nan());
    assert_eq!(wide[1], f64::INFINITY);
    assert_eq!(wide[2], f64::NEG_INFINITY);
    // Non-finite ride raw IEEE bits — -0.0 keeps its sign.
    assert_eq!(wide[3].to_bits(), (-0.0f64).to_bits());
}

#[test]
fn tensor_bin_decode_rejects_malformed() {
    let good = tensor_bin_record(&[2], "f32", &f32_le(&[1.0, 2.0])).unwrap();
    let data = bin_data(&good).clone();
    // Wrong dtype spellings.
    assert!(tensor_bin_decode(&[2], "i32", &data).is_none());
    assert!(tensor_bin_decode(&[2], "F32", &data).is_none());
    // Payload length must be numel × itemsize.
    assert!(tensor_bin_decode(&[3], "f32", &data).is_none());
    assert!(tensor_bin_decode(&[2], "f64", &data).is_none());
    // Bad base64 / missing tag / non-string tag.
    assert!(tensor_bin_decode(&[2], "f32", &json!({"__tensor_bin__": "!!!"})).is_none());
    assert!(tensor_bin_decode(&[2], "f32", &json!({"__tensor_bin__": "AA"})).is_none());
    assert!(tensor_bin_decode(&[2], "f32", &json!({"other": "AAAA"})).is_none());
    assert!(tensor_bin_decode(&[2], "f32", &json!({"__tensor_bin__": 7})).is_none());
    // tensor_bin_record validates the same contract on encode.
    assert!(tensor_bin_record(&[2], "f32", &f32_le(&[1.0])).is_none());
    assert!(tensor_bin_record(&[2], "i64", &f32_le(&[1.0, 2.0])).is_none());
}

#[test]
fn tensor_bin_wire_round_trip_f32_storage() {
    // A `{"__tensor__": …, "dtype": "f32", "data": {"__tensor_bin__": …}}`
    // record decodes to an F32-backed TensorValue…
    let payload = f32_le(&[0.5, -1.25, 3.0, 4.5]);
    let rec = tensor_bin_record(&[2, 2], "f32", &payload).unwrap();
    let t = TaggedValue::from(rec.clone());
    let tv = t.as_tensor().expect("bin record should decode to Tensor");
    assert_eq!(tv.data.dtype(), "f32");
    assert_eq!(tv.data.to_f64_vec(), &[0.5, -1.25, 3.0, 4.5]);
    // …and re-encodes below the threshold as the array form with
    // dtype "f64" (the array spelling carries widened f64 elements;
    // the stored F32 dtype only shows on the binary spelling).
    let re = tagged_to_value(&t);
    assert!(re["__tensor__"]["data"].is_array());
    assert_eq!(re["__tensor__"]["dtype"], json!("f64"));
    // The re-encoded array decodes back equal (f64 widening eq).
    assert_eq!(TaggedValue::from(re), t);
}

#[test]
fn tensor_encode_emits_bin_at_threshold() {
    // numel >= TENSOR_BIN_THRESHOLD → the binary spelling; below it the
    // wire is byte-identical to the array form.
    let n = TENSOR_BIN_THRESHOLD;
    let big = tensor(vec![n], vec![1.5; n]).unwrap();
    let v = tagged_to_value(&big);
    let inner = &v["__tensor__"];
    assert_eq!(inner["dtype"], json!("f64"));
    let b64 = inner["data"]["__tensor_bin__"]
        .as_str()
        .expect("bin spelling");
    assert!(!b64.is_empty());
    // Round-trips through the lenient decoder to an equal tensor.
    let back = TaggedValue::from(v);
    assert_eq!(back, big);

    let small = tensor(vec![n - 1], vec![1.5; n - 1]).unwrap();
    let v = tagged_to_value(&small);
    assert!(v["__tensor__"]["data"].is_array());
    assert_eq!(v["__tensor__"]["dtype"], json!("f64"));
}

#[test]
fn tensor_encode_bin_preserves_f32_dtype() {
    // An F32-stored tensor ≥ threshold encodes `dtype: "f32"` with the
    // narrow payload — and decodes back to F32 storage.
    let n = TENSOR_BIN_THRESHOLD;
    let payload = f32_le(&vec![0.25f32; n]);
    let rec = tensor_bin_record(&[n], "f32", &payload).unwrap();
    let t = TaggedValue::from(rec);
    let tv = t.as_tensor().unwrap();
    assert_eq!(tv.data.dtype(), "f32");
    // Re-encode: still F32 storage → bin spelling with dtype "f32".
    let v = tagged_to_value(&t);
    assert_eq!(v["__tensor__"]["dtype"], json!("f32"));
    assert!(v["__tensor__"]["data"]["__tensor_bin__"].is_string());
    assert_eq!(TaggedValue::from(v), t);
}

#[test]
fn tensor_eq_and_hash_across_dtypes() {
    // F32 storage equals the F64 tensor holding the same widened values
    // (f32→f64 is exact and injective).
    let f32_rec = tensor_bin_record(&[3], "f32", &f32_le(&[1.0, 2.5, -0.0])).unwrap();
    let f64_t = tensor(vec![3], vec![1.0, 2.5, -0.0]).unwrap();
    let f32_t = TaggedValue::from(f32_rec);
    assert_eq!(f32_t, f64_t);
    fn h(v: &TaggedValue) -> u64 {
        let mut s = std::collections::hash_map::DefaultHasher::new();
        v.hash(&mut s);
        s.finish()
    }
    assert_eq!(h(&f32_t), h(&f64_t));
}

#[test]
fn tensor_bin_decode_falls_back_to_object_on_malformed() {
    // Every malformation degrades to a plain object (lenient
    // `__bytes__` convention), re-encoding unchanged.
    for inner in [
        // bad base64
        json!({"__tensor__": {"shape": [2], "dtype": "f32",
            "data": {"__tensor_bin__": "!!!"}}}),
        // wrong payload length (2×f32 = 8 bytes, not 16)
        json!({"__tensor__": {"shape": [4], "dtype": "f32",
            "data": {"__tensor_bin__": "AAAAAAAAAAAAAAAAAAA="}}}),
        // dtype absent — bin requires it
        json!({"__tensor__": {"shape": [2],
            "data": {"__tensor_bin__": "AAAAAAAAAAA="}}}),
        // unsupported dtype
        json!({"__tensor__": {"shape": [2], "dtype": "i32",
            "data": {"__tensor_bin__": "AAAAAAAAAAA="}}}),
        // "f32" + array data is malformed (the array spelling is f64)
        json!({"__tensor__": {"shape": [2], "dtype": "f32", "data": [1.0, 2.0]}}),
        // bin tag object missing the string
        json!({"__tensor__": {"shape": [2], "dtype": "f32", "data": {"__tensor_bin__": 3}}}),
    ] {
        let t = TaggedValue::from(inner.clone());
        assert!(matches!(t, TaggedValue::Obj(_)), "must fall back: {inner}");
        assert_eq!(tagged_to_value(&t), inner);
    }
}

#[test]
fn materialize_tensor_bin_expands_to_array_form() {
    // Encode a ≥threshold F32 tensor → bin record; materialize rewrites
    // `data` to the widened f64 array with dtype "f64" — the stdout
    // contract `hnl-run` preserves.
    let n = TENSOR_BIN_THRESHOLD;
    let payload = f32_le(&vec![1.25f32; n]);
    let rec = tensor_bin_record(&[n], "f32", &payload).unwrap();
    let mut v = rec;
    materialize_tensor_bin(&mut v);
    let inner = &v["__tensor__"];
    assert_eq!(inner["dtype"], json!("f64"));
    let arr = inner["data"]
        .as_array()
        .expect("materialized data is a list");
    assert_eq!(arr.len(), n);
    assert_eq!(arr[0], json!(1.25));
    // The materialized record decodes as an ordinary f64 tensor.
    let t = TaggedValue::from(v);
    assert!(t.as_tensor().is_some());

    // Non-finite elements materialize as __nonfinite__ tags.
    let payload = f64_le(&[f64::NAN, f64::INFINITY]);
    // shape [2] is below threshold for *encoding*, but materialize is
    // spelling-agnostic — hand it a bin record directly.
    let mut v = tensor_bin_record(&[2], "f64", &payload).unwrap();
    materialize_tensor_bin(&mut v);
    assert_eq!(v["__tensor__"]["data"][0], json!({"__nonfinite__": "nan"}));
    assert_eq!(v["__tensor__"]["data"][1], json!({"__nonfinite__": "inf"}));

    // Nested inside a larger document, and malformed records pass
    // through untouched.
    let mut doc = json!({"outer": [{"__tensor__": v["__tensor__"].clone()}], "keep": 1});
    materialize_tensor_bin(&mut doc);
    assert!(doc["outer"][0]["__tensor__"]["data"].is_array());
    let mut bad = json!({"__tensor__": {"shape": [1], "dtype": "f32",
        "data": {"__tensor_bin__": "!!!"}}});
    materialize_tensor_bin(&mut bad);
    assert_eq!(bad["__tensor__"]["data"]["__tensor_bin__"], json!("!!!"));
}

#[test]
fn tensor_bin_is_portable() {
    // The bin form is self-contained data — `check_portable` passes it
    // unchanged (unlike `__resource__`/`__compiled__` handles).
    let n = TENSOR_BIN_THRESHOLD;
    let payload = f64_le(&vec![2.0; n]);
    let rec = tensor_bin_record(&[n], "f64", &payload).unwrap();
    assert!(check_portable(&rec).is_ok());
    // And it round-trips through the TaggedValue codec.
    let t = TaggedValue::from(rec);
    assert!(t.is_tensor());
}
