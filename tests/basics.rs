//! Basic tests for the `handl-value` crate.
//!
//! Covers round-trip conversions between `serde_json::Value` and
//! `TaggedValue`, arithmetic, comparison, pair/either helpers, truthiness,
//! and the `tval!` macro.

use handl_value::{
    add, div, either_left, either_right, either_value, eq, is_either_left, is_either_right, lt,
    mod_, mul, pair, pair_fst, pair_snd, sub, tagged_to_value, truthy, tval, TaggedValue,
};
use rustc_hash::FxHashMap;
use serde_json::{json, Value};
use std::rc::Rc;

// ---------------------------------------------------------------------------
// Round-trip: serde_json::Value -> TaggedValue -> serde_json::Value
// ---------------------------------------------------------------------------

fn round_trip(v: Value) -> Value {
    let t: TaggedValue = v.into();
    tagged_to_value(&t)
}

#[test]
fn round_trip_null() {
    assert_eq!(round_trip(Value::Null), Value::Null);
}

#[test]
fn round_trip_bool() {
    assert_eq!(round_trip(json!(true)), json!(true));
    assert_eq!(round_trip(json!(false)), json!(false));
}

#[test]
fn round_trip_int() {
    assert_eq!(round_trip(json!(42)), json!(42));
    assert_eq!(round_trip(json!(0)), json!(0));
    assert_eq!(round_trip(json!(-7)), json!(-7));
}

#[test]
fn round_trip_float() {
    assert_eq!(round_trip(json!(3.14)), json!(3.14));
    assert_eq!(round_trip(json!(-0.5)), json!(-0.5));
}

#[test]
fn round_trip_string() {
    assert_eq!(round_trip(json!("hello")), json!("hello"));
    assert_eq!(round_trip(json!("")), json!(""));
}

#[test]
fn round_trip_bytes() {
    // Bytes use the {"__bytes__": [n, ...]} JSON encoding (ADR-0083 §2.1).
    let v = json!({"__bytes__": [0xDE, 0xAD, 0xBE, 0xEF]});
    assert_eq!(round_trip(v.clone()), v);
    // Empty buffer round-trips.
    let empty = json!({"__bytes__": []});
    assert_eq!(round_trip(empty.clone()), empty);
    // All byte values survive.
    let all_bytes: Vec<Value> = (0u8..=255).map(|b| json!(b)).collect();
    let full = json!({ "__bytes__": Value::Array(all_bytes) });
    assert_eq!(round_trip(full.clone()), full);
}

#[test]
fn bytes_accessor_and_truthiness() {
    use handl_value::bytes;
    let bv = bytes(vec![0x00, 0x01, 0xFF]);
    assert_eq!(bv.as_bytes(), Some(&[0x00u8, 0x01, 0xFF][..]));
    // Non-empty bytes is truthy; empty bytes is falsy.
    assert!(truthy(&bv));
    assert!(!truthy(&bytes(Vec::<u8>::new())));
    // Equality is structural on the buffer contents.
    assert!(eq(&bytes(vec![1, 2, 3]), &bytes(vec![1, 2, 3])));
    assert!(!eq(&bytes(vec![1, 2, 3]), &bytes(vec![1, 2, 4])));
}

#[test]
fn round_trip_array() {
    assert_eq!(round_trip(json!([1, 2, 3])), json!([1, 2, 3]));
    assert_eq!(
        round_trip(json!([true, "x", null])),
        json!([true, "x", null])
    );
}

#[test]
fn round_trip_object() {
    assert_eq!(
        round_trip(json!({"a": 1, "b": "two"})),
        json!({"a": 1, "b": "two"})
    );
}

#[test]
fn round_trip_pair() {
    let p = json!({"__pair__": [1, 2]});
    let t: TaggedValue = p.clone().into();
    // Should be the dedicated Pair variant, not an Obj.
    assert!(matches!(t, TaggedValue::Pair(_)));
    assert_eq!(tagged_to_value(&t), p);
}

#[test]
fn round_trip_either_left() {
    let e = json!({"__either__": "left", "value": 42});
    let t: TaggedValue = e.clone().into();
    assert!(matches!(t, TaggedValue::EitherLeft(_)));
    assert_eq!(tagged_to_value(&t), e);
}

#[test]
fn round_trip_either_right() {
    let e = json!({"__either__": "right", "value": "hi"});
    let t: TaggedValue = e.clone().into();
    assert!(matches!(t, TaggedValue::EitherRight(_)));
    assert_eq!(tagged_to_value(&t), e);
}

#[test]
fn round_trip_arrow() {
    let a = json!({
        "__arrow__": true,
        "params": ["x", "y"],
        "body": 5,
        "env": {"z": 3}
    });
    let t: TaggedValue = a.clone().into();
    match &t {
        TaggedValue::Arrow {
            params, body, env, ..
        } => {
            assert_eq!(params.len(), 2);
            assert_eq!(params[0], "x");
            assert_eq!(params[1], "y");
            assert_eq!(*body, 5);
            assert_eq!(env.get("z").and_then(|v| v.as_i64()), Some(3));
        }
        _ => panic!("expected Arrow variant, got {:?}", t),
    }
    assert_eq!(tagged_to_value(&t), a);
}

// ---------------------------------------------------------------------------
// Arithmetic
// ---------------------------------------------------------------------------

#[test]
fn arithmetic_int_plus_int() {
    let r = add(&TaggedValue::Int(2), &TaggedValue::Int(3)).unwrap();
    assert_eq!(r.as_i64(), Some(5));
}

#[test]
fn arithmetic_int_plus_float() {
    let r = add(&TaggedValue::Int(2), &TaggedValue::Float(3.5)).unwrap();
    assert_eq!(r.as_f64(), Some(5.5));
    assert!(matches!(r, TaggedValue::Float(_)));
}

#[test]
fn arithmetic_float_plus_float() {
    let r = add(&TaggedValue::Float(1.5), &TaggedValue::Float(2.5)).unwrap();
    assert_eq!(r.as_f64(), Some(4.0));
}

#[test]
fn arithmetic_type_error() {
    let err = add(&TaggedValue::Str(Rc::from("a")), &TaggedValue::Int(1));
    assert!(err.is_err());
}

#[test]
fn arithmetic_sub_mul_div_mod() {
    assert_eq!(
        sub(&TaggedValue::Int(10), &TaggedValue::Int(3))
            .unwrap()
            .as_i64(),
        Some(7)
    );
    assert_eq!(
        mul(&TaggedValue::Int(4), &TaggedValue::Int(5))
            .unwrap()
            .as_i64(),
        Some(20)
    );
    assert_eq!(
        div(&TaggedValue::Int(20), &TaggedValue::Int(4))
            .unwrap()
            .as_i64(),
        Some(5)
    );
    assert_eq!(
        mod_(&TaggedValue::Int(10), &TaggedValue::Int(3))
            .unwrap()
            .as_i64(),
        Some(1)
    );
}

#[test]
fn arithmetic_div_by_zero() {
    assert!(div(&TaggedValue::Int(1), &TaggedValue::Int(0)).is_err());
    assert!(mod_(&TaggedValue::Int(1), &TaggedValue::Int(0)).is_err());
}

// ---------------------------------------------------------------------------
// Comparison
// ---------------------------------------------------------------------------

#[test]
fn comparison_lt() {
    assert!(lt(&TaggedValue::Int(1), &TaggedValue::Int(2)).unwrap());
    assert!(!lt(&TaggedValue::Int(5), &TaggedValue::Int(2)).unwrap());
    assert!(lt(&TaggedValue::Float(1.0), &TaggedValue::Float(2.0)).unwrap());
    assert!(lt(&TaggedValue::Int(1), &TaggedValue::Float(2.0)).unwrap());
}

#[test]
fn comparison_eq_ints_floats_strings() {
    assert!(eq(&TaggedValue::Int(1), &TaggedValue::Int(1)));
    assert!(!eq(&TaggedValue::Int(1), &TaggedValue::Int(2)));
    assert!(eq(&TaggedValue::Float(1.5), &TaggedValue::Float(1.5)));
    assert!(eq(
        &TaggedValue::Str(Rc::from("abc")),
        &TaggedValue::Str(Rc::from("abc"))
    ));
    assert!(!eq(
        &TaggedValue::Str(Rc::from("abc")),
        &TaggedValue::Str(Rc::from("abd"))
    ));
    // Cross-numeric equality.
    assert!(eq(&TaggedValue::Int(2), &TaggedValue::Float(2.0)));
}

// ---------------------------------------------------------------------------
// Pair helpers
// ---------------------------------------------------------------------------

#[test]
fn pair_helpers() {
    let p = pair(TaggedValue::Int(1), TaggedValue::Str(Rc::from("two")));
    assert_eq!(pair_fst(&p).unwrap().as_i64(), Some(1));
    assert_eq!(pair_snd(&p).unwrap().as_str(), Some("two"));
    // Non-pair returns None.
    assert!(pair_fst(&TaggedValue::Int(1)).is_none());
    assert!(pair_snd(&TaggedValue::Null).is_none());
}

// ---------------------------------------------------------------------------
// Either helpers
// ---------------------------------------------------------------------------

#[test]
fn either_helpers() {
    let l = either_left(TaggedValue::Int(10));
    assert!(is_either_left(&l));
    assert!(!is_either_right(&l));
    assert_eq!(either_value(&l).unwrap().as_i64(), Some(10));

    let r = either_right(TaggedValue::Str(Rc::from("x")));
    assert!(!is_either_left(&r));
    assert!(is_either_right(&r));
    assert_eq!(either_value(&r).unwrap().as_str(), Some("x"));

    // Non-either returns false / None.
    assert!(!is_either_left(&TaggedValue::Null));
    assert!(!is_either_right(&TaggedValue::Null));
    assert!(either_value(&TaggedValue::Int(1)).is_none());
}

// ---------------------------------------------------------------------------
// Truthiness (mirrors handl rules: false, null, 0, "" are falsy)
// ---------------------------------------------------------------------------

#[test]
fn truthiness_rules() {
    // Falsy
    assert!(!truthy(&TaggedValue::Null));
    assert!(!truthy(&TaggedValue::Bool(false)));
    assert!(!truthy(&TaggedValue::Int(0)));
    assert!(!truthy(&TaggedValue::Float(0.0)));
    assert!(!truthy(&TaggedValue::Str(Rc::from(""))));

    // Truthy
    assert!(truthy(&TaggedValue::Bool(true)));
    assert!(truthy(&TaggedValue::Int(1)));
    assert!(truthy(&TaggedValue::Int(-1)));
    assert!(truthy(&TaggedValue::Float(3.14)));
    assert!(truthy(&TaggedValue::Str(Rc::from("x"))));
    // Objects and arrays are truthy (mirrors is_truthy_object_and_array).
    assert!(truthy(&TaggedValue::Arr(Rc::from(Vec::new()))));
    let mut m = FxHashMap::default();
    m.insert(Rc::from("a"), TaggedValue::Int(1));
    assert!(truthy(&TaggedValue::Obj(Rc::new(m))));
    // Pairs and Eithers are truthy.
    assert!(truthy(&pair(TaggedValue::Null, TaggedValue::Null)));
    assert!(truthy(&either_left(TaggedValue::Null)));
}

// ---------------------------------------------------------------------------
// tval! macro
// ---------------------------------------------------------------------------

#[test]
fn tval_macro_null() {
    let v = tval!(null);
    assert!(v.is_null());
    assert!(matches!(v, TaggedValue::Null));
}

#[test]
fn tval_macro_bool() {
    assert_eq!(tval!(true).as_bool(), Some(true));
    assert_eq!(tval!(false).as_bool(), Some(false));
}

#[test]
fn tval_macro_int() {
    let v = tval!(42);
    assert_eq!(v.as_i64(), Some(42));
    assert!(matches!(v, TaggedValue::Int(_)));
}

#[test]
fn tval_macro_float() {
    let v = tval!(3.14);
    assert_eq!(v.as_f64(), Some(3.14));
    assert!(matches!(v, TaggedValue::Float(_)));
}

#[test]
fn tval_macro_str() {
    let v = tval!("hello");
    assert_eq!(v.as_str(), Some("hello"));
    assert!(matches!(v, TaggedValue::Str(_)));
}

#[test]
fn tval_macro_array() {
    let v = tval!([1, 2, 3]);
    let arr = v.as_array().unwrap();
    assert_eq!(arr.len(), 3);
    assert_eq!(arr[0].as_i64(), Some(1));
    assert_eq!(arr[1].as_i64(), Some(2));
    assert_eq!(arr[2].as_i64(), Some(3));
}

#[test]
fn tval_macro_array_mixed() {
    let v = tval!([1, "two", true, null]);
    let arr = v.as_array().unwrap();
    assert_eq!(arr.len(), 4);
    assert_eq!(arr[0].as_i64(), Some(1));
    assert_eq!(arr[1].as_str(), Some("two"));
    assert_eq!(arr[2].as_bool(), Some(true));
    assert!(arr[3].is_null());
}

#[test]
fn tval_macro_object() {
    let v = tval!({"a": 1, "b": true, "c": "x"});
    assert_eq!(v.get("a").unwrap().as_i64(), Some(1));
    assert_eq!(v.get("b").unwrap().as_bool(), Some(true));
    assert_eq!(v.get("c").unwrap().as_str(), Some("x"));
    assert!(v.get("missing").is_none());
}

#[test]
fn tval_macro_nested() {
    let v = tval!({"arr": [1, 2], "obj": {"k": 3}});
    let arr = v.get("arr").unwrap().as_array().unwrap();
    assert_eq!(arr.len(), 2);
    let inner = v.get("obj").unwrap();
    assert_eq!(inner.get("k").unwrap().as_i64(), Some(3));
}
