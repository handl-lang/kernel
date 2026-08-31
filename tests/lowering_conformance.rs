//! Lowering-conformance tests for `lower_v1_to_v2` (ADR-0052 lowering table).
//!
//! Each test constructs a v1 `Scheme` and asserts the exact `SchemeV2` shape
//! produced by `lower_v1_to_v2`, covering every row of the ADR-0052 lowering
//! table. These are regression/conformance tests for the *current* lowering
//! behavior; they do not modify the kernel.

use handl_language::{ArrSource, LangError, Scheme, SchemeV2, lower_v1_to_v2};
use serde_json::Value;

/// Lower a non-`Vau` scheme, panicking on error.
fn lower(s: &Scheme) -> SchemeV2 {
    lower_v1_to_v2(s).expect("lowering should succeed for non-Vau")
}

// --- ADR-0052 lowering table, row by row ---

#[test]
fn lit_lowers_to_const_arr() {
    let s = Scheme::lit(42);
    assert_eq!(
        lower(&s),
        SchemeV2::arr_native_lit("const", vec![], Value::from(42))
    );
}

#[test]
fn var_lowers_to_proj_env_arr() {
    let s = Scheme::var("x");
    assert_eq!(
        lower(&s),
        SchemeV2::arr_native_lit("proj_env", vec![], Value::String("x".into()))
    );
}

#[test]
fn var_payload_lowers_to_proj_env_arr() {
    // The "$payload" sentinel name is a plain string for the lowering.
    let s = Scheme::var("$payload");
    assert_eq!(
        lower(&s),
        SchemeV2::arr_native_lit("proj_env", vec![], Value::String("$payload".into()))
    );
}

#[test]
fn child_lowers_to_proj_child_arr_u64() {
    // `lower_v1_to_v2` emits `Value::from(i.index() as u64)`.
    let s = Scheme::child(3);
    assert_eq!(
        lower(&s),
        SchemeV2::arr_native_lit("proj_child", vec![], Value::from(3u64))
    );
}

#[test]
fn prim_lowers_to_native_arr_with_lowered_args() {
    let s = Scheme::prim("add", vec![Scheme::child(0), Scheme::child(1)]);
    assert_eq!(
        lower(&s),
        SchemeV2::Arr {
            op: "add".into(),
            args: vec![
                SchemeV2::arr_native_lit("proj_child", vec![], Value::from(0u64)),
                SchemeV2::arr_native_lit("proj_child", vec![], Value::from(1u64)),
            ],
            source: ArrSource::Native,
            lit: None,
        }
    );
}

#[test]
fn foreign_lowers_to_foreign_arr_with_lowered_args() {
    let s = Scheme::foreign("fs.read", vec![Scheme::child(0)]);
    assert_eq!(
        lower(&s),
        SchemeV2::Arr {
            op: "fs.read".into(),
            args: vec![SchemeV2::arr_native_lit("proj_child", vec![], Value::from(0u64))],
            source: ArrSource::Foreign("fs.read".into()),
            lit: None,
        }
    );
}

#[test]
fn bind_lowers_to_seq_seq_extend_env_body() {
    // value >>> arr(extend_env name) >>> body
    let s = Scheme::Bind {
        name: "x".into(),
        value: Box::new(Scheme::lit(1)),
        body: Box::new(Scheme::var("x")),
    };
    assert_eq!(
        lower(&s),
        SchemeV2::seq(
            SchemeV2::seq(
                SchemeV2::arr_native_lit("const", vec![], Value::from(1)),
                SchemeV2::arr_native_lit("extend_env", vec![], Value::String("x".into())),
            ),
            SchemeV2::arr_native_lit("proj_env", vec![], Value::String("x".into())),
        )
    );
}

#[test]
fn app_lowers_to_dynamic_app() {
    // The lowering conservatively emits the dynamic `app` form for every
    // v1 `App` (no scope info to identify a static callee).
    let s = Scheme::App {
        callee: Box::new(Scheme::var("f")),
        args: vec![Scheme::lit(1), Scheme::lit(2)],
    };
    assert_eq!(
        lower(&s),
        SchemeV2::app(
            SchemeV2::arr_native_lit("proj_env", vec![], Value::String("f".into())),
            vec![
                SchemeV2::arr_native_lit("const", vec![], Value::from(1)),
                SchemeV2::arr_native_lit("const", vec![], Value::from(2)),
            ],
        )
    );
}

#[test]
fn branch_lowers_to_seq_seq_tag_choice() {
    // cond >>> arr(tag) >>> Choice(then, else)
    let s = Scheme::Branch {
        cond: Box::new(Scheme::var("c")),
        then_: Box::new(Scheme::lit(1)),
        else_: Box::new(Scheme::lit(2)),
    };
    assert_eq!(
        lower(&s),
        SchemeV2::seq(
            SchemeV2::seq(
                SchemeV2::arr_native_lit("proj_env", vec![], Value::String("c".into())),
                SchemeV2::arr_native("tag", vec![]),
            ),
            SchemeV2::choice(
                SchemeV2::arr_native_lit("const", vec![], Value::from(1)),
                SchemeV2::arr_native_lit("const", vec![], Value::from(2)),
            ),
        )
    );
}

#[test]
fn vau_lowers_to_error() {
    let s = Scheme::vau(vec!["a".into()], Scheme::lit(42));
    let err = lower_v1_to_v2(&s).unwrap_err();
    match err {
        LangError::Engine(msg) => assert!(msg.contains("Vau"), "message should mention Vau: {msg}"),
        other => panic!("expected Engine error, got {other:?}"),
    }
}
