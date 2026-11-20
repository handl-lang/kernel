use super::*;
use crate::term::{ArrSource, Term};
use hnl_engine::TermData;
use serde_json::Value;

/// Convert `TermData` back to `Term` for APIs that require `Term`.
fn t(td: TermData) -> Term {
    td.to_term().expect("TermData -> Term conversion")
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
        TermData::arr(lit.into())
    } else {
        TermData::op(name, args, &ArrSource::Native, Some(lit.into()))
    }
}

#[test]
fn construct_and_accessors() {
    let def = EvalSchemeDef::new(
        "eval.binary.add",
        "binary.add",
        t(op_native(
            "add",
            vec![
                op_lit("proj_child", vec![], Value::from(0u64)),
                op_lit("proj_child", vec![], Value::from(1u64)),
            ],
        )),
    )
    .with_replaces(vec!["eval.add.old".into()])
    .with_requires(vec!["token.plus".into()]);
    assert_eq!(def.id(), "eval.binary.add");
    assert_eq!(def.node_kind, "binary.add");
    assert_eq!(def.replaces(), &["eval.add.old".to_string()]);
    assert_eq!(def.requires(), &["token.plus".to_string()]);
    assert_eq!(def.identity_key(), "binary.add");
}

#[test]
fn serde_roundtrip() {
    let def = EvalSchemeDef::new(
        "eval.lit",
        "lit",
        t(op_lit("const", vec![], Value::from(42))),
    );
    let j = serde_json::to_string(&def).unwrap();
    let back: EvalSchemeDef = serde_json::from_str(&j).unwrap();
    assert_eq!(def, back);
}

#[test]
fn equality() {
    let a = EvalSchemeDef::new("a", "k", t(op_native("id", vec![])));
    let b = EvalSchemeDef::new("a", "k", t(op_native("id", vec![])));
    assert_eq!(a, b);
}
