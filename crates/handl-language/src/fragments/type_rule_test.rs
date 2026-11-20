use super::*;
use crate::term::{ArrSource, Term};
use hnl_engine::TermData;
use serde_json::Value;

/// Convert `TermData` back to `Term` for APIs that require `Term`.
fn t(td: TermData) -> Term {
    td.to_term().expect("TermData -> Term conversion")
}

/// Judgment op without a literal payload (mirrors `TermData::op`).
fn op_judgment(name: &str, args: Vec<TermData>) -> TermData {
    TermData::op(name, args, &ArrSource::Judgment, None)
}

/// Judgment op with a literal payload (mirrors `TermData::op`).
fn op_judgment_lit(name: &str, args: Vec<TermData>, lit: impl Into<Value>) -> TermData {
    TermData::op(name, args, &ArrSource::Judgment, Some(lit.into()))
}

#[test]
fn construct_and_accessors() {
    let def = TypeRuleDef::new(
        "type.lit",
        "lit",
        t(op_judgment_lit("synth_child", vec![], Value::from(0u64))),
    )
    .with_replaces(vec!["type.lit.old".into()])
    .with_requires(vec!["type.bool".into()]);
    assert_eq!(def.id(), "type.lit");
    assert_eq!(def.node_kind, "lit");
    assert!(def.check.is_none());
    assert_eq!(def.replaces(), &["type.lit.old".to_string()]);
    assert_eq!(def.requires(), &["type.bool".to_string()]);
    assert_eq!(def.identity_key(), "lit");
}

#[test]
fn with_check_sets_check_scheme() {
    let def = TypeRuleDef::new("type.lambda", "lambda", t(op_judgment("construct", vec![])))
        .with_check(t(op_judgment("check_child", vec![])));
    assert!(def.check.is_some());
}

#[test]
fn serde_roundtrip_synth_only() {
    let def = TypeRuleDef::new(
        "type.lit",
        "lit",
        t(op_judgment_lit("synth_child", vec![], Value::from(0u64))),
    );
    let j = serde_json::to_string(&def).unwrap();
    let back: TypeRuleDef = serde_json::from_str(&j).unwrap();
    assert_eq!(def, back);
}

#[test]
fn serde_roundtrip_with_check() {
    let def = TypeRuleDef::new("type.lambda", "lambda", t(op_judgment("construct", vec![])))
        .with_check(t(op_judgment("check_child", vec![])));
    let j = serde_json::to_string(&def).unwrap();
    let back: TypeRuleDef = serde_json::from_str(&j).unwrap();
    assert_eq!(def, back);
}

#[test]
fn serde_omits_check_when_none() {
    let def = TypeRuleDef::new("type.lit", "lit", t(op_judgment("id", vec![])));
    let j = serde_json::to_string(&def).unwrap();
    assert!(
        !j.contains("check"),
        "check should be omitted when None: {j}"
    );
}

#[test]
fn equality() {
    let a = TypeRuleDef::new("a", "k", t(op_judgment("id", vec![])));
    let b = TypeRuleDef::new("a", "k", t(op_judgment("id", vec![])));
    assert_eq!(a, b);
}
