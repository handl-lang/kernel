//! Integration test: a non-trivial `Language` serializes to JSON and
//! deserializes to an equal `Language`.

use handl_language::{
    AstShapeDef, AstShapeRef, CapabilityDecl, EvalSchemeDef, GrammarPosition, GrammarRow, Language,
    SchemeVersion, Term, TokenKindDef,
};
use plugin_engine::{ArrSource, TermData};
use serde_json::Value;

/// Convert `TermData` back to `Term` for APIs that require `Term`.
fn t(td: TermData) -> Term {
    td.to_term().expect("TermData -> Term conversion")
}

/// Native op without a literal payload.
fn op_native(name: &str, args: Vec<TermData>) -> TermData {
    TermData::op(name, args, &ArrSource::Native, None)
}

/// Native op with a literal payload.
fn op_lit(name: &str, args: Vec<TermData>, lit: Value) -> TermData {
    TermData::op(name, args, &ArrSource::Native, Some(lit))
}

/// Foreign op.
fn op_foreign(name: &str, args: Vec<TermData>) -> TermData {
    TermData::op(name, args, &ArrSource::Foreign(name.into()), None)
}

/// Constant arrow with the given value.
fn arr(value: Value) -> TermData {
    TermData::arr(value)
}

fn nontrivial_language() -> Language {
    let mut lang = Language::new();
    lang.tokens
        .merge(TokenKindDef::new("token.num").with_label("number"))
        .unwrap();
    lang.tokens.merge(TokenKindDef::new("token.plus")).unwrap();
    lang.grammar
        .merge(
            GrammarRow::new(
                "grammar.add.infix",
                "token.plus",
                GrammarPosition::Infix,
                AstShapeRef::new("binary.add", 2),
            )
            .with_binding_power(10, 11),
        )
        .unwrap();
    lang.ast
        .merge(
            AstShapeDef::new("ast.binary.add", "binary.add")
                .with_payload_schema(serde_json::json!({"type": "object"})),
        )
        .unwrap();
    lang.eval
        .merge(EvalSchemeDef::new(
            "eval.binary.add",
            "binary.add",
            t(op_native(
                "add",
                vec![
                    op_lit("proj_child", vec![], Value::from(0u64)),
                    op_lit("proj_child", vec![], Value::from(1u64)),
                ],
            )),
        ))
        .unwrap();
    lang.eval
        .merge(EvalSchemeDef::new(
            "eval.io",
            "io",
            t(op_foreign(
                "fs.read",
                vec![op_lit("proj_child", vec![], Value::from(0u64))],
            )),
        ))
        .unwrap();
    lang.caps
        .merge(CapabilityDecl::new("net.connect").with_description("network"))
        .unwrap();
    lang
}

#[test]
fn json_roundtrip_equal() {
    let lang = nontrivial_language();
    let j = serde_json::to_string_pretty(&lang).unwrap();
    let back: Language = serde_json::from_str(&j).unwrap();
    assert_eq!(lang, back);
}

#[test]
fn json_contains_version_field() {
    let lang = nontrivial_language();
    let j = serde_json::to_string(&lang).unwrap();
    assert!(j.contains("\"scheme_version\""));
    assert!(j.contains("\"v2\""));
    let back: Language = serde_json::from_str(&j).unwrap();
    assert_eq!(back.scheme_version, SchemeVersion::v2());
}

#[test]
fn empty_language_roundtrip() {
    let lang = Language::new();
    let j = serde_json::to_string(&lang).unwrap();
    let back: Language = serde_json::from_str(&j).unwrap();
    assert_eq!(lang, back);
}

#[test]
fn scheme_with_nested_foreign_roundtrips_through_language() {
    let mut lang = Language::new();
    lang.eval
        .merge(EvalSchemeDef::new(
            "eval.complex",
            "complex",
            // cond >>> arr(tag) >>> Choice(then, else)
            t(TermData::seq(
                TermData::seq(
                    op_foreign("fs.stat", vec![arr(Value::from("/x"))]),
                    op_native("tag", vec![]),
                ),
                TermData::choice(
                    TermData::app(
                        op_lit("proj_env", vec![], Value::String("f".into())),
                        vec![op_lit("proj_child", vec![], Value::from(0u64))],
                    ),
                    arr(Value::Bool(false)),
                ),
            )),
        ))
        .unwrap();
    let j = serde_json::to_string(&lang).unwrap();
    let back: Language = serde_json::from_str(&j).unwrap();
    assert_eq!(lang, back);
}
