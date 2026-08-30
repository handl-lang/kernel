//! Integration test: a non-trivial `Language` serializes to JSON and
//! deserializes to an equal `Language`.

use handl_language::{
    AstShapeDef, AstShapeRef, CapabilityDecl, EvalSchemeDef, GrammarPosition, GrammarRow,
    Language, Scheme, SchemeVersion, TokenKindDef,
};
use serde_json::Value;

fn nontrivial_language() -> Language {
    let mut lang = Language::new();
    lang.tokens.merge(TokenKindDef::new("token.num").with_label("number")).unwrap();
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
            Scheme::Prim {
                op: "add".into(),
                args: vec![Scheme::child(0), Scheme::child(1)],
            },
        ))
        .unwrap();
    lang.eval
        .merge(EvalSchemeDef::new(
            "eval.io",
            "io",
            Scheme::foreign("fs.read", vec![Scheme::child(0)]),
        ))
        .unwrap();
    lang.caps.merge(CapabilityDecl::new("net.connect").with_description("network")).unwrap();
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
    assert!(j.contains("\"v1\""));
    let back: Language = serde_json::from_str(&j).unwrap();
    assert_eq!(back.scheme_version, SchemeVersion::v1());
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
            Scheme::Branch {
                cond: Box::new(Scheme::Foreign {
                    name: "fs.stat".into(),
                    args: vec![Scheme::lit(Value::from("/x"))],
                }),
                then_: Box::new(Scheme::App {
                    callee: Box::new(Scheme::var("f")),
                    args: vec![Scheme::child(0)],
                }),
                else_: Box::new(Scheme::lit(Value::Null)),
            },
        ))
        .unwrap();
    let j = serde_json::to_string(&lang).unwrap();
    let back: Language = serde_json::from_str(&j).unwrap();
    assert_eq!(lang, back);
}
