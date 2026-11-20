use super::*;
use crate::fragments::token_kind::TokenKindDef;
use serde_json::json;

#[test]
fn language_value_round_trips() {
    let mut lang = Language::new();
    lang.tokens.merge(TokenKindDef::new("token.num")).unwrap();
    let v = language_value(&lang);
    assert!(is_language_value(&v));
    assert_eq!(as_language(&v), Some(lang));
}

#[test]
fn plain_string_is_not_a_language_value() {
    let v = Value::String("handl".to_string());
    assert!(!is_language_value(&v));
    assert_eq!(as_language(&v), None);
}

#[test]
fn equal_languages_produce_equal_values() {
    let mut lang = Language::new();
    lang.tokens.merge(TokenKindDef::new("token.num")).unwrap();
    assert_eq!(language_value(&lang), language_value(&lang));
}

#[test]
fn ast_value_round_trips() {
    let mut ast = Ast::new();
    ast.push(AstNode::new("lit").with_payload(Value::from(42)));
    let v = ast_value(&ast);
    assert!(is_ast_value(&v));
    assert_eq!(as_ast(&v), Some(ast));
}

#[test]
fn plain_string_is_not_an_ast_value() {
    let v = Value::String("x".to_string());
    assert!(!is_ast_value(&v));
    assert_eq!(as_ast(&v), None);
}

#[test]
fn tag_value_mints_tagged_object() {
    let v = tag_value("type.collection", &json!({ "name": "number" })).expect("mint succeeds");
    assert!(is_tag_value(&v));
    assert_eq!(as_tag(&v), Some("type.collection"));
    assert_eq!(v["name"], json!("number"));
    assert_eq!(v["__tag__"], json!("type.collection"));
}

#[test]
fn tag_value_null_payload_is_empty() {
    let v = tag_value("unit", &Value::Null).expect("mint succeeds");
    assert_eq!(as_tag(&v), Some("unit"));
    assert_eq!(v.as_object().unwrap().len(), 1);
}

#[test]
fn tag_value_wraps_non_object_payload_in_value() {
    // ADR-0077: non-object payloads are wrapped in {value: ...} so
    // that tag.tag("ok", 42) produces {"__tag__": "ok", "value": 42}.
    let v = tag_value("ok", &json!(42)).expect("mint succeeds");
    assert_eq!(as_tag(&v), Some("ok"));
    assert_eq!(v["value"], json!(42));

    let v = tag_value("err", &json!("oops")).expect("mint succeeds");
    assert_eq!(as_tag(&v), Some("err"));
    assert_eq!(v["value"], json!("oops"));
}

#[test]
fn tag_value_rejects_smuggled_tag_key() {
    // A payload that already carries `__tag__` cannot be re-tagged —
    // the host `tag` op always sets the tag; the payload must not smuggle
    // one in (forgery prevention, ADR-0055 §3).
    assert!(tag_value("type.pi", &json!({ "__tag__": "type.collection" })).is_none());
}

#[test]
fn plain_string_is_not_a_tag_value() {
    let v = Value::String("number".to_string());
    assert!(!is_tag_value(&v));
    assert_eq!(as_tag(&v), None);
}

#[test]
fn tagged_value_with_non_string_tag_is_not_a_tag_value() {
    // A `__tag__` that isn't a string is not a valid tag (defensive).
    let v = json!({ "__tag__": 5, "name": "number" });
    assert!(!is_tag_value(&v));
    assert_eq!(as_tag(&v), None);
}

#[test]
fn is_reserved_value_key_recognizes_sentinels() {
    assert!(is_reserved_value_key("__tag__"));
    assert!(is_reserved_value_key("__registry__"));
    assert!(is_reserved_value_key("__language__"));
    assert!(is_reserved_value_key("__ast__"));
    assert!(is_reserved_value_key("__arrow__"));
    assert!(is_reserved_value_key("__compiled__"));
    assert!(!is_reserved_value_key("name"));
    assert!(!is_reserved_value_key("__proto__"));
}

#[test]
fn tagged_values_equal_by_structure() {
    // ADR-0055 §5: equality is structural (same tag + payload ⇒ equal).
    let a = tag_value("type.collection", &json!({ "name": "number" })).unwrap();
    let b = tag_value("type.collection", &json!({ "name": "number" })).unwrap();
    assert_eq!(a, b);
    let c = tag_value("type.collection", &json!({ "name": "string" })).unwrap();
    assert_ne!(a, c);
    assert_ne!(a, json!("number"));
}
