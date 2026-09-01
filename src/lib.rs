//! # handl-language
//!
//! The `Language` data schema and staged `lex`/`parse`/`eval` dispatch
//! signatures for the HAndL platform (ADR-0044).
//!
//! A `Language` is pure serializable data — no Rust trait objects, closures,
//! or `Box<dyn Behavior>`. It is built by merging typed fragments into six
//! [`FragmentSet`]s and is `serde`-serializable end to end. Evaluation
//! semantics are expressed as [`Scheme`] combinators (a small, versioned
//! core); surface constructs are [`DesugarRule`]s that lower to that core.
//!
//! Phase 1 provides the data schema, the `Ast` arena, the `Scheme` combinator
//! set, desugar rules, staged dispatch signatures (returning
//! [`LangError::NotImplemented`]), scheme versioning, and capability
//! derivation. Engines, runtime, and migrations are later phases.

#![warn(missing_docs)]

/// The `Ast` arena and `AstRef` handle.
pub mod ast;
/// Capability set derivation.
pub mod capabilities;
/// Desugar rules.
pub mod desugar;
/// Error types.
pub mod error;
/// The `Fragment` trait.
pub mod fragment;
/// `FragmentSet<T>` merge with declared-override policy.
pub mod fragment_set;
/// Fragment type definitions.
pub mod fragments;
/// The `Language` struct.
pub mod language;
/// The arrow-calculus `Scheme` kernel (ADR-0052).
pub mod scheme;
/// Staged `lex`/`parse`/`eval` dispatch entry points.
pub mod staged;
/// Scheme combinator versioning.
pub mod version;

pub use ast::{Ast, AstNode, AstRef, Span};
pub use capabilities::{capabilities, foreign_names, subset_of};
pub use desugar::{DesugarRule, desugar};
pub use error::LangError;
pub use fragment::Fragment;
pub use fragment_set::FragmentSet;
pub use fragments::{
    AstDesugarChild, AstDesugarCondition, AstDesugarRule, AstShapeDef, AstShapeRef, CapabilityDecl, ChildSeparator,
    DelimitedShape, EvalSchemeDef, GrammarPosition, GrammarRow, LexerPattern, LexerRuleDef,
    LiteralKind, OptionSchema, PairShape, TokenKindDef, TypeRuleDef,
};
pub use language::Language;
pub use scheme::{ArrSource, Scheme};
pub use staged::{Source, Token, Tokens, ValueOut, eval, lex, parse, run};
pub use version::SchemeVersion;

/// The value type used throughout the crate: a re-export of `serde_json::Value`.
pub type Value = serde_json::Value;

/// The sentinel object key marking a [`Value`] as carrying a serialized
/// [`Language`] (ADR-0041: `Language` is a first-class value).
///
/// A language value is a JSON object `{"__language__": <serialized Language>}`.
/// The full [`Language`] data is embedded in the value — this is a genuine
/// first-class value, not a string handle into a registry. Use
/// [`language_value`] to construct one and [`as_language`] to extract it.
pub const LANGUAGE_VALUE_KEY: &str = "__language__";

/// Wrap a [`Language`] into a [`Value`] tagged so it can be recognized by
/// [`as_language`].
///
/// The entire [`Language`] is serialized into the value, so a handl program
/// can hold, pass, and store a `Language` as an ordinary value. The meta host
/// functions (`lex`/`parse`/`eval`/`run`/`compile`) accept such a value as
/// their first argument and operate on the embedded [`Language`] directly — no
/// string-handle registry lookup is required.
///
/// # Panics
///
/// Panics if `lang` fails to serialize (it is always serde-serializable).
pub fn language_value(lang: &Language) -> Value {
    let inner = serde_json::to_value(lang).expect("Language is serde-serializable");
    serde_json::json!({ LANGUAGE_VALUE_KEY: inner })
}

/// Extract a [`Language`] from a [`Value`] produced by [`language_value`].
///
/// Returns `None` if the value is not a tagged language value or cannot be
/// deserialized.
pub fn as_language(value: &Value) -> Option<Language> {
    value
        .get(LANGUAGE_VALUE_KEY)
        .and_then(|v| serde_json::from_value(v.clone()).ok())
}

/// Whether `value` is a tagged language value (produced by [`language_value`]).
pub fn is_language_value(value: &Value) -> bool {
    value.get(LANGUAGE_VALUE_KEY).is_some()
}

/// The sentinel object key marking a [`Value`] as carrying a serialized
/// [`Ast`] subtree — an unevaluated expression (ADR-0041 §6, ADR-0045).
///
/// A vau-bound unevaluated child is a JSON object
/// `{"__ast__": <serialized Ast>}`. The embedded [`Ast`] is the subtree
/// rooted at the child (the child node plus all transitively-referenced
/// descendants, reindexed into a standalone arena), so the meta `eval`
/// host function can consume it directly: `eval(self, ast_value)`. Use
/// [`ast_value`] to construct one and [`as_ast`] to extract it.
pub const AST_VALUE_KEY: &str = "__ast__";

/// Wrap an [`Ast`] into a [`Value`] tagged so it can be recognized by
/// [`as_ast`].
///
/// The entire [`Ast`] is serialized into the value, so a handl program can
/// hold and pass an unevaluated expression as an ordinary value. The meta
/// `eval` host function accepts such a value as its second argument.
///
/// # Panics
///
/// Panics if `ast` fails to serialize (it is always serde-serializable).
pub fn ast_value(ast: &Ast) -> Value {
    let inner = serde_json::to_value(ast).expect("Ast is serde-serializable");
    serde_json::json!({ AST_VALUE_KEY: inner })
}

/// Extract an [`Ast`] from a [`Value`] produced by [`ast_value`].
///
/// Returns `None` if the value is not a tagged ast value or cannot be
/// deserialized.
pub fn as_ast(value: &Value) -> Option<Ast> {
    value
        .get(AST_VALUE_KEY)
        .and_then(|v| serde_json::from_value(v.clone()).ok())
}

/// Whether `value` is a tagged ast value (produced by [`ast_value`]).
pub fn is_ast_value(value: &Value) -> bool {
    value.get(AST_VALUE_KEY).is_some()
}

/// The sentinel object key marking a [`Value`] as a **tagged value**
/// (ADR-0055 — Tagged Values).
///
/// A tagged value is a JSON object `{"__tag__": <tag_name>, ...payload}`
/// minted by the host `tag` capability. The `__tag__` key is **reserved**:
/// user-constructed object literals cannot produce a `__tag__` key (the eval
/// engines reject it), so the only way a value acquires a `__tag__` key is
/// through the host `tag.tag` host function. This is the forgery-prevention
/// mechanism — tagging is a host capability, not a user-constructible
/// convention (ADR-0055 §3). Use [`tag_value`] to construct one, [`as_tag`] to
/// read its tag name, and [`is_tag_value`] to test for it.
pub const TAG_VALUE_KEY: &str = "__tag__";

/// The sentinel object key marking a [`Value`] as carrying the **host type
/// registry** identity of a type value (ADR-0054 — Generic Typecheck Engine).
///
/// A type value minted by a host type registry is a JSON object
/// `{"__tag__": <tag_name>, "__registry__": <registry_id>, ...payload}`.
/// The `__registry__` key records which registry minted the type value, so
/// equality and matching can be scoped to a single registry (ADR-0054
/// §"construct"). Like `__tag__`, this key is **reserved**: user object
/// literals cannot produce it, so a type value's registry identity is
/// unforgeable.
pub const REGISTRY_VALUE_KEY: &str = "__registry__";

/// Mint a tagged value (ADR-0055).
///
/// Returns `{"__tag__": tag_name, ...payload}`. The `payload` object's fields
/// become the tagged value's payload. If `payload` is not an object (or is
/// `Null`), an empty payload is used. Returns `None` if `payload` already
/// contains a `__tag__` key — a minted value cannot be re-tagged through the
/// payload (the host `tag` op always sets the tag; the payload must not
/// smuggle one in).
///
/// This is the host-side minting primitive; user code reaches it via the
/// `tag.tag` host function exposed by `plugin-lib-tag`.
pub fn tag_value(tag_name: &str, payload: &Value) -> Option<Value> {
    let mut obj = match payload {
        Value::Object(map) => map.clone(),
        Value::Null => serde_json::Map::new(),
        _ => return None,
    };
    if obj.contains_key(TAG_VALUE_KEY) {
        return None;
    }
    obj.insert(TAG_VALUE_KEY.to_string(), Value::from(tag_name));
    Some(Value::Object(obj))
}

/// Read the tag name of a tagged value (ADR-0055).
///
/// Returns `Some(name)` if `value` is a tagged value (an object containing a
/// string `__tag__` key), else `None`. Only values minted by [`tag_value`]
/// (the host `tag` capability) carry a `__tag__` key — user object literals
/// cannot forge one (the engines reserve the key).
pub fn as_tag(value: &Value) -> Option<&str> {
    value.get(TAG_VALUE_KEY).and_then(|v| v.as_str())
}

/// Whether `value` is a tagged value (produced by [`tag_value`]).
pub fn is_tag_value(value: &Value) -> bool {
    value.get(TAG_VALUE_KEY).and_then(|v| v.as_str()).is_some()
}

/// Whether `key` is a reserved value-level key that user-constructed object
/// literals must not produce (ADR-0055 §"Negative — A reserved key").
///
/// The reserved keys are the double-underscore-prefixed host sentinels:
/// `__tag__` (ADR-0055), `__registry__` (ADR-0054 — host type registry
/// identity), `__language__` (ADR-0041), `__ast__` (ADR-0041 §6), and
/// `__arrow__` (ADR-0052 closure values). These are minted by host
/// primitives (`tag_value`, the host type registry `construct` op,
/// `language_value`, `ast_value`, the `closure` op), never by user object
/// literals. The eval engines call this to reject such keys at
/// object-construction time, making the sentinels unforgeable.
pub fn is_reserved_value_key(key: &str) -> bool {
    matches!(
        key,
        TAG_VALUE_KEY | REGISTRY_VALUE_KEY | LANGUAGE_VALUE_KEY | AST_VALUE_KEY | "__arrow__"
    )
}

#[cfg(test)]
mod value_tests {
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
        let v = tag_value("type.collection", &json!({ "name": "number" }))
            .expect("mint succeeds");
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
    fn tag_value_rejects_non_object_payload() {
        assert!(tag_value("unit", &json!(5)).is_none());
        assert!(tag_value("unit", &json!("x")).is_none());
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
}
