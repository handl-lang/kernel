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
/// The `Scheme` combinator set.
pub mod scheme;
/// The v2 arrow-calculus `SchemeV2` kernel (ADR-0052).
pub mod scheme_v2;
/// Staged `lex`/`parse`/`eval` dispatch entry points.
pub mod staged;
/// Scheme combinator versioning.
pub mod version;

pub use ast::{Ast, AstNode, AstRef, Span};
pub use capabilities::{capabilities, foreign_names, foreign_names_v2, subset_of};
pub use desugar::{DesugarRule, desugar};
pub use error::LangError;
pub use fragment::Fragment;
pub use fragment_set::FragmentSet;
pub use fragments::{
    AstShapeDef, AstShapeRef, CapabilityDecl, DelimitedShape, EvalSchemeDef, EvalSchemeDefV2,
    GrammarPosition, GrammarRow, LexerPattern, LexerRuleDef, OptionSchema, PairShape,
    TokenKindDef,
};
pub use language::Language;
pub use scheme::Scheme;
pub use scheme_v2::{ArrSource, SchemeV2, lower_v1_to_v2};
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

#[cfg(test)]
mod value_tests {
    use super::*;
    use crate::fragments::token_kind::TokenKindDef;

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
}
