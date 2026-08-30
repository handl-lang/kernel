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
/// Staged `lex`/`parse`/`eval` dispatch entry points.
pub mod staged;
/// Scheme combinator versioning.
pub mod version;

pub use ast::{Ast, AstNode, AstRef, Span};
pub use capabilities::{capabilities, foreign_names, subset_of};
pub use desugar::{desugar, DesugarRule};
pub use error::LangError;
pub use fragment::Fragment;
pub use fragment_set::FragmentSet;
pub use fragments::{
    AstShapeDef, AstShapeRef, CapabilityDecl, EvalSchemeDef, GrammarPosition, GrammarRow,
    LexerPattern, LexerRuleDef, OptionSchema, TokenKindDef,
};
pub use language::Language;
pub use scheme::Scheme;
pub use staged::{eval, lex, parse, run, Source, Token, Tokens, ValueOut};
pub use version::SchemeVersion;

/// The value type used throughout the crate: a re-export of `serde_json::Value`.
pub type Value = serde_json::Value;
