//! Fragment type definitions for each `Language` fragment set.
//!
//! Each type implements [`Fragment`](crate::Fragment) and is
//! `serde`-serializable, carrying only data — no Rust trait objects, closures,
//! or behavior.

/// AST shape fragment definitions.
pub mod ast_shape;
/// Capability declaration fragment definitions.
pub mod capability;
/// Eval scheme fragment definitions (arrow-calculus kernel, ADR-0052).
pub mod eval_scheme;
/// Grammar row fragment definitions.
pub mod grammar;
/// Lexer rule fragment definitions.
pub mod lexer_rule;
/// Option schema fragment definitions.
pub mod option;
/// Token kind fragment definitions.
pub mod token_kind;

pub use ast_shape::AstShapeDef;
pub use capability::CapabilityDecl;
pub use eval_scheme::EvalSchemeDef;
pub use grammar::{AstShapeRef, DelimitedShape, GrammarPosition, GrammarRow, PairShape};
pub use lexer_rule::{LexerPattern, LexerRuleDef};
pub use option::OptionSchema;
pub use token_kind::TokenKindDef;
