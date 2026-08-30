//! Fragment type definitions for each `Language` fragment set.
//!
//! Each type implements [`Fragment`](crate::Fragment) and is
//! `serde`-serializable, carrying only data — no Rust trait objects, closures,
//! or behavior.

/// Token kind fragment definitions.
pub mod token_kind;
/// Grammar row fragment definitions.
pub mod grammar;
/// Eval scheme fragment definitions.
pub mod eval_scheme;
/// AST shape fragment definitions.
pub mod ast_shape;
/// Capability declaration fragment definitions.
pub mod capability;
/// Option schema fragment definitions.
pub mod option;
/// Lexer rule fragment definitions.
pub mod lexer_rule;

pub use ast_shape::AstShapeDef;
pub use capability::CapabilityDecl;
pub use eval_scheme::EvalSchemeDef;
pub use grammar::{AstShapeRef, GrammarPosition, GrammarRow};
pub use lexer_rule::{LexerPattern, LexerRuleDef};
pub use option::OptionSchema;
pub use token_kind::TokenKindDef;
