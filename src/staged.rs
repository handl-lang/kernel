//! Staged entry points — `lex`, `parse`, `eval`, and the `run` convenience
//! (ADR-0044 §2).
//!
//! Each stage consumes only the previous stage's output plus the `Language`
//! spec. Phase 1 has **no engines bound**, so `lex`/`parse`/`eval` return
//! [`LangError::NotImplemented`]. The dispatch signatures are in place so
//! later phases can wire engines without changing the `Language` data contract.
//!
//! `Value` is [`serde_json::Value`] — no new value type is invented. `Token`
//! is a minimal local stub to avoid coupling to `handl_plugin_lexer::Token`.

use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::ast::Ast;
use crate::error::LangError;
use crate::language::Language;

/// A unit of source text produced by the lexer. A minimal stub; later phases
/// may widen this or reuse `handl_plugin_lexer::Token`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Token {
    /// The token kind id (keyed to `TokenKindDef::id`).
    pub kind: String,
    /// The matched source text.
    pub text: String,
}

/// Source text to be lexed. A newtype around `String`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
pub struct Source(pub String);

impl Source {
    /// Create a new source from a string.
    pub fn new(src: impl Into<String>) -> Self {
        Self(src.into())
    }

    /// The source text.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl From<String> for Source {
    fn from(s: String) -> Self {
        Self(s)
    }
}

impl From<&str> for Source {
    fn from(s: &str) -> Self {
        Self(s.to_string())
    }
}

/// A token stream produced by `lex`. A newtype around `Vec<Token>`.
#[derive(Debug, Clone, PartialEq, Default, Serialize, Deserialize)]
pub struct Tokens(pub Vec<Token>);

impl Tokens {
    /// Create an empty token stream.
    pub fn new() -> Self {
        Self::default()
    }

    /// The backing token slice.
    pub fn as_slice(&self) -> &[Token] {
        &self.0
    }
}

/// The value type produced by `eval`: a re-export of `serde_json::Value`.
pub type ValueOut = Value;

/// Lex source text into a token stream using the given language.
///
/// Phase 1: no lexer engine is bound, so this returns
/// [`LangError::NotImplemented`].
///
/// # Errors
///
/// Always returns [`LangError::NotImplemented`] in Phase 1.
pub fn lex(_lang: &Language, _src: &Source) -> Result<Tokens, LangError> {
    Err(LangError::NotImplemented)
}

/// Parse a token stream into an `Ast` using the given language.
///
/// Phase 1: no parser engine is bound, so this returns
/// [`LangError::NotImplemented`].
///
/// # Errors
///
/// Always returns [`LangError::NotImplemented`] in Phase 1.
pub fn parse(_lang: &Language, _toks: &Tokens) -> Result<Ast, LangError> {
    Err(LangError::NotImplemented)
}

/// Evaluate an `Ast` into a [`Value`] using the given language.
///
/// Phase 1: no eval engine is bound, so this returns
/// [`LangError::NotImplemented`].
///
/// # Errors
///
/// Always returns [`LangError::NotImplemented`] in Phase 1.
pub fn eval(_lang: &Language, _ast: &Ast) -> Result<ValueOut, LangError> {
    Err(LangError::NotImplemented)
}

/// Convenience: `run(lang, src) = eval(lang, &parse(lang, &lex(lang, src)?)?)`.
///
/// # Errors
///
/// Propagates the first stage error. In Phase 1 this is always
/// [`LangError::NotImplemented`] from `lex`.
pub fn run(lang: &Language, src: &Source) -> Result<ValueOut, LangError> {
    eval(lang, &parse(lang, &lex(lang, src)?)?)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lex_returns_not_implemented() {
        let lang = Language::new();
        let src = Source::new("1 + 2");
        let err = lex(&lang, &src).unwrap_err();
        assert_eq!(err, LangError::NotImplemented);
    }

    #[test]
    fn parse_returns_not_implemented() {
        let lang = Language::new();
        let toks = Tokens::new();
        let err = parse(&lang, &toks).unwrap_err();
        assert_eq!(err, LangError::NotImplemented);
    }

    #[test]
    fn eval_returns_not_implemented() {
        let lang = Language::new();
        let ast = Ast::new();
        let err = eval(&lang, &ast).unwrap_err();
        assert_eq!(err, LangError::NotImplemented);
    }

    #[test]
    fn run_returns_not_implemented() {
        let lang = Language::new();
        let src = Source::new("1 + 2");
        let err = run(&lang, &src).unwrap_err();
        assert_eq!(err, LangError::NotImplemented);
    }

    #[test]
    fn source_constructors() {
        let s = Source::new("hi");
        assert_eq!(s.as_str(), "hi");
        let s2: Source = "ho".into();
        assert_eq!(s2.as_str(), "ho");
        let s3: Source = String::from("hey").into();
        assert_eq!(s3.as_str(), "hey");
    }

    #[test]
    fn tokens_default_and_slice() {
        let t = Tokens::new();
        assert!(t.as_slice().is_empty());
    }

    #[test]
    fn token_serde_roundtrip() {
        let t = Token {
            kind: "token.number".into(),
            text: "42".into(),
        };
        let j = serde_json::to_string(&t).unwrap();
        let back: Token = serde_json::from_str(&j).unwrap();
        assert_eq!(t, back);
    }
}
