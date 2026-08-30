//! Error types for the `handl-language` data crate.
//!
//! [`LangError`] is the single error enum used by fragment merge, the `Ast`
//! arena, scheme (de)serialization, and the staged `lex`/`parse`/`eval`
//! dispatch entry points. It deliberately does not depend on
//! `handl_platform::PlatformError` so that `handl-language` remains a
//! low-level, dependency-light data crate.

use thiserror::Error;

/// Errors raised by `handl-language` operations.
#[derive(Error, Debug, Clone, PartialEq)]
pub enum LangError {
    /// No engine is bound for the requested stage (Phase 1 has no engines).
    #[error("not implemented: no engine bound for this stage")]
    NotImplemented,
    /// Two fragments target the same identity key and neither declares
    /// `replaces`.
    #[error("collision: existing {existing} conflicts with incoming {incoming}")]
    Collision {
        /// The id of the fragment already present in the set.
        existing: String,
        /// The id of the fragment being merged.
        incoming: String,
    },
    /// A fragment declared `replaces: [id]` but the named id is not present.
    #[error("unknown replace target: {missing}")]
    UnknownReplace {
        /// The id that was declared in `replaces` but is absent from the set.
        missing: String,
    },
    /// A fragment declared `requires: [id, ...]` but one or more required ids
    /// are absent after the merge.
    #[error("missing required fragments: {missing:?}")]
    MissingRequires {
        /// The ids that were declared in `requires` but are absent.
        missing: Vec<String>,
    },
    /// A `replaces` chain forms a cycle (A replaces B replaces A).
    #[error("cyclic replace chain: {chain:?}")]
    CyclicReplace {
        /// The ids forming the cycle, in order.
        chain: Vec<String>,
    },
    /// An `AstRef` indexed past the end of the `Ast` arena.
    #[error("ast index out of bounds: {index}")]
    AstIndexOutOfBounds {
        /// The offending index.
        index: usize,
    },
    /// A serde (de)serialization failure.
    #[error("serde error: {0}")]
    Serde(String),
    /// An engine-reported error (used by later phases; included for API
    /// completeness).
    #[error("engine error: {0}")]
    Engine(String),
    /// A variable was referenced but is not bound in the current scope.
    ///
    /// Added in Phase 2 for the tree-walk eval engine, which resolves `Var`
    /// schemes against a scope stack and reports this error when a name is
    /// unbound.
    #[error("unknown variable: {name}")]
    UnknownVariable {
        /// The unbound variable name.
        name: String,
    },
    /// A lexing failure: the source text could not be tokenized (e.g. an
    /// unrecognized character, or an unterminated delimited block).
    ///
    /// Added for the data-driven lexer engine (`plugin-engine-lex-pattern`),
    /// which reports the byte offset where lexing stalled.
    #[error("lex error at position {position}: {message}")]
    LexError {
        /// The byte offset in the source where lexing failed.
        position: usize,
        /// A human-readable description of the failure.
        message: String,
    },
}

impl From<serde_json::Error> for LangError {
    fn from(err: serde_json::Error) -> Self {
        LangError::Serde(err.to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn from_serde_json_error() {
        let err = serde_json::from_str::<serde_json::Value>("{bad}").unwrap_err();
        let lang_err = LangError::from(err);
        assert!(matches!(lang_err, LangError::Serde(_)));
    }

    #[test]
    fn display_messages() {
        assert_eq!(
            format!("{}", LangError::NotImplemented),
            "not implemented: no engine bound for this stage"
        );
        assert_eq!(
            format!(
                "{}",
                LangError::Collision {
                    existing: "a".into(),
                    incoming: "b".into()
                }
            ),
            "collision: existing a conflicts with incoming b"
        );
        assert_eq!(
            format!(
                "{}",
                LangError::UnknownReplace { missing: "x".into() }
            ),
            "unknown replace target: x"
        );
        assert_eq!(
            format!(
                "{}",
                LangError::MissingRequires {
                    missing: vec!["y".into()]
                }
            ),
            "missing required fragments: [\"y\"]"
        );
        assert_eq!(
            format!(
                "{}",
                LangError::CyclicReplace {
                    chain: vec!["a".into(), "b".into(), "a".into()]
                }
            ),
            "cyclic replace chain: [\"a\", \"b\", \"a\"]"
        );
        assert_eq!(
            format!(
                "{}",
                LangError::AstIndexOutOfBounds { index: 5 }
            ),
            "ast index out of bounds: 5"
        );
        assert_eq!(
            format!("{}", LangError::Serde("boom".into())),
            "serde error: boom"
        );
        assert_eq!(
            format!("{}", LangError::Engine("nope".into())),
            "engine error: nope"
        );
        assert_eq!(
            format!(
                "{}",
                LangError::UnknownVariable { name: "x".into() }
            ),
            "unknown variable: x"
        );
        assert_eq!(
            format!(
                "{}",
                LangError::LexError {
                    position: 7,
                    message: "unrecognized character".into()
                }
            ),
            "lex error at position 7: unrecognized character"
        );
    }
}
