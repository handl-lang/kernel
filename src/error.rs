//! Error types for the `handl-language` data crate.
//!
//! [`LangError`] is the single error enum used by fragment merge, the `Ast`
//! arena, scheme (de)serialization, and the staged `lex`/`parse`/`eval`
//! dispatch entry points. It deliberately does not depend on
//! `handl_platform::PlatformError` so that `handl-language` remains a
//! low-level, dependency-light data crate.

use thiserror::Error;

use crate::ast::{AstNode, Span};

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
    ///
    /// Carries a human-readable `message`, an optional source `span`, an
    /// optional `node_kind` for the AST node where the error originated, and a
    /// pre-formatted `context` suffix appended in `Display`. The `message`
    /// field is kept pure (no position info) so callers can match on it with
    /// `.contains(...)`. The structured `span` / `node_kind` fields are
    /// available for programmatic consumers (LSP, diagnostics).
    #[error("engine error: {message}{context}")]
    Engine {
        /// The core error message (no source position info).
        message: String,
        /// Pre-formatted context suffix, e.g. `" at 12..15 in binary.add"`.
        /// Empty when no source context is available.
        context: String,
        /// The byte span in the source where the error originated, if known.
        span: Option<Span>,
        /// The kind of the AST node where the error originated, if known.
        node_kind: Option<String>,
    },
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

impl LangError {
    /// Build an engine error with no source context.
    ///
    /// Use this when no `AstNode` or `Span` is available (e.g. dispatch
    /// machinery, kit assembly, standalone binary loading).
    pub fn engine(msg: impl Into<String>) -> Self {
        LangError::Engine {
            message: msg.into(),
            context: String::new(),
            span: None,
            node_kind: None,
        }
    }

    /// Return the source `Span` carried by this error, if any.
    ///
    /// Only the `Engine` variant carries structured span info today; all other
    /// variants return `None`.
    pub fn span(&self) -> Option<Span> {
        match self {
            LangError::Engine { span, .. } => *span,
            _ => None,
        }
    }

    /// Attach a node's span (and kind) to this error, if not already set.
    ///
    /// This is a builder-style helper for the common pattern of creating an
    /// error with [`LangError::engine`] and then attaching source context once
    /// the responsible `AstNode` is known. If the error already carries a span
    /// (e.g. it was built with [`LangError::engine_node`] or
    /// [`LangError::engine_at`]), it is returned unchanged. Non-`Engine`
    /// variants are also returned unchanged.
    pub fn with_node(mut self, node: &AstNode) -> Self {
        if self.span().is_none() {
            self = match self {
                LangError::Engine {
                    message,
                    span: None,
                    node_kind: _,
                    context,
                } => {
                    let mut new_context = String::new();
                    if let Some(s) = node.span {
                        new_context.push_str(&format!(" at {}..{}", s.start, s.end));
                    }
                    if !node.kind.is_empty() {
                        new_context.push_str(&format!(" in {}", node.kind));
                    }
                    // Preserve any pre-existing context that preceded the
                    // source-location suffix (rare, but keep behaviour stable).
                    if !context.is_empty() {
                        new_context.push_str(&context);
                    }
                    LangError::Engine {
                        message,
                        context: new_context,
                        span: node.span,
                        node_kind: Some(node.kind.clone()),
                    }
                }
                // Engine variant already had a span (matched above is None,
                // so this arm is unreachable for the inner match), or other
                // variants — return as-is.
                other => other,
            };
        }
        self
    }

    /// Attach an explicit span (and optional node kind) to this error, if not
    /// already set.
    ///
    /// See [`LangError::with_node`] for the rationale. Use this when you have a
    /// `Span` (e.g. from a token) but not an `AstNode` directly.
    pub fn with_span(mut self, span: Span) -> Self {
        if self.span().is_none() {
            self = match self {
                LangError::Engine {
                    message,
                    span: None,
                    node_kind,
                    context,
                } => {
                    let mut new_context = format!(" at {}..{}", span.start, span.end);
                    if !context.is_empty() {
                        new_context.push_str(&context);
                    }
                    LangError::Engine {
                        message,
                        context: new_context,
                        span: Some(span),
                        node_kind,
                    }
                }
                other => other,
            };
        }
        self
    }

    /// Build an engine error with source context from an `AstNode`.
    ///
    /// Attaches `node.span` and `node.kind` as structured fields and appends
    /// a `" at {start}..{end} in {kind}"` suffix to the `Display` output.
    /// The `message` field itself stays pure for `.contains()` matching.
    pub fn engine_node(msg: impl Into<String>, node: &AstNode) -> Self {
        let mut context = String::new();
        if let Some(span) = node.span {
            context.push_str(&format!(" at {}..{}", span.start, span.end));
        }
        if !node.kind.is_empty() {
            context.push_str(&format!(" in {}", node.kind));
        }
        LangError::Engine {
            message: msg.into(),
            context,
            span: node.span,
            node_kind: Some(node.kind.clone()),
        }
    }

    /// Build an engine error with explicit source context.
    ///
    /// Use this when you have a `Span` and/or node kind but not an `AstNode`
    /// directly (e.g. you have an `AstRef` and an `Ast` arena).
    pub fn engine_at(
        msg: impl Into<String>,
        span: Option<Span>,
        node_kind: Option<impl Into<String>>,
    ) -> Self {
        let node_kind = node_kind.map(|k| k.into());
        let mut context = String::new();
        if let Some(s) = span {
            context.push_str(&format!(" at {}..{}", s.start, s.end));
        }
        if let Some(k) = &node_kind {
            if !k.is_empty() {
                context.push_str(&format!(" in {}", k));
            }
        }
        LangError::Engine {
            message: msg.into(),
            context,
            span,
            node_kind,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{AstNode, Span};

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
                LangError::UnknownReplace {
                    missing: "x".into()
                }
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
            format!("{}", LangError::AstIndexOutOfBounds { index: 5 }),
            "ast index out of bounds: 5"
        );
        assert_eq!(
            format!("{}", LangError::Serde("boom".into())),
            "serde error: boom"
        );
        assert_eq!(
            format!("{}", LangError::engine("nope")),
            "engine error: nope"
        );
        assert_eq!(
            format!(
                "{}",
                LangError::engine_node(
                    "boom",
                    &AstNode::new("binary.add").with_span(Span { start: 12, end: 15 })
                )
            ),
            "engine error: boom at 12..15 in binary.add"
        );
        assert_eq!(
            format!("{}", LangError::engine_node("boom", &AstNode::new("lit"))),
            "engine error: boom in lit"
        );
        assert_eq!(
            format!(
                "{}",
                LangError::engine_at("boom", Some(Span { start: 0, end: 3 }), Some("var"))
            ),
            "engine error: boom at 0..3 in var"
        );
        assert_eq!(
            format!("{}", LangError::UnknownVariable { name: "x".into() }),
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

    #[test]
    fn span_accessor_returns_engine_span() {
        let with_span = LangError::engine_at("boom", Some(Span { start: 1, end: 4 }), Some("x"));
        assert_eq!(with_span.span(), Some(Span { start: 1, end: 4 }));
        let without_span = LangError::engine("boom");
        assert_eq!(without_span.span(), None);
        // Non-Engine variants never carry a span.
        assert_eq!(LangError::NotImplemented.span(), None);
    }

    #[test]
    fn with_node_attaches_span_and_kind() {
        let err = LangError::engine("nope");
        assert!(err.span().is_none());
        let node = AstNode::new("binary.add").with_span(Span { start: 12, end: 15 });
        let err = err.with_node(&node);
        assert_eq!(err.span(), Some(Span { start: 12, end: 15 }));
        // Display now includes the source-location suffix.
        assert_eq!(
            format!("{}", err),
            "engine error: nope at 12..15 in binary.add"
        );
        match err {
            LangError::Engine {
                node_kind: Some(ref k),
                ..
            } => assert_eq!(k, "binary.add"),
            other => panic!("expected Engine variant, got {:?}", other),
        }
    }

    #[test]
    fn with_node_is_idempotent_when_span_already_set() {
        let err = LangError::engine_node(
            "boom",
            &AstNode::new("lit").with_span(Span { start: 0, end: 1 }),
        );
        let original_span = err.span();
        let other = AstNode::new("binary.add").with_span(Span {
            start: 99,
            end: 100,
        });
        let err = err.with_node(&other);
        // Span already set → with_node must not overwrite it.
        assert_eq!(err.span(), original_span);
    }

    #[test]
    fn with_span_attaches_explicit_span() {
        let err = LangError::engine("nope");
        let err = err.with_span(Span { start: 5, end: 8 });
        assert_eq!(err.span(), Some(Span { start: 5, end: 8 }));
        assert_eq!(format!("{}", err), "engine error: nope at 5..8");
    }

    #[test]
    fn with_node_leaves_non_engine_variants_untouched() {
        let err = LangError::UnknownVariable { name: "x".into() };
        let node = AstNode::new("var").with_span(Span { start: 0, end: 1 });
        let err = err.with_node(&node);
        assert!(matches!(err, LangError::UnknownVariable { .. }));
        assert_eq!(err.span(), None);
    }
}
