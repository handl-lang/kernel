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
    /// Added for the data-driven lexer engine (`hnl-engine-lex-pattern`),
    /// which reports the byte offset where lexing stalled.
    #[error("lex error at position {position}: {message}")]
    LexError {
        /// The byte offset in the source where lexing failed.
        position: usize,
        /// A human-readable description of the failure.
        message: String,
    },
    /// Evaluation suspended at a `perform`ed effect, waiting on `resume`
    /// (multi-shot effect resumption — `host/project/design/
    /// multishot-resume.md`).
    ///
    /// This is an **engine-internal control-flow signal**, not a user
    /// error: a `perform` under a `handle` whose clause takes the
    /// resumption unwinds evaluation to the innermost `handle` driver,
    /// which invokes the clause with the `resume` value. The `id`
    /// indexes the suspending engine's thread-local suspension table —
    /// the payload lives there, not in this variant, so the kernel stays
    /// free of `TaggedValue`/`TermData` dependencies. An engine that
    /// never mints suspension records must never see this variant; one
    /// escaping to the user reports as an ordinary error message.
    #[error("eval suspended awaiting resumption {id}")]
    Suspended {
        /// The engine-side suspension-table index.
        id: u64,
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

    /// Build a [`LangError::Suspended`] control-flow signal for the
    /// engine-side suspension record `id` (multi-shot `resume`).
    pub fn suspended(id: u64) -> Self {
        LangError::Suspended { id }
    }

    /// The suspension-table index when this error is a
    /// [`LangError::Suspended`] control-flow signal, else `None`.
    ///
    /// `handle` drivers match on this to catch only suspensions — any
    /// code that *catches* engine errors (impl-value fallbacks,
    /// language-level `try`) must re-propagate `Suspended` unchanged or
    /// a `resume` continuation dies silently.
    pub fn suspension_id(&self) -> Option<u64> {
        match self {
            LangError::Suspended { id } => Some(*id),
            _ => None,
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
#[path = "error_test.rs"]
mod error_test;
