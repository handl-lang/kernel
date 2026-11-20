//! Token kind fragment definitions.

use serde::{Deserialize, Serialize};

use crate::fragment::Fragment;

/// How a token's text is interpreted into a payload [`crate::Value`] by the
/// Pratt parser's `atom_payload` (ADR-0053).
///
/// Replaces the former `kind_id.contains("number")` / `contains("bool")` /
/// `contains("null")` / `contains("string")` substring heuristics with typed
/// dispatch. Adding a new literal form is a new variant + a token row, not a
/// parser edit.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum LiteralKind {
    /// Integer (fallback: float). Replaces `contains("number")`.
    Number,
    /// `"true"` → true, anything else → false. Replaces `contains("bool")`.
    Bool,
    /// Always `Value::Null`. Replaces `contains("null")`.
    Null,
    /// Strip `delim_chars` from each end, apply the escape table.
    /// Replaces the hardcoded quote-strip + `\\n`/`\\t`/`\\\"`/`\\\\` table.
    String {
        /// Number of delimiter characters to strip from each end (e.g. 1 for
        /// `"..."`).
        delim_chars: usize,
        /// Escape pairs: each `(from, to)` replacement applied in order.
        escapes: Vec<(String, String)>,
    },
    /// Strip a fixed prefix and suffix, optionally wrap the remainder.
    /// Covers `json{...}`: prefix `"json{"`, suffix `"}"`, wrap `Some(("{", "}"))`.
    StripAffix {
        /// The prefix to strip from the start of the token text.
        prefix: String,
        /// The suffix to strip from the end of the token text.
        suffix: String,
        /// When set, wrap the stripped remainder with `(open, close)`.
        wrap: Option<(String, String)>,
    },
    /// Use the token text verbatim. The default for identifiers and keywords.
    Raw,
}

impl Default for LiteralKind {
    fn default() -> Self {
        Self::Raw
    }
}

/// Serde helper: skip the `trivia` flag when it is `false` (the default).
fn is_false(b: &bool) -> bool {
    !*b
}

/// A definition of one token kind in a language.
///
/// Identity key: `id` (see ADR-0044 §5). Token kind declarations are
/// **structural facts** ("this token exists"), not behavioral definitions:
/// two emitters declaring `token.lparen` are agreeing it exists, not
/// conflicting. Merge therefore uses **union (idempotent)** semantics —
/// merging a token kind that already exists is a no-op (the first declaration
/// is kept), not an error.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct TokenKindDef {
    /// Stable identifier (e.g. `"token.number"`).
    pub id: String,
    /// Optional human-readable label.
    pub label: Option<String>,
    /// How the parser interprets this token's text into a payload value
    /// (ADR-0053). When `None`, the parser uses [`LiteralKind::Raw`]
    /// (verbatim text as a string).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub literal: Option<LiteralKind>,
    /// Whether this token kind is *trivia* — a lexical token that carries no
    /// syntactic meaning and is skipped by the parser (e.g. comments). The
    /// lexer still emits trivia tokens (so tooling such as the LSP can surface
    /// comments / doc-comments), but the Pratt parser filters them out before
    /// driving the grammar. Marking a token as trivia is a data change, not a
    /// parser edit (ADR-0044).
    #[serde(default, skip_serializing_if = "is_false")]
    pub trivia: bool,
    /// Whether this token kind is *layout* — a token the lexer emits but the
    /// Pratt cursor skips transparently everywhere (e.g. a newline token).
    /// Unlike `trivia`, layout tokens stay in the token stream the cursor
    /// sees: a `DelimitedShape` may opt into treating one as an element
    /// separator (`DelimitedShape::newline_separator`), which is how records
    /// get newline-separated entries. Skipping is data-driven (this flag),
    /// never a hardcoded kind check (ADR-0044).
    #[serde(default, skip_serializing_if = "is_false")]
    pub layout: bool,
    /// Free-form classification of this token kind for tooling that must not
    /// hardcode kind strings (ADR-0044 "language as data"). The canonical kit
    /// uses: `keyword`, `identifier`, `number`, `string`, `bool`, `null`,
    /// `template`, `operator`, `punctuation`, `open-bracket`,
    /// `close-bracket`, `comment`, `doc-comment`, `eof`. Optional for
    /// backward compatibility with third-party kits — tooling should fall
    /// back gracefully when `None`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub category: Option<String>,
    /// For bracket token kinds (`open-bracket`/`close-bracket` categories),
    /// the id of the matching counterpart kind (e.g. `token.lparen` pairs
    /// with `token.rparen`). Lets bracket-matching tooling pair delimiters
    /// without hardcoding kind strings.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub pair: Option<String>,
    /// Optional hover/documentation markdown for this token kind, surfaced by
    /// tooling (e.g. the LSP's keyword hover). Free-form markdown; tooling
    /// falls back to a generic description when absent.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub doc: Option<String>,
    /// ids this fragment declares it replaces.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub replaces: Vec<String>,
    /// ids this fragment hard-requires.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub requires: Vec<String>,
}

impl TokenKindDef {
    /// Create a new token kind definition with the given id.
    pub fn new(id: impl Into<String>) -> Self {
        Self {
            id: id.into(),
            label: None,
            literal: None,
            trivia: false,
            layout: false,
            category: None,
            pair: None,
            doc: None,
            replaces: Vec::new(),
            requires: Vec::new(),
        }
    }

    /// Attach a label.
    pub fn with_label(mut self, label: impl Into<String>) -> Self {
        self.label = Some(label.into());
        self
    }

    /// Attach a literal kind for typed atom dispatch (ADR-0053).
    pub fn with_literal(mut self, literal: LiteralKind) -> Self {
        self.literal = Some(literal);
        self
    }

    /// Mark this token kind as trivia (skipped by the parser).
    pub fn with_trivia(mut self) -> Self {
        self.trivia = true;
        self
    }

    /// Attach a classification category (e.g. `"keyword"`, `"open-bracket"`).
    pub fn with_category(mut self, category: impl Into<String>) -> Self {
        self.category = Some(category.into());
        self
    }

    /// Attach the id of the matching bracket counterpart.
    pub fn with_pair(mut self, pair: impl Into<String>) -> Self {
        self.pair = Some(pair.into());
        self
    }

    /// Attach hover/documentation markdown for this token kind.
    pub fn with_doc(mut self, doc: impl Into<String>) -> Self {
        self.doc = Some(doc.into());
        self
    }

    /// Attach a `replaces` list.
    pub fn with_replaces(mut self, replaces: Vec<String>) -> Self {
        self.replaces = replaces;
        self
    }

    /// Attach a `requires` list.
    pub fn with_requires(mut self, requires: Vec<String>) -> Self {
        self.requires = requires;
        self
    }
}

impl Fragment for TokenKindDef {
    fn id(&self) -> &str {
        &self.id
    }
    fn replaces(&self) -> &[String] {
        &self.replaces
    }
    fn requires(&self) -> &[String] {
        &self.requires
    }
    fn identity_key(&self) -> String {
        self.id.clone()
    }
    /// Token kind declarations merge idempotently (union semantics): two
    /// emitters declaring the same token kind are agreeing it exists, not
    /// conflicting, so the duplicate is silently dropped (first wins).
    const UNION: bool = true;
}

#[cfg(test)]
#[path = "token_kind_test.rs"]
mod token_kind_test;
