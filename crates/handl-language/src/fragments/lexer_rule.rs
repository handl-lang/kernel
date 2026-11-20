//! Lexer rule fragment definitions.
//!
//! A [`LexerRuleDef`] carries the *pattern* data a data-driven lexer engine
//! uses to recognize one token kind in source text (ADR-0044 §1). Like token
//! kinds and AST shapes, lexer rules are **structural facts** ("this is how you
//! recognize a `token.number`"), so they merge with **union (idempotent)**
//! semantics — re-declaring the same rule id is a no-op (first wins).
//!
//! The identity key is the rule `id` (not `token_kind`), so multiple rules can
//! produce the same token kind (e.g. `lex.bool.true` and `lex.bool.false` both
//! produce `token.bool`).

use serde::{Deserialize, Serialize};

use crate::fragment::Fragment;

/// The pattern a lexer rule matches.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum LexerPattern {
    /// Match an exact literal string (e.g. `"let"`, `"("`, `"=="`).
    ///
    /// When multiple literals match at the same position, the longest match
    /// wins.
    Literal {
        /// The exact text to match.
        text: String,
    },
    /// Match a run of characters from a character class.
    ///
    /// The first character must be in `start_chars`; subsequent characters
    /// must be in `continue_chars`.
    CharClass {
        /// Characters that can start the run (e.g. `"a-zA-Z_"` for
        /// identifiers). Supports ranges like `a-z`, `A-Z`, `0-9`, and single
        /// chars.
        start_chars: String,
        /// Characters that can continue the run (e.g. `"a-zA-Z0-9_"`).
        /// Supports the same range syntax.
        continue_chars: String,
    },
    /// Match a number literal: optional leading `-`, digits, optional `.` +
    /// digits.
    Number,
    /// Match a delimited block (string, comment, template).
    Delimited {
        /// The opening delimiter (e.g. `"\"`, `"--"`, `"/*"`).
        open: String,
        /// The closing delimiter (e.g. `"\"`, `"\n"`, `"*/"`).
        close: String,
        /// Whether to process `\` escape sequences inside.
        escape: bool,
        /// Whether to process `${expr}` interpolation inside.
        interpolation: bool,
        /// Whether the close delimiter is "end of input" (for EOF-terminated
        /// blocks). Used for line comments where close is `\n` but EOF also
        /// terminates.
        close_at_eof: bool,
        /// When set, the scanner tracks nesting depth: each occurrence of
        /// this string increments the depth, and the `close` delimiter only
        /// terminates the block when depth returns to zero. Used for
        /// brace-balanced blocks like `json{...}` where inner `{` / `}`
        /// pairs must not prematurely close the token.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        nesting_open: Option<String>,
    },
}

/// A lexer rule definition — one pattern for recognizing a token kind.
///
/// Identity key: `id`. This allows multiple rules to produce the same token
/// kind (e.g. `lex.bool.true` and `lex.bool.false` both produce `token.bool`).
/// `LexerRuleDef` is a **union** type (like `TokenKindDef`) — duplicate rules
/// for the same id are idempotent (the first declaration is kept).
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct LexerRuleDef {
    /// Stable identifier (e.g. `"lex.number"`).
    pub id: String,
    /// The token kind id this rule produces (e.g. `"token.number"`).
    pub token_kind: String,
    /// The pattern to match.
    pub pattern: LexerPattern,
    /// Priority — lower = tried first by the lexer engine.
    pub priority: i32,
    /// ids this fragment declares it replaces.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub replaces: Vec<String>,
    /// ids this fragment hard-requires.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub requires: Vec<String>,
}

impl LexerRuleDef {
    /// Create a new lexer rule definition.
    pub fn new(
        id: impl Into<String>,
        token_kind: impl Into<String>,
        pattern: LexerPattern,
        priority: i32,
    ) -> Self {
        Self {
            id: id.into(),
            token_kind: token_kind.into(),
            pattern,
            priority,
            replaces: Vec::new(),
            requires: Vec::new(),
        }
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

impl Fragment for LexerRuleDef {
    fn id(&self) -> &str {
        &self.id
    }
    fn replaces(&self) -> &[String] {
        &self.replaces
    }
    fn requires(&self) -> &[String] {
        &self.requires
    }
    /// The identity key is the rule `id` (not `token_kind`), so multiple rules
    /// can produce the same token kind (e.g. `true`/`false` → `token.bool`).
    fn identity_key(&self) -> String {
        self.id.clone()
    }
    /// Lexer rule declarations are structural facts, so they merge
    /// idempotently (union semantics): two emitters declaring the same rule
    /// id are agreeing on the pattern, not conflicting, so the duplicate is
    /// silently dropped (first wins).
    const UNION: bool = true;
}

#[cfg(test)]
#[path = "lexer_rule_test.rs"]
mod lexer_rule_test;
