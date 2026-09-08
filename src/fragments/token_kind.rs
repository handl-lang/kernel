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

/// Host-facing classification of a token kind (ADR-0081).
///
/// Replaces the former `kind.starts_with("token.keyword.")` /
/// `kind == "token.lparen"` string heuristics in hosts (LSP, tooling) with
/// declared data: each [`TokenKindDef`] optionally declares the category a
/// host should treat it as. The taxonomy is host vocabulary — it is fixed in
/// Rust because it is the contract between `Language` data and host
/// classification, while the *mapping* from token kind to category is data
/// (a new language declares its own kinds mapped onto these categories).
///
/// `None` on a [`TokenKindDef`] means *unclassified*: hosts must not guess.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq, Hash)]
#[serde(rename_all = "kebab-case")]
pub enum TokenCategory {
    /// Reserved-word keyword (`token.keyword.*`).
    Keyword,
    /// User-defined identifier.
    Identifier,
    /// Numeric literal.
    Number,
    /// String literal.
    String,
    /// Template/interpolated string.
    Template,
    /// Embedded JSON literal (`json{...}`).
    Json,
    /// Boolean literal.
    Boolean,
    /// Null literal.
    Null,
    /// Line/block comment (trivia).
    Comment,
    /// Documentation comment (trivia).
    DocComment,
    /// Infix/prefix operator or other symbolic token.
    Operator,
    /// Open `(`.
    OpenParen,
    /// Close `)`.
    CloseParen,
    /// Open `[`.
    OpenBracket,
    /// Close `]`.
    CloseBracket,
    /// Open `{`.
    OpenBrace,
    /// Close `}`.
    CloseBrace,
    /// `,` separator.
    Comma,
    /// `;` separator.
    Semicolon,
    /// `:` type-annotation / key-value separator.
    Colon,
    /// `.` member access.
    Dot,
    /// `::` binding separator.
    Bind,
    /// `...` spread/ellipsis.
    Ellipsis,
}

impl TokenCategory {
    /// Whether this category is an opening bracket (`(`/`[`/`{`).
    pub fn is_open_bracket(self) -> bool {
        matches!(
            self,
            Self::OpenParen | Self::OpenBracket | Self::OpenBrace
        )
    }

    /// Whether this category is a closing bracket (`)`/`]`/`}`).
    pub fn is_close_bracket(self) -> bool {
        matches!(
            self,
            Self::CloseParen | Self::CloseBracket | Self::CloseBrace
        )
    }

    /// Whether this category is any bracket (open or close).
    pub fn is_bracket(self) -> bool {
        self.is_open_bracket() || self.is_close_bracket()
    }

    /// The matching close category for an open bracket (`OpenParen` →
    /// `CloseParen`), or `None` for non-open categories.
    pub fn matching_close(self) -> Option<Self> {
        match self {
            Self::OpenParen => Some(Self::CloseParen),
            Self::OpenBracket => Some(Self::CloseBracket),
            Self::OpenBrace => Some(Self::CloseBrace),
            _ => None,
        }
    }

    /// The matching open category for a close bracket (`CloseParen` →
    /// `OpenParen`), or `None` for non-close categories.
    pub fn matching_open(self) -> Option<Self> {
        match self {
            Self::CloseParen => Some(Self::OpenParen),
            Self::CloseBracket => Some(Self::OpenBracket),
            Self::CloseBrace => Some(Self::OpenBrace),
            _ => None,
        }
    }

    /// Whether this category counts as an *operator* for highlighting and
    /// hover purposes. Covers [`Self::Operator`] plus the symbolic
    /// separators that historically lived in the operator set (`::`,
    /// `...`). Mirrors the former `is_operator_kind` kind list.
    pub fn is_operator_like(self) -> bool {
        matches!(self, Self::Operator | Self::Bind | Self::Ellipsis)
    }

    /// Whether this category counts as a *delimiter/punctuation* for
    /// highlighting purposes: brackets plus `,` `;` `:` `.`. Mirrors the
    /// former `is_delimiter_kind` kind list (minus `token.arrow`, which was
    /// unreachable — every caller checked operator first).
    pub fn is_delimiter_like(self) -> bool {
        self.is_bracket()
            || matches!(self, Self::Comma | Self::Semicolon | Self::Colon | Self::Dot)
    }

    /// Whether this category is comment trivia ([`Self::Comment`] or
    /// [`Self::DocComment`]).
    pub fn is_comment_like(self) -> bool {
        matches!(self, Self::Comment | Self::DocComment)
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
    /// Host-facing classification (ADR-0081): how hosts such as the LSP
    /// should treat this token kind (keyword, bracket, operator, ...).
    /// `None` means unclassified — hosts must not fall back to `kind`
    /// string heuristics.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub category: Option<TokenCategory>,
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
            category: None,
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

    /// Attach a host-facing category (ADR-0081).
    pub fn with_category(mut self, category: TokenCategory) -> Self {
        self.category = Some(category);
        self
    }

    /// Mark this token kind as trivia (skipped by the parser).
    pub fn with_trivia(mut self) -> Self {
        self.trivia = true;
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
mod tests {
    use super::*;

    #[test]
    fn construct_and_accessors() {
        let t = TokenKindDef::new("token.number")
            .with_label("number")
            .with_replaces(vec!["token.int".into()])
            .with_requires(vec!["token.dot".into()]);
        assert_eq!(t.id(), "token.number");
        assert_eq!(t.label.as_deref(), Some("number"));
        assert_eq!(t.replaces(), &["token.int".to_string()]);
        assert_eq!(t.requires(), &["token.dot".to_string()]);
        assert_eq!(t.identity_key(), "token.number");
    }

    #[test]
    fn serde_roundtrip() {
        let t = TokenKindDef::new("token.string").with_replaces(vec!["token.text".into()]);
        let j = serde_json::to_string(&t).unwrap();
        let back: TokenKindDef = serde_json::from_str(&j).unwrap();
        assert_eq!(t, back);
    }

    #[test]
    fn equality() {
        assert_eq!(TokenKindDef::new("a"), TokenKindDef::new("a"));
        assert_ne!(TokenKindDef::new("a"), TokenKindDef::new("b"));
    }

    #[test]
    fn skip_empty_fields_in_serde() {
        let t = TokenKindDef::new("token.x");
        let j = serde_json::to_string(&t).unwrap();
        assert!(!j.contains("replaces"));
        assert!(!j.contains("requires"));
        assert!(!j.contains("literal"));
        assert!(!j.contains("trivia"));
    }

    #[test]
    fn literal_kind_serde_roundtrip() {
        let t = TokenKindDef::new("token.number").with_literal(LiteralKind::Number);
        let j = serde_json::to_string(&t).unwrap();
        let back: TokenKindDef = serde_json::from_str(&j).unwrap();
        assert_eq!(t, back);
        assert!(j.contains("literal"));
    }

    #[test]
    fn literal_kind_string_roundtrip() {
        let t = TokenKindDef::new("token.string").with_literal(LiteralKind::String {
            delim_chars: 1,
            escapes: vec![
                ("\\n".into(), "\n".into()),
                ("\\t".into(), "\t".into()),
                ("\\\"".into(), "\"".into()),
                ("\\\\".into(), "\\".into()),
            ],
        });
        let j = serde_json::to_string(&t).unwrap();
        let back: TokenKindDef = serde_json::from_str(&j).unwrap();
        assert_eq!(t, back);
    }

    #[test]
    fn literal_kind_strip_affix_roundtrip() {
        let t = TokenKindDef::new("token.json").with_literal(LiteralKind::StripAffix {
            prefix: "json{".into(),
            suffix: "}".into(),
            wrap: Some(("{".into(), "}".into())),
        });
        let j = serde_json::to_string(&t).unwrap();
        let back: TokenKindDef = serde_json::from_str(&j).unwrap();
        assert_eq!(t, back);
    }

    #[test]
    fn is_union_type() {
        // Token kind declarations are structural facts, so they merge
        // idempotently rather than colliding.
        assert!(TokenKindDef::UNION);
    }

    #[test]
    fn merge_same_id_is_idempotent() {
        use crate::FragmentSet;
        let mut set: FragmentSet<TokenKindDef> = FragmentSet::new();
        let first = TokenKindDef::new("token.lparen").with_label("(");
        let second = TokenKindDef::new("token.lparen").with_label("(dup)");
        set.merge(first.clone()).expect("first merge ok");
        // Merging a second declaration with the same id is a no-op (union),
        // NOT a collision.
        set.merge(second).expect("duplicate merge is idempotent");
        assert_eq!(set.len(), 1);
        // The first declaration is kept.
        assert_eq!(
            set.get_by_id("token.lparen").unwrap().label.as_deref(),
            Some("(")
        );
    }
}
