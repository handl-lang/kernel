//! Token-kind classification tables resolved from `Language::tokens`
//! data (ADR-0044) — moved here from `kit-canonical` (ADR-0128 §0.8) so
//! tooling hosts classify without linking the canonical kit.

use crate::Language;


/// Token-kind classification resolved from a [`Language`]'s `tokens` fragment
/// set (`TokenKindDef::category`/`pair`/`doc`/`label`) — the data-driven
/// replacement for the string-matching `is_identifier_kind`-style helpers
/// below.
///
/// Build one per host from the language
/// (`TokenClasses::new(lang)`) and query by category, pair, label,
/// or doc instead of comparing `token.kind` against `"token.*"` literals: a
/// language whose kinds are named differently still classifies correctly
/// because the category travels with the token data.
///
/// Category vocabulary used by the canonical kit: `keyword`, `identifier`,
/// `number`, `string`, `bool`, `null`, `template`, `operator`,
/// `punctuation`, `open-bracket`, `close-bracket`, `comment`, `doc-comment`,
/// `eof`.
#[derive(Debug, Clone)]
pub struct TokenClasses {
    /// kind id → category.
    categories: std::collections::HashMap<String, String>,
    /// kind id → paired bracket kind id.
    pairs: std::collections::HashMap<String, String>,
    /// surface-syntax label → kind id (first declaration wins).
    labels: std::collections::HashMap<String, String>,
    /// kind id → declared surface-syntax label.
    kind_labels: std::collections::HashMap<String, String>,
    /// kind id → hover/doc markdown.
    docs: std::collections::HashMap<String, String>,
}

impl TokenClasses {
    /// Build the classification tables from `lang`'s `tokens` fragment set.
    pub fn new(lang: &Language) -> Self {
        let mut classes = Self {
            categories: std::collections::HashMap::new(),
            pairs: std::collections::HashMap::new(),
            labels: std::collections::HashMap::new(),
            kind_labels: std::collections::HashMap::new(),
            docs: std::collections::HashMap::new(),
        };
        for def in lang.tokens.iter() {
            if let Some(cat) = &def.category {
                classes.categories.insert(def.id.clone(), cat.clone());
            }
            if let Some(pair) = &def.pair {
                classes.pairs.insert(def.id.clone(), pair.clone());
            }
            if let Some(label) = &def.label {
                classes
                    .labels
                    .entry(label.clone())
                    .or_insert_with(|| def.id.clone());
                classes.kind_labels.insert(def.id.clone(), label.clone());
            }
            if let Some(doc) = &def.doc {
                classes.docs.insert(def.id.clone(), doc.clone());
            }
        }
        classes
    }

    /// Whether token kind `kind` is classified as `category`.
    pub fn is(&self, kind: &str, category: &str) -> bool {
        self.categories
            .get(kind)
            .map(|c| c == category)
            .unwrap_or(false)
    }

    /// The declared category for `kind`, if any.
    pub fn category_of(&self, kind: &str) -> Option<&str> {
        self.categories.get(kind).map(String::as_str)
    }

    /// Whether `kind` is an identifier.
    pub fn is_identifier(&self, kind: &str) -> bool {
        self.is(kind, "identifier")
    }

    /// Whether `kind` is a keyword.
    pub fn is_keyword(&self, kind: &str) -> bool {
        self.is(kind, "keyword")
    }

    /// Whether `kind` is a number literal.
    pub fn is_number(&self, kind: &str) -> bool {
        self.is(kind, "number")
    }

    /// Whether `kind` is a string literal.
    pub fn is_string(&self, kind: &str) -> bool {
        self.is(kind, "string")
    }

    /// Whether `kind` is a boolean literal.
    pub fn is_bool(&self, kind: &str) -> bool {
        self.is(kind, "bool")
    }

    /// Whether `kind` is the null literal.
    pub fn is_null(&self, kind: &str) -> bool {
        self.is(kind, "null")
    }

    /// Whether `kind` is a comment (line or doc comment).
    pub fn is_comment(&self, kind: &str) -> bool {
        self.is(kind, "comment") || self.is(kind, "doc-comment")
    }

    /// Whether `kind` is a doc comment.
    pub fn is_doc_comment(&self, kind: &str) -> bool {
        self.is(kind, "doc-comment")
    }

    /// Whether `kind` is an operator.
    pub fn is_operator(&self, kind: &str) -> bool {
        self.is(kind, "operator")
    }

    /// Whether `kind` is a template string.
    pub fn is_template(&self, kind: &str) -> bool {
        self.is(kind, "template")
    }

    /// Whether `kind` is a delimiter/punctuation (brackets and separators).
    pub fn is_delimiter(&self, kind: &str) -> bool {
        self.is(kind, "punctuation")
            || self.is(kind, "open-bracket")
            || self.is(kind, "close-bracket")
    }

    /// Whether `kind` opens a bracket pair.
    pub fn is_open_bracket(&self, kind: &str) -> bool {
        self.is(kind, "open-bracket")
    }

    /// Whether `kind` closes a bracket pair.
    pub fn is_close_bracket(&self, kind: &str) -> bool {
        self.is(kind, "close-bracket")
    }

    /// Whether `kind` is any bracket (open or close).
    pub fn is_bracket(&self, kind: &str) -> bool {
        self.is_open_bracket(kind) || self.is_close_bracket(kind)
    }

    /// The kind id paired with `kind` (open ↔ close), if declared.
    pub fn pair_of(&self, kind: &str) -> Option<&str> {
        self.pairs.get(kind).map(String::as_str)
    }

    /// Resolve a surface-syntax `label` (e.g. `"."`, `"::"`) to the kind id
    /// that declares it — the data-driven answer to "is this the dot token?".
    pub fn kind_for_label(&self, label: &str) -> Option<&str> {
        self.labels.get(label).map(String::as_str)
    }

    /// Whether token kind `kind` is the kind that spells `label`.
    pub fn is_label(&self, kind: &str, label: &str) -> bool {
        self.kind_for_label(label) == Some(kind)
    }

    /// The surface-syntax label declared for `kind`, if any.
    pub fn label_of(&self, kind: &str) -> Option<&str> {
        self.kind_labels.get(kind).map(String::as_str)
    }

    /// The hover/doc markdown declared for `kind`, if any.
    pub fn doc_of(&self, kind: &str) -> Option<&str> {
        self.docs.get(kind).map(String::as_str)
    }
}