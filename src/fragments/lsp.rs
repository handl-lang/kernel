//! LSP surface fragment (ADR-0100).
//!
//! A `LspDef` is a generic, method-keyed declaration of which LSP requests a
//! language supports and which data-driven rules the `plugin-lsp` engine should
//! run for each.  The engine is method-agnostic: it looks at the LSP method
//! string, evaluates the rule list in order, and dispatches each rule by its
//! `kind` field.  All rule configuration lives in the `config` map, so a
//! language can invent rules for any future `kind` the engine learns without
//! changing the `Language` schema.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use crate::fragment::Fragment;
use crate::fragments::transform_def::TransformCondition;
use crate::Value;

/// A fragment that declares the LSP surface for a language.
///
/// `lsp.yaml` is a list of these fragments (typically one per kit).  The
/// `rules` map defines named rule recipes; the `lsp` map assigns rule ids to
/// LSP method strings.  Missing methods mean the engine returns an empty/null
/// response for that request.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct LspDef {
    /// Stable fragment identifier (e.g. `canonical.lsp`).
    pub id: String,
    /// Rule recipes keyed by rule id.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub rules: BTreeMap<String, LspRule>,
    /// LSP method -> ordered list of rule ids to evaluate.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub lsp: BTreeMap<String, Vec<String>>,
    /// ids this fragment declares it replaces.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub replaces: Vec<String>,
    /// ids this fragment hard-requires.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub requires: Vec<String>,
}

impl LspDef {
    /// Create a new empty LSP fragment.
    pub fn new(id: impl Into<String>) -> Self {
        Self {
            id: id.into(),
            rules: BTreeMap::new(),
            lsp: BTreeMap::new(),
            replaces: Vec::new(),
            requires: Vec::new(),
        }
    }
}

impl Fragment for LspDef {
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
}

/// A single data-driven rule recipe.
///
/// `kind` selects the `plugin-lsp` provider that runs the rule.  All other
/// fields are interpreted by that provider.  The `config` map preserves
/// arbitrary provider configuration without hard-coding it in the `Language`
/// schema, so the surface can evolve entirely in `lsp.yaml`.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct LspRule {
    /// The rule provider kind (e.g. `export`, `import_path`, `import_name`).
    pub kind: String,
    /// Optional AST/token condition gating the rule.
    #[serde(default, skip_serializing_if = "Option::is_none", rename = "match")]
    pub match_condition: Option<LspMatch>,
    /// Provider-specific configuration.
    #[serde(flatten)]
    pub config: BTreeMap<String, Value>,
}

/// Conditions an `LspRule` can match against.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum LspMatch {
    /// Match an AST node kind, optionally gated by a `TransformCondition`.
    Match {
        /// The AST node kind to consider.
        node_kind: String,
        /// Optional extra condition on the matched node.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        when: Option<TransformCondition>,
    },
    /// Match a token position / cursor context.
    Token {
        /// The cursor must follow one of these token ids.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        preceding: Vec<String>,
        /// The cursor must be inside a string token.
        #[serde(default)]
        in_string: bool,
    },
    /// A named native provider (engine-specific).
    Native(String),
}
