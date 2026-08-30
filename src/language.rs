//! The `Language` struct — pure serializable data built by merging fragments
//! (ADR-0044 §1).
//!
//! A `Language` carries no Rust: no trait objects, no closures, no
//! `Box<dyn Behavior>`. It is `serde`-serializable end to end. Composition is
//! [`Language::merge`], applied in kit-defined order; partial merge failure
//! rolls back atomically.

use serde::{Deserialize, Serialize};

use crate::error::LangError;
use crate::fragment_set::FragmentSet;
use crate::fragments::{
    AstShapeDef, CapabilityDecl, EvalSchemeDef, GrammarRow, LexerRuleDef, OptionSchema,
    TokenKindDef,
};
use crate::version::SchemeVersion;

/// A language definition as pure serializable data.
///
/// Built by merging fragments into six typed fragment sets. The
/// `scheme_version` field (ADR-0044 §7) declares which `Scheme` combinator
/// version the language targets.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct Language {
    /// Token kind definitions.
    pub tokens: FragmentSet<TokenKindDef>,
    /// Grammar table rows.
    pub grammar: FragmentSet<GrammarRow>,
    /// Eval scheme definitions mapping node kinds to [`Scheme`](crate::Scheme)s.
    pub eval: FragmentSet<EvalSchemeDef>,
    /// AST node shape definitions.
    pub ast: FragmentSet<AstShapeDef>,
    /// Capability declarations.
    pub caps: FragmentSet<CapabilityDecl>,
    /// Option schemas.
    pub options: FragmentSet<OptionSchema>,
    /// Lexer rule definitions — the patterns a data-driven lexer engine reads
    /// to tokenize source text.
    pub lexer_rules: FragmentSet<LexerRuleDef>,
    /// The scheme combinator version this language targets.
    pub scheme_version: SchemeVersion,
}

impl Default for Language {
    fn default() -> Self {
        Self::new()
    }
}

impl Language {
    /// Create a new empty language targeting `SchemeVersion::v1()`.
    pub fn new() -> Self {
        Self {
            tokens: FragmentSet::new(),
            grammar: FragmentSet::new(),
            eval: FragmentSet::new(),
            ast: FragmentSet::new(),
            caps: FragmentSet::new(),
            options: FragmentSet::new(),
            lexer_rules: FragmentSet::new(),
            scheme_version: SchemeVersion::v1(),
        }
    }

    /// Merge another `Language` into this one, set by set.
    ///
    /// All six fragment sets are merged independently. On any failure, **no
    /// partial state is committed**: the merge is performed into a clone and
    /// only swapped in on full success (atomic rollback).
    ///
    /// # Errors
    ///
    /// Returns the first [`LangError`] encountered; `self` is left unchanged.
    pub fn merge(&mut self, other: Language) -> Result<(), LangError> {
        let mut clone = self.clone();
        for frag in other.tokens.fragments().cloned() {
            clone.tokens.merge(frag)?;
        }
        for frag in other.grammar.fragments().cloned() {
            clone.grammar.merge(frag)?;
        }
        for frag in other.eval.fragments().cloned() {
            clone.eval.merge(frag)?;
        }
        for frag in other.ast.fragments().cloned() {
            clone.ast.merge(frag)?;
        }
        for frag in other.caps.fragments().cloned() {
            clone.caps.merge(frag)?;
        }
        for frag in other.options.fragments().cloned() {
            clone.options.merge(frag)?;
        }
        for frag in other.lexer_rules.fragments().cloned() {
            clone.lexer_rules.merge(frag)?;
        }
        *self = clone;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fragments::grammar::{AstShapeRef, GrammarPosition};
    use crate::scheme::Scheme;
    use serde_json::Value;

    #[test]
    fn new_is_empty_with_v1() {
        let lang = Language::new();
        assert!(lang.tokens.is_empty());
        assert_eq!(lang.scheme_version, SchemeVersion::v1());
    }

    #[test]
    fn default_is_empty_with_v1() {
        let lang = Language::default();
        assert!(lang.tokens.is_empty());
        assert_eq!(lang.scheme_version, SchemeVersion::v1());
    }

    #[test]
    fn merge_all_six_sets() {
        let mut base = Language::new();
        let mut other = Language::new();
        other.tokens.merge(TokenKindDef::new("token.num")).unwrap();
        other.grammar
            .merge(GrammarRow::new(
                "g1",
                "token.plus",
                GrammarPosition::Infix,
                AstShapeRef::new("binary.add", 2),
            ))
            .unwrap();
        other.eval
            .merge(EvalSchemeDef::new("e1", "binary.add", Scheme::lit(Value::Null)))
            .unwrap();
        other.ast.merge(AstShapeDef::new("a1", "binary.add")).unwrap();
        other.caps.merge(CapabilityDecl::new("fs.read")).unwrap();
        other.options.merge(OptionSchema::new("opt.x")).unwrap();
        base.merge(other).unwrap();
        assert_eq!(base.tokens.len(), 1);
        assert_eq!(base.grammar.len(), 1);
        assert_eq!(base.eval.len(), 1);
        assert_eq!(base.ast.len(), 1);
        assert_eq!(base.caps.len(), 1);
        assert_eq!(base.options.len(), 1);
    }

    #[test]
    fn partial_failure_rolls_back_atomically() {
        let mut base = Language::new();
        base.tokens.merge(TokenKindDef::new("token.num")).unwrap();

        let mut other = Language::new();
        // This token merges fine.
        other.tokens.merge(TokenKindDef::new("token.str")).unwrap();
        // This eval collides: base already has "binary.add".
        other.eval
            .merge(EvalSchemeDef::new("e1", "binary.add", Scheme::lit(Value::Null)))
            .unwrap();
        // Set up the base to collide on the eval set.
        base.eval
            .merge(EvalSchemeDef::new("e0", "binary.add", Scheme::lit(Value::Null)))
            .unwrap();
        let snapshot = base.clone();

        // `other.eval` has "binary.add" which collides with base's "binary.add".
        let err = base.merge(other).unwrap_err();
        assert_eq!(
            err,
            LangError::Collision {
                existing: "e0".into(),
                incoming: "e1".into()
            }
        );
        // base unchanged.
        assert_eq!(base, snapshot);
        assert_eq!(base.tokens.len(), 1);
    }

    #[test]
    fn serde_roundtrip() {
        let mut lang = Language::new();
        lang.tokens.merge(TokenKindDef::new("token.num")).unwrap();
        lang.caps.merge(CapabilityDecl::new("fs.read")).unwrap();
        let j = serde_json::to_string(&lang).unwrap();
        let back: Language = serde_json::from_str(&j).unwrap();
        assert_eq!(lang, back);
    }

    #[test]
    fn scheme_version_serializes() {
        let lang = Language::new();
        let j = serde_json::to_string(&lang).unwrap();
        assert!(j.contains("\"v1\""));
        let back: Language = serde_json::from_str(&j).unwrap();
        assert_eq!(back.scheme_version, SchemeVersion::v1());
    }
}
