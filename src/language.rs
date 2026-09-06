//! The `Language` struct — pure serializable data built by merging fragments
//! (ADR-0044 §1).
//!
//! A `Language` carries no Rust: no trait objects, no closures, no
//! `Box<dyn Behavior>`. It is `serde`-serializable end to end. Composition is
//! [`Language::merge`], applied in kit-defined order; partial merge failure
//! rolls back atomically.

use serde::{Deserialize, Serialize};

use crate::ast::{Ast, AstNode, AstRef};
use crate::error::LangError;
use crate::fragment_set::FragmentSet;
use crate::fragments::{
    AstShapeDef, CapabilityDecl, EvalSchemeDef, GrammarRow, LexerRuleDef, OptionSchema,
    TokenKindDef, TypeRuleDef,
};
use crate::version::SchemeVersion;

/// A language definition as pure serializable data.
///
/// Built by merging fragments into typed fragment sets. The
/// `scheme_version` field (ADR-0044 §7) declares which `Scheme` combinator
/// version the language targets; the canonical version is `"v2"` (the
/// arrow-calculus kernel, ADR-0052).
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct Language {
    /// Token kind definitions.
    pub tokens: FragmentSet<TokenKindDef>,
    /// Grammar table rows.
    pub grammar: FragmentSet<GrammarRow>,
    /// Eval scheme definitions mapping node kinds to
    /// [`Scheme`](crate::Scheme)s (arrow-calculus kernel, ADR-0052).
    pub eval: FragmentSet<EvalSchemeDef>,
    /// Type rule definitions: node kind → synth/check `Scheme`
    /// (ADR-0054 — Generic Typecheck Engine).
    pub types: FragmentSet<TypeRuleDef>,
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
    /// Create a new empty language targeting `SchemeVersion::v2()`.
    pub fn new() -> Self {
        Self {
            tokens: FragmentSet::new(),
            grammar: FragmentSet::new(),
            eval: FragmentSet::new(),
            types: FragmentSet::new(),
            ast: FragmentSet::new(),
            caps: FragmentSet::new(),
            options: FragmentSet::new(),
            lexer_rules: FragmentSet::new(),
            scheme_version: SchemeVersion::v2(),
        }
    }

    /// Merge another `Language` into this one, set by set.
    ///
    /// All fragment sets are merged independently. On any failure, **no
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
        for frag in other.types.fragments().cloned() {
            clone.types.merge(frag)?;
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

    /// Resolve a named child role (ADR-0081) to its positional index for a node
    /// kind, using this language's AST shapes.
    ///
    /// This is the runtime-resolution entry point engines call to replace
    /// `kind ==` shape checks: instead of testing `node.kind == "assign"` and
    /// assuming child 0 is the target, an engine resolves
    /// `lang.child_role_index(node.kind, "target")` and projects that position.
    ///
    /// Returns `Ok(Some(index))` when the role is declared, `Ok(None)` when the
    /// node kind has no shape or no such role (opaque/positional fallback), and
    /// `Err` when a shape exists but the resolved index is out of bounds for
    /// the node's children (a load-time data inconsistency).
    pub fn child_role_index(
        &self,
        node_kind: &str,
        role: &str,
    ) -> Result<Option<usize>, LangError> {
        let Some(def) = self.ast.get_by_identity(node_kind) else {
            return Ok(None);
        };
        Ok(def.role_index(role))
    }

    /// Whether a child node of `child_kind` occupying `role` of `node_kind`
    /// is declared **literal** — its payload is the datum itself rather than
    /// an expression to evaluate (ADR-0081 extension).
    ///
    /// Engines use this to replace `key_node.kind == "var" || kind ==
    /// "string"`-style literal-vs-computed heuristics: e.g. an object
    /// `entry` shape declares `literal_children: { key: [var, string] }` so
    /// `{ a: 1, "b": 2 }` keys are read from the payload while `[expr]:` /
    /// `paren` keys are evaluated.
    ///
    /// Returns `Some(bool)` when the shape declares a literal-kinds list for
    /// `role`, `None` when it declares none — callers keep their legacy
    /// fallback heuristic for role-less shapes.
    pub fn literal_child(
        &self,
        node_kind: &str,
        role: &str,
        child_kind: &str,
    ) -> Option<bool> {
        self.ast
            .get_by_identity(node_kind)
            .and_then(|def| def.literal_child(role, child_kind))
    }

    /// Whether `node_kind`'s shape declares any variadic child role (ADR-0081).
    ///
    /// Engines use this to replace `kind == "paren" || kind == "array"` shape
    /// heuristics: a node whose shape declares a variadic role (e.g. `params`
    /// or `statements`) is a collection-like node, regardless of its surface
    /// kind name. Returns `false` when the kind has no shape or no variadic
    /// roles (callers fall back to legacy kind checks for role-less shapes).
    pub fn has_variadic_role(&self, node_kind: &str) -> bool {
        self.ast
            .get_by_identity(node_kind)
            .and_then(|def| def.children.as_ref())
            .map(|children| children.iter().any(|spec| spec.variadic))
            .unwrap_or(false)
    }

    /// Extract the parameter name from a param node, unwrapping type
    /// annotations (ADR-0081 data-driven: uses the `subject` child role
    /// declared by `type-annot`'s `AstShapeDef`, never a `kind ==`
    /// check).
    ///
    /// A bare `var` node has a string payload (the name) and is returned
    /// directly. A `type-annot` node (e.g. `x: Int`) has a `subject` role
    /// pointing at the inner `var`; this resolves that child and reads
    /// its string payload. Returns `Err` if the name cannot be extracted.
    pub fn param_name(&self, ast: &Ast, param_node: &AstNode) -> Result<String, LangError> {
        // Fast path: the param is a bare `var` with a string payload.
        if let Some(name) = param_node.payload.as_str() {
            return Ok(name.to_string());
        }
        // Data-driven unwrap: if the node's shape declares a `subject`
        // role (e.g. `type-annot`), resolve that child and read its
        // string payload. This is the data-driven equivalent of
        // "if kind == type-annot, look at child 0" — but it works for
        // any shape that declares a `subject` role, not just
        // `type-annot` specifically.
        if let Ok(Some(subject_idx)) = self.child_role_index(&param_node.kind, "subject") {
            let children = param_node
                .payload
                .get("children")
                .and_then(|c| c.as_array());
            if let Some(children) = children {
                if let Some(child_entry) = children.get(subject_idx) {
                    if let Some(inner_idx) = child_entry.as_u64() {
                        let inner = ast.at(AstRef::new(inner_idx as usize))?;
                        if let Some(name) = inner.payload.as_str() {
                            return Ok(name.to_string());
                        }
                    }
                }
            }
        }
        Err(LangError::engine(
            "closure: param must be a var with string payload (or a type-annot wrapping one)"
                .to_string(),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fragments::TypeRuleDef;
    use crate::fragments::grammar::{AstShapeRef, GrammarPosition};
    use crate::scheme::Scheme;

    #[test]
    fn new_is_empty_with_v2() {
        let lang = Language::new();
        assert!(lang.tokens.is_empty());
        assert_eq!(lang.scheme_version, SchemeVersion::v2());
    }

    #[test]
    fn default_is_empty_with_v2() {
        let lang = Language::default();
        assert!(lang.tokens.is_empty());
        assert_eq!(lang.scheme_version, SchemeVersion::v2());
    }

    #[test]
    fn merge_all_sets() {
        let mut base = Language::new();
        let mut other = Language::new();
        other.tokens.merge(TokenKindDef::new("token.num")).unwrap();
        other
            .grammar
            .merge(GrammarRow::new(
                "g1",
                "token.plus",
                GrammarPosition::Infix,
                AstShapeRef::new("binary.add", 2),
            ))
            .unwrap();
        other
            .eval
            .merge(EvalSchemeDef::new(
                "e1",
                "binary.add",
                Scheme::arr_native("add", vec![]),
            ))
            .unwrap();
        other
            .types
            .merge(TypeRuleDef::new(
                "t1",
                "lit",
                Scheme::arr_judgment("synth_child", vec![]),
            ))
            .unwrap();
        other
            .ast
            .merge(AstShapeDef::new("a1", "binary.add"))
            .unwrap();
        other.caps.merge(CapabilityDecl::new("fs.read")).unwrap();
        other.options.merge(OptionSchema::new("opt.x")).unwrap();
        base.merge(other).unwrap();
        assert_eq!(base.tokens.len(), 1);
        assert_eq!(base.grammar.len(), 1);
        assert_eq!(base.eval.len(), 1);
        assert_eq!(base.types.len(), 1);
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
        other
            .eval
            .merge(EvalSchemeDef::new(
                "e1",
                "binary.add",
                Scheme::arr_native("add", vec![]),
            ))
            .unwrap();
        // Set up the base to collide on the eval set.
        base.eval
            .merge(EvalSchemeDef::new(
                "e0",
                "binary.add",
                Scheme::arr_native("add", vec![]),
            ))
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
        assert!(j.contains("\"v2\""));
        let back: Language = serde_json::from_str(&j).unwrap();
        assert_eq!(back.scheme_version, SchemeVersion::v2());
    }
}
