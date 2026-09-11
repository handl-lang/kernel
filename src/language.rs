//! The `Language` struct — pure serializable data built by merging fragments
//! (ADR-0044 §1).
//!
//! A `Language` carries no Rust: no trait objects, no closures, no
//! `Box<dyn Behavior>`. It is `serde`-serializable end to end. Composition is
//! [`Language::merge`], applied in kit-defined order; partial merge failure
//! rolls back atomically.

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

use crate::Value;
use crate::ast::{Ast, AstNode, AstRef};
use crate::error::LangError;
use crate::fragment_set::FragmentSet;
use crate::fragments::{
    AstShapeDef, CapabilityDecl, EvalSchemeDef, GrammarRow, LexerRuleDef, LintRuleDef,
    OptionSchema, TokenKindDef, TransformDef, TypeRuleDef,
};
use crate::version::SchemeVersion;

/// A language definition as pure serializable data.
///
/// Built by merging fragments into typed fragment sets. The
/// `scheme_version` field (ADR-0044 §7) declares which `Term` combinator
/// version the language targets; the canonical version is `"v2"` (the
/// arrow-calculus kernel, ADR-0052).
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct Language {
    /// Token kind definitions.
    pub tokens: FragmentSet<TokenKindDef>,
    /// Grammar table rows.
    pub grammar: FragmentSet<GrammarRow>,
    /// Eval scheme definitions mapping node kinds to
    /// [`Term`](crate::Term)s (arrow-calculus kernel, ADR-0052).
    pub eval: FragmentSet<EvalSchemeDef>,
    /// Type rule definitions: node kind → synth/check `Term`
    /// (ADR-0054 — Generic Typecheck Engine).
    pub types: FragmentSet<TypeRuleDef>,
    /// AST node shape definitions.
    pub ast: FragmentSet<AstShapeDef>,
    /// Transform rule definitions (ADR-0094 — Generic AST Transform Engine):
    /// the `(pass, node_kind, priority)`-keyed dispatch table transform
    /// engines read. `AstShapeDef::desugar` rules are **lowered** into this
    /// set at merge time (pass `"desugar"`).
    pub transforms: FragmentSet<TransformDef>,
    /// Capability declarations.
    pub caps: FragmentSet<CapabilityDecl>,
    /// Option schemas.
    pub options: FragmentSet<OptionSchema>,
    /// Lexer rule definitions — the patterns a data-driven lexer engine reads
    /// to tokenize source text.
    pub lexer_rules: FragmentSet<LexerRuleDef>,
    /// Lint rule definitions (ADR-0097 — Lint Rules as Language Data): the
    /// rule table lint engines read. Absent in serialized languages written
    /// before ADR-0097, hence `serde(default)`.
    #[serde(default)]
    pub lints: FragmentSet<LintRuleDef>,
    /// Evaluated `op` declarations keyed by op name (ADR-0098/0100).
    #[serde(default)]
    pub ops: BTreeMap<String, crate::Value>,
    /// Handler values keyed by handler name (ADR-0098/0100).
    #[serde(default)]
    pub handlers: BTreeMap<String, crate::Value>,
    /// Handlers indexed by grade (computed from `handlers` entries).
    #[serde(default)]
    pub handlers_by_grade: BTreeMap<String, crate::Value>,
    /// Declared laws `source ~> target` keyed by name (ADR-0100).
    #[serde(default)]
    pub laws: BTreeMap<String, crate::Value>,
    /// Declared rewrite rules `source ~> target` keyed by name (ADR-0100).
    #[serde(default)]
    pub rewrites: BTreeMap<String, crate::Value>,
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
            transforms: FragmentSet::new(),
            caps: FragmentSet::new(),
            options: FragmentSet::new(),
            lexer_rules: FragmentSet::new(),
            lints: FragmentSet::new(),
            ops: BTreeMap::new(),
            handlers: BTreeMap::new(),
            handlers_by_grade: BTreeMap::new(),
            laws: BTreeMap::new(),
            rewrites: BTreeMap::new(),
            scheme_version: SchemeVersion::v2(),
        }
    }

    /// Return the evaluated `op` declaration for `name`, if any.
    pub fn op_decl(&self, name: &str) -> Option<crate::Value> {
        self.ops.get(name).cloned()
    }

    /// Return the first handler value whose `grades` list contains `grade`.
    pub fn handler_for_grade(&self, grade: &str) -> Option<crate::Value> {
        if let Some(v) = self.handlers_by_grade.get(grade) {
            return Some(v.clone());
        }
        self.handlers
            .values()
            .find(|h| {
                h.get("grades")
                    .and_then(Value::as_array)
                    .map(|arr| arr.iter().any(|v| v.as_str() == Some(grade)))
                    .unwrap_or(false)
            })
            .cloned()
    }

    /// Register an evaluated `op` declaration under its name.
    pub fn register_op(&mut self, name: impl Into<String>, value: crate::Value) {
        self.ops.insert(name.into(), value);
    }

    /// Register an evaluated `handler` declaration under its name and update
    /// the grade index.
    pub fn register_handler(&mut self, name: impl Into<String>, value: crate::Value) {
        let name = name.into();
        if let Some(grades) = value.get("grades").and_then(Value::as_array) {
            for g in grades.iter().filter_map(Value::as_str) {
                self.handlers_by_grade.insert(g.to_string(), value.clone());
            }
        }
        self.handlers.insert(name, value);
    }

    /// Return the declared law `source ~> target` for `name`, if any.
    pub fn law(&self, name: &str) -> Option<crate::Value> {
        self.laws.get(name).cloned()
    }

    /// Return the declared rewrite rule `source ~> target` for `name`, if any.
    pub fn rewrite_rule(&self, name: &str) -> Option<crate::Value> {
        self.rewrites.get(name).cloned()
    }

    /// Register a declared law `source ~> target` under its name.
    pub fn register_law(&mut self, name: impl Into<String>, value: crate::Value) {
        self.laws.insert(name.into(), value);
    }

    /// Register a declared rewrite rule `source ~> target` under its name.
    pub fn register_rewrite(&mut self, name: impl Into<String>, value: crate::Value) {
        self.rewrites.insert(name.into(), value);
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
            clone.merge_ast_fragment_inner(frag)?;
        }
        for frag in other.transforms.fragments().cloned() {
            // A fragment already present with identical content is a no-op —
            // in particular, a `transform.desugar.*` rule synthesized by
            // `AstShapeDef::desugar` lowering above must not collide with
            // the same synthesized rule carried over in `other.transforms`.
            if clone.transforms.get_by_id(&frag.id) == Some(&frag) {
                continue;
            }
            clone.transforms.merge(frag)?;
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
        for frag in other.lints.fragments().cloned() {
            clone.lints.merge(frag)?;
        }
        *self = clone;
        Ok(())
    }

    /// Merge a single [`AstShapeDef`] into this language, lowering any
    /// `desugar` rule it carries into a [`TransformDef`] in the `transforms`
    /// set (ADR-0094 §6).
    ///
    /// This is the merge path every `ast`-fragment loader should use: it
    /// merges `frag` into `ast` and, when the fragment is actually kept by
    /// the merge (AST shapes are union fragments — a duplicate declaration
    /// is dropped, and so is its desugar rule) and declares
    /// `desugar: Some(..)`, synthesizes a `TransformDef` with
    /// `id = "transform.desugar.<node_kind>"`, `pass = "desugar"`, and
    /// `priority = 0`.
    ///
    /// The merge is atomic: on failure `self` is left unchanged.
    ///
    /// # Errors
    ///
    /// Returns [`LangError`] if either the shape merge or the synthesized
    /// transform merge fails.
    pub fn merge_ast_fragment(&mut self, frag: AstShapeDef) -> Result<(), LangError> {
        let mut clone = self.clone();
        clone.merge_ast_fragment_inner(frag)?;
        *self = clone;
        Ok(())
    }

    /// Non-atomic inner merge used by [`Language::merge`] (which already
    /// merges into a clone) and [`Language::merge_ast_fragment`].
    fn merge_ast_fragment_inner(&mut self, frag: AstShapeDef) -> Result<(), LangError> {
        let id = frag.id.clone();
        let node_kind = frag.node_kind.clone();
        let desugar = frag.desugar.clone();
        // `AstShapeDef` merges with union semantics: an incoming shape whose
        // `node_kind` is already declared is *dropped* (first declaration
        // wins), and its `desugar` rule is dropped with it. Capture the
        // shape currently occupying the identity key so we can tell whether
        // this merge actually installed the incoming fragment.
        let prior = self.ast.get_by_identity(&node_kind);
        let prior_id = prior.map(|d| d.id.clone());
        let prior_had_desugar = prior.map(|d| d.desugar.is_some()).unwrap_or(false);
        self.ast.merge(frag)?;
        let kept = self
            .ast
            .get_by_identity(&node_kind)
            .map(|d| d.id == id)
            .unwrap_or(false);
        // Union-dropped incoming shape, or an idempotent re-merge of the
        // fragment already in place: nothing to lower.
        if !kept || prior_id.as_deref() == Some(id.as_str()) {
            return Ok(());
        }
        // The replaced shape's synthesized desugar rule (if any) is stale —
        // remove it so `transforms` stays in sync with `ast`. (`replaces`
        // cannot express this: the synthesized id is deterministic, so the
        // incoming rule would "replace" itself and trip the cycle check.)
        let synth_id = format!("transform.desugar.{}", node_kind);
        if prior_had_desugar {
            self.transforms.remove_by_id(&synth_id);
        }
        if let Some(rule) = desugar {
            self.transforms
                .merge(crate::fragments::transform_def::lower_desugar_rule(
                    &node_kind, &rule,
                ))?;
        }
        Ok(())
    }

    /// All transform rules declared for `pass` + `node_kind`, sorted by
    /// `priority` ascending (lower priority fires first).
    ///
    /// This is the lookup a transform engine builds its
    /// `kind → Vec<TransformDef>` dispatch table from (ADR-0094 §4).
    pub fn transforms_for(&self, pass: &str, node_kind: &str) -> Vec<&TransformDef> {
        let mut rules: Vec<&TransformDef> = self
            .transforms
            .iter()
            .filter(|d| d.pass == pass && d.node_kind == node_kind)
            .collect();
        rules.sort_by_key(|d| d.priority);
        rules
    }

    /// Return the [`TokenKindDef`] declared for `kind`, if any.
    pub fn token_kind(&self, kind: &str) -> Option<&TokenKindDef> {
        self.tokens.get_by_id(kind)
    }

    /// Return the classification `category` declared for token kind `kind`
    /// (e.g. `"keyword"`, `"open-bracket"`), or `None` when the kind is
    /// undeclared or carries no category.
    ///
    /// This is the data-driven replacement for string-matching on kind ids
    /// (`kind == "token.lparen"`, `kind.starts_with("token.keyword")`) in
    /// tooling — a language that spells or names its tokens differently still
    /// classifies correctly because the category travels with the token data
    /// (ADR-0044).
    pub fn token_category(&self, kind: &str) -> Option<&str> {
        self.token_kind(kind).and_then(|d| d.category.as_deref())
    }

    /// Whether token kind `kind` is classified as `category`.
    pub fn token_in_category(&self, kind: &str, category: &str) -> bool {
        self.token_category(kind) == Some(category)
    }

    /// Return the id of the bracket counterpart declared for `kind`
    /// (`TokenKindDef::pair`), if any.
    pub fn token_pair(&self, kind: &str) -> Option<&str> {
        self.token_kind(kind).and_then(|d| d.pair.as_deref())
    }

    /// Return the hover/documentation markdown declared for `kind`
    /// (`TokenKindDef::doc`), if any.
    pub fn token_doc(&self, kind: &str) -> Option<&str> {
        self.token_kind(kind).and_then(|d| d.doc.as_deref())
    }

    /// Resolve a surface-syntax `label` (e.g. `"."`, `"::"`) to the id of the
    /// token kind that declares it. Lets tooling ask "which kind is the
    /// member-access token?" without hardcoding canonical kind ids — a
    /// language that spells member access differently still answers.
    ///
    /// When several kinds share a label the first declaration wins.
    pub fn token_kind_for_label(&self, label: &str) -> Option<&str> {
        self.tokens
            .iter()
            .find(|d| d.label.as_deref() == Some(label))
            .map(|d| d.id.as_str())
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
    pub fn literal_child(&self, node_kind: &str, role: &str, child_kind: &str) -> Option<bool> {
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

    /// Extract the parameter names from an arrow's params node, splitting
    /// off an optional rest parameter (`[a, b, ...rest] ~> body`).
    ///
    /// Returns `(fixed_params, rest_param)`. A params node whose shape
    /// declares a variadic child role (ADR-0081, e.g. `elements`) is a
    /// parameter list: each child is an ordinary param (resolved via
    /// [`param_name`](Self::param_name)) unless its own shape declares
    /// `pattern_role: rest`, in which case its `subject` child names the
    /// rest binding. A non-collection params node is a single param; if
    /// it is itself a `rest` node, the arrow is fully variadic.
    ///
    /// The `rest` check is data-driven — dispatch is on the child's
    /// `AstShapeDef::pattern_role`, never on a hardcoded kind string.
    ///
    /// Use [`is_array_pattern`](Self::is_array_pattern) to distinguish a
    /// positional/`paren` param list from an array-destructuring pattern.
    pub fn param_names(
        &self,
        ast: &Ast,
        params_node: &AstNode,
    ) -> Result<(Vec<String>, Option<String>), LangError> {
        let is_rest = |node: &AstNode| {
            self.ast
                .get_by_identity(&node.kind)
                .and_then(|s| s.pattern_role.as_deref())
                == Some("rest")
        };
        if !self.has_variadic_role(&params_node.kind) {
            let name = self.param_name(ast, params_node)?;
            return if is_rest(params_node) {
                Ok((Vec::new(), Some(name)))
            } else {
                Ok((vec![name], None))
            };
        }
        let children = params_node
            .payload
            .get("children")
            .and_then(|c| c.as_array())
            .ok_or_else(|| LangError::engine("closure: params missing children".to_string()))?;
        let mut names = Vec::with_capacity(children.len());
        let mut rest: Option<String> = None;
        for entry in children {
            let idx = entry.as_u64().ok_or_else(|| {
                LangError::engine("closure: param index must be a number".to_string())
            })? as usize;
            let child = ast.at(AstRef::new(idx))?;
            let name = self.param_name(ast, child)?;
            if is_rest(child) {
                if rest.is_some() {
                    return Err(LangError::engine(
                        "closure: multiple rest params".to_string(),
                    ));
                }
                rest = Some(name);
            } else {
                if rest.is_some() {
                    return Err(LangError::engine(
                        "closure: rest param must be last".to_string(),
                    ));
                }
                names.push(name);
            }
        }
        Ok((names, rest))
    }

    /// Whether a params node is an array-destructuring pattern.
    ///
    /// A positional parameter list (`(x, y) ~> body`) has no `pattern_role`
    /// on its params node, while an array pattern (`[x, y] ~> body`) uses a
    /// node whose `AstShapeDef` declares `pattern_role: "sequence"` and a
    /// variadic child role (e.g. `elements` for `array`). This check is
    /// data-driven over `AstShapeDef` metadata rather than a `kind == "array"`
    /// test.
    pub fn is_array_pattern(&self, params_node: &AstNode) -> bool {
        self.ast
            .get_by_identity(&params_node.kind)
            .map_or(false, |def| {
                def.pattern_role.as_deref() == Some("sequence")
                    && self.has_variadic_role(&params_node.kind)
            })
    }

    /// Extract the binding target name from a top-level binding node.
    ///
    /// A binding shape declares a `target` child role (e.g. `assign`)
    /// whose payload is a `var` or `type-annot` node. Some legacy
    /// binding forms (e.g. `bind`) carry the name directly in the payload
    /// under `name`; that is used as a fallback when no `target` role is
    /// declared. Returns `None` when the node is not a binding shape.
    ///
    /// This is the data-driven equivalent of a
    /// `root.kind == "assign"` check in module export collection.
    pub fn binding_target(&self, ast: &Ast, node: &AstNode) -> Option<String> {
        if let Ok(Some(target_idx)) = self.child_role_index(&node.kind, "target") {
            let children = node.payload.get("children").and_then(|c| c.as_array())?;
            let entry = children.get(target_idx)?;
            let idx = entry.as_u64()? as usize;
            let target_node = ast.at(AstRef::new(idx)).ok()?;
            return self.param_name(ast, target_node).ok();
        }
        node.payload
            .get("name")
            .and_then(|v| v.as_str())
            .map(String::from)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fragments::TypeRuleDef;
    use crate::fragments::ast_shape::{AstDesugarChild, AstDesugarCondition, AstDesugarRule};
    use crate::fragments::grammar::{AstShapeRef, GrammarPosition};
    use crate::fragments::{RewriteStep, TransformCondition, TransformRule};
    use crate::term::{ArrSource, Term};
    use plugin_engine::TermData;

    fn td(t: TermData) -> Term {
        t.to_term().expect("TermData -> Term")
    }

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
    fn token_classification_helpers_are_data_driven() {
        // A language whose token kinds use *noncanonical* ids still
        // classifies via `category`/`pair`/`doc`/`label` — this is the
        // genericity property ADR-0044 requires of host tooling.
        let mut lang = Language::new();
        lang.tokens
            .merge(
                TokenKindDef::new("tok::name")
                    .with_category("identifier")
                    .with_label("ident"),
            )
            .unwrap();
        lang.tokens
            .merge(
                TokenKindDef::new("tok::open")
                    .with_category("open-bracket")
                    .with_pair("tok::close"),
            )
            .unwrap();
        lang.tokens
            .merge(
                TokenKindDef::new("tok::close")
                    .with_category("close-bracket")
                    .with_pair("tok::open"),
            )
            .unwrap();
        lang.tokens
            .merge(
                TokenKindDef::new("tok::kw")
                    .with_category("keyword")
                    .with_doc("docs!"),
            )
            .unwrap();

        assert_eq!(lang.token_category("tok::name"), Some("identifier"));
        assert!(lang.token_in_category("tok::kw", "keyword"));
        assert!(!lang.token_in_category("tok::kw", "identifier"));
        assert_eq!(lang.token_pair("tok::open"), Some("tok::close"));
        assert_eq!(lang.token_pair("tok::close"), Some("tok::open"));
        assert_eq!(lang.token_doc("tok::kw"), Some("docs!"));
        assert_eq!(lang.token_kind_for_label("ident"), Some("tok::name"));
        assert_eq!(lang.token_category("tok::missing"), None);
        assert_eq!(lang.token_kind_for_label("missing"), None);
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
                td(TermData::op("add", vec![], &ArrSource::Native, None)),
            ))
            .unwrap();
        other
            .types
            .merge(TypeRuleDef::new(
                "t1",
                "lit",
                td(TermData::op("synth_child", vec![], &ArrSource::Judgment, None)),
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
                td(TermData::op("add", vec![], &ArrSource::Native, None)),
            ))
            .unwrap();
        // Set up the base to collide on the eval set.
        base.eval
            .merge(EvalSchemeDef::new(
                "e0",
                "binary.add",
                td(TermData::op("add", vec![], &ArrSource::Native, None)),
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
    fn transforms_for_sorts_by_priority() {
        let mut lang = Language::new();
        lang.transforms
            .merge(
                TransformDef::new("t.hi", "desugar", "x", TransformRule::Native("a".into()))
                    .with_priority(10),
            )
            .unwrap();
        lang.transforms
            .merge(
                TransformDef::new("t.lo", "desugar", "x", TransformRule::Native("b".into()))
                    .with_priority(-5),
            )
            .unwrap();
        lang.transforms
            .merge(TransformDef::new(
                "t.zero",
                "desugar",
                "x",
                TransformRule::Native("c".into()),
            ))
            .unwrap();
        // Other pass / other kind are not returned.
        lang.transforms
            .merge(TransformDef::new(
                "t.other",
                "lower",
                "x",
                TransformRule::Native("d".into()),
            ))
            .unwrap();
        lang.transforms
            .merge(TransformDef::new(
                "t.other2",
                "desugar",
                "y",
                TransformRule::Native("e".into()),
            ))
            .unwrap();

        let rules = lang.transforms_for("desugar", "x");
        let ids: Vec<&str> = rules.iter().map(|d| d.id.as_str()).collect();
        assert_eq!(ids, vec!["t.lo", "t.zero", "t.hi"]);
        assert!(lang.transforms_for("desugar", "nope").is_empty());
        assert!(lang.transforms_for("nope", "x").is_empty());
    }

    #[test]
    fn merge_ast_fragment_lowers_desugar_to_transform() {
        let mut lang = Language::new();
        let shape = AstShapeDef::new("ast.nullish", "nullish").with_desugar(AstDesugarRule {
            target_kind: "if".into(),
            children: vec![
                AstDesugarChild::Keep(0),
                AstDesugarChild::Create {
                    kind: "lit".into(),
                    payload: None,
                    children: vec![],
                },
            ],
            when: Some(AstDesugarCondition {
                child_index: 0,
                child_kind: "array".into(),
            }),
        });
        lang.merge_ast_fragment(shape).unwrap();

        let def = lang
            .transforms
            .get_by_id("transform.desugar.nullish")
            .expect("desugar rule lowered to a TransformDef");
        assert_eq!(def.pass, "desugar");
        assert_eq!(def.node_kind, "nullish");
        assert_eq!(def.priority, 0);
        assert_eq!(
            def.when,
            Some(TransformCondition::KindAt {
                index: Some(0),
                role: None,
                kind: "array".into()
            })
        );
        match &def.rule {
            TransformRule::Declarative {
                target_kind,
                children,
                payload,
            } => {
                assert_eq!(target_kind, "if");
                assert_eq!(*payload, None);
                assert_eq!(
                    *children,
                    vec![
                        RewriteStep::Keep(0),
                        RewriteStep::Create {
                            kind: "lit".into(),
                            payload: None,
                            children: vec![],
                        },
                    ]
                );
            }
            _ => panic!("expected Declarative rule"),
        }
        // Lookup path finds it.
        assert_eq!(lang.transforms_for("desugar", "nullish").len(), 1);
    }

    #[test]
    fn language_merge_lowers_desugar_too() {
        let mut base = Language::new();
        let mut other = Language::new();
        other
            .ast
            .merge(AstShapeDef::new("ast.x", "x").with_desugar(AstDesugarRule {
                target_kind: "y".into(),
                children: vec![AstDesugarChild::KeepRest(1)],
                when: None,
            }))
            .unwrap();
        base.merge(other).unwrap();
        let def = base.transforms.get_by_id("transform.desugar.x").unwrap();
        assert_eq!(def.pass, "desugar");
        assert!(def.when.is_none());
        match &def.rule {
            TransformRule::Declarative { children, .. } => {
                assert_eq!(*children, vec![RewriteStep::KeepRest(1)]);
            }
            _ => panic!("expected Declarative rule"),
        }
    }

    #[test]
    fn ast_union_drop_does_not_lower() {
        // A second shape declaring the same node_kind is a union no-op; its
        // desugar rule must be dropped with it.
        let mut lang = Language::new();
        lang.merge_ast_fragment(AstShapeDef::new("ast.x", "x").with_desugar(AstDesugarRule {
            target_kind: "y".into(),
            children: vec![],
            when: None,
        }))
        .unwrap();
        // Union-dropped duplicate — different id, same node_kind.
        lang.merge_ast_fragment(
            AstShapeDef::new("ast.x.dup", "x").with_desugar(AstDesugarRule {
                target_kind: "z".into(),
                children: vec![],
                when: None,
            }),
        )
        .unwrap();
        assert_eq!(lang.transforms.len(), 1);
        let def = lang.transforms.get_by_id("transform.desugar.x").unwrap();
        match &def.rule {
            TransformRule::Declarative { target_kind, .. } => assert_eq!(target_kind, "y"),
            _ => panic!("expected Declarative rule"),
        }
        // Re-merging the identical fragment stays idempotent — no collision.
        let again = lang.clone();
        lang.merge_ast_fragment(AstShapeDef::new("ast.x", "x").with_desugar(AstDesugarRule {
            target_kind: "y".into(),
            children: vec![],
            when: None,
        }))
        .unwrap();
        assert_eq!(lang, again);
    }

    #[test]
    fn ast_replace_updates_lowered_transform() {
        // Replacing a shape that carried a desugar rule replaces the
        // synthesized TransformDef instead of colliding.
        let mut lang = Language::new();
        lang.merge_ast_fragment(AstShapeDef::new("ast.x", "x").with_desugar(AstDesugarRule {
            target_kind: "y".into(),
            children: vec![],
            when: None,
        }))
        .unwrap();
        lang.merge_ast_fragment(
            AstShapeDef::new("ast.x2", "x")
                .with_replaces(vec!["ast.x".into()])
                .with_desugar(AstDesugarRule {
                    target_kind: "z".into(),
                    children: vec![],
                    when: None,
                }),
        )
        .unwrap();
        assert_eq!(lang.transforms.len(), 1);
        let def = lang.transforms.get_by_id("transform.desugar.x").unwrap();
        match &def.rule {
            TransformRule::Declarative { target_kind, .. } => assert_eq!(target_kind, "z"),
            _ => panic!("expected Declarative rule"),
        }

        // Replacing with a shape that drops `desugar` removes the stale rule.
        lang.merge_ast_fragment(
            AstShapeDef::new("ast.x3", "x").with_replaces(vec!["ast.x2".into()]),
        )
        .unwrap();
        assert!(lang.transforms.is_empty());
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
