//! # handl-language
//!
//! The `Language` data schema and staged `lex`/`parse`/`eval` dispatch
//! signatures for the HAndL platform (ADR-0044).
//!
//! A `Language` is pure serializable data — no Rust trait objects, closures,
//! or `Box<dyn Behavior>`. It is built by merging typed fragments into six
//! [`FragmentSet`]s and is `serde`-serializable end to end. Evaluation
//! semantics are expressed as [`Term`] combinators (a small, versioned
//! core); surface constructs are [`DesugarRule`]s that lower to that core.
//!
//! Phase 1 provides the data schema, the `Ast` arena, the `Term` combinator
//! set, desugar rules, staged dispatch signatures (returning
//! [`LangError::NotImplemented`]), scheme versioning, and capability
//! derivation. Engines, runtime, and migrations are later phases.

#![warn(missing_docs)]

/// The `Ast` arena and `AstRef` handle.
pub mod ast;
/// Capability set derivation.
pub mod capabilities;
/// Desugar rules.
pub mod desugar;
/// Dynamic handler law verification over the `Term` IR (ADR-0076 OQ#2).
pub mod dynamic_handlers;
/// Row polymorphism for effect rows (ADR-0076 OQ#1).
/// Error types.
pub mod error;
/// The `Fragment` trait.
pub mod fragment;
/// `FragmentSet<T>` merge with declared-override policy.
pub mod fragment_set;
/// Fragment type definitions.
pub mod fragments;
/// Free-variable substitution for arrow bodies (ADR-0106).
pub mod instantiate;
/// The `Language` struct.
pub mod language;
/// Structural law inference over the `Term` IR (ADR-0076 OQ#5).
pub mod law_inference;
/// Explicit `forall f g. lhs = rhs` quantified law syntax over the `Term`
/// IR (ADR-0076 OQ#4).
pub mod quantified_laws;
/// `Val → Ast` reification — the AST-surface half of `quote`
/// (phase-2 spec WS-G; metaprogram term materialization).
pub mod quote_ast;
/// Staged `lex`/`parse`/`eval` dispatch entry points.
pub mod staged;
/// The arrow-calculus `Term` kernel (ADR-0052).
pub mod term;
pub mod token_classes;
/// Proof verdicts for the partial-evaluator typechecker (ADR-0068).
pub mod verdict;
/// Term combinator versioning.
pub mod version;

pub use ast::{Ast, AstNode, AstRef, Span, subtree_name_candidates, subtree_var_names};
pub use capabilities::{capabilities, foreign_names, subset_of};
pub use desugar::{DesugarRule, desugar};
pub use dynamic_handlers::{
    DispatchError, RegistrationResult, RuntimeVerification, VerifiedImpl, VerifiedImplStore,
    dynamic_dispatch, verify_at_runtime, verify_at_runtime_with_builtin,
};
pub use error::LangError;
pub use fragment::Fragment;
pub use fragment_set::FragmentSet;
pub use fragments::{
    AstDesugarChild, AstDesugarCondition, AstDesugarRule, AstShapeDef, AstShapeRef, CapabilityDecl,
    ChildRoleSpec, ChildSeparator, DelimitedShape, EvalSchemeDef, GrammarPosition, GrammarRow,
    KeywordClause, LexerPattern, LexerRuleDef, LintCheck, LintFix, LintRuleDef, LiteralKind,
    LspDef, LspMatch, LspRule, OptionSchema, PAYLOAD_ATTR_OF, PairShape, PayloadExtractSpec,
    PayloadTokenSpec, RewriteStep, TokenKindDef, TokenStep, TransformCondition, TransformDef,
    TransformRule, TypeRuleDef,
};
pub use handl_calculus::{AstView, LanguageView, Model, ModelCtx, RewriteResult};
pub use instantiate::LIT_KIND;
pub use language::Language;
pub use law_inference::{
    InferredLaw, LawCheckResult, LawPattern, LawStatus, builtin_law_catalog, infer_laws, law_equal,
    normalize, uses_first,
};
pub use quantified_laws::{
    LawCheckResult as QuantifiedLawCheckResult, LawExpr, LawSubst, LawVar, QuantifiedLaw,
    builtin_quantified_laws, check_quantified_law, instantiate,
};
pub use quote_ast::{REIFY_LIT_KIND, reify_ast, reify_ast_value};
pub use term::{
    ArrSource, RewriteWitness, Side, Term, eliminate_all_handlers, eliminate_handler_in_scheme,
};
pub use token_classes::{
    TokenClasses, is_bool_kind, is_comment_kind, is_delimiter_kind, is_doc_comment_kind,
    is_identifier_kind, is_keyword_kind, is_null_kind, is_number_kind, is_operator_kind,
    is_string_kind, is_template_kind,
};

impl handl_calculus::AstView for Ast {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }

    fn node_kind(&self, r: handl_calculus::AstRef) -> Option<&str> {
        self.get(AstRef::new(r)).map(|n| n.kind.as_str())
    }

    fn node_child(
        &self,
        r: handl_calculus::AstRef,
        index: usize,
    ) -> Option<handl_calculus::AstRef> {
        let node = self.get(AstRef::new(r))?;
        node.payload
            .get("children")?
            .as_array()?
            .get(index)?
            .as_u64()
            .map(|i| i as usize)
    }
}

impl handl_calculus::LanguageView for Language {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }

    fn child_role_index(&self, kind: &str, role: &str) -> Option<usize> {
        self.child_role_index(kind, role).ok().flatten()
    }

    fn child_role_index_at(&self, kind: &str, role: &str, arity: usize) -> Option<usize> {
        self.ast
            .get_by_identity(kind)
            .and_then(|def| def.role_index_at(role, arity))
    }

    fn eval_rule(&self, kind: &str) -> Option<&Term> {
        self.eval.get_by_identity(kind).map(|def| &def.scheme)
    }

    fn type_rule(&self, kind: &str) -> Option<&Term> {
        self.types.get_by_identity(kind).map(|def| &def.synth)
    }

    fn op_decl(&self, name: &str) -> Option<Value> {
        self.op_decl(name)
    }

    fn handler_for_grade(&self, grade: &str) -> Option<Value> {
        self.handler_for_grade(grade)
    }

    fn law(&self, name: &str) -> Option<Value> {
        self.law(name)
    }

    fn rewrite_rule(&self, name: &str) -> Option<Value> {
        self.rewrite_rule(name)
    }
}
pub use staged::{Source, SpannedToken, Token, Tokens, ValueOut, eval, lex, parse, run};
pub use verdict::{Proof, Verdict};
pub use version::SchemeVersion;

/// The value type used throughout the crate: a re-export of `serde_json::Value`.
pub type Value = serde_json::Value;

/// The sentinel object key marking a [`Value`] as carrying a serialized
/// [`Language`] (ADR-0041: `Language` is a first-class value).
///
/// A language value is a JSON object `{"__language__": <serialized Language>}`.
/// The full [`Language`] data is embedded in the value — this is a genuine
/// first-class value, not a string handle into a registry. Use
/// [`language_value`] to construct one and [`as_language`] to extract it.
pub const LANGUAGE_VALUE_KEY: &str = "__language__";

/// Wrap a [`Language`] into a [`Value`] tagged so it can be recognized by
/// [`as_language`].
///
/// The entire [`Language`] is serialized into the value, so a handl program
/// can hold, pass, and store a `Language` as an ordinary value. The meta host
/// functions (`lex`/`parse`/`eval`/`run`/`compile`) accept such a value as
/// their first argument and operate on the embedded [`Language`] directly — no
/// string-handle registry lookup is required.
///
/// # Panics
///
/// Panics if `lang` fails to serialize (it is always serde-serializable).
pub fn language_value(lang: &Language) -> Value {
    let inner = serde_json::to_value(lang).expect("Language is serde-serializable");
    serde_json::json!({ LANGUAGE_VALUE_KEY: inner })
}

/// Extract a [`Language`] from a [`Value`] produced by [`language_value`].
///
/// Returns `None` if the value is not a tagged language value or cannot be
/// deserialized.
pub fn as_language(value: &Value) -> Option<Language> {
    value
        .get(LANGUAGE_VALUE_KEY)
        .and_then(|v| serde_json::from_value(v.clone()).ok())
}

/// Whether `value` is a tagged language value (produced by [`language_value`]).
pub fn is_language_value(value: &Value) -> bool {
    value.get(LANGUAGE_VALUE_KEY).is_some()
}

/// The sentinel object key marking a [`Value`] as carrying a serialized
/// [`Ast`] subtree — an unevaluated expression (ADR-0041 §6, ADR-0045).
///
/// A vau-bound unevaluated child is a JSON object
/// `{"__ast__": <serialized Ast>}`. The embedded [`Ast`] is the subtree
/// rooted at the child (the child node plus all transitively-referenced
/// descendants, reindexed into a standalone arena), so the meta `eval`
/// host function can consume it directly: `eval(self, ast_value)`. Use
/// [`ast_value`] to construct one and [`as_ast`] to extract it.
pub const AST_VALUE_KEY: &str = "__ast__";

/// Wrap an [`Ast`] into a [`Value`] tagged so it can be recognized by
/// [`as_ast`].
///
/// The entire [`Ast`] is serialized into the value, so a handl program can
/// hold and pass an unevaluated expression as an ordinary value. The meta
/// `eval` host function accepts such a value as its second argument.
///
/// # Panics
///
/// Panics if `ast` fails to serialize (it is always serde-serializable).
pub fn ast_value(ast: &Ast) -> Value {
    let inner = serde_json::to_value(ast).expect("Ast is serde-serializable");
    serde_json::json!({ AST_VALUE_KEY: inner })
}

/// Extract an [`Ast`] from a [`Value`] produced by [`ast_value`].
///
/// Returns `None` if the value is not a tagged ast value or cannot be
/// deserialized.
pub fn as_ast(value: &Value) -> Option<Ast> {
    value
        .get(AST_VALUE_KEY)
        .and_then(|v| serde_json::from_value(v.clone()).ok())
}

/// Whether `value` is a tagged ast value (produced by [`ast_value`]).
pub fn is_ast_value(value: &Value) -> bool {
    value.get(AST_VALUE_KEY).is_some()
}

/// The sentinel object key marking a [`Value`] as a **tagged value**
/// (ADR-0055 — Tagged Values).
///
/// A tagged value is a JSON object `{"__tag__": <tag_name>, ...payload}`
/// minted by the host `tag` capability. The `__tag__` key is **reserved**:
/// user-constructed object literals cannot produce a `__tag__` key (the eval
/// engines reject it), so the only way a value acquires a `__tag__` key is
/// through the host `tag.tag` host function. This is the forgery-prevention
/// mechanism — tagging is a host capability, not a user-constructible
/// convention (ADR-0055 §3). Use [`tag_value`] to construct one, [`as_tag`] to
/// read its tag name, and [`is_tag_value`] to test for it.
pub const TAG_VALUE_KEY: &str = "__tag__";

/// The sentinel object key marking a [`Value`] as carrying the **host type
/// registry** identity of a type value (ADR-0054 — Generic Typecheck Engine).
///
/// A type value minted by a host type registry is a JSON object
/// `{"__tag__": <tag_name>, "__registry__": <registry_id>, ...payload}`.
/// The `__registry__` key records which registry minted the type value, so
/// equality and matching can be scoped to a single registry (ADR-0054
/// §"construct"). Like `__tag__`, this key is **reserved**: user object
/// literals cannot produce it, so a type value's registry identity is
/// unforgeable.
pub const REGISTRY_VALUE_KEY: &str = "__registry__";

/// Mint a tagged value (ADR-0055).
///
/// Returns `{"__tag__": tag_name, ...payload}`. The `payload` object's fields
/// become the tagged value's payload. If `payload` is `Null`, an empty
/// payload is used. If `payload` is a non-object, non-null value (e.g. a
/// number or string), it is wrapped in `{value: payload}` so that
/// `tag.tag("ok", 42)` produces `{"__tag__": "ok", "value": 42}` (ADR-0077).
/// Returns `None` if `payload` already contains a `__tag__` key — a minted
/// value cannot be re-tagged through the payload (the host `tag` op always
/// sets the tag; the payload must not smuggle one in).
///
/// This is the host-side minting primitive; user code reaches it via the
/// `tag.tag` host function exposed by `plugin-lib-tag`.
pub fn tag_value(tag_name: &str, payload: &Value) -> Option<Value> {
    let mut obj = match payload {
        Value::Object(map) => map.clone(),
        Value::Null => serde_json::Map::new(),
        _ => {
            let mut m = serde_json::Map::new();
            m.insert("value".to_string(), payload.clone());
            m
        }
    };
    if obj.contains_key(TAG_VALUE_KEY) {
        return None;
    }
    obj.insert(TAG_VALUE_KEY.to_string(), Value::from(tag_name));
    Some(Value::Object(obj))
}

/// Read the tag name of a tagged value (ADR-0055).
///
/// Returns `Some(name)` if `value` is a tagged value (an object containing a
/// string `__tag__` key), else `None`. Only values minted by [`tag_value`]
/// (the host `tag` capability) carry a `__tag__` key — user object literals
/// cannot forge one (the engines reserve the key).
pub fn as_tag(value: &Value) -> Option<&str> {
    value.get(TAG_VALUE_KEY).and_then(|v| v.as_str())
}

/// Whether `value` is a tagged value (produced by [`tag_value`]).
pub fn is_tag_value(value: &Value) -> bool {
    value.get(TAG_VALUE_KEY).and_then(|v| v.as_str()).is_some()
}

/// Whether `key` is a reserved value-level key that user-constructed object
/// literals must not produce (ADR-0055 §"Negative — A reserved key").
///
/// The reserved keys are the double-underscore-prefixed host sentinels:
/// `__tag__` (ADR-0055), `__registry__` (ADR-0054 — host type registry
/// identity), `__language__` (ADR-0041), `__ast__` (ADR-0041 §6), and
/// `__arrow__` (ADR-0052/ADR-0106 self-contained arrow values), and
/// `__compiled__` (ADR-0047 §3 compiled-program handles into the
/// process-local `COMPILED_REGISTRY`). These are minted by host primitives
/// (`tag_value`, the host type registry `construct` op, `language_value`,
/// `ast_value`, the `closure` op, the `.hnl` module loader,
/// `compiled_value`), never by user object literals. The eval engines
/// call this to reject such keys at object-construction time, making the
/// sentinels unforgeable.
pub fn is_reserved_value_key(key: &str) -> bool {
    matches!(
        key,
        TAG_VALUE_KEY
            | REGISTRY_VALUE_KEY
            | LANGUAGE_VALUE_KEY
            | AST_VALUE_KEY
            | "__arrow__"
            | "__compiled__"
    )
}

#[cfg(test)]
mod lib_value_test;
