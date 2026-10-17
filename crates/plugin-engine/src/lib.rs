//! # plugin-engine
//!
//! Foundation types for pluggable interpretation and rewrite models.

pub mod term;
pub mod term_data;
pub mod term_interpreter;

pub use term::{
    ArrSource, RewriteWitness, Side, Term, eliminate_all_handlers, eliminate_handler_in_scheme,
};
pub use term_data::TermData;
pub use term_interpreter::interpret;

/// A reference to a node in an AST arena.
///
/// The real AST type lives in `handl-language` (`handl_language::AstRef`, a
/// `usize` newtype); `plugin-engine` cannot name that type without creating
/// a dependency cycle (`handl-language` already depends on `plugin-engine`
/// for [`Term`]), so the handle is exposed here as the bare arena index.
pub type AstRef = usize;

/// Placeholder marker for an AST node in [`ModelCtx`].
///
/// The concrete node type is `handl_language::AstNode`, which
/// `plugin-engine` cannot name without a dependency cycle. `Model` impls
/// cannot inspect it yet — it only keeps the reference alive. Node access
/// goes through [`AstView`] instead.
#[derive(Debug, Clone)]
pub struct AstNode;

/// A minimal, object-safe view over a language definition.
///
/// Implemented by `handl_language::Language` (in `handl-language`, which
/// already depends on `plugin-engine`, so no cycle is introduced).
/// [`Model`] impls use this to resolve AST child positions by named role
/// (ADR-0081) and to look up eval schemes / type rules by node kind —
/// never hardcoded `kind ==` checks.
pub trait LanguageView {
    /// Upcast for implementations that need the concrete language type.
    fn as_any(&self) -> &dyn std::any::Any;

    /// Resolve the child position of `role` within nodes of kind `kind`
    /// (ADR-0081). Returns `None` when the kind has no shape or no such
    /// role (positional fallback is then the caller's concern).
    ///
    /// The index is the shape's full-form position (all declared roles,
    /// optional included, occupy a slot). For kinds whose shape declares
    /// `optional` roles, prefer [`child_role_index_at`](Self::child_role_index_at).
    fn child_role_index(&self, kind: &str, role: &str) -> Option<usize>;

    /// Arity-aware role resolution (ADR-0081 optional-role extension):
    /// resolve `role` for a `kind` node that actually has `arity` children.
    ///
    /// Optional slots are filled in declaration order by
    /// `arity - (required count)`; a role whose optional slot is absent at
    /// this arity resolves to `None`. The default implementation ignores
    /// `arity` and delegates to [`child_role_index`](Self::child_role_index)
    /// — correct for shapes without optional roles.
    fn child_role_index_at(&self, kind: &str, role: &str, arity: usize) -> Option<usize> {
        let _ = arity;
        self.child_role_index(kind, role)
    }

    /// The eval scheme (`Term`) registered for `kind`, if any.
    fn eval_rule(&self, kind: &str) -> Option<&Term>;

    /// The type-rule synth scheme (`Term`) registered for `kind`, if any.
    fn type_rule(&self, kind: &str) -> Option<&Term>;

    /// The evaluated `op` declaration value for `name`, if any.
    ///
    /// An `op` value is a tagged record
    /// `{"__tag__": "op", "name": ..., "inputs": ..., "output": ...,
    /// "grade": ...}` where `grade` is the op's *named dimension* — the
    /// value-level spelling of `Op.dim` (ADR-0120 Phase 3).
    fn op_decl(&self, name: &str) -> Option<serde_json::Value>;

    /// The first `handler` value whose `grades` list contains `grade`, if any.
    ///
    /// `grade` is a *named dimension* label — the key is dimension-typed
    /// (ADR-0120 Phase 3). A handler value is a tagged record
    /// `{"__tag__": "Handler", "grades": [...], "impls": {...}}` whose
    /// `grades` list is the set of named dimensions it interprets.
    fn handler_for_grade(&self, grade: &str) -> Option<serde_json::Value>;

    /// The declared law `source ~> target` for `name`, if any.
    ///
    /// A law value is an object with `source` and `target` fields that
    /// serialize [`Term`] arrows.
    fn law(&self, name: &str) -> Option<serde_json::Value>;

    /// The declared rewrite rule `source ~> target` for `name`, if any.
    ///
    /// A rewrite value is an object with `source` and `target` fields that
    /// serialize [`Term`] arrows.
    fn rewrite_rule(&self, name: &str) -> Option<serde_json::Value>;
}

/// A minimal, object-safe view over an AST arena.
///
/// Implemented by `handl_language::Ast` (in `handl-language`). The real
/// node type cannot cross this boundary, so nodes are exposed through
/// accessors: [`node_kind`](AstView::node_kind) and
/// [`node_child`](AstView::node_child) (children ride in
/// `node.payload["children"]` as arena indices).
pub trait AstView {
    /// Upcast for implementations that need the concrete AST type.
    fn as_any(&self) -> &dyn std::any::Any;

    /// The kind string of the node at `r`, if `r` is in bounds.
    fn node_kind(&self, r: AstRef) -> Option<&str>;

    /// The arena ref of the child at position `index` of node `r`, if the
    /// node exists and has a child at that position.
    fn node_child(&self, r: AstRef, index: usize) -> Option<AstRef>;
}

/// Placeholder language error type for the `Model` skeleton.
#[derive(Debug, Clone, PartialEq)]
pub enum LangError {
    /// Feature not yet implemented.
    NotImplemented,
}

/// The result of a model-level rewrite attempt.
pub enum RewriteResult<T> {
    /// The source and target are equal, carrying the (shared) value.
    Equal(T),
    /// The source and target are not equal.
    NotEqual,
    /// Replace the source with the target.
    Replace,
    /// The rewrite is logically proved.
    Proved,
    /// The rewrite is compiled to a runtime form.
    Compiled,
    /// The rewrite produced a transformed target value.
    Rewritten(T),
    /// The rewrite is not supported by this model.
    Unsupported,
}

impl<T> RewriteResult<T> {
    /// Return the value carried by an `Equal` or `Rewritten` result.
    ///
    /// Panics for `NotEqual`, `Replace`, `Proved`, `Compiled`, and `Unsupported`.
    pub fn into_value(self) -> T {
        match self {
            RewriteResult::Equal(v) | RewriteResult::Rewritten(v) => v,
            _ => panic!("called `RewriteResult::into_value` on a result without a value"),
        }
    }
}

/// Context passed to `Model` methods.
pub struct ModelCtx<'a> {
    /// The full AST being processed, viewed through [`AstView`].
    pub ast: &'a dyn AstView,
    /// The language definition in scope, viewed through [`LanguageView`].
    pub lang: &'a dyn LanguageView,
    /// The current AST node (opaque marker — access it via `ast` instead).
    pub current_node: &'a AstNode,
    /// A reference to the current node.
    pub node_ref: AstRef,
    /// Runtime handler stack for the `"Handle"` / `"Op"` tag dynamic
    /// dispatch. The `"Handle"` tag pushes its evaluated implementation here
    /// for the duration of its body; the `"Op"` tag dispatch searches the
    /// stack innermost-last for a `{"__tag__": "Handler", "impls": {...}}`
    /// value providing the op name.
    pub handler_stack: Vec<serde_json::Value>,
}

impl ModelCtx<'_> {
    /// Push a handler value onto the handler stack.
    pub fn push_handler(&mut self, value: serde_json::Value) {
        self.handler_stack.push(value);
    }

    /// Pop the innermost handler value from the handler stack, if any.
    pub fn pop_handler(&mut self) -> Option<serde_json::Value> {
        self.handler_stack.pop()
    }
}

/// A pluggable model for interpreting and rewriting `Term` schemes.
pub trait Model {
    /// The value type the model produces and consumes.
    type Value;

    /// Run the model on a `Term` with the given incoming value.
    fn run(
        &self,
        term: &Term,
        incoming: Self::Value,
        ctx: &mut ModelCtx,
    ) -> Result<Self::Value, LangError>;

    /// Attempt to rewrite `source` into `target` under the given witness,
    /// using the provided `incoming` value.
    fn rewrite(
        &self,
        source: &Term,
        target: &Term,
        witness: &RewriteWitness,
        incoming: &Self::Value,
        ctx: &mut ModelCtx,
    ) -> Result<RewriteResult<Self::Value>, LangError>;
}

/// ADR-0103: identify `Term` variants that are HoTT-specific (type/proof
/// judgments) and should delegate to the type model, not the kernel.
///
/// These tags "leaked into the computational kernel" per the ADR. They
/// represent type-level semantics (paths, equivalences, cells, etc.) that
/// belong in `type_model.hnl`, not in the Rust execution engines.
///
/// As the ADR-0103 migration progresses, more tags move from the kernel
/// (Rust `ValueModel`) to the delegate model (Handl-authored `.hnl`).
/// This predicate is the boundary function used by [`CompositeModel`] to
/// decide which model handles each `Term`.
pub fn is_hott_tag(term: &Term) -> bool {
    // Thin wrapper: convert once to TermData and delegate to the data-driven
    // tag check (ADR-0103). The tag set (Path, Equiv, CellId, Src, Tgt,
    // CellCompV, Whisker, Univalence, Glue, Fibrant, JElim, Refine, Cobind,
    // Rewrite) is matched against the `"__tag__"` field by
    // [`TermData::is_hott_tag`].
    TermData::from_term(term).is_hott_tag()
}

/// A composite model that delegates specific `Term` tags to a delegate model
/// while using a primary model for all other tags.
///
/// This is the ADR-0103 Phase 4 infrastructure: HoTT-specific tags (Path, Equiv,
/// CellId, etc.) delegate to a Handl-authored model (data), while core
/// arrow-calculus tags stay in the Rust engine (bootstrap). As the migration
/// progresses, more tags move to the delegate model.
///
/// The `delegated_tags` predicate determines which `Term`s go to the
/// delegate. For `run`, the decision is based on the term itself. For
/// `rewrite`, the decision is based on the source or target — if either
/// is delegated, the entire rewrite goes to the delegate.
///
/// # Type parameters
///
/// - `M1` — the primary model (e.g. the Rust `ValueModel`).
/// - `M2` — the delegate model (e.g. `HandlModelAdapter`). Must share the
///   same `Value` type as `M1`.
pub struct CompositeModel<M1: Model, M2: Model<Value = M1::Value>> {
    primary: M1,
    delegate: M2,
    delegated_tags: fn(&Term) -> bool,
}

impl<M1: Model, M2: Model<Value = M1::Value>> CompositeModel<M1, M2> {
    /// Create a new composite model.
    ///
    /// - `primary` handles all tags that `delegated_tags` returns `false` for.
    /// - `delegate` handles all tags that `delegated_tags` returns `true` for.
    /// - `delegated_tags` is a function pointer (not a closure) so the
    ///   composite model remains `Sized` without a `Box`.
    pub fn new(primary: M1, delegate: M2, delegated_tags: fn(&Term) -> bool) -> Self {
        Self {
            primary,
            delegate,
            delegated_tags,
        }
    }
}

impl<M1: Model, M2: Model<Value = M1::Value>> Model for CompositeModel<M1, M2> {
    type Value = M1::Value;

    fn run(
        &self,
        term: &Term,
        incoming: Self::Value,
        ctx: &mut ModelCtx,
    ) -> Result<Self::Value, LangError> {
        if (self.delegated_tags)(term) {
            self.delegate.run(term, incoming, ctx)
        } else {
            self.primary.run(term, incoming, ctx)
        }
    }

    fn rewrite(
        &self,
        source: &Term,
        target: &Term,
        witness: &RewriteWitness,
        incoming: &Self::Value,
        ctx: &mut ModelCtx,
    ) -> Result<RewriteResult<Self::Value>, LangError> {
        if (self.delegated_tags)(source) || (self.delegated_tags)(target) {
            self.delegate
                .rewrite(source, target, witness, incoming, ctx)
        } else {
            self.primary.rewrite(source, target, witness, incoming, ctx)
        }
    }
}

// --- ADR-0103 continuation: data-driven model seam (TermData / Value) ---

/// A data-driven model that runs on [`TermData`] / `serde_json::Value` instead
/// of the `Term` enum (ADR-0103 continuation).
///
/// Parallels [`Model`] but operates on the tagged-record data representation,
/// avoiding the `Term` enum round-trip for Handl-authored models. The
/// `incoming` value is borrowed (data models do not own it) and `ctx` is
/// shared immutably — data models read `handler_stack` / `node_ref` rather
/// than mutating the context.
pub trait ModelData {
    /// Run the model on a `TermData` with the given incoming value.
    fn run_data(
        &self,
        term: &TermData,
        incoming: &serde_json::Value,
        ctx: &ModelCtx,
    ) -> Result<serde_json::Value, LangError>;
}

/// A composite [`ModelData`] that delegates specific `TermData` tags to a
/// delegate model while using a primary model for all other tags.
///
/// Data-driven counterpart of [`CompositeModel`]: `delegated_tags` decides
/// which `TermData` goes to the delegate (e.g. HoTT tags via
/// [`TermData::is_hott_tag`]); the rest go to the primary. Both models must
/// implement [`ModelData`].
///
/// # Type parameters
///
/// - `M1` — the primary model (e.g. `ModelDataAdapter<ValueModel>`).
/// - `M2` — the delegate model (e.g. a Handl-authored `ModelData`).
pub struct CompositeDataModel<M1: ModelData, M2: ModelData> {
    primary: M1,
    delegate: M2,
    delegated_tags: fn(&TermData) -> bool,
}

impl<M1: ModelData, M2: ModelData> CompositeDataModel<M1, M2> {
    /// Create a new data-driven composite model.
    ///
    /// - `primary` handles all tags that `delegated_tags` returns `false` for.
    /// - `delegate` handles all tags that `delegated_tags` returns `true` for.
    /// - `delegated_tags` is a function pointer (e.g.
    ///   [`TermData::is_hott_tag`]) so the composite stays `Sized` without a
    ///   `Box`.
    pub fn new(primary: M1, delegate: M2, delegated_tags: fn(&TermData) -> bool) -> Self {
        Self {
            primary,
            delegate,
            delegated_tags,
        }
    }
}

impl<M1: ModelData, M2: ModelData> ModelData for CompositeDataModel<M1, M2> {
    fn run_data(
        &self,
        term: &TermData,
        incoming: &serde_json::Value,
        ctx: &ModelCtx,
    ) -> Result<serde_json::Value, LangError> {
        if (self.delegated_tags)(term) {
            self.delegate.run_data(term, incoming, ctx)
        } else {
            self.primary.run_data(term, incoming, ctx)
        }
    }
}

/// Adapter that wraps a [`Model`] as a [`ModelData`], converting `TermData`
/// back to `Term` via [`TermData::to_term`].
///
/// This lets existing `Model` impls plug into the data-driven composite
/// ([`CompositeDataModel`]) without a separate `ModelData` implementation.
/// The incoming value is cloned and the context is rebuilt as a mutable copy
/// (data models only read `handler_stack` / `node_ref`, so the clone is
/// observationally invisible).
pub struct ModelDataAdapter<M: Model<Value = serde_json::Value>>(pub M);

impl<M: Model<Value = serde_json::Value>> ModelData for ModelDataAdapter<M> {
    fn run_data(
        &self,
        term: &TermData,
        incoming: &serde_json::Value,
        ctx: &ModelCtx,
    ) -> Result<serde_json::Value, LangError> {
        let term = term.to_term().map_err(|_| LangError::NotImplemented)?;
        let mut ctx = ModelCtx {
            ast: ctx.ast,
            lang: ctx.lang,
            current_node: ctx.current_node,
            node_ref: ctx.node_ref,
            handler_stack: ctx.handler_stack.clone(),
        };
        self.0.run(&term, incoming.clone(), &mut ctx)
    }
}
