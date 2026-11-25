//! The arrow-calculus `Term` kernel (ADR-0104b).
//!
//! `Term` is the arrow-calculus evaluation kernel. A `Term` is an
//! engine-agnostic description of *what* to evaluate, not *how*. Engines
//! (tree-walk, bytecode, cranelift) interpret schemes; the scheme itself is
//! pure data. Surface constructs are lowered to a small set of core
//! combinators. [`Term::desugar`] recursively expands any remaining derived
//! forms into this core set before interpretation.
//!
//! `Value` here is [`serde_json::Value`] — no new value type is invented.

use serde::{Deserialize, Serialize};
use serde_json::Value;

/// A side for a `Whisker` cell attachment.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum Side {
    /// The left side of a whisker.
    Left,
    /// The right side of a whisker.
    Right,
}

/// The arrow-calculus kernel: a small data-only combinator set.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum Term {
    /// Pure constant arrow (Sanada's `arr`).
    Arr {
        /// The dimension of this arrow (ADR-0119 §3, ADR-0120 Phase 3).
        ///
        /// The single dimension/grade slot shared with [`Term::Op`]:
        /// `Const(n)` is a numeric dimension (`~[n]~>`) and `Const("S")`
        /// is a *named* dimension (formerly a "grade").
        #[serde(default = "default_dim_value")]
        dim: Box<Term>,
        /// The constant value.
        value: Value,
    },
    /// Pure constant value (ADR-0104b).
    Const {
        /// The constant value.
        value: Value,
    },
    /// Named graded operation (Sanada's `op`).
    Op {
        /// The dimension of this arrow (ADR-0119 §3, ADR-0120 Phase 3).
        ///
        /// `dim` is the single dimension/grade slot: a literal `Const(n)` is
        /// a numeric dimension (`~[n]~>`) and a literal `Const("S")` is a
        /// *named* dimension — what the graded-effect surface called a
        /// "grade". Handler dispatch resolves the label via
        /// [`Term::dim_label`] so an op at dimension `S` reaches the
        /// handler covering `S`. This is distinct from
        /// [`ArrSource::Foreign`], which is the host-function boundary
        /// (a module-registry key), not a dimension.
        #[serde(default = "default_dim_value")]
        dim: Box<Term>,
        /// The operator name (e.g. `"add"`, `"proj_env"`).
        name: String,
        /// The argument sub-schemes feeding the op.
        args: Vec<Term>,
        /// Whether this is a native pure op or a foreign (host) call.
        source: ArrSource,
        /// An inline literal operand for ops that take a literal value
        /// rather than a sub-scheme (`proj_env`, `proj_child`).
        /// `None` for ordinary ops. Literal operands ride here so `args`
        /// stays a pure list of sub-schemes.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        lit: Option<Value>,
        /// Optional declarative op metadata (ADR-0173).
        ///
        /// `attrs` is node *identity* metadata: `(op, children, attrs)`
        /// is the e-node key wherever `Term` feeds an e-graph. The kernel
        /// keeps it untyped (`Option<Value>`); schemas are declared by
        /// `Language` fragment data (ADR-0044). Serialization of a term
        /// with `attrs: None` is byte-identical to the pre-attrs shape;
        /// old JSON parses with `attrs = None`.
        ///
        /// Reserved key [`OP_GRADE_ATTR`] (`"grade"`): when `attrs` is a
        /// JSON object, the `"grade"` entry carries a *graded arrow's*
        /// grade as a serialized [`Term`] (serde JSON, the same shape
        /// [`Term::quote`] consumers deserialize via
        /// `serde_json::from_value::<Term>`). This is the grade channel
        /// parallel to [`Term::Op::dim`]: `dim` stays the globular
        /// dimension index — consumed by `cell_boundary_`,
        /// `law_inference`, `quantified_laws`, and globular projection —
        /// while `attrs["grade"]` carries the `~[G]~>` grade payload, an
        /// arbitrary Handl data expression. See
        /// `host/project/design/graded-arrows.md` §9.5: ADR-0120 Phase 3
        /// unified grade and dimension into `Op.dim`; the graded-arrow
        /// surface splits them again — the grade must never enter `dim`
        /// (a grade would mint a bogus `Const "Addable"` dimension and
        /// misroute handler dispatch via [`Term::dim_label`]). Use
        /// [`Term::with_op_grade`] / [`Term::op_grade`] to write and read
        /// the channel.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        attrs: Option<Value>,
    },

    /// `>>>[k]` — composition along axis `k` (ADR-0120 Phase 2).
    ///
    /// `axis` is an ordinary expression position holding the composition
    /// axis: `>>>` is `>>>[0]` (sequential composition of 1-cells) and
    /// `>>>[k]` composes along the k-th globular axis. Nonzero `k`
    /// executes as a globular paste `∘ₖ` via `cell_comp_axis`, enforcing
    /// the boundary law `tgt_k(fst) = src_k(snd)`. The effective
    /// dimension is `max(declared, cell_dim(fst), cell_dim(snd))` —
    /// `Cell`/`__dim__` records (n-cells) and `dim_arrow` values paste at
    /// their own height; `k >= n` on plain values is a dimension error.
    Seq {
        /// The composition axis (`0` for ordinary `>>>`).
        #[serde(default = "default_axis_value")]
        axis: Box<Term>,
        /// The first arrow; its output feeds `snd`.
        fst: Box<Term>,
        /// The second arrow; fed by `fst`'s output.
        snd: Box<Term>,
    },

    /// `first` — fan-out: run `inner` on the first component of a pair,
    /// carry the second component through unchanged.
    First {
        /// The arrow to run on the first component.
        inner: Box<Term>,
    },

    /// `ArrowChoice` — route on `Either`.
    Choice {
        /// The arrow handling the `Left` case.
        l: Box<Term>,
        /// The arrow handling the `Right` case.
        r: Box<Term>,
    },

    /// `ArrowLoop` — feedback.
    Loop {
        /// The feedback body.
        body: Box<Term>,
    },

    /// `app` / `ArrowApply` — dynamic/higher-order arrow application.
    App {
        /// The callee arrow.
        callee: Box<Term>,
        /// The argument arrows.
        args: Vec<Term>,
    },

    /// Bounded iteration.
    Iter {
        /// The remaining iteration budget.
        fuel: Box<Term>,
        /// The predicate arrow `state -> bool`.
        predicate: Box<Term>,
        /// The step arrow `state -> state`.
        step: Box<Term>,
        /// The initial state.
        initial: Box<Term>,
    },

    /// Child projection by named role (ADR-0081).
    Child {
        /// The child role to project from the current AST node.
        role: String,
    },

    /// `handle body with target = impl_` (ADR-0076).
    Handle {
        /// The handler body.
        body: Box<Term>,
        /// The capability name being managed.
        target: String,
        /// The handler implementation.
        impl_: Box<Term>,
        /// Optional handler accumulator — the `acc` child role of
        /// `ast.handle` (data/ast.yaml). `None` for the accumulator-free
        /// form; old serialized payloads (no `acc` key) decode as `None`
        /// and `None` is skipped on serialize, keeping the pre-`acc`
        /// shape byte-identical.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        acc: Option<Box<Term>>,
    },

    /// `rewrite source ~> target` — a scheme rewrite step.
    Rewrite {
        /// The source arrow before rewriting.
        source: Box<Term>,
        /// The target arrow after rewriting.
        target: Box<Term>,
        /// Why the rewrite is sound.
        witness: RewriteWitness,
    },

    /// Source face of a 2-cell.
    Src {
        /// The 2-cell value.
        cell: Box<Term>,
    },

    /// Target face of a 2-cell.
    Tgt {
        /// The 2-cell value.
        cell: Box<Term>,
    },

    /// Record field projection.
    RecordProj {
        /// The record to project from.
        record: Box<Term>,
        /// The field name.
        field: String,
    },

    /// Record field update.
    RecordWith {
        /// The record to update.
        record: Box<Term>,
        /// The field name.
        field: String,
        /// The new value for the field.
        value: Box<Term>,
    },

    /// Tagged value wrapper.
    Tag {
        /// The tag name.
        tag: String,
        /// The inner value.
        value: Box<Term>,
    },

    /// Cobind over a grade and body.
    Cobind {
        /// The grade.
        grade: Box<Term>,
        /// The body.
        body: Box<Term>,
    },

    /// A term in open data form (ADR-0119 §7 fold, ADR-0120 Phase 5).
    ///
    /// `data` is an ADR-0103 tagged record `{"__tag__": <name>, ...}`
    /// whose `__tag__` names a *derived* operator — `Path`, `Equiv`,
    /// `Refine`, `CellId`, `Whisker`, `Univalence`, … — folded out of
    /// the closed `Term` vocabulary. The kernel carries the record
    /// opaquely (no structural interpretation); `TermData::from_term`
    /// reproduces `data` exactly, so tag-directed evaluators, models,
    /// and the law machinery see the same record the surface forms
    /// produce. [`TermData::to_term`] maps any unrecognised tag to this
    /// variant, making the `Term`/`TermData` conversion total.
    Opaque {
        /// The tagged record naming the derived operator and its fields.
        data: Value,
    },
}

/// Whether an `Op` is a native pure function or a foreign host call.
///
/// `Foreign(name)` is the **host-function boundary**: `name` is a
/// module-registry key (`modules.lookup`, `Instr::Ffi`, FFI/dlsym) and a
/// capability name (`capabilities::foreign_names`). It is *not* a
/// dimension — effect grades/dimensions live in `Op::dim` (ADR-0120
/// Phase 3); the graded-op lowering no longer emits `Foreign(grade)`.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum ArrSource {
    /// A native pure op.
    Native,
    /// A foreign (host) function call — capability-tracked.
    Foreign(String),
    /// A typecheck judgment op (ADR-0054).
    Judgment,
    /// A dynamic host dispatch op (ADR-0060).
    DynamicForeign,
}

/// A witness recording why a `Term::Rewrite` is sound.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum RewriteWitness {
    /// A declared law or rewrite rule by name from `Language` data.
    Named(String),
    /// A computed rewrite step.
    Compute,
    /// A hint produced during handler elimination.
    HandlerHint,
    /// A type or capability cast.
    Cast,
}

/// The reserved [`Term::Op::attrs`] key carrying a graded arrow's grade
/// term (see the `attrs` field docs): `attrs` must be a JSON object and
/// `attrs["grade"]` holds the grade [`Term`] in serde JSON form.
pub const OP_GRADE_ATTR: &str = "grade";

/// Default dimension for `Arr`/`Op` when not supplied (1).
fn default_dim_value() -> Box<Term> {
    Box::new(Term::Const {
        value: Value::from(1),
    })
}

/// Default composition axis for `Seq` when not supplied (0 — ordinary `>>>`).
fn default_axis_value() -> Box<Term> {
    Box::new(Term::Const {
        value: Value::from(0),
    })
}

impl Term {
    /// The default dimension (1) for `Arr`/`Op` when not supplied.
    pub fn default_dim() -> Box<Term> {
        default_dim_value()
    }

    /// The default composition axis (0) for `Seq` when not supplied.
    pub fn default_axis() -> Box<Term> {
        default_axis_value()
    }

    /// Whether this term is the default composition axis (literal `0`).
    pub fn is_default_axis(&self) -> bool {
        self.nat_literal() == Some(0)
    }

    /// Resolve this term as a natural-number literal, if it is one.
    ///
    /// Recognizes the literal positions used for dimension/axis slots:
    /// `Const n` and `Arr n` where `n` is a non-negative integer.
    /// Returns `None` for compound expressions (ops, apps, …).
    pub fn nat_literal(&self) -> Option<u64> {
        match self {
            Term::Const { value } | Term::Arr { value, .. } => value
                .as_u64()
                .or_else(|| value.as_i64().and_then(|n| u64::try_from(n).ok())),
            _ => None,
        }
    }

    /// Resolve this term as a *named* dimension label, if it is one
    /// (ADR-0120 Phase 3).
    ///
    /// A dimension term is an ordinary `Term`; the literal positions
    /// `Const "S"` and `Arr "S"` denote the named dimension `S` — the
    /// surface `~[S]~>` and, equivalently, what the graded-effect
    /// surface called a grade. Numeric literals and compound dimension
    /// expressions return `None`: they are unnamed dimensions, not
    /// handler-routing labels.
    pub fn dim_label(&self) -> Option<String> {
        match self {
            Term::Const { value } | Term::Arr { value, .. } => value.as_str().map(str::to_string),
            _ => None,
        }
    }

    /// The globular dimension of a term (ADR-0120 Phase 5): the `dim`
    /// slot when it is a numeric literal, otherwise a structural
    /// estimate through the combinators (a composite has the greatest
    /// dimension of its parts). Defaults to `1` — an ordinary 1-cell.
    ///
    /// This is the *declared* dimension — the static estimate that picks
    /// the sequential-vs-pasting `Seq` branch. At the value level the
    /// effective dimension also lifts to `cell_dim` of the evaluated
    /// operands, so a term declared dimension 2 can still produce and
    /// paste 3-cell (`Cell`/`__dim__`) values at axis 2.
    pub fn globular_dim(&self) -> u64 {
        if let Term::Arr { dim, .. } | Term::Op { dim, .. } = self {
            if let Some(d) = dim.nat_literal() {
                return d.max(1);
            }
        }
        match self {
            Term::Seq { fst, snd, .. } => fst.globular_dim().max(snd.globular_dim()),
            Term::First { inner } => inner.globular_dim(),
            Term::Choice { l, r } => l.globular_dim().max(r.globular_dim()),
            Term::Loop { body } | Term::Handle { body, .. } | Term::Cobind { body, .. } => {
                body.globular_dim()
            }
            Term::App { callee, .. } => callee.globular_dim(),
            Term::Iter { step, .. } => step.globular_dim(),
            Term::RecordProj { record, .. } | Term::RecordWith { record, .. } => {
                record.globular_dim()
            }
            Term::Tag { value, .. } => value.globular_dim(),
            Term::Src { cell } | Term::Tgt { cell } => cell.globular_dim(),
            Term::Rewrite { target, .. } => target.globular_dim(),
            _ => 1,
        }
    }

    /// Convenience constructor for a pure constant arrow.
    pub fn const_value(value: impl Into<Value>) -> Self {
        Term::Arr {
            dim: Self::default_dim(),
            value: value.into(),
        }
    }

    /// Convenience constructor for a pure constant value.
    pub fn constant(value: impl Into<Value>) -> Self {
        Term::Const {
            value: value.into(),
        }
    }

    /// Convenience constructor for a *named* dimension term (`Const "S"`).
    ///
    /// Used as the `dim` slot of `Arr`/`Op` when an arrow or operation
    /// lives at a named dimension — the unified grade/dimension slot
    /// (ADR-0120 Phase 3).
    pub fn named_dim(label: impl Into<String>) -> Self {
        Term::Const {
            value: Value::String(label.into()),
        }
    }

    /// Convenience constructor for a native `op` with no literal payload.
    pub fn op_native(name: impl Into<String>, args: Vec<Term>) -> Self {
        Term::Op {
            dim: Self::default_dim(),
            name: name.into(),
            args,
            source: ArrSource::Native,
            lit: None,
            attrs: None,
        }
    }

    /// Backward-compatible alias for [`Term::op_native`].
    pub fn arr_native(op: impl Into<String>, args: Vec<Term>) -> Self {
        let op = op.into();
        if op == "const" && args.is_empty() {
            Term::const_value(Value::Null)
        } else {
            Term::op_native(op, args)
        }
    }

    /// Convenience constructor for a native `op` at an explicit dimension.
    ///
    /// `dim` is an ordinary `Term` dimension slot — `Term::constant(n)` for
    /// a numeric dimension, [`Term::named_dim`] for a named dimension/grade
    /// (ADR-0120 Phase 3).
    pub fn op_native_dim(name: impl Into<String>, dim: Term, args: Vec<Term>) -> Self {
        Term::Op {
            dim: Box::new(dim),
            name: name.into(),
            args,
            source: ArrSource::Native,
            lit: None,
            attrs: None,
        }
    }

    /// Convenience constructor for a foreign `op`.
    pub fn op_foreign(name: impl Into<String>, args: Vec<Term>) -> Self {
        let name = name.into();
        Term::Op {
            dim: Self::default_dim(),
            name: name.clone(),
            args,
            source: ArrSource::Foreign(name),
            lit: None,
            attrs: None,
        }
    }

    /// Backward-compatible alias for [`Term::op_foreign`].
    pub fn arr_foreign(name: impl Into<String>, args: Vec<Term>) -> Self {
        Term::op_foreign(name, args)
    }

    /// Convenience constructor for a native `op` carrying a literal payload.
    pub fn op_native_lit(name: impl Into<String>, args: Vec<Term>, lit: impl Into<Value>) -> Self {
        Term::Op {
            dim: Self::default_dim(),
            name: name.into(),
            args,
            source: ArrSource::Native,
            lit: Some(lit.into()),
            attrs: None,
        }
    }

    /// Backward-compatible alias for [`Term::op_native_lit`].
    pub fn arr_native_lit(op: impl Into<String>, args: Vec<Term>, lit: impl Into<Value>) -> Self {
        let op = op.into();
        if op == "const" && args.is_empty() {
            Term::const_value(lit)
        } else {
            Term::op_native_lit(op, args, lit)
        }
    }

    /// Convenience constructor for a typecheck judgment `op` with no literal payload.
    pub fn op_judgment(name: impl Into<String>, args: Vec<Term>) -> Self {
        Term::Op {
            dim: Self::default_dim(),
            name: name.into(),
            args,
            source: ArrSource::Judgment,
            lit: None,
            attrs: None,
        }
    }

    /// Backward-compatible alias for [`Term::op_judgment`].
    pub fn arr_judgment(op: impl Into<String>, args: Vec<Term>) -> Self {
        Term::op_judgment(op, args)
    }

    /// Convenience constructor for a typecheck judgment `op` carrying a literal payload.
    pub fn op_judgment_lit(
        name: impl Into<String>,
        args: Vec<Term>,
        lit: impl Into<Value>,
    ) -> Self {
        Term::Op {
            dim: Self::default_dim(),
            name: name.into(),
            args,
            source: ArrSource::Judgment,
            lit: Some(lit.into()),
            attrs: None,
        }
    }

    /// Backward-compatible alias for [`Term::op_judgment_lit`].
    pub fn arr_judgment_lit(op: impl Into<String>, args: Vec<Term>, lit: impl Into<Value>) -> Self {
        Term::op_judgment_lit(op, args, lit)
    }

    /// Convenience constructor for a native `op` carrying declarative attrs (ADR-0173).
    ///
    /// `attrs` is untyped node-identity metadata — `(name, args, attrs)` is
    /// the e-node key. See [`Term::Op::attrs`].
    pub fn op_native_attrs(
        name: impl Into<String>,
        args: Vec<Term>,
        attrs: impl Into<Value>,
    ) -> Self {
        Term::Op {
            dim: Self::default_dim(),
            name: name.into(),
            args,
            source: ArrSource::Native,
            lit: None,
            attrs: Some(attrs.into()),
        }
    }

    /// Convenience constructor for a native `op` at an explicit dimension
    /// carrying declarative attrs (ADR-0173).
    pub fn op_native_dim_attrs(
        name: impl Into<String>,
        dim: Term,
        args: Vec<Term>,
        attrs: impl Into<Value>,
    ) -> Self {
        Term::Op {
            dim: Box::new(dim),
            name: name.into(),
            args,
            source: ArrSource::Native,
            lit: None,
            attrs: Some(attrs.into()),
        }
    }

    /// Convenience constructor for a foreign `op` carrying declarative attrs (ADR-0173).
    pub fn op_foreign_attrs(
        name: impl Into<String>,
        args: Vec<Term>,
        attrs: impl Into<Value>,
    ) -> Self {
        let name = name.into();
        Term::Op {
            dim: Self::default_dim(),
            name: name.clone(),
            args,
            source: ArrSource::Foreign(name),
            lit: None,
            attrs: Some(attrs.into()),
        }
    }

    /// Convenience constructor for a native `op` carrying both a literal
    /// payload and declarative attrs (ADR-0173).
    pub fn op_native_lit_attrs(
        name: impl Into<String>,
        args: Vec<Term>,
        lit: impl Into<Value>,
        attrs: impl Into<Value>,
    ) -> Self {
        Term::Op {
            dim: Self::default_dim(),
            name: name.into(),
            args,
            source: ArrSource::Native,
            lit: Some(lit.into()),
            attrs: Some(attrs.into()),
        }
    }

    /// Convenience constructor for a typecheck judgment `op` carrying
    /// declarative attrs (ADR-0173).
    pub fn op_judgment_attrs(
        name: impl Into<String>,
        args: Vec<Term>,
        attrs: impl Into<Value>,
    ) -> Self {
        Term::Op {
            dim: Self::default_dim(),
            name: name.into(),
            args,
            source: ArrSource::Judgment,
            lit: None,
            attrs: Some(attrs.into()),
        }
    }

    /// Convenience constructor for a typecheck judgment `op` carrying both
    /// a literal payload and declarative attrs (ADR-0173).
    pub fn op_judgment_lit_attrs(
        name: impl Into<String>,
        args: Vec<Term>,
        lit: impl Into<Value>,
        attrs: impl Into<Value>,
    ) -> Self {
        Term::Op {
            dim: Self::default_dim(),
            name: name.into(),
            args,
            source: ArrSource::Judgment,
            lit: Some(lit.into()),
            attrs: Some(attrs.into()),
        }
    }

    /// Set the declarative attrs slot on an `Op` term (ADR-0173).
    ///
    /// Returns `self` unchanged for non-`Op` terms.
    pub fn with_attrs(self, attrs: impl Into<Value>) -> Self {
        match self {
            Term::Op {
                dim,
                name,
                args,
                source,
                lit,
                ..
            } => Term::Op {
                dim,
                name,
                args,
                source,
                lit,
                attrs: Some(attrs.into()),
            },
            other => other,
        }
    }

    /// Attach a grade term to an `Op`'s grade channel — the reserved
    /// [`OP_GRADE_ATTR`] entry of `attrs` (graded arrows `~[G]~>`,
    /// `host/project/design/graded-arrows.md` §9.5).
    ///
    /// `grade` is stored as serde JSON inside the `attrs` object: when
    /// `attrs` is already an object its other keys are preserved; when it
    /// is `None` a fresh `{"grade": …}` object is created; a non-object
    /// `attrs` is replaced (the channel requires an object — non-object
    /// attrs cannot carry named keys). Returns `self` unchanged for
    /// non-`Op` terms. The grade term rides as *data* — like `attrs`
    /// generally it is not desugared, handler-eliminated, or instantiated
    /// by scheme machinery; populate it with an already-lowered `Term`.
    pub fn with_op_grade(self, grade: Term) -> Self {
        match self {
            Term::Op {
                dim,
                name,
                args,
                source,
                lit,
                attrs,
            } => {
                let grade_json =
                    serde_json::to_value(&grade).unwrap_or(Value::Null);
                let mut map = match attrs {
                    Some(Value::Object(map)) => map,
                    _ => serde_json::Map::new(),
                };
                map.insert(OP_GRADE_ATTR.to_string(), grade_json);
                Term::Op {
                    dim,
                    name,
                    args,
                    source,
                    lit,
                    attrs: Some(Value::Object(map)),
                }
            }
            other => other,
        }
    }

    /// Read an `Op`'s grade channel — the [`OP_GRADE_ATTR`] entry of
    /// `attrs` deserialized back into a [`Term`]. Returns `None` for
    /// non-`Op` terms, absent/malformed `attrs`, or a grade payload that
    /// does not deserialize as a `Term`.
    pub fn op_grade(&self) -> Option<Term> {
        match self {
            Term::Op {
                attrs: Some(attrs),
                ..
            } => attrs
                .get(OP_GRADE_ATTR)
                .and_then(|v| serde_json::from_value::<Term>(v.clone()).ok()),
            _ => None,
        }
    }

    /// Convenience constructor for `>>>` — `>>>[0]` sequential composition.
    pub fn seq(fst: Term, snd: Term) -> Self {
        Term::Seq {
            axis: Self::default_axis(),
            fst: Box::new(fst),
            snd: Box::new(snd),
        }
    }

    /// Convenience constructor for `>>>[k]` — composition along axis `k`.
    ///
    /// `axis` is an ordinary expression position (literal, variable, or
    /// compound term). Callers pass `Term::seq(f, g)` for `>>>[0]`.
    pub fn seq_axis(axis: Term, fst: Term, snd: Term) -> Self {
        Term::Seq {
            axis: Box::new(axis),
            fst: Box::new(fst),
            snd: Box::new(snd),
        }
    }

    /// Convenience constructor for `first`.
    pub fn first(inner: Term) -> Self {
        Term::First {
            inner: Box::new(inner),
        }
    }

    /// Convenience constructor for `ArrowChoice` routing.
    pub fn choice(l: Term, r: Term) -> Self {
        Term::Choice {
            l: Box::new(l),
            r: Box::new(r),
        }
    }

    /// Convenience constructor for `ArrowLoop` feedback.
    pub fn loop_feedback(body: Term) -> Self {
        Term::Loop {
            body: Box::new(body),
        }
    }

    /// Convenience constructor for `app` / `ArrowApply`.
    pub fn app(callee: Term, args: Vec<Term>) -> Self {
        Term::App {
            callee: Box::new(callee),
            args,
        }
    }

    /// Construct a `handle body with target = impl_` node (ADR-0076).
    pub fn handle(body: Term, target: impl Into<String>, impl_: Term) -> Self {
        Term::Handle {
            body: Box::new(body),
            target: target.into(),
            impl_: Box::new(impl_),
            acc: None,
        }
    }

    /// Construct a `handle body with target = impl_` node carrying a
    /// handler accumulator — the `acc` role of `ast.handle`.
    pub fn handle_acc(body: Term, target: impl Into<String>, impl_: Term, acc: Term) -> Self {
        Term::Handle {
            body: Box::new(body),
            target: target.into(),
            impl_: Box::new(impl_),
            acc: Some(Box::new(acc)),
        }
    }

    /// Recursively desugar derived surface forms into the core `Term` combinators.
    /// Recursively desugar derived surface forms into the core `Term` combinators.
    pub fn desugar(&self) -> Term {
        match self {
            // Core forms: preserve shape and desugar children.
            Term::Arr { dim, value } => Term::Arr {
                dim: Box::new(dim.desugar()),
                value: value.clone(),
            },
            Term::Const { value } => Term::Const {
                value: value.clone(),
            },
            Term::Op {
                dim,
                name,
                args,
                source,
                lit,
                attrs,
            } => Term::Op {
                dim: Box::new(dim.desugar()),
                name: name.clone(),
                args: args.iter().map(Term::desugar).collect(),
                source: source.clone(),
                lit: lit.clone(),
                attrs: attrs.clone(),
            },
            Term::Seq { axis, fst, snd } => Term::Seq {
                axis: Box::new(axis.desugar()),
                fst: Box::new(fst.desugar()),
                snd: Box::new(snd.desugar()),
            },
            Term::First { inner } => Term::First {
                inner: Box::new(inner.desugar()),
            },
            Term::Choice { l, r } => Term::Choice {
                l: Box::new(l.desugar()),
                r: Box::new(r.desugar()),
            },
            Term::Loop { body } => Term::Loop {
                body: Box::new(body.desugar()),
            },
            Term::App { callee, args } => Term::App {
                callee: Box::new(callee.desugar()),
                args: args.iter().map(Term::desugar).collect(),
            },
            Term::Iter {
                fuel,
                predicate,
                step,
                initial,
            } => Term::Iter {
                fuel: Box::new(fuel.desugar()),
                predicate: Box::new(predicate.desugar()),
                step: Box::new(step.desugar()),
                initial: Box::new(initial.desugar()),
            },
            Term::Child { role } => Term::Child { role: role.clone() },
            Term::Handle {
                body,
                target,
                impl_,
                acc,
            } => Term::Handle {
                body: Box::new(body.desugar()),
                target: target.clone(),
                impl_: Box::new(impl_.desugar()),
                acc: acc.as_ref().map(|a| Box::new(a.desugar())),
            },
            Term::Rewrite {
                source,
                target,
                witness,
            } => Term::Rewrite {
                source: Box::new(source.desugar()),
                target: Box::new(target.desugar()),
                witness: witness.clone(),
            },
            Term::Src { cell } => Term::Src {
                cell: Box::new(cell.desugar()),
            },
            Term::Tgt { cell } => Term::Tgt {
                cell: Box::new(cell.desugar()),
            },
            Term::RecordProj { record, field } => Term::RecordProj {
                record: Box::new(record.desugar()),
                field: field.clone(),
            },
            Term::RecordWith {
                record,
                field,
                value,
            } => Term::RecordWith {
                record: Box::new(record.desugar()),
                field: field.clone(),
                value: Box::new(value.desugar()),
            },
            Term::Tag { tag, value } => Term::Tag {
                tag: tag.clone(),
                value: Box::new(value.desugar()),
            },
            Term::Cobind { grade, body } => Term::Cobind {
                grade: Box::new(grade.desugar()),
                body: Box::new(body.desugar()),
            },
            // `Opaque` carries data-level fields (TermData records), not
            // `Term` structure — there is nothing to recursively desugar.
            Term::Opaque { data } => Term::Opaque { data: data.clone() },
        }
    }

    /// Eliminate every `Handle` node in this scheme.
    /// Eliminate every `Handle` node in this scheme.
    pub fn eliminate_handlers(&self) -> Term {
        match self {
            Term::Arr { dim, value } => Term::Arr {
                dim: Box::new(dim.eliminate_handlers()),
                value: value.clone(),
            },
            Term::Const { value } => Term::Const {
                value: value.clone(),
            },
            Term::Op {
                dim,
                name,
                args,
                source,
                lit,
                attrs,
            } => {
                let new_args: Vec<Term> = args.iter().map(|a| a.eliminate_handlers()).collect();
                Term::Op {
                    dim: Box::new(dim.eliminate_handlers()),
                    name: name.clone(),
                    args: new_args,
                    source: source.clone(),
                    lit: lit.clone(),
                    attrs: attrs.clone(),
                }
            }
            Term::Iter {
                fuel,
                predicate,
                step,
                initial,
            } => Term::Iter {
                fuel: Box::new(fuel.eliminate_handlers()),
                predicate: Box::new(predicate.eliminate_handlers()),
                step: Box::new(step.eliminate_handlers()),
                initial: Box::new(initial.eliminate_handlers()),
            },
            Term::Child { role } => Term::Child { role: role.clone() },
            Term::Seq { axis, fst, snd } => Term::Seq {
                axis: Box::new(axis.eliminate_handlers()),
                fst: Box::new(fst.eliminate_handlers()),
                snd: Box::new(snd.eliminate_handlers()),
            },
            Term::First { inner } => Term::First {
                inner: Box::new(inner.eliminate_handlers()),
            },
            Term::Choice { l, r } => Term::Choice {
                l: Box::new(l.eliminate_handlers()),
                r: Box::new(r.eliminate_handlers()),
            },
            Term::Loop { body } => Term::Loop {
                body: Box::new(body.eliminate_handlers()),
            },
            Term::App { callee, args } => {
                let new_args: Vec<Term> = args.iter().map(|a| a.eliminate_handlers()).collect();
                Term::App {
                    callee: Box::new(callee.eliminate_handlers()),
                    args: new_args,
                }
            }
            Term::Handle {
                body,
                target,
                impl_,
                ..
            } => {
                let elim_body = body.eliminate_handlers();
                let elim_impl = impl_.eliminate_handlers();
                substitute_capability(&elim_body, target, &elim_impl)
            }
            Term::Rewrite {
                source,
                target,
                witness,
            } => Term::Rewrite {
                source: Box::new(source.eliminate_handlers()),
                target: Box::new(target.eliminate_handlers()),
                witness: witness.clone(),
            },
            Term::Src { cell } => Term::Src {
                cell: Box::new(cell.eliminate_handlers()),
            },
            Term::Tgt { cell } => Term::Tgt {
                cell: Box::new(cell.eliminate_handlers()),
            },
            Term::RecordProj { record, field } => Term::RecordProj {
                record: Box::new(record.eliminate_handlers()),
                field: field.clone(),
            },
            Term::RecordWith {
                record,
                field,
                value,
            } => Term::RecordWith {
                record: Box::new(record.eliminate_handlers()),
                field: field.clone(),
                value: Box::new(value.eliminate_handlers()),
            },
            Term::Tag { tag, value } => Term::Tag {
                tag: tag.clone(),
                value: Box::new(value.eliminate_handlers()),
            },
            Term::Cobind { grade, body } => Term::Cobind {
                grade: Box::new(grade.eliminate_handlers()),
                body: Box::new(body.eliminate_handlers()),
            },
            // Data-form terms carry their fields as TermData records;
            // handler elimination does not descend into them.
            Term::Opaque { data } => Term::Opaque { data: data.clone() },
        }
    }
}

/// Substitute bare `arr(target)` references in `scheme` with `impl_`.
///
/// An `Op` is a reference to the handled boundary `target` when (a) its
/// `name` is `target`, (b) its host boundary `Foreign(n)` is `target`, or
/// (c) its `dim` resolves to the named dimension `target` (ADR-0120
/// Phase 3: `handle S with impl` substitutes every op *at dimension* `S`).
fn substitute_capability(scheme: &Term, target: &str, impl_: &Term) -> Term {
    match scheme {
        Term::Arr { dim, value } => Term::Arr {
            dim: Box::new(substitute_capability(dim, target, impl_)),
            value: value.clone(),
        },
        Term::Const { value } => Term::Const {
            value: value.clone(),
        },
        Term::Op {
            dim,
            name,
            args,
            source,
            lit,
            attrs,
        } => {
            if args.is_empty() && lit.is_none() {
                let at_target_dim = dim.dim_label().as_deref() == Some(target);
                match source {
                    _ if at_target_dim => return impl_.clone(),
                    ArrSource::Native if name == target => return impl_.clone(),
                    ArrSource::Foreign(n) if n == target => return impl_.clone(),
                    _ => {}
                }
            }
            let new_args: Vec<Term> = args
                .iter()
                .map(|a| substitute_capability(a, target, impl_))
                .collect();
            Term::Op {
                dim: Box::new(substitute_capability(dim, target, impl_)),
                name: name.clone(),
                args: new_args,
                source: source.clone(),
                lit: lit.clone(),
                attrs: attrs.clone(),
            }
        }
        Term::Seq { axis, fst, snd } => Term::Seq {
            axis: Box::new(substitute_capability(axis, target, impl_)),
            fst: Box::new(substitute_capability(fst, target, impl_)),
            snd: Box::new(substitute_capability(snd, target, impl_)),
        },
        Term::First { inner } => Term::First {
            inner: Box::new(substitute_capability(inner, target, impl_)),
        },
        Term::Choice { l, r } => Term::Choice {
            l: Box::new(substitute_capability(l, target, impl_)),
            r: Box::new(substitute_capability(r, target, impl_)),
        },
        Term::Loop { body } => Term::Loop {
            body: Box::new(substitute_capability(body, target, impl_)),
        },
        Term::App { callee, args } => {
            let new_args: Vec<Term> = args
                .iter()
                .map(|a| substitute_capability(a, target, impl_))
                .collect();
            Term::App {
                callee: Box::new(substitute_capability(callee, target, impl_)),
                args: new_args,
            }
        }
        Term::Iter {
            fuel,
            predicate,
            step,
            initial,
        } => Term::Iter {
            fuel: Box::new(substitute_capability(fuel, target, impl_)),
            predicate: Box::new(substitute_capability(predicate, target, impl_)),
            step: Box::new(substitute_capability(step, target, impl_)),
            initial: Box::new(substitute_capability(initial, target, impl_)),
        },
        Term::Child { role } => Term::Child { role: role.clone() },
        Term::Handle {
            body,
            target: t,
            impl_: i,
            acc,
        } => Term::Handle {
            body: Box::new(substitute_capability(body, target, impl_)),
            target: t.clone(),
            impl_: Box::new(substitute_capability(i, target, impl_)),
            acc: acc
                .as_ref()
                .map(|a| Box::new(substitute_capability(a, target, impl_))),
        },
        Term::Rewrite {
            source,
            target: t,
            witness,
        } => Term::Rewrite {
            source: Box::new(substitute_capability(source, target, impl_)),
            target: Box::new(substitute_capability(t, target, impl_)),
            witness: witness.clone(),
        },
        Term::Src { cell } => Term::Src {
            cell: Box::new(substitute_capability(cell, target, impl_)),
        },
        Term::Tgt { cell } => Term::Tgt {
            cell: Box::new(substitute_capability(cell, target, impl_)),
        },
        Term::RecordProj { record, field } => Term::RecordProj {
            record: Box::new(substitute_capability(record, target, impl_)),
            field: field.clone(),
        },
        Term::RecordWith {
            record,
            field,
            value,
        } => Term::RecordWith {
            record: Box::new(substitute_capability(record, target, impl_)),
            field: field.clone(),
            value: Box::new(substitute_capability(value, target, impl_)),
        },
        Term::Tag { tag, value } => Term::Tag {
            tag: tag.clone(),
            value: Box::new(substitute_capability(value, target, impl_)),
        },
        Term::Cobind { grade, body } => Term::Cobind {
            grade: Box::new(substitute_capability(grade, target, impl_)),
            body: Box::new(substitute_capability(body, target, impl_)),
        },
        // Data-form fields are TermData records, not `Term`s.
        Term::Opaque { data } => Term::Opaque { data: data.clone() },
    }
}

/// Eliminate all handlers in a scheme (free function version).
pub fn eliminate_all_handlers(scheme: &Term) -> Term {
    scheme.eliminate_handlers()
}

/// Eliminate handlers in a scheme (alias for compatibility).
pub fn eliminate_handler_in_scheme(scheme: &Term) -> Term {
    scheme.eliminate_handlers()
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::Value;

    #[test]
    fn const_value_roundtrips() {
        let s = Term::const_value(Value::from(42));
        let j = serde_json::to_string(&s).unwrap();
        let back: Term = serde_json::from_str(&j).unwrap();
        assert_eq!(s, back);
    }

    #[test]
    fn op_attrs_serde_contract() {
        // ADR-0173: `attrs: None` serializes byte-identically to the
        // pre-attrs shape, and old JSON (no `attrs` key) parses with
        // `attrs = None`.
        let t = Term::op_native("add", vec![Term::constant(1)]);
        let j = serde_json::to_string(&t).unwrap();
        assert!(!j.contains("attrs"), "None attrs must not serialize: {j}");
        let back: Term = serde_json::from_str(&j).unwrap();
        assert_eq!(t, back);

        // Old-shape JSON (no attrs key) parses.
        let old =
            r#"{"Op":{"dim":{"Const":{"value":1}},"name":"add","args":[],"source":"Native"}}"#;
        let t2: Term = serde_json::from_str(old).unwrap();
        assert!(matches!(t2, Term::Op { attrs: None, .. }));

        // A payload round-trips.
        let t3 = Term::op_native_attrs("tensor.conv", vec![], serde_json::json!({"k": 1}));
        let j3 = serde_json::to_string(&t3).unwrap();
        let back3: Term = serde_json::from_str(&j3).unwrap();
        assert_eq!(t3, back3);
    }

    #[test]
    fn op_grade_channel_roundtrips() {
        // The graded-arrow channel: `attrs["grade"]` carries a serialized
        // `Term`, `dim` stays the dimension slot untouched.
        let grade = Term::named_dim("Addable");
        let t = Term::op_native("f", vec![]).with_op_grade(grade.clone());
        assert_eq!(t.op_grade(), Some(grade));
        // `dim` is untouched — the grade never enters the dimension slot.
        assert_eq!(t.dim_label(), None);
        assert_eq!(t.globular_dim(), 1);

        // Serde round-trip preserves the channel (attrs is a `Value`).
        let j = serde_json::to_string(&t).unwrap();
        let back: Term = serde_json::from_str(&j).unwrap();
        assert_eq!(back.op_grade(), Some(Term::named_dim("Addable")));

        // Existing attrs keys survive `with_op_grade`.
        let t2 = Term::op_native_attrs("g", vec![], serde_json::json!({"k": 1}))
            .with_op_grade(Term::constant(2));
        let attrs = match &t2 {
            Term::Op { attrs: Some(a), .. } => a.clone(),
            _ => panic!("expected attrs"),
        };
        assert_eq!(attrs["k"], serde_json::json!(1));
        assert_eq!(t2.op_grade(), Some(Term::constant(2)));

        // Non-Op terms pass through unchanged.
        let c = Term::constant(1).with_op_grade(Term::constant(2));
        assert!(matches!(c, Term::Const { .. }));
        assert_eq!(c.op_grade(), None);
    }

    #[test]
    fn handle_acc_serde_contract() {
        // `acc: None` serializes byte-identically to the pre-acc shape,
        // and old JSON (no `acc` key) parses with `acc = None`.
        let t = Term::handle(Term::constant(1), "io", Term::constant(2));
        let j = serde_json::to_string(&t).unwrap();
        assert!(!j.contains("acc"), "None acc must not serialize: {j}");
        let old =
            r#"{"Handle":{"body":{"Const":{"value":1}},"target":"io","impl_":{"Const":{"value":2}}}}"#;
        let back: Term = serde_json::from_str(old).unwrap();
        assert_eq!(t, back);
        assert!(matches!(back, Term::Handle { acc: None, .. }));

        // An accumulator round-trips.
        let t2 = Term::handle_acc(Term::constant(1), "io", Term::constant(2), Term::constant(0));
        let j2 = serde_json::to_string(&t2).unwrap();
        let back2: Term = serde_json::from_str(&j2).unwrap();
        assert_eq!(t2, back2);
    }
}
