//! Row polymorphism for effect rows (ADR-0076 OQ#1, production upgrade).
//!
//! The research PoC in `arrow-calculus-kernel-poc/src/type_level_effects.rs`
//! tracks effect rows with phantom types (`Nil` / `Cons<H, T>`) on a
//! `TypedGraph<Row>` wrapper. That is a *phantom-type simulation*: the row is
//! threaded by the smart constructors' return types, not computed by the type
//! system.
//!
//! This module upgrades that concept to a real (if not yet type-inferred) row
//! polymorphism layer over the production [`Term`](crate::term::Term)
//! kernel. An [`EffectRow`] is a set of operation names plus an optional
//! polymorphic tail; a [`TypedScheme`] pairs a `Term` with its inferred
//! [`EffectRow`]. The row records which capabilities a graph *manages* -- the
//! `Handle` targets appearing in the graph. After
//! [`Term::eliminate_handlers`](crate::term::Term::eliminate_handlers)
//! the row is empty -- a "clean" graph manages no capabilities and is safe to
//! normalize.
//!
//! # The capability-declaration interpretation
//!
//! The production `Term` has no dedicated `Op` node (unlike the research
//! PoC's `EffectGraph::Op` or the Lean mechanization's `op`). In those systems
//! an `Op(name)` *adds* `name` to the row and a `Handle` *removes* it (the
//! handler covers the op). The production `Term` has no `Op`, so there is
//! nothing for a `Handle` to remove -- instead, the `Handle` target itself is
//! the capability marker: a `Handle { body, target, impl_ }` *declares* that
//! `target` is a capability the graph manages (provides an interpretation
//! for). The effect row is the set of all `Handle` targets in the graph.
//!
//! This is the "capability declaration" reading: the row tells you which
//! capabilities the graph is managing. A graph with no `Handle` nodes has an
//! empty row -- everything in it is concrete. After `eliminate_handlers`
//! removes every `Handle` node, the row is empty by construction -- the graph
//! is clean (no capabilities managed, everything is concrete).
//!
//! # What this is and isn't
//!
//! This is **structural row tracking**, not full row-polymorphic type
//! inference. The [`EffectRow::tail`] field models the *shape* of a row
//! variable (an open row), but this module does not perform unification or
//! inference of row variables across bind sites -- that is the typechecker's
//! job (ADR-0054). What this module provides is the runtime data structure
//! and the structural inference pass that the typechecker and the module
//! pipeline can consult to reject programs with unhandled capabilities
//! before normalization.

use std::collections::BTreeSet;

use crate::term::Term;

/// An effect row: a set of operation names (the "labelled" part) plus an
/// optional polymorphic tail.
///
/// The row records which capabilities a [`Term`] graph manages. An empty
/// row (no `ops`, no `tail`) means the graph is clean -- it manages no
/// capabilities and is safe to normalize.
///
/// The `tail` models row polymorphism at the data level: `Some(name)` means
/// "this graph may manage additional capabilities bound to the row variable
/// `name`." This module does not infer tails -- it records them when a caller
/// (the typechecker) supplies them. Structural inference via
/// [`infer_effect_row`] always produces a closed row (`tail: None`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EffectRow {
    /// The known operations (the labelled part of the row): the capability
    /// names the graph manages.
    pub ops: BTreeSet<String>,
    /// The polymorphic tail: `None` for a closed row (exactly these ops),
    /// `Some(name)` for an open row (these ops plus any others bound to
    /// `name`). Structural inference produces closed rows; the typechecker
    /// may attach a tail when ascribing a polymorphic type.
    pub tail: Option<String>,
}

impl EffectRow {
    /// The empty (closed) row: no managed capabilities. A clean graph has
    /// an empty row.
    pub fn empty() -> Self {
        EffectRow {
            ops: BTreeSet::new(),
            tail: None,
        }
    }

    /// A closed row with a single managed operation.
    pub fn single(op: &str) -> Self {
        let mut ops = BTreeSet::new();
        ops.insert(op.to_string());
        EffectRow { ops, tail: None }
    }

    /// A closed row from an iterator of operation names.
    pub fn from_ops<I: IntoIterator<Item = String>>(ops: I) -> Self {
        EffectRow {
            ops: ops.into_iter().collect(),
            tail: None,
        }
    }

    /// Whether this row is empty (no managed capabilities, no open tail).
    /// A clean graph has an empty row.
    pub fn is_empty(&self) -> bool {
        self.ops.is_empty() && self.tail.is_none()
    }

    /// Whether `op` is in the labelled part of this row. An open row
    /// (`tail: Some(_)`) may still contain `op` in its unknown tail -- this
    /// method only reports the known labelled part.
    pub fn contains(&self, op: &str) -> bool {
        self.ops.contains(op)
    }

    /// Union this row with `other`. The labelled parts are merged. If either
    /// side has a tail, the result keeps a tail (preferring `self`'s tail
    /// when both have one -- a real row-unification pass would unify the two
    /// tail variables; this is not modelled here because rows are computed,
    /// not inferred).
    ///
    /// This is the row combination for sequential and choice composition:
    /// `f >>> g` manages everything `f` manages plus everything `g`
    /// manages.
    pub fn union(&self, other: &EffectRow) -> EffectRow {
        let mut ops = self.ops.clone();
        ops.extend(other.ops.iter().cloned());
        EffectRow {
            ops,
            tail: self.tail.clone().or_else(|| other.tail.clone()),
        }
    }

    /// Remove `op` from the labelled part of this row. This is the row
    /// transformation a handler performs on the body's row when the body
    /// itself tracks unhandled ops (the Lean/PoC semantics): `handle body
    /// with target = impl` *provides* `target`, removing it from the body's
    /// requirements.
    ///
    /// Removing an op that is not present is a no-op. The tail is preserved
    /// (an open row minus a labelled op is still open).
    pub fn remove(&self, op: &str) -> EffectRow {
        let mut ops = self.ops.clone();
        ops.remove(op);
        EffectRow {
            ops,
            tail: self.tail.clone(),
        }
    }

    /// Add `op` to the labelled part of this row. This is the row
    /// transformation a `Handle` performs in the capability-declaration
    /// interpretation: a `Handle { target, ... }` declares that `target` is
    /// a capability the graph manages.
    pub fn insert(&self, op: &str) -> EffectRow {
        let mut ops = self.ops.clone();
        ops.insert(op.to_string());
        EffectRow {
            ops,
            tail: self.tail.clone(),
        }
    }

    /// Attach a polymorphic tail to this row, marking it open. Used by the
    /// typechecker when ascribing a row-polymorphic type.
    pub fn with_tail(mut self, tail: impl Into<String>) -> Self {
        self.tail = Some(tail.into());
        self
    }
}

impl Default for EffectRow {
    fn default() -> Self {
        Self::empty()
    }
}

impl std::fmt::Display for EffectRow {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let labelled: Vec<&str> = self.ops.iter().map(String::as_str).collect();
        match &self.tail {
            None => write!(f, "{{{}}}", labelled.join(", ")),
            Some(t) => {
                if labelled.is_empty() {
                    write!(f, "{{{t}}}")
                } else {
                    write!(f, "{{{}, {t}}}", labelled.join(", "))
                }
            }
        }
    }
}

/// Infer the effect row of a [`Term`] by structural inspection.
///
/// The row is the set of capabilities the graph *manages* -- the `Handle`
/// targets appearing anywhere in the graph. A `Handle { body, target, impl_ }`
/// declares that `target` is a capability the graph provides an interpretation
/// for; that capability name is part of the graph's effect row. The body and
/// impl may themselves manage further capabilities (their own nested `Handle`
/// targets), which are unioned in.
///
/// This is the "capability declaration" reading adapted to the production
/// `Term`, which has no dedicated `Op` node (unlike the research PoC's
/// `EffectGraph::Op` or the Lean mechanization's `op`). In those systems an
/// `Op(name)` *adds* `name` to the row and a `Handle` *removes* it (the handler
/// covers the op). The production `Term` has no `Op`, so there is nothing
/// for a `Handle` to remove -- instead, the `Handle` target itself is the
/// capability marker: the row is the set of `Handle` targets. After
/// [`Term::eliminate_handlers`](crate::term::Term::eliminate_handlers)
/// every `Handle` node is gone, so the inferred row of the eliminated scheme
/// is empty by construction -- the graph is clean (no capabilities managed,
/// everything is concrete).
///
/// The rules:
///
/// - `Arr { .. }`: no effect. A concrete base arrow manages no capability.
/// - `Seq { fst, snd }`: the union of both children's rows.
/// - `First { inner }`, `Loop { body }`: the inner row (pass-through).
/// - `Choice { l, r }`: the union of both branches.
/// - `App { callee, args }`: the union of the callee's and every argument's
///   row.
/// - `Handle { body, target, impl_ }`: `target` is added to the row (this
///   handle manages the `target` capability), unioned with the body's and
///   impl's rows. The result is `{target} ∪ infer(body) ∪ infer(impl_)`.
pub fn infer_effect_row(scheme: &Term) -> EffectRow {
    match scheme {
        // Concrete base arrows manage no capability.
        Term::Arr { .. } => EffectRow::empty(),
        // Combinators: thread/union the children's rows.
        Term::Seq { fst, snd } => infer_effect_row(fst).union(&infer_effect_row(snd)),
        Term::First { inner } => infer_effect_row(inner),
        Term::Choice { l, r } => infer_effect_row(l).union(&infer_effect_row(r)),
        Term::Loop { body } => infer_effect_row(body),
        Term::App { callee, args } => {
            let mut row = infer_effect_row(callee);
            for a in args {
                row = row.union(&infer_effect_row(a));
            }
            row
        }
        // The handler site: `target` is a capability this graph manages, so
        // it is added to the row. The body and impl may manage further
        // capabilities (their own nested handles), which are unioned in.
        Term::Handle {
            body,
            target,
            impl_,
        } => {
            let body_row = infer_effect_row(body);
            let impl_row = infer_effect_row(impl_);
            body_row.union(&impl_row).insert(target)
        }
    }
}

/// A [`Term`] paired with its inferred [`EffectRow`].
///
/// The row is computed once at construction and cached alongside the scheme.
/// Use [`TypedScheme::is_clean`] to check whether the scheme manages no
/// capabilities (safe to normalize).
#[derive(Clone, Debug)]
pub struct TypedScheme {
    /// The underlying scheme graph.
    pub scheme: Term,
    /// The inferred effect row: which capabilities this scheme manages.
    pub row: EffectRow,
}

impl TypedScheme {
    /// Compute the effect row of a [`Term`] by inspecting its structure.
    /// See [`infer_effect_row`] for the rules.
    pub fn infer_row(scheme: &Term) -> EffectRow {
        infer_effect_row(scheme)
    }

    /// Wrap a [`Term`] with its structurally-inferred effect row.
    pub fn from_scheme(scheme: &Term) -> Self {
        let row = infer_effect_row(scheme);
        TypedScheme {
            scheme: scheme.clone(),
            row,
        }
    }

    /// Whether this scheme is clean (no managed capabilities, no open tail).
    /// A clean scheme is safe to normalize -- it is fully concrete.
    pub fn is_clean(&self) -> bool {
        self.row.is_empty()
    }
}

/// Errors raised by [`eliminate_and_check`] when a scheme still manages
/// capabilities after handler elimination.
#[derive(Debug, PartialEq, Eq)]
pub enum EffectRowError {
    /// The eliminated scheme still manages capabilities. `ops` is the set of
    /// capability names (Handle targets) that remain. After
    /// `eliminate_handlers` this should be empty by construction; a non-empty
    /// set indicates a graph that still contains `Handle` nodes -- i.e. a
    /// program with unhandled effects that were not eliminated.
    UnhandledOps {
        /// The set of capability names still managed after elimination.
        ops: BTreeSet<String>,
    },
}

impl std::fmt::Display for EffectRowError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EffectRowError::UnhandledOps { ops } => {
                let names: Vec<&str> = ops.iter().map(String::as_str).collect();
                write!(
                    f,
                    "unhandled capabilities remain after handler elimination: {{{}}}",
                    names.join(", ")
                )
            }
        }
    }
}

impl std::error::Error for EffectRowError {}

/// Eliminate every [`Term::Handle`] node in `scheme` and verify the result
/// is clean (no managed capabilities).
///
/// This is the compile-time safety check that closes ADR-0076 OQ#1 for the
/// real compiler: after handler elimination, the resulting graph must have
/// an empty effect row (no `Handle` nodes, no managed capabilities). If it
/// does not, the program still has unhandled effects -- a compile-time error
/// listing the remaining capability names is returned instead.
///
/// Because `eliminate_handlers` removes every `Handle` node, the inferred row
/// of the result is empty by construction -- this check is a belt-and-braces
/// verification that the elimination pass did not leave any capability
/// declaration behind. It is also the seam where a future, more general row
/// inference (one that can spot unhandled `arr(target)` references not covered
/// by any `Handle`) would surface a compile-time "unhandled capabilities"
/// error.
///
/// # Errors
///
/// Returns [`EffectRowError::UnhandledOps`] if the eliminated scheme's effect
/// row is not empty.
pub fn eliminate_and_check(scheme: &Term) -> Result<Term, EffectRowError> {
    let eliminated = scheme.eliminate_handlers();
    let row = infer_effect_row(&eliminated);
    if row.is_empty() {
        Ok(eliminated)
    } else {
        Err(EffectRowError::UnhandledOps { ops: row.ops })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: does this `Term` contain any `Handle` node?
    fn contains_handle(s: &Term) -> bool {
        match s {
            Term::Arr { args, .. } => args.iter().any(contains_handle),
            Term::Seq { fst, snd } => contains_handle(fst) || contains_handle(snd),
            Term::First { inner } => contains_handle(inner),
            Term::Choice { l, r } => contains_handle(l) || contains_handle(r),
            Term::Loop { body } => contains_handle(body),
            Term::App { callee, args } => {
                contains_handle(callee) || args.iter().any(contains_handle)
            }
            Term::Handle { .. } => true,
        }
    }

    // --- EffectRow basics -------------------------------------------------

    #[test]
    fn empty_row_is_empty() {
        let r = EffectRow::empty();
        assert!(r.is_empty());
        assert!(r.ops.is_empty());
        assert_eq!(r.tail, None);
    }

    #[test]
    fn single_row_contains_its_op() {
        let r = EffectRow::single("map");
        assert!(!r.is_empty());
        assert!(r.contains("map"));
        assert!(!r.contains("serialize"));
        assert_eq!(r.tail, None);
    }

    #[test]
    fn union_merges_ops() {
        let a = EffectRow::single("map");
        let b = EffectRow::single("serialize");
        let u = a.union(&b);
        assert!(u.contains("map"));
        assert!(u.contains("serialize"));
        assert_eq!(u.ops.len(), 2);
        assert_eq!(u.tail, None);
    }

    #[test]
    fn union_with_empty_is_identity() {
        let a = EffectRow::single("map");
        let u = a.union(&EffectRow::empty());
        assert_eq!(u, a);
    }

    #[test]
    fn remove_drops_op() {
        let r = EffectRow::single("map");
        let removed = r.remove("map");
        assert!(removed.is_empty());
        assert!(!removed.contains("map"));
    }

    #[test]
    fn remove_nonexistent_is_noop() {
        let r = EffectRow::single("map");
        let removed = r.remove("serialize");
        assert_eq!(removed, r);
    }

    #[test]
    fn insert_adds_op() {
        let r = EffectRow::empty();
        let inserted = r.insert("map");
        assert!(inserted.contains("map"));
        assert!(!inserted.is_empty());
    }

    #[test]
    fn insert_is_idempotent() {
        let r = EffectRow::single("map");
        let inserted = r.insert("map");
        assert_eq!(inserted.ops.len(), 1);
    }

    #[test]
    fn open_tail_makes_row_non_empty() {
        let r = EffectRow {
            ops: BTreeSet::new(),
            tail: Some("r".to_string()),
        };
        assert!(!r.is_empty());
    }

    #[test]
    fn union_keeps_open_tail() {
        let open = EffectRow {
            ops: BTreeSet::new(),
            tail: Some("r".to_string()),
        };
        let closed = EffectRow::single("map");
        let u = open.union(&closed);
        assert_eq!(u.tail, Some("r".to_string()));
        assert!(u.contains("map"));
    }

    #[test]
    fn display_closed_row() {
        let r = EffectRow::single("map");
        assert_eq!(format!("{r}"), "{map}");
    }

    #[test]
    fn display_open_row() {
        let r = EffectRow::single("map").with_tail("r");
        assert_eq!(format!("{r}"), "{map, r}");
    }

    // --- infer_effect_row -------------------------------------------------

    #[test]
    fn infer_row_of_arr_is_empty() {
        // A concrete base arrow manages no capability.
        let s = Term::arr_native("add", vec![Term::arr_native_lit("const", vec![], 1)]);
        assert!(infer_effect_row(&s).is_empty());
    }

    #[test]
    fn infer_row_of_foreign_arr_is_empty() {
        let s = Term::arr_foreign("fs.read", vec![]);
        assert!(infer_effect_row(&s).is_empty());
    }

    #[test]
    fn infer_row_of_handle_contains_target() {
        // handle(arr("map"), "map", impl) manages "map" -> row {map}.
        let s = Term::handle(
            Term::arr_native("map", vec![]),
            "map",
            Term::arr_native("add", vec![]),
        );
        let row = infer_effect_row(&s);
        assert!(row.contains("map"));
        assert!(!row.is_empty());
    }

    #[test]
    fn infer_row_of_seq_unions_children() {
        // seq(handle(..., "map", ...), handle(..., "serialize", ...))
        // -> row {map, serialize}
        let s = Term::seq(
            Term::handle(
                Term::arr_native("map", vec![]),
                "map",
                Term::arr_native("add", vec![]),
            ),
            Term::handle(
                Term::arr_native("serialize", vec![]),
                "serialize",
                Term::arr_native("to_json", vec![]),
            ),
        );
        let row = infer_effect_row(&s);
        assert!(row.contains("map"));
        assert!(row.contains("serialize"));
        assert_eq!(row.ops.len(), 2);
    }

    #[test]
    fn infer_row_of_handle_unions_body_and_impl() {
        // handle(body, "map", impl) where impl manages "serialize".
        // -> row {map, serialize}
        let s = Term::handle(
            Term::arr_native("map", vec![]),
            "map",
            Term::handle(
                Term::arr_native("serialize", vec![]),
                "serialize",
                Term::arr_native("to_json", vec![]),
            ),
        );
        let row = infer_effect_row(&s);
        assert!(row.contains("map"));
        assert!(row.contains("serialize"));
    }

    #[test]
    fn infer_row_of_first_threads_inner() {
        let s = Term::first(Term::handle(
            Term::arr_native("map", vec![]),
            "map",
            Term::arr_native("add", vec![]),
        ));
        let row = infer_effect_row(&s);
        assert!(row.contains("map"));
    }

    #[test]
    fn infer_row_of_choice_unions_branches() {
        let s = Term::choice(
            Term::handle(
                Term::arr_native("map", vec![]),
                "map",
                Term::arr_native("add", vec![]),
            ),
            Term::handle(
                Term::arr_native("serialize", vec![]),
                "serialize",
                Term::arr_native("to_json", vec![]),
            ),
        );
        let row = infer_effect_row(&s);
        assert!(row.contains("map"));
        assert!(row.contains("serialize"));
    }

    #[test]
    fn infer_row_of_loop_threads_body() {
        let s = Term::loop_feedback(Term::handle(
            Term::arr_native("map", vec![]),
            "map",
            Term::arr_native("add", vec![]),
        ));
        let row = infer_effect_row(&s);
        assert!(row.contains("map"));
    }

    #[test]
    fn infer_row_of_app_unions_callee_and_args() {
        let s = Term::app(
            Term::handle(
                Term::arr_native("map", vec![]),
                "map",
                Term::arr_native("add", vec![]),
            ),
            vec![Term::handle(
                Term::arr_native("serialize", vec![]),
                "serialize",
                Term::arr_native("to_json", vec![]),
            )],
        );
        let row = infer_effect_row(&s);
        assert!(row.contains("map"));
        assert!(row.contains("serialize"));
    }

    #[test]
    fn infer_row_of_nested_handles() {
        // handle(handle(arr("a"), "a", impl_a), "b", impl_b)
        // -> row {a, b}
        let s = Term::handle(
            Term::handle(
                Term::arr_native("a", vec![]),
                "a",
                Term::arr_native("impl_a", vec![]),
            ),
            "b",
            Term::arr_native("impl_b", vec![]),
        );
        let row = infer_effect_row(&s);
        assert!(row.contains("a"));
        assert!(row.contains("b"));
    }

    #[test]
    fn infer_row_of_no_handles_is_empty() {
        // A graph with no Handle nodes manages no capabilities.
        let s = Term::seq(
            Term::arr_native("add", vec![]),
            Term::first(Term::arr_foreign("fs.read", vec![])),
        );
        assert!(infer_effect_row(&s).is_empty());
    }

    // --- TypedScheme ------------------------------------------------------

    #[test]
    fn typed_scheme_from_scheme_infers_row() {
        let s = Term::handle(
            Term::arr_native("map", vec![]),
            "map",
            Term::arr_native("add", vec![]),
        );
        let ts = TypedScheme::from_scheme(&s);
        assert!(!ts.is_clean());
        assert!(ts.row.contains("map"));
    }

    #[test]
    fn typed_scheme_clean_when_no_handles() {
        let s = Term::seq(
            Term::arr_native("add", vec![]),
            Term::arr_native("id", vec![]),
        );
        let ts = TypedScheme::from_scheme(&s);
        assert!(ts.is_clean());
    }

    // --- eliminate_and_check ----------------------------------------------

    #[test]
    fn eliminate_and_check_clean_scheme_ok() {
        // A scheme with no handles is already clean.
        let s = Term::seq(
            Term::arr_native("add", vec![]),
            Term::arr_native("id", vec![]),
        );
        let eliminated = eliminate_and_check(&s).expect("clean scheme");
        assert!(!contains_handle(&eliminated));
        assert_eq!(eliminated, s);
    }

    #[test]
    fn eliminate_and_check_handle_becomes_clean() {
        // handle(arr(target), "target", add) -> add. Row empty after elim.
        let s = Term::handle(
            Term::arr_native("target", vec![]),
            "target",
            Term::arr_native("add", vec![]),
        );
        let eliminated = eliminate_and_check(&s).expect("clean after elimination");
        assert!(!contains_handle(&eliminated));
        assert_eq!(eliminated, Term::arr_native("add", vec![]));
    }

    #[test]
    fn eliminate_and_check_nested_handles_becomes_clean() {
        let s = Term::handle(
            Term::handle(
                Term::arr_native("a", vec![]),
                "a",
                Term::arr_native("impl_a", vec![]),
            ),
            "b",
            Term::arr_native("impl_b", vec![]),
        );
        let eliminated = eliminate_and_check(&s).expect("clean after elimination");
        assert!(!contains_handle(&eliminated));
        assert_eq!(eliminated, Term::arr_native("impl_a", vec![]));
    }

    #[test]
    fn eliminate_and_check_seq_of_handles_becomes_clean() {
        let s = Term::seq(
            Term::handle(
                Term::arr_native("map", vec![]),
                "map",
                Term::arr_native("add", vec![]),
            ),
            Term::handle(
                Term::arr_native("serialize", vec![]),
                "serialize",
                Term::arr_native("to_json", vec![]),
            ),
        );
        let eliminated = eliminate_and_check(&s).expect("clean after elimination");
        assert!(!contains_handle(&eliminated));
        assert!(infer_effect_row(&eliminated).is_empty());
    }

    #[test]
    fn eliminate_and_check_impl_with_handle_becomes_clean() {
        // handle(arr("map"), "map", handle(arr("serialize"), "serialize", impl))
        // -> impl (after eliminating both handles)
        let s = Term::handle(
            Term::arr_native("map", vec![]),
            "map",
            Term::handle(
                Term::arr_native("serialize", vec![]),
                "serialize",
                Term::arr_native("to_json", vec![]),
            ),
        );
        let eliminated = eliminate_and_check(&s).expect("clean after elimination");
        assert!(!contains_handle(&eliminated));
        assert!(infer_effect_row(&eliminated).is_empty());
    }

    // --- EffectRowError display -------------------------------------------

    #[test]
    fn effect_row_error_displays_ops() {
        let mut ops = BTreeSet::new();
        ops.insert("map".to_string());
        ops.insert("serialize".to_string());
        let err = EffectRowError::UnhandledOps { ops };
        let msg = format!("{err}");
        assert!(msg.contains("map"));
        assert!(msg.contains("serialize"));
        assert!(msg.contains("unhandled capabilities remain"));
    }
}
