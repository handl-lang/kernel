//! ADR-0103 Phase 6: `TermData` — the data representation of `Term`.
//!
//! `TermData` is a newtype around `serde_json::Value` representing a `Term`
//! as a tagged JSON record. Each `Term` variant becomes an object with a
//! `__tag__` field and one field per variant payload:
//!
//! ```json
//! {"__tag__": "Arr", "value": 5}
//! {"__tag__": "Seq", "fst": {...}, "snd": {...}}
//! {"__tag__": "Op", "name": "add", "args": [...], "source": "Native", "lit": null}
//! ```
//!
//! This is the target representation per ADR-0103: the `Term` enum disappears,
//! replaced by `serde_json::Value` (tagged records). The existing `Term` enum
//! stays as the bootstrap representation; `TermData` is the data target.
//!
//! ## Conversion
//!
//! [`TermData::from_term`] converts a `Term` to `TermData`.
//! [`TermData::to_term`] converts back (for bootstrap compatibility).
//! The conversion is lossless for every variant of the kernel vocabulary.
//!
//! ## Why not serde?
//!
//! The `Term` enum derives `Serialize`/`Deserialize`, but serde's default
//! (externally tagged) representation (`{"Arr": {"value": 5}}`) does **not**
//! match the ADR-0103 tagged-record shape (`{"__tag__": "Arr", "value": 5}`).
//! The tagged-record shape is what Handl-authored models consume (see
//! `plugin_lib_handl::model::term_to_value`), so `TermData` uses that shape
//! directly. The conversion is implemented manually to stay lossless and to
//! keep the JSON shape stable independent of serde's enum representation.

use serde_json::{Value, json};

use crate::term::{ArrSource, RewriteWitness, Side, Term};

/// A `Term` represented as a tagged JSON record (ADR-0103 Phase 6).
///
/// This is the data representation that will replace the `Term` enum. Each
/// `Term` variant becomes a JSON object with a `__tag__` field and one field
/// per variant payload. The representation is serializable, resumable, and
/// model-interpretable — the key properties ADR-0103 requires.
///
/// Construct a `TermData` with the per-variant constructors ([`TermData::arr`],
/// [`TermData::seq`], …) or convert an existing `Term` with
/// [`TermData::from_term`]. Inspect the tag with [`TermData::tag`] and access
/// fields with [`TermData::get`] / [`TermData::get_term`] / [`TermData::get_str`]
/// / [`TermData::get_term_list`].
#[derive(Debug, Clone, PartialEq)]
pub struct TermData(pub Value);

impl TermData {
    // --- Tag access ---

    /// The tag string (e.g. `"Arr"`, `"Seq"`, `"Op"`).
    ///
    /// Returns the empty string if the inner value is not a tagged record.
    pub fn tag(&self) -> &str {
        self.0.get("__tag__").and_then(|v| v.as_str()).unwrap_or("")
    }

    /// Whether this `TermData` has the given tag.
    pub fn is_tag(&self, tag: &str) -> bool {
        self.tag() == tag
    }

    /// Whether this `TermData` carries a HoTT-specific tag (ADR-0103).
    ///
    /// Data-driven counterpart of `plugin_engine::is_hott_tag(&Term)`: the
    /// same tag set (Path, Equiv, CellId, Src, Tgt, CellCompV, Whisker,
    /// Univalence, Glue, Fibrant, JElim, Refine, Cobind, Rewrite) is matched
    /// against the `"__tag__"` field instead of the `Term` enum.
    pub fn is_hott_tag(&self) -> bool {
        matches!(
            self.tag(),
            "Path"
                | "Equiv"
                | "CellId"
                | "Src"
                | "Tgt"
                | "CellCompV"
                | "Whisker"
                | "Univalence"
                | "Glue"
                | "Fibrant"
                | "JElim"
                | "Refine"
                | "Cobind"
                | "Rewrite"
        )
    }

    // --- Field access ---

    /// Get a field by name.
    pub fn get(&self, field: &str) -> Option<&Value> {
        self.0.get(field)
    }

    /// Get a field as a `TermData` (for nested terms).
    pub fn get_term(&self, field: &str) -> Option<TermData> {
        self.0.get(field).map(|v| TermData(v.clone()))
    }

    /// Get a field as a string.
    pub fn get_str(&self, field: &str) -> Option<&str> {
        self.0.get(field).and_then(|v| v.as_str())
    }

    /// Get a field as a list of `TermData`.
    pub fn get_term_list(&self, field: &str) -> Vec<TermData> {
        self.0
            .get(field)
            .and_then(|v| v.as_array())
            .map(|arr| arr.iter().map(|v| TermData(v.clone())).collect())
            .unwrap_or_default()
    }

    /// Resolve this record as a natural-number literal (`Const n` / `Arr n`),
    /// matching [`Term::nat_literal`]. Used for `Seq` axis slots.
    pub fn nat_literal(&self) -> Option<u64> {
        let value = self.0.get("value")?;
        if !matches!(self.tag(), "Const" | "Arr") {
            return None;
        }
        value
            .as_u64()
            .or_else(|| value.as_i64().and_then(|n| u64::try_from(n).ok()))
    }

    /// The `axis` slot of a `Seq` record as a `TermData`, defaulting to the
    /// `Const 0` record when the field is absent (pre-Phase-2 records).
    pub fn axis(&self) -> TermData {
        self.get_term("axis")
            .unwrap_or_else(|| TermData(json!({"__tag__": "Const", "value": 0})))
    }

    /// The `dim` slot of an `Arr`/`Op` record as a `TermData`, defaulting
    /// to the `Const 1` record when the field is absent (pre-ADR-0119
    /// records). `dim` is the single dimension/grade slot (ADR-0120
    /// Phase 3): a numeric literal is a numeric dimension and a string
    /// literal is a *named* dimension — the handler-routing label that
    /// the graded-effect surface called a "grade".
    pub fn dim(&self) -> TermData {
        self.get_term("dim")
            .unwrap_or_else(|| TermData(json!({"__tag__": "Const", "value": 1})))
    }

    /// Resolve this record as a *named* dimension label (ADR-0120
    /// Phase 3), matching [`Term::dim_label`]: `Const "S"` / `Arr "S"`
    /// denote the named dimension `S`. Numeric literals and compound
    /// dimension expressions return `None` — unnamed dimensions carry
    /// no handler-routing label. Call on a `dim` slot obtained via
    /// [`TermData::dim`] (e.g. `op_td.dim().dim_label()`).
    pub fn dim_label(&self) -> Option<String> {
        match self.tag() {
            "Const" | "Arr" => self
                .0
                .get("value")
                .and_then(|v| v.as_str())
                .map(str::to_string),
            _ => None,
        }
    }

    /// For an `Op` term, parse the `source` field back into an [`ArrSource`].
    ///
    /// Returns `None` when the `source` field is absent or malformed (which
    /// only happens for a non-`Op` `TermData` or a corrupt record).
    pub fn arr_source(&self) -> Option<ArrSource> {
        value_to_arr_source(self.0.get("source")).ok()
    }

    /// The globular dimension of a term (ADR-0120 Phase 5): the `dim` slot
    /// when it is a numeric literal, otherwise a structural estimate
    /// through the combinators (a composite has the greatest dimension of
    /// its parts). Defaults to `1` — an ordinary 1-cell.
    ///
    /// This is the *declared* dimension — the static estimate that picks
    /// the sequential-vs-pasting `Seq` branch. At the value level the
    /// effective dimension also lifts to `cell_dim` of the evaluated
    /// operands, so a term declared dimension 2 can still produce and
    /// paste 3-cell (`Cell`/`__dim__`) values at axis 2.
    pub fn globular_dim(&self) -> u64 {
        // `TermData::dim` supplies a `Const 1` default when the slot is
        // absent — check the raw field so structural terms (Seq, Tag, …)
        // fall through to the composite estimate below.
        if let Some(dim_td) = self.get_term("dim") {
            if let Some(d) = dim_td.nat_literal() {
                return d.max(1);
            }
        }
        match self.tag() {
            "Seq" => self
                .get_term("fst")
                .map(|t| t.globular_dim())
                .unwrap_or(1)
                .max(self.get_term("snd").map(|t| t.globular_dim()).unwrap_or(1)),
            "First" => self
                .get_term("inner")
                .map(|t| t.globular_dim())
                .unwrap_or(1),
            "Choice" => self
                .get_term("l")
                .map(|t| t.globular_dim())
                .unwrap_or(1)
                .max(self.get_term("r").map(|t| t.globular_dim()).unwrap_or(1)),
            "Loop" | "Handle" | "Cobind" => {
                self.get_term("body").map(|t| t.globular_dim()).unwrap_or(1)
            }
            "App" => self
                .get_term("callee")
                .map(|t| t.globular_dim())
                .unwrap_or(1),
            "Iter" => self.get_term("step").map(|t| t.globular_dim()).unwrap_or(1),
            "RecordProj" | "RecordWith" => self
                .get_term("record")
                .map(|t| t.globular_dim())
                .unwrap_or(1),
            "Tag" => self
                .get_term("value")
                .map(|t| t.globular_dim())
                .unwrap_or(1),
            "Src" | "Tgt" => self.get_term("cell").map(|t| t.globular_dim()).unwrap_or(1),
            "Rewrite" => self
                .get_term("target")
                .map(|t| t.globular_dim())
                .unwrap_or(1),
            _ => 1,
        }
    }

    // --- Constructors for all 28 Term variants ---

    /// Construct an `Arr` (pure constant arrow).
    pub fn arr(value: impl Into<Value>) -> Self {
        TermData(json!({
            "__tag__": "Arr",
            "dim": json!({"__tag__": "Const", "value": 1}),
            "value": value.into()
        }))
    }

    /// Construct a `Const` (constant value).
    pub fn const_value(value: impl Into<Value>) -> Self {
        TermData(json!({ "__tag__": "Const", "value": value.into() }))
    }

    /// Construct an `Op` (named operation).
    ///
    /// `source` is the [`ArrSource`] serialized via the ADR-0103 shape
    /// (see [`arr_source_to_value`]). `lit` is `null` when `None`.
    pub fn op(
        name: impl Into<String>,
        args: Vec<TermData>,
        source: &ArrSource,
        lit: Option<Value>,
    ) -> Self {
        let args_arr: Vec<Value> = args.into_iter().map(|t| t.0).collect();
        TermData(json!({
            "__tag__": "Op",
            "dim": json!({"__tag__": "Const", "value": 1}),
            "name": name.into(),
            "args": args_arr,
            "source": arr_source_to_value(source),
            "lit": lit.unwrap_or(Value::Null)
        }))
    }

    /// Construct an `Op` at an explicit dimension (ADR-0120 Phase 3).
    ///
    /// `dim` is an ordinary dimension term — `Const n` for a numeric
    /// dimension, `Const "S"` for a named dimension/grade.
    pub fn op_dim(
        name: impl Into<String>,
        dim: TermData,
        args: Vec<TermData>,
        source: &ArrSource,
        lit: Option<Value>,
    ) -> Self {
        let args_arr: Vec<Value> = args.into_iter().map(|t| t.0).collect();
        TermData(json!({
            "__tag__": "Op",
            "dim": dim.0,
            "name": name.into(),
            "args": args_arr,
            "source": arr_source_to_value(source),
            "lit": lit.unwrap_or(Value::Null)
        }))
    }

    /// Construct a `Const` wrapping `value` — a literal dimension term
    /// suitable for an `Op`'s `dim` slot (e.g. `Const "S"` for a named
    /// dimension).
    pub fn dim_const(value: impl Into<Value>) -> Self {
        TermData(json!({ "__tag__": "Const", "value": value.into() }))
    }

    /// Construct a `Seq` (sequential composition, `>>>[0]`).
    pub fn seq(fst: TermData, snd: TermData) -> Self {
        TermData(json!({
            "__tag__": "Seq",
            "axis": json!({"__tag__": "Const", "value": 0}),
            "fst": fst.0,
            "snd": snd.0
        }))
    }

    /// Construct a `Seq` composing along `axis` (`>>>[k]`, ADR-0120 Phase 2).
    pub fn seq_axis(axis: TermData, fst: TermData, snd: TermData) -> Self {
        TermData(json!({
            "__tag__": "Seq",
            "axis": axis.0,
            "fst": fst.0,
            "snd": snd.0
        }))
    }

    /// Construct a `First` (fan-out on first component).
    pub fn first(inner: TermData) -> Self {
        TermData(json!({ "__tag__": "First", "inner": inner.0 }))
    }

    /// Construct a `Choice` (route on Either).
    pub fn choice(l: TermData, r: TermData) -> Self {
        TermData(json!({ "__tag__": "Choice", "l": l.0, "r": r.0 }))
    }

    /// Construct a `Loop` (feedback).
    pub fn loop_feedback(body: TermData) -> Self {
        TermData(json!({ "__tag__": "Loop", "body": body.0 }))
    }

    /// Construct an `App` (arrow application).
    pub fn app(callee: TermData, args: Vec<TermData>) -> Self {
        let args_arr: Vec<Value> = args.into_iter().map(|t| t.0).collect();
        TermData(json!({ "__tag__": "App", "callee": callee.0, "args": args_arr }))
    }

    /// Construct an `Iter` (bounded iteration).
    pub fn iter(fuel: TermData, predicate: TermData, step: TermData, initial: TermData) -> Self {
        TermData(json!({
            "__tag__": "Iter",
            "fuel": fuel.0,
            "predicate": predicate.0,
            "step": step.0,
            "initial": initial.0
        }))
    }

    /// Construct a `Child` (child projection by named role).
    pub fn child(role: impl Into<String>) -> Self {
        TermData(json!({ "__tag__": "Child", "role": role.into() }))
    }

    /// Construct a `Handle` (handler management).
    pub fn handle(body: TermData, target: impl Into<String>, impl_: TermData) -> Self {
        TermData(json!({
            "__tag__": "Handle",
            "body": body.0,
            "target": target.into(),
            "impl_": impl_.0
        }))
    }

    /// Construct a `Rewrite` (scheme rewrite step).
    pub fn rewrite(source: TermData, target: TermData, witness: &RewriteWitness) -> Self {
        TermData(json!({
            "__tag__": "Rewrite",
            "source": source.0,
            "target": target.0,
            "witness": rewrite_witness_to_value(witness)
        }))
    }

    /// Construct a `Path` (path between two terms).
    ///
    /// The endpoints are stored as `from` and `to` fields (matching
    /// `term_to_value`); `witness` is `null` when `None`.
    pub fn path(from: TermData, to: TermData, witness: Option<TermData>) -> Self {
        TermData(json!({
            "__tag__": "Path",
            "from": from.0,
            "to": to.0,
            "witness": witness.map(|w| w.0).unwrap_or(Value::Null)
        }))
    }

    /// Construct an `Equiv` (equality between two terms).
    pub fn equiv(a: TermData, b: TermData, path: Option<TermData>) -> Self {
        TermData(json!({
            "__tag__": "Equiv",
            "a": a.0,
            "b": b.0,
            "path": path.map(|p| p.0).unwrap_or(Value::Null)
        }))
    }

    /// Construct a `CellId` (identity of a cell).
    pub fn cell_id(arrow: TermData) -> Self {
        TermData(json!({ "__tag__": "CellId", "arrow": arrow.0 }))
    }

    /// Construct a `Src` (source face of a 2-cell).
    pub fn src(cell: TermData) -> Self {
        TermData(json!({ "__tag__": "Src", "cell": cell.0 }))
    }

    /// Construct a `Tgt` (target face of a 2-cell).
    pub fn tgt(cell: TermData) -> Self {
        TermData(json!({ "__tag__": "Tgt", "cell": cell.0 }))
    }

    /// Construct a `CellCompV` (vertical cell composition).
    pub fn cell_comp_v(first: TermData, second: TermData) -> Self {
        TermData(json!({
            "__tag__": "CellCompV",
            "first": first.0,
            "second": second.0
        }))
    }

    /// Construct a `Whisker` (whisker attaching an arrow to a cell).
    pub fn whisker(side: &Side, arrow: TermData, cell: TermData) -> Self {
        TermData(json!({
            "__tag__": "Whisker",
            "side": side_to_value(side),
            "arrow": arrow.0,
            "cell": cell.0
        }))
    }

    /// Construct a `RecordProj` (record field projection).
    pub fn record_proj(record: TermData, field: impl Into<String>) -> Self {
        TermData(json!({
            "__tag__": "RecordProj",
            "record": record.0,
            "field": field.into()
        }))
    }

    /// Construct a `RecordWith` (record field update).
    pub fn record_with(record: TermData, field: impl Into<String>, value: TermData) -> Self {
        TermData(json!({
            "__tag__": "RecordWith",
            "record": record.0,
            "field": field.into(),
            "value": value.0
        }))
    }

    /// Construct a `Tag` (tagged value wrapper).
    ///
    /// Named `tag_value` to avoid clashing with the [`TermData::tag`] accessor.
    pub fn tag_value(tag: impl Into<String>, value: TermData) -> Self {
        TermData(json!({ "__tag__": "Tag", "tag": tag.into(), "value": value.0 }))
    }

    /// Construct a `Univalence` (univalence from an equivalence).
    pub fn univalence(equiv: TermData) -> Self {
        TermData(json!({ "__tag__": "Univalence", "equiv": equiv.0 }))
    }

    /// Construct a `Glue` (glue a family along a path).
    pub fn glue(family: TermData, path: TermData) -> Self {
        TermData(json!({ "__tag__": "Glue", "family": family.0, "path": path.0 }))
    }

    /// Construct a `Fibrant` (fibrant type former).
    pub fn fibrant(base: TermData, family: TermData) -> Self {
        TermData(json!({ "__tag__": "Fibrant", "base": base.0, "family": family.0 }))
    }

    /// Construct a `JElim` (J-elimination).
    pub fn jelim(path: TermData, motive: TermData, base: TermData) -> Self {
        TermData(json!({
            "__tag__": "JElim",
            "path": path.0,
            "motive": motive.0,
            "base": base.0
        }))
    }

    /// Construct a `Refine` (refine a sort by a predicate).
    pub fn refine(sort: TermData, predicate: TermData) -> Self {
        TermData(json!({
            "__tag__": "Refine",
            "sort": sort.0,
            "predicate": predicate.0
        }))
    }

    /// Construct a `Cobind` (cobind over a grade and body).
    pub fn cobind(grade: TermData, body: TermData) -> Self {
        TermData(json!({ "__tag__": "Cobind", "grade": grade.0, "body": body.0 }))
    }

    // --- Conversion ---

    /// Convert a `Term` to `TermData`.
    ///
    /// This mirrors `plugin_lib_handl::model::term_to_value` so the JSON
    /// shape is identical to what Handl-authored models consume. The
    /// conversion is lossless for every variant of the kernel vocabulary.
    pub fn from_term(term: &Term) -> Self {
        TermData(term_to_value(term))
    }

    /// Convert `TermData` back to a `Term` (bootstrap compatibility).
    ///
    /// Matches on `self.tag()` and reconstructs the `Term` variant. Returns
    /// `Err("unknown tag: ...")` for unknown tags and a descriptive error
    /// when a tagged record is missing required fields.
    pub fn to_term(&self) -> Result<Term, String> {
        value_to_term(&self.0)
    }

    /// Borrow the inner `serde_json::Value`.
    pub fn as_value(&self) -> &Value {
        &self.0
    }

    /// Consume the `TermData`, returning the inner `serde_json::Value`.
    pub fn into_value(self) -> Value {
        self.0
    }
}

// --- Tagged-record serialization helpers (mirrors plugin_lib_handl::model) ---

/// Serialize a `Term` to the ADR-0103 tagged-record `Value` shape.
///
/// This is the canonical conversion shared with
/// `plugin_lib_handl::model::term_to_value`. Kept here so `plugin-engine`
/// can convert without depending on `plugin-lib-handl`.
/// Serialize a `Term` to the ADR-0103 tagged-record `Value` shape.
///
/// This is the canonical conversion shared with
/// `plugin_lib_handl::model::term_to_value`. Kept here so `plugin-engine`
/// can convert without depending on `plugin-lib-handl`.
fn term_to_value(term: &Term) -> Value {
    match term {
        Term::Arr { dim, value } => json!({
            "__tag__": "Arr",
            "dim": term_to_value(dim),
            "value": value
        }),
        Term::Const { value } => json!({ "__tag__": "Const", "value": value }),
        Term::Op {
            dim,
            name,
            args,
            source,
            lit,
        } => json!({
            "__tag__": "Op",
            "dim": term_to_value(dim),
            "name": name,
            "args": args.iter().map(term_to_value).collect::<Vec<_>>(),
            "source": arr_source_to_value(source),
            "lit": lit.as_ref().cloned().unwrap_or(Value::Null)
        }),
        Term::Seq { axis, fst, snd } => json!({
            "__tag__": "Seq",
            "axis": term_to_value(axis),
            "fst": term_to_value(fst),
            "snd": term_to_value(snd)
        }),
        Term::First { inner } => json!({ "__tag__": "First", "inner": term_to_value(inner) }),
        Term::Choice { l, r } => {
            json!({ "__tag__": "Choice", "l": term_to_value(l), "r": term_to_value(r) })
        }
        Term::Loop { body } => json!({ "__tag__": "Loop", "body": term_to_value(body) }),
        Term::App { callee, args } => json!({
            "__tag__": "App",
            "callee": term_to_value(callee),
            "args": args.iter().map(term_to_value).collect::<Vec<_>>()
        }),
        Term::Iter {
            fuel,
            predicate,
            step,
            initial,
        } => json!({
            "__tag__": "Iter",
            "fuel": term_to_value(fuel),
            "predicate": term_to_value(predicate),
            "step": term_to_value(step),
            "initial": term_to_value(initial)
        }),
        Term::Child { role } => json!({ "__tag__": "Child", "role": role }),
        Term::Handle {
            body,
            target,
            impl_,
        } => json!({
            "__tag__": "Handle",
            "body": term_to_value(body),
            "target": target,
            "impl_": term_to_value(impl_)
        }),
        Term::Rewrite {
            source,
            target,
            witness,
        } => json!({
            "__tag__": "Rewrite",
            "source": term_to_value(source),
            "target": term_to_value(target),
            "witness": rewrite_witness_to_value(witness)
        }),
        Term::Src { cell } => json!({ "__tag__": "Src", "cell": term_to_value(cell) }),
        Term::Tgt { cell } => json!({ "__tag__": "Tgt", "cell": term_to_value(cell) }),
        Term::RecordProj { record, field } => json!({
            "__tag__": "RecordProj",
            "record": term_to_value(record),
            "field": field
        }),
        Term::RecordWith {
            record,
            field,
            value,
        } => json!({
            "__tag__": "RecordWith",
            "record": term_to_value(record),
            "field": field,
            "value": term_to_value(value)
        }),
        Term::Tag { tag, value } => {
            json!({ "__tag__": "Tag", "tag": tag, "value": term_to_value(value) })
        }
        Term::Cobind { grade, body } => {
            json!({ "__tag__": "Cobind", "grade": term_to_value(grade), "body": term_to_value(body) })
        }
        // The record round-trips verbatim: `Opaque` *is* the data form.
        Term::Opaque { data } => data.clone(),
    }
}

/// Serialize an [`ArrSource`] to the ADR-0103 tagged-record `Value` shape.
fn arr_source_to_value(source: &ArrSource) -> Value {
    match source {
        ArrSource::Native => Value::String("Native".into()),
        ArrSource::Foreign(s) => json!({ "__tag__": "Foreign", "value": s }),
        ArrSource::Judgment => Value::String("Judgment".into()),
        ArrSource::DynamicForeign => Value::String("DynamicForeign".into()),
    }
}

/// Serialize a [`RewriteWitness`] to the ADR-0103 tagged-record `Value` shape.
fn rewrite_witness_to_value(witness: &RewriteWitness) -> Value {
    match witness {
        RewriteWitness::Named(name) => json!({ "__tag__": "Named", "value": name }),
        RewriteWitness::Compute => json!({ "__tag__": "Compute" }),
        RewriteWitness::HandlerHint => json!({ "__tag__": "HandlerHint" }),
        RewriteWitness::Cast => json!({ "__tag__": "Cast" }),
    }
}

/// Serialize a [`Side`] to the ADR-0103 tagged-record `Value` shape.
fn side_to_value(side: &Side) -> Value {
    match side {
        Side::Left => Value::String("Left".into()),
        Side::Right => Value::String("Right".into()),
    }
}

// --- Reverse conversion helpers ---

/// Parse an ADR-0103 tagged-record `Value` back into a `Term`.
/// Parse an ADR-0103 tagged-record `Value` back into a `Term`.
fn value_to_term(value: &Value) -> Result<Term, String> {
    let tag = value
        .get("__tag__")
        .and_then(|v| v.as_str())
        .ok_or_else(|| "TermData is not a tagged record (missing __tag__)".to_string())?;
    match tag {
        "Arr" => Ok(Term::Arr {
            dim: value_to_dim(value)?,
            value: field(value, "value")?,
        }),
        "Const" => Ok(Term::Const {
            value: field(value, "value")?,
        }),
        "Op" => Ok(Term::Op {
            dim: value_to_dim(value)?,
            name: field_str(value, "name")?.to_string(),
            args: field_term_list(value, "args")?,
            source: value_to_arr_source(value.get("source"))?,
            lit: match value.get("lit") {
                Some(Value::Null) | None => None,
                Some(v) => Some(v.clone()),
            },
        }),
        "Seq" => Ok(Term::Seq {
            axis: value_to_axis(value)?,
            fst: Box::new(field_term(value, "fst")?),
            snd: Box::new(field_term(value, "snd")?),
        }),
        "First" => Ok(Term::First {
            inner: Box::new(field_term(value, "inner")?),
        }),
        "Choice" => Ok(Term::Choice {
            l: Box::new(field_term(value, "l")?),
            r: Box::new(field_term(value, "r")?),
        }),
        "Loop" => Ok(Term::Loop {
            body: Box::new(field_term(value, "body")?),
        }),
        "App" => Ok(Term::App {
            callee: Box::new(field_term(value, "callee")?),
            args: field_term_list(value, "args")?,
        }),
        "Iter" => Ok(Term::Iter {
            fuel: Box::new(field_term(value, "fuel")?),
            predicate: Box::new(field_term(value, "predicate")?),
            step: Box::new(field_term(value, "step")?),
            initial: Box::new(field_term(value, "initial")?),
        }),
        "Child" => Ok(Term::Child {
            role: field_str(value, "role")?.to_string(),
        }),
        "Handle" => Ok(Term::Handle {
            body: Box::new(field_term(value, "body")?),
            target: field_str(value, "target")?.to_string(),
            impl_: Box::new(field_term(value, "impl_")?),
        }),
        "Rewrite" => Ok(Term::Rewrite {
            source: Box::new(field_term(value, "source")?),
            target: Box::new(field_term(value, "target")?),
            witness: value_to_rewrite_witness(value.get("witness"))?,
        }),
        "Src" => Ok(Term::Src {
            cell: Box::new(field_term(value, "cell")?),
        }),
        "Tgt" => Ok(Term::Tgt {
            cell: Box::new(field_term(value, "cell")?),
        }),
        "RecordProj" => Ok(Term::RecordProj {
            record: Box::new(field_term(value, "record")?),
            field: field_str(value, "field")?.to_string(),
        }),
        "RecordWith" => Ok(Term::RecordWith {
            record: Box::new(field_term(value, "record")?),
            field: field_str(value, "field")?.to_string(),
            value: Box::new(field_term(value, "value")?),
        }),
        "Tag" => Ok(Term::Tag {
            tag: field_str(value, "tag")?.to_string(),
            value: Box::new(field_term(value, "value")?),
        }),
        "Cobind" => Ok(Term::Cobind {
            grade: Box::new(field_term(value, "grade")?),
            body: Box::new(field_term(value, "body")?),
        }),
        // ADR-0119 §7 fold / ADR-0120 Phase 5: any tag outside the closed
        // kernel vocabulary names a *derived* operator in data form —
        // `Path`, `Equiv`, `Refine`, `CellId`, `Whisker`, `Univalence`,
        // `Glue`, `Fibrant`, `JElim`, … — carried as `Term::Opaque` so the
        // conversion stays total and `TermData::from_term` round-trips the
        // record exactly.
        _ => Ok(Term::Opaque {
            data: value.clone(),
        }),
    }
}

fn value_to_dim(value: &Value) -> Result<Box<Term>, String> {
    match value.get("dim") {
        Some(Value::Null) | None => Ok(Box::new(Term::Const {
            value: Value::from(1),
        })),
        Some(v) => value_to_term(v).map(Box::new),
    }
}

/// Parse the `axis` field of a `Seq` record, defaulting to `0` when absent
/// so serialized `Seq`s written before ADR-0120 Phase 2 keep decoding.
fn value_to_axis(value: &Value) -> Result<Box<Term>, String> {
    match value.get("axis") {
        Some(Value::Null) | None => Ok(Box::new(Term::Const {
            value: Value::from(0),
        })),
        Some(v) => value_to_term(v).map(Box::new),
    }
}

/// Parse an [`ArrSource`] from its ADR-0103 `Value` shape.
fn value_to_arr_source(value: Option<&Value>) -> Result<ArrSource, String> {
    match value {
        Some(Value::String(s)) if s == "Native" => Ok(ArrSource::Native),
        Some(Value::String(s)) if s == "Judgment" => Ok(ArrSource::Judgment),
        Some(Value::String(s)) if s == "DynamicForeign" => Ok(ArrSource::DynamicForeign),
        Some(Value::Object(map))
            if map.get("__tag__").and_then(|v| v.as_str()) == Some("Foreign") =>
        {
            let name = map
                .get("value")
                .and_then(|v| v.as_str())
                .ok_or_else(|| "Foreign source missing 'value' string".to_string())?;
            Ok(ArrSource::Foreign(name.to_string()))
        }
        other => Err(format!("invalid ArrSource: {other:?}")),
    }
}

/// Parse a [`RewriteWitness`] from its ADR-0103 `Value` shape.
fn value_to_rewrite_witness(value: Option<&Value>) -> Result<RewriteWitness, String> {
    let v = value.ok_or_else(|| "missing 'witness' field".to_string())?;
    let tag = v
        .get("__tag__")
        .and_then(|t| t.as_str())
        .ok_or_else(|| "witness is not a tagged record".to_string())?;
    match tag {
        "Named" => {
            let name = v
                .get("value")
                .and_then(|n| n.as_str())
                .ok_or_else(|| "Named witness missing 'value' string".to_string())?;
            Ok(RewriteWitness::Named(name.to_string()))
        }
        "Compute" => Ok(RewriteWitness::Compute),
        "HandlerHint" => Ok(RewriteWitness::HandlerHint),
        "Cast" => Ok(RewriteWitness::Cast),
        other => Err(format!("unknown witness tag: {other}")),
    }
}

/// Parse a [`Side`] from its ADR-0103 `Value` shape.
///
/// Unused while `Whisker` lives in data form (`Term::Opaque`, ADR-0119 §7):
/// the opaque record carries `side` verbatim and nothing decodes it
/// structurally. Kept so Whisker records re-gain a structured decode path if
/// they fold back out of `Opaque`.
#[allow(dead_code)]
fn value_to_side(value: Option<&Value>) -> Result<Side, String> {
    match value {
        Some(Value::String(s)) if s == "Left" => Ok(Side::Left),
        Some(Value::String(s)) if s == "Right" => Ok(Side::Right),
        other => Err(format!("invalid Side: {other:?}")),
    }
}

/// Get a required field as a cloned `Value`.
fn field(value: &Value, name: &str) -> Result<Value, String> {
    value
        .get(name)
        .cloned()
        .ok_or_else(|| format!("missing field '{name}'"))
}

/// Get a required field as a string slice.
fn field_str<'a>(value: &'a Value, name: &str) -> Result<&'a str, String> {
    value
        .get(name)
        .and_then(|v| v.as_str())
        .ok_or_else(|| format!("missing or non-string field '{name}'"))
}

/// Get a required field as a `Term` (nested tagged record).
fn field_term(value: &Value, name: &str) -> Result<Term, String> {
    value
        .get(name)
        .ok_or_else(|| format!("missing field '{name}'"))
        .and_then(value_to_term)
}

/// Get a required field as a list of `Term`s.
fn field_term_list(value: &Value, name: &str) -> Result<Vec<Term>, String> {
    value
        .get(name)
        .and_then(|v| v.as_array())
        .ok_or_else(|| format!("missing or non-array field '{name}'"))?
        .iter()
        .map(value_to_term)
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn c(n: i64) -> Term {
        Term::Const {
            value: Value::from(n),
        }
    }

    fn dim1() -> Box<Term> {
        Box::new(c(1))
    }

    /// One representative `Term` per variant of the kernel vocabulary.
    ///
    /// `TermData::from_term` documents itself as lossless, so every one of
    /// these must survive `from_term` -> `to_term` unchanged.
    ///
    /// The module this replaces tested the pre-ADR-0119 shapes — `Arr { value }`
    /// with no `dim`, plus the `Path`/`Equiv`/`Refine`/`CellId`/`JElim` variants
    /// that ADR-0119 §7 folded into `Term::Opaque` — and had been disabled with
    /// `#[cfg(any())]`, so it had not compiled or run for the whole transition.
    fn sample_terms() -> Vec<(&'static str, Term)> {
        let boxed = |t: Term| Box::new(t);
        vec![
            (
                "Arr",
                Term::Arr {
                    dim: dim1(),
                    value: Value::from(1),
                },
            ),
            ("Const", c(42)),
            (
                "Op",
                Term::Op {
                    dim: dim1(),
                    name: "add".into(),
                    args: vec![c(1)],
                    source: ArrSource::Native,
                    lit: None,
                },
            ),
            (
                "Seq",
                Term::Seq {
                    axis: Box::new(c(0)),
                    fst: boxed(c(1)),
                    snd: boxed(c(2)),
                },
            ),
            ("First", Term::First { inner: boxed(c(1)) }),
            (
                "Choice",
                Term::Choice {
                    l: boxed(c(1)),
                    r: boxed(c(2)),
                },
            ),
            ("Loop", Term::Loop { body: boxed(c(1)) }),
            (
                "App",
                Term::App {
                    callee: boxed(c(1)),
                    args: vec![c(2)],
                },
            ),
            (
                "Iter",
                Term::Iter {
                    fuel: boxed(c(3)),
                    predicate: boxed(c(1)),
                    step: boxed(c(2)),
                    initial: boxed(c(0)),
                },
            ),
            ("Child", Term::Child { role: "subject".into() }),
            (
                "Handle",
                Term::Handle {
                    body: boxed(c(1)),
                    target: "io".into(),
                    impl_: boxed(c(2)),
                },
            ),
            (
                "Rewrite",
                Term::Rewrite {
                    source: boxed(c(1)),
                    target: boxed(c(2)),
                    witness: RewriteWitness::Compute,
                },
            ),
            ("Src", Term::Src { cell: boxed(c(1)) }),
            ("Tgt", Term::Tgt { cell: boxed(c(1)) }),
            (
                "RecordProj",
                Term::RecordProj {
                    record: boxed(c(1)),
                    field: "x".into(),
                },
            ),
            (
                "RecordWith",
                Term::RecordWith {
                    record: boxed(c(1)),
                    field: "x".into(),
                    value: boxed(c(2)),
                },
            ),
            (
                "Tag",
                Term::Tag {
                    tag: "Foo".into(),
                    value: boxed(c(1)),
                },
            ),
            (
                "Cobind",
                Term::Cobind {
                    grade: boxed(c(1)),
                    body: boxed(c(2)),
                },
            ),
            (
                "Opaque",
                Term::Opaque {
                    data: json!({"__tag__": "Whisker", "side": "Left"}),
                },
            ),
        ]
    }

    #[test]
    fn every_variant_round_trips_through_term_data() {
        for (name, term) in sample_terms() {
            let data = TermData::from_term(&term);
            // `Opaque` reproduces the folded record verbatim, so its tag is the
            // *derived* operator's tag (`Whisker`), not `Opaque` — that is the
            // ADR-0119 §7 fold: a derived operator survives as the same record
            // the surface forms produce.
            let expected_tag = match &term {
                Term::Opaque { data } => data["__tag__"].as_str().unwrap().to_string(),
                _ => name.to_string(),
            };
            assert_eq!(data.tag(), expected_tag, "tag mismatch for {name}");
            let back = data
                .to_term()
                .unwrap_or_else(|e| panic!("{name}: to_term failed: {e}"));
            assert_eq!(back, term, "{name} did not round-trip through TermData");
        }
    }

    #[test]
    fn unknown_tag_decodes_to_opaque() {
        // `to_term` is total: an unrecognised tagged record becomes `Opaque`,
        // which is what makes the ADR-0119 §7 fold safe — a derived operator the
        // bootstrap vocabulary does not know survives as data rather than
        // failing the conversion.
        let data = TermData(json!({
            "__tag__": "SomeFutureOperator",
            "x": 1,
        }));
        match data.to_term() {
            Ok(Term::Opaque { data }) => {
                assert_eq!(data["__tag__"], "SomeFutureOperator");
            }
            other => panic!("expected Opaque, got {other:?}"),
        }
    }
}
