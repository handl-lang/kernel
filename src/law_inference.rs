//! Structural law inference over the production `Term` IR (ADR-0076 OQ#5).
//!
//! The research PoC in `arrow-calculus-kernel-poc/src/law_inference.rs`
//! implements law *inference*: given an arrow graph, discover which
//! CutElim-proven structural laws it satisfies WITHOUT the user declaring
//! them. The PoC operates on `PolyGraph` (a separate IR). This module ports
//! the concept to the production [`Term`](crate::term::Term) kernel.
//!
//! # What this is
//!
//! ADR-0075's "primary mode" (trait inference), scoped to single-arrow laws.
//! Instead of requiring the user to write `law map_id: first(id) = id`, the
//! system has a *library* of known law patterns (the "law catalog") and
//! checks each one against a `Term`:
//!
//!   1. **Structural match** -- does the scheme's wiring match the law
//!      pattern's expected structure? (e.g. functor laws need a `First`-shaped
//!      graph.)
//!   2. **CutElim verify** -- do both sides of the law equation normalize to
//!      the same form under CutElim?
//!
//! If both pass, the system reports: "this arrow satisfies law
//! `functor_identity`" -- without the user declaring it. This mirrors the
//! Lean mechanization (`TraitInference.lean`): the `UsesFirst` structural
//! recognizer triggers the check, and `CutElim` normalization discharges it.
//!
//! # What this is NOT
//!
//! Inference works ONLY for the CutElim-proven STRUCTURAL fragment -- the
//! functor laws (`first` identity/fusion). These laws ARE the CutElim
//! rewrites, so the system can discover them from wiring alone. Non-functor
//! laws (roundtrip, semigroup associativity, sortedness) CANNOT be inferred
//! -- they are semantic facts about specific base arrows that require
//! explicit axioms, which cannot be discovered from wiring. This matches
//! `EquationalLawInference.lean`: structural recognition triggers the check,
//! but an axiom discharges it. This module does not attempt to infer
//! axiom-requiring laws; it documents the boundary explicitly.
//!
//! # Porting notes
//!
//! The PoC's `PolyGraph` has six rewrites; four are portable to `Term`:
//!   - `ceIdLeft`    : `Seq(id, G) ==> G`
//!   - `ceIdRight`   : `Seq(G, id) ==> G`
//!   - `ceFirstFusion`: `Seq(First(G), First(H)) ==> First(Seq(G, H))`
//!   - `ceFirstId`   : `First(id) ==> id`
//!
//! The two `Left` rewrites (`ceLeftFusion`, `ceLeftId`) are NOT portable:
//! the production `Term` has no coproduct functor (`Left`) variant. The
//! `Choice` variant routes on `Either` but is not a functor, so the
//! coproduct functor laws are not inferable here.

use plugin_engine::TermData;
use serde_json::Value;

use crate::term::{ArrSource, Term};

/// Fuel budget for normalization. Generous for these small graphs; the bound
/// exists only as a termination safety net (the CutElim rewrite relation is
/// not proven strongly normalizing for all graphs, but the four rewrites here
/// are size-non-increasing and terminate quickly in practice).
const NORMALIZE_FUEL: usize = 1024;

// ============================================================================
// 1. CutElim normalizer for `Term`
// ============================================================================
//
// The four portable CutElim rewrites, applied as local scheme-rewrite steps.
// `normalize` applies these bottom-up to a fixpoint, bounded by `fuel`.
// `law_equal` checks structural equality of the normalized forms.

/// Is this `Arr` the identity arrow (`op: "id"`, no args, native, no lit)?
///
/// The production `Term` has no dedicated `Id` variant; identity is the
/// base arrow `Arr { op: "id", args: [], source: Native, lit: None }`. This
/// is the PoC's `PolyGraph::Id` recognizer ported to `Term`.
fn is_id_td(td: &TermData) -> bool {
    td.tag() == "Op"
        && td.get_str("name") == Some("id")
        && td.get_term_list("args").is_empty()
        && td.arr_source() == Some(ArrSource::Native)
        && td.get("lit").map_or(true, |v| v.is_null())
}

/// Is this `Arr` the identity arrow? Thin `&Term` wrapper around
/// [`is_id_td`] for callers (and tests) that hold a `Term`.
#[cfg(test)]
fn is_id(scheme: &Term) -> bool {
    is_id_td(&TermData::from_term(scheme))
}

/// Try to apply ONE CutElim rewrite at the root of `scheme` (TermData form).
/// Returns the rewritten scheme if a rule fired, else `None`.
///
/// The four portable rewrites:
///   - `ce_id_left`     : `Seq(id, G) ==> G`
///   - `ce_id_right`    : `Seq(G, id) ==> G`
///   - `ce_first_fusion`: `Seq(First(G), First(H)) ==> First(Seq(G, H))`
///   - `ce_first_id`    : `First(id) ==> id`
fn rewrite_root_td(td: &TermData) -> Option<TermData> {
    match td.tag() {
        "Seq" => {
            let fst = td.get_term("fst")?;
            let snd = td.get_term("snd")?;
            // ce_id_left : Seq(id, G) ==> G
            if is_id_td(&fst) {
                return Some(snd);
            }
            // ce_id_right : Seq(G, id) ==> G
            if is_id_td(&snd) {
                return Some(fst);
            }
            // ce_first_fusion : Seq(First(G), First(H)) ==> First(Seq(G, H))
            if fst.tag() == "First" && snd.tag() == "First" {
                let g1 = fst.get_term("inner")?;
                let g2 = snd.get_term("inner")?;
                return Some(TermData::first(TermData::seq(g1, g2)));
            }
            None
        }
        // ce_first_id : First(id) ==> id
        "First" => {
            let inner = td.get_term("inner")?;
            if is_id_td(&inner) { Some(inner) } else { None }
        }
        _ => None,
    }
}

/// Rebuild `td` with the given child fields replaced by normalized children.
/// Non-child fields (names, roles, witnesses, sides, …) are preserved by
/// cloning the original tagged record and overwriting only the listed fields.
fn with_children(td: &TermData, children: &[(&str, TermData)]) -> TermData {
    let mut value = td.as_value().clone();
    if let Some(obj) = value.as_object_mut() {
        for (field, child) in children {
            obj.insert((*field).to_string(), child.as_value().clone());
        }
    }
    TermData(value)
}

/// Rebuild `td` with a list child field replaced by normalized children.
fn with_child_list(td: &TermData, field: &str, children: Vec<TermData>) -> TermData {
    let mut value = td.as_value().clone();
    if let Some(obj) = value.as_object_mut() {
        let arr: Vec<Value> = children.into_iter().map(|t| t.into_value()).collect();
        obj.insert(field.to_string(), Value::Array(arr));
    }
    TermData(value)
}

/// Recurse into a required child field, returning the normalized child and
/// whether it changed. A missing/null field is returned unchanged (no change).
fn pass_req(td: &TermData, field: &str) -> (TermData, bool) {
    match td.get_term(field) {
        Some(child) if !child.as_value().is_null() => rewrite_pass_td(&child),
        Some(child) => (child, false),
        None => (TermData(Value::Null), false),
    }
}

/// Recurse into an optional child field (Null/absent → no child, no change).
fn pass_opt(td: &TermData, field: &str) -> (Option<TermData>, bool) {
    match td.get(field) {
        Some(Value::Null) | None => (None, false),
        Some(_) => match td.get_term(field) {
            Some(child) => {
                let (c2, c) = rewrite_pass_td(&child);
                (Some(c2), c)
            }
            None => (None, false),
        },
    }
}

/// One bottom-up pass: normalize children first, then apply root rewrites
/// repeatedly until no root rule fires. Returns the pass result and whether
/// anything changed.
///
/// Recurses into every child scheme of every variant: `Seq` (fst, snd),
/// `First` (inner), `Choice` (l, r), `Loop` (body), `App` (callee + args),
/// `Arr` (args), `Handle` (body, impl_). Then applies root rewrites to
/// fixpoint so a cascade like `Seq(First(id), First(id)) -> First(Seq(id,
/// id)) -> First(id) -> id` completes within a single pass.
fn rewrite_pass_td(td: &TermData) -> (TermData, bool) {
    // First recurse into children (bottom-up). The non-child fields are
    // preserved by cloning the original tagged record and overwriting only
    // the child fields with their normalized forms.
    let (g_norm, child_changed) = match td.tag() {
        "Op" => {
            let mut changed = false;
            let args2: Vec<TermData> = td
                .get_term_list("args")
                .into_iter()
                .map(|a| {
                    let (a2, c) = rewrite_pass_td(&a);
                    changed = changed || c;
                    a2
                })
                .collect();
            (with_child_list(td, "args", args2), changed)
        }
        "Seq" => {
            let (f2, cf) = pass_req(td, "fst");
            let (s2, cs) = pass_req(td, "snd");
            (with_children(td, &[("fst", f2), ("snd", s2)]), cf || cs)
        }
        "First" => {
            let (i2, c) = pass_req(td, "inner");
            (with_children(td, &[("inner", i2)]), c)
        }
        "Choice" => {
            let (l2, cl) = pass_req(td, "l");
            let (r2, cr) = pass_req(td, "r");
            (with_children(td, &[("l", l2), ("r", r2)]), cl || cr)
        }
        "Loop" => {
            let (b2, c) = pass_req(td, "body");
            (with_children(td, &[("body", b2)]), c)
        }
        "App" => {
            let (c2, cc) = pass_req(td, "callee");
            let mut changed = cc;
            let args2: Vec<TermData> = td
                .get_term_list("args")
                .into_iter()
                .map(|a| {
                    let (a2, c) = rewrite_pass_td(&a);
                    changed = changed || c;
                    a2
                })
                .collect();
            let rebuilt = with_child_list(&with_children(td, &[("callee", c2)]), "args", args2);
            (rebuilt, changed)
        }
        "Handle" => {
            let (b2, cb) = pass_req(td, "body");
            let (i2, ci) = pass_req(td, "impl_");
            (with_children(td, &[("body", b2), ("impl_", i2)]), cb || ci)
        }
        "Rewrite" => {
            let (s2, cs) = pass_req(td, "source");
            let (t2, ct) = pass_req(td, "target");
            (
                with_children(td, &[("source", s2), ("target", t2)]),
                cs || ct,
            )
        }
        "Iter" => {
            let (f2, cf) = pass_req(td, "fuel");
            let (p2, cp) = pass_req(td, "predicate");
            let (s2, cs) = pass_req(td, "step");
            let (i2, ci) = pass_req(td, "initial");
            (
                with_children(
                    td,
                    &[
                        ("fuel", f2),
                        ("predicate", p2),
                        ("step", s2),
                        ("initial", i2),
                    ],
                ),
                cf || cp || cs || ci,
            )
        }
        "Path" => {
            let (a2, ca) = pass_req(td, "from");
            let (b2, cb) = pass_req(td, "to");
            let (w2, cw) = pass_opt(td, "witness");
            let mut children = vec![("from", a2), ("to", b2)];
            if let Some(w) = w2 {
                children.push(("witness", w));
            }
            (with_children(td, &children), ca || cb || cw)
        }
        "Equiv" => {
            let (a2, ca) = pass_req(td, "a");
            let (b2, cb) = pass_req(td, "b");
            let (p2, cp) = pass_opt(td, "path");
            let mut children = vec![("a", a2), ("b", b2)];
            if let Some(p) = p2 {
                children.push(("path", p));
            }
            (with_children(td, &children), ca || cb || cp)
        }
        "Src" => {
            let (c2, cc) = pass_req(td, "cell");
            (with_children(td, &[("cell", c2)]), cc)
        }
        "Tgt" => {
            let (c2, cc) = pass_req(td, "cell");
            (with_children(td, &[("cell", c2)]), cc)
        }
        "RecordProj" => {
            let (r2, cr) = pass_req(td, "record");
            (with_children(td, &[("record", r2)]), cr)
        }
        "RecordWith" => {
            let (r2, cr) = pass_req(td, "record");
            let (v2, cv) = pass_req(td, "value");
            (
                with_children(td, &[("record", r2), ("value", v2)]),
                cr || cv,
            )
        }
        "Tag" => {
            let (v2, cv) = pass_req(td, "value");
            (with_children(td, &[("value", v2)]), cv)
        }
        "CellId" => {
            let (a2, ca) = pass_req(td, "arrow");
            (with_children(td, &[("arrow", a2)]), ca)
        }
        "CellCompV" => {
            let (f2, cf) = pass_req(td, "first");
            let (s2, cs) = pass_req(td, "second");
            (
                with_children(td, &[("first", f2), ("second", s2)]),
                cf || cs,
            )
        }
        "Whisker" => {
            let (a2, ca) = pass_req(td, "arrow");
            let (c2, cc) = pass_req(td, "cell");
            (with_children(td, &[("arrow", a2), ("cell", c2)]), ca || cc)
        }
        "Univalence" => {
            let (e2, ce) = pass_req(td, "equiv");
            (with_children(td, &[("equiv", e2)]), ce)
        }
        "Glue" => {
            let (f2, cf) = pass_req(td, "family");
            let (p2, cp) = pass_req(td, "path");
            (with_children(td, &[("family", f2), ("path", p2)]), cf || cp)
        }
        "Fibrant" => {
            let (b2, cb) = pass_req(td, "base");
            let (f2, cf) = pass_req(td, "family");
            (with_children(td, &[("base", b2), ("family", f2)]), cb || cf)
        }
        "JElim" => {
            let (p2, cp) = pass_req(td, "path");
            let (m2, cm) = pass_req(td, "motive");
            let (b2, cb) = pass_req(td, "base");
            (
                with_children(td, &[("path", p2), ("motive", m2), ("base", b2)]),
                cp || cm || cb,
            )
        }
        "Refine" => {
            let (s2, cs) = pass_req(td, "sort");
            let (p2, cp) = pass_req(td, "predicate");
            (
                with_children(td, &[("sort", s2), ("predicate", p2)]),
                cs || cp,
            )
        }
        "Cobind" => {
            let (g2, cg) = pass_req(td, "grade");
            let (b2, cb) = pass_req(td, "body");
            (with_children(td, &[("grade", g2), ("body", b2)]), cg || cb)
        }
        // Leaf variants (no child schemes) and unknown tags: unchanged.
        _ => (td.clone(), false),
    };

    // Then try root rewrites on the (children-normalized) scheme. Repeat at
    // the root until no root rule fires.
    let mut cur = g_norm;
    let mut root_changed = false;
    loop {
        match rewrite_root_td(&cur) {
            Some(next) => {
                cur = next;
                root_changed = true;
            }
            None => break,
        }
    }
    (cur, child_changed || root_changed)
}

/// Normalize a scheme by repeatedly applying the four CutElim rewrites
/// bottom-up until a fixpoint is reached or `fuel` passes are exhausted.
///
/// If fuel is exhausted before a fixpoint, the result is the
/// partially-normalized scheme (`law_equal` may then report false negatives).
pub fn normalize(scheme: &Term, fuel: usize) -> Term {
    let mut cur = TermData::from_term(scheme);
    for _ in 0..fuel {
        let (next, changed) = rewrite_pass_td(&cur);
        if !changed {
            break;
        }
        cur = next;
    }
    cur.to_term().unwrap_or_else(|_| scheme.clone())
}

/// Two schemes are `law_equal` iff they normalize to the same form under
/// CutElim. `Term` derives `PartialEq`, so structural equality of the
/// normalized forms is the comparison. `Arr` names are compared structurally
/// (the name is opaque data -- two `Arr`s are equal only if their names,
/// args, source, and lit match). This is what lets the composition law
/// `First(Seq(f, g)) === Seq(First(f), First(g))` verify: both sides
/// normalize to `First(Seq(f, g))` with matching `f`, `g`.
pub fn law_equal(a: &Term, b: &Term) -> bool {
    normalize(a, NORMALIZE_FUEL) == normalize(b, NORMALIZE_FUEL)
}

// ============================================================================
// 2. Structural Pattern Recognizers
// ============================================================================
//
// Mirrors `UsesFirst` from `TraitInference.lean`: a structural pattern
// recognizer that detects whether a scheme uses the `First` combinator. The
// inference theorem says: if a scheme `G` uses `First`, then `G` satisfies
// the functor identity and composition laws -- without the law being
// declared. The recognition is purely from the scheme's wiring structure.
//
// "Uses first" means the scheme contains a `First(_)` node anywhere in its
// combinator tree. This catches nested cases like `First(Seq(First(f), g))`
// (the outer `First` is the trigger) and `Seq(First(f), arr("h"))` (where
// `First` is not at the root).

/// Does a child field of `td` use the `First` combinator? Missing/null
/// fields do not.
fn child_uses_first(td: &TermData, field: &str) -> bool {
    match td.get_term(field) {
        Some(child) if !child.as_value().is_null() => uses_first_td(&child),
        _ => false,
    }
}

/// Does a list child field of `td` use the `First` combinator in any element?
fn children_uses_first(td: &TermData, field: &str) -> bool {
    td.get_term_list(field).iter().any(uses_first_td)
}

/// Does the scheme use the `First` combinator anywhere in its tree
/// (TermData form)? Mirrors `UsesFirst` from the Lean mechanization.
fn uses_first_td(td: &TermData) -> bool {
    match td.tag() {
        "First" => true,
        "Op" => children_uses_first(td, "args"),
        "App" => child_uses_first(td, "callee") || children_uses_first(td, "args"),
        "Seq" => child_uses_first(td, "fst") || child_uses_first(td, "snd"),
        "Choice" => child_uses_first(td, "l") || child_uses_first(td, "r"),
        "Loop" => child_uses_first(td, "body"),
        "Handle" => child_uses_first(td, "body") || child_uses_first(td, "impl_"),
        "Rewrite" => child_uses_first(td, "source") || child_uses_first(td, "target"),
        "Iter" => {
            child_uses_first(td, "fuel")
                || child_uses_first(td, "predicate")
                || child_uses_first(td, "step")
                || child_uses_first(td, "initial")
        }
        "Path" => {
            child_uses_first(td, "from")
                || child_uses_first(td, "to")
                || child_uses_first(td, "witness")
        }
        "Equiv" => {
            child_uses_first(td, "a") || child_uses_first(td, "b") || child_uses_first(td, "path")
        }
        "Src" | "Tgt" => child_uses_first(td, "cell"),
        "RecordProj" => child_uses_first(td, "record"),
        "RecordWith" => child_uses_first(td, "record") || child_uses_first(td, "value"),
        "Tag" => child_uses_first(td, "value"),
        "CellId" => child_uses_first(td, "arrow"),
        "CellCompV" => child_uses_first(td, "first") || child_uses_first(td, "second"),
        "Whisker" => child_uses_first(td, "arrow") || child_uses_first(td, "cell"),
        "Univalence" => child_uses_first(td, "equiv"),
        "Glue" => child_uses_first(td, "family") || child_uses_first(td, "path"),
        "Fibrant" => child_uses_first(td, "base") || child_uses_first(td, "family"),
        "JElim" => {
            child_uses_first(td, "path")
                || child_uses_first(td, "motive")
                || child_uses_first(td, "base")
        }
        "Refine" => child_uses_first(td, "sort") || child_uses_first(td, "predicate"),
        "Cobind" => child_uses_first(td, "grade") || child_uses_first(td, "body"),
        // Leaf variants and unknown tags do not use `First`.
        _ => false,
    }
}

/// Does the scheme use the `First` combinator anywhere in its tree?
/// Mirrors `UsesFirst` from the Lean mechanization. Thin `&Term` wrapper
/// around [`uses_first_td`].
pub fn uses_first(scheme: &Term) -> bool {
    uses_first_td(&TermData::from_term(scheme))
}

// ============================================================================
// 3. Law Patterns
// ============================================================================

/// A known law pattern the system can check against an arrow. This is the
/// "law catalog" -- a library of laws the system knows about. Given a
/// `Term`, the inference engine checks each pattern.
///
/// This is the single-arrow analogue of ADR-0075's `CatalogEntry`. Where
/// `CatalogEntry` bundles multiple laws under a named trait, a `LawPattern`
/// is ONE law that attaches to ONE arrow -- no bundle needed (ADR-0076: "A
/// single-arrow law needs no bundle").
pub struct LawPattern {
    /// Short name, e.g. "functor_identity".
    pub name: String,
    /// Human-readable statement, e.g. "first(id) = id".
    pub description: String,
    /// The law check: given a scheme, decide whether the law applies and
    /// holds. This combines the structural-match step and the CutElim-verify
    /// step into one function.
    pub check: fn(&Term) -> LawCheckResult,
}

/// The outcome of checking a single law pattern against an arrow.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LawCheckResult {
    /// The law applies and holds (both sides normalize equal under CutElim).
    Satisfied,
    /// The law applies but does NOT hold (normalization differs).
    Violated,
    /// The law does not apply to this arrow (structural mismatch -- the
    /// arrow's wiring does not match the law pattern's expected shape).
    NotApplicable,
}

/// Check the functor identity law: `first(id) = id` (ceFirstId).
///
/// If the arrow uses `First`, construct `lhs = First(id)`, `rhs = id`, and
/// verify via `law_equal`. The law is a CutElim rewrite, so it holds for any
/// `First`-shaped scheme. The inference: "G uses `First`, therefore it
/// satisfies the functor identity law (by ceFirstId)."
fn check_functor_identity(arrow: &Term) -> LawCheckResult {
    if !uses_first(arrow) {
        return LawCheckResult::NotApplicable;
    }
    // functor identity: first(id) = id  (ceFirstId)
    let id_td = TermData::op("id", vec![], &ArrSource::Native, None);
    let lhs = TermData::first(id_td.clone())
        .to_term()
        .expect("TermData -> Term");
    let rhs = id_td.to_term().expect("TermData -> Term");
    if law_equal(&lhs, &rhs) {
        LawCheckResult::Satisfied
    } else {
        LawCheckResult::Violated
    }
}

/// Check the functor composition law:
/// `first(f >>> g) = first(f) >>> first(g)` (ceFirstFusion).
///
/// If the arrow uses `First`, construct both sides with concrete base arrows
/// `f`, `g` and verify via `law_equal`. The law is a CutElim rewrite, so it
/// holds for any `First`-shaped scheme. The inference: "G uses `First`,
/// therefore it satisfies the functor composition law (by ceFirstFusion)."
fn check_functor_composition(arrow: &Term) -> LawCheckResult {
    if !uses_first(arrow) {
        return LawCheckResult::NotApplicable;
    }
    // functor composition: first(f;g) = first(f);first(g)  (ceFirstFusion)
    let f = TermData::op("f", vec![], &ArrSource::Native, None);
    let g = TermData::op("g", vec![], &ArrSource::Native, None);
    let lhs = TermData::first(TermData::seq(f.clone(), g.clone()))
        .to_term()
        .expect("TermData -> Term");
    let rhs = TermData::seq(TermData::first(f), TermData::first(g))
        .to_term()
        .expect("TermData -> Term");
    if law_equal(&lhs, &rhs) {
        LawCheckResult::Satisfied
    } else {
        LawCheckResult::Violated
    }
}

// ============================================================================
// 4. The Law Catalog (built-in law patterns)
// ============================================================================

/// The built-in law catalog: CutElim-proven structural law patterns.
///
/// All entries are CutElim-proven structural laws (the four portable
/// rewrites). Non-functor laws (roundtrip, associativity, sortedness) are
/// NOT in the catalog because they require semantic axioms that cannot be
/// discovered from wiring -- see the module docs.
pub fn builtin_law_catalog() -> Vec<LawPattern> {
    vec![
        LawPattern {
            name: "functor_identity".to_string(),
            description: "first(id) = id".to_string(),
            check: check_functor_identity,
        },
        LawPattern {
            name: "functor_composition".to_string(),
            description: "first(f >>> g) = first(f) >>> first(g)".to_string(),
            check: check_functor_composition,
        },
    ]
}

// ============================================================================
// 5. The Inference Engine
// ============================================================================

/// The status of an inferred law.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LawStatus {
    /// The law holds (CutElim-proven: both sides normalize equal).
    Satisfied,
    /// The law does not hold (normalization differs).
    Violated,
}

/// A law inferred for an arrow, without declaration.
#[derive(Debug, Clone)]
pub struct InferredLaw {
    /// Short name, e.g. "functor_identity".
    pub name: String,
    /// Human-readable statement, e.g. "first(id) = id".
    pub description: String,
    /// Whether the law holds for this arrow.
    pub status: LawStatus,
}

/// Infer which laws an arrow satisfies, without declaration. This is the
/// "primary mode" from ADR-0075, scoped to single-arrow laws.
///
/// The engine checks each law pattern in the catalog against the arrow:
///   - `NotApplicable` -> skipped (the law does not apply to this wiring).
///   - `Satisfied`     -> reported (the law holds, CutElim-proven).
///   - `Violated`      -> reported (the law applies but does not hold).
pub fn infer_laws(arrow: &Term) -> Vec<InferredLaw> {
    let catalog = builtin_law_catalog();
    let mut results = Vec::new();
    for pattern in &catalog {
        let result = (pattern.check)(arrow);
        match result {
            LawCheckResult::Satisfied => results.push(InferredLaw {
                name: pattern.name.clone(),
                description: pattern.description.clone(),
                status: LawStatus::Satisfied,
            }),
            LawCheckResult::Violated => results.push(InferredLaw {
                name: pattern.name.clone(),
                description: pattern.description.clone(),
                status: LawStatus::Violated,
            }),
            LawCheckResult::NotApplicable => {} // skip -- law does not apply
        }
    }
    results
}

// ============================================================================
// 6. Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // --- TermData thin wrappers (ADR-0103 Phase 6 migration) ---

    /// Convert `TermData` back to `Term` for APIs that require `Term`.
    fn td(t: TermData) -> Term {
        t.to_term().expect("TermData -> Term conversion")
    }

    /// Native op without a literal payload (mirrors `TermData::op`).
    fn op_native(name: &str, args: Vec<TermData>) -> TermData {
        if name == "const" && args.is_empty() {
            TermData::arr(Value::Null)
        } else {
            TermData::op(name, args, &ArrSource::Native, None)
        }
    }

    /// Native op with a literal payload (mirrors `TermData::op`).
    fn op_lit(name: &str, args: Vec<TermData>, lit: impl Into<Value>) -> TermData {
        if name == "const" && args.is_empty() {
            TermData::arr(lit)
        } else {
            TermData::op(name, args, &ArrSource::Native, Some(lit.into()))
        }
    }

    /// Foreign op (mirrors `TermData::op`).
    fn op_foreign(name: &str, args: Vec<TermData>) -> TermData {
        TermData::op(name, args, &ArrSource::Foreign(name.to_string()), None)
    }

    /// Sequential composition (mirrors `TermData::seq`).
    fn seq(fst: TermData, snd: TermData) -> TermData {
        TermData::seq(fst, snd)
    }

    /// First (mirrors `TermData::first`).
    fn first(inner: TermData) -> TermData {
        TermData::first(inner)
    }

    /// Choice routing (mirrors `TermData::choice`).
    fn choice(l: TermData, r: TermData) -> TermData {
        TermData::choice(l, r)
    }

    /// Loop feedback (mirrors `TermData::loop_feedback`).
    fn loop_feedback(body: TermData) -> TermData {
        TermData::loop_feedback(body)
    }

    fn id() -> TermData {
        op_native("id", vec![])
    }
    fn f() -> TermData {
        op_native("f", vec![])
    }
    fn g() -> TermData {
        op_native("g", vec![])
    }

    #[test]
    fn is_id_recognizes_identity_arrow() {
        assert!(is_id(&td(op_native("id", vec![]))));
        // A non-identity op is not the identity arrow.
        assert!(!is_id(&td(op_native("add", vec![]))));
        // An identity with args is not the bare identity arrow.
        assert!(!is_id(&td(op_native("id", vec![op_native("x", vec![])]))));
        // A foreign "id" is not the native identity arrow.
        assert!(!is_id(&td(op_foreign("id", vec![]))));
        // An identity with a literal payload is not the bare identity arrow.
        assert!(!is_id(&td(op_lit("id", vec![], 42))));
    }

    #[test]
    fn normalize_ce_id_left() {
        // Seq(Id, f) ==> f  (ceIdLeft)
        let s = td(seq(id(), f()));
        assert_eq!(normalize(&s, NORMALIZE_FUEL), td(f()));
    }

    #[test]
    fn normalize_ce_id_right() {
        // Seq(f, Id) ==> f  (ceIdRight)
        let s = td(seq(f(), id()));
        assert_eq!(normalize(&s, NORMALIZE_FUEL), td(f()));
    }

    #[test]
    fn normalize_ce_first_id() {
        // First(Id) ==> Id  (ceFirstId)
        let s = td(first(id()));
        assert_eq!(normalize(&s, NORMALIZE_FUEL), td(id()));
    }

    #[test]
    fn normalize_ce_first_fusion() {
        // Seq(First(f), First(g)) ==> First(Seq(f, g))  (ceFirstFusion)
        let s = td(seq(first(f()), first(g())));
        assert_eq!(normalize(&s, NORMALIZE_FUEL), td(first(seq(f(), g()))));
    }

    #[test]
    fn normalize_cascade_completes_in_one_pass() {
        // Seq(First(id), First(id)) -> First(Seq(id, id)) -> First(id) -> id
        let s = td(seq(first(id()), first(id())));
        assert_eq!(normalize(&s, NORMALIZE_FUEL), td(id()));
    }

    #[test]
    fn normalize_is_idempotent_on_normal_form() {
        let s = td(first(seq(f(), g())));
        let once = normalize(&s, NORMALIZE_FUEL);
        let twice = normalize(&once, NORMALIZE_FUEL);
        assert_eq!(once, twice);
    }

    #[test]
    fn law_equal_first_id_equals_id() {
        assert!(law_equal(&td(first(id())), &td(id())));
    }

    #[test]
    fn law_equal_first_fusion() {
        // Seq(First(f), First(g)) === First(Seq(f, g))
        let lhs = td(seq(first(f()), first(g())));
        let rhs = td(first(seq(f(), g())));
        assert!(law_equal(&lhs, &rhs));
    }

    #[test]
    fn law_equal_distinguishes_distinct_arrows() {
        // first(f) is not law_equal to f -- they do not normalize together.
        assert!(!law_equal(&td(first(f())), &td(f())));
    }

    #[test]
    fn uses_first_detects_first() {
        assert!(uses_first(&td(first(f()))));
    }

    #[test]
    fn uses_first_false_for_plain_arr() {
        assert!(!uses_first(&td(op_native("sort", vec![]))));
    }

    #[test]
    fn uses_first_detects_nested() {
        // Seq(First(f), g) uses first (nested, not at root).
        assert!(uses_first(&td(seq(first(f()), g()))));
    }

    #[test]
    fn uses_first_recurses_into_choice_and_loop() {
        assert!(uses_first(&td(choice(first(f()), g()))));
        assert!(uses_first(&td(loop_feedback(first(f())))));
        assert!(!uses_first(&td(choice(f(), g()))));
    }

    #[test]
    fn infer_laws_first_reports_both_functor_laws() {
        let inferred = infer_laws(&td(first(f())));
        // functor_identity (Satisfied) and functor_composition (Satisfied).
        assert_eq!(inferred.len(), 2);
        assert!(
            inferred
                .iter()
                .any(|l| l.name == "functor_identity" && l.status == LawStatus::Satisfied)
        );
        assert!(
            inferred
                .iter()
                .any(|l| l.name == "functor_composition" && l.status == LawStatus::Satisfied)
        );
    }

    #[test]
    fn infer_laws_plain_arr_reports_no_laws() {
        let inferred = infer_laws(&td(op_native("sort", vec![])));
        assert!(inferred.is_empty());
    }

    #[test]
    fn infer_laws_seq_of_firsts_reports_both() {
        let inferred = infer_laws(&td(seq(first(f()), first(g()))));
        assert_eq!(inferred.len(), 2);
        assert!(
            inferred
                .iter()
                .any(|l| l.name == "functor_identity" && l.status == LawStatus::Satisfied)
        );
        assert!(
            inferred
                .iter()
                .any(|l| l.name == "functor_composition" && l.status == LawStatus::Satisfied)
        );
    }

    #[test]
    fn infer_laws_roundtrip_reports_no_laws() {
        // Non-functor laws are NOT inferable: a serialize/deserialize
        // roundtrip is a semantic fact, not a CutElim-proven structural law.
        let s = td(seq(
            op_native("serialize", vec![]),
            op_native("deserialize", vec![]),
        ));
        let inferred = infer_laws(&s);
        assert!(inferred.is_empty());
    }

    #[test]
    fn builtin_law_catalog_has_two_portable_patterns() {
        let catalog = builtin_law_catalog();
        assert_eq!(catalog.len(), 2);
        let names: Vec<&str> = catalog.iter().map(|p| p.name.as_str()).collect();
        assert!(names.contains(&"functor_identity"));
        assert!(names.contains(&"functor_composition"));
        // The coproduct functor laws are NOT in the catalog (no `Left` in
        // `Term`).
        assert!(!names.contains(&"coproduct_functor_identity"));
        assert!(!names.contains(&"coproduct_functor_composition"));
    }
}
