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
fn is_id(scheme: &Term) -> bool {
    matches!(
        scheme,
        Term::Op { name: op, args, source, lit }
            if op == "id"
                && args.is_empty()
                && matches!(source, ArrSource::Native)
                && lit.is_none()
    )
}

/// Try to apply ONE CutElim rewrite at the root of `scheme`. Returns the
/// rewritten scheme if a rule fired, else `None`.
///
/// The four portable rewrites:
///   - `ce_id_left`     : `Seq(id, G) ==> G`
///   - `ce_id_right`    : `Seq(G, id) ==> G`
///   - `ce_first_fusion`: `Seq(First(G), First(H)) ==> First(Seq(G, H))`
///   - `ce_first_id`    : `First(id) ==> id`
fn rewrite_root(scheme: &Term) -> Option<Term> {
    match scheme {
        // ce_id_left : Seq(id, G) ==> G
        Term::Seq { fst, snd } if is_id(fst) => Some((**snd).clone()),
        // ce_id_right : Seq(G, id) ==> G
        Term::Seq { fst, snd } if is_id(snd) => Some((**fst).clone()),
        // ce_first_fusion : Seq(First(G), First(H)) ==> First(Seq(G, H))
        Term::Seq { fst, snd }
            if matches!(**fst, Term::First { .. }) && matches!(**snd, Term::First { .. }) =>
        {
            match (&**fst, &**snd) {
                (Term::First { inner: g1 }, Term::First { inner: g2 }) => Some(Term::First {
                    inner: Box::new(Term::seq((**g1).clone(), (**g2).clone())),
                }),
                _ => None,
            }
        }
        // ce_first_id : First(id) ==> id
        Term::First { inner } if is_id(inner) => Some((**inner).clone()),
        _ => None,
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
fn rewrite_pass(scheme: &Term) -> (Term, bool) {
    // First recurse into children (bottom-up).
    let (g_norm, child_changed) = match scheme {
        Term::Op {
            name: op,
            args,
            source,
            lit,
        } => {
            let mut changed = false;
            let args2: Vec<Term> = args
                .iter()
                .map(|a| {
                    let (a2, c) = rewrite_pass(a);
                    changed = changed || c;
                    a2
                })
                .collect();
            (
                Term::Op {
                    name: op.clone(),
                    args: args2,
                    source: source.clone(),
                    lit: lit.clone(),
                },
                changed,
            )
        }
        Term::Seq { fst, snd } => {
            let (f2, cf) = rewrite_pass(fst);
            let (s2, cs) = rewrite_pass(snd);
            (
                Term::Seq {
                    fst: Box::new(f2),
                    snd: Box::new(s2),
                },
                cf || cs,
            )
        }
        Term::First { inner } => {
            let (i2, c) = rewrite_pass(inner);
            (
                Term::First {
                    inner: Box::new(i2),
                },
                c,
            )
        }
        Term::Choice { l, r } => {
            let (l2, cl) = rewrite_pass(l);
            let (r2, cr) = rewrite_pass(r);
            (
                Term::Choice {
                    l: Box::new(l2),
                    r: Box::new(r2),
                },
                cl || cr,
            )
        }
        Term::Loop { body } => {
            let (b2, c) = rewrite_pass(body);
            (Term::Loop { body: Box::new(b2) }, c)
        }
        Term::App { callee, args } => {
            let (c2, cc) = rewrite_pass(callee);
            let mut changed = cc;
            let args2: Vec<Term> = args
                .iter()
                .map(|a| {
                    let (a2, c) = rewrite_pass(a);
                    changed = changed || c;
                    a2
                })
                .collect();
            (
                Term::App {
                    callee: Box::new(c2),
                    args: args2,
                },
                changed,
            )
        }
        Term::Handle {
            body,
            target,
            impl_,
        } => {
            let (b2, cb) = rewrite_pass(body);
            let (i2, ci) = rewrite_pass(impl_);
            (
                Term::Handle {
                    body: Box::new(b2),
                    target: target.clone(),
                    impl_: Box::new(i2),
                },
                cb || ci,
            )
        }
        Term::Rewrite {
            source,
            target,
            witness,
        } => {
            let (s2, cs) = rewrite_pass(source);
            let (t2, ct) = rewrite_pass(target);
            (
                Term::Rewrite {
                    source: Box::new(s2),
                    target: Box::new(t2),
                    witness: witness.clone(),
                },
                cs || ct,
            )
        }
        Term::Arr { value } => (
            Term::Arr {
                value: value.clone(),
            },
            false,
        ),
        Term::Child { role } => (Term::Child { role: role.clone() }, false),
        Term::Iter {
            fuel,
            predicate,
            step,
            initial,
        } => {
            let (f2, cf) = rewrite_pass(fuel);
            let (p2, cp) = rewrite_pass(predicate);
            let (s2, cs) = rewrite_pass(step);
            let (i2, ci) = rewrite_pass(initial);
            (
                Term::Iter {
                    fuel: Box::new(f2),
                    predicate: Box::new(p2),
                    step: Box::new(s2),
                    initial: Box::new(i2),
                },
                cf || cp || cs || ci,
            )
        }
        Term::Path {
            endpoints: (a, b),
            witness,
        } => {
            let (a2, ca) = rewrite_pass(a);
            let (b2, cb) = rewrite_pass(b);
            let (w2, cw) = witness
                .as_ref()
                .map(|w| {
                    let (w2, c) = rewrite_pass(w);
                    (Some(Box::new(w2)), c)
                })
                .unwrap_or((None, false));
            (
                Term::Path {
                    endpoints: (Box::new(a2), Box::new(b2)),
                    witness: w2,
                },
                ca || cb || cw,
            )
        }
        Term::Equiv { a, b, path } => {
            let (a2, ca) = rewrite_pass(a);
            let (b2, cb) = rewrite_pass(b);
            let (p2, cp) = path
                .as_ref()
                .map(|p| {
                    let (p2, c) = rewrite_pass(p);
                    (Some(Box::new(p2)), c)
                })
                .unwrap_or((None, false));
            (
                Term::Equiv {
                    a: Box::new(a2),
                    b: Box::new(b2),
                    path: p2,
                },
                ca || cb || cp,
            )
        }
        Term::Const { value } => (
            Term::Const {
                value: value.clone(),
            },
            false,
        ),
        Term::Src { cell } => {
            let (c2, cc) = rewrite_pass(cell);
            (Term::Src { cell: Box::new(c2) }, cc)
        }
        Term::Tgt { cell } => {
            let (c2, cc) = rewrite_pass(cell);
            (Term::Tgt { cell: Box::new(c2) }, cc)
        }
        Term::RecordProj { record, field } => {
            let (r2, cr) = rewrite_pass(record);
            (
                Term::RecordProj {
                    record: Box::new(r2),
                    field: field.clone(),
                },
                cr,
            )
        }
        Term::RecordWith {
            record,
            field,
            value,
        } => {
            let (r2, cr) = rewrite_pass(record);
            let (v2, cv) = rewrite_pass(value);
            (
                Term::RecordWith {
                    record: Box::new(r2),
                    field: field.clone(),
                    value: Box::new(v2),
                },
                cr || cv,
            )
        }
        Term::Tag { tag, value } => {
            let (v2, cv) = rewrite_pass(value);
            (
                Term::Tag {
                    tag: tag.clone(),
                    value: Box::new(v2),
                },
                cv,
            )
        }
        Term::CellId { arrow } => {
            let (a2, ca) = rewrite_pass(arrow);
            (
                Term::CellId {
                    arrow: Box::new(a2),
                },
                ca,
            )
        }
        Term::CellCompV { first, second } => {
            let (f2, cf) = rewrite_pass(first);
            let (s2, cs) = rewrite_pass(second);
            (
                Term::CellCompV {
                    first: Box::new(f2),
                    second: Box::new(s2),
                },
                cf || cs,
            )
        }
        Term::Whisker { side, arrow, cell } => {
            let (a2, ca) = rewrite_pass(arrow);
            let (c2, cc) = rewrite_pass(cell);
            (
                Term::Whisker {
                    side: side.clone(),
                    arrow: Box::new(a2),
                    cell: Box::new(c2),
                },
                ca || cc,
            )
        }
        Term::Univalence { equiv } => {
            let (e2, ce) = rewrite_pass(equiv);
            (
                Term::Univalence {
                    equiv: Box::new(e2),
                },
                ce,
            )
        }
        Term::Glue { family, path } => {
            let (f2, cf) = rewrite_pass(family);
            let (p2, cp) = rewrite_pass(path);
            (
                Term::Glue {
                    family: Box::new(f2),
                    path: Box::new(p2),
                },
                cf || cp,
            )
        }
        Term::Fibrant { base, family } => {
            let (b2, cb) = rewrite_pass(base);
            let (f2, cf) = rewrite_pass(family);
            (
                Term::Fibrant {
                    base: Box::new(b2),
                    family: Box::new(f2),
                },
                cb || cf,
            )
        }
        Term::JElim { path, motive, base } => {
            let (p2, cp) = rewrite_pass(path);
            let (m2, cm) = rewrite_pass(motive);
            let (b2, cb) = rewrite_pass(base);
            (
                Term::JElim {
                    path: Box::new(p2),
                    motive: Box::new(m2),
                    base: Box::new(b2),
                },
                cp || cm || cb,
            )
        }
        Term::Refine { sort, predicate } => {
            let (s2, cs) = rewrite_pass(sort);
            let (p2, cp) = rewrite_pass(predicate);
            (
                Term::Refine {
                    sort: Box::new(s2),
                    predicate: Box::new(p2),
                },
                cs || cp,
            )
        }
        Term::Cobind { grade, body } => {
            let (g2, cg) = rewrite_pass(grade);
            let (b2, cb) = rewrite_pass(body);
            (
                Term::Cobind {
                    grade: Box::new(g2),
                    body: Box::new(b2),
                },
                cg || cb,
            )
        }
    };

    // Then try root rewrites on the (children-normalized) scheme. Repeat at
    // the root until no root rule fires.
    let mut cur = g_norm;
    let mut root_changed = false;
    loop {
        match rewrite_root(&cur) {
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
    let mut cur = scheme.clone();
    for _ in 0..fuel {
        let (next, changed) = rewrite_pass(&cur);
        if !changed {
            break;
        }
        cur = next;
    }
    cur
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

/// Does the scheme use the `First` combinator anywhere in its tree?
/// Mirrors `UsesFirst` from the Lean mechanization.
pub fn uses_first(scheme: &Term) -> bool {
    match scheme {
        Term::First { .. } => true,
        Term::Op { args, .. } => args.iter().any(uses_first),
        Term::Seq { fst, snd } => uses_first(fst) || uses_first(snd),
        Term::Choice { l, r } => uses_first(l) || uses_first(r),
        Term::Loop { body } => uses_first(body),
        Term::App { callee, args } => uses_first(callee) || args.iter().any(uses_first),
        Term::Handle { body, impl_, .. } => uses_first(body) || uses_first(impl_),
        Term::Rewrite { source, target, .. } => uses_first(source) || uses_first(target),
        Term::Arr { .. } | Term::Child { .. } => false,
        Term::Iter {
            fuel,
            predicate,
            step,
            initial,
        } => uses_first(fuel) || uses_first(predicate) || uses_first(step) || uses_first(initial),
        Term::Path {
            endpoints: (a, b),
            witness,
        } => {
            let mut r = uses_first(a) || uses_first(b);
            if let Some(w) = witness {
                r = r || uses_first(w);
            }
            r
        }
        Term::Equiv { a, b, path } => {
            let mut r = uses_first(a) || uses_first(b);
            if let Some(p) = path {
                r = r || uses_first(p);
            }
            r
        }
        Term::Const { .. } => false,
        Term::Src { cell } => uses_first(cell),
        Term::Tgt { cell } => uses_first(cell),
        Term::RecordProj { record, .. } => uses_first(record),
        Term::RecordWith { record, value, .. } => uses_first(record) || uses_first(value),
        Term::Tag { value, .. } => uses_first(value),
        Term::CellId { arrow } => uses_first(arrow),
        Term::CellCompV { first, second } => uses_first(first) || uses_first(second),
        Term::Whisker { arrow, cell, .. } => uses_first(arrow) || uses_first(cell),
        Term::Univalence { equiv } => uses_first(equiv),
        Term::Glue { family, path } => uses_first(family) || uses_first(path),
        Term::Fibrant { base, family } => uses_first(base) || uses_first(family),
        Term::JElim { path, motive, base } => {
            uses_first(path) || uses_first(motive) || uses_first(base)
        }
        Term::Refine { sort, predicate } => uses_first(sort) || uses_first(predicate),
        Term::Cobind { grade, body } => uses_first(grade) || uses_first(body),
    }
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
    let lhs = Term::first(Term::arr_native("id", vec![]));
    let rhs = Term::arr_native("id", vec![]);
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
    let f = Term::arr_native("f", vec![]);
    let g = Term::arr_native("g", vec![]);
    let lhs = Term::first(Term::seq(f.clone(), g.clone()));
    let rhs = Term::seq(Term::first(f), Term::first(g));
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

    fn id() -> Term {
        Term::arr_native("id", vec![])
    }
    fn f() -> Term {
        Term::arr_native("f", vec![])
    }
    fn g() -> Term {
        Term::arr_native("g", vec![])
    }

    #[test]
    fn is_id_recognizes_identity_arrow() {
        assert!(is_id(&Term::arr_native("id", vec![])));
        // A non-identity op is not the identity arrow.
        assert!(!is_id(&Term::arr_native("add", vec![])));
        // An identity with args is not the bare identity arrow.
        assert!(!is_id(&Term::arr_native(
            "id",
            vec![Term::arr_native("x", vec![])]
        )));
        // A foreign "id" is not the native identity arrow.
        assert!(!is_id(&Term::arr_foreign("id", vec![])));
        // An identity with a literal payload is not the bare identity arrow.
        assert!(!is_id(&Term::arr_native_lit("id", vec![], 42)));
    }

    #[test]
    fn normalize_ce_id_left() {
        // Seq(Id, f) ==> f  (ceIdLeft)
        let s = Term::seq(id(), f());
        assert_eq!(normalize(&s, NORMALIZE_FUEL), f());
    }

    #[test]
    fn normalize_ce_id_right() {
        // Seq(f, Id) ==> f  (ceIdRight)
        let s = Term::seq(f(), id());
        assert_eq!(normalize(&s, NORMALIZE_FUEL), f());
    }

    #[test]
    fn normalize_ce_first_id() {
        // First(Id) ==> Id  (ceFirstId)
        let s = Term::first(id());
        assert_eq!(normalize(&s, NORMALIZE_FUEL), id());
    }

    #[test]
    fn normalize_ce_first_fusion() {
        // Seq(First(f), First(g)) ==> First(Seq(f, g))  (ceFirstFusion)
        let s = Term::seq(Term::first(f()), Term::first(g()));
        assert_eq!(
            normalize(&s, NORMALIZE_FUEL),
            Term::first(Term::seq(f(), g()))
        );
    }

    #[test]
    fn normalize_cascade_completes_in_one_pass() {
        // Seq(First(id), First(id)) -> First(Seq(id, id)) -> First(id) -> id
        let s = Term::seq(Term::first(id()), Term::first(id()));
        assert_eq!(normalize(&s, NORMALIZE_FUEL), id());
    }

    #[test]
    fn normalize_is_idempotent_on_normal_form() {
        let s = Term::first(Term::seq(f(), g()));
        let once = normalize(&s, NORMALIZE_FUEL);
        let twice = normalize(&once, NORMALIZE_FUEL);
        assert_eq!(once, twice);
    }

    #[test]
    fn law_equal_first_id_equals_id() {
        assert!(law_equal(&Term::first(id()), &id()));
    }

    #[test]
    fn law_equal_first_fusion() {
        // Seq(First(f), First(g)) === First(Seq(f, g))
        let lhs = Term::seq(Term::first(f()), Term::first(g()));
        let rhs = Term::first(Term::seq(f(), g()));
        assert!(law_equal(&lhs, &rhs));
    }

    #[test]
    fn law_equal_distinguishes_distinct_arrows() {
        // first(f) is not law_equal to f -- they do not normalize together.
        assert!(!law_equal(&Term::first(f()), &f()));
    }

    #[test]
    fn uses_first_detects_first() {
        assert!(uses_first(&Term::first(f())));
    }

    #[test]
    fn uses_first_false_for_plain_arr() {
        assert!(!uses_first(&Term::arr_native("sort", vec![])));
    }

    #[test]
    fn uses_first_detects_nested() {
        // Seq(First(f), g) uses first (nested, not at root).
        assert!(uses_first(&Term::seq(Term::first(f()), g())));
    }

    #[test]
    fn uses_first_recurses_into_choice_and_loop() {
        assert!(uses_first(&Term::choice(Term::first(f()), g())));
        assert!(uses_first(&Term::loop_feedback(Term::first(f()))));
        assert!(!uses_first(&Term::choice(f(), g())));
    }

    #[test]
    fn infer_laws_first_reports_both_functor_laws() {
        let inferred = infer_laws(&Term::first(f()));
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
        let inferred = infer_laws(&Term::arr_native("sort", vec![]));
        assert!(inferred.is_empty());
    }

    #[test]
    fn infer_laws_seq_of_firsts_reports_both() {
        let inferred = infer_laws(&Term::seq(Term::first(f()), Term::first(g())));
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
        let s = Term::seq(
            Term::arr_native("serialize", vec![]),
            Term::arr_native("deserialize", vec![]),
        );
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
