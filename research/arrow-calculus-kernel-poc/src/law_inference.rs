// ADR-0076 Open Question #5 -- Rust-side prototype.
//
// Law INFERENCE for single-arrow laws: can the system INFER that an arrow
// satisfies a law (e.g. `map id = id`) without the user declaring it?
//
// This is ADR-0075's "primary mode" (trait inference) scoped to SINGLE-ARROW
// laws. Instead of requiring the user to write `law map_id: map id = id`, the
// system has a LIBRARY of known law patterns (the "law catalog") and checks
// each one against an arrow graph:
//
//   1. Structural match -- does the arrow's wiring match the law pattern's
//      expected structure? (e.g. functor laws need a `first`-shaped graph;
//      coproduct functor laws need a `left`-shaped graph.)
//   2. CutElim verify   -- do both sides of the law equation normalize to the
//      same form under CutElim?
//
// If both pass, the system REPORTS: "this arrow satisfies law `functor_identity`"
// -- without the user declaring it.
//
// This mirrors the Lean mechanization (`TraitInference.lean`): the
// `UsesFirst` / `UsesLeft` structural recognizers trigger the check, and
// `CutElim` normalization discharges it. The inference theorem says: if a
// graph `G` uses `first`, then `G` satisfies the functor identity and
// composition laws -- without the law being declared.
//
// HONESTY NOTE (read me): inference works ONLY for the CutElim-proven
// STRUCTURAL fragment -- the functor laws (`first` identity/fusion) and the
// coproduct functor laws (`left` identity/fusion). These laws ARE the six
// CutElim rewrites, so the system can discover them from wiring alone.
// Non-functor laws (roundtrip, semigroup associativity, sortedness) CANNOT
// be inferred -- they are semantic facts about specific base arrows that
// require explicit axioms, which cannot be discovered from wiring. This
// matches `EquationalLawInference.lean`: structural recognition triggers the
// check, but an axiom discharges it. This prototype does not attempt to
// infer axiom-requiring laws; it documents the boundary explicitly.
//
// ADR: platform/project/adrs/0076-decoupled-trait-layer.md (Open Question #5)
//      platform/project/adrs/0075-traits-as-arrow-signatures.md (section 1:
//      "Primary mode: trait inference"; section 3: "The matching pipeline")
//
// Reuses the graph model, CutElim normalizer, and fingerprint from
// `trait_catalog.rs` (ADR-0075 substrate, unchanged) via the `#[path]`
// module-include trick -- the graph model is NOT duplicated.

// Pull in the existing trait catalog as a submodule. Its `fn main()` (and
// the demo helpers used only by that main) become dead code when included
// here -- `#[allow(dead_code)]` silences those expected warnings. The
// types/functions we use are live.
#[path = "trait_catalog.rs"]
#[allow(dead_code)]
mod trait_catalog;

#[allow(unused_imports)]
use trait_catalog::{law_equal, normalize, fingerprint, PolyGraph, Substitution, Ty, Unifier};

use std::fmt;

// ----------------------------------------------------------------------------
// Local graph-construction helpers.
//
// The helpers in `trait_catalog.rs` (`gid`/`gcomp`/`gfirst`/...) are
// module-private, so they are not visible through the `#[path]` include.
// We redefine the minimal constructor set here -- thin wrappers over the
// shared `PolyGraph` enum, NOT a duplication of the graph model.
// ----------------------------------------------------------------------------

fn gid() -> PolyGraph {
    PolyGraph::Id
}
fn gcomp(a: PolyGraph, b: PolyGraph) -> PolyGraph {
    PolyGraph::Comp(Box::new(a), Box::new(b))
}
fn gfirst(a: PolyGraph) -> PolyGraph {
    PolyGraph::First(Box::new(a))
}
fn gleft(a: PolyGraph) -> PolyGraph {
    PolyGraph::Left(Box::new(a))
}
fn garr(name: &str) -> PolyGraph {
    PolyGraph::Arr(name.to_string())
}

// ----------------------------------------------------------------------------
// Local type-construction helpers (same reason: the ones in
// `trait_catalog.rs` are module-private).
// ----------------------------------------------------------------------------

fn tv(s: &str) -> Ty {
    Ty::Var(s.to_string())
}
#[allow(dead_code)]
fn atom(s: &str) -> Ty {
    Ty::Atom(s.to_string())
}
fn sum(a: Ty, b: Ty) -> Ty {
    Ty::Sum(Box::new(a), Box::new(b))
}
#[allow(dead_code)]
fn arr_t(a: Ty, b: Ty) -> Ty {
    Ty::Arrow(Box::new(a), Box::new(b))
}
fn app_t(g: Ty, a: Ty) -> Ty {
    Ty::App(Box::new(g), Box::new(a))
}

// ============================================================================
// 1. Law Pattern (the inference target)
// ============================================================================
//
// A known law pattern that the system can check against any arrow. This is
// the "law catalog" -- a library of laws the system knows about. Given an
// arrow graph, the inference engine checks each pattern.
//
// This is the single-arrow analogue of ADR-0075's `CatalogEntry` (section 3).
// Where `CatalogEntry` bundles multiple laws under a named trait, a
// `LawPattern` is ONE law that attaches to ONE arrow -- no bundle needed
// (ADR-0076: "A single-arrow law needs no bundle").

/// A known law pattern that the system can check against any arrow.
/// This is the "law catalog" -- a library of laws the system knows about.
pub struct LawPattern {
    /// Short name, e.g. "functor_identity".
    pub name: String,
    /// Human-readable statement, e.g. "first(id) = id".
    pub description: String,
    /// The type shape this law applies to, e.g. `F<A> ~> F<B>` for functor
    /// laws. Uses `Ty::App` for higher-kinded types. This is the type-filter
    /// step of the ADR-0075 pipeline (section 3, step 1).
    pub type_shape: (Ty, Ty),
    /// The law check: given an arrow graph, decide whether the law applies
    /// and holds. This combines the structural-match step (ADR-0075 pipeline
    /// step 2) and the CutElim-verify step (step 3) into one function.
    pub check: fn(&PolyGraph) -> LawCheckResult,
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

impl fmt::Display for LawCheckResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LawCheckResult::Satisfied => write!(f, "Satisfied"),
            LawCheckResult::Violated => write!(f, "Violated"),
            LawCheckResult::NotApplicable => write!(f, "NotApplicable"),
        }
    }
}

// ============================================================================
// 2. Structural Pattern Recognizers
// ============================================================================
//
// Mirrors `UsesFirst` / `UsesLeft` from `TraitInference.lean` (lines 35-37):
// structural pattern recognizers that detect whether a graph uses the
// `first` / `left` combinator. The inference theorem says: if a graph `G`
// uses `first`, then `G` satisfies the functor identity and composition laws
// -- without the law being declared. The recognition is purely from the
// graph's wiring structure.
//
// "Uses first" means the graph contains a `First(_)` node anywhere in its
// combinator tree. This is more general than "the top-level is First" -- it
// catches nested cases like `first(comp(first(f), g))` where the outer
// `first` is the trigger, and also `comp(first(f), arr("h"))` where `first`
// is not at the root.

/// Does the graph use the `first` combinator (product functoriality)
/// anywhere in its combinator tree? Mirrors `UsesFirst` in
/// `TraitInference.lean`.
fn uses_first(graph: &PolyGraph) -> bool {
    match graph {
        PolyGraph::Id | PolyGraph::Arr(_) => false,
        PolyGraph::First(_) => true,
        PolyGraph::Comp(a, b) => uses_first(a) || uses_first(b),
        PolyGraph::Left(a) => uses_first(a),
        PolyGraph::Loop(a) => uses_first(a),
        PolyGraph::Choice(a, b) => uses_first(a) || uses_first(b),
        PolyGraph::App(a) => uses_first(a),
    }
}

/// Does the graph use the `left` combinator (coproduct functoriality)
/// anywhere in its combinator tree? Mirrors `UsesLeft` in
/// `TraitInference.lean`.
fn uses_left(graph: &PolyGraph) -> bool {
    match graph {
        PolyGraph::Id | PolyGraph::Arr(_) => false,
        PolyGraph::Left(_) => true,
        PolyGraph::Comp(a, b) => uses_left(a) || uses_left(b),
        PolyGraph::First(a) => uses_left(a),
        PolyGraph::Loop(a) => uses_left(a),
        PolyGraph::Choice(a, b) => uses_left(a) || uses_left(b),
        PolyGraph::App(a) => uses_left(a),
    }
}

// ============================================================================
// 3. Law Checking Functions
// ============================================================================
//
// For each law pattern, a function that:
//   1. Checks if the arrow has the right structure (e.g. uses `first` for
//      functor laws).
//   2. If yes, constructs both sides of the law equation.
//   3. Runs `law_equal(lhs, rhs)` (CutElim normalization).
//   4. Returns Satisfied / Violated / NotApplicable.
//
// The laws are UNIVERSAL: for ALL f, `first(id) = id` and
// `first(f;g) = first(f);first(g)`. These are CutElim rewrites (ceFirstId,
// ceFirstFusion) that always hold. The inference recognizes the STRUCTURE
// (the arrow uses `first`) and CONFIRMS the law via CutElim. The law is
// CutElim-proven, so for any `first`-shaped graph the check always returns
// Satisfied -- the structural recognition is what makes it INFERENCE rather
// than declaration.

/// Check the functor identity law: `first(id) = id` (ceFirstId).
///
/// If the arrow uses `first`, construct `lhs = first(id)`, `rhs = id`, and
/// verify via `law_equal`. The law is a CutElim rewrite, so it holds for any
/// `first`-shaped graph. The inference: "G uses first, therefore it
/// satisfies the functor identity law (by ceFirstId)."
fn check_functor_identity(arrow: &PolyGraph) -> LawCheckResult {
    if !uses_first(arrow) {
        return LawCheckResult::NotApplicable;
    }
    // functor identity: first(id) = id  (ceFirstId)
    let lhs = gfirst(gid());
    let rhs = gid();
    if law_equal(&lhs, &rhs) {
        LawCheckResult::Satisfied
    } else {
        LawCheckResult::Violated
    }
}

/// Check the functor composition law:
/// `first(f >>> g) = first(f) >>> first(g)` (ceFirstFusion).
///
/// If the arrow uses `first`, construct both sides with concrete base arrows
/// `f`, `g` and verify via `law_equal`. The law is a CutElim rewrite, so it
/// holds for any `first`-shaped graph. The inference: "G uses first,
/// therefore it satisfies the functor composition law (by ceFirstFusion)."
fn check_functor_composition(arrow: &PolyGraph) -> LawCheckResult {
    if !uses_first(arrow) {
        return LawCheckResult::NotApplicable;
    }
    // functor composition: first(f;g) = first(f);first(g)  (ceFirstFusion)
    let f = garr("f");
    let g = garr("g");
    let lhs = gfirst(gcomp(f.clone(), g.clone()));
    let rhs = gcomp(gfirst(f), gfirst(g));
    if law_equal(&lhs, &rhs) {
        LawCheckResult::Satisfied
    } else {
        LawCheckResult::Violated
    }
}

/// Check the coproduct functor identity law: `left(id) = id` (ceLeftId).
///
/// If the arrow uses `left`, construct `lhs = left(id)`, `rhs = id`, and
/// verify via `law_equal`. The law is a CutElim rewrite, so it holds for any
/// `left`-shaped graph.
fn check_coproduct_functor_identity(arrow: &PolyGraph) -> LawCheckResult {
    if !uses_left(arrow) {
        return LawCheckResult::NotApplicable;
    }
    // coproduct functor identity: left(id) = id  (ceLeftId)
    let lhs = gleft(gid());
    let rhs = gid();
    if law_equal(&lhs, &rhs) {
        LawCheckResult::Satisfied
    } else {
        LawCheckResult::Violated
    }
}

/// Check the coproduct functor composition law:
/// `left(f >>> g) = left(f) >>> left(g)` (ceLeftFusion).
///
/// If the arrow uses `left`, construct both sides with concrete base arrows
/// `f`, `g` and verify via `law_equal`.
fn check_coproduct_functor_composition(arrow: &PolyGraph) -> LawCheckResult {
    if !uses_left(arrow) {
        return LawCheckResult::NotApplicable;
    }
    // coproduct functor composition: left(f;g) = left(f);left(g)  (ceLeftFusion)
    let f = garr("f");
    let g = garr("g");
    let lhs = gleft(gcomp(f.clone(), g.clone()));
    let rhs = gcomp(gleft(f), gleft(g));
    if law_equal(&lhs, &rhs) {
        LawCheckResult::Satisfied
    } else {
        LawCheckResult::Violated
    }
}

// ============================================================================
// 4. The Law Catalog (built-in law patterns)
// ============================================================================
//
// The built-in law catalog: known law patterns the system can infer. This is
// the single-arrow analogue of ADR-0075's `populate_builtin_catalog`
// (section 3). Where the trait catalog bundles laws under named traits
// (Functor, CoproductFunctor, ...), the law catalog lists individual laws
// that attach to single arrows.
//
// All four patterns here are CutElim-proven structural laws (the six
// rewrites). Non-functor laws (roundtrip, associativity, sortedness) are
// NOT in the catalog because they require semantic axioms that cannot be
// discovered from wiring -- see the HONESTY NOTE at the top of this file.

/// The built-in law catalog: known law patterns the system can infer.
/// All entries are CutElim-proven structural laws.
pub fn builtin_law_catalog() -> Vec<LawPattern> {
    vec![
        LawPattern {
            name: "functor_identity".to_string(),
            description: "first(id) = id".to_string(),
            // F<A> ~> F<B> -- the higher-kinded functor type shape.
            type_shape: (app_t(tv("F"), tv("A")), app_t(tv("F"), tv("B"))),
            check: check_functor_identity,
        },
        LawPattern {
            name: "functor_composition".to_string(),
            description: "first(f >>> g) = first(f) >>> first(g)".to_string(),
            type_shape: (app_t(tv("F"), tv("A")), app_t(tv("F"), tv("B"))),
            check: check_functor_composition,
        },
        LawPattern {
            name: "coproduct_functor_identity".to_string(),
            description: "left(id) = id".to_string(),
            // (A + C) ~> (B + D) -- the coproduct functor type shape.
            type_shape: (sum(tv("A"), tv("C")), sum(tv("B"), tv("D"))),
            check: check_coproduct_functor_identity,
        },
        LawPattern {
            name: "coproduct_functor_composition".to_string(),
            description: "left(f >>> g) = left(f) >>> left(g)".to_string(),
            type_shape: (sum(tv("A"), tv("C")), sum(tv("B"), tv("D"))),
            check: check_coproduct_functor_composition,
        },
    ]
}

// ============================================================================
// 5. The Inference Engine
// ============================================================================
//
// Infer which laws an arrow satisfies, without declaration. This is the
// "primary mode" from ADR-0075 (section 1), scoped to single-arrow laws.
//
// The engine iterates over the law catalog and runs each pattern's check.
// Only Satisfied/Violated results are reported; NotApplicable is skipped
// (the law does not apply to this arrow's wiring).

/// The status of an inferred law.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LawStatus {
    /// The law holds (CutElim-proven: both sides normalize equal).
    Satisfied,
    /// The law does not hold (normalization differs).
    Violated,
}

impl fmt::Display for LawStatus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LawStatus::Satisfied => write!(f, "Satisfied"),
            LawStatus::Violated => write!(f, "Violated"),
        }
    }
}

/// A law inferred for an arrow, without declaration.
#[derive(Debug, Clone)]
pub struct InferredLaw {
    pub name: String,
    pub description: String,
    pub status: LawStatus,
}

impl fmt::Display for InferredLaw {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}  [{}]", self.name, self.description, self.status)
    }
}

/// Infer which laws an arrow satisfies, without declaration.
/// This is the "primary mode" from ADR-0075, scoped to single-arrow laws.
///
/// The engine checks each law pattern in the catalog against the arrow:
///   - NotApplicable -> skipped (the law does not apply to this wiring).
///   - Satisfied     -> reported (the law holds, CutElim-proven).
///   - Violated      -> reported (the law applies but does not hold).
pub fn infer_laws(arrow: &PolyGraph) -> Vec<InferredLaw> {
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

/// Helper: does the inference report a given law as Satisfied?
fn satisfies(inferred: &[InferredLaw], name: &str) -> bool {
    inferred
        .iter()
        .any(|l| l.name == name && l.status == LawStatus::Satisfied)
}

/// Helper: collect the names of all Satisfied inferred laws.
fn satisfied_names(inferred: &[InferredLaw]) -> Vec<String> {
    inferred
        .iter()
        .filter(|l| l.status == LawStatus::Satisfied)
        .map(|l| l.name.clone())
        .collect()
}

// ============================================================================
// 6. Declared-law verification (for the inference-vs-declaration comparison)
// ============================================================================
//
// To show that inference produces the same result as declaration, we
// reconstruct the DECLARED-law path inline: the user writes the law
// equations, and the system verifies them via `law_equal` (CutElim). This is
// the ADR-0076 "secondary mode" (declared laws) / ADR-0075 section 2. The
// `LawfulArrow::verify` in `decoupled_traits.rs` does exactly this; we
// replicate the core check here to avoid a cross-bin module dependency.
//
// The point: the SAME laws that `verify` checks (when declared) are the ones
// `infer_laws` discovers (when not declared). Inference matches declaration.

/// A declared law (the user wrote it). Verified via CutElim `law_equal`.
struct DeclaredLaw {
    name: String,
    lhs: PolyGraph,
    rhs: PolyGraph,
}

/// Verify a set of declared laws via CutElim. Returns the names of laws that
/// hold (lhs and rhs normalize equal). This mirrors `LawfulArrow::verify`
/// from `decoupled_traits.rs` (the axiom: None path).
fn verify_declared_laws(laws: &[DeclaredLaw]) -> Vec<String> {
    laws.iter()
        .filter(|law| law_equal(&law.lhs, &law.rhs))
        .map(|law| law.name.clone())
        .collect()
}

/// The functor laws as a user would DECLARE them (ADR-0076 section 1):
///   law map_id:    first(id)        = id
///   law map_comp:  first(f >>> g)   = first(f) >>> first(g)
fn declared_functor_laws() -> Vec<DeclaredLaw> {
    vec![
        DeclaredLaw {
            name: "functor_identity".to_string(),
            lhs: gfirst(gid()),
            rhs: gid(),
        },
        DeclaredLaw {
            name: "functor_composition".to_string(),
            lhs: gfirst(gcomp(garr("f"), garr("g"))),
            rhs: gcomp(gfirst(garr("f")), gfirst(garr("g"))),
        },
    ]
}

/// The coproduct functor laws as a user would DECLARE them:
///   law left_id:    left(id)        = id
///   law left_comp:  left(f >>> g)   = left(f) >>> left(g)
fn declared_coproduct_functor_laws() -> Vec<DeclaredLaw> {
    vec![
        DeclaredLaw {
            name: "coproduct_functor_identity".to_string(),
            lhs: gleft(gid()),
            rhs: gid(),
        },
        DeclaredLaw {
            name: "coproduct_functor_composition".to_string(),
            lhs: gleft(gcomp(garr("f"), garr("g"))),
            rhs: gcomp(gleft(garr("f")), gleft(garr("g"))),
        },
    ]
}

// ============================================================================
// 7. Demo + Tests
// ============================================================================

fn print_section(title: &str) {
    println!();
    println!("=== {} ===", title);
}

fn print_inferred(label: &str, arrow: &PolyGraph) {
    let inferred = infer_laws(arrow);
    println!("  arrow : {}", arrow);
    if inferred.is_empty() {
        println!("  {} -> no laws applicable (NotApplicable for all patterns)", label);
    } else {
        for law in &inferred {
            println!("  {} -> {}", label, law);
        }
    }
}

fn main() {
    print_section("ADR-0076 OQ#5 prototype: Law Inference for Single-Arrow Laws");
    println!("Can the system INFER that an arrow satisfies a law without declaration?");
    println!("This is ADR-0075's 'primary mode' (trait inference) scoped to single arrows.");
    println!();
    println!("Law catalog (built-in, all CutElim-proven structural laws):");
    for p in builtin_law_catalog() {
        println!("  - {}: {}  [type: {} ~> {}]", p.name, p.description, p.type_shape.0, p.type_shape.1);
    }

    let f = garr("f");
    let g = garr("g");

    // ====================================================================
    // Demo 1: A first-shaped arrow (functor). The system discovers both
    // functor laws without the user declaring them.
    // ====================================================================
    print_section("Demo 1: first(f) -- functorial core (no law declared)");
    let map_graph = gfirst(f.clone());
    print_inferred("infer", &map_graph);
    // Should report: functor_identity (Satisfied), functor_composition (Satisfied)

    // ====================================================================
    // Demo 2: A left-shaped arrow (coproduct functor). The system discovers
    // both coproduct functor laws without declaration.
    // ====================================================================
    print_section("Demo 2: left(f) -- coproduct functorial core (no law declared)");
    let left_graph = gleft(f.clone());
    print_inferred("infer", &left_graph);
    // Should report: coproduct_functor_identity (Satisfied),
    //                coproduct_functor_composition (Satisfied)

    // ====================================================================
    // Demo 3: A non-functor arrow (bare arr). No laws applicable -- the
    // wiring does not match any law pattern.
    // ====================================================================
    print_section("Demo 3: arr(\"sort\") -- bare base arrow (no functor structure)");
    let bare = garr("sort");
    print_inferred("infer", &bare);
    // Should report: no laws (NotApplicable for all patterns)

    // ====================================================================
    // Demo 4: A complex graph: first(comp(first(f), g)) -- nested first.
    // The outer first triggers the functor law check.
    // ====================================================================
    print_section("Demo 4: first(comp(first(f), g)) -- nested first (complex graph)");
    let complex = gfirst(gcomp(gfirst(f.clone()), g.clone()));
    print_inferred("infer", &complex);
    // Should report: functor_identity (Satisfied), functor_composition (Satisfied)

    // ====================================================================
    // Demo 5: id -- identity is not first/left-shaped. No laws applicable.
    // ====================================================================
    print_section("Demo 5: id -- identity arrow (not first/left-shaped)");
    print_inferred("infer", &gid());
    // Should report: no laws

    // ====================================================================
    // Demo 6: A graph that uses BOTH first and left -- satisfies all four
    // laws. Shows multi-match (ADR-0075 section 3: a graph can satisfy
    // multiple law patterns).
    // ====================================================================
    print_section("Demo 6: comp(first(f), left(g)) -- uses both first AND left");
    let both = gcomp(gfirst(f.clone()), gleft(g.clone()));
    print_inferred("infer", &both);
    // Should report: all four laws (Satisfied)

    // ====================================================================
    // Demo 7: Inference vs Declaration. Show that inference produces the
    // SAME result as declaration -- the primary mode (inference) and the
    // secondary mode (declaration) agree.
    // ====================================================================
    print_section("Demo 7: Inference (primary mode) vs Declaration (secondary mode)");
    println!("The same laws the system DISCOVERS (inference) are the ones the");
    println!("user would DECLARE (declaration). Both are CutElim-proven.");

    // --- Declared path: user writes the functor laws, system verifies ---
    println!();
    println!("--- Declared (user writes the law) ---");
    let declared = declared_functor_laws();
    for law in &declared {
        println!("  law {}: {} = {}", law.name, law.lhs, law.rhs);
    }
    let declared_verified = verify_declared_laws(&declared);
    println!("  verify (CutElim): verified = {:?}", declared_verified);

    // --- Inferred path: user writes nothing, system discovers the laws ---
    println!("--- Inferred (system discovers the law, no declaration) ---");
    let inferred = infer_laws(&map_graph);
    for law in &inferred {
        println!("  {}", law);
    }
    let inferred_satisfied = satisfied_names(&inferred);
    println!("  infer (CutElim): satisfied = {:?}", inferred_satisfied);

    // The two agree: the declared-verified laws == the inferred-satisfied laws.
    let mut declared_sorted = declared_verified.clone();
    declared_sorted.sort();
    let mut inferred_sorted = inferred_satisfied.clone();
    inferred_sorted.sort();
    assert_eq!(
        declared_sorted, inferred_sorted,
        "inference matches declaration: same laws, CutElim-proven"
    );
    println!();
    println!("  [ok] inference matches declaration: {:?} == {:?}", declared_sorted, inferred_sorted);
    println!("  The primary mode (inference) and secondary mode (declaration) agree.");

    // ====================================================================
    // Tests (assertions consolidated).
    // ====================================================================
    print_section("Tests");

    // --- Test 1: first(f) -> functor_identity + functor_composition ---
    let inf = infer_laws(&gfirst(garr("f")));
    assert!(satisfies(&inf, "functor_identity"), "first(f) satisfies functor_identity");
    assert!(satisfies(&inf, "functor_composition"), "first(f) satisfies functor_composition");
    assert!(
        !satisfies(&inf, "coproduct_functor_identity"),
        "first(f) does NOT satisfy coproduct functor identity"
    );
    assert!(
        !satisfies(&inf, "coproduct_functor_composition"),
        "first(f) does NOT satisfy coproduct functor composition"
    );
    println!("[pass] first(f) -> functor_identity + functor_composition (Satisfied)");

    // --- Test 2: left(f) -> coproduct_functor_identity + composition ---
    let inf = infer_laws(&gleft(garr("f")));
    assert!(satisfies(&inf, "coproduct_functor_identity"), "left(f) satisfies coproduct_functor_identity");
    assert!(satisfies(&inf, "coproduct_functor_composition"), "left(f) satisfies coproduct_functor_composition");
    assert!(!satisfies(&inf, "functor_identity"), "left(f) does NOT satisfy functor identity");
    assert!(!satisfies(&inf, "functor_composition"), "left(f) does NOT satisfy functor composition");
    println!("[pass] left(f) -> coproduct_functor_identity + composition (Satisfied)");

    // --- Test 3: arr("sort") -> no laws (NotApplicable for all) ---
    let inf = infer_laws(&garr("sort"));
    assert!(inf.is_empty(), "bare arr has no applicable laws");
    println!("[pass] arr(\"sort\") -> no laws (NotApplicable for all patterns)");

    // --- Test 4: first(comp(first(f), g)) -> functor laws (outer first) ---
    let inf = infer_laws(&gfirst(gcomp(gfirst(garr("f")), garr("g"))));
    assert!(satisfies(&inf, "functor_identity"), "nested first satisfies functor_identity");
    assert!(satisfies(&inf, "functor_composition"), "nested first satisfies functor_composition");
    println!("[pass] first(comp(first(f), g)) -> functor laws (outer first triggers)");

    // --- Test 5: id -> no laws ---
    let inf = infer_laws(&gid());
    assert!(inf.is_empty(), "id has no applicable laws");
    println!("[pass] id -> no laws (not first/left-shaped)");

    // --- Test 6: comp(first(f), left(g)) -> all four laws (multi-match) ---
    let inf = infer_laws(&gcomp(gfirst(garr("f")), gleft(garr("g"))));
    assert!(satisfies(&inf, "functor_identity"), "comp(first,left) satisfies functor_identity");
    assert!(satisfies(&inf, "functor_composition"), "comp(first,left) satisfies functor_composition");
    assert!(satisfies(&inf, "coproduct_functor_identity"), "comp(first,left) satisfies coproduct_functor_identity");
    assert!(satisfies(&inf, "coproduct_functor_composition"), "comp(first,left) satisfies coproduct_functor_composition");
    println!("[pass] comp(first(f), left(g)) -> all four laws (multi-match)");

    // --- Test 7: inference matches declaration (functor laws) ---
    let declared_verified = verify_declared_laws(&declared_functor_laws());
    let inferred_satisfied = satisfied_names(&infer_laws(&gfirst(garr("f"))));
    let mut d = declared_verified.clone();
    d.sort();
    let mut i = inferred_satisfied.clone();
    i.sort();
    assert_eq!(d, i, "inference matches declaration for functor laws");
    println!("[pass] inference matches declaration: functor laws {:?} == {:?}", d, i);

    // --- Test 8: inference matches declaration (coproduct functor laws) ---
    let declared_verified = verify_declared_laws(&declared_coproduct_functor_laws());
    let inferred_satisfied = satisfied_names(&infer_laws(&gleft(garr("f"))));
    let mut d = declared_verified.clone();
    d.sort();
    let mut i = inferred_satisfied.clone();
    i.sort();
    assert_eq!(d, i, "inference matches declaration for coproduct functor laws");
    println!("[pass] inference matches declaration: coproduct functor laws {:?} == {:?}", d, i);

    // --- Test 9: the law catalog has exactly 4 CutElim-proven patterns ---
    let catalog = builtin_law_catalog();
    assert_eq!(catalog.len(), 4, "exactly 4 law patterns (2 functor + 2 coproduct)");
    for p in &catalog {
        // Every pattern in the catalog is CutElim-proven (structural).
        // Non-functor laws are NOT here -- they require axioms.
        assert!(
            p.name.contains("functor"),
            "all catalog patterns are functor laws (CutElim-proven structural): {}",
            p.name
        );
    }
    println!("[pass] law catalog has 4 CutElim-proven structural patterns (no axiom laws)");

    // --- Test 10: non-functor laws are NOT inferable (honesty boundary) ---
    // The roundtrip law (serialize >>> deserialize = id) is a semantic fact
    // about opaque base arrows. It is NOT a CutElim rewrite and CANNOT be
    // discovered from wiring. The law catalog does not contain it, and
    // infer_laws on a serialize/deserialize graph returns no laws.
    let serialize = gcomp(garr("serialize"), garr("deserialize"));
    let inf = infer_laws(&serialize);
    assert!(
        inf.is_empty(),
        "roundtrip law is NOT inferable (requires axiom, not in catalog)"
    );
    // Confirm: law_equal does NOT hold for the roundtrip equation (the base
    // arrows are opaque -- CutElim cannot simplify them).
    assert!(
        !law_equal(&serialize, &gid()),
        "roundtrip is NOT CutElim-proven (serialize/deserialize are opaque)"
    );
    println!("[pass] roundtrip law NOT inferable (axiom-requiring, not CutElim-proven)");
    println!("       -> non-functor laws CANNOT be discovered from wiring (honesty boundary)");

    // --- Test 11: structural recognizers (UsesFirst / UsesLeft) ---
    assert!(uses_first(&gfirst(garr("f"))), "uses_first: first(f)");
    assert!(uses_first(&gfirst(gcomp(gfirst(garr("f")), garr("g")))), "uses_first: nested first");
    assert!(uses_first(&gcomp(gfirst(garr("f")), garr("h"))), "uses_first: first in comp");
    assert!(!uses_first(&garr("f")), "uses_first: bare arr is false");
    assert!(!uses_first(&gid()), "uses_first: id is false");
    assert!(!uses_first(&gleft(garr("f"))), "uses_first: left(f) is false");
    assert!(uses_left(&gleft(garr("f"))), "uses_left: left(f)");
    assert!(uses_left(&gcomp(gfirst(garr("f")), gleft(garr("g")))), "uses_left: left in comp");
    assert!(!uses_left(&gfirst(garr("f"))), "uses_left: first(f) is false");
    println!("[pass] structural recognizers (UsesFirst / UsesLeft) match Lean");

    print_section("All tests passed");
    println!();
    println!("Summary:");
    println!("  Inferable (CutElim-proven structural laws):");
    println!("    - functor_identity:        first(id) = id              (ceFirstId)");
    println!("    - functor_composition:     first(f;g) = first(f);first(g) (ceFirstFusion)");
    println!("    - coproduct_functor_identity:    left(id) = id          (ceLeftId)");
    println!("    - coproduct_functor_composition: left(f;g) = left(f);left(g) (ceLeftFusion)");
    println!("  NOT inferable (axiom-requiring semantic laws):");
    println!("    - roundtrip:     serialize >>> deserialize = id  (needs axiom hinv)");
    println!("    - associativity: (f >>> g) >>> h = f >>> (g >>> h) (semantic)");
    println!("    - sortedness:    Sorted(sort(x))                   (semantic)");
    println!();
    println!("Answer to ADR-0076 OQ#5: single-arrow laws CAN be inferred for the");
    println!("CutElim-proven structural fragment (functor + coproduct functor).");
    println!("Non-functor laws cannot -- they need axioms, undiscoverable from wiring.");
    println!("This is ADR-0075's primary mode (inference) for the structural fragment;");
    println!("the secondary mode (declaration) remains necessary for axiom-requiring laws.");
}
