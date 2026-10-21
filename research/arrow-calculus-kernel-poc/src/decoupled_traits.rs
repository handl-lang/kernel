// ADR-0076 (Decoupled Trait Layer) -- Rust-side prototype.
//
// Implements the THREE independent, composable features from ADR-0076,
// layered ON TOP of the existing ADR-0075 substrate (graph model, CutElim
// normalizer, fingerprint, catalog storage):
//
//   1. Law on an arrow  -- standalone, attachable to any arrow. No bundle
//      needed for single-operation laws. `=` means extensional equality
//      (both sides normalize equal under CutElim, or via a semantic axiom).
//   2. Bundle           -- a named record of arrows + laws over them. Only
//      needed for multi-operation laws (e.g. roundtrip needs serialize +
//      deserialize from the same impl). Without laws, just a record (sugar).
//   3. Handler          -- `handle ... with` scoped dependency injection.
//      Lexically scoped, nearest-wins. Law checking at the handle site.
//      Static = law-checked, dynamic = no law guarantee.
//
// The "trait" pattern is an EMERGENT SHAPE produced by combining all three,
// not a syntactic category. No `trait` keyword. No `impl` keyword.
//
// Reuses the graph model, CutElim normalizer, fingerprint, and storage from
// `trait_catalog.rs` (ADR-0075 substrate, unchanged) via the `#[path]`
// module-include trick -- the graph model is NOT duplicated.
//
// ADR: platform/project/adrs/0076-decoupled-trait-layer.md
//
// HONESTY NOTE (read me): `handle` here is a RUNTIME SIMULATION of what
// would be compile-time lexical scoping + law checking in the real
// language. The semantics demonstrated (scoped installation, nearest-wins
// lookup, law verification at the handle site, handlers-primary /
// catalog-fallback resolution) are the real design; only the enforcement
// TIMING differs (a runtime closure vs. a compile-time scope). This is
// documented inline at the `handle` function. The verification machinery
// itself (CutElim `law_equal`, axiom placeholders) is real and unchanged
// from ADR-0075.

// Pull in the existing trait catalog as a submodule. Its `fn main()` (and
// the demo helpers used only by that main) become dead code when included
// here -- `#[allow(dead_code)]` silences those expected warnings. The
// types/functions we use are live.
#[path = "trait_catalog.rs"]
#[allow(dead_code)]
mod trait_catalog;

#[allow(unused_imports)]
use trait_catalog::{
    CatalogEntry, EntryId, InMemoryStore, LawEquation, MatchedTrait, PolyGraph, PolySigEntry,
    PolyInfer, Substitution, TraitCatalogStore, Ty, Unifier, VerificationResult, fingerprint,
    law_equal, normalize, populate_builtin_catalog,
};

use std::collections::HashMap;
use std::fmt;

// ----------------------------------------------------------------------------
// Local graph-construction helpers.
//
// The helpers in `trait_catalog.rs` (`gid`/`gcomp`/`gfirst`/...) are
// module-private, so they are not visible through the `#[path]` include.
// We redefine the minimal constructor set here -- these are thin wrappers
// over the shared `PolyGraph` enum, NOT a duplication of the graph model.
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
#[allow(dead_code)]
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
fn atom(s: &str) -> Ty {
    Ty::Atom(s.to_string())
}
fn list(a: Ty) -> Ty {
    Ty::List(Box::new(a))
}
fn arr_t(a: Ty, b: Ty) -> Ty {
    Ty::Arrow(Box::new(a), Box::new(b))
}
#[allow(dead_code)]
fn app_t(g: Ty, a: Ty) -> Ty {
    Ty::App(Box::new(g), Box::new(a))
}

// ============================================================================
// 1. Law on an arrow  (ADR-0076 section "Law on an arrow")
// ============================================================================
//
// A `law` is a standalone declaration that an arrow satisfies an equation.
// It attaches to any arrow -- no bundle required for single-operation laws.
//
// `=` inside a law context means extensional equality of arrows: both sides
// produce the same output for all inputs. This is verified by CutElim
// normalization (for structural laws, `axiom: None`) or by a semantic axiom
// (for non-functor laws, `axiom: Some(name)` -- assumed, not proven).

/// A law attached to a single arrow. The arrow satisfies the law if both
/// sides normalize to the same form under CutElim (for structural laws,
/// `axiom: None`) or via a semantic axiom (for non-functor laws,
/// `axiom: Some`).
#[derive(Debug, Clone)]
pub struct ArrowLaw {
    pub name: String,          // "map_id"
    pub lhs: PolyGraph,        // map id  (i.e. first(id))
    pub rhs: PolyGraph,        // id
    pub axiom: Option<String>, // None = CutElim-proven; Some("hinv") = needs axiom
}

impl fmt::Display for ArrowLaw {
    // ADR-0076: laws use `=` (not the old ADR-0075 `==`). The `law` context
    // disambiguates, so no special symbol is needed.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.axiom {
            None => write!(f, "law {}: {} = {}", self.name, self.lhs, self.rhs),
            Some(ax) => write!(f, "law {}: {} = {}   [axiom: {}]", self.name, self.lhs, self.rhs, ax),
        }
    }
}

/// An arrow with its attached laws.
#[derive(Debug, Clone)]
pub struct LawfulArrow {
    pub arrow: PolyGraph,
    pub laws: Vec<ArrowLaw>,
}

/// The outcome of verifying a set of laws.
#[derive(Debug, Clone, Default)]
pub struct VerificationReport {
    /// Laws confirmed by CutElim normalization (axiom: None, lhs/rhs
    /// normalize equal).
    pub verified: Vec<String>,
    /// Laws CutElim disproved (axiom: None, lhs/rhs normalize different).
    pub failed: Vec<String>,
    /// Laws discharged by a semantic axiom (axiom: Some) -- assumed, not
    /// proven by CutElim. Honest placeholder.
    pub placeholder: Vec<String>,
}

impl VerificationReport {
    pub fn is_clean(&self) -> bool {
        self.failed.is_empty()
    }

    pub fn summary(&self) -> String {
        format!(
            "verified={} failed={} placeholder={}",
            self.verified.len(),
            self.failed.len(),
            self.placeholder.len()
        )
    }
}

impl fmt::Display for VerificationReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "verified={:?} failed={:?} placeholder={:?}", self.verified, self.failed, self.placeholder)
    }
}

impl LawfulArrow {
    /// Verify all attached laws. Returns (verified, failed, placeholder).
    ///
    /// - `axiom: None`  -> verify via `law_equal(lhs, rhs)` (CutElim).
    /// - `axiom: Some`  -> mark as placeholder (the axiom is assumed, not
    ///   proven by CutElim). This matches EquationalLawInference.lean: the
    ///   law's `sound` field is an explicit hypothesis, not a `sorry`.
    pub fn verify(&self) -> VerificationReport {
        let mut report = VerificationReport::default();
        for law in &self.laws {
            match &law.axiom {
                None => {
                    if law_equal(&law.lhs, &law.rhs) {
                        report.verified.push(law.name.clone());
                    } else {
                        report.failed.push(law.name.clone());
                    }
                }
                Some(_) => {
                    report.placeholder.push(law.name.clone());
                }
            }
        }
        report
    }
}

impl fmt::Display for LawfulArrow {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "arrow: {}\n", self.arrow)?;
        for law in &self.laws {
            write!(f, "  {}\n", law)?;
        }
        Ok(())
    }
}

// ============================================================================
// 2. Bundle  (ADR-0076 section "Bundle")
// ============================================================================
//
// A bundle is a named record of arrows plus laws over them. It is only
// needed when a law spans multiple operations that must come from the same
// impl (same handler). Without laws, a bundle is just a record of arrows --
// sugar, no semantic power.

/// A law over multiple arrows in the bundle (e.g. roundtrip needs both
/// `serialize` and `deserialize` from the same impl).
#[derive(Debug, Clone)]
pub struct BundleLaw {
    pub name: String,          // "roundtrip"
    pub lhs: PolyGraph,        // serialize >>> deserialize
    pub rhs: PolyGraph,        // id
    pub axiom: Option<String>, // None = CutElim; Some = needs axiom
}

impl fmt::Display for BundleLaw {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.axiom {
            None => write!(f, "law {}: {} = {}", self.name, self.lhs, self.rhs),
            Some(ax) => write!(f, "law {}: {} = {}   [axiom: {}]", self.name, self.lhs, self.rhs, ax),
        }
    }
}

/// A bundle of arrows with shared laws. Only needed for multi-operation
/// laws. The bundle guarantees the arrows come from the same impl (same
/// handler). Without laws, it is just a record of arrows -- sugar.
#[derive(Debug, Clone)]
pub struct Bundle {
    pub name: String,                       // "Serializer"
    pub arrows: HashMap<String, PolyGraph>, // "serialize" -> graph
    pub laws: Vec<BundleLaw>,
}

impl Bundle {
    /// Verify all bundle laws. Same semantics as `LawfulArrow::verify`:
    /// `axiom: None` -> CutElim; `axiom: Some` -> placeholder.
    pub fn verify(&self) -> VerificationReport {
        let mut report = VerificationReport::default();
        for law in &self.laws {
            match &law.axiom {
                None => {
                    if law_equal(&law.lhs, &law.rhs) {
                        report.verified.push(law.name.clone());
                    } else {
                        report.failed.push(law.name.clone());
                    }
                }
                Some(_) => {
                    report.placeholder.push(law.name.clone());
                }
            }
        }
        report
    }
}

impl fmt::Display for Bundle {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "bundle {}: {} arrows, {} laws", self.name, self.arrows.len(), self.laws.len())?;
        for (k, g) in &self.arrows {
            write!(f, "\n  {} : {}", k, g)?;
        }
        for law in &self.laws {
            write!(f, "\n  {}", law)?;
        }
        Ok(())
    }
}

// ============================================================================
// 3. Handler  (ADR-0076 section "Handler")
// ============================================================================
//
// A handler injects an arrow or bundle at a scope boundary. This is
// dependency injection over effect handlers -- the single resolution
// mechanism. Lexically scoped, nearest-wins (like exception handlers).
// No coherence problem: scoping IS resolution.

/// A handler scope: installs arrows/bundles for use within a body.
/// Lexically scoped, nearest-wins (like exception handlers).
pub struct HandlerScope {
    /// Installed single arrows: "map" -> graph.
    arrows: HashMap<String, PolyGraph>,
    /// Installed bundles: "Serializer<JSON>" -> Bundle.
    bundles: HashMap<String, Bundle>,
    /// Parent scope (for nesting / shadowing).
    parent: Option<Box<HandlerScope>>,
}

impl HandlerScope {
    pub fn new() -> Self {
        HandlerScope {
            arrows: HashMap::new(),
            bundles: HashMap::new(),
            parent: None,
        }
    }

    /// Create a nested scope that shadows the parent (nearest-wins).
    pub fn child(&self) -> Self {
        HandlerScope {
            arrows: HashMap::new(),
            bundles: HashMap::new(),
            parent: Some(Box::new(self.clone())),
        }
    }

    pub fn install_arrow(&mut self, name: &str, graph: PolyGraph) {
        self.arrows.insert(name.to_string(), graph);
    }

    pub fn install_bundle(&mut self, key: &str, bundle: Bundle) {
        self.bundles.insert(key.to_string(), bundle);
    }

    /// Look up an arrow by name, nearest-wins (walk from current scope to
    /// parent). This is the resolution mechanism -- no catalog search needed
    /// when a handler is installed.
    pub fn lookup_arrow(&self, name: &str) -> Option<&PolyGraph> {
        if let Some(g) = self.arrows.get(name) {
            return Some(g);
        }
        self.parent.as_ref().and_then(|p| p.lookup_arrow(name))
    }

    /// Look up a bundle by key, nearest-wins.
    pub fn lookup_bundle(&self, key: &str) -> Option<&Bundle> {
        if let Some(b) = self.bundles.get(key) {
            return Some(b);
        }
        self.parent.as_ref().and_then(|p| p.lookup_bundle(key))
    }

    /// Iterate over the arrows installed at THIS scope (not parents).
    pub fn local_arrows(&self) -> impl Iterator<Item = (&String, &PolyGraph)> {
        self.arrows.iter()
    }

    /// Iterate over the bundles installed at THIS scope (not parents).
    pub fn local_bundles(&self) -> impl Iterator<Item = (&String, &Bundle)> {
        self.bundles.iter()
    }
}

impl Clone for HandlerScope {
    fn clone(&self) -> Self {
        HandlerScope {
            arrows: self.arrows.clone(),
            bundles: self.bundles.clone(),
            parent: self.parent.clone(),
        }
    }
}

// ============================================================================
// 4. `handle ... with` form  (ADR-0076 section "Handler")
// ============================================================================
//
// Execute a body with a handler installed. The handler's arrows/bundles are
// available within the body. Laws are checked at installation time.
//
// RUNTIME SIMULATION NOTE: in the real language, `handle ... with` is
// syntax with compile-time lexical scoping and compile-time law checking
// (a failed law check is a compile error). This prototype demonstrates the
// SEMANTICS with a runtime closure: a child scope is created, the install
// closure populates it, laws are verified and reported, then the body
// closure runs against the child scope. The semantics (scoped installation,
// nearest-wins, law verification at the handle site) are the real design;
// only the enforcement timing differs (runtime vs. compile-time).
//
// Law checking: bundles installed at this scope are verified here (they
// carry their own laws). Bare arrows carry no laws in the scope (the
// dynamic case); for the law+handler combo, the install closure verifies a
// `LawfulArrow` and then installs its bare `.arrow` -- demonstrating that
// the law was checked at the handle site.

/// Execute a body with a handler installed. The handler's arrows/bundles
/// are available within the body. Laws are checked at installation time.
pub fn handle<F, R>(
    scope: &HandlerScope,
    install: impl FnOnce(&mut HandlerScope),
    body: F,
) -> R
where
    F: FnOnce(&HandlerScope) -> R,
{
    let mut child = scope.child();
    install(&mut child);
    // Law checking at installation: verify all bundles installed at THIS
    // scope. (Bare arrows carry no laws in the scope -- the dynamic case.
    // For the law+handler combo the install closure verifies a LawfulArrow
    // before installing its bare arrow; see the demo.)
    for (key, bundle) in child.local_bundles() {
        let report = bundle.verify();
        if report.is_clean() {
            println!("  [handle] bundle {} law check: {} ({})", key, report.summary(), bundle.name);
        } else {
            println!("  [handle] bundle {} law check FAILED: {} ({})", key, report.summary(), bundle.name);
        }
    }
    body(&child)
}

// ============================================================================
// 5. Resolution: handlers primary, catalog search fallback
// ============================================================================
//
// 1. Primary: explicit handler -- names the impl, lexically scoped, no
//    ambiguity, laws checked at installation.
// 2. Fallback: catalog search -- when no handler is installed, search the
//    open trait catalog. One match = inject. Multiple = error (the compiler
//    never silently picks). Zero = NotFound.
// 3. No global coherence -- the problem is avoided by lexical scoping.

/// The result of resolving an arrow by name.
#[derive(Debug, Clone)]
pub enum Resolution {
    /// Found via handler (explicit). The arrow/bundle was installed in scope.
    Handler { name: String },
    /// Found via catalog search (fallback, no handler installed).
    /// One match = inject. Multiple = error (ambiguity).
    Catalog { matched: Vec<MatchedTrait> },
    /// Not found.
    NotFound,
}

impl fmt::Display for Resolution {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Resolution::Handler { name } => write!(f, "Handler({})", name),
            Resolution::Catalog { matched } => {
                if matched.len() == 1 {
                    write!(f, "Catalog(1 match: {})", matched[0].entry_name)
                } else {
                    let names: Vec<&str> = matched.iter().map(|m| m.entry_name.as_str()).collect();
                    write!(f, "Catalog(AMBIGUOUS: {} matches {:?})", matched.len(), names)
                }
            }
            Resolution::NotFound => write!(f, "NotFound"),
        }
    }
}

/// Resolve an arrow by name: check handler scope first (primary), then fall
/// back to catalog search (fallback).
///
/// - If the handler scope has the arrow -> `Resolution::Handler`.
/// - If not -> fall back to catalog search (`store.lookup_by_type_shape`).
///   One match = inject. Multiple = `Resolution::Catalog { matched }` (the
///   caller sees the ambiguity). Zero -> `NotFound`.
///
/// NOTE: the catalog fallback here uses the type-shape index (step 1 of the
/// ADR-0075 3-step pipeline). The returned `MatchedTrait` entries carry the
/// `cutelim_proven` flag but do NOT re-run CutElim law verification (that
/// is the handle site's job for explicit handlers; the catalog fallback is
/// the dynamic, no-law-guarantee path). Full law verification on a concrete
/// graph uses `infer_traits` (see `trait_catalog.rs`).
pub fn resolve_arrow(
    scope: &HandlerScope,
    name: &str,
    store: &mut impl TraitCatalogStore,
    graph_type: &Ty,
) -> Resolution {
    // Primary: explicit handler.
    if scope.lookup_arrow(name).is_some() {
        return Resolution::Handler {
            name: name.to_string(),
        };
    }

    // Fallback: catalog search by type shape.
    let candidates = store.lookup_by_type_shape(graph_type);
    if candidates.is_empty() {
        return Resolution::NotFound;
    }

    // Map catalog entries to MatchedTrait (law verification is the handle
    // site's job; the fallback reports candidates + count for disambiguation).
    let mut matched: Vec<MatchedTrait> = candidates
        .into_iter()
        .map(|(_, e)| MatchedTrait {
            entry_name: e.name.clone(),
            verified_laws: Vec::new(),
            placeholder_laws: Vec::new(),
            cutelim_proven: e.cutelim_proven,
        })
        .collect();
    matched.sort_by(|a, b| a.entry_name.cmp(&b.entry_name));
    Resolution::Catalog { matched }
}

// ============================================================================
// 6. Demo graphs + bundles
// ============================================================================

/// A `map` arrow represented by its functorial core: `first(f)` -- the
/// product-functorial action that lifts an element arrow `f` across a
/// product. This is the structural core CutElim reasons about (the six
/// rewrites include `ceFirstId` and `ceFirstFusion`). The full `map` over
/// lists is built from loop/first/choice/arr (see `map_shape_graph` in
/// `trait_catalog.rs`), but the functor LAWS attach to the `first`
/// structure, so this representation is what makes the laws CutElim-proven.
fn map_graph() -> PolyGraph {
    gfirst(garr("f"))
}

/// A `Serializer<JSON>` bundle: serialize + deserialize as opaque base
/// arrows, with a roundtrip law. The roundtrip law is NOT a CutElim rewrite
/// (serialize/deserialize are opaque base arrows) -- it is a semantic fact
/// requiring an axiom (`hinv`: the inverse relationship). This matches
/// EquationalLawInference.lean: non-functor laws need explicit axioms.
fn serializer_bundle(with_roundtrip: bool) -> Bundle {
    let mut arrows = HashMap::new();
    arrows.insert("serialize".to_string(), garr("serialize"));
    arrows.insert("deserialize".to_string(), garr("deserialize"));
    let laws = if with_roundtrip {
        vec![BundleLaw {
            name: "roundtrip".to_string(),
            lhs: gcomp(garr("serialize"), garr("deserialize")),
            rhs: gid(),
            axiom: Some("hinv".to_string()),
        }]
    } else {
        Vec::new()
    };
    Bundle {
        name: "Serializer".to_string(),
        arrows,
        laws,
    }
}

/// The functor laws attached to a map arrow (single-operation laws, no
/// bundle needed). Both are CutElim-proven (`axiom: None`).
fn functor_laws() -> Vec<ArrowLaw> {
    vec![
        ArrowLaw {
            name: "identity".to_string(),
            // map id = id  -->  first(id) = id  (ceFirstId)
            lhs: gfirst(gid()),
            rhs: gid(),
            axiom: None,
        },
        ArrowLaw {
            name: "composition".to_string(),
            // map (f >>> g) = map f >>> map g
            // -->  first(f;g) = first(f);first(g)  (ceFirstFusion)
            lhs: gfirst(gcomp(garr("f"), garr("g"))),
            rhs: gcomp(gfirst(garr("f")), gfirst(garr("g"))),
            axiom: None,
        },
    ]
}

fn print_section(title: &str) {
    println!();
    println!("=== {} ===", title);
}

// ============================================================================
// 7. Demo + Tests
// ============================================================================

fn main() {
    print_section("ADR-0076 prototype: Decoupled Trait Layer (Laws, Bundles, Handlers)");
    println!("Three independent features: law, bundle, handler.");
    println!("The 'trait' pattern emerges from combining all three.");

    // ====================================================================
    // Combo 1: Law alone -- a map arrow with functor laws, no bundle, no
    // handler. Verify the laws hold (CutElim).
    // ====================================================================
    print_section("Combo 1: Law alone (verified arrow, no bundle, no handler)");
    let map_lawful = LawfulArrow {
        arrow: map_graph(),
        laws: functor_laws(),
    };
    println!("{}", map_lawful);
    let report1 = map_lawful.verify();
    println!("verify: {}", report1);
    assert!(report1.verified.contains(&"identity".to_string()), "functor identity law verifies");
    assert!(report1.verified.contains(&"composition".to_string()), "functor composition law verifies");
    assert!(report1.failed.is_empty(), "no functor laws fail");
    println!("[ok] functor laws verified by CutElim (axiom: None -> Verified)");

    // ====================================================================
    // Combo 2: Bundle alone -- Serializer record, no laws, no handler.
    // Just a record of arrows (sugar).
    // ====================================================================
    print_section("Combo 2: Bundle alone (named record, no laws, no handler)");
    let serializer_record = serializer_bundle(false);
    println!("{}", serializer_record);
    let report2 = serializer_record.verify();
    println!("verify: {} (no laws to check)", report2.summary());
    assert!(report2.verified.is_empty(), "no laws -> no verified");
    assert!(report2.placeholder.is_empty(), "no laws -> no placeholder");
    assert!(report2.failed.is_empty(), "no laws -> no failed");
    println!("[ok] bundle without laws is just a record (verify returns empty)");

    // ====================================================================
    // Combo 3: Handler alone -- inject a bare arrow (no law, no bundle).
    // Dynamic -- no law guarantee.
    // ====================================================================
    print_section("Combo 3: Handler alone (effect injection, dynamic, no law)");
    let root_scope = HandlerScope::new();
    handle(&root_scope, |s| s.install_arrow("map", map_graph()), |s| {
        let found = s.lookup_arrow("map");
        println!("  installed bare arrow 'map' (no laws attached)");
        println!("  lookup 'map': {}", if found.is_some() { "found" } else { "NOT found" });
        assert!(found.is_some(), "handler-installed arrow is found in scope");
        println!("[ok] bare arrow injected via handler (dynamic, no law guarantee)");
    });

    // ====================================================================
    // Combo 4: Law + Bundle -- Serializer with roundtrip law.
    // Multi-operation law -- needs the bundle (serialize + deserialize from
    // the same impl). The roundtrip law is NOT CutElim-proven; it needs a
    // semantic axiom (hinv) -> placeholder (Unknown).
    // ====================================================================
    print_section("Combo 4: Law + Bundle (verified multi-op contract)");
    let serializer_lawful = serializer_bundle(true);
    println!("{}", serializer_lawful);
    let report4 = serializer_lawful.verify();
    println!("verify: {}", report4);
    assert!(report4.placeholder.contains(&"roundtrip".to_string()), "roundtrip is axiom placeholder");
    assert!(report4.verified.is_empty(), "roundtrip is NOT CutElim-proven");
    assert!(report4.failed.is_empty(), "axiom laws are placeholders, not failures");
    println!("[ok] roundtrip law is a semantic axiom placeholder (axiom: Some(hinv) -> Unknown)");

    // ====================================================================
    // Combo 5: Law + Handler -- inject a verified arrow.
    // The LawfulArrow is verified at the handle site, then its bare arrow is
    // installed. map is installed AND its laws were verified at installation.
    // ====================================================================
    print_section("Combo 5: Law + Handler (verified, injected arrow)");
    handle(&root_scope, |s| {
        // Law checking at the handle site: verify the LawfulArrow, then
        // install its bare arrow. In the real language this would be a
        // compile-time check; here it is a runtime verification.
        let lawful = LawfulArrow {
            arrow: map_graph(),
            laws: functor_laws(),
        };
        let r = lawful.verify();
        println!("  [handle] arrow 'map' law check: {} (verified at installation)", r.summary());
        assert!(r.is_clean(), "verified arrow must have no failed laws");
        s.install_arrow("map", lawful.arrow);
    }, |s| {
        let found = s.lookup_arrow("map");
        println!("  lookup 'map': {} (laws verified at handle site)", if found.is_some() { "found" } else { "NOT found" });
        assert!(found.is_some(), "verified arrow is installed in scope");
        println!("[ok] verified arrow injected via handler (law checked at handle site)");
    });

    // ====================================================================
    // Combo 6: Bundle + Handler -- inject a bundle (no laws, just the
    // record). serialize/deserialize available from scope.
    // ====================================================================
    print_section("Combo 6: Bundle + Handler (injected contract, no laws)");
    handle(&root_scope, |s| s.install_bundle("Serializer<JSON>", serializer_bundle(false)), |s| {
        let bundle = s.lookup_bundle("Serializer<JSON>");
        println!("  installed bundle 'Serializer<JSON>' (no laws)");
        println!("  lookup 'Serializer<JSON>': {}", if bundle.is_some() { "found" } else { "NOT found" });
        assert!(bundle.is_some(), "handler-installed bundle is found in scope");
        let b = bundle.unwrap();
        assert!(b.arrows.contains_key("serialize"), "serialize available from scope");
        assert!(b.arrows.contains_key("deserialize"), "deserialize available from scope");
        println!("[ok] bundle injected via handler (serialize/deserialize available)");
    });

    // ====================================================================
    // Combo 7: Law + Bundle + Handler -- the full "trait" pattern.
    // Inject a law-verified bundle. serialize/deserialize available, and the
    // roundtrip law is verified (as an axiom placeholder) at installation.
    // ====================================================================
    print_section("Combo 7: Law + Bundle + Handler (the 'trait' pattern)");
    handle(&root_scope, |s| s.install_bundle("Serializer<JSON>", serializer_bundle(true)), |s| {
        let bundle = s.lookup_bundle("Serializer<JSON>");
        println!("  installed law-verified bundle 'Serializer<JSON>'");
        println!("  lookup 'Serializer<JSON>': {}", if bundle.is_some() { "found" } else { "NOT found" });
        assert!(bundle.is_some(), "law-verified bundle is found in scope");
        let b = bundle.unwrap();
        assert!(b.arrows.contains_key("serialize"), "serialize available");
        assert!(b.arrows.contains_key("deserialize"), "deserialize available");
        assert_eq!(b.laws.len(), 1, "roundtrip law attached");
        println!("[ok] full trait pattern: bundle + roundtrip law verified at handle site");
    });

    // ====================================================================
    // Extra: Handler nesting + shadowing (inner handler overrides outer).
    // ====================================================================
    print_section("Extra: Handler nesting + shadowing (nearest-wins)");
    handle(&root_scope, |s| s.install_arrow("map", garr("outer_map")), |outer| {
        println!("  outer: installed 'map' = outer_map");
        assert_eq!(outer.lookup_arrow("map").unwrap(), &garr("outer_map"));
        // Inner handler shadows the outer 'map'.
        handle(outer, |s| s.install_arrow("map", garr("inner_map")), |inner| {
            println!("  inner: installed 'map' = inner_map (shadows outer)");
            assert_eq!(inner.lookup_arrow("map").unwrap(), &garr("inner_map"), "nearest-wins");
            // An arrow only in the outer scope is still visible from inner.
            handle(inner, |s| s.install_arrow("sort", garr("sort")), |innermost| {
                assert_eq!(innermost.lookup_arrow("map").unwrap(), &garr("inner_map"), "inner map still wins");
                assert_eq!(innermost.lookup_arrow("sort").unwrap(), &garr("sort"), "innermost sort found");
                println!("  innermost: 'map' = inner_map (inner wins), 'sort' = sort (local)");
            });
        });
        // After inner returns, outer still sees its own map.
        assert_eq!(outer.lookup_arrow("map").unwrap(), &garr("outer_map"), "outer map restored after inner scope exits");
        println!("  after inner exits: outer 'map' = outer_map (scope restored)");
    });
    println!("[ok] handler nesting + shadowing (nearest-wins, lexical scoping)");

    // ====================================================================
    // Extra: Resolution -- handlers primary, catalog search fallback.
    // ====================================================================
    print_section("Extra: Resolution (handlers primary, catalog fallback)");

    // Build the catalog (the ambient default handler set).
    let mut store = InMemoryStore::new();
    let n = populate_builtin_catalog(&mut store);
    println!("  built-in catalog entries: {}", n);

    // The map type [a] ~> [b] -- matches Functor, Mapping, AND Sorting via
    // the type filter (multi-match -> ambiguity).
    let map_type = arr_t(list(tv("a")), list(tv("b")));

    // (a) Handler installed -> Resolution::Handler (primary).
    handle(&root_scope, |s| s.install_arrow("map", map_graph()), |s| {
        let res = resolve_arrow(s, "map", &mut store, &map_type);
        println!("  resolve 'map' with handler installed: {}", res);
        assert!(matches!(res, Resolution::Handler { .. }), "handler takes priority over catalog");
        println!("  [ok] handler found -> Handler (primary)");
    });

    // (b) No handler installed -> catalog search fallback. The map type
    // matches multiple entries (Functor, Mapping, Sorting) -> ambiguity
    // error (the compiler never silently picks).
    let res_ambig = resolve_arrow(&root_scope, "map", &mut store, &map_type);
    println!("  resolve 'map' with NO handler (catalog fallback): {}", res_ambig);
    match &res_ambig {
        Resolution::Catalog { matched } => {
            assert!(matched.len() > 1, "map type matches multiple catalog entries");
            let names: Vec<&str> = matched.iter().map(|m| m.entry_name.as_str()).collect();
            println!("  catalog returned {} matches: {:?} (ambiguous -> error)", matched.len(), names);
        }
        _ => panic!("expected catalog fallback with multiple matches"),
    }
    println!("  [ok] multiple catalog matches -> ambiguity (never silently picks)");

    // (c) No handler, no catalog match -> NotFound.
    let weird_type = arr_t(atom("WeirdA"), atom("WeirdB"));
    let res_none = resolve_arrow(&root_scope, "weird", &mut store, &weird_type);
    println!("  resolve 'weird' (no match): {}", res_none);
    assert!(matches!(res_none, Resolution::NotFound), "no handler + no catalog match -> NotFound");
    println!("  [ok] no match -> NotFound");

    // (d) Single catalog match -> inject (one match = ok). CoproductFunctor
    // has type shape (A+C)~>(B+D); a matching query yields exactly one.
    let coproduct_type = arr_t(
        sum_t(tv("A"), tv("C")),
        sum_t(tv("B"), tv("D")),
    );
    let res_single = resolve_arrow(&root_scope, "left", &mut store, &coproduct_type);
    println!("  resolve 'left' (single catalog match): {}", res_single);
    match &res_single {
        Resolution::Catalog { matched } => {
            assert_eq!(matched.len(), 1, "coproduct type matches exactly one entry");
            assert_eq!(matched[0].entry_name, "CoproductFunctor");
        }
        _ => panic!("expected single catalog match"),
    }
    println!("  [ok] single catalog match -> inject (CoproductFunctor)");

    // ====================================================================
    // Extra: `=` in law display (not the old ADR-0075 `==`).
    // ====================================================================
    print_section("Extra: `=` in law display (ADR-0076 drops the `==` ceremony)");
    let law_display = ArrowLaw {
        name: "map_id".to_string(),
        lhs: gfirst(gid()),
        rhs: gid(),
        axiom: None,
    };
    let rendered = format!("{}", law_display);
    println!("  {}", rendered);
    assert!(rendered.contains("="), "law uses '='");
    assert!(!rendered.contains("\u{2261}"), "law does NOT use the old '\u{2261}' symbol");
    let axiom_law = BundleLaw {
        name: "roundtrip".to_string(),
        lhs: gcomp(garr("serialize"), garr("deserialize")),
        rhs: gid(),
        axiom: Some("hinv".to_string()),
    };
    println!("  {}", axiom_law);
    assert!(format!("{}", axiom_law).contains("[axiom: hinv]"), "axiom laws are annotated");
    println!("[ok] laws display with '=' (not '\u{2261}'); axiom laws annotated");

    // ====================================================================
    // Tests (assertions consolidated).
    // ====================================================================
    print_section("Tests");

    // --- Test 1: functor identity + composition verify via CutElim ---
    let r = LawfulArrow { arrow: map_graph(), laws: functor_laws() }.verify();
    assert_eq!(r.verified, vec!["identity".to_string(), "composition".to_string()], "functor laws verify via CutElim");
    assert!(r.failed.is_empty(), "no functor laws fail");
    println!("[pass] functor identity + composition verify via CutElim (axiom: None -> Verified)");

    // --- Test 2: non-functor law (roundtrip) is an axiom placeholder ---
    let r = serializer_bundle(true).verify();
    assert_eq!(r.placeholder, vec!["roundtrip".to_string()], "roundtrip is axiom placeholder");
    assert!(r.verified.is_empty(), "roundtrip NOT CutElim-proven");
    assert!(r.failed.is_empty(), "axiom law is a placeholder, not a failure");
    println!("[pass] roundtrip law with axiom: Some -> Unknown (placeholder)");

    // --- Test 3: bundle without laws verifies empty ---
    let r = serializer_bundle(false).verify();
    assert!(r.verified.is_empty() && r.placeholder.is_empty() && r.failed.is_empty(), "no laws -> empty report");
    println!("[pass] bundle without laws: verify returns empty");

    // --- Test 4: handler scope install + lookup ---
    let mut s = HandlerScope::new();
    s.install_arrow("map", map_graph());
    assert!(s.lookup_arrow("map").is_some(), "installed arrow is found");
    assert!(s.lookup_arrow("missing").is_none(), "missing arrow is None");
    s.install_bundle("Serializer<JSON>", serializer_bundle(false));
    assert!(s.lookup_bundle("Serializer<JSON>").is_some(), "installed bundle is found");
    assert!(s.lookup_bundle("missing").is_none(), "missing bundle is None");
    println!("[pass] handler scope install + lookup");

    // --- Test 5: handler nesting + shadowing ---
    let mut outer = HandlerScope::new();
    outer.install_arrow("map", garr("outer"));
    let inner = outer.child();
    assert_eq!(inner.lookup_arrow("map").unwrap(), &garr("outer"), "child sees parent arrow");
    let mut inner = outer.child();
    inner.install_arrow("map", garr("inner"));
    assert_eq!(inner.lookup_arrow("map").unwrap(), &garr("inner"), "inner shadows outer (nearest-wins)");
    assert_eq!(outer.lookup_arrow("map").unwrap(), &garr("outer"), "outer unchanged after inner shadow");
    println!("[pass] handler nesting + shadowing (nearest-wins)");

    // --- Test 6: resolution handler-found vs catalog-fallback vs NotFound ---
    let mut store2 = InMemoryStore::new();
    populate_builtin_catalog(&mut store2);
    let mt = arr_t(list(tv("a")), list(tv("b")));
    // Handler found.
    let mut hs = HandlerScope::new();
    hs.install_arrow("map", map_graph());
    assert!(matches!(resolve_arrow(&hs, "map", &mut store2, &mt), Resolution::Handler { .. }), "handler found");
    // Catalog fallback: multiple -> Catalog with >1.
    let res = resolve_arrow(&HandlerScope::new(), "map", &mut store2, &mt);
    match res {
        Resolution::Catalog { matched } => assert!(matched.len() > 1, "multiple catalog matches"),
        _ => panic!("expected catalog fallback"),
    }
    // NotFound.
    let weird = arr_t(atom("WeirdA"), atom("WeirdB"));
    assert!(matches!(resolve_arrow(&HandlerScope::new(), "weird", &mut store2, &weird), Resolution::NotFound), "not found");
    println!("[pass] resolution: Handler / Catalog(ambiguous) / NotFound");

    // --- Test 7: all 7 combos demonstrated without panic ---
    // (Each combo above ran its own assertion; this is the consolidated
    //  confirmation that the full composition table is exercised.)
    println!("[pass] all 7 composition combos demonstrated without panic");
    println!("  1. Law alone            -> verified arrow");
    println!("  2. Bundle alone         -> named record (sugar)");
    println!("  3. Handler alone        -> effect injection (dynamic)");
    println!("  4. Law + Bundle         -> verified multi-op contract");
    println!("  5. Law + Handler        -> verified, injected arrow");
    println!("  6. Bundle + Handler     -> injected contract");
    println!("  7. Law+Bundle+Handler   -> the 'trait' pattern");

    // --- Test 8: `=` in law display (not `==`) ---
    let law = ArrowLaw { name: "map_id".to_string(), lhs: gfirst(gid()), rhs: gid(), axiom: None };
    let rendered = format!("{}", law);
    assert!(rendered.contains("=") && !rendered.contains("\u{2261}"), "law uses '=' not '\u{2261}'");
    println!("[pass] law display uses '=' (not the old '\u{2261}')");

    print_section("All tests passed");
}

// ----------------------------------------------------------------------------
// Local helper used only by the resolution demo (sum type constructor).
// ----------------------------------------------------------------------------

fn sum_t(a: Ty, b: Ty) -> Ty {
    Ty::Sum(Box::new(a), Box::new(b))
}
