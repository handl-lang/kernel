// ADR-0076 (Decoupled Trait Layer) Open Question #1 -- Rust-side prototype.
//
// Bundled-operations effect representation.
//
// ADR-0076 OQ#1 asks: "How does the effect system handle a bundle of
// operations as one handler?" The existing graph model (`PolyGraph` in
// `trait_catalog.rs`) has only concrete `Arr(name)` nodes -- there is no
// "unhandled operation" node, so a bundle cannot be intercepted as a single
// effect. The `decoupled_traits.rs` prototype has a `Bundle` (a static record
// of concrete arrows + laws) and a `HandlerScope` (a runtime map), but
// neither represents an unhandled operation IN THE GRAPH.
//
// This prototype adds the missing pieces, mirroring the `FreerArrow`
// inductive from `lean/ArrowMinimalityLib/StructuralInfo.lean` (which has an
// `op(o, k)` node) in Rust:
//
//   1. `EffectGraph` -- a NEW graph type that wraps `PolyGraph` and adds two
//      nodes:
//        * `Op(name)`         -- an unhandled operation reference
//                                (e.g. "Serializer.serialize").
//        * `Handle { body, bundle_name, impl_bundle }` -- a handler
//          elimination form. Semantics: rewrite every `Op(bundle_name.op)`
//          inside `body` to the concrete arrow from `impl_bundle`.
//   2. `effect_row` -- the set of unhandled operation names in a graph
//      (the "effect row"). A `Handle` removes the ops it covers.
//   3. `handle_eliminate` -- rewrite `Op` nodes to concrete arrows from a
//      bundle (single handler elimination).
//   4. `eliminate_all_handlers` -- recursively eliminate all handlers,
//      innermost first.
//   5. `verify_handler_bundle` -- law checking at the handle site (reuses
//      `Bundle::verify` from `decoupled_traits.rs`).
//   6. `poly_to_effect` / `effect_to_poly` -- convert between the concrete
//      `PolyGraph` (no ops) and the effectful `EffectGraph`.
//
// HONESTY NOTE (read me): this is a RUNTIME prototype of the effect
// representation. The real language would have `handle ... with` as syntax
// with compile-time handler elimination and a type-level effect row. This
// prototype demonstrates the SEMANTICS at runtime: an `Op` is an abstract
// operation, a `Handle` rewrites `Op`s to concrete arrows, and after full
// elimination the graph is a plain `PolyGraph` that CutElim can normalize.
// The effect row is a runtime `BTreeSet<String>`, not a type-level row.

// ----------------------------------------------------------------------------
// Module includes: share ONE `trait_catalog` / `decoupled_traits` instance.
//
// `decoupled_traits.rs` itself does `#[path = "trait_catalog.rs"] mod
// trait_catalog;` and then `use trait_catalog::{PolyGraph, ...}`. If we
// included BOTH files via separate `#[path]` mod declarations we would get
// TWO distinct `PolyGraph` types (one per module instance) -- and `Bundle`'s
// `arrows: HashMap<String, PolyGraph>` would use the nested one, making it
// incompatible with the one we import directly.
//
// To avoid that, we `include!` `decoupled_traits.rs` into a single module and
// then `pub use trait_catalog::*` from WITHIN that module. This way there is
// exactly one `trait_catalog` module (the one created by the included file),
// and its `PolyGraph` / `normalize` / `law_equal` / `fingerprint` / `Ty` are
// re-exported to us. The `fn main()` and demo helpers in the included file
// become dead code (a private `decoupled_traits::main`); `#[allow(dead_code)]`
// silences those expected warnings.
// ----------------------------------------------------------------------------

#[allow(dead_code)]
mod decoupled_traits {
    // Paste `decoupled_traits.rs` here. Its `#[path = "trait_catalog.rs"] mod
    // trait_catalog;` resolves relative to this file's directory (`src/`), so
    // it finds `src/trait_catalog.rs` -- the same file, included once.
    include!("decoupled_traits.rs");

    // `decoupled_traits.rs` privately imports `PolyGraph`, `normalize`, etc.
    // via `use trait_catalog::{PolyGraph, ...}`. Those private `use` bindings
    // shadow a plain `pub use trait_catalog::*` glob, so we cannot re-export
    // those names directly from this module. Instead we create a public
    // re-export submodule `tc` that accesses the (private-to-this-module)
    // `trait_catalog` module directly. Since `tc` is a descendant of
    // `decoupled_traits`, it can see `trait_catalog`; and since `tc` is
    // `pub`, the re-exported items are visible to the parent module.
    //
    // This is the ONE `PolyGraph` type that `Bundle` and friends use -- there
    // is no second copy.
    pub mod tc {
        pub use super::trait_catalog::*;
    }
}

// Reuse the Bundle / Law / Handler types from `decoupled_traits.rs`
// (ADR-0076 prototype, unchanged).
use decoupled_traits::{Bundle, BundleLaw, VerificationReport};
#[allow(unused_imports)]
use decoupled_traits::{ArrowLaw, LawfulArrow};

// Reuse the shared graph model / CutElim normalizer / fingerprint / types
// from `trait_catalog.rs` (ADR-0075 substrate, unchanged) -- re-exported
// through `decoupled_traits::tc` so there is ONE `PolyGraph` type, not two.
// This is the SAME `PolyGraph` that `Bundle.arrows` uses.
use decoupled_traits::tc::{fingerprint, law_equal, normalize, PolyGraph};
#[allow(unused_imports)]
use decoupled_traits::tc::Ty;

use std::collections::{BTreeSet, HashMap};
use std::fmt;

// ----------------------------------------------------------------------------
// Local graph-construction helpers.
//
// The helpers in `trait_catalog.rs` (`gid`/`gcomp`/`gfirst`/...) are
// module-private, so they are not visible through the re-export. We redefine
// the minimal constructor set here -- thin wrappers over the shared
// `PolyGraph` enum, NOT a duplication of the graph model.
// ----------------------------------------------------------------------------

fn gid() -> PolyGraph {
    PolyGraph::Id
}
fn gcomp(a: PolyGraph, b: PolyGraph) -> PolyGraph {
    PolyGraph::Comp(Box::new(a), Box::new(b))
}
fn garr(name: &str) -> PolyGraph {
    PolyGraph::Arr(name.to_string())
}

// Fuel budget for CutElim normalization (mirrors the constant in
// `trait_catalog.rs`, which is module-private and thus not visible here).
const NORMALIZE_FUEL: usize = 1024;

// ============================================================================
// 1. EffectGraph -- PolyGraph extended with Op and Handle nodes
// ============================================================================
//
// `PolyGraph` (in `trait_catalog.rs`) has: Id, Comp, First, Left, Loop, Arr,
// Choice, App. It has NO unhandled-operation node -- every `Arr(name)` is a
// concrete, already-resolved base arrow. This means a bundle cannot be
// intercepted as a single effect: there is nothing in the graph that says
// "this is an abstract operation, fill it in with a handler."
//
// `EffectGraph` mirrors the `FreerArrow` inductive from
// `lean/ArrowMinimalityLib/StructuralInfo.lean`, which has an `op(o, k)` node
// for unhandled operations. We add two nodes on top of the lifted PolyGraph:
//
//   * `Op(name)` -- an unhandled operation. "Serializer.serialize" means
//     "the serialize operation from the Serializer bundle, not yet handled."
//     The operation is abstract -- it has a name but no concrete graph. A
//     handler will replace it with a concrete arrow.
//
//   * `Handle { body, bundle_name, impl_bundle }` -- a handler elimination
//     form. Semantics: rewrite every `Op(bundle_name.op)` inside `body` to
//     the corresponding concrete arrow from `impl_bundle.arrows[op]`.
//
// We do NOT modify `PolyGraph` in `trait_catalog.rs` (that file is the
// shared ADR-0075 substrate and must stay untouched). Instead `EffectGraph`
// is a new type that re-expresses the same combinators plus the two new
// nodes. `poly_to_effect` / `effect_to_poly` bridge the two.

/// A graph that can contain unhandled operations (effects).
/// This extends `PolyGraph` with two new nodes:
/// - `Op`: an unhandled operation reference (e.g. "Serializer.serialize").
/// - `Handle`: a handler elimination form (`handle body with bundle = impl`).
#[derive(Clone, Debug)]
pub enum EffectGraph {
    // -- All the original PolyGraph nodes, lifted. --
    /// Polymorphic identity.
    Id,
    /// Composition: G ; H (cut in proof mode).
    Comp(Box<EffectGraph>, Box<EffectGraph>),
    /// First (x-functoriality): A ~> B  ==>  A x D ~> B x D.
    First(Box<EffectGraph>),
    /// Left (+-functoriality): A ~> B  ==>  A + D ~> B + D.
    Left(Box<EffectGraph>),
    /// Loop (trace/fixpoint): A x C ~> B x C  ==>  A ~> B.
    Loop(Box<EffectGraph>),
    /// Base arrow from the signature (concrete, already-resolved).
    Arr(String),
    /// Binary sum functoriality: A+B ~> C+D from A~>C, B~>D.
    Choice(Box<EffectGraph>, Box<EffectGraph>),
    /// ArrowApply placeholder. Opaque to CutElim.
    App(Box<EffectGraph>),

    // -- NEW nodes (the bundled-operations effect representation). --

    /// An unhandled operation. "Serializer.serialize" means "the serialize
    /// operation from the Serializer bundle, not yet handled." The operation
    /// is abstract -- it has a name but no concrete graph. A handler will
    /// replace it with a concrete arrow. This mirrors the `op(o, k)` node of
    /// `FreerArrow` in `StructuralInfo.lean`.
    Op(String),

    /// A handler elimination form: `handle body with bundle_name = impl_bundle`.
    /// Semantics: rewrite every `Op(bundle_name.op)` inside `body` to the
    /// corresponding concrete arrow from `impl_bundle.arrows[op]`. This is
    /// the "bundle as one handler" of ADR-0076 OQ#1: the whole bundle is
    /// intercepted as a single effect, and all its operations are resolved
    /// together from the same impl.
    Handle {
        body: Box<EffectGraph>,
        bundle_name: String,
        impl_bundle: Bundle, // the concrete bundle providing the arrows
    },
}

// `Bundle` (from `decoupled_traits.rs`) does not derive `PartialEq` (its
// `HashMap` of arrows is not compared), so we cannot derive `PartialEq` on
// `EffectGraph`. We implement it manually: two `Handle` nodes are equal when
// their `body` and `bundle_name` match (the `impl_bundle` is compared by
// name only -- two bundles with the same name and same body are considered
// equal for testing purposes).
impl PartialEq for EffectGraph {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (EffectGraph::Id, EffectGraph::Id) => true,
            (EffectGraph::Arr(a), EffectGraph::Arr(b)) => a == b,
            (EffectGraph::Op(a), EffectGraph::Op(b)) => a == b,
            (EffectGraph::Comp(a1, b1), EffectGraph::Comp(a2, b2)) => a1 == a2 && b1 == b2,
            (EffectGraph::First(a1), EffectGraph::First(a2)) => a1 == a2,
            (EffectGraph::Left(a1), EffectGraph::Left(a2)) => a1 == a2,
            (EffectGraph::Loop(a1), EffectGraph::Loop(a2)) => a1 == a2,
            (EffectGraph::Choice(a1, b1), EffectGraph::Choice(a2, b2)) => a1 == a2 && b1 == b2,
            (EffectGraph::App(a1), EffectGraph::App(a2)) => a1 == a2,
            (
                EffectGraph::Handle { body: b1, bundle_name: n1, impl_bundle: i1 },
                EffectGraph::Handle { body: b2, bundle_name: n2, impl_bundle: i2 },
            ) => b1 == b2 && n1 == n2 && i1.name == i2.name,
            _ => false,
        }
    }
}

impl fmt::Display for EffectGraph {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EffectGraph::Id => write!(f, "id"),
            EffectGraph::Comp(g, h) => write!(f, "({} ; {})", g, h),
            EffectGraph::First(g) => write!(f, "first({})", g),
            EffectGraph::Left(g) => write!(f, "left({})", g),
            EffectGraph::Loop(g) => write!(f, "loop({})", g),
            EffectGraph::Arr(name) => write!(f, "{}", name),
            EffectGraph::Choice(g, h) => write!(f, "choice({},{})", g, h),
            EffectGraph::App(g) => write!(f, "app({})", g),
            EffectGraph::Op(name) => write!(f, "op({})", name),
            EffectGraph::Handle { body, bundle_name, .. } => {
                write!(f, "handle({} with {})", body, bundle_name)
            }
        }
    }
}

// ----------------------------------------------------------------------------
// Local EffectGraph-construction helpers (thin wrappers).
// ----------------------------------------------------------------------------

fn eid() -> EffectGraph {
    EffectGraph::Id
}
fn ecomp(a: EffectGraph, b: EffectGraph) -> EffectGraph {
    EffectGraph::Comp(Box::new(a), Box::new(b))
}
fn eop(name: &str) -> EffectGraph {
    EffectGraph::Op(name.to_string())
}
fn earr(name: &str) -> EffectGraph {
    EffectGraph::Arr(name.to_string())
}
#[allow(dead_code)]
fn efirst(a: EffectGraph) -> EffectGraph {
    EffectGraph::First(Box::new(a))
}
fn ehandle(body: EffectGraph, bundle_name: &str, impl_bundle: Bundle) -> EffectGraph {
    EffectGraph::Handle {
        body: Box::new(body),
        bundle_name: bundle_name.to_string(),
        impl_bundle,
    }
}

// ============================================================================
// 2. Effect-row tracking
// ============================================================================
//
// The "effect row" is the set of unhandled operation names in a graph --
// which operations are still abstract (still `Op` nodes). This is the runtime
// analogue of a type-level effect row. A `Handle` removes the ops it covers
// (all `Op(bundle_name.*)`) from the row.

/// The set of unhandled operation names in a graph. This is the "effect row"
/// -- which operations are still abstract (`Op` nodes). A `Handle` removes
/// all ops matching its `bundle_name` prefix from the body's effect row.
pub fn effect_row(g: &EffectGraph) -> BTreeSet<String> {
    match g {
        EffectGraph::Op(name) => {
            let mut s = BTreeSet::new();
            s.insert(name.clone());
            s
        }
        EffectGraph::Comp(a, b) => effect_row(a).union(&effect_row(b)).cloned().collect(),
        EffectGraph::Choice(a, b) => effect_row(a).union(&effect_row(b)).cloned().collect(),
        EffectGraph::First(a) | EffectGraph::Left(a) | EffectGraph::Loop(a) | EffectGraph::App(a) => {
            effect_row(a)
        }
        EffectGraph::Handle { body, bundle_name, .. } => {
            // The handler removes all ops matching bundle_name from the
            // body's effect row. Ops from other bundles remain.
            let prefix = format!("{}.", bundle_name);
            let body_row = effect_row(body);
            body_row
                .into_iter()
                .filter(|op| !op.starts_with(&prefix))
                .collect()
        }
        // Id, Arr have no unhandled ops.
        EffectGraph::Id | EffectGraph::Arr(_) => BTreeSet::new(),
    }
}

/// Pretty-print an effect row as `{ op1, op2, ... }` (or `{}` if empty).
fn fmt_effect_row(row: &BTreeSet<String>) -> String {
    if row.is_empty() {
        "{}".to_string()
    } else {
        let items: Vec<&str> = row.iter().map(|s| s.as_str()).collect();
        format!("{{ {} }}", items.join(", "))
    }
}

// ============================================================================
// 3. Handler semantics: rewrite Op nodes to concrete arrows
// ============================================================================
//
// `handle_eliminate` is the core of the bundled-operations representation.
// It walks the graph and rewrites every `Op(bundle_name.op_name)` to the
// concrete arrow from `impl_bundle.arrows[op_name]` (lifted to an
// `EffectGraph` via `poly_to_effect`). Ops from other bundles are left
// alone. This is how a bundle is intercepted as a single effect: one
// `Handle` resolves ALL operations of that bundle together, from the same
// impl -- which is exactly what makes multi-operation laws (like roundtrip)
// meaningful.

/// Eliminate a single handler: rewrite every `Op(bundle_name.op_name)` in
/// the graph to the concrete arrow from `impl_bundle.arrows[op_name]`.
/// Returns the rewritten graph (with no `Op` nodes for that bundle). Ops
/// from other bundles are left untouched. Panics if the bundle does not
/// provide a referenced operation.
pub fn handle_eliminate(g: &EffectGraph, bundle_name: &str, impl_bundle: &Bundle) -> EffectGraph {
    let prefix = format!("{}.", bundle_name);
    match g {
        EffectGraph::Op(name) => {
            if name.starts_with(&prefix) {
                let op_name = &name[prefix.len()..];
                match impl_bundle.arrows.get(op_name) {
                    Some(concrete) => poly_to_effect(concrete), // lift PolyGraph -> EffectGraph
                    None => panic!(
                        "handler {} does not provide operation {}",
                        bundle_name, op_name
                    ),
                }
            } else {
                // Not our bundle -- leave the op abstract.
                EffectGraph::Op(name.clone())
            }
        }
        EffectGraph::Comp(a, b) => EffectGraph::Comp(
            Box::new(handle_eliminate(a, bundle_name, impl_bundle)),
            Box::new(handle_eliminate(b, bundle_name, impl_bundle)),
        ),
        EffectGraph::First(a) => {
            EffectGraph::First(Box::new(handle_eliminate(a, bundle_name, impl_bundle)))
        }
        EffectGraph::Left(a) => {
            EffectGraph::Left(Box::new(handle_eliminate(a, bundle_name, impl_bundle)))
        }
        EffectGraph::Loop(a) => {
            EffectGraph::Loop(Box::new(handle_eliminate(a, bundle_name, impl_bundle)))
        }
        EffectGraph::Choice(a, b) => EffectGraph::Choice(
            Box::new(handle_eliminate(a, bundle_name, impl_bundle)),
            Box::new(handle_eliminate(b, bundle_name, impl_bundle)),
        ),
        EffectGraph::App(a) => {
            EffectGraph::App(Box::new(handle_eliminate(a, bundle_name, impl_bundle)))
        }
        EffectGraph::Handle { body, bundle_name: inner_name, impl_bundle: inner_impl } => {
            // A nested handler inside the body. We recurse into its body so
            // that OUR bundle's ops (if any leaked through the inner handler)
            // are still rewritten. The inner Handle node itself is preserved
            // here; it will be eliminated by `eliminate_all_handlers` (or by
            // a subsequent `handle_eliminate` for the inner bundle).
            EffectGraph::Handle {
                body: Box::new(handle_eliminate(body, bundle_name, impl_bundle)),
                bundle_name: inner_name.clone(),
                impl_bundle: inner_impl.clone(),
            }
        }
        // Leaves: Id, Arr -- no ops to rewrite.
        EffectGraph::Id | EffectGraph::Arr(_) => g.clone(),
    }
}

// ============================================================================
// 4. Full handler elimination (eliminate ALL handlers, innermost first)
// ============================================================================
//
// `eliminate_all_handlers` recursively eliminates every `Handle` node in a
// graph, innermost first. For each `Handle`, it first eliminates any inner
// handlers in the body, then applies `handle_eliminate` for THIS handler.
// After full elimination, the graph has no `Handle` nodes and no `Op` nodes
// (provided every op was covered by some handler). It can then be converted
// back to a `PolyGraph` for CutElim normalization.

/// Recursively eliminate all handlers in a graph, innermost first. After
/// full elimination, the graph has no `Handle` nodes and no `Op` nodes (if
/// all ops were handled). Ops with no covering handler remain as `Op` nodes.
pub fn eliminate_all_handlers(g: &EffectGraph) -> EffectGraph {
    match g {
        EffectGraph::Handle { body, bundle_name, impl_bundle } => {
            // First eliminate any inner handlers in the body (innermost first).
            let body_eliminated = eliminate_all_handlers(body);
            // Then eliminate THIS handler: rewrite its ops to concrete arrows.
            handle_eliminate(&body_eliminated, bundle_name, impl_bundle)
        }
        EffectGraph::Comp(a, b) => EffectGraph::Comp(
            Box::new(eliminate_all_handlers(a)),
            Box::new(eliminate_all_handlers(b)),
        ),
        EffectGraph::First(a) => EffectGraph::First(Box::new(eliminate_all_handlers(a))),
        EffectGraph::Left(a) => EffectGraph::Left(Box::new(eliminate_all_handlers(a))),
        EffectGraph::Loop(a) => EffectGraph::Loop(Box::new(eliminate_all_handlers(a))),
        EffectGraph::Choice(a, b) => EffectGraph::Choice(
            Box::new(eliminate_all_handlers(a)),
            Box::new(eliminate_all_handlers(b)),
        ),
        EffectGraph::App(a) => EffectGraph::App(Box::new(eliminate_all_handlers(a))),
        // Leaves: Id, Arr, Op -- no handlers to eliminate.
        EffectGraph::Id | EffectGraph::Arr(_) | EffectGraph::Op(_) => g.clone(),
    }
}

// ============================================================================
// 5. Law checking at the handle site
// ============================================================================
//
// ADR-0076: "Law checking runs once at the `handle` site." When a handler is
// installed, the bundle's laws are verified (CutElim for structural laws,
// axioms for non-functor laws). This prototype reuses `Bundle::verify` from
// `decoupled_traits.rs` -- the verification machinery is unchanged.

/// When a handler is installed, verify the bundle's laws. This is the "law
/// checking at the handle site" from ADR-0076. Returns a `VerificationReport`.
/// Reuses `Bundle::verify` from `decoupled_traits.rs`.
pub fn verify_handler_bundle(bundle: &Bundle) -> VerificationReport {
    bundle.verify()
}

// ============================================================================
// 6. Convert between PolyGraph and EffectGraph
// ============================================================================
//
// `poly_to_effect` lifts a concrete `PolyGraph` (no ops) to an `EffectGraph`.
// `effect_to_poly` converts an `EffectGraph` (after handler elimination, no
// `Op`/`Handle` nodes remain) back to a `PolyGraph` for CutElim normalization.
// It panics if `Op` or `Handle` nodes remain -- they should be eliminated
// first.

/// Lift a `PolyGraph` (concrete, no ops) to an `EffectGraph`.
pub fn poly_to_effect(g: &PolyGraph) -> EffectGraph {
    match g {
        PolyGraph::Id => EffectGraph::Id,
        PolyGraph::Comp(a, b) => EffectGraph::Comp(
            Box::new(poly_to_effect(a)),
            Box::new(poly_to_effect(b)),
        ),
        PolyGraph::First(a) => EffectGraph::First(Box::new(poly_to_effect(a))),
        PolyGraph::Left(a) => EffectGraph::Left(Box::new(poly_to_effect(a))),
        PolyGraph::Loop(a) => EffectGraph::Loop(Box::new(poly_to_effect(a))),
        PolyGraph::Arr(name) => EffectGraph::Arr(name.clone()),
        PolyGraph::Choice(a, b) => EffectGraph::Choice(
            Box::new(poly_to_effect(a)),
            Box::new(poly_to_effect(b)),
        ),
        PolyGraph::App(a) => EffectGraph::App(Box::new(poly_to_effect(a))),
    }
}

/// Convert an `EffectGraph` (after handler elimination, no `Op`/`Handle`
/// nodes) back to a `PolyGraph` for CutElim normalization. Panics if `Op` or
/// `Handle` nodes remain (they should be eliminated first).
pub fn effect_to_poly(g: &EffectGraph) -> PolyGraph {
    match g {
        EffectGraph::Id => PolyGraph::Id,
        EffectGraph::Comp(a, b) => PolyGraph::Comp(
            Box::new(effect_to_poly(a)),
            Box::new(effect_to_poly(b)),
        ),
        EffectGraph::First(a) => PolyGraph::First(Box::new(effect_to_poly(a))),
        EffectGraph::Left(a) => PolyGraph::Left(Box::new(effect_to_poly(a))),
        EffectGraph::Loop(a) => PolyGraph::Loop(Box::new(effect_to_poly(a))),
        EffectGraph::Arr(name) => PolyGraph::Arr(name.clone()),
        EffectGraph::Choice(a, b) => PolyGraph::Choice(
            Box::new(effect_to_poly(a)),
            Box::new(effect_to_poly(b)),
        ),
        EffectGraph::App(a) => PolyGraph::App(Box::new(effect_to_poly(a))),
        EffectGraph::Op(_) => panic!("cannot convert: unhandled Op remains"),
        EffectGraph::Handle { .. } => panic!("cannot convert: Handle node remains"),
    }
}

// ============================================================================
// 7. Demo bundles
// ============================================================================

/// A concrete `Serializer<JSON>` bundle: serialize + deserialize as concrete
/// base arrows, with a roundtrip law. The roundtrip law is NOT a CutElim
/// rewrite (the arrows are opaque) -- it needs a semantic axiom (`hinv`).
/// This mirrors `serializer_bundle` in `decoupled_traits.rs` but uses
/// JSON-named concrete arrows so the rewrite is visible in the output.
fn json_serializer_bundle() -> Bundle {
    let mut arrows: HashMap<String, PolyGraph> = HashMap::new();
    arrows.insert("serialize".to_string(), garr("json_serialize"));
    arrows.insert("deserialize".to_string(), garr("json_deserialize"));
    Bundle {
        name: "Serializer".to_string(),
        arrows,
        laws: vec![BundleLaw {
            name: "roundtrip".to_string(),
            lhs: gcomp(garr("json_serialize"), garr("json_deserialize")),
            rhs: gid(),
            axiom: Some("hinv".to_string()),
        }],
    }
}

/// A minimal bundle "A" with one operation `op1` -> concrete arrow `a_concrete`.
fn bundle_a() -> Bundle {
    let mut arrows: HashMap<String, PolyGraph> = HashMap::new();
    arrows.insert("op1".to_string(), garr("a_concrete"));
    Bundle {
        name: "A".to_string(),
        arrows,
        laws: vec![],
    }
}

/// A minimal bundle "B" with one operation `op2` -> concrete arrow `b_concrete`.
fn bundle_b() -> Bundle {
    let mut arrows: HashMap<String, PolyGraph> = HashMap::new();
    arrows.insert("op2".to_string(), garr("b_concrete"));
    Bundle {
        name: "B".to_string(),
        arrows,
        laws: vec![],
    }
}

fn print_section(title: &str) {
    println!();
    println!("=== {} ===", title);
}

// ============================================================================
// 8. Demo + Tests
// ============================================================================

fn main() {
    print_section("ADR-0076 OQ#1: Bundled-operations effect representation");
    println!("EffectGraph extends PolyGraph with Op (unhandled op) and Handle (handler elimination).");
    println!("A bundle is intercepted as a single effect; handler elimination rewrites Op -> concrete arrow.");

    // ====================================================================
    // Demo 1: A graph with unhandled operations (effects).
    // "migrate" uses Serializer.serialize and Serializer.deserialize as
    // abstract ops -- they are NOT yet concrete arrows.
    // ====================================================================
    print_section("Demo 1: graph with unhandled operations (effects)");
    let migrate_with_effects = ecomp(
        eop("Serializer.serialize"),
        eop("Serializer.deserialize"),
    );
    println!("  graph: {}", migrate_with_effects);
    let row1 = effect_row(&migrate_with_effects);
    println!("  effect_row: {}", fmt_effect_row(&row1));
    assert_eq!(
        row1,
        {
            let mut s = BTreeSet::new();
            s.insert("Serializer.serialize".to_string());
            s.insert("Serializer.deserialize".to_string());
            s
        },
        "effect_row lists both unhandled ops"
    );
    println!("[ok] effect_row of a graph with Op nodes returns the right set");

    // ====================================================================
    // Demo 2: A concrete Serializer bundle (the impl).
    // ====================================================================
    print_section("Demo 2: concrete Serializer<JSON> bundle (the impl)");
    let json_serializer = json_serializer_bundle();
    println!("{}", json_serializer);

    // ====================================================================
    // Demo 3: Handle the effects -- wrap migrate in a handler.
    // The handler intercepts the whole Serializer bundle as one effect.
    // ====================================================================
    print_section("Demo 3: handle the effects (bundle as one handler)");
    let handled = ehandle(
        migrate_with_effects.clone(),
        "Serializer",
        json_serializer.clone(),
    );
    println!("  graph: {}", handled);
    let row_handled = effect_row(&handled);
    println!("  effect_row: {}", fmt_effect_row(&row_handled));
    assert!(
        row_handled.is_empty(),
        "handled graph has no unhandled Serializer ops"
    );
    println!("[ok] effect_row of handled graph excludes the handled bundle's ops");

    // ====================================================================
    // Demo 4: Verify the bundle's laws at the handle site.
    // ====================================================================
    print_section("Demo 4: law checking at the handle site");
    let report = verify_handler_bundle(&json_serializer);
    println!("  verify: {}", report);
    assert!(
        report.placeholder.contains(&"roundtrip".to_string()),
        "roundtrip is an axiom placeholder"
    );
    assert!(report.verified.is_empty(), "roundtrip is NOT CutElim-proven");
    assert!(report.failed.is_empty(), "axiom laws are placeholders, not failures");
    println!("[ok] roundtrip law -> placeholder (axiom: hinv) at the handle site");

    // ====================================================================
    // Demo 5: Eliminate the handler -- rewrite Op nodes to concrete arrows.
    // ====================================================================
    print_section("Demo 5: handler elimination (Op -> concrete arrow rewrite)");
    let eliminated = eliminate_all_handlers(&handled);
    println!("  eliminated: {}", eliminated);
    // After elimination: Comp(Arr("json_serialize"), Arr("json_deserialize")).
    let expected_eliminated = ecomp(earr("json_serialize"), earr("json_deserialize"));
    assert_eq!(eliminated, expected_eliminated, "ops rewritten to concrete arrows");
    let row_elim = effect_row(&eliminated);
    assert!(row_elim.is_empty(), "no unhandled ops remain after elimination");
    println!("[ok] handle_eliminate replaces Op nodes with concrete arrows from the bundle");

    // ====================================================================
    // Demo 6: Convert to PolyGraph and run CutElim.
    // ====================================================================
    print_section("Demo 6: convert to PolyGraph and run CutElim");
    let poly = effect_to_poly(&eliminated);
    println!("  poly: {}", poly);
    let norm = normalize(&poly, NORMALIZE_FUEL);
    println!("  normalized: {}", norm);
    // The graph is Comp(Arr, Arr) -- no id/first rewrites apply, so it is
    // already in normal form.
    assert_eq!(norm, poly, "Comp(Arr, Arr) is already normal");
    let fp = fingerprint(&poly);
    println!("  fingerprint: {}", fp);
    println!("[ok] after full elimination, graph converts to PolyGraph and normalizes");

    // ====================================================================
    // Demo 7: handle_eliminate leaves Op nodes from OTHER bundles alone.
    // ====================================================================
    print_section("Demo 7: handle_eliminate leaves other bundles' ops alone");
    let mixed = ecomp(eop("Serializer.serialize"), eop("Logger.log"));
    let partial_elim = handle_eliminate(&mixed, "Serializer", &json_serializer);
    println!("  before: {}", mixed);
    println!("  after Serializer handle: {}", partial_elim);
    // Serializer.serialize -> json_serialize; Logger.log stays as Op.
    let expected_partial = ecomp(earr("json_serialize"), eop("Logger.log"));
    assert_eq!(partial_elim, expected_partial, "only Serializer ops are rewritten");
    let row_partial = effect_row(&partial_elim);
    assert_eq!(
        row_partial,
        {
            let mut s = BTreeSet::new();
            s.insert("Logger.log".to_string());
            s
        },
        "Logger.log remains unhandled"
    );
    println!("[ok] handle_eliminate leaves Op nodes from other bundles alone");

    // ====================================================================
    // Demo 8: Nested handlers -- inner eliminated first, then outer.
    // ====================================================================
    print_section("Demo 8: nested handlers (inner first, then outer)");
    let nested = ehandle(
        ehandle(
            ecomp(eop("A.op1"), eop("B.op2")),
            "A",
            bundle_a(),
        ),
        "B",
        bundle_b(),
    );
    println!("  graph: {}", nested);
    let row_nested = effect_row(&nested);
    println!("  effect_row (handled): {}", fmt_effect_row(&row_nested));
    assert!(row_nested.is_empty(), "nested handlers cover all ops");
    let nested_eliminated = eliminate_all_handlers(&nested);
    println!("  eliminated: {}", nested_eliminated);
    let expected_nested = ecomp(earr("a_concrete"), earr("b_concrete"));
    assert_eq!(
        nested_eliminated, expected_nested,
        "inner A.op1 -> a_concrete, outer B.op2 -> b_concrete"
    );
    println!("[ok] nested handlers: inner eliminated first, then outer");

    // ====================================================================
    // Demo 9: Unhandled ops remain after partial handling.
    // ====================================================================
    print_section("Demo 9: unhandled ops remain after partial handling");
    let partial = ecomp(eop("A.op1"), eop("C.op3")); // no handler for C
    let row_partial_full = effect_row(&partial);
    println!("  graph: {}", partial);
    println!("  effect_row: {}", fmt_effect_row(&row_partial_full));
    assert_eq!(row_partial_full.len(), 2, "both ops unhandled");
    // Handle A only.
    let partial_handled = ehandle(partial, "A", bundle_a());
    let row_after_a = effect_row(&partial_handled);
    println!("  after handling A: effect_row = {}", fmt_effect_row(&row_after_a));
    assert_eq!(
        row_after_a,
        {
            let mut s = BTreeSet::new();
            s.insert("C.op3".to_string());
            s
        },
        "C.op3 remains unhandled"
    );
    let partial_eliminated = eliminate_all_handlers(&partial_handled);
    println!("  eliminated: {}", partial_eliminated);
    let expected_partial_elim = ecomp(earr("a_concrete"), eop("C.op3"));
    assert_eq!(
        partial_eliminated, expected_partial_elim,
        "A.op1 rewritten, C.op3 remains as Op"
    );
    println!("[ok] unhandled ops remain after partial handling (effect_row still has them)");

    // ====================================================================
    // Demo 10: effect_to_poly panics on remaining Op/Handle.
    // ====================================================================
    print_section("Demo 10: effect_to_poly panics on remaining Op/Handle");
    let still_has_op = ecomp(earr("a_concrete"), eop("C.op3"));
    let panic_op = std::panic::catch_unwind(|| effect_to_poly(&still_has_op));
    assert!(panic_op.is_err(), "effect_to_poly panics on remaining Op");
    println!("[ok] effect_to_poly panics on remaining Op node");
    let still_has_handle = ehandle(earr("x"), "A", bundle_a());
    let panic_handle = std::panic::catch_unwind(|| effect_to_poly(&still_has_handle));
    assert!(panic_handle.is_err(), "effect_to_poly panics on remaining Handle");
    println!("[ok] effect_to_poly panics on remaining Handle node");

    // ====================================================================
    // Demo 11: The "trait" pattern -- Law + Bundle + Handler.
    // A handled bundle with verified laws, eliminated to concrete arrows,
    // then CutElim-normalizable.
    // ====================================================================
    print_section("Demo 11: the 'trait' pattern (Law + Bundle + Handler)");
    let trait_body = ecomp(eop("Serializer.serialize"), eop("Serializer.deserialize"));
    let trait_bundle = json_serializer_bundle();
    let trait_handled = ehandle(
        trait_body,
        "Serializer",
        trait_bundle.clone(),
    );
    // 1. Law checking at the handle site.
    let trait_report = verify_handler_bundle(&trait_bundle);
    println!("  law check at handle site: {}", trait_report);
    assert!(trait_report.is_clean(), "no failed laws");
    assert!(
        trait_report.placeholder.contains(&"roundtrip".to_string()),
        "roundtrip verified as axiom placeholder"
    );
    // 2. Effect row is empty (all ops handled).
    let trait_row = effect_row(&trait_handled);
    println!("  effect_row: {}", fmt_effect_row(&trait_row));
    assert!(trait_row.is_empty(), "all ops handled");
    // 3. Eliminate handlers -> concrete arrows.
    let trait_eliminated = eliminate_all_handlers(&trait_handled);
    println!("  eliminated: {}", trait_eliminated);
    // 4. Convert to PolyGraph and normalize.
    let trait_poly = effect_to_poly(&trait_eliminated);
    let trait_norm = normalize(&trait_poly, NORMALIZE_FUEL);
    println!("  poly: {} -> normalized: {}", trait_poly, trait_norm);
    // 5. The roundtrip law (serialize >>> deserialize = id) can be checked
    //    against the eliminated graph via law_equal (it will NOT hold under
    //    CutElim because the arrows are opaque -- that is why it is an axiom).
    let roundtrip_lhs = gcomp(garr("json_serialize"), garr("json_deserialize"));
    let roundtrip_holds_cutelim = law_equal(&roundtrip_lhs, &gid());
    println!(
        "  roundtrip via CutElim (opaque arrows): {} (expected false -> needs axiom)",
        roundtrip_holds_cutelim
    );
    assert!(!roundtrip_holds_cutelim, "roundtrip is NOT CutElim-proven (opaque arrows)");
    println!("[ok] trait pattern: verified bundle -> eliminated -> PolyGraph -> CutElim-normalizable");

    // ====================================================================
    // Demo 12: poly_to_effect / effect_to_poly round-trip (concrete graph).
    // ====================================================================
    print_section("Demo 12: poly_to_effect / effect_to_poly round-trip");
    let concrete = gcomp(gid(), garr("f"));
    let lifted = poly_to_effect(&concrete);
    println!("  poly: {} -> effect: {}", concrete, lifted);
    let back = effect_to_poly(&lifted);
    println!("  effect -> poly: {}", back);
    assert_eq!(concrete, back, "round-trip preserves concrete graph");
    // And normalization works through the round-trip.
    assert!(law_equal(&concrete, &back), "round-tripped graph is law_equal to original");
    println!("[ok] poly_to_effect / effect_to_poly round-trip preserves the graph");

    // ====================================================================
    // Consolidated test summary.
    // ====================================================================
    print_section("Tests");
    println!("[pass] effect_row of a graph with Op nodes returns the right set");
    println!("[pass] effect_row of a handled graph excludes the handled bundle's ops");
    println!("[pass] handle_eliminate replaces Op nodes with concrete arrows from the bundle");
    println!("[pass] handle_eliminate leaves Op nodes from other bundles alone");
    println!("[pass] eliminate_all_handlers removes all Handle and Op nodes (when all ops handled)");
    println!("[pass] nested handlers: inner eliminated first, then outer");
    println!("[pass] unhandled ops remain after partial handling (effect_row still has them)");
    println!("[pass] effect_to_poly panics on remaining Op/Handle");
    println!("[pass] law checking at handle site: roundtrip -> placeholder (axiom)");
    println!("[pass] after full elimination, graph converts to PolyGraph and normalizes");
    println!("[pass] the 'trait' pattern: Law + Bundle + Handler -> eliminated -> CutElim-normalizable");
    println!("[pass] poly_to_effect / effect_to_poly round-trip preserves the graph");

    // Silence unused-helper warnings (eid/efirst are provided for completeness).
    let _ = eid();
    let _ = efirst(eid());

    print_section("All tests passed");
}
