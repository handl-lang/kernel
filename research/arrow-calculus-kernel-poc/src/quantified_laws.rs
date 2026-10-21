// ADR-0076 Open Question #4 -- Rust-side prototype.
//
// Higher-order law QUANTIFIER syntax for the decoupled trait layer.
//
// Laws need to express universal quantification over arrows:
//   forall f g. map (f >>> g) = map f >>> map g
//
// The current prototype (law_inference.rs, decoupled_traits.rs) uses free
// variables implicitly -- `f` and `g` look like specific named arrows
// (`arr("f")`, `arr("g")`), not universally quantified variables. This
// prototype makes the quantification EXPLICIT: a `QuantifiedLaw` binds
// variables in a `vars` vector, and the checker instantiates them under
// multiple test substitutions to verify the law holds for ALL arrows.
//
// HONESTY NOTE (read me): testing under multiple substitutions is a
// HEURISTIC, not a proof. We cannot test ALL possible arrows (infinite).
// The real proof is in Lean (`TraitInference.lean` proves these laws for
// all arrows via CutElim). This prototype demonstrates the SYNTAX
// (explicit `forall` quantifier) and the CHECKING MECHANISM
// (substitution-based testing), not completeness. The heuristic is strong
// for CutElim-proven structural laws (the rewrites are schema-level -- they
// fire for any inner arrow), but it is NOT a substitute for the Lean proof.
//
// ADR: platform/project/adrs/0076-decoupled-trait-layer.md (Open Question #4)
//
// Reuses the graph model, CutElim normalizer, and law_equal from
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
use trait_catalog::{law_equal, normalize, PolyGraph};

use std::collections::HashMap;
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

// ============================================================================
// 1. Quantified Law Expressions
// ============================================================================
//
// A law expression type that explicitly binds variables. Unlike the implicit
// approach (where `arr("f")` is a free variable that looks like a constant),
// `LawExpr::Var(LawVar("f"))` is an explicitly universally quantified
// variable, and `LawExpr::Const("sort")` is a concrete base arrow (a
// constant). This distinction is the core of OQ#4: the syntax makes
// quantification honest.

/// A variable in a law equation. Universally quantified.
/// "f" means "for all arrows f of the appropriate type".
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LawVar(pub String);

/// A law expression: a graph with quantified variables.
/// Variables are explicitly bound (by `QuantifiedLaw.vars`), not free.
#[derive(Clone, Debug, PartialEq)]
pub enum LawExpr {
    /// A quantified variable reference. This is a universally quantified
    /// variable -- "for all arrows f". Distinct from `Const`, which is a
    /// specific named arrow.
    Var(LawVar),
    /// A concrete base arrow (a constant, not a variable).
    /// e.g. `Const("sort")` is a specific arrow; `Var("f")` is any arrow.
    Const(String),
    /// Polymorphic identity: `id`.
    Id,
    /// Composition: `f >>> g` (written `f ; g` in display).
    Comp(Box<LawExpr>, Box<LawExpr>),
    /// First (product functoriality): `first(f)`.
    First(Box<LawExpr>),
    /// Left (coproduct functoriality): `left(f)`.
    Left(Box<LawExpr>),
    /// Loop (trace/fixpoint): `loop(f)`.
    Loop(Box<LawExpr>),
    /// Binary sum functoriality: `choice(f, g)`.
    Choice(Box<LawExpr>, Box<LawExpr>),
    /// ArrowApply placeholder: `app(f)`.
    App(Box<LawExpr>),
}

/// A quantified law: `forall vars. lhs = rhs`.
///
/// The `vars` vector lists the universally quantified variables. The law
/// holds iff for ALL substitutions of arrows into those variables, the
/// instantiated `lhs` and `rhs` are extensionally equal (normalize to the
/// same form under CutElim, or hold via a semantic axiom).
///
/// `axiom`: `None` = CutElim-proven (structural law); `Some(name)` = the law
/// requires a semantic axiom (not provable by CutElim alone). This matches
/// the `axiom` field on `ArrowLaw` / `BundleLaw` in `decoupled_traits.rs`.
pub struct QuantifiedLaw {
    /// Short name, e.g. "functor_composition".
    pub name: String,
    /// Universally quantified variables, e.g. [LawVar("f"), LawVar("g")].
    /// Empty = no quantification (a ground equation).
    pub vars: Vec<LawVar>,
    /// Left-hand side of the equation.
    pub lhs: LawExpr,
    /// Right-hand side of the equation.
    pub rhs: LawExpr,
    /// `None` = CutElim-proven; `Some(name)` = requires a semantic axiom.
    pub axiom: Option<String>,
}

// ============================================================================
// 2. Substitution: instantiate variables with concrete graphs
// ============================================================================
//
// A substitution maps law variables to concrete `PolyGraph`s. Instantiating
// a `LawExpr` with a substitution produces a concrete `PolyGraph` that can
// be checked via `law_equal` (CutElim normalization).
//
// This is the mechanism that makes quantification honest: instead of testing
// the law with ONE specific placeholder arrow (`arr("f")`), we test it under
// MULTIPLE substitutions -- different arrow shapes that exercise different
// CutElim behaviors.

/// A substitution mapping law variables to concrete `PolyGraph`s.
#[derive(Clone, Debug, Default)]
pub struct LawSubst {
    map: HashMap<String, PolyGraph>,
}

impl LawSubst {
    pub fn new() -> Self {
        LawSubst {
            map: HashMap::new(),
        }
    }

    /// Bind a law variable to a concrete graph.
    pub fn bind(&mut self, var: &str, graph: PolyGraph) {
        self.map.insert(var.to_string(), graph);
    }

    /// Look up the graph bound to a variable.
    pub fn get(&self, var: &str) -> Option<&PolyGraph> {
        self.map.get(var)
    }
}

/// Instantiate a `LawExpr` with a substitution, producing a concrete
/// `PolyGraph`.
///
/// - `Var(f)`    -> the graph bound to `f` in the substitution (panics if
///   unbound -- all quantified variables must be bound before instantiation).
/// - `Const(name)` -> `Arr(name)` (a concrete base arrow, not a variable).
/// - Combinators -> recurse structurally, mirroring `PolyGraph`.
pub fn instantiate(expr: &LawExpr, subst: &LawSubst) -> PolyGraph {
    match expr {
        LawExpr::Var(LawVar(name)) => subst.get(name).cloned().unwrap_or_else(|| {
            panic!("unbound law variable: {} (all quantified vars must be bound)", name)
        }),
        LawExpr::Const(name) => PolyGraph::Arr(name.clone()),
        LawExpr::Id => PolyGraph::Id,
        LawExpr::Comp(a, b) => PolyGraph::Comp(
            Box::new(instantiate(a, subst)),
            Box::new(instantiate(b, subst)),
        ),
        LawExpr::First(a) => PolyGraph::First(Box::new(instantiate(a, subst))),
        LawExpr::Left(a) => PolyGraph::Left(Box::new(instantiate(a, subst))),
        LawExpr::Loop(a) => PolyGraph::Loop(Box::new(instantiate(a, subst))),
        LawExpr::Choice(a, b) => PolyGraph::Choice(
            Box::new(instantiate(a, subst)),
            Box::new(instantiate(b, subst)),
        ),
        LawExpr::App(a) => PolyGraph::App(Box::new(instantiate(a, subst))),
    }
}

// ============================================================================
// 3. Law Checking Under Quantification
// ============================================================================
//
// Check a quantified law by testing it under multiple substitutions. If the
// law holds for ALL test substitutions, it is Satisfied. If it fails under
// ANY substitution, it is Violated.
//
// Since we cannot test ALL possible arrows (infinite), we test with a
// representative set of "test arrows" -- different shapes that exercise
// different CutElim behaviors:
//   - `arr("test_f")`: a generic opaque arrow (the default).
//   - `id`: the identity arrow (tests id-related rewrites: ceIdLeft,
//     ceIdRight, ceFirstId, ceLeftId).
//   - `comp(arr("test_a"), arr("test_b"))`: a composed arrow (tests fusion:
//     ceFirstFusion, ceLeftFusion).
//   - `first(arr("test_h"))`: a first-shaped arrow (tests nesting).
//
// If the law holds under all test substitutions, we report Satisfied. This
// is NOT a proof (we cannot test all arrows), but it is a strong heuristic.
// The real proof is in Lean (TraitInference.lean proves these laws for all
// arrows via CutElim). The prototype demonstrates the SYNTAX and the
// CHECKING MECHANISM, not completeness.

/// The outcome of checking a quantified law under test substitutions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LawCheckResult {
    /// The law holds under all test substitutions (CutElim-proven heuristic).
    Satisfied,
    /// The law fails under at least one test substitution.
    Violated,
    /// The law cannot be checked via CutElim (axiom-requiring, or no
    /// substitutions were tested).
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

/// The representative set of test arrows used for substitution-based
/// checking. Each exercises a different CutElim behavior.
fn test_arrows() -> Vec<PolyGraph> {
    vec![
        // A generic opaque arrow. CutElim treats Arr(name) as opaque -- no
        // rewrite fires on it directly. This is the "default" case.
        garr("test_f"),
        // The identity arrow. Tests id-related rewrites: ceIdLeft
        // (comp(id, G) ==> G), ceIdRight (comp(G, id) ==> G), ceFirstId
        // (first(id) ==> id), ceLeftId (left(id) ==> id).
        gid(),
        // A composed arrow. Tests fusion rewrites: ceFirstFusion
        // (comp(first G, first H) ==> first(comp G H)), ceLeftFusion.
        gcomp(garr("test_a"), garr("test_b")),
        // A first-shaped arrow. Tests nesting: first(first(...)) and
        // interaction between first and other combinators.
        gfirst(garr("test_h")),
    ]
}

/// Generate test substitutions for a set of variables. Each variable gets
/// assigned one of the test arrows; the result is the cartesian product of
/// all test arrows across all variables.
///
/// For 0 vars: 1 substitution (the empty substitution).
/// For 1 var:  4 substitutions (4 test arrows).
/// For 2 vars: 16 substitutions (4 x 4).
/// For N vars: 4^N substitutions.
fn generate_test_substitutions(vars: &[LawVar]) -> Vec<LawSubst> {
    let arrows = test_arrows();
    let mut result = vec![LawSubst::new()];
    for var in vars {
        let mut next = Vec::new();
        for subst in &result {
            for arrow in &arrows {
                let mut s = subst.clone();
                s.bind(&var.0, arrow.clone());
                next.push(s);
            }
        }
        result = next;
    }
    result
}

/// Count the number of test substitutions for a set of variables.
/// 4^N for N vars (1 for 0 vars).
fn count_test_substitutions(vars: &[LawVar]) -> usize {
    test_arrows().len().pow(vars.len() as u32)
}

/// Check a quantified law by testing it under multiple substitutions.
///
/// - If `axiom.is_some()`: return `NotApplicable` (CutElim cannot verify
///   axiom-requiring laws -- they need a semantic axiom, not normalization).
/// - Otherwise: instantiate `lhs` and `rhs` under each test substitution and
///   check `law_equal`. If ALL pass, `Satisfied`. If ANY fails, `Violated`.
///
/// HONESTY: this is a heuristic, not a proof. See the module-level note.
pub fn check_quantified_law(law: &QuantifiedLaw) -> LawCheckResult {
    // Axiom-requiring laws cannot be verified by CutElim alone.
    if law.axiom.is_some() {
        return LawCheckResult::NotApplicable;
    }

    let test_substitutions = generate_test_substitutions(&law.vars);
    let mut all_hold = true;
    let mut any_tested = false;
    for subst in &test_substitutions {
        any_tested = true;
        let lhs = instantiate(&law.lhs, subst);
        let rhs = instantiate(&law.rhs, subst);
        if !law_equal(&lhs, &rhs) {
            all_hold = false;
            break;
        }
    }
    if !any_tested {
        return LawCheckResult::NotApplicable;
    }
    if all_hold {
        LawCheckResult::Satisfied
    } else {
        LawCheckResult::Violated
    }
}

// ============================================================================
// 4. The Quantified Law Catalog
// ============================================================================
//
// The built-in quantified law catalog. Each law explicitly binds its
// universally quantified variables. Laws are either CutElim-proven
// (`axiom: None`) or axiom-requiring (`axiom: Some(name)`).
//
// CutElim-proven structural laws (the six rewrites):
//   - functor_identity:        first(id) = id              (ceFirstId)
//   - functor_composition:     first(f;g) = first(f);first(g) (ceFirstFusion)
//   - coproduct_functor_identity:    left(id) = id          (ceLeftId)
//   - coproduct_functor_composition: left(f;g) = left(f);left(g) (ceLeftFusion)
//   - id_left:                 f;id = f                     (ceIdRight)
//   - id_right:                id;f = f                     (ceIdLeft)
//
// Axiom-requiring law (NOT CutElim-proven):
//   - roundtrip:               serialize;deserialize = id   (needs axiom hinv)

/// The built-in quantified law catalog.
pub fn builtin_quantified_laws() -> Vec<QuantifiedLaw> {
    vec![
        // --- Functor laws (product functoriality, CutElim-proven) ---
        QuantifiedLaw {
            name: "functor_identity".to_string(),
            // first(id) = id -- f is quantified but unused (the law is about
            // the functor's interaction with id, not about f). We keep f in
            // vars to match the ADR's `forall f. map id = id` framing.
            vars: vec![LawVar("f".to_string())],
            lhs: LawExpr::First(Box::new(LawExpr::Id)),
            rhs: LawExpr::Id,
            axiom: None,
        },
        QuantifiedLaw {
            name: "functor_composition".to_string(),
            vars: vec![LawVar("f".to_string()), LawVar("g".to_string())],
            lhs: LawExpr::First(Box::new(LawExpr::Comp(
                Box::new(LawExpr::Var(LawVar("f".to_string()))),
                Box::new(LawExpr::Var(LawVar("g".to_string()))),
            ))),
            rhs: LawExpr::Comp(
                Box::new(LawExpr::First(Box::new(LawExpr::Var(LawVar(
                    "f".to_string(),
                ))))),
                Box::new(LawExpr::First(Box::new(LawExpr::Var(LawVar(
                    "g".to_string(),
                ))))),
            ),
            axiom: None,
        },
        // --- Identity laws (universal, CutElim-proven) ---
        // f >>> id = f  (ceIdRight: comp(G, id) ==> G)
        QuantifiedLaw {
            name: "id_left".to_string(),
            vars: vec![LawVar("f".to_string())],
            lhs: LawExpr::Comp(
                Box::new(LawExpr::Var(LawVar("f".to_string()))),
                Box::new(LawExpr::Id),
            ),
            rhs: LawExpr::Var(LawVar("f".to_string())),
            axiom: None,
        },
        // id >>> f = f  (ceIdLeft: comp(id, G) ==> G)
        QuantifiedLaw {
            name: "id_right".to_string(),
            vars: vec![LawVar("f".to_string())],
            lhs: LawExpr::Comp(
                Box::new(LawExpr::Id),
                Box::new(LawExpr::Var(LawVar("f".to_string()))),
            ),
            rhs: LawExpr::Var(LawVar("f".to_string())),
            axiom: None,
        },
        // --- Coproduct functor laws (sum functoriality, CutElim-proven) ---
        QuantifiedLaw {
            name: "coproduct_functor_identity".to_string(),
            vars: vec![],
            lhs: LawExpr::Left(Box::new(LawExpr::Id)),
            rhs: LawExpr::Id,
            axiom: None,
        },
        QuantifiedLaw {
            name: "coproduct_functor_composition".to_string(),
            vars: vec![LawVar("f".to_string()), LawVar("g".to_string())],
            lhs: LawExpr::Left(Box::new(LawExpr::Comp(
                Box::new(LawExpr::Var(LawVar("f".to_string()))),
                Box::new(LawExpr::Var(LawVar("g".to_string()))),
            ))),
            rhs: LawExpr::Comp(
                Box::new(LawExpr::Left(Box::new(LawExpr::Var(LawVar(
                    "f".to_string(),
                ))))),
                Box::new(LawExpr::Left(Box::new(LawExpr::Var(LawVar(
                    "g".to_string(),
                ))))),
            ),
            axiom: None,
        },
        // --- Axiom-requiring law (NOT CutElim-proven) ---
        // serialize >>> deserialize = id -- a semantic fact about specific
        // base arrows. CutElim treats Arr("serialize") and Arr("deserialize")
        // as opaque; it cannot simplify their composition to id. This law
        // requires a semantic axiom (hinv: serialize and deserialize are
        // inverses). Mirrors EquationalLawInference.lean.
        QuantifiedLaw {
            name: "roundtrip".to_string(),
            vars: vec![],
            lhs: LawExpr::Comp(
                Box::new(LawExpr::Const("serialize".to_string())),
                Box::new(LawExpr::Const("deserialize".to_string())),
            ),
            rhs: LawExpr::Id,
            axiom: Some("hinv".to_string()),
        },
    ]
}

// ============================================================================
// 5. Quantified Law Inference
// ============================================================================
//
// Infer which quantified laws an arrow satisfies, based on its structure.
// Uses the same structural recognition as law_inference.rs (uses_first,
// uses_left) but checks quantified laws with explicit variable binding.
//
// Structural recognition determines which laws APPLY to an arrow:
//   - Functor laws (functor_identity, functor_composition): arrow uses `first`.
//   - Coproduct functor laws: arrow uses `left`.
//   - Identity laws (id_left, id_right): arrow is a "bare" arrow (no first,
//     no left) -- these are universal laws that apply to any arrow, but for
//     inference we report them only for arrows without functor/coproduct
//     structure (the structural laws are more specific/relevant for those).
//
// Axiom-requiring laws are NOT inferable (they require a semantic axiom that
// cannot be discovered from wiring). This matches the honesty boundary from
// law_inference.rs: non-functor laws cannot be inferred from structure.

/// Does the graph use the `first` combinator anywhere in its tree?
/// Mirrors `UsesFirst` in `TraitInference.lean` / `law_inference.rs`.
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

/// Does the graph use the `left` combinator anywhere in its tree?
/// Mirrors `UsesLeft` in `TraitInference.lean` / `law_inference.rs`.
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

/// Does a quantified law apply to an arrow, based on structural recognition?
///
/// - Functor laws (functor_identity, functor_composition): arrow uses `first`.
/// - Coproduct functor laws: arrow uses `left`.
/// - Identity laws (id_left, id_right): arrow is bare (no first, no left).
///   These are universal laws (hold for all arrows), but for inference we
///   report them only for arrows without functor/coproduct structure -- the
///   structural laws are the more specific/relevant inference for those.
fn law_applies_to_arrow(law: &QuantifiedLaw, arrow: &PolyGraph) -> bool {
    match law.name.as_str() {
        "functor_identity" | "functor_composition" => uses_first(arrow),
        "coproduct_functor_identity" | "coproduct_functor_composition" => {
            uses_left(arrow)
        }
        "id_left" | "id_right" => !uses_first(arrow) && !uses_left(arrow),
        _ => false,
    }
}

/// The status of an inferred quantified law.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LawStatus {
    /// The law holds (CutElim-proven: all test substitutions pass).
    Satisfied,
    /// The law does not hold (at least one test substitution fails).
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

/// A quantified law inferred for an arrow, without declaration.
#[derive(Debug, Clone)]
pub struct InferredQuantifiedLaw {
    pub name: String,
    pub vars: Vec<String>,
    pub status: LawStatus,
    /// How many test substitutions were checked.
    pub tested_substitutions: usize,
}

impl fmt::Display for InferredQuantifiedLaw {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.vars.is_empty() {
            write!(
                f,
                "{}  [{} ({} substitutions)]",
                self.name, self.status, self.tested_substitutions
            )
        } else {
            write!(
                f,
                "forall {}. {}  [{} ({} substitutions)]",
                self.vars.join(" "),
                self.name,
                self.status,
                self.tested_substitutions
            )
        }
    }
}

/// Infer which quantified laws an arrow satisfies, without declaration.
///
/// Iterates over the quantified law catalog. For each law:
///   1. Skip axiom-requiring laws (not inferable -- require semantic axioms).
///   2. Check structural applicability (`law_applies_to_arrow`).
///   3. If applicable, check the law under test substitutions.
///   4. Report Satisfied or Violated (NotApplicable is skipped).
pub fn infer_quantified_laws(arrow: &PolyGraph) -> Vec<InferredQuantifiedLaw> {
    let catalog = builtin_quantified_laws();
    let mut results = Vec::new();
    for law in &catalog {
        // Skip axiom-requiring laws for inference (they can't be inferred
        // from wiring -- they need a semantic axiom).
        if law.axiom.is_some() {
            continue;
        }

        if law_applies_to_arrow(law, arrow) {
            let result = check_quantified_law(law);
            match result {
                LawCheckResult::Satisfied => results.push(InferredQuantifiedLaw {
                    name: law.name.clone(),
                    vars: law.vars.iter().map(|v| v.0.clone()).collect(),
                    status: LawStatus::Satisfied,
                    tested_substitutions: count_test_substitutions(&law.vars),
                }),
                LawCheckResult::Violated => results.push(InferredQuantifiedLaw {
                    name: law.name.clone(),
                    vars: law.vars.iter().map(|v| v.0.clone()).collect(),
                    status: LawStatus::Violated,
                    tested_substitutions: count_test_substitutions(&law.vars),
                }),
                LawCheckResult::NotApplicable => {} // skip
            }
        }
    }
    results
}

/// Helper: does the inference report a given law as Satisfied?
fn satisfies(inferred: &[InferredQuantifiedLaw], name: &str) -> bool {
    inferred
        .iter()
        .any(|l| l.name == name && l.status == LawStatus::Satisfied)
}

/// Helper: collect the names of all Satisfied inferred laws.
#[allow(dead_code)]
fn satisfied_names(inferred: &[InferredQuantifiedLaw]) -> Vec<String> {
    inferred
        .iter()
        .filter(|l| l.status == LawStatus::Satisfied)
        .map(|l| l.name.clone())
        .collect()
}

// ============================================================================
// 6. Display: show laws with explicit forall
// ============================================================================

impl fmt::Display for LawExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LawExpr::Var(v) => write!(f, "{}", v.0),
            LawExpr::Const(name) => write!(f, "{}", name),
            LawExpr::Id => write!(f, "id"),
            LawExpr::Comp(a, b) => write!(f, "({} ; {})", a, b),
            LawExpr::First(a) => write!(f, "first({})", a),
            LawExpr::Left(a) => write!(f, "left({})", a),
            LawExpr::Loop(a) => write!(f, "loop({})", a),
            LawExpr::Choice(a, b) => write!(f, "choice({}, {})", a, b),
            LawExpr::App(a) => write!(f, "app({})", a),
        }
    }
}

impl fmt::Display for QuantifiedLaw {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let equation = if self.vars.is_empty() {
            format!("{} = {}", self.lhs, self.rhs)
        } else {
            let vars = self
                .vars
                .iter()
                .map(|v| v.0.clone())
                .collect::<Vec<_>>()
                .join(" ");
            format!("forall {}. {} = {}", vars, self.lhs, self.rhs)
        };
        match &self.axiom {
            None => write!(f, "law {}: {}", self.name, equation),
            Some(ax) => write!(f, "law {}: {}   [axiom: {}]", self.name, equation, ax),
        }
    }
}

// ============================================================================
// 7. Demo + Tests
// ============================================================================

fn print_section(title: &str) {
    println!();
    println!("=== {} ===", title);
}

fn main() {
    print_section("ADR-0076 OQ#4 prototype: Higher-Order Law Quantifier Syntax");
    println!("Laws quantify over arrows explicitly: forall f g. map (f >>> g) = map f >>> map g");
    println!("This makes quantification HONEST -- variables are bound, not free.");
    println!();

    // ====================================================================
    // Demo 1: Display the quantified law catalog with explicit forall.
    // ====================================================================
    print_section("Demo 1: Quantified law catalog (explicit forall)");
    let catalog = builtin_quantified_laws();
    for law in &catalog {
        println!("  {}", law);
    }

    // ====================================================================
    // Demo 2: Check a law under multiple substitutions.
    // ====================================================================
    print_section("Demo 2: Check functor_composition under 16 substitutions");
    let law = &catalog[1]; // functor_composition
    let n_subst = count_test_substitutions(&law.vars);
    println!("  {}", law);
    println!("  Testing under {} substitutions (4 test arrows x {} vars)...", n_subst, law.vars.len());
    let result = check_quantified_law(law);
    println!("  Result: {} (tested under {} substitutions)", result, n_subst);

    // ====================================================================
    // Demo 3: Infer quantified laws for first(f).
    // ====================================================================
    print_section("Demo 3: Infer quantified laws for first(f) -- functorial core");
    let map_graph = gfirst(garr("f"));
    println!("  arrow: {}", map_graph);
    let inferred = infer_quantified_laws(&map_graph);
    for law in &inferred {
        println!("  -> {}", law);
    }

    // ====================================================================
    // Demo 4: Infer for a bare arr (no functor structure).
    // ====================================================================
    print_section("Demo 4: Infer quantified laws for arr(\"sort\") -- bare base arrow");
    let bare = garr("sort");
    println!("  arrow: {}", bare);
    let inferred = infer_quantified_laws(&bare);
    for law in &inferred {
        println!("  -> {}", law);
    }

    // ====================================================================
    // Demo 5: Infer for left(f) (coproduct functor).
    // ====================================================================
    print_section("Demo 5: Infer quantified laws for left(f) -- coproduct functorial core");
    let left_graph = gleft(garr("f"));
    println!("  arrow: {}", left_graph);
    let inferred = infer_quantified_laws(&left_graph);
    for law in &inferred {
        println!("  -> {}", law);
    }

    // ====================================================================
    // Demo 6: The roundtrip law (axiom-requiring, NOT inferable).
    // ====================================================================
    print_section("Demo 6: The roundtrip law (axiom-requiring, NOT inferable)");
    let roundtrip = &catalog[6]; // roundtrip
    println!("  {}", roundtrip);
    println!("  axiom.is_some() -> skipped in inference (cannot be discovered from wiring)");
    let serialize_deserialize = gcomp(garr("serialize"), garr("deserialize"));
    let inferred = infer_quantified_laws(&serialize_deserialize);
    println!("  infer_quantified_laws(serialize;deserialize) -> {} laws (axiom skipped)",
        inferred.len());

    // ====================================================================
    // Demo 7: Compare implicit free variables vs explicit forall.
    // ====================================================================
    print_section("Demo 7: Implicit free variables (old) vs explicit forall (new)");
    println!("The old approach (law_inference.rs) uses arr(\"f\"), arr(\"g\") as implicit");
    println!("free variables. The new approach binds them explicitly and tests under");
    println!("multiple substitutions. Both produce the same result, but the new one");
    println!("is honest about quantification.");
    println!();

    // --- Implicit approach (replicates law_inference.rs pattern) ---
    println!("--- Implicit (old: free variables, single substitution) ---");
    let f = garr("f");
    let g = garr("g");
    let implicit_fid = law_equal(&gfirst(gid()), &gid());
    let implicit_fcomp = law_equal(&gfirst(gcomp(f.clone(), g.clone())), &gcomp(gfirst(f), gfirst(g)));
    println!("  functor_identity:     law_equal(first(id), id)         = {}", implicit_fid);
    println!("  functor_composition:  law_equal(first(f;g), first(f);first(g)) = {}", implicit_fcomp);

    // --- Explicit approach (new: forall, multiple substitutions) ---
    println!("--- Explicit (new: forall, multiple substitutions) ---");
    let explicit_fid = check_quantified_law(&catalog[0]);
    let explicit_fcomp = check_quantified_law(&catalog[1]);
    println!("  functor_identity:     check_quantified_law = {} (4 substitutions)", explicit_fid);
    println!("  functor_composition:  check_quantified_law = {} (16 substitutions)", explicit_fcomp);
    println!();
    println!("  Both agree: implicit and explicit produce the same Satisfied/Violated result.");
    println!("  The new approach is honest: 'forall f g' is explicit, not implicit.");

    // ====================================================================
    // Demo 8: A law that FAILS under some substitution.
    // ====================================================================
    print_section("Demo 8: A bogus law that fails under substitution");
    let bogus = QuantifiedLaw {
        name: "bogus_first_eq_f".to_string(),
        vars: vec![LawVar("f".to_string())],
        lhs: LawExpr::First(Box::new(LawExpr::Var(LawVar("f".to_string())))),
        rhs: LawExpr::Var(LawVar("f".to_string())),
        axiom: None,
    };
    println!("  {}", bogus);
    println!("  This is NOT true: first(f) is not f (first adds a product component).");
    let result = check_quantified_law(&bogus);
    println!("  Result: {} (fails under substitution with arr(\"test_f\"))", result);
    println!("  Note: under f=id, first(id)=id would pass (ceFirstId), but under");
    println!("  f=arr(\"test_f\"), first(arr(\"test_f\")) != arr(\"test_f\") -> Violated.");
    println!("  This shows why testing MULTIPLE substitutions matters: a bogus law");
    println!("  might pass under one substitution but fail under another.");

    // ====================================================================
    // Tests (assertions consolidated).
    // ====================================================================
    print_section("Tests");

    // --- Test 1: catalog has 7 laws ---
    let catalog = builtin_quantified_laws();
    assert_eq!(catalog.len(), 7, "exactly 7 laws (4 structural + 2 universal id + 1 axiom)");
    println!("[pass] quantified law catalog has 7 laws (4 structural + 2 universal id + 1 axiom)");

    // --- Test 2: functor_identity: forall f. first(id) = id -- Satisfied, 4 subst ---
    let law = &catalog[0];
    assert_eq!(law.name, "functor_identity");
    assert_eq!(law.vars.len(), 1, "functor_identity has 1 var (f)");
    assert_eq!(count_test_substitutions(&law.vars), 4, "1 var -> 4 substitutions");
    let result = check_quantified_law(law);
    assert_eq!(result, LawCheckResult::Satisfied, "functor_identity Satisfied");
    println!("[pass] functor_identity: forall f. first(id) = id -- Satisfied under 4 substitutions");

    // --- Test 3: functor_composition: forall f g. first(f;g) = first(f);first(g) -- 16 subst ---
    let law = &catalog[1];
    assert_eq!(law.name, "functor_composition");
    assert_eq!(law.vars.len(), 2, "functor_composition has 2 vars (f, g)");
    assert_eq!(count_test_substitutions(&law.vars), 16, "2 vars -> 16 substitutions");
    let result = check_quantified_law(law);
    assert_eq!(result, LawCheckResult::Satisfied, "functor_composition Satisfied");
    println!("[pass] functor_composition: forall f g. first(f;g) = first(f);first(g) -- Satisfied under 16 substitutions");

    // --- Test 4: id_left: forall f. f;id = f -- Satisfied, 4 subst ---
    let law = &catalog[2];
    assert_eq!(law.name, "id_left");
    assert_eq!(law.vars.len(), 1, "id_left has 1 var (f)");
    assert_eq!(count_test_substitutions(&law.vars), 4, "1 var -> 4 substitutions");
    let result = check_quantified_law(law);
    assert_eq!(result, LawCheckResult::Satisfied, "id_left Satisfied");
    println!("[pass] id_left: forall f. f;id = f -- Satisfied under 4 substitutions");

    // --- Test 5: id_right: forall f. id;f = f -- Satisfied, 4 subst ---
    let law = &catalog[3];
    assert_eq!(law.name, "id_right");
    assert_eq!(law.vars.len(), 1, "id_right has 1 var (f)");
    assert_eq!(count_test_substitutions(&law.vars), 4, "1 var -> 4 substitutions");
    let result = check_quantified_law(law);
    assert_eq!(result, LawCheckResult::Satisfied, "id_right Satisfied");
    println!("[pass] id_right: forall f. id;f = f -- Satisfied under 4 substitutions");

    // --- Test 6: coproduct_functor_identity: left(id) = id -- Satisfied, no vars ---
    let law = &catalog[4];
    assert_eq!(law.name, "coproduct_functor_identity");
    assert_eq!(law.vars.len(), 0, "coproduct_functor_identity has 0 vars");
    assert_eq!(count_test_substitutions(&law.vars), 1, "0 vars -> 1 substitution");
    let result = check_quantified_law(law);
    assert_eq!(result, LawCheckResult::Satisfied, "coproduct_functor_identity Satisfied");
    println!("[pass] coproduct_functor_identity: left(id) = id -- Satisfied (no vars)");

    // --- Test 7: coproduct_functor_composition: forall f g. left(f;g) = left(f);left(g) -- 16 subst ---
    let law = &catalog[5];
    assert_eq!(law.name, "coproduct_functor_composition");
    assert_eq!(law.vars.len(), 2, "coproduct_functor_composition has 2 vars");
    assert_eq!(count_test_substitutions(&law.vars), 16, "2 vars -> 16 substitutions");
    let result = check_quantified_law(law);
    assert_eq!(result, LawCheckResult::Satisfied, "coproduct_functor_composition Satisfied");
    println!("[pass] coproduct_functor_composition: forall f g. left(f;g) = left(f);left(g) -- Satisfied under 16 substitutions");

    // --- Test 8: roundtrip: axiom-requiring, NOT inferable ---
    let law = &catalog[6];
    assert_eq!(law.name, "roundtrip");
    assert!(law.axiom.is_some(), "roundtrip requires an axiom");
    assert_eq!(law.axiom.as_deref(), Some("hinv"), "roundtrip axiom is hinv");
    // check_quantified_law returns NotApplicable for axiom laws.
    let result = check_quantified_law(law);
    assert_eq!(result, LawCheckResult::NotApplicable, "axiom law -> NotApplicable (CutElim cannot verify)");
    // infer_quantified_laws skips axiom laws.
    let serialize_deserialize = gcomp(garr("serialize"), garr("deserialize"));
    let inferred = infer_quantified_laws(&serialize_deserialize);
    assert!(
        !inferred.iter().any(|l| l.name == "roundtrip"),
        "roundtrip is NOT inferable (axiom-requiring, skipped)"
    );
    println!("[pass] roundtrip: axiom-requiring, NOT inferable (skipped in inference)");

    // --- Test 9: infer_quantified_laws for first(f) -> functor_identity + functor_composition ---
    let inferred = infer_quantified_laws(&gfirst(garr("f")));
    assert!(satisfies(&inferred, "functor_identity"), "first(f) satisfies functor_identity");
    assert!(satisfies(&inferred, "functor_composition"), "first(f) satisfies functor_composition");
    assert!(!satisfies(&inferred, "id_left"), "first(f) does NOT get id_left (has functor structure)");
    assert!(!satisfies(&inferred, "id_right"), "first(f) does NOT get id_right");
    assert!(!satisfies(&inferred, "coproduct_functor_identity"), "first(f) does NOT get coproduct laws");
    assert_eq!(inferred.len(), 2, "first(f) -> exactly 2 laws");
    println!("[pass] infer_quantified_laws for first(f): returns functor_identity + functor_composition");

    // --- Test 10: infer_quantified_laws for arr("sort") -> id_left + id_right ---
    let inferred = infer_quantified_laws(&garr("sort"));
    assert!(satisfies(&inferred, "id_left"), "arr(\"sort\") satisfies id_left (universal)");
    assert!(satisfies(&inferred, "id_right"), "arr(\"sort\") satisfies id_right (universal)");
    assert!(!satisfies(&inferred, "functor_identity"), "arr(\"sort\") does NOT get functor laws");
    assert!(!satisfies(&inferred, "coproduct_functor_identity"), "arr(\"sort\") does NOT get coproduct laws");
    assert_eq!(inferred.len(), 2, "arr(\"sort\") -> exactly 2 laws");
    println!("[pass] infer_quantified_laws for arr(\"sort\"): returns id_left + id_right (universal)");

    // --- Test 11: infer_quantified_laws for left(f) -> coproduct_functor_identity + composition ---
    let inferred = infer_quantified_laws(&gleft(garr("f")));
    assert!(satisfies(&inferred, "coproduct_functor_identity"), "left(f) satisfies coproduct_functor_identity");
    assert!(satisfies(&inferred, "coproduct_functor_composition"), "left(f) satisfies coproduct_functor_composition");
    assert!(!satisfies(&inferred, "functor_identity"), "left(f) does NOT get functor laws");
    assert!(!satisfies(&inferred, "id_left"), "left(f) does NOT get id_left (has coproduct structure)");
    assert_eq!(inferred.len(), 2, "left(f) -> exactly 2 laws");
    println!("[pass] infer_quantified_laws for left(f): returns coproduct_functor_identity + composition");

    // --- Test 12: bogus law first(f) = f: Violated ---
    let bogus = QuantifiedLaw {
        name: "bogus_first_eq_f".to_string(),
        vars: vec![LawVar("f".to_string())],
        lhs: LawExpr::First(Box::new(LawExpr::Var(LawVar("f".to_string())))),
        rhs: LawExpr::Var(LawVar("f".to_string())),
        axiom: None,
    };
    let result = check_quantified_law(&bogus);
    assert_eq!(result, LawCheckResult::Violated, "bogus law first(f) = f is Violated");
    // Specifically: it fails under the arr("test_f") substitution.
    let mut subst = LawSubst::new();
    subst.bind("f", garr("test_f"));
    let lhs = instantiate(&bogus.lhs, &subst);
    let rhs = instantiate(&bogus.rhs, &subst);
    assert!(
        !law_equal(&lhs, &rhs),
        "first(arr(\"test_f\")) != arr(\"test_f\") under CutElim"
    );
    println!("[pass] bogus law first(f) = f: Violated (fails under substitution with arr(\"test_f\"))");

    // --- Test 13: display uses "forall" explicitly ---
    let law = &catalog[1]; // functor_composition
    let display = format!("{}", law);
    assert!(
        display.contains("forall"),
        "display uses 'forall' explicitly: {}",
        display
    );
    assert!(
        display.contains("forall f g"),
        "display shows 'forall f g': {}",
        display
    );
    println!("[pass] display uses \"forall\" explicitly (not free variables)");
    println!("       e.g. {}", display);

    // --- Test 14: explicit quantification matches implicit ---
    // The implicit approach (law_inference.rs) checks with a single
    // substitution (arr("f"), arr("g")). The explicit approach checks under
    // multiple substitutions. Both should agree on Satisfied/Violated for
    // the CutElim-proven structural laws.
    let implicit_fid = law_equal(&gfirst(gid()), &gid());
    let explicit_fid = check_quantified_law(&catalog[0]) == LawCheckResult::Satisfied;
    assert_eq!(
        implicit_fid, explicit_fid,
        "functor_identity: implicit matches explicit"
    );

    let f = garr("f");
    let g = garr("g");
    let implicit_fcomp = law_equal(&gfirst(gcomp(f.clone(), g.clone())), &gcomp(gfirst(f), gfirst(g)));
    let explicit_fcomp = check_quantified_law(&catalog[1]) == LawCheckResult::Satisfied;
    assert_eq!(
        implicit_fcomp, explicit_fcomp,
        "functor_composition: implicit matches explicit"
    );

    let implicit_id_left = law_equal(&gcomp(garr("f"), gid()), &garr("f"));
    let explicit_id_left = check_quantified_law(&catalog[2]) == LawCheckResult::Satisfied;
    assert_eq!(
        implicit_id_left, explicit_id_left,
        "id_left: implicit matches explicit"
    );

    let implicit_id_right = law_equal(&gcomp(gid(), garr("f")), &garr("f"));
    let explicit_id_right = check_quantified_law(&catalog[3]) == LawCheckResult::Satisfied;
    assert_eq!(
        implicit_id_right, explicit_id_right,
        "id_right: implicit matches explicit"
    );
    println!("[pass] explicit quantification matches implicit (same results as law_inference.rs pattern)");

    // --- Test 15: Var vs Const distinction ---
    // Var("f") is a quantified variable; Const("sort") is a concrete arrow.
    // instantiate with Var unbound panics; with Const it produces Arr(name).
    let mut subst = LawSubst::new();
    subst.bind("f", garr("concrete_f"));
    let var_result = instantiate(&LawExpr::Var(LawVar("f".to_string())), &subst);
    assert_eq!(var_result, garr("concrete_f"), "Var(f) instantiates to the bound graph");
    let const_result = instantiate(&LawExpr::Const("sort".to_string()), &subst);
    assert_eq!(const_result, garr("sort"), "Const(\"sort\") instantiates to Arr(\"sort\")");
    println!("[pass] Var vs Const distinction: Var binds to substitution, Const is a concrete arrow");

    print_section("All tests passed");
    println!();
    println!("Summary:");
    println!("  Quantified law syntax: forall vars. lhs = rhs");
    println!("  CutElim-proven (structural, axiom: None):");
    println!("    - functor_identity:        forall f. first(id) = id              (ceFirstId)");
    println!("    - functor_composition:     forall f g. first(f;g) = first(f);first(g) (ceFirstFusion)");
    println!("    - id_left:                 forall f. f;id = f                     (ceIdRight)");
    println!("    - id_right:                forall f. id;f = f                     (ceIdLeft)");
    println!("    - coproduct_functor_identity:    left(id) = id                    (ceLeftId)");
    println!("    - coproduct_functor_composition: forall f g. left(f;g) = left(f);left(g) (ceLeftFusion)");
    println!("  Axiom-requiring (NOT CutElim-proven, axiom: Some):");
    println!("    - roundtrip:               serialize;deserialize = id  [axiom: hinv]");
    println!();
    println!("Answer to ADR-0076 OQ#4: higher-order laws CAN express explicit");
    println!("universal quantification over arrows. The syntax `forall f g. lhs = rhs`");

    println!("binds variables explicitly (LawVar), distinct from concrete arrows");
    println!("(Const). Checking instantiates variables under multiple test");
    println!("substitutions (4^N for N vars) and verifies via CutElim. This is a");
    println!("HEURISTIC (not a proof -- the real proof is in Lean); it demonstrates");
    println!("the SYNTAX and CHECKING MECHANISM, not completeness.");
    println!();
    println!("Still open:");
    println!("  - Completeness: heuristic testing vs proof (Lean proves for all arrows).");
    println!("  - Quantifier syntax for TYPES not just arrows (e.g. forall A B. ...).");
    println!("  - The precise surface syntax (forall vs implicit scoping) is a");
    println!("    language design decision deferred to the surface syntax ADR.");
}
