//! Explicit `forall f g. lhs = rhs` quantified law syntax over the production
//! `Scheme` IR (ADR-0076 Open Question #4).
//!
//! The research PoC in `arrow-calculus-kernel-poc/src/quantified_laws.rs`
//! prototypes higher-order law *quantifier* syntax: laws that explicitly
//! universally quantify over arrows (`forall f g. first(f;g) = first(f);first(g)`),
//! distinct from concrete base arrows. The PoC operates on `PolyGraph` (a
//! separate research IR). This module ports the concept to the production
//! [`Scheme`](crate::scheme::Scheme) kernel.
//!
//! # What this is
//!
//! A [`QuantifiedLaw`] is `forall vars. lhs = rhs` where `lhs`/`rhs` are
//! [`LawExpr`]s — graph expressions with quantified variables. Variables are
//! explicitly bound by `vars` (a [`LawVar`]), distinct from concrete base
//! arrows ([`LawExpr::Const`]). The checker instantiates variables under
//! multiple test substitutions (the cartesian product of a representative set
//! of test arrows) and verifies each instantiation via
//! [`law_equal`](crate::law_inference::law_equal) (CutElim normalization).
//!
//! # What this is NOT (honesty note)
//!
//! Testing under multiple substitutions is a **heuristic, not a proof**. We
//! cannot test ALL possible arrows (infinite). The real proof is in Lean
//! (`TraitInference.lean` proves these laws for all arrows via CutElim). This
//! module demonstrates the **syntax** (explicit `forall` quantifier) and the
//! **checking mechanism** (substitution-based testing), not completeness. The
//! heuristic is strong for CutElim-proven structural laws (the rewrites are
//! schema-level — they fire for any inner arrow), but it is NOT a substitute
//! for the Lean proof.
//!
//! # Porting notes
//!
//! The PoC's `PolyGraph` has a `Left` variant (coproduct functor) and an `Id`
//! variant. The production `Scheme` has **no** `Left` variant (no coproduct
//! functor — `Choice` routes on `Either` but is not a functor) and **no** `Id`
//! variant (identity is the base arrow `arr_native("id", [])`). Accordingly:
//!
//!   - [`LawExpr`] has **no** `Left` variant. The coproduct functor laws
//!     (`coproduct_functor_identity`, `coproduct_functor_composition`) are NOT
//!     ported.
//!   - [`LawExpr::Id`] instantiates to `Scheme::arr_native("id", [])`.
//!   - [`LawExpr::App`] mirrors `Scheme::App { callee, args: Vec<Scheme> }`
//!     (a callee plus a vector of argument schemes), not the PoC's unary `App`.
//!
//! The CutElim normalizer is NOT duplicated: this module reuses
//! [`law_equal`](crate::law_inference::law_equal) from
//! [`law_inference`](crate::law_inference).

use crate::law_inference::law_equal;
use crate::scheme::Scheme;
use std::collections::HashMap;
use std::fmt;

/// A variable in a law equation. Universally quantified.
///
/// `"f"` means "for all arrows f of the appropriate type". Distinct from
/// [`LawExpr::Const`], which is a specific named base arrow.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LawVar(pub String);

/// A law expression: a [`Scheme`] graph with quantified variables.
///
/// Variables are explicitly bound by [`QuantifiedLaw::vars`], not free. Maps
/// directly to [`Scheme`]:
/// - [`Var`](LawExpr::Var)`(f)` is a quantified variable (instantiated to a
///   concrete `Scheme` via [`LawSubst`]).
/// - [`Const`](LawExpr::Const)`(name)` is a concrete base arrow:
///   `Scheme::arr_native(name, [])`.
/// - [`Id`](LawExpr::Id) is the identity: `Scheme::arr_native("id", [])`.
/// - [`Seq`](LawExpr::Seq), [`First`](LawExpr::First),
///   [`Choice`](LawExpr::Choice), [`Loop`](LawExpr::Loop),
///   [`App`](LawExpr::App) mirror the corresponding `Scheme` variants.
/// - There is **no** `Left` variant — `Scheme` has no coproduct functor.
#[derive(Clone, Debug, PartialEq)]
pub enum LawExpr {
    /// A quantified variable reference. Universally quantified — "for all
    /// arrows f". Distinct from [`Const`](LawExpr::Const), a specific arrow.
    Var(LawVar),
    /// A concrete base arrow (a constant, not a variable).
    /// e.g. `Const("sort")` is a specific arrow; `Var("f")` is any arrow.
    Const(String),
    /// Polymorphic identity: instantiates to `Scheme::arr_native("id", [])`.
    Id,
    /// Sequential composition: `f >>> g` (written `f ; g` in display).
    Seq(Box<LawExpr>, Box<LawExpr>),
    /// `first` (product functoriality): `first(f)`.
    First(Box<LawExpr>),
    /// `ArrowChoice` routing: `choice(f, g)`.
    Choice(Box<LawExpr>, Box<LawExpr>),
    /// `ArrowLoop` (trace/fixpoint): `loop(f)`.
    Loop(Box<LawExpr>),
    /// `app` / `ArrowApply`: `app(callee, args...)`. Mirrors
    /// `Scheme::App { callee, args }` (a callee plus a vector of arguments).
    App(Box<LawExpr>, Vec<LawExpr>),
}

/// A quantified law: `forall vars. lhs = rhs`.
///
/// The `vars` vector lists the universally quantified variables. The law
/// holds iff for ALL substitutions of arrows into those variables, the
/// instantiated `lhs` and `rhs` are extensionally equal (normalize to the
/// same form under CutElim, or hold via a semantic axiom).
///
/// `axiom`: `None` = CutElim-proven (structural law); `Some(name)` = the law
/// requires a semantic axiom (not provable by CutElim alone).
pub struct QuantifiedLaw {
    /// Short name, e.g. "functor_composition".
    pub name: String,
    /// Universally quantified variables, e.g. `[LawVar("f"), LawVar("g")]`.
    /// Empty = no quantification (a ground equation).
    pub vars: Vec<LawVar>,
    /// Left-hand side of the equation.
    pub lhs: LawExpr,
    /// Right-hand side of the equation.
    pub rhs: LawExpr,
    /// `None` = CutElim-proven; `Some(name)` = requires a semantic axiom.
    pub axiom: Option<String>,
}

/// A substitution mapping law variables to concrete [`Scheme`]s.
///
/// Instantiating a [`LawExpr`] with a substitution produces a concrete
/// `Scheme` that can be checked via
/// [`law_equal`](crate::law_inference::law_equal) (CutElim normalization).
#[derive(Clone, Debug, Default)]
pub struct LawSubst {
    map: HashMap<String, Scheme>,
}

impl LawSubst {
    /// Create an empty substitution.
    pub fn new() -> Self {
        Self::default()
    }

    /// Bind a law variable to a concrete scheme.
    pub fn bind(&mut self, var: &str, scheme: Scheme) {
        self.map.insert(var.to_string(), scheme);
    }

    /// Look up the scheme bound to a variable.
    pub fn get(&self, var: &str) -> Option<&Scheme> {
        self.map.get(var)
    }
}

/// Instantiate a [`LawExpr`] with a substitution, producing a concrete
/// [`Scheme`].
///
/// - [`Var`](LawExpr::Var)`(f)` -> the scheme bound to `f` in the substitution
///   (panics if unbound — all quantified variables must be bound before
///   instantiation).
/// - [`Const`](LawExpr::Const)`(name)` -> `Scheme::arr_native(name, [])` (a
///   concrete base arrow, not a variable).
/// - [`Id`](LawExpr::Id) -> `Scheme::arr_native("id", [])`.
/// - Combinators -> recurse structurally, mirroring `Scheme`.
pub fn instantiate(expr: &LawExpr, subst: &LawSubst) -> Scheme {
    match expr {
        LawExpr::Var(LawVar(name)) => subst.get(name).cloned().unwrap_or_else(|| {
            panic!("unbound law variable: {} (all quantified vars must be bound)", name)
        }),
        LawExpr::Const(name) => Scheme::arr_native(name, vec![]),
        LawExpr::Id => Scheme::arr_native("id", vec![]),
        LawExpr::Seq(a, b) => Scheme::Seq {
            fst: Box::new(instantiate(a, subst)),
            snd: Box::new(instantiate(b, subst)),
        },
        LawExpr::First(a) => Scheme::First {
            inner: Box::new(instantiate(a, subst)),
        },
        LawExpr::Choice(a, b) => Scheme::Choice {
            l: Box::new(instantiate(a, subst)),
            r: Box::new(instantiate(b, subst)),
        },
        LawExpr::Loop(a) => Scheme::Loop {
            body: Box::new(instantiate(a, subst)),
        },
        LawExpr::App(callee, args) => Scheme::App {
            callee: Box::new(instantiate(callee, subst)),
            args: args.iter().map(|a| instantiate(a, subst)).collect(),
        },
    }
}

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
///
/// - `arr("test_f")`: a generic opaque arrow (CutElim treats it as opaque).
/// - `id`: the identity arrow (tests id-related rewrites: ceIdLeft, ceIdRight,
///   ceFirstId).
/// - `seq(arr("test_a"), arr("test_b"))`: a composed arrow (tests fusion:
///   ceFirstFusion).
/// - `first(arr("test_h"))`: a first-shaped arrow (tests nesting).
fn test_arrows() -> Vec<Scheme> {
    vec![
        // A generic opaque arrow. CutElim treats Arr(name) as opaque -- no
        // rewrite fires on it directly. This is the "default" case.
        Scheme::arr_native("test_f", vec![]),
        // The identity arrow. Tests id-related rewrites: ceIdLeft
        // (seq(id, G) ==> G), ceIdRight (seq(G, id) ==> G), ceFirstId
        // (first(id) ==> id).
        Scheme::arr_native("id", vec![]),
        // A composed arrow. Tests fusion rewrites: ceFirstFusion
        // (seq(first G, first H) ==> first(seq G H)).
        Scheme::seq(
            Scheme::arr_native("test_a", vec![]),
            Scheme::arr_native("test_b", vec![]),
        ),
        // A first-shaped arrow. Tests nesting: first(first(...)) and
        // interaction between first and other combinators.
        Scheme::First {
            inner: Box::new(Scheme::arr_native("test_h", vec![])),
        },
    ]
}

/// Generate test substitutions for a set of variables. Each variable gets
/// assigned one of the test arrows; the result is the cartesian product of
/// all test arrows across all variables.
///
/// For 0 vars: 1 substitution (the empty substitution).
/// For 1 var: 4 substitutions (4 test arrows).
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

/// Check a quantified law by testing it under multiple substitutions.
///
/// - If `axiom.is_some()`: return [`NotApplicable`](LawCheckResult::NotApplicable)
///   (CutElim cannot verify axiom-requiring laws — they need a semantic axiom,
///   not normalization).
/// - Otherwise: instantiate `lhs` and `rhs` under each test substitution and
///   check [`law_equal`](crate::law_inference::law_equal). If ALL pass,
///   [`Satisfied`](LawCheckResult::Satisfied). If ANY fails,
///   [`Violated`](LawCheckResult::Violated).
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

/// The built-in quantified law catalog.
///
/// Each law explicitly binds its universally quantified variables. Laws are
/// either CutElim-proven (`axiom: None`) or axiom-requiring
/// (`axiom: Some(name)`).
///
/// CutElim-proven structural laws (the four portable rewrites):
/// - `functor_identity`:        `first(id) = id`              (ceFirstId)
/// - `functor_composition`:     `first(f;g) = first(f);first(g)` (ceFirstFusion)
/// - `id_left`:                 `f;id = f`                     (ceIdRight)
/// - `id_right`:                `id;f = f`                     (ceIdLeft)
///
/// Axiom-requiring law (NOT CutElim-proven):
/// - `roundtrip`:               `serialize;deserialize = id`   (needs axiom hinv)
///
/// The two `Left`-based coproduct functor laws from the PoC
/// (`coproduct_functor_identity`, `coproduct_functor_composition`) are NOT
/// ported: `Scheme` has no coproduct functor (`Left`) variant.
pub fn builtin_quantified_laws() -> Vec<QuantifiedLaw> {
    vec![
        // --- Functor laws (product functoriality, CutElim-proven) ---
        // functor_identity: first(id) = id  (ceFirstId)
        QuantifiedLaw {
            name: "functor_identity".into(),
            // first(id) = id -- f is quantified but unused (the law is about
            // the functor's interaction with id, not about f). We keep f in
            // vars to match the ADR's `forall f. map id = id` framing.
            vars: vec![LawVar("f".into())],
            lhs: LawExpr::First(Box::new(LawExpr::Id)),
            rhs: LawExpr::Id,
            axiom: None,
        },
        // functor_composition: first(f;g) = first(f);first(g)  (ceFirstFusion)
        QuantifiedLaw {
            name: "functor_composition".into(),
            vars: vec![LawVar("f".into()), LawVar("g".into())],
            lhs: LawExpr::First(Box::new(LawExpr::Seq(
                Box::new(LawExpr::Var(LawVar("f".into()))),
                Box::new(LawExpr::Var(LawVar("g".into()))),
            ))),
            rhs: LawExpr::Seq(
                Box::new(LawExpr::First(Box::new(LawExpr::Var(LawVar("f".into()))))),
                Box::new(LawExpr::First(Box::new(LawExpr::Var(LawVar("g".into()))))),
            ),
            axiom: None,
        },
        // --- Identity laws (universal, CutElim-proven) ---
        // f >>> id = f  (ceIdRight: seq(G, id) ==> G)
        QuantifiedLaw {
            name: "id_left".into(),
            vars: vec![LawVar("f".into())],
            lhs: LawExpr::Seq(
                Box::new(LawExpr::Var(LawVar("f".into()))),
                Box::new(LawExpr::Id),
            ),
            rhs: LawExpr::Var(LawVar("f".into())),
            axiom: None,
        },
        // id >>> f = f  (ceIdLeft: seq(id, G) ==> G)
        QuantifiedLaw {
            name: "id_right".into(),
            vars: vec![LawVar("f".into())],
            lhs: LawExpr::Seq(
                Box::new(LawExpr::Id),
                Box::new(LawExpr::Var(LawVar("f".into()))),
            ),
            rhs: LawExpr::Var(LawVar("f".into())),
            axiom: None,
        },
        // --- Axiom-requiring law (NOT CutElim-proven) ---
        // serialize >>> deserialize = id -- a semantic fact about specific
        // base arrows. CutElim treats arr("serialize") and arr("deserialize")
        // as opaque; it cannot simplify their composition to id. This law
        // requires a semantic axiom (hinv: serialize and deserialize are
        // inverses). Mirrors EquationalLawInference.lean.
        QuantifiedLaw {
            name: "roundtrip".into(),
            vars: vec![],
            lhs: LawExpr::Seq(
                Box::new(LawExpr::Const("serialize".into())),
                Box::new(LawExpr::Const("deserialize".into())),
            ),
            rhs: LawExpr::Id,
            axiom: Some("hinv".into()),
        },
    ]
}

// ============================================================================
// Display: show laws with explicit forall
// ============================================================================

impl fmt::Display for LawExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LawExpr::Var(v) => write!(f, "{}", v.0),
            LawExpr::Const(name) => write!(f, "{}", name),
            LawExpr::Id => write!(f, "id"),
            LawExpr::Seq(a, b) => write!(f, "({} ; {})", a, b),
            LawExpr::First(a) => write!(f, "first({})", a),
            LawExpr::Choice(a, b) => write!(f, "choice({}, {})", a, b),
            LawExpr::Loop(a) => write!(f, "loop({})", a),
            LawExpr::App(callee, args) => {
                let args = args
                    .iter()
                    .map(|a| a.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "app({}, [{}])", callee, args)
            }
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
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn id() -> Scheme {
        Scheme::arr_native("id", vec![])
    }

    #[test]
    fn instantiate_var_produces_bound_scheme() {
        let mut subst = LawSubst::new();
        subst.bind("f", Scheme::arr_native("concrete_f", vec![]));
        let result = instantiate(&LawExpr::Var(LawVar("f".into())), &subst);
        assert_eq!(result, Scheme::arr_native("concrete_f", vec![]));
    }

    #[test]
    fn instantiate_id_produces_identity_arrow() {
        let subst = LawSubst::new();
        let result = instantiate(&LawExpr::Id, &subst);
        assert_eq!(result, id());
    }

    #[test]
    fn instantiate_const_produces_base_arrow() {
        let subst = LawSubst::new();
        let result = instantiate(&LawExpr::Const("sort".into()), &subst);
        assert_eq!(result, Scheme::arr_native("sort", vec![]));
    }

    #[test]
    #[should_panic(expected = "unbound law variable: f")]
    fn instantiate_unbound_var_panics() {
        let subst = LawSubst::new();
        let _ = instantiate(&LawExpr::Var(LawVar("f".into())), &subst);
    }

    #[test]
    fn instantiate_seq_produces_scheme_seq() {
        let mut subst = LawSubst::new();
        subst.bind("f", Scheme::arr_native("a", vec![]));
        subst.bind("g", Scheme::arr_native("b", vec![]));
        let result = instantiate(
            &LawExpr::Seq(
                Box::new(LawExpr::Var(LawVar("f".into()))),
                Box::new(LawExpr::Var(LawVar("g".into()))),
            ),
            &subst,
        );
        assert_eq!(
            result,
            Scheme::seq(
                Scheme::arr_native("a", vec![]),
                Scheme::arr_native("b", vec![])
            )
        );
    }

    #[test]
    fn check_functor_identity_satisfied() {
        let catalog = builtin_quantified_laws();
        let law = catalog
            .iter()
            .find(|l| l.name == "functor_identity")
            .expect("functor_identity in catalog");
        assert_eq!(check_quantified_law(law), LawCheckResult::Satisfied);
    }

    #[test]
    fn check_functor_composition_satisfied() {
        let catalog = builtin_quantified_laws();
        let law = catalog
            .iter()
            .find(|l| l.name == "functor_composition")
            .expect("functor_composition in catalog");
        assert_eq!(check_quantified_law(law), LawCheckResult::Satisfied);
    }

    #[test]
    fn check_id_left_satisfied() {
        let catalog = builtin_quantified_laws();
        let law = catalog
            .iter()
            .find(|l| l.name == "id_left")
            .expect("id_left in catalog");
        assert_eq!(check_quantified_law(law), LawCheckResult::Satisfied);
    }

    #[test]
    fn check_id_right_satisfied() {
        let catalog = builtin_quantified_laws();
        let law = catalog
            .iter()
            .find(|l| l.name == "id_right")
            .expect("id_right in catalog");
        assert_eq!(check_quantified_law(law), LawCheckResult::Satisfied);
    }

    #[test]
    fn check_roundtrip_not_applicable() {
        let catalog = builtin_quantified_laws();
        let law = catalog
            .iter()
            .find(|l| l.name == "roundtrip")
            .expect("roundtrip in catalog");
        assert!(law.axiom.is_some());
        assert_eq!(law.axiom.as_deref(), Some("hinv"));
        assert_eq!(check_quantified_law(law), LawCheckResult::NotApplicable);
    }

    #[test]
    fn generate_test_substitutions_zero_vars_one_subst() {
        let vars: Vec<LawVar> = vec![];
        let substs = generate_test_substitutions(&vars);
        assert_eq!(substs.len(), 1, "0 vars -> 1 substitution");
    }

    #[test]
    fn generate_test_substitutions_one_var_four_substs() {
        let vars = vec![LawVar("f".into())];
        let substs = generate_test_substitutions(&vars);
        assert_eq!(substs.len(), 4, "1 var -> 4 substitutions");
    }

    #[test]
    fn generate_test_substitutions_two_vars_sixteen_substs() {
        let vars = vec![LawVar("f".into()), LawVar("g".into())];
        let substs = generate_test_substitutions(&vars);
        assert_eq!(substs.len(), 16, "2 vars -> 16 substitutions");
    }

    #[test]
    fn catalog_has_exactly_five_laws() {
        let catalog = builtin_quantified_laws();
        assert_eq!(catalog.len(), 5, "exactly 5 laws (4 CutElim-proven + 1 axiom)");
        let proven = catalog.iter().filter(|l| l.axiom.is_none()).count();
        let axiom = catalog.iter().filter(|l| l.axiom.is_some()).count();
        assert_eq!(proven, 4, "4 CutElim-proven laws");
        assert_eq!(axiom, 1, "1 axiom-requiring law");
    }

    #[test]
    fn bogus_law_first_eq_f_is_violated() {
        // first(f) = f is NOT true: first adds a product component.
        let bogus = QuantifiedLaw {
            name: "bogus_first_eq_f".into(),
            vars: vec![LawVar("f".into())],
            lhs: LawExpr::First(Box::new(LawExpr::Var(LawVar("f".into())))),
            rhs: LawExpr::Var(LawVar("f".into())),
            axiom: None,
        };
        assert_eq!(check_quantified_law(&bogus), LawCheckResult::Violated);
        // Specifically: it fails under the arr("test_f") substitution.
        let mut subst = LawSubst::new();
        subst.bind("f", Scheme::arr_native("test_f", vec![]));
        let lhs = instantiate(&bogus.lhs, &subst);
        let rhs = instantiate(&bogus.rhs, &subst);
        assert!(
            !law_equal(&lhs, &rhs),
            "first(arr(\"test_f\")) != arr(\"test_f\") under CutElim"
        );
    }

    #[test]
    fn display_uses_forall_explicitly() {
        let catalog = builtin_quantified_laws();
        let law = catalog
            .iter()
            .find(|l| l.name == "functor_composition")
            .expect("functor_composition in catalog");
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
    }

    #[test]
    fn display_law_expr() {
        assert_eq!(format!("{}", LawExpr::Id), "id");
        assert_eq!(format!("{}", LawExpr::Const("sort".into())), "sort");
        assert_eq!(format!("{}", LawExpr::Var(LawVar("f".into()))), "f");
        assert_eq!(
            format!("{}", LawExpr::First(Box::new(LawExpr::Id))),
            "first(id)"
        );
    }
}
