// Phase 4 (Polymorphic): Annotation-Free Polymorphic Inference over Arrow Graphs
//
// This prototype extends `proof_graph_tests.rs` with POLYMORPHIC TYPES and
// Hindley-Milner-style annotation-free inference over the graph structure.
//
// The headline claim of FORMALISM_PROOF_GRAPHS.md §7 is that useful
// properties of arrow graphs can be inferred from structure ALONE, with no
// type annotations on the graph. The monomorphic prototype showed this for
// fixed types (Int, Bool, [Int]). Here we show the full power: with a
// POLYMORPHIC signature, the graph's PRINCIPAL (most general) type is
// recovered purely from structure + unification.
//
// Key demonstration:
//   comp(first(id), id)  ⟹  (α × β) ⇝ (α × β)
// with NO annotations — purely from structure + unification. This is the
// real power of annotation-free inference.
//
// Extensions over the monomorphic prototype:
//   1. Ty::Var(String) — type variables in the signature.
//   2. Ty::Arrow(A, B) — arrow types as first-class types (for higher-order
//      base arrows like `map : (α⇝β) ⇝ ([α]⇝[β])`).
//   3. Hindley-Milner unification over the graph: fresh variables are
//      generated at each polymorphic base arrow and unified across
//      composition boundaries.
//   4. Principal type inference: the MOST GENERAL type is inferred, then
//      generalized (free vars renamed to α, β, γ, …).
//   5. Generalized proof obligations: "the middle type UNIFIES" rather than
//      "the middle type MATCHES".
//   6. The graph constructors `first`/`left`/`loop` carry NO type argument —
//      the side/feedback channel is a fresh variable, inferred by unification.
//      This is what makes the graph truly annotation-free.

use std::collections::HashMap;
use std::fmt;

// ============================================================================
// 1. Polymorphic Types (mirrors ProofGraphs.lean §1, with type variables)
// ============================================================================

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Ty {
    Atom(String),               // base type (Int, Bool, String, ...)
    Var(String),                // type variable (α, β, t0, ...)
    Prod(Box<Ty>, Box<Ty>),     // A × B   (read: A ∧ B in proof mode)
    Sum(Box<Ty>, Box<Ty>),      // A + B   (read: A ∨ B in proof mode)
    Arrow(Box<Ty>, Box<Ty>),    // A ⇝ B   (arrow type as a first-class type,
                                //         needed for higher-order base arrows)
    Unit,                       // ⊤
    Void,                       // ⊥
    List(Box<Ty>),              // [A]
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ty::Atom(s) => write!(f, "{}", s),
            Ty::Var(s) => write!(f, "{}", s),
            Ty::Prod(a, b) => write!(f, "({} × {})", a, b),
            Ty::Sum(a, b) => write!(f, "({} + {})", a, b),
            Ty::Arrow(a, b) => write!(f, "({} ⇝ {})", a, b),
            Ty::Unit => write!(f, "()"),
            Ty::Void => write!(f, "⊥"),
            Ty::List(t) => write!(f, "[{}]", t),
        }
    }
}

impl Ty {
    /// Collect all free type-variable names, in order of first appearance.
    pub fn free_vars(&self) -> Vec<String> {
        fn go(t: &Ty, out: &mut Vec<String>) {
            match t {
                Ty::Var(s) => {
                    if !out.contains(s) {
                        out.push(s.clone());
                    }
                }
                Ty::Prod(a, b) | Ty::Sum(a, b) | Ty::Arrow(a, b) => {
                    go(a, out);
                    go(b, out);
                }
                Ty::List(t) => go(t, out),
                _ => {}
            }
        }
        let mut out = Vec::new();
        go(self, &mut out);
        out
    }

    /// Apply a variable renaming (a simple substitution mapping var → ty).
    pub fn apply_map(&self, map: &HashMap<String, Ty>) -> Ty {
        match self {
            Ty::Var(s) => map.get(s).cloned().unwrap_or_else(|| self.clone()),
            Ty::Prod(a, b) => Ty::Prod(
                Box::new(a.apply_map(map)),
                Box::new(b.apply_map(map)),
            ),
            Ty::Sum(a, b) => Ty::Sum(
                Box::new(a.apply_map(map)),
                Box::new(b.apply_map(map)),
            ),
            Ty::Arrow(a, b) => Ty::Arrow(
                Box::new(a.apply_map(map)),
                Box::new(b.apply_map(map)),
            ),
            Ty::List(t) => Ty::List(Box::new(t.apply_map(map))),
            other => other.clone(),
        }
    }
}

// ============================================================================
// 2. Substitution (Type Variable Bindings)
// ============================================================================

#[derive(Debug, Clone, Default)]
pub struct Substitution {
    bindings: HashMap<String, Ty>,
}

impl Substitution {
    pub fn new() -> Self {
        Substitution {
            bindings: HashMap::new(),
        }
    }

    pub fn insert(&mut self, var: String, ty: Ty) {
        self.bindings.insert(var, ty);
    }

    pub fn get(&self, var: &str) -> Option<&Ty> {
        self.bindings.get(var)
    }

    /// Apply the substitution fully (follow chains).
    pub fn apply(&self, ty: &Ty) -> Ty {
        match ty {
            Ty::Var(name) => match self.get(name) {
                Some(t) => self.apply(t),
                None => ty.clone(),
            },
            Ty::Prod(a, b) => Ty::Prod(
                Box::new(self.apply(a)),
                Box::new(self.apply(b)),
            ),
            Ty::Sum(a, b) => Ty::Sum(
                Box::new(self.apply(a)),
                Box::new(self.apply(b)),
            ),
            Ty::Arrow(a, b) => Ty::Arrow(
                Box::new(self.apply(a)),
                Box::new(self.apply(b)),
            ),
            Ty::List(t) => Ty::List(Box::new(self.apply(t))),
            other => other.clone(),
        }
    }

    /// Compose: (s1 ∘ s2) applies s2 first, then s1.
    pub fn compose(&self, other: &Substitution) -> Substitution {
        let mut result = self.clone();
        for (var, ty) in &other.bindings {
            result.insert(var.clone(), self.apply(ty));
        }
        result
    }
}

// ============================================================================
// 3. Unification (Constraint Solving) — Hindley-Milner
// ============================================================================

pub struct Unifier;

impl Unifier {
    /// Unify two types; returns a substitution if successful.
    pub fn unify(ty1: &Ty, ty2: &Ty) -> Option<Substitution> {
        let mut subst = Substitution::new();
        if Unifier::unify_with_subst(ty1, ty2, &mut subst) {
            Some(subst)
        } else {
            None
        }
    }

    /// Unify two types, accumulating bindings into `subst`.
    /// Applies `subst` to both sides first (so bindings discovered earlier
    /// in the same unification are respected).
    fn unify_with_subst(ty1: &Ty, ty2: &Ty, subst: &mut Substitution) -> bool {
        let ty1 = subst.apply(ty1);
        let ty2 = subst.apply(ty2);

        match (&ty1, &ty2) {
            // Identical atoms / unit / void
            (Ty::Atom(a), Ty::Atom(b)) => a == b,
            (Ty::Unit, Ty::Unit) => true,
            (Ty::Void, Ty::Void) => true,

            // Variables
            (Ty::Var(a), Ty::Var(b)) if a == b => true,
            (Ty::Var(a), b) => {
                if Unifier::occurs_in(a, b) {
                    false // occurs check fails (infinite type)
                } else {
                    subst.insert(a.clone(), b.clone());
                    true
                }
            }
            (a, Ty::Var(b)) => {
                if Unifier::occurs_in(b, a) {
                    false
                } else {
                    subst.insert(b.clone(), a.clone());
                    true
                }
            }

            // Structural constructors unify component-wise
            (Ty::Prod(a1, b1), Ty::Prod(a2, b2)) => {
                Unifier::unify_with_subst(a1, a2, subst)
                    && Unifier::unify_with_subst(b1, b2, subst)
            }
            (Ty::Sum(a1, b1), Ty::Sum(a2, b2)) => {
                Unifier::unify_with_subst(a1, a2, subst)
                    && Unifier::unify_with_subst(b1, b2, subst)
            }
            (Ty::Arrow(a1, b1), Ty::Arrow(a2, b2)) => {
                Unifier::unify_with_subst(a1, a2, subst)
                    && Unifier::unify_with_subst(b1, b2, subst)
            }
            (Ty::List(t1), Ty::List(t2)) => Unifier::unify_with_subst(t1, t2, subst),

            // No unification (head mismatch)
            _ => false,
        }
    }

    /// Occurs check: does variable `var` occur in type `ty`?
    fn occurs_in(var: &str, ty: &Ty) -> bool {
        match ty {
            Ty::Var(v) => v == var,
            Ty::Prod(a, b) | Ty::Sum(a, b) | Ty::Arrow(a, b) => {
                Unifier::occurs_in(var, a) || Unifier::occurs_in(var, b)
            }
            Ty::List(t) => Unifier::occurs_in(var, t),
            _ => false,
        }
    }
}

// ============================================================================
// 4. Arrow Graphs (annotation-free: first/left/loop carry NO type argument)
// ============================================================================

/// A polymorphic signature entry. The input/output may contain `Ty::Var`;
/// each use of the base arrow instantiates those variables freshly.
#[derive(Debug, Clone)]
pub struct PolySigEntry {
    pub name: &'static str,
    pub input: Ty,
    pub output: Ty,
}

/// An annotation-free arrow graph.
///
/// Unlike the monomorphic `Graph`, the `first`/`left`/`loop` constructors
/// carry NO type argument: the side/feedback channel is a FRESH type
/// variable, recovered by unification. This is what makes the graph truly
/// annotation-free — even the "carrier" types of the functorial/trace
/// combinators are inferred.
#[derive(Debug, Clone)]
pub enum PolyGraph {
    /// Polymorphic identity: α ⇝ α (α is fresh per use)
    Id,
    /// Composition: G ; H  (cut in proof mode)
    Comp(Box<PolyGraph>, Box<PolyGraph>),
    /// First (×-functoriality): A ⇝ B  ⟹  A×D ⇝ B×D  (D is a fresh var)
    First(Box<PolyGraph>),
    /// Left (+-functoriality): A ⇝ B  ⟹  A+D ⇝ B+D  (D is a fresh var)
    Left(Box<PolyGraph>),
    /// Loop (trace/fixpoint): A×C ⇝ B×C  ⟹  A ⇝ B  (C is a fresh var)
    Loop(Box<PolyGraph>),
    /// Base arrow from the (polymorphic) signature
    Arr(&'static str),
}

impl fmt::Display for PolyGraph {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PolyGraph::Id => write!(f, "id"),
            PolyGraph::Comp(g, h) => write!(f, "({} ; {})", g, h),
            PolyGraph::First(g) => write!(f, "first({})", g),
            PolyGraph::Left(g) => write!(f, "left({})", g),
            PolyGraph::Loop(g) => write!(f, "loop({})", g),
            PolyGraph::Arr(name) => write!(f, "{}", name),
        }
    }
}

// ============================================================================
// 5. Polymorphic Type Inference (Hindley-Milner over graphs)
// ============================================================================

/// The inference engine: a fresh-variable generator carrying a substitution.
pub struct PolyInfer {
    next_var: usize,
}

impl PolyInfer {
    pub fn new() -> Self {
        PolyInfer { next_var: 0 }
    }

    /// Generate a fresh type variable (internal name `t0`, `t1`, …).
    fn fresh_var(&mut self) -> Ty {
        let name = format!("t{}", self.next_var);
        self.next_var += 1;
        Ty::Var(name)
    }

    /// Instantiate a polymorphic signature entry: replace each distinct
    /// type variable in (input, output) with a fresh variable.
    fn instantiate(&mut self, entry: &PolySigEntry) -> (Ty, Ty) {
        let mut names: Vec<String> = Vec::new();
        for v in entry.input.free_vars() {
            if !names.contains(&v) {
                names.push(v);
            }
        }
        for v in entry.output.free_vars() {
            if !names.contains(&v) {
                names.push(v);
            }
        }
        let mut map: HashMap<String, Ty> = HashMap::new();
        for v in &names {
            map.insert(v.clone(), self.fresh_var());
        }
        (entry.input.apply_map(&map), entry.output.apply_map(&map))
    }

    /// Unify two types, merging the result into the running substitution.
    /// Returns an error message on failure (with both sides shown AFTER
    /// applying the current substitution, for a readable diagnostic).
    fn unify(
        &mut self,
        ty1: &Ty,
        ty2: &Ty,
        subst: &mut Substitution,
    ) -> Result<(), String> {
        let s1 = subst.apply(ty1);
        let s2 = subst.apply(ty2);
        if Unifier::unify_with_subst(&s1, &s2, subst) {
            Ok(())
        } else {
            Err(format!("{} does not unify with {}", s1, s2))
        }
    }

    /// The core inference: walk the graph, generating fresh variables and
    /// unifying across composition boundaries. Returns (input, output) with
    /// the running substitution applied.
    pub fn infer(
        &mut self,
        graph: &PolyGraph,
        sig: &[PolySigEntry],
        subst: &mut Substitution,
    ) -> Result<(Ty, Ty), String> {
        match graph {
            PolyGraph::Id => {
                let a = self.fresh_var();
                Ok((a.clone(), a))
            }

            PolyGraph::Comp(g, h) => {
                let (ga, gb) = self.infer(g, sig, subst)?;
                let (ha, hb) = self.infer(h, sig, subst)?;
                // Cut rule: the middle type must UNIFY (not merely match).
                self.unify(&gb, &ha, subst)
                    .map_err(|e| format!("Composition mismatch in ({} ; {}): {}", g, h, e))?;
                Ok((ga, hb))
            }

            PolyGraph::First(g) => {
                let (ga, gb) = self.infer(g, sig, subst)?;
                let d = self.fresh_var();
                Ok((
                    Ty::Prod(Box::new(ga), Box::new(d.clone())),
                    Ty::Prod(Box::new(gb), Box::new(d)),
                ))
            }

            PolyGraph::Left(g) => {
                let (ga, gb) = self.infer(g, sig, subst)?;
                let d = self.fresh_var();
                Ok((
                    Ty::Sum(Box::new(ga), Box::new(d.clone())),
                    Ty::Sum(Box::new(gb), Box::new(d)),
                ))
            }

            PolyGraph::Loop(g) => {
                // G : A×C ⇝ B×C  ⟹  loop G : A ⇝ B
                // A, B, C are all fresh; we unify G's input with A×C and
                // G's output with B×C, sharing C across both.
                let (ga, gb) = self.infer(g, sig, subst)?;
                let a = self.fresh_var();
                let b = self.fresh_var();
                let c = self.fresh_var();
                self.unify(&ga, &Ty::Prod(Box::new(a.clone()), Box::new(c.clone())), subst)
                    .map_err(|e| format!("Loop input mismatch in loop({}): {}", g, e))?;
                self.unify(&gb, &Ty::Prod(Box::new(b.clone()), Box::new(c)), subst)
                    .map_err(|e| format!("Loop output/feedback mismatch in loop({}): {}", g, e))?;
                Ok((a, b))
            }

            PolyGraph::Arr(name) => {
                let entry = sig
                    .iter()
                    .find(|e| e.name == *name)
                    .ok_or_else(|| format!("Unknown base arrow: {}", name))?;
                let (i, o) = self.instantiate(entry);
                Ok((i, o))
            }
        }
    }
}

/// The top-level annotation-free inference: infer the PRINCIPAL type of a
/// graph against a polymorphic signature, then generalize (rename free
/// variables to α, β, γ, …).
///
/// The graph carries NO type annotations; types flow from the polymorphic
/// signature through the graph structure via unification.
pub fn infer_type_poly(
    graph: &PolyGraph,
    sig: &[PolySigEntry],
) -> Result<(Ty, Ty), String> {
    let mut inf = PolyInfer::new();
    let mut subst = Substitution::new();
    let (i, o) = inf.infer(graph, sig, &mut subst)?;
    let (gi, go) = generalize_pair(&subst.apply(&i), &subst.apply(&o));
    Ok((gi, go))
}

/// Infer WITHOUT generalizing — returns the raw resolved types (useful for
/// checking specializations where we want to see the concrete variables).
pub fn infer_type_poly_raw(
    graph: &PolyGraph,
    sig: &[PolySigEntry],
) -> Result<(Ty, Ty, Substitution), String> {
    let mut inf = PolyInfer::new();
    let mut subst = Substitution::new();
    let (i, o) = inf.infer(graph, sig, &mut subst)?;
    Ok((subst.apply(&i), subst.apply(&o), subst))
}

// ============================================================================
// 6. Generalization (principal type = most general type)
// ============================================================================

/// Greek-letter names for the principal type, in order of appearance.
const GREEK: &[&str] = &["α", "β", "γ", "δ", "ε", "ζ", "η", "θ", "ι", "κ"];

/// Generalize a type: collect free variables in order of appearance and
/// rename them to α, β, γ, … (the conventional principal-type notation).
/// Falls back to τ{n} if there are more than `GREEK.len()` distinct vars.
pub fn generalize(ty: &Ty) -> Ty {
    let vars = ty.free_vars();
    let mut map: HashMap<String, Ty> = HashMap::new();
    for (idx, v) in vars.iter().enumerate() {
        let name = if idx < GREEK.len() {
            GREEK[idx].to_string()
        } else {
            format!("τ{}", idx)
        };
        map.insert(v.clone(), Ty::Var(name));
    }
    ty.apply_map(&map)
}

/// Generalize a pair (input, output) consistently: free vars are collected
/// across BOTH types (input first) so the same variable gets the same name.
pub fn generalize_pair(i: &Ty, o: &Ty) -> (Ty, Ty) {
    let mut vars = i.free_vars();
    for v in o.free_vars() {
        if !vars.contains(&v) {
            vars.push(v);
        }
    }
    let mut map: HashMap<String, Ty> = HashMap::new();
    for (idx, v) in vars.iter().enumerate() {
        let name = if idx < GREEK.len() {
            GREEK[idx].to_string()
        } else {
            format!("τ{}", idx)
        };
        map.insert(v.clone(), Ty::Var(name));
    }
    (i.apply_map(&map), o.apply_map(&map))
}

// ============================================================================
// 7. Generalized Proof Obligation Generation (polymorphic)
// ============================================================================

/// A proof obligation: a fact that must hold for the graph to be well-typed.
/// In the polymorphic setting, the obligation is that two types UNIFY
/// (rather than being syntactically equal).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PolyProofObligation {
    /// What must be proven (e.g. "t3 unifies with t5").
    pub fact: String,
    /// Where in the graph it came from.
    pub source: String,
    /// Whether it has been discharged (unification succeeded).
    pub discharged: bool,
}

/// Generate proof obligations from a polymorphic graph.
///
/// For each composition boundary, the obligation is "the middle type
/// UNIFIES" (with the unifier recorded when discharged). For each loop, the
/// obligation is "the feedback channel type UNIFIES across both ports".
pub fn proof_obligations_poly(
    graph: &PolyGraph,
    sig: &[PolySigEntry],
) -> Vec<PolyProofObligation> {
    let mut obligations = Vec::new();
    let mut inf = PolyInfer::new();
    let mut subst = Substitution::new();
    let _ = inf.infer_obligations(graph, sig, &mut subst, &mut obligations);
    obligations
}

impl PolyInfer {
    fn infer_obligations(
        &mut self,
        graph: &PolyGraph,
        sig: &[PolySigEntry],
        subst: &mut Substitution,
        obligations: &mut Vec<PolyProofObligation>,
    ) -> Result<(Ty, Ty), String> {
        match graph {
            PolyGraph::Id => {
                let a = self.fresh_var();
                Ok((a.clone(), a))
            }

            PolyGraph::Comp(g, h) => {
                let (ga, gb) = self.infer_obligations(g, sig, subst, obligations)?;
                let (ha, hb) = self.infer_obligations(h, sig, subst, obligations)?;
                let gb_s = subst.apply(&gb);
                let ha_s = subst.apply(&ha);
                let source = format!("comp({}, {})", g, h);
                match self.unify(&gb, &ha, subst) {
                    Ok(()) => {
                        obligations.push(PolyProofObligation {
                            fact: format!("Cut: {} unifies with {}", gb_s, ha_s),
                            source,
                            discharged: true,
                        });
                    }
                    Err(e) => {
                        obligations.push(PolyProofObligation {
                            fact: format!("Cut: {}", e),
                            source,
                            discharged: false,
                        });
                    }
                }
                Ok((ga, hb))
            }

            PolyGraph::First(g) => {
                let (ga, gb) = self.infer_obligations(g, sig, subst, obligations)?;
                let d = self.fresh_var();
                Ok((
                    Ty::Prod(Box::new(ga), Box::new(d.clone())),
                    Ty::Prod(Box::new(gb), Box::new(d)),
                ))
            }

            PolyGraph::Left(g) => {
                let (ga, gb) = self.infer_obligations(g, sig, subst, obligations)?;
                let d = self.fresh_var();
                Ok((
                    Ty::Sum(Box::new(ga), Box::new(d.clone())),
                    Ty::Sum(Box::new(gb), Box::new(d)),
                ))
            }

            PolyGraph::Loop(g) => {
                let (ga, gb) = self.infer_obligations(g, sig, subst, obligations)?;
                let a = self.fresh_var();
                let b = self.fresh_var();
                let c = self.fresh_var();
                let source = format!("loop({})", g);
                let ga_s = subst.apply(&ga);
                let gb_s = subst.apply(&gb);
                let in_ok = self.unify(&ga, &Ty::Prod(Box::new(a.clone()), Box::new(c.clone())), subst).is_ok();
                let out_ok = self.unify(&gb, &Ty::Prod(Box::new(b.clone()), Box::new(c)), subst).is_ok();
                if in_ok && out_ok {
                    obligations.push(PolyProofObligation {
                        fact: format!("Feedback: {} unifies to (A×C), {} unifies to (B×C) with shared C", ga_s, gb_s),
                        source,
                        discharged: true,
                    });
                } else {
                    obligations.push(PolyProofObligation {
                        fact: format!("Feedback channel does not unify: input {} / output {}", ga_s, gb_s),
                        source,
                        discharged: false,
                    });
                }
                Ok((a, b))
            }

            PolyGraph::Arr(name) => {
                let entry = sig
                    .iter()
                    .find(|e| e.name == *name)
                    .ok_or_else(|| format!("Unknown base arrow: {}", name))?;
                if !sig.iter().any(|e| e.name == *name) {
                    obligations.push(PolyProofObligation {
                        fact: format!("Base arrow '{}' exists in signature", name),
                        source: format!("arr({})", name),
                        discharged: false,
                    });
                }
                let (i, o) = self.instantiate(entry);
                Ok((i, o))
            }
        }
    }
}

// ============================================================================
// 8. Standard Polymorphic Signature
// ============================================================================

fn tv(s: &str) -> Ty {
    Ty::Var(s.to_string())
}
fn atom(s: &str) -> Ty {
    Ty::Atom(s.to_string())
}
fn int() -> Ty {
    atom("Int")
}
fn bool() -> Ty {
    atom("Bool")
}
fn prod(a: Ty, b: Ty) -> Ty {
    Ty::Prod(Box::new(a), Box::new(b))
}
fn arr_t(a: Ty, b: Ty) -> Ty {
    Ty::Arrow(Box::new(a), Box::new(b))
}
fn list(a: Ty) -> Ty {
    Ty::List(Box::new(a))
}

/// The polymorphic signature: id, map (curried), map_pair (uncurried),
/// filter, length, int_succ, int_eq, bool_not, …
fn poly_sig() -> Vec<PolySigEntry> {
    vec![
        // id : α ⇝ α
        PolySigEntry {
            name: "id",
            input: tv("a"),
            output: tv("a"),
        },
        // map (curried): (α ⇝ β) ⇝ ([α] ⇝ [β])
        // This is the higher-order form that makes comp(map, map) work.
        PolySigEntry {
            name: "map",
            input: arr_t(tv("a"), tv("b")),
            output: arr_t(list(tv("a")), list(tv("b"))),
        },
        // map_pair (uncurried): (α ⇝ β) × [α] ⇝ [β]
        // Matches the task's stated signature for `map`.
        PolySigEntry {
            name: "map_pair",
            input: prod(arr_t(tv("a"), tv("b")), list(tv("a"))),
            output: list(tv("b")),
        },
        // filter : (α ⇝ Bool) × [α] ⇝ [α]
        PolySigEntry {
            name: "filter",
            input: prod(arr_t(tv("a"), bool()), list(tv("a"))),
            output: list(tv("a")),
        },
        // length : [α] ⇝ Int   (polymorphic in the element type)
        PolySigEntry {
            name: "length",
            input: list(tv("a")),
            output: int(),
        },
        // head : [α] ⇝ α
        PolySigEntry {
            name: "head",
            input: list(tv("a")),
            output: tv("a"),
        },
        // int_succ : Int ⇝ Int
        PolySigEntry {
            name: "int_succ",
            input: int(),
            output: int(),
        },
        // int_eq : Int × Int ⇝ Bool
        PolySigEntry {
            name: "int_eq",
            input: prod(int(), int()),
            output: bool(),
        },
        // bool_not : Bool ⇝ Bool
        PolySigEntry {
            name: "bool_not",
            input: bool(),
            output: bool(),
        },
        // dup : α ⇝ α × α   (useful for fanout)
        PolySigEntry {
            name: "dup",
            input: tv("a"),
            output: prod(tv("a"), tv("a")),
        },
        // swap : α × β ⇝ β × α
        PolySigEntry {
            name: "swap",
            input: prod(tv("a"), tv("b")),
            output: prod(tv("b"), tv("a")),
        },
        // assoc : (α × β) × γ ⇝ α × (β × γ)
        PolySigEntry {
            name: "assoc",
            input: prod(prod(tv("a"), tv("b")), tv("c")),
            output: prod(tv("a"), prod(tv("b"), tv("c"))),
        },
    ]
}

// ============================================================================
// 9. Test Suite
// ============================================================================

// --- Test 1: Polymorphic identity (constructor) ---
fn test_polymorphic_identity_constructor() {
    println!("\n=== Test 1: Polymorphic Identity (constructor) ===");
    let sig = poly_sig();
    let g = PolyGraph::Id;

    let (a, b) = infer_type_poly(&g, &sig).expect("id should typecheck");
    println!("  Graph: {}", g);
    println!("  Inferred principal type: {} ⇝ {}", a, b);
    // Should be α ⇝ α (a single variable, input = output)
    assert_eq!(a, b, "identity input and output must be the same variable");
    assert!(matches!(a, Ty::Var(_)), "identity should be polymorphic");
    println!("  ✓ Polymorphic identity inferred: {} ⇝ {}", a, b);
}

// --- Test 2: Polymorphic identity (signature arrow `id`) ---
fn test_polymorphic_identity_sig() {
    println!("\n=== Test 2: Polymorphic Identity (signature `id : α ⇝ α`) ===");
    let sig = poly_sig();
    let g = PolyGraph::Arr("id");

    let (a, b) = infer_type_poly(&g, &sig).expect("id should typecheck");
    println!("  Graph: {}", g);
    println!("  Inferred principal type: {} ⇝ {}", a, b);
    assert_eq!(a, b, "id input and output must be the same variable");
    assert!(matches!(a, Ty::Var(_)), "id should be polymorphic");
    println!("  ✓ Signature id : α ⇝ α inferred without annotations");
}

// --- Test 3: Polymorphic map (curried) ---
fn test_polymorphic_map_curried() {
    println!("\n=== Test 3: Polymorphic map (curried) ===");
    let sig = poly_sig();
    let g = PolyGraph::Arr("map");

    let (a, b) = infer_type_poly(&g, &sig).expect("map should typecheck");
    println!("  Graph: {}", g);
    println!("  Inferred principal type: {} ⇝ {}", a, b);
    // map : (α ⇝ β) ⇝ ([α] ⇝ [β])
    assert_eq!(
        a,
        arr_t(tv("α"), tv("β")),
        "map input should be (α ⇝ β)"
    );
    assert_eq!(
        b,
        arr_t(list(tv("α")), list(tv("β"))),
        "map output should be ([α] ⇝ [β])"
    );
    println!("  ✓ map : (α ⇝ β) ⇝ ([α] ⇝ [β]) inferred");
}

// --- Test 4: Polymorphic map (uncurried, product form) ---
fn test_polymorphic_map_pair() {
    println!("\n=== Test 4: Polymorphic map (uncurried, product form) ===");
    let sig = poly_sig();
    let g = PolyGraph::Arr("map_pair");

    let (a, b) = infer_type_poly(&g, &sig).expect("map_pair should typecheck");
    println!("  Graph: {}", g);
    println!("  Inferred principal type: {} ⇝ {}", a, b);
    // map_pair : (α ⇝ β) × [α] ⇝ [β]
    assert_eq!(a, prod(arr_t(tv("α"), tv("β")), list(tv("α"))));
    assert_eq!(b, list(tv("β")));
    println!("  ✓ map_pair : (α ⇝ β) × [α] ⇝ [β] inferred");
}

// --- Test 5: Polymorphic filter ---
fn test_polymorphic_filter() {
    println!("\n=== Test 5: Polymorphic filter ===");
    let sig = poly_sig();
    let g = PolyGraph::Arr("filter");

    let (a, b) = infer_type_poly(&g, &sig).expect("filter should typecheck");
    println!("  Graph: {}", g);
    println!("  Inferred principal type: {} ⇝ {}", a, b);
    // filter : (α ⇝ Bool) × [α] ⇝ [α]
    assert_eq!(a, prod(arr_t(tv("α"), bool()), list(tv("α"))));
    assert_eq!(b, list(tv("α")));
    println!("  ✓ filter : (α ⇝ Bool) × [α] ⇝ [α] inferred");
    println!("    (element type preserved — inferred, not annotated)");
}

// --- Test 6: Specialization — comp(id, int_succ) should specialize α = Int ---
fn test_specialization_id_succ() {
    println!("\n=== Test 6: Specialization (comp(id, int_succ) ⟹ α = Int) ===");
    let sig = poly_sig();
    // id : α ⇝ α ; int_succ : Int ⇝ Int  ⟹  Int ⇝ Int
    let g = PolyGraph::Comp(
        Box::new(PolyGraph::Arr("id")),
        Box::new(PolyGraph::Arr("int_succ")),
    );

    let (a, b) = infer_type_poly(&g, &sig).expect("comp(id, int_succ) should typecheck");
    println!("  Graph: {}", g);
    println!("  Inferred type: {} ⇝ {}", a, b);
    // The polymorphic α of id is specialized to Int by unifying with int_succ.
    assert_eq!(a, int(), "input should specialize to Int");
    assert_eq!(b, int(), "output should be Int");
    println!("  ✓ id's α specialized to Int via unification");
}

// --- Test 7: Polymorphic composition — comp(map, map) ---
fn test_polymorphic_composition_map_map() {
    println!("\n=== Test 7: Polymorphic composition (comp(map, map)) ===");
    let sig = poly_sig();
    // map : (α⇝β) ⇝ ([α]⇝[β])
    // comp(map, map): output of first ([α]⇝[β]) unifies with input of second (γ⇝δ)
    //   ⟹ γ = [α], δ = [β]
    //   ⟹ comp(map, map) : (α ⇝ β) ⇝ ([[α]] ⇝ [[β]])   (map over lists of lists)
    let g = PolyGraph::Comp(
        Box::new(PolyGraph::Arr("map")),
        Box::new(PolyGraph::Arr("map")),
    );

    let (a, b) =
        infer_type_poly(&g, &sig).expect("comp(map, map) should typecheck");
    println!("  Graph: {}", g);
    println!("  Inferred principal type: {} ⇝ {}", a, b);
    // Expected: (α ⇝ β) ⇝ ([[α]] ⇝ [[β]])
    assert_eq!(a, arr_t(tv("α"), tv("β")));
    assert_eq!(b, arr_t(list(list(tv("α"))), list(list(tv("β")))));
    println!("  ✓ comp(map, map) : (α ⇝ β) ⇝ ([[α]] ⇝ [[β]]) — the map-map");
}

// --- Test 8: The KEY demonstration — comp(first(id), id) ⟹ (α × β) ⇝ (α × β) ---
fn test_key_demonstration_first_id_comp_id() {
    println!("\n=== Test 8: KEY — comp(first(id), id) ⟹ (α × β) ⇝ (α × β) ===");
    let sig = poly_sig();
    // first(id) : α × D ⇝ α × D   (D fresh)
    // id        : γ ⇝ γ
    // comp: unify (α × D) with γ  ⟹  γ = α × D
    // result: (α × D) ⇝ (α × D)  =  (α × β) ⇝ (α × β)
    let g = PolyGraph::Comp(
        Box::new(PolyGraph::First(Box::new(PolyGraph::Id))),
        Box::new(PolyGraph::Id),
    );

    let (a, b) = infer_type_poly(&g, &sig).expect("key graph should typecheck");
    println!("  Graph: {}", g);
    println!("  Inferred principal type: {} ⇝ {}", a, b);
    assert_eq!(a, b, "input and output must match");
    assert_eq!(a, prod(tv("α"), tv("β")), "should be (α × β)");
    println!("  ✓ comp(first(id), id) : (α × β) ⇝ (α × β) — NO annotations!");
    println!("    This is the real power of annotation-free inference.");
}

// --- Test 9: Polymorphic loop with a polymorphic body ---
fn test_polymorphic_loop() {
    println!("\n=== Test 9: Polymorphic loop (polymorphic body) ===");
    let sig = poly_sig();
    // loop(first(id)) : loop of (α×C ⇝ α×C)  ⟹  α ⇝ α
    // first(id) : A×D ⇝ A×D (polymorphic). loop unifies input with A×C,
    // output with B×C, sharing C. With first(id): input = a×d, output = a×d.
    // Unify a×d with A×C and a×d with B×C  ⟹  A = a, B = a, C = d.
    // Result: A ⇝ B = a ⇝ a (polymorphic identity via feedback).
    let g = PolyGraph::Loop(Box::new(PolyGraph::First(Box::new(PolyGraph::Id))));

    let (a, b) = infer_type_poly(&g, &sig).expect("polymorphic loop should typecheck");
    println!("  Graph: {}", g);
    println!("  Inferred principal type: {} ⇝ {}", a, b);
    assert_eq!(a, b, "loop of first(id) should be polymorphic identity");
    assert!(matches!(a, Ty::Var(_)), "should be a single type variable");
    println!("  ✓ loop(first(id)) : α ⇝ α — polymorphic identity via feedback");
}

// --- Test 10: Ill-typed polymorphic graph (unification failure) ---
fn test_ill_typed_polymorphic() {
    println!("\n=== Test 10: Ill-typed polymorphic graph (unification failure) ===");
    let sig = poly_sig();
    // comp(int_succ, length): int_succ : Int ⇝ Int, length : [α] ⇝ Int
    // Middle type Int must unify with [α]  ⟹  FAIL (Int ≠ [α]).
    let g = PolyGraph::Comp(
        Box::new(PolyGraph::Arr("int_succ")),
        Box::new(PolyGraph::Arr("length")),
    );

    let result = infer_type_poly(&g, &sig);
    assert!(result.is_err(), "ill-typed graph should fail");
    let err = result.unwrap_err();
    println!("  Graph: {}", g);
    println!("  Error (expected): {}", err);

    let obligations = proof_obligations_poly(&g, &sig);
    let undischarged: Vec<_> = obligations.iter().filter(|o| !o.discharged).collect();
    assert!(
        !undischarged.is_empty(),
        "ill-typed graph should have undischarged obligations"
    );
    println!("  Proof obligations: {}", obligations.len());
    for ob in &obligations {
        let mark = if ob.discharged { "✓" } else { "✗" };
        println!("    {} [{}] {} (from: {})", mark, if ob.discharged { "discharged" } else { "OPEN" }, ob.fact, ob.source);
    }
    println!("  ✓ Ill-typed polymorphic graph correctly rejected by unification");
}

// --- Test 11: Let-polymorphism — two independent uses of id keep distinct types ---
fn test_let_polymorphism() {
    println!("\n=== Test 11: Let-polymorphism (independent uses of id stay distinct) ===");
    let sig = poly_sig();
    // comp(first(id), first(id)):
    //   first(id) : α × D ⇝ α × D
    //   first(id) : β × E ⇝ β × E   (FRESH instantiation — independent α)
    // comp: unify (α × D) with (β × E)  ⟹  α = β, D = E
    // result: (α × D) ⇝ (α × D)  =  (α × β) ⇝ (α × β)
    //
    // The key point: each `id` is instantiated with FRESH variables, so the
    // two uses do not over-constrain each other. This is the essence of
    // let-polymorphism: a polymorphic binding can be used at different types
    // in different positions. Here the composition forces them to agree, but
    // a parallel (&&&) construction would let them differ.
    let g = PolyGraph::Comp(
        Box::new(PolyGraph::First(Box::new(PolyGraph::Arr("id")))),
        Box::new(PolyGraph::First(Box::new(PolyGraph::Arr("id")))),
    );

    let (a, b) = infer_type_poly(&g, &sig).expect("let-poly graph should typecheck");
    println!("  Graph: {}", g);
    println!("  Inferred principal type: {} ⇝ {}", a, b);
    assert_eq!(a, b);
    assert_eq!(a, prod(tv("α"), tv("β")));
    println!("  ✓ Two independent instantiations of id unify correctly");

    // Now a parallel construction where the two id's keep DIFFERENT types:
    //   comp(id, swap) where swap : α×β ⇝ β×α composed after id : γ⇝γ
    //   unify γ with α×β  ⟹  γ = α×β
    //   result: (α×β) ⇝ (β×α)
    let g2 = PolyGraph::Comp(
        Box::new(PolyGraph::Arr("id")),
        Box::new(PolyGraph::Arr("swap")),
    );
    let (a2, b2) = infer_type_poly(&g2, &sig).expect("id ; swap should typecheck");
    println!("  Graph: {}", g2);
    println!("  Inferred principal type: {} ⇝ {}", a2, b2);
    assert_eq!(a2, prod(tv("α"), tv("β")));
    assert_eq!(b2, prod(tv("β"), tv("α")));
    println!("  ✓ id ; swap : (α × β) ⇝ (β × α) — id specialized to the pair type");
}

// --- Test 12: Specialization of map with a concrete function ---
fn test_map_specialization() {
    println!("\n=== Test 12: Specialization of map (comp(map, ...) with concrete fn) ===");
    let sig = poly_sig();
    // map applied to int_succ: comp(map, ...)? No — map is curried:
    //   map : (α⇝β) ⇝ ([α]⇝[β])
    // To specialize, feed it a concrete function. comp(map, ???) needs the
    // output ([α]⇝[β]) to feed the next stage. Instead, specialize via
    // composition with `head`:
    //   comp(map, head) is ill-typed (output is an arrow, head wants a list).
    //
    // Better: use map_pair (uncurried) and compose with length:
    //   map_pair : (α⇝β) × [α] ⇝ [β]
    //   length   : [γ] ⇝ Int
    //   comp(map_pair, length): unify [β] with [γ] ⟹ γ = β
    //   result: ((α⇝β) × [α]) ⇝ Int   (polymorphic in α, β)
    let g = PolyGraph::Comp(
        Box::new(PolyGraph::Arr("map_pair")),
        Box::new(PolyGraph::Arr("length")),
    );
    let (a, b) = infer_type_poly(&g, &sig).expect("map_pair ; length should typecheck");
    println!("  Graph: {}", g);
    println!("  Inferred principal type: {} ⇝ {}", a, b);
    assert_eq!(a, prod(arr_t(tv("α"), tv("β")), list(tv("α"))));
    assert_eq!(b, int());
    println!("  ✓ comp(map_pair, length) : ((α⇝β) × [α]) ⇝ Int — polymorphic");
}

// --- Test 13: Proof obligations discharged on a well-typed polymorphic graph ---
fn test_proof_obligations_discharged() {
    println!("\n=== Test 13: Proof obligations (discharged on well-typed graph) ===");
    let sig = poly_sig();
    let g = PolyGraph::Comp(
        Box::new(PolyGraph::First(Box::new(PolyGraph::Arr("id")))),
        Box::new(PolyGraph::Arr("swap")),
    );
    // first(id) : α×D ⇝ α×D ; swap : β×γ ⇝ γ×β
    // unify (α×D) with (β×γ) ⟹ β=α, γ=D
    // result: (α×D) ⇝ (D×α)  =  (α×β) ⇝ (β×α)
    let (a, b) = infer_type_poly(&g, &sig).expect("graph should typecheck");
    println!("  Graph: {}", g);
    println!("  Inferred principal type: {} ⇝ {}", a, b);
    assert_eq!(a, prod(tv("α"), tv("β")));
    assert_eq!(b, prod(tv("β"), tv("α")));

    let obligations = proof_obligations_poly(&g, &sig);
    println!("  Proof obligations: {}", obligations.len());
    for ob in &obligations {
        let mark = if ob.discharged { "✓" } else { "✗" };
        println!("    {} [{}] {} (from: {})", mark, if ob.discharged { "discharged" } else { "OPEN" }, ob.fact, ob.source);
    }
    let all_discharged = obligations.iter().all(|o| o.discharged);
    assert!(all_discharged, "well-typed graph should discharge all obligations");
    println!("  ✓ All proof obligations discharged (unification succeeded)");
}

// --- Test 14: Occurs check prevents infinite types ---
fn test_occurs_check() {
    println!("\n=== Test 14: Occurs check (rejects infinite types) ===");
    // Directly test the unifier: α vs (α ⇝ α) should fail the occurs check.
    let a = tv("a");
    let infinite = arr_t(tv("a"), tv("a"));
    assert!(
        Unifier::unify(&a, &infinite).is_none(),
        "occurs check should reject α = (α ⇝ α)"
    );
    println!("  unify(α, α ⇝ α) = None  (occurs check prevents infinite type)");
    // And a non-recursive case should succeed.
    let b = tv("b");
    assert!(Unifier::unify(&a, &b).is_some(), "α = β should unify");
    println!("  unify(α, β) = Some(...)  (distinct vars unify)");
    println!("  ✓ Occurs check works");
}

// ============================================================================
// 10. Main
// ============================================================================

fn main() {
    println!("╔══════════════════════════════════════════════════════════════╗");
    println!("║  Phase 4 (Polymorphic): Annotation-Free Inference over      ║");
    println!("║  Arrow Graphs — Hindley-Milner Unification                  ║");
    println!("╚══════════════════════════════════════════════════════════════╝");
    println!("\nWith a polymorphic signature, the graph's PRINCIPAL type is");
    println!("recovered purely from structure + unification — NO annotations.\n");

    test_polymorphic_identity_constructor();
    test_polymorphic_identity_sig();
    test_polymorphic_map_curried();
    test_polymorphic_map_pair();
    test_polymorphic_filter();
    test_specialization_id_succ();
    test_polymorphic_composition_map_map();
    test_key_demonstration_first_id_comp_id();
    test_polymorphic_loop();
    test_ill_typed_polymorphic();
    test_let_polymorphism();
    test_map_specialization();
    test_proof_obligations_discharged();
    test_occurs_check();

    println!("\n═══════════════════════════════════════════════════════════════");
    println!("  All tests passed.");
    println!("═══════════════════════════════════════════════════════════════");
    println!("\nSummary:");
    println!("  • Polymorphic types: Ty::Var + Ty::Arrow for higher-order base arrows.");
    println!("  • HM unification over graphs: fresh vars per base-arrow use, unified");
    println!("    across composition boundaries (cut rule = unification, not matching).");
    println!("  • Principal type inference: most general type inferred + generalized");
    println!("    to α, β, γ, …");
    println!("  • Generalized proof obligations: 'middle type UNIFIES' (discharged");
    println!("    when unification succeeds).");
    println!("  • Let-polymorphism: each use of a polymorphic arrow is freshly");
    println!("    instantiated, so independent uses keep distinct types.");
    println!("  • Occurs check prevents infinite types.");
    println!("\nThe headline: comp(first(id), id) : (α × β) ⇝ (α × β), with NO");
    println!("annotations — purely from structure + unification. This is the real");
    println!("power of annotation-free inference over λ-free arrow graphs.");
}

// ============================================================================
// 11. Unit tests (run with `cargo test --bin poly_proof_graph`)
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unit_unify_var_atom() {
        let s = Unifier::unify(&tv("a"), &int()).unwrap();
        assert_eq!(s.apply(&tv("a")), int());
    }

    #[test]
    fn unit_unify_prod() {
        let t1 = prod(tv("a"), tv("b"));
        let t2 = prod(int(), bool());
        let s = Unifier::unify(&t1, &t2).unwrap();
        assert_eq!(s.apply(&tv("a")), int());
        assert_eq!(s.apply(&tv("b")), bool());
    }

    #[test]
    fn unit_unify_arrow() {
        let t1 = arr_t(tv("a"), list(tv("a")));
        let t2 = arr_t(int(), list(int()));
        let s = Unifier::unify(&t1, &t2).unwrap();
        assert_eq!(s.apply(&tv("a")), int());
    }

    #[test]
    fn unit_unify_head_mismatch() {
        assert!(Unifier::unify(&int(), &bool()).is_none());
        assert!(Unifier::unify(&int(), &list(int())).is_none());
    }

    #[test]
    fn unit_occurs_check() {
        let a = tv("a");
        let rec = arr_t(tv("a"), tv("a"));
        assert!(Unifier::unify(&a, &rec).is_none());
    }

    #[test]
    fn unit_generalize_renames_in_order() {
        // t0 appears first, t1 second
        let ty = prod(tv("t0"), prod(tv("t1"), tv("t0")));
        let g = generalize(&ty);
        assert_eq!(g, prod(tv("α"), prod(tv("β"), tv("α"))));
    }

    #[test]
    fn unit_infer_id_polymorphic() {
        let sig = poly_sig();
        let (a, b) = infer_type_poly(&PolyGraph::Id, &sig).unwrap();
        assert_eq!(a, b);
        assert!(matches!(a, Ty::Var(_)));
    }

    #[test]
    fn unit_infer_comp_id_int_succ_specializes() {
        let sig = poly_sig();
        let g = PolyGraph::Comp(
            Box::new(PolyGraph::Arr("id")),
            Box::new(PolyGraph::Arr("int_succ")),
        );
        let (a, b) = infer_type_poly(&g, &sig).unwrap();
        assert_eq!(a, int());
        assert_eq!(b, int());
    }

    #[test]
    fn unit_infer_comp_map_map_principal() {
        let sig = poly_sig();
        let g = PolyGraph::Comp(
            Box::new(PolyGraph::Arr("map")),
            Box::new(PolyGraph::Arr("map")),
        );
        let (a, b) = infer_type_poly(&g, &sig).unwrap();
        assert_eq!(a, arr_t(tv("α"), tv("β")));
        assert_eq!(b, arr_t(list(list(tv("α"))), list(list(tv("β")))));
    }

    #[test]
    fn unit_key_demonstration() {
        let sig = poly_sig();
        let g = PolyGraph::Comp(
            Box::new(PolyGraph::First(Box::new(PolyGraph::Id))),
            Box::new(PolyGraph::Id),
        );
        let (a, b) = infer_type_poly(&g, &sig).unwrap();
        assert_eq!(a, prod(tv("α"), tv("β")));
        assert_eq!(b, prod(tv("α"), tv("β")));
    }

    #[test]
    fn unit_ill_typed_rejected() {
        let sig = poly_sig();
        let g = PolyGraph::Comp(
            Box::new(PolyGraph::Arr("int_succ")),
            Box::new(PolyGraph::Arr("length")),
        );
        assert!(infer_type_poly(&g, &sig).is_err());
    }

    #[test]
    fn unit_loop_polymorphic() {
        let sig = poly_sig();
        let g = PolyGraph::Loop(Box::new(PolyGraph::First(Box::new(PolyGraph::Id))));
        let (a, b) = infer_type_poly(&g, &sig).unwrap();
        assert_eq!(a, b);
        assert!(matches!(a, Ty::Var(_)));
    }

    #[test]
    fn unit_proof_obligations_discharged() {
        let sig = poly_sig();
        let g = PolyGraph::Comp(
            Box::new(PolyGraph::First(Box::new(PolyGraph::Arr("id")))),
            Box::new(PolyGraph::Arr("swap")),
        );
        let obs = proof_obligations_poly(&g, &sig);
        assert!(!obs.is_empty());
        assert!(obs.iter().all(|o| o.discharged));
    }
}
