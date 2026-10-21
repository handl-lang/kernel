// ADR-0075 (Traits as Arrow Signatures) -- Rust-side prototype.
//
// Implements the open trait catalog, the 3-step matching pipeline
// (type filter -> structural fingerprint -> CutElim normalization), an
// abstract storage trait with an in-memory backend, and a CutElim
// normalizer mirroring the six rewrite rules from
// `lean/ArrowMinimalityLib/ProofAdvantage.lean`.
//
// Self-contained: pure std, no external dependencies. Each `*_tests.rs`
// in this workspace is its own bin/crate target, so the graph/type model
// is copied here (clearly marked) rather than imported across bins.
//
// ADR: platform/project/adrs/0075-traits-as-arrow-signatures.md
//
// HONESTY NOTE (read me): only the *functor* laws (first/left identity
// and fusion) are CutElim-proven in this prototype -- they ARE the six
// CutElim rewrites. The Sorting/Mapping/Filtering laws are *semantic
// placeholders* (Sorted, LengthEq, AllSatisfy) that are NOT expressible
// as graph equations over the 5-combinator kernel and are therefore
// marked `cutelim_proven: false`. This matches the ADR's explicit
// position that non-functor law verification is aspirational (ADR
// "What is NOT yet proven"; Open Question #2).

use std::collections::HashMap;
use std::fmt;

// ============================================================================
// 1. Polymorphic Types  (Mirrors src/poly_proof_graph_tests.rs lines 40-111)
// ============================================================================

// Mirrors src/poly_proof_graph_tests.rs (Ty enum).
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum Ty {
    Atom(String),               // base type (Int, Bool, String, ...)
    Var(String),                // type variable (alpha, beta, t0, ...)
    Prod(Box<Ty>, Box<Ty>),     // A x B   (read: A & B in proof mode)
    Sum(Box<Ty>, Box<Ty>),      // A + B   (read: A | B in proof mode)
    Arrow(Box<Ty>, Box<Ty>),    // A ~> B  (arrow type as a first-class type,
                                //         needed for higher-order base arrows)
    Unit,                       // top
    Void,                       // bottom
    List(Box<Ty>),              // [A]
    // ADR-0075 section 5 type application: F<A>. `F` is a type-constructor
    // variable (a `Ty::Var`) and `A` is the argument. This is the
    // higher-kinded constructor that lets `Functor`'s `type_shape` be the
    // generic `F<A> ~> F<B>` instead of the `List` instance `[A] ~> [B]`
    // (ADR Open Question #5). NOTE: this adds the constructor and the
    // unification to make the type filter discriminate HKT shapes; it does
    // NOT add higher-kinded trait *parameters* to the surface syntax
    // (still no `trait Functor<F>` declaration form) -- that remains open.
    App(Box<Ty>, Box<Ty>),      // F<A>  (ADR-0075 section 5)
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ty::Atom(s) => write!(f, "{}", s),
            Ty::Var(s) => write!(f, "{}", s),
            Ty::Prod(a, b) => write!(f, "({} x {})", a, b),
            Ty::Sum(a, b) => write!(f, "({} + {})", a, b),
            Ty::Arrow(a, b) => write!(f, "({} ~> {})", a, b),
            Ty::Unit => write!(f, "()"),
            Ty::Void => write!(f, "_|_"),
            Ty::List(t) => write!(f, "[{}]", t),
            // ADR-0075 section 5: angle brackets, not square brackets.
            Ty::App(g, a) => write!(f, "{}<{}>", g, a),
        }
    }
}

impl Ty {
    // Mirrors src/poly_proof_graph_tests.rs (free_vars).
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
                Ty::App(g, a) => {
                    go(g, out);
                    go(a, out);
                }
                _ => {}
            }
        }
        let mut out = Vec::new();
        go(self, &mut out);
        out
    }

    // Mirrors src/poly_proof_graph_tests.rs (apply_map).
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
            Ty::App(g, a) => Ty::App(
                Box::new(g.apply_map(map)),
                Box::new(a.apply_map(map)),
            ),
            other => other.clone(),
        }
    }
}

// ----------------------------------------------------------------------------
// Small type-construction helpers (local convenience, not mirrored).
// ----------------------------------------------------------------------------

fn tv(s: &str) -> Ty {
    Ty::Var(s.to_string())
}
fn atom(s: &str) -> Ty {
    Ty::Atom(s.to_string())
}
fn prod(a: Ty, b: Ty) -> Ty {
    Ty::Prod(Box::new(a), Box::new(b))
}
fn sum(a: Ty, b: Ty) -> Ty {
    Ty::Sum(Box::new(a), Box::new(b))
}
fn arr_t(a: Ty, b: Ty) -> Ty {
    Ty::Arrow(Box::new(a), Box::new(b))
}
fn list(a: Ty) -> Ty {
    Ty::List(Box::new(a))
}
// ADR-0075 section 5 type application: F<A>.
fn app_t(g: Ty, a: Ty) -> Ty {
    Ty::App(Box::new(g), Box::new(a))
}
fn bool_t() -> Ty {
    atom("Bool")
}

// ============================================================================
// 2. Substitution  (Mirrors src/poly_proof_graph_tests.rs lines 117-169)
// ============================================================================

// Mirrors src/poly_proof_graph_tests.rs (Substitution).
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
            Ty::App(g, a) => Ty::App(
                Box::new(self.apply(g)),
                Box::new(self.apply(a)),
            ),
            other => other.clone(),
        }
    }
}

// ============================================================================
// 3. Unification (HM)  (Mirrors src/poly_proof_graph_tests.rs lines 175-251)
// ============================================================================

// Mirrors src/poly_proof_graph_tests.rs (Unifier).
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

    fn unify_with_subst(ty1: &Ty, ty2: &Ty, subst: &mut Substitution) -> bool {
        let ty1 = subst.apply(ty1);
        let ty2 = subst.apply(ty2);

        match (&ty1, &ty2) {
            (Ty::Atom(a), Ty::Atom(b)) => a == b,
            (Ty::Unit, Ty::Unit) => true,
            (Ty::Void, Ty::Void) => true,

            (Ty::Var(a), Ty::Var(b)) if a == b => true,
            (Ty::Var(a), b) => {
                if Unifier::occurs_in(a, b) {
                    false
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

            // ADR-0075 section 5 / Open Question #5: higher-kinded type
            // application. `App(F, A)` unifies structurally with another
            // `App(G, B)` by unifying the constructors and the arguments.
            (Ty::App(f1, a1), Ty::App(f2, a2)) => {
                Unifier::unify_with_subst(f1, f2, subst)
                    && Unifier::unify_with_subst(a1, a2, subst)
            }
            // Bridge `List(t)` to `App(Atom("List"), t)`. The `Ty` enum
            // bakes the unary `List` constructor in as a dedicated variant,
            // so for an HKT shape `F<A>` to unify with a concrete `[X]`
            // (i.e. `List(X)`) -- binding `F := List, A := X` -- we treat
            // `List(t)` as isomorphic to `App(Atom("List"), t)` here. This
            // is what lets `Functor`'s `F<A> ~> F<B>` match the demo `map`
            // graph's inferred type `[a] ~> [b]`. A bare `Atom` (e.g.
            // `Int`) is NOT bridged, so `Int` does not unify with `F<A>`
            // and a non-functor arrow `Int ~> Bool` is correctly pruned.
            (Ty::App(f1, a1), Ty::List(t2)) => {
                Unifier::unify_with_subst(f1, &atom("List"), subst)
                    && Unifier::unify_with_subst(a1, t2, subst)
            }
            (Ty::List(t1), Ty::App(f2, a2)) => {
                Unifier::unify_with_subst(&atom("List"), f2, subst)
                    && Unifier::unify_with_subst(t1, a2, subst)
            }

            _ => false,
        }
    }

    fn occurs_in(var: &str, ty: &Ty) -> bool {
        match ty {
            Ty::Var(v) => v == var,
            Ty::Prod(a, b) | Ty::Sum(a, b) | Ty::Arrow(a, b) => {
                Unifier::occurs_in(var, a) || Unifier::occurs_in(var, b)
            }
            Ty::List(t) => Unifier::occurs_in(var, t),
            Ty::App(g, a) => Unifier::occurs_in(var, g) || Unifier::occurs_in(var, a),
            _ => false,
        }
    }
}

// ============================================================================
// 4. Arrow Graphs  (Mirrors src/poly_proof_graph_tests.rs lines 257-300)
//    Extended with `Choice` (binary sum functoriality) and `App` (placeholder
//    for ArrowApply), per the ADR-0075 task.
// ============================================================================

// Mirrors src/poly_proof_graph_tests.rs (PolySigEntry).
#[derive(Debug, Clone)]
pub struct PolySigEntry {
    pub name: &'static str,
    pub input: Ty,
    pub output: Ty,
}

// Mirrors src/poly_proof_graph_tests.rs (PolyGraph), extended.
//
// Extensions over the mirrored original:
//   * `Choice(G, H)` -- binary sum functoriality:  A+B ~> C+D  from  A~>C, B~>D.
//     (The original has only the unary `Left`/`left` functoriality A~>B => A+D~>B+D.)
//   * `App(G)`       -- placeholder for ArrowApply (ADR-0052 kernel `app`).
//     Inference treats it opaquely (fresh input/output vars); it is NOT wired
//     into CutElim. Present so the graph model matches the kernel alphabet
//     (arr/comp/first/left/loop/choice/app) without claiming apply semantics.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum PolyGraph {
    /// Polymorphic identity: alpha ~> alpha (alpha is fresh per use)
    Id,
    /// Composition: G ; H  (cut in proof mode)
    Comp(Box<PolyGraph>, Box<PolyGraph>),
    /// First (x-functoriality): A ~> B  ==>  A x D ~> B x D  (D is a fresh var)
    First(Box<PolyGraph>),
    /// Left (+-functoriality): A ~> B  ==>  A + D ~> B + D  (D is a fresh var)
    Left(Box<PolyGraph>),
    /// Loop (trace/fixpoint): A x C ~> B x C  ==>  A ~> B  (C is a fresh var)
    Loop(Box<PolyGraph>),
    /// Base arrow from the (polymorphic) signature. Owned `String` so the
    /// graph (and thus `CatalogEntry`) is `Serialize`/`Deserialize`-clean and
    /// survives a SQLite round-trip. `law_equal`/`normalize` compare `Arr`
    /// names by string equality, so owned vs `&'static str` is behaviorally
    /// identical.
    Arr(String),
    /// Binary sum functoriality (ADR-0075 extension): A+B ~> C+D from A~>C, B~>D.
    Choice(Box<PolyGraph>, Box<PolyGraph>),
    /// ArrowApply placeholder (ADR-0075 extension). Opaque to inference/CutElim.
    App(Box<PolyGraph>),
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
            PolyGraph::Choice(g, h) => write!(f, "choice({},{})", g, h),
            PolyGraph::App(g) => write!(f, "app({})", g),
        }
    }
}

// ----------------------------------------------------------------------------
// Graph-construction helpers (local convenience).
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
fn gloop(a: PolyGraph) -> PolyGraph {
    PolyGraph::Loop(Box::new(a))
}
fn garr(name: &'static str) -> PolyGraph {
    PolyGraph::Arr(name.to_string())
}
fn gchoice(a: PolyGraph, b: PolyGraph) -> PolyGraph {
    PolyGraph::Choice(Box::new(a), Box::new(b))
}

// ============================================================================
// 5. Polymorphic Type Inference  (Mirrors src/poly_proof_graph_tests.rs
//    lines 306-458), extended with `Choice` and `App` cases.
// ============================================================================

// Mirrors src/poly_proof_graph_tests.rs (PolyInfer).
pub struct PolyInfer {
    next_var: usize,
}

impl PolyInfer {
    pub fn new() -> Self {
        PolyInfer { next_var: 0 }
    }

    fn fresh_var(&mut self) -> Ty {
        let name = format!("t{}", self.next_var);
        self.next_var += 1;
        Ty::Var(name)
    }

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

    /// Core inference: walk the graph, generating fresh variables and
    /// unifying across composition boundaries. Returns (input, output)
    /// with the running substitution applied by the caller.
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
                self.unify(&gb, &ha, subst).map_err(|e| {
                    format!("Composition mismatch in ({} ; {}): {}", g, h, e)
                })?;
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
                // G : A x C ~> B x C  ==>  loop G : A ~> B
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
                    .find(|e| e.name == name.as_str())
                    .ok_or_else(|| format!("Unknown base arrow: {}", name))?;
                let (i, o) = self.instantiate(entry);
                Ok((i, o))
            }

            // ADR-0075 extension: binary sum functoriality.
            //   G1 : A1 ~> B1,  G2 : A2 ~> B2  ==>  choice(G1,G2) : A1+A2 ~> B1+B2
            PolyGraph::Choice(g1, g2) => {
                let (a1, b1) = self.infer(g1, sig, subst)?;
                let (a2, b2) = self.infer(g2, sig, subst)?;
                Ok((Ty::Sum(Box::new(a1), Box::new(a2)), Ty::Sum(Box::new(b1), Box::new(b2))))
            }

            // ADR-0075 extension: ArrowApply placeholder. Opaque: fresh vars.
            // The inner graph is inferred only to validate it; its type is not
            // connected to the apply result (full ArrowApply wiring is future work).
            PolyGraph::App(g) => {
                let _ = self.infer(g, sig, subst)?;
                let a = self.fresh_var();
                let b = self.fresh_var();
                Ok((a, b))
            }
        }
    }
}

/// Top-level annotation-free inference: infer the PRINCIPAL type, then
/// generalize (rename free variables to alpha, beta, gamma, ...).
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

// ----------------------------------------------------------------------------
// Generalization  (Mirrors src/poly_proof_graph_tests.rs lines 464-503)
// ----------------------------------------------------------------------------

const GREEK: &[&str] = &["a", "b", "g", "d", "e", "z", "h", "th", "i", "k"];

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
            format!("t{}", idx)
        };
        map.insert(v.clone(), Ty::Var(name));
    }
    (i.apply_map(&map), o.apply_map(&map))
}

// ============================================================================
// 6. CutElim Normalizer  (mirrors lean/ArrowMinimalityLib/ProofAdvantage.lean
//    lines 95-134: ceIdLeft, ceIdRight, ceFirstFusion, ceLeftFusion,
//    ceFirstId, ceLeftId, plus reflexive-transitive closure)
// ============================================================================
//
// The six rewrites, applied as local graph-rewrite steps:
//
//   ceIdLeft      : comp(id, G)        ==> G
//   ceIdRight     : comp(G, id)        ==> G
//   ceFirstFusion : comp(first G, first H) ==> first(comp G H)
//   ceLeftFusion  : comp(left  G, left  H) ==> left (comp G H)
//   ceFirstId     : first(id)          ==> id
//   ceLeftId      : left(id)           ==> id
//
// `normalize` applies these bottom-up to a fixpoint, bounded by `fuel`.
// `law_equal` checks structural equality of the normalized forms.
//
// Termination honesty (ADR "Consequences"/Open Question #2): the CutElim
// rewrite relation is NOT proven strongly normalizing for all graphs. The
// six rewrites here are size-non-increasing and in practice terminate
// quickly (the proof-net advantage), but a fuel bound is used as a safety
// net. If fuel is exhausted before a fixpoint, the result is the
// partially-normalized graph (law_equal may then report false negatives).

/// Try to apply ONE rewrite at the root of `g`. Returns the rewritten graph
/// if a rule fired, else None.
fn rewrite_root(g: &PolyGraph) -> Option<PolyGraph> {
    match g {
        // ceIdLeft : comp(id, G) ==> G
        PolyGraph::Comp(a, b) if matches!(**a, PolyGraph::Id) => Some((**b).clone()),
        // ceIdRight : comp(G, id) ==> G
        PolyGraph::Comp(a, b) if matches!(**b, PolyGraph::Id) => Some((**a).clone()),
        // ceFirstFusion : comp(first G, first H) ==> first(comp G H)
        PolyGraph::Comp(a, b)
            if matches!(**a, PolyGraph::First(_)) && matches!(**b, PolyGraph::First(_)) =>
        {
            match (&**a, &**b) {
                (PolyGraph::First(g1), PolyGraph::First(g2)) => {
                    Some(PolyGraph::First(Box::new(gcomp((**g1).clone(), (**g2).clone()))))
                }
                _ => None,
            }
        }
        // ceLeftFusion : comp(left G, left H) ==> left(comp G H)
        PolyGraph::Comp(a, b)
            if matches!(**a, PolyGraph::Left(_)) && matches!(**b, PolyGraph::Left(_)) =>
        {
            match (&**a, &**b) {
                (PolyGraph::Left(g1), PolyGraph::Left(g2)) => {
                    Some(PolyGraph::Left(Box::new(gcomp((**g1).clone(), (**g2).clone()))))
                }
                _ => None,
            }
        }
        // ceFirstId : first(id) ==> id
        PolyGraph::First(inner) if matches!(**inner, PolyGraph::Id) => Some(PolyGraph::Id),
        // ceLeftId : left(id) ==> id
        PolyGraph::Left(inner) if matches!(**inner, PolyGraph::Id) => Some(PolyGraph::Id),
        _ => None,
    }
}

/// One bottom-up pass: normalize children first, then try root rewrites
/// repeatedly at the root until no root rule fires. Returns the pass result
/// and whether anything changed.
fn rewrite_pass(g: &PolyGraph) -> (PolyGraph, bool) {
    // First recurse into children (bottom-up).
    let (g_norm, child_changed) = match g {
        PolyGraph::Id | PolyGraph::Arr(_) => (g.clone(), false),
        PolyGraph::Comp(a, b) => {
            let (a2, ca) = rewrite_pass(a);
            let (b2, cb) = rewrite_pass(b);
            (PolyGraph::Comp(Box::new(a2), Box::new(b2)), ca || cb)
        }
        PolyGraph::First(a) => {
            let (a2, c) = rewrite_pass(a);
            (PolyGraph::First(Box::new(a2)), c)
        }
        PolyGraph::Left(a) => {
            let (a2, c) = rewrite_pass(a);
            (PolyGraph::Left(Box::new(a2)), c)
        }
        PolyGraph::Loop(a) => {
            let (a2, c) = rewrite_pass(a);
            (PolyGraph::Loop(Box::new(a2)), c)
        }
        PolyGraph::Choice(a, b) => {
            let (a2, ca) = rewrite_pass(a);
            let (b2, cb) = rewrite_pass(b);
            (PolyGraph::Choice(Box::new(a2), Box::new(b2)), ca || cb)
        }
        PolyGraph::App(a) => {
            let (a2, c) = rewrite_pass(a);
            (PolyGraph::App(Box::new(a2)), c)
        }
    };

    // Then try root rewrites on the (children-normalized) graph. Repeat at
    // the root until no root rule fires, so a cascade like
    //   comp(first id, first id) -> first(comp id id) -> first id -> id
    // completes within a single pass.
    let mut cur = g_norm.clone();
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

/// Normalize a graph by repeatedly applying the six CutElim rewrites
/// bottom-up until a fixpoint is reached or `fuel` passes are exhausted.
pub fn normalize(graph: &PolyGraph, fuel: usize) -> PolyGraph {
    let mut cur = graph.clone();
    for _ in 0..fuel {
        let (next, changed) = rewrite_pass(&cur);
        if !changed {
            break;
        }
        cur = next;
    }
    cur
}

/// Fuel budget for normalization. Generous for these small graphs; the
/// bound exists only as a termination safety net (see honesty note above).
const NORMALIZE_FUEL: usize = 1024;

/// Two graphs are `law_equal` iff they normalize to the same form under
/// CutElim. `Arr` names are compared structurally (the name is opaque data
/// -- we do not interpret it, but two `Arr`s are equal only if their names
/// match). This is what lets the composition law `first(f;g) === first f; first g`
/// verify: both sides normalize to `first(f ; g)` with matching `f`, `g`.
pub fn law_equal(g1: &PolyGraph, g2: &PolyGraph) -> bool {
    normalize(g1, NORMALIZE_FUEL) == normalize(g2, NORMALIZE_FUEL)
}

// ============================================================================
// 7. Catalog Types  (ADR-0075 section 3: open trait catalog)
// ============================================================================

/// An equational law: two graphs that must normalize to the same form
/// under CutElim. (ADR section 3 `laws`.)
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct LawEquation {
    pub name: String,
    pub lhs: PolyGraph,
    pub rhs: PolyGraph,
}

/// A catalog entry: a named law pattern. (ADR section 3 `entry`.)
///
/// `cutelim_proven` is the ADR's flag for whether CutElim normalization is
/// proven for this pattern. For the functor entries it is `true` (the laws
/// ARE the CutElim rewrites). For Sorting/Mapping/Filtering it is `false`:
/// their laws are semantic placeholders (Sorted/LengthEq/AllSatisfy) not
/// expressible as graph equations over the 5-combinator kernel.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct CatalogEntry {
    pub name: String,
    pub type_shape: Ty,
    pub fingerprint: String,
    pub laws: Vec<LawEquation>,
    pub cutelim_proven: bool,
}

/// Canonical structural fingerprint of a graph (ADR section 3
/// `fingerprint`; Open Question #6). The fingerprint is a canonical hash
/// of the combinator tree, computed by:
///
/// 1. **Associativity flattening** -- nested `comp(comp(f,g),h)` is
///    flattened to a list `[f,g,h]` (order preserved; `comp` is NOT
///    commutative) and re-nested left-associated. This makes
///    `comp(comp(f,g),h)` and `comp(f,comp(g,h))` produce the same
///    fingerprint.
/// 2. **Identity pruning** -- `id` nodes are dropped from `comp` chains
///    (since `comp(id,f) equiv f` by CutElim `ceIdLeft`/`ceIdRight`). This
///    makes `comp(id,f)` and `f` produce the same fingerprint.
/// 3. **de Bruijn Arr-name canonicalization** -- each `Arr(name)` is
///    replaced by `arr#N` where N is the index of first appearance of that
///    name in a left-to-right traversal. This is invariant under
///    alpha-renaming (`comp(arr_x,arr_y)` == `comp(arr_a,arr_b)`) while
///    preserving sharing structure (`comp(arr_f,arr_f)` != `comp(arr_f,arr_g)`).
///
/// This is a CHEAP structural canonicalization -- NOT full CutElim. It
/// catches associativity of `comp`, identity absorption in `comp` chains,
/// and alpha-equivalence of base-arrow names. It does NOT catch deeper
/// equivalences like `first(id) equiv id` (a CutElim `ceFirstId` step) or
/// `first(f;g) equiv first f; first g` (a `ceFirstFusion` step) -- those
/// are left to Step 3 (CutElim normalization). The fingerprint is a fast
/// filter; the precise check is `law_equal`.
pub fn fingerprint(graph: &PolyGraph) -> String {
    let canon = canonicalize(graph);
    display_canonical(&canon)
}

/// The OLD fingerprint (pre-canonicalization): the combinator-tree shape
/// with all `Arr` names erased to a placeholder `arr`. Kept for
/// comparison/testing -- demonstrates what the canonical fingerprint
/// improves on. Two graphs with the same combinator shape but different
/// base-arrow names share a raw fingerprint; associativity and identity
/// differences are NOT canonicalized.
pub fn raw_fingerprint(graph: &PolyGraph) -> String {
    fn go(g: &PolyGraph) -> String {
        match g {
            PolyGraph::Id => "id".to_string(),
            PolyGraph::Arr(_) => "arr".to_string(),
            PolyGraph::Comp(a, b) => format!("comp({},{})", go(a), go(b)),
            PolyGraph::First(a) => format!("first({})", go(a)),
            PolyGraph::Left(a) => format!("left({})", go(a)),
            PolyGraph::Loop(a) => format!("loop({})", go(a)),
            PolyGraph::Choice(a, b) => format!("choice({},{})", go(a), go(b)),
            PolyGraph::App(a) => format!("app({})", go(a)),
        }
    }
    go(graph)
}

/// Lightweight structural canonicalization (associativity flatten +
/// identity prune + de Bruijn Arr names). Returns a `PolyGraph` whose
/// `Display` form (via `display_canonical`) is the canonical fingerprint.
/// The returned graph has de Bruijn-indexed `Arr` names (`arr#0`,
/// `arr#1`, ...) and left-associated `comp` chains with `id` pruned.
pub fn canonicalize(graph: &PolyGraph) -> PolyGraph {
    let structurally_canonical = canonicalize_structure(graph);
    de_bruijn_arr_names(&structurally_canonical)
}

/// Structural canonicalization: recursively canonicalize children, then
/// flatten `comp` chains (associativity), prune `id` from `comp` chains
/// (identity absorption), and re-nest left-associated.
fn canonicalize_structure(graph: &PolyGraph) -> PolyGraph {
    match graph {
        PolyGraph::Id => PolyGraph::Id,
        PolyGraph::Arr(name) => PolyGraph::Arr(name.clone()),
        PolyGraph::Comp(a, b) => {
            // Recursively canonicalize children first (bottom-up).
            let a_canon = canonicalize_structure(a);
            let b_canon = canonicalize_structure(b);
            // Flatten the comp chain into a flat list (associativity).
            let mut elements: Vec<PolyGraph> = Vec::new();
            flatten_comp(&a_canon, &mut elements);
            flatten_comp(&b_canon, &mut elements);
            // Prune id nodes from the chain (identity absorption:
            // comp(id, f) equiv f by ceIdLeft / ceIdRight).
            elements.retain(|e| !matches!(e, PolyGraph::Id));
            // Re-nest left-associated.
            renest_comp(elements)
        }
        PolyGraph::First(a) => PolyGraph::First(Box::new(canonicalize_structure(a))),
        PolyGraph::Left(a) => PolyGraph::Left(Box::new(canonicalize_structure(a))),
        PolyGraph::Loop(a) => PolyGraph::Loop(Box::new(canonicalize_structure(a))),
        PolyGraph::Choice(a, b) => PolyGraph::Choice(
            Box::new(canonicalize_structure(a)),
            Box::new(canonicalize_structure(b)),
        ),
        PolyGraph::App(a) => PolyGraph::App(Box::new(canonicalize_structure(a))),
    }
}

/// Flatten a (possibly nested) `comp` chain into a flat list of
/// non-`comp` elements, preserving left-to-right order. `comp` is
/// associative but NOT commutative, so order is preserved.
fn flatten_comp(graph: &PolyGraph, out: &mut Vec<PolyGraph>) {
    match graph {
        PolyGraph::Comp(a, b) => {
            flatten_comp(a, out);
            flatten_comp(b, out);
        }
        _ => out.push(graph.clone()),
    }
}

/// Re-nest a flat list of elements into a left-associated `comp` chain.
/// Empty list -> `id`; single element -> that element; two+ ->
/// `comp(comp(..., e2), e3)`.
fn renest_comp(elements: Vec<PolyGraph>) -> PolyGraph {
    match elements.len() {
        0 => PolyGraph::Id,
        1 => elements.into_iter().next().unwrap(),
        _ => {
            let mut iter = elements.into_iter();
            let mut acc = iter.next().unwrap();
            for e in iter {
                acc = PolyGraph::Comp(Box::new(acc), Box::new(e));
            }
            acc
        }
    }
}

/// Replace each `Arr(name)` with `Arr("arr#N")` where N is the de Bruijn
/// index: the first occurrence of a name gets index 0, a repeat of the
/// same name gets the same index, a new name gets the next index. This is
/// invariant under alpha-renaming while preserving sharing structure.
fn de_bruijn_arr_names(graph: &PolyGraph) -> PolyGraph {
    let mut name_map: HashMap<String, usize> = HashMap::new();
    let mut next_index: usize = 0;
    de_bruijn_go(graph, &mut name_map, &mut next_index)
}

fn de_bruijn_go(
    graph: &PolyGraph,
    map: &mut HashMap<String, usize>,
    next: &mut usize,
) -> PolyGraph {
    match graph {
        PolyGraph::Id => PolyGraph::Id,
        PolyGraph::Arr(name) => {
            let idx = if let Some(&idx) = map.get(name) {
                idx
            } else {
                let idx = *next;
                map.insert(name.clone(), idx);
                *next += 1;
                idx
            };
            PolyGraph::Arr(format!("arr#{}", idx))
        }
        PolyGraph::Comp(a, b) => PolyGraph::Comp(
            Box::new(de_bruijn_go(a, map, next)),
            Box::new(de_bruijn_go(b, map, next)),
        ),
        PolyGraph::First(a) => PolyGraph::First(Box::new(de_bruijn_go(a, map, next))),
        PolyGraph::Left(a) => PolyGraph::Left(Box::new(de_bruijn_go(a, map, next))),
        PolyGraph::Loop(a) => PolyGraph::Loop(Box::new(de_bruijn_go(a, map, next))),
        PolyGraph::Choice(a, b) => PolyGraph::Choice(
            Box::new(de_bruijn_go(a, map, next)),
            Box::new(de_bruijn_go(b, map, next)),
        ),
        PolyGraph::App(a) => PolyGraph::App(Box::new(de_bruijn_go(a, map, next))),
    }
}

/// Display a canonicalized graph as a fingerprint string. `Arr` nodes
/// already carry de Bruijn names (`arr#N`); other combinators use their
/// structural shape.
fn display_canonical(graph: &PolyGraph) -> String {
    match graph {
        PolyGraph::Id => "id".to_string(),
        PolyGraph::Arr(name) => name.clone(),
        PolyGraph::Comp(a, b) => format!("comp({},{})", display_canonical(a), display_canonical(b)),
        PolyGraph::First(a) => format!("first({})", display_canonical(a)),
        PolyGraph::Left(a) => format!("left({})", display_canonical(a)),
        PolyGraph::Loop(a) => format!("loop({})", display_canonical(a)),
        PolyGraph::Choice(a, b) => {
            format!("choice({},{})", display_canonical(a), display_canonical(b))
        }
        PolyGraph::App(a) => format!("app({})", display_canonical(a)),
    }
}

// ============================================================================
// 8. Abstract Storage + In-Memory Implementation  (ADR-0075 section 4)
// ============================================================================
//
// The storage interface is abstract so a SQLite backend can plug in later
// WITHOUT changing the inference engine. The engine (section 9 pipeline)
// is written against `impl TraitCatalogStore`. This file provides only the
// in-memory implementation (`InMemoryStore`); the SQLite schema is sketched
// in ADR section 4 and is NOT implemented here.

/// Stable identifier for a catalog entry. (INTEGER PRIMARY KEY in the
/// SQLite schema.)
pub type EntryId = usize;

/// Cached verification outcome for a `(graph fingerprint, law pattern)` pair.
/// (ADR section 4 `verification_cache`.)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VerificationResult {
    /// CutElim normalization confirmed the law: lhs and rhs normalize equal.
    Verified,
    /// The law is a semantic placeholder not yet expressible as a graph
    /// equation (cutelim_proven = false). Not verified, not failed.
    Unknown,
    /// CutElim normalization disproved the law: lhs and rhs normalize to
    /// different forms.
    Failed,
}

impl fmt::Display for VerificationResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            VerificationResult::Verified => write!(f, "verified"),
            VerificationResult::Unknown => write!(f, "unknown(placeholder)"),
            VerificationResult::Failed => write!(f, "failed"),
        }
    }
}

/// Abstract storage interface (ADR section 4 `interface TraitCatalogStore`).
///
/// The engine takes `&mut impl TraitCatalogStore` -- `&mut` because the
/// pipeline writes verification results to the cache. A read-only view
/// (e.g. a remote catalog) can be wrapped with interior mutability later;
/// the abstraction point that matters is that the engine never names
/// `InMemoryStore` or SQLite directly.
pub trait TraitCatalogStore {
    /// All entries whose `type_shape` unifies with `shape` (ADR: indexed
    /// by type shape; this prototype scans linearly -- O(|catalog|) -- and
    /// a real backend uses a hash/B-tree index).
    fn lookup_by_type_shape(&self, shape: &Ty) -> Vec<(EntryId, CatalogEntry)>;

    /// All entries with exactly `fp` as their fingerprint (ADR: indexed).
    fn lookup_by_fingerprint(&self, fp: &str) -> Vec<(EntryId, CatalogEntry)>;

    /// Fetch a single entry by id.
    fn get(&self, id: EntryId) -> Option<CatalogEntry>;

    /// Insert a new entry, returning its id.
    fn insert(&mut self, entry: CatalogEntry) -> EntryId;

    /// Remove an entry.
    fn remove(&mut self, id: EntryId);

    /// Read a cached verification result for `(graph_fingerprint, law_pattern_id)`.
    fn get_cached_verification(
        &self,
        graph_fp: &str,
        law_pattern_id: &str,
    ) -> Option<VerificationResult>;

    /// Write a cached verification result.
    fn put_cached_verification(
        &mut self,
        graph_fp: String,
        law_pattern_id: String,
        result: VerificationResult,
    );

    /// All entries (used by the demo/tests to count the built-in catalog).
    fn entries(&self) -> Vec<(EntryId, CatalogEntry)>;

    /// Cache-statistics hooks (instrumentation). A real backend may back
    /// these with query counters; the in-memory impl uses simple counters.
    fn record_cache_hit(&mut self);
    fn record_cache_miss(&mut self);
    fn cache_hits(&self) -> usize;
    fn cache_misses(&self) -> usize;
}

/// In-memory storage backend (ADR section 4 "Alternative implementations":
/// "In-memory -- for development and testing; no persistence").
pub struct InMemoryStore {
    next_id: EntryId,
    by_id: HashMap<EntryId, CatalogEntry>,
    cache: HashMap<(String, String), VerificationResult>,
    /// Number of cache reads that hit (for the demo). A real backend would
    /// expose this via instrumentation; kept here for visibility.
    pub cache_hits: usize,
    /// Number of cache reads that missed.
    pub cache_misses: usize,
}

impl InMemoryStore {
    pub fn new() -> Self {
        InMemoryStore {
            next_id: 0,
            by_id: HashMap::new(),
            cache: HashMap::new(),
            cache_hits: 0,
            cache_misses: 0,
        }
    }
}

impl TraitCatalogStore for InMemoryStore {
    fn lookup_by_type_shape(&self, shape: &Ty) -> Vec<(EntryId, CatalogEntry)> {
        self.by_id
            .iter()
            .filter(|(_, e)| Unifier::unify(&e.type_shape, shape).is_some())
            .map(|(id, e)| (*id, e.clone()))
            .collect()
    }

    fn lookup_by_fingerprint(&self, fp: &str) -> Vec<(EntryId, CatalogEntry)> {
        self.by_id
            .iter()
            .filter(|(_, e)| e.fingerprint == fp)
            .map(|(id, e)| (*id, e.clone()))
            .collect()
    }

    fn get(&self, id: EntryId) -> Option<CatalogEntry> {
        self.by_id.get(&id).cloned()
    }

    fn insert(&mut self, entry: CatalogEntry) -> EntryId {
        let id = self.next_id;
        self.next_id += 1;
        self.by_id.insert(id, entry);
        id
    }

    fn remove(&mut self, id: EntryId) {
        self.by_id.remove(&id);
    }

    fn get_cached_verification(
        &self,
        graph_fp: &str,
        law_pattern_id: &str,
    ) -> Option<VerificationResult> {
        self.cache
            .get(&(graph_fp.to_string(), law_pattern_id.to_string()))
            .copied()
    }

    fn put_cached_verification(
        &mut self,
        graph_fp: String,
        law_pattern_id: String,
        result: VerificationResult,
    ) {
        self.cache.insert((graph_fp, law_pattern_id), result);
    }

    fn entries(&self) -> Vec<(EntryId, CatalogEntry)> {
        let mut v: Vec<(EntryId, CatalogEntry)> =
            self.by_id.iter().map(|(id, e)| (*id, e.clone())).collect();
        v.sort_by_key(|(id, _)| *id);
        v
    }

    fn record_cache_hit(&mut self) {
        self.cache_hits += 1;
    }
    fn record_cache_miss(&mut self) {
        self.cache_misses += 1;
    }
    fn cache_hits(&self) -> usize {
        self.cache_hits
    }
    fn cache_misses(&self) -> usize {
        self.cache_misses
    }
}

// ============================================================================
// 9. The 3-Step Matching Pipeline  (ADR-0075 section 3 + section 12)
// ============================================================================
//
//   Step 1: Type filter   -- HM unify the graph's inferred type against each
//                            entry's `type_shape`. Prune non-unifying entries.
//   Step 2: Fingerprint   -- hash-compare the graph's structural fingerprint
//                            with each surviving entry's `fingerprint`.
//   Step 3: CutElim       -- for each law of each surviving entry, run
//                            `law_equal` (or recall a cached result). Only
//                            CutElim-proven entries are checked; placeholder
//                            entries report `Unknown` and no verified laws.
//
// Multi-match: ALL matching entries are returned (ADR section 3 "Multi-match").

/// A trait matched to a graph, with the subset of its laws that CutElim
/// verified. `cutelim_proven` and `placeholder_law_count` are reported for
/// honesty (the ADR is explicit that non-functor laws are aspirational).
#[derive(Debug, Clone)]
pub struct MatchedTrait {
    pub entry_name: String,
    pub verified_laws: Vec<String>,
    /// Laws that are semantic placeholders (not CutElim-checkable).
    pub placeholder_laws: Vec<String>,
    pub cutelim_proven: bool,
}

/// Run the 3-step pipeline. `sig` is the base-arrow signature used to infer
/// the graph's type (annotation-free HM). Returns all matching traits.
pub fn infer_traits(
    store: &mut impl TraitCatalogStore,
    graph: &PolyGraph,
    sig: &[PolySigEntry],
) -> Vec<MatchedTrait> {
    // --- Step 0: infer the graph's type and fingerprint ---
    let (gin, gout) = infer_type_poly(graph, sig).unwrap_or_else(|e| {
        // If inference fails, use fresh vars so type-filter prunes everything.
        eprintln!("[infer_traits] type inference failed: {}", e);
        (tv("__infer_fail__"), tv("__infer_fail__"))
    });
    let graph_type = arr_t(gin.clone(), gout.clone());
    let graph_fp = fingerprint(graph);

    // --- Step 1: type filter (HM unify) ---
    let type_candidates = store.lookup_by_type_shape(&graph_type);

    // --- Step 2: structural fingerprint (hash compare) ---
    let fp_candidates: Vec<(EntryId, CatalogEntry)> = type_candidates
        .into_iter()
        .filter(|(_, e)| e.fingerprint == graph_fp)
        .collect();

    // --- Step 3: CutElim law verification (slow, only on candidates) ---
    let mut matches: Vec<MatchedTrait> = Vec::new();
    for (_id, entry) in &fp_candidates {
        let mut verified: Vec<String> = Vec::new();
        let mut placeholders: Vec<String> = Vec::new();

        for law in &entry.laws {
            let law_id = format!("{}::{}", entry.name, law.name);
            // Cache check.
            if let Some(cached) = store.get_cached_verification(&graph_fp, &law_id) {
                store.record_cache_hit();
                match cached {
                    VerificationResult::Verified => verified.push(law.name.clone()),
                    VerificationResult::Unknown => placeholders.push(law.name.clone()),
                    VerificationResult::Failed => {}
                }
                continue;
            }
            store.record_cache_miss();

            // Placeholder laws: not expressible as graph equations.
            if !entry.cutelim_proven {
                store.put_cached_verification(
                    graph_fp.clone(),
                    law_id.clone(),
                    VerificationResult::Unknown,
                );
                placeholders.push(law.name.clone());
                continue;
            }

            // CutElim-proven law: normalize both sides and compare.
            let result = if law_equal(&law.lhs, &law.rhs) {
                VerificationResult::Verified
            } else {
                VerificationResult::Failed
            };
            store.put_cached_verification(graph_fp.clone(), law_id.clone(), result);
            if result == VerificationResult::Verified {
                verified.push(law.name.clone());
            }
        }

        matches.push(MatchedTrait {
            entry_name: entry.name.clone(),
            verified_laws: verified,
            placeholder_laws: placeholders,
            cutelim_proven: entry.cutelim_proven,
        });
    }

    // Stable ordering by entry name for deterministic output.
    matches.sort_by(|a, b| a.entry_name.cmp(&b.entry_name));
    matches
}

// ============================================================================
// 10. Built-in Catalog  (ADR-0075 section 3 "fully catalog-driven")
// ============================================================================
//
// The engine ships with a built-in catalog. This is NOT a hardcoded
// refinement fallback -- the engine has zero hardcoded contracts; all
// refinement inference goes through the catalog. Users can extend,
// override, or replace these entries.
//
// CutElim-proven (laws ARE the CutElim rewrites):
//   * Functor          -- first(id) === id,  first(f;g) === first f ; first g
//   * CoproductFunctor -- left(id)  === id,  left(f;g)  === left f  ; left g
//
// Semantic placeholders (cutelim_proven = false; aspirational per ADR):
//   * Sorting   -- sort : [A] ~> [A],  law sorted:  Sorted(sort(x))
//   * Mapping   -- map  : [A] ~> [B],  law length:  LengthEq(map(x), x)
//   * Filtering -- filter,            law allsat:  AllSatisfy(filter(x), p)

/// A representative `map`-shaped graph (ADR section 1):
///   map = loop (arr uncons >>> choice (arr nil) (first f >>> arr cons))
/// built from primitives, then a `merge` step collapses the summed output.
/// Used both as the demo graph and as the fingerprint source for the
/// Functor/Mapping catalog entries.
fn map_shape_graph() -> PolyGraph {
    // loop ( first ( uncons ; choice nil (first f ; cons) ) )
    let inner = gcomp(
        garr("uncons"),
        gchoice(
            garr("nil"),
            gcomp(gfirst(garr("f")), garr("cons")),
        ),
    );
    let looped = gloop(gfirst(inner));
    // merge the ([B]+[B]) ~> [B]
    gcomp(looped, garr("merge"))
}

/// Populate the built-in catalog into `store`. Returns the number inserted.
pub fn populate_builtin_catalog(store: &mut impl TraitCatalogStore) -> usize {
    let map_fp = fingerprint(&map_shape_graph());

    // --- Functor (CutElim-proven via ceFirstId / ceFirstFusion) ---
    let functor = CatalogEntry {
        name: "Functor".to_string(),
        // ADR-0075 section 5 / Open Question #5: the generic `Functor<F>`
        // type shape is the higher-kinded `F<A> ~> F<B>` (using `Ty::App`),
        // NOT the `List` instance `[A] ~> [B]`. Unification bridges
        // `List(t)` to `App(Atom("List"), t)`, so the demo `map` graph's
        // inferred type `[a] ~> [b]` still matches (binding `F := List,
        // A := a, B := b`), while a non-functor arrow like `Int ~> Bool`
        // does NOT (an `Atom` is not an `App`). NOTE: this is the type
        // filter only -- higher-kinded trait *parameters* in the surface
        // syntax (`trait Functor<F>`) remain open (ADR OQ#5).
        type_shape: arr_t(app_t(tv("F"), tv("A")), app_t(tv("F"), tv("B"))),
        fingerprint: map_fp.clone(),
        laws: vec![
            LawEquation {
                name: "identity".to_string(),
                lhs: gfirst(gid()),
                rhs: gid(),
            },
            LawEquation {
                name: "composition".to_string(),
                lhs: gfirst(gcomp(garr("f"), garr("g"))),
                rhs: gcomp(gfirst(garr("f")), gfirst(garr("g"))),
            },
        ],
        cutelim_proven: true,
    };
    store.insert(functor);

    // --- CoproductFunctor (CutElim-proven via ceLeftId / ceLeftFusion) ---
    let coproduct_fp = fingerprint(&gleft(gcomp(garr("f"), garr("g"))));
    let coproduct = CatalogEntry {
        name: "CoproductFunctor".to_string(),
        type_shape: arr_t(sum(tv("A"), tv("C")), sum(tv("B"), tv("D"))),
        fingerprint: coproduct_fp,
        laws: vec![
            LawEquation {
                name: "identity".to_string(),
                lhs: gleft(gid()),
                rhs: gid(),
            },
            LawEquation {
                name: "composition".to_string(),
                lhs: gleft(gcomp(garr("f"), garr("g"))),
                rhs: gcomp(gleft(garr("f")), gleft(garr("g"))),
            },
        ],
        cutelim_proven: true,
    };
    store.insert(coproduct);

    // --- Sorting (semantic placeholder; NOT CutElim-proven) ---
    let sort_fp = fingerprint(&gcomp(garr("uncons"), gloop(gfirst(garr("cmp")))));
    let sorting = CatalogEntry {
        name: "Sorting".to_string(),
        type_shape: arr_t(list(tv("A")), list(tv("A"))),
        fingerprint: sort_fp,
        laws: vec![LawEquation {
            name: "sorted".to_string(),
            // Placeholder: Sorted(sort(x)) is a semantic predicate, not a
            // graph equation. lhs/rhs are sentinels; never checked because
            // cutelim_proven = false.
            lhs: garr("__placeholder__"),
            rhs: garr("__placeholder__"),
        }],
        cutelim_proven: false,
    };
    store.insert(sorting);

    // --- Mapping (semantic placeholder; NOT CutElim-proven) ---
    let mapping = CatalogEntry {
        name: "Mapping".to_string(),
        type_shape: arr_t(list(tv("A")), list(tv("B"))),
        fingerprint: map_fp.clone(),
        laws: vec![LawEquation {
            name: "length".to_string(),
            // Placeholder: LengthEq(map(x), x) is a semantic predicate.
            lhs: garr("__placeholder__"),
            rhs: garr("__placeholder__"),
        }],
        cutelim_proven: false,
    };
    store.insert(mapping);

    // --- Filtering (semantic placeholder; NOT CutElim-proven) ---
    let filter_fp = fingerprint(&gcomp(gfirst(garr("p")), gloop(garr("uncons"))));
    let filtering = CatalogEntry {
        name: "Filtering".to_string(),
        // filter : (A ~> Bool) ~> ([A] ~> [A])  (ADR section 3)
        type_shape: arr_t(
            arr_t(tv("A"), bool_t()),
            arr_t(list(tv("A")), list(tv("A"))),
        ),
        fingerprint: filter_fp,
        laws: vec![LawEquation {
            name: "allsat".to_string(),
            // Placeholder: AllSatisfy(filter(x), p) is a semantic predicate.
            lhs: garr("__placeholder__"),
            rhs: garr("__placeholder__"),
        }],
        cutelim_proven: false,
    };
    store.insert(filtering);

    5
}

// ============================================================================
// 11. Demo + Tests (mirrors the `*_tests.rs` style: section dividers,
//     `fn main()` runs a demo then assertions.)
// ============================================================================

/// The base-arrow signature used for the demo `map` graph.
fn demo_signature() -> Vec<PolySigEntry> {
    // uncons : [A] ~> (() + (A x [C]))
    //   Prototype liberty: the tail is a polymorphic [C] independent of A,
    //   so HM does not force the element type of input and output to match
    //   (real uncons has tail [A]). This lets map infer [a] ~> [b].
    vec![
        PolySigEntry {
            name: "uncons",
            input: list(tv("A")),
            output: sum(Ty::Unit, prod(tv("A"), list(tv("C")))),
        },
        PolySigEntry {
            name: "nil",
            input: Ty::Unit,
            output: list(tv("B")),
        },
        PolySigEntry {
            name: "cons",
            input: prod(tv("B"), list(tv("B"))),
            output: list(tv("B")),
        },
        PolySigEntry {
            name: "f",
            input: tv("A"),
            output: tv("B"),
        },
        PolySigEntry {
            name: "merge",
            input: sum(list(tv("B")), list(tv("B"))),
            output: list(tv("B")),
        },
    ]
}

fn print_section(title: &str) {
    println!();
    println!("=== {} ===", title);
}

fn main() {
    print_section("ADR-0075 prototype: Traits as Arrow Signatures");

    // --------------------------------------------------------------------
    // Demo: build a `map` graph from primitives and run the pipeline.
    // --------------------------------------------------------------------
    print_section("Demo: map graph from primitives (loop+first+choice+arr)");
    let map_graph = map_shape_graph();
    let sig = demo_signature();
    let (gin, gout) = infer_type_poly(&map_graph, &sig).expect("map graph should type-check");
    println!("graph : {}", map_graph);
    println!("type  : {} ~> {}", gin, gout);
    println!("fp    : {}", fingerprint(&map_graph));

    // Build the catalog.
    let mut store = InMemoryStore::new();
    let n = populate_builtin_catalog(&mut store);
    println!("built-in catalog entries: {}", n);

    // First inference run.
    print_section("Pipeline run #1 (cold cache)");
    let matches1 = infer_traits(&mut store, &map_graph, &sig);
    println!("matches (multi-match):");
    for m in &matches1 {
        println!(
            "  - {} : cutelim_proven={} verified={:?} placeholder={:?}",
            m.entry_name, m.cutelim_proven, m.verified_laws, m.placeholder_laws
        );
    }
    println!(
        "cache: hits={} misses={}",
        store.cache_hits(), store.cache_misses()
    );

    // Second inference run -- should hit the cache for the CutElim-proven
    // laws (the demo's cache-hit demonstration).
    print_section("Pipeline run #2 (warm cache)");
    let matches2 = infer_traits(&mut store, &map_graph, &sig);
    println!("matches (multi-match):");
    for m in &matches2 {
        println!(
            "  - {} : cutelim_proven={} verified={:?} placeholder={:?}",
            m.entry_name, m.cutelim_proven, m.verified_laws, m.placeholder_laws
        );
    }
    println!(
        "cache: hits={} misses={}",
        store.cache_hits(), store.cache_misses()
    );

    // --------------------------------------------------------------------
    // Tests as assertions.
    // --------------------------------------------------------------------
    print_section("Tests");

    // --- Test 1: CutElim law_equal true cases ---
    assert!(law_equal(&gfirst(gid()), &gid()), "ceFirstId: first(id) === id");
    assert!(
        law_equal(&gcomp(gfirst(garr("f")), gfirst(garr("g"))), &gfirst(gcomp(garr("f"), garr("g")))),
        "ceFirstFusion: comp(first f, first g) === first(comp f g)"
    );
    assert!(law_equal(&gleft(gid()), &gid()), "ceLeftId: left(id) === id");
    assert!(
        law_equal(&gcomp(gleft(garr("f")), gleft(garr("g"))), &gleft(gcomp(garr("f"), garr("g")))),
        "ceLeftFusion: comp(left f, left g) === left(comp f g)"
    );
    assert!(law_equal(&gcomp(gid(), garr("f")), &garr("f")), "ceIdLeft: comp(id, f) === f");
    assert!(law_equal(&gcomp(garr("f"), gid()), &garr("f")), "ceIdRight: comp(f, id) === f");
    println!("[pass] CutElim law_equal true cases (all 6 rewrites)");

    // --- Test 2: CutElim law_equal false cases ---
    // first(f) does not normalize to id (f is an opaque base arrow).
    assert!(!law_equal(&gfirst(garr("f")), &gid()), "first(f) !== id");
    // comp(id, f) normalizes to f, not g (different opaque names).
    assert!(!law_equal(&gcomp(gid(), garr("f")), &garr("g")), "comp(id,f) !== g");
    // comp(first f, first g) normalizes to first(comp f g), not first(comp g f).
    assert!(
        !law_equal(&gcomp(gfirst(garr("f")), gfirst(garr("g"))), &gfirst(gcomp(garr("g"), garr("f")))),
        "first(f;g) !== first(g;f) (order matters)"
    );
    println!("[pass] CutElim law_equal false cases");

    // --- Test 3: fingerprint same-shape-different-Arr ---
    assert_eq!(
        fingerprint(&garr("f")),
        fingerprint(&garr("g")),
        "fingerprint ignores Arr names: arr(f) == arr(g)"
    );
    assert_eq!(
        fingerprint(&gcomp(garr("f"), garr("g"))),
        fingerprint(&gcomp(garr("x"), garr("y"))),
        "fingerprint ignores Arr names in structure"
    );
    println!("[pass] fingerprint same-shape-different-Arr");

    // --- Test 4: fingerprint different-shape ---
    assert_ne!(
        fingerprint(&gcomp(garr("f"), garr("g"))),
        fingerprint(&gfirst(garr("f"))),
        "comp and first have different fingerprints"
    );
    assert_ne!(
        fingerprint(&map_shape_graph()),
        fingerprint(&gleft(gcomp(garr("f"), garr("g")))),
        "map-shape and left-shape differ"
    );
    println!("[pass] fingerprint different-shape");

    // --- Test 4a: canonical fingerprint -- associativity (ADR OQ#6) ---
    // comp(comp(f,g),h) and comp(f,comp(g,h)) are the same graph by
    // associativity of >>>. The canonical fingerprint flattens comp chains
    // so both produce the same hash. The OLD raw_fingerprint does NOT.
    let left_assoc = gcomp(gcomp(garr("f"), garr("g")), garr("h"));
    let right_assoc = gcomp(garr("f"), gcomp(garr("g"), garr("h")));
    assert_eq!(
        fingerprint(&left_assoc),
        fingerprint(&right_assoc),
        "associativity: comp(comp(f,g),h) == comp(f,comp(g,h)) after canonicalization"
    );
    // Confirm the old raw_fingerprint does NOT catch this (demonstrates
    // the improvement).
    assert_ne!(
        raw_fingerprint(&left_assoc),
        raw_fingerprint(&right_assoc),
        "raw_fingerprint does NOT canonicalize associativity (was: different)"
    );
    // Deeper nesting: comp(comp(comp(a,b),c),d) == comp(a,comp(b,comp(c,d)))
    let deep_left = gcomp(gcomp(gcomp(garr("a"), garr("b")), garr("c")), garr("d"));
    let deep_right = gcomp(garr("a"), gcomp(garr("b"), gcomp(garr("c"), garr("d"))));
    assert_eq!(
        fingerprint(&deep_left),
        fingerprint(&deep_right),
        "associativity: deep nesting flattens to same fingerprint"
    );
    println!("[pass] canonical fingerprint -- associativity (comp flattening)");

    // --- Test 4b: canonical fingerprint -- identity pruning (ADR OQ#6) ---
    // comp(id, f) and f are the same graph after CutElim ceIdLeft. The
    // canonical fingerprint prunes id from comp chains, so both produce
    // the same hash. The OLD raw_fingerprint does NOT.
    assert_eq!(
        fingerprint(&gcomp(gid(), garr("f"))),
        fingerprint(&garr("f")),
        "identity pruning: comp(id, f) == f after canonicalization"
    );
    assert_eq!(
        fingerprint(&gcomp(garr("f"), gid())),
        fingerprint(&garr("f")),
        "identity pruning: comp(f, id) == f after canonicalization"
    );
    // comp(id, comp(id, f)) == f (double identity absorption).
    assert_eq!(
        fingerprint(&gcomp(gid(), gcomp(gid(), garr("f")))),
        fingerprint(&garr("f")),
        "identity pruning: comp(id, comp(id, f)) == f"
    );
    // comp(id, id) == id (all identities pruned).
    assert_eq!(
        fingerprint(&gcomp(gid(), gid())),
        fingerprint(&gid()),
        "identity pruning: comp(id, id) == id"
    );
    // Confirm the old raw_fingerprint does NOT catch this.
    assert_ne!(
        raw_fingerprint(&gcomp(gid(), garr("f"))),
        raw_fingerprint(&garr("f")),
        "raw_fingerprint does NOT prune identity (was: different)"
    );
    println!("[pass] canonical fingerprint -- identity pruning (id dropped from comp)");

    // --- Test 4c: canonical fingerprint -- alpha-invariance (ADR OQ#6) ---
    // comp(arr_x, arr_y) and comp(arr_a, arr_b) are alpha-equivalent.
    // The de Bruijn indexing makes both -> comp(arr#0, arr#1).
    assert_eq!(
        fingerprint(&gcomp(garr("x"), garr("y"))),
        fingerprint(&gcomp(garr("a"), garr("b"))),
        "alpha-invariance: comp(arr_x, arr_y) == comp(arr_a, arr_b)"
    );
    // Single arr: arr(f) == arr(g) (already tested in Test 3, reaffirm).
    assert_eq!(
        fingerprint(&garr("f")),
        fingerprint(&garr("g")),
        "alpha-invariance: single arr names erased"
    );
    println!("[pass] canonical fingerprint -- alpha-invariance (de Bruijn Arr names)");

    // --- Test 4d: canonical fingerprint -- sharing preserved (ADR OQ#6) ---
    // comp(arr_f, arr_f) uses the SAME arrow twice (sharing). comp(arr_f,
    // arr_g) uses two DIFFERENT arrows. The de Bruijn indexing preserves
    // this: the first -> comp(arr#0, arr#0), the second -> comp(arr#0,
    // arr#1). These must have DIFFERENT fingerprints.
    assert_ne!(
        fingerprint(&gcomp(garr("f"), garr("f"))),
        fingerprint(&gcomp(garr("f"), garr("g"))),
        "sharing preserved: comp(arr_f, arr_f) != comp(arr_f, arr_g)"
    );
    // Three-way: comp(arr_f, comp(arr_f, arr_g)) has sharing (f twice);
    // comp(arr_f, comp(arr_g, arr_h)) has no sharing (all distinct).
    assert_ne!(
        fingerprint(&gcomp(garr("f"), gcomp(garr("f"), garr("g")))),
        fingerprint(&gcomp(garr("f"), gcomp(garr("g"), garr("h")))),
        "sharing preserved: repeated arr name differs from all-distinct"
    );
    // But comp(arr_f, comp(arr_f, arr_g)) and comp(arr_x, comp(arr_x,
    // arr_y)) ARE alpha-equivalent (same sharing pattern).
    assert_eq!(
        fingerprint(&gcomp(garr("f"), gcomp(garr("f"), garr("g")))),
        fingerprint(&gcomp(garr("x"), gcomp(garr("x"), garr("y")))),
        "alpha-invariance with sharing: same sharing pattern matches"
    );
    println!("[pass] canonical fingerprint -- sharing preserved (de Bruijn distinguishes repeated names)");

    // --- Test 4e: canonical fingerprint -- law-relevant difference (ADR OQ#6) ---
    // first(f) and left(f) are different combinators with different laws.
    // Their fingerprints must differ.
    assert_ne!(
        fingerprint(&gfirst(garr("f"))),
        fingerprint(&gleft(garr("f"))),
        "law-relevant difference: first(f) != left(f)"
    );
    // comp(first(f), first(g)) and comp(left(f), left(g)) also differ.
    assert_ne!(
        fingerprint(&gcomp(gfirst(garr("f")), gfirst(garr("g")))),
        fingerprint(&gcomp(gleft(garr("f")), gleft(garr("g")))),
        "law-relevant difference: comp(first,first) != comp(left,left)"
    );
    // loop and first are different combinators.
    assert_ne!(
        fingerprint(&gloop(garr("f"))),
        fingerprint(&gfirst(garr("f"))),
        "law-relevant difference: loop(f) != first(f)"
    );
    // choice and comp are different combinators.
    assert_ne!(
        fingerprint(&gchoice(garr("f"), garr("g"))),
        fingerprint(&gcomp(garr("f"), garr("g"))),
        "law-relevant difference: choice(f,g) != comp(f,g)"
    );
    println!("[pass] canonical fingerprint -- law-relevant differences preserved");

    // --- Test 4f: canonical fingerprint -- combinational improvement ---
    // Associativity + identity + alpha together: comp(comp(id, arr_x),
    // arr_y) == comp(arr_a, arr_b) after canonicalization (id pruned,
    // comp flattened, names de Bruijn'd).
    assert_eq!(
        fingerprint(&gcomp(gcomp(gid(), garr("x")), garr("y"))),
        fingerprint(&gcomp(garr("a"), garr("b"))),
        "combined: comp(comp(id, arr_x), arr_y) == comp(arr_a, arr_b)"
    );
    // But NOT equal to comp(arr_a, arr_a) (different sharing).
    assert_ne!(
        fingerprint(&gcomp(gcomp(gid(), garr("x")), garr("y"))),
        fingerprint(&gcomp(garr("a"), garr("a"))),
        "combined: sharing still distinguishes after id pruning + associativity"
    );
    println!("[pass] canonical fingerprint -- combined associativity + identity + alpha + sharing");

    // --- Test 5: type filter pruning ---
    // The map graph type [a] ~> [b] must NOT unify with Filtering's
    // (A ~> Bool) ~> ([A] ~> [A]) nor CoproductFunctor's (A+C)~>(B+D).
    let map_type = arr_t(gin.clone(), gout.clone());
    let type_matches = store.lookup_by_type_shape(&map_type);
    let type_names: Vec<&str> = type_matches.iter().map(|(_, e)| e.name.as_str()).collect();
    assert!(type_names.contains(&"Functor"), "Functor passes type filter");
    assert!(type_names.contains(&"Mapping"), "Mapping passes type filter");
    assert!(type_names.contains(&"Sorting"), "Sorting passes type filter ([A]~>[A] unifies)");
    assert!(!type_names.contains(&"Filtering"), "Filtering pruned by type filter");
    assert!(!type_names.contains(&"CoproductFunctor"), "CoproductFunctor pruned by type filter");
    println!("[pass] type filter pruning (Filtering, CoproductFunctor excluded)");

    // --- Test 6: fingerprint pruning ---
    let map_fp = fingerprint(&map_shape_graph());
    let fp_matches = store.lookup_by_fingerprint(&map_fp);
    let fp_names: Vec<&str> = fp_matches.iter().map(|(_, e)| e.name.as_str()).collect();
    assert!(fp_names.contains(&"Functor"), "Functor shares map fingerprint");
    assert!(fp_names.contains(&"Mapping"), "Mapping shares map fingerprint");
    assert!(!fp_names.contains(&"Sorting"), "Sorting pruned by fingerprint");
    println!("[pass] fingerprint pruning (Sorting excluded)");

    // --- Test 7: pipeline map -> Functor (multi-match) ---
    assert!(matches1.iter().any(|m| m.entry_name == "Functor"), "map matches Functor");
    let functor_match = matches1.iter().find(|m| m.entry_name == "Functor").unwrap();
    assert_eq!(
        functor_match.verified_laws, vec!["identity".to_string(), "composition".to_string()],
        "Functor's two laws are CutElim-verified"
    );
    assert!(functor_match.cutelim_proven, "Functor is cutelim_proven");
    // Multi-match: Mapping also matches (same type+fp), but with placeholder laws.
    assert!(matches1.iter().any(|m| m.entry_name == "Mapping"), "map also matches Mapping (multi-match)");
    let mapping_match = matches1.iter().find(|m| m.entry_name == "Mapping").unwrap();
    assert!(mapping_match.verified_laws.is_empty(), "Mapping has no CutElim-verified laws");
    assert!(!mapping_match.cutelim_proven, "Mapping is a placeholder entry");
    assert_eq!(mapping_match.placeholder_laws, vec!["length".to_string()], "Mapping's law is a placeholder");
    // Sorting/Filtering/CoproductFunctor must NOT be in the final matches.
    let match_names: Vec<&str> = matches1.iter().map(|m| m.entry_name.as_str()).collect();
    assert!(!match_names.contains(&"Sorting"), "Sorting not in final matches (pruned by fp)");
    assert!(!match_names.contains(&"Filtering"), "Filtering not in final matches (pruned by type)");
    assert!(!match_names.contains(&"CoproductFunctor"), "CoproductFunctor not in final matches (pruned by type+fp)");
    println!("[pass] pipeline map -> [Functor (verified), Mapping (placeholder)] (multi-match)");

    // --- Test 8: cache hit on re-inference ---
    // Run #1 missed (computed+cached) Functor's two laws and Mapping's one.
    // Run #2 must have hit the cache for those three law checks.
    assert!(store.cache_hits() >= 3, "run #2 should hit cache for cached laws, got {} hits", store.cache_hits());
    // Both runs return identical matches.
    assert_eq!(matches1.len(), matches2.len(), "both runs return same number of matches");
    for (a, b) in matches1.iter().zip(matches2.iter()) {
        assert_eq!(a.entry_name, b.entry_name);
        assert_eq!(a.verified_laws, b.verified_laws);
    }
    println!("[pass] cache hit on re-inference (cache_hits={})", store.cache_hits());

    // --- Test 9: 5 built-in entries present ---
    let all = store.entries();
    assert_eq!(all.len(), 5, "built-in catalog has 5 entries, got {}", all.len());
    let names: Vec<String> = all.iter().map(|(_, e)| e.name.clone()).collect();
    for required in ["Functor", "CoproductFunctor", "Sorting", "Mapping", "Filtering"].iter() {
        assert!(names.iter().any(|n| n == *required), "built-in catalog contains {}", required);
    }
    println!("[pass] 5 built-in entries present: {:?}", names);

    // --- Test 10: CutElim-proven vs placeholder honesty ---
    let proven: Vec<&str> = all
        .iter()
        .filter(|(_, e)| e.cutelim_proven)
        .map(|(_, e)| e.name.as_str())
        .collect();
    let placeholder: Vec<&str> = all
        .iter()
        .filter(|(_, e)| !e.cutelim_proven)
        .map(|(_, e)| e.name.as_str())
        .collect();
    assert_eq!(proven, vec!["Functor", "CoproductFunctor"], "only functor entries are CutElim-proven");
    assert_eq!(placeholder, vec!["Sorting", "Mapping", "Filtering"], "semantic entries are placeholders");
    println!("[pass] CutElim-proven={:?}  placeholder={:?}", proven, placeholder);

    // --- Test 11: HKT type-filter discrimination (ADR-0075 section 5, OQ#5) ---
    // Functor's `type_shape` is now the higher-kinded `F<A> ~> F<B>`. The
    // type filter must (a) still match a `[a] ~> [b]` graph (binding
    // F := List, A := a, B := b via the List<->App bridge), (b) NOT match a
    // non-functor arrow `Int ~> Bool` (an Atom is not an App), and (c) match
    // a non-List constructor `Tree<a> ~> Tree<b>` (F := Tree), showing the
    // filter is not pinned to List.
    let functor_shape = arr_t(app_t(tv("F"), tv("A")), app_t(tv("F"), tv("B")));

    // (a) Positive: [a] ~> [b] unifies with F<A> ~> F<B>.
    let list_arrow = arr_t(list(tv("a")), list(tv("b")));
    let u_list = Unifier::unify(&functor_shape, &list_arrow)
        .expect("[a]~>[b] must unify with F<A>~>F<B>");
    let f_list = u_list.get("F").expect("F bound for [a]~>[b]");
    assert!(
        matches!(f_list, Ty::Atom(s) if s == "List"),
        "F := List for [a]~>[b], got {}",
        f_list
    );
    println!("[pass] [a]~>[b] unifies with F<A>~>F<B> (F := List)");

    // (b) Negative: Int ~> Bool does NOT unify with F<A> ~> F<B>.
    let int_arrow = arr_t(atom("Int"), atom("Bool"));
    assert!(
        Unifier::unify(&functor_shape, &int_arrow).is_none(),
        "Int~>Bool must NOT unify with F<A>~>F<B> (Int is not an App)"
    );
    println!("[pass] Int~>Bool does NOT unify with F<A>~>F<B>");

    // (c) Positive (non-List constructor): Tree<a> ~> Tree<b> unifies with
    // F<A> ~> F<B> with F := Tree. This shows the HKT filter is generic, not
    // pinned to List. (A full graph-based test would require Tree-typed base
    // arrows in the signature; here we exercise the type-filter unification
    // directly, which is the layer the Ty::App addition targets.)
    let tree_arrow = arr_t(app_t(atom("Tree"), tv("a")), app_t(atom("Tree"), tv("b")));
    let u_tree = Unifier::unify(&functor_shape, &tree_arrow)
        .expect("Tree<a>~>Tree<b> must unify with F<A>~>F<B>");
    let f_tree = u_tree.get("F").expect("F bound for Tree<a>~>Tree<b>");
    assert!(
        matches!(f_tree, Ty::Atom(s) if s == "Tree"),
        "F := Tree for Tree<a>~>Tree<b>, got {}",
        f_tree
    );
    println!("[pass] Tree<a>~>Tree<b> unifies with F<A>~>F<B> (F := Tree)");

    // (d) End-to-end: the demo map graph's inferred type [a] ~> [b] still
    // passes Functor's HKT type filter through the store lookup (the same
    // path the pipeline's step 1 uses).
    let map_type = arr_t(gin.clone(), gout.clone());
    let map_type_matches = store.lookup_by_type_shape(&map_type);
    let map_type_names: Vec<&str> =
        map_type_matches.iter().map(|(_, e)| e.name.as_str()).collect();
    assert!(
        map_type_names.contains(&"Functor"),
        "map type [a]~>[b] still passes Functor's HKT type filter"
    );
    println!("[pass] map type [a]~>[b] passes Functor's HKT type filter (Functor in candidates)");

    print_section("All tests passed");
}
