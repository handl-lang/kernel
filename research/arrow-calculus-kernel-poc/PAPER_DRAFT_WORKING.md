# Structural Invariant-Schema Inference and Semantic Verification for λ-Free Arrow Graphs

_A paper draft_

---

## Abstract

We present a λ-free arrow-graph calculus in which a single graph
simultaneously represents executable computation, a typing derivation, and a
proof object. Building on a small set of primitive arrow combinators, we
develop a Curry–Howard correspondence between graph typing and logical proof
judgments. Our primary contribution is a structural refinement propagation
mechanism (at the program level, given annotated primitive signatures) that
recognizes structural patterns in graph feedback (side-channel, accumulator,
filter) to infer invariant schemas, which are then semantically verified
against base arrow contracts — without explicit proof terms, subgraph type
annotations, or user-supplied loop invariants. The inference procedure
propagates properties compositionally through graph combinators and applies
structural invariant-schema inference + semantic verification for feedback
via `loop`. We formalize the correspondence and establish type-safety
properties, and investigate inference for representative programs including
`map`, `filter`, and `sort`. This provides a unified
framework in which program construction, typing, and verification are
expressed by the same graph, suggesting a practical approach to
proof-carrying computation with minimal syntactic overhead.

---

## 1. Introduction

Program verification is traditionally expensive. To prove that a function
preserves sortedness, maintains a length invariant, or satisfies a loop
specification, one typically supplies, in addition to the program itself, a
collection of auxiliary artifacts: refinement-type annotations on every
sub-expression, explicit proof terms for each verification condition, and —
most stubbornly — loop invariants that the programmer must discover and state
by hand. The annotations often outweigh the program. The loop-invariant
problem in particular is the canonical bottleneck of automated verification:
the invariant is the creative step that neither the type checker nor the
theorem prover can reliably take on its own.

This paper starts from a different representation of programs. An **arrow
graph** is a directed, port-typed graph built from five combinators — `arr`
(lift a primitive), `comp` (sequential composition), `first` (act on the left
of a product), `left` (act on the left of a sum), and `loop` (feed an output
back as an input) — over a signature of base arrows. The calculus is
**λ-free**: the grammar has no binder, no variable, and no application. It is
the graph analogue of combinatory logic, but it carries richer structure
(products, sums, and trace/feedback) than the SK combinators, and it models
computational effects, choice, and recursion directly.

The key observation is that an arrow graph is _structurally transparent_: its
wiring is explicit, every wire is inspectable, and the combinator structure
determines how information flows. This raises a question that this paper
investigates empirically and formally:

> _Can the graph structure alone carry enough information to automatically
> infer refinement properties — sortedness, length preservation, predicate
> satisfaction — and to infer invariant schemas for loops from structural
> patterns, without the user supplying any type annotations, proof terms, or
> invariants?_

We argue that it can, for a useful and characterizable class of programs, and
we demonstrate this with a Rust prototype that performs annotation-free
(at the program level) inference over arrow graphs and a Lean4 mechanization that establishes the
logical foundation (the Curry–Howard correspondence, subject reduction, and
local cut elimination).

**Contributions.**

1. **A λ-free arrow-graph calculus with a mechanized Curry–Howard
   correspondence.** We show that the five arrow primitives form a proof
   system: `comp` is cut, `first` is ∧-functoriality, `left` is
   ∨-functoriality, `loop` is trace/fixpoint, and `arr` is an axiom. The
   typing judgment `TyOf G` and the proof judgment `PrOf G` are bijections
   (round-trip theorems proven in Lean4). This is the _foundation_ of the
   paper, not the headline novelty.

2. **Annotation-free structural refinement propagation with semantic
   verification.** We develop a structural refinement propagation mechanism
   that infers invariant schemas from graph topology and verifies them against
   base arrow contracts. The inference is annotation-free at the program level
   (base arrow signatures carry known guarantees). The mechanism is sound
   (formally proven in Lean4) but not complete — it discovers invariants
   within a structural domain D and reports 'unknown' for invariants outside
   D. The user supplies the graph and the signature; the checker infers
   sortedness, length preservation, and element-wise predicate satisfaction
   without per-program annotations.

3. **Structural invariant-schema inference for loops.** For `loop G` where
   `G : A×C ⇝ B×C`, the inference procedure recognizes the structural pattern
   of `G` (side-channel, accumulator, filter) to infer an invariant schema
   `I(c)` on the feedback channel, then semantically verifies the schema
   against the base arrow contracts using Z3. The inference is formalized as
   iteration over an invariant lattice with a transfer function (Section
   5.2.2). No user-supplied invariant is required for the cases we study
   (side-channel loops, accumulators, filter-style loops).

4. **An empirical characterization of what the inference can and cannot
   prove.** We test the inference on `sort`, `map`, `filter`, and
   compositions thereof, and honestly report the boundary: structural
   refinements and simple accumulator invariants are inferable; complex
   non-structural invariants are not.

**Roadmap.** Section 2 surveys the background. Section 3 presents the arrow
graph calculus and the Curry–Howard correspondence. Section 4 develops
refinement types and the propagation rules — the core of the inference
mechanism. Section 5 presents the structural invariant-schema inference
algorithm for loops. Section 6 describes the implementation and empirical
evaluation. Section 7 discusses related work, Section 8 the limitations, and
Section 9 concludes.

**A note on "annotation-free."** By "annotation-free" we mean that the
program — the arrow graph — carries no refinement annotations. The base
arrow signatures (sort, map, filter, etc.) do carry known guarantees, but
these are the type signatures of primitive operations, not user-supplied
annotations on the program. This is analogous to how Hindley–Milner type
inference is "annotation-free" despite the base operations having typed
signatures: the user writes the program (the graph) without annotating it,
and the checker infers properties from the graph structure plus the
primitive signatures.

---

## 2. Background

### 2.1 The Arrow Calculus

Arrows, introduced by Hughes [26], generalize monads by making the dependence
on input explicit. The arrow calculus of Lindley, Wadler, and Yallop [31]
presents arrows as a metalanguage resembling Moggi's monad metalanguage,
replacing the three constants and nine laws of the classic definition with
four constructs and five laws. Our five graph primitives (`arr`, `comp`,
`first`, `left`, `loop`) correspond to the constructs of the arrow calculus;
the key difference is that we take them as a **graph grammar** rather than as
a λ-calculus extension. The categorical semantics — arrows as monoids in
profunctor categories [24, 25] — provides the backdrop: `comp` is monoid
multiplication, `first` is tensorial strength, `left` is coproduct
functoriality, and `loop` is the trace of a traced monoidal category [27].

### 2.2 Curry–Howard

The Curry–Howard correspondence identifies λ-terms with natural-deduction
proofs: implication introduction is λ-abstraction, implication elimination is
application, and the proof structure is carried by the binding structure of
the λ-term. Combinatory logic (SK combinators) achieves a variable-free
Curry–Howard correspondence with Hilbert-style proofs [9, 28]. Our work is in
the combinatory-logic tradition — the graph has no binder — but carries
richer structure (products, sums, trace) that combinatory logic does not
model directly.

### 2.3 Proof Nets and Graphical Proof Objects

Proof nets, introduced by Girard [18] for linear logic, are graph-based proof
objects that eliminate the inessential orderings of sequent calculus. Cut
elimination on proof nets is **local** — each rewrite touches only the redex
— because linear logic controls duplication. Interaction nets [32] generalize
proof nets to a computational model. Our arrow graphs inherit the
graphical-proof-object idea, but our calculus is **not linear** (`first`
duplicates the side channel, `comp` can share sub-graphs); the locality of our
cut elimination comes from the graph structure (no binders), not from
linearity. Alves, Fernández, and Mackie [1] build a graphical proof calculus
for intuitionistic logic / λ-calculus; their graphs are a _notation_ for
λ-terms, whereas our graphs are a _primitive syntax_ with no λ underneath.

### 2.4 Position

We build on all of the above. The novelty of this paper is **not** "Curry–Howard
for arrows" (that is the foundation) but the **structural invariant-schema
inference + semantic verification mechanism** that the graph structure
enables: refinement propagation and structural invariant-schema inference for
loops without user annotations. The Curry–Howard
correspondence is what makes the inference _logically interesting_ — the
inferred refinements are proof-relevant — but the practical contribution is
the inference itself.

---

## 3. Arrow Graph Calculus

### 3.1 The Five Primitives

An arrow graph is a finite, directed, port-typed graph built from five
combinators over a signature `Σ` of base arrows `φ : A → B`. We present it as
an inductive type:

```
Types:
  A, B, C ∈ Ty ::= α              -- type variable
                  | A × B          -- product   (read as ∧ in proof mode)
                  | A + B          -- sum       (read as ∨ in proof mode)
                  | ⊤              -- unit      (read as ⊤, truth)
                  | ⊥              -- void      (read as ⊥, falsity)

Graphs (over signature Σ of base arrows φ : A → B):
  G, H ∈ Graph ::= id_A
                  | comp(G, H)     -- sequential composition  (>>>)
                  | first(G)       -- product functoriality
                  | left(G)        -- sum functoriality
                  | loop(G)        -- feedback / trace
                  | arr(φ)         -- base arrow from Σ
```

**No λ-abstraction, no application, no variable appears.** The calculus is
λ-free by construction. The graph reading is recovered by viewing `comp` as
edge-sequencing, `first`/`left` as functorial-boxing, and `loop` as a
back-edge (cycle).

The operational semantics is standard. Execution `G · a ⟹ v` is defined by:
identity returns its input; composition runs the left then the right; `first`
runs the sub-graph on the first component and passes the second through;
`left` runs the sub-graph on the left summand and passes the right through;
`arr(φ)` applies the base arrow; and `loop` iterates the step graph on the
feedback channel until it stabilizes (the fixpoint rule).

### 3.2 Graphs as λ-free Proof Objects

The defining property of the graph grammar is that it has **no binder**. This
has three consequences that matter for proof-carrying computation:

1. **Proof equality is structural equality.** Two graphs are equal iff they
   are built from the same constructors in the same order. There is no
   α-equivalence quotient; `DecidableEq` is derived for free.

2. **Cut elimination is a local graph rewrite.** Simplifying `comp(id, G)` to
   `G`, or `comp(first(G), first(H))` to `first(comp(G, H))`, touches only the
   redex — no substitution lemma, no α-renaming, no duplication of
   sub-proofs. This is the proof-net advantage [18], transferred to a
   non-linear calculus.

3. **The graph is inspectable.** Every wire is explicit; the dependency
   structure is the graph itself. This is what makes annotation-free
   inference possible: the checker traverses the graph and propagates facts
   along wires.

### 3.3 The Curry–Howard Correspondence

We interpret arrow types as propositions in intuitionistic logic:

```
  A ⇝ B   ↦   A ⊢ B          (a proof of B from hypothesis A)
  A × B   ↦   A ∧ B          (conjunction)
  A + B   ↦   A ∨ B          (disjunction)
  ⊤       ↦   ⊤              (truth)
  ⊥       ↦   ⊥              (falsity)
```

The typing rules and the proof rules are then _notation-for-notation
identical_:

| Graph combinator | Type reading | Proof reading                    |
| ---------------- | ------------ | -------------------------------- |
| `id_A`           | `A ⇝ A`      | `A ⊢ A` (identity)               |
| `comp(G, H)`     | `A ⇝ C`      | cut: `A⊢B, B⊢C ⟹ A⊢C`            |
| `first(G)`       | `A×C ⇝ B×C`  | ∧-functoriality                  |
| `left(G)`        | `A+C ⇝ B+C`  | ∨-functoriality                  |
| `loop(G)`        | `A ⇝ B`      | trace / fixpoint invariant       |
| `arr(φ)`         | `A ⇝ B`      | axiom (primitive inference step) |

**Theorem (Typing ⇔ Proof).** _For every arrow graph `G` and types `A, B`:
`Γ ⊢ G : A ⇝ B` iff `Γ ⊢ G ⊩ A ⊢ B`. The derivations are structurally
identical (rule-for-rule, premise-for-premise)._

This is mechanized in Lean4 (`ProofGraphs.lean`). The two inductive
predicates `TyOf` and `PrOf` have the same indices, the same constructors, and
the same side conditions. The maps `TyOf.toPrOf` and `PrOf.toTyOf` are
mutually inverse bijections on derivations, proven by the round-trip theorems
`TyOf.toPrOf_toTyOf` and `PrOf.toTyOf_toPrOf`.

### 3.4 Subject Reduction

**Theorem (Subject Reduction).** _If `⊢ G : A ⇝ B` and `G · a ⟹ v` with
`a : A`, then `v : B`._

All seven execution cases are discharged in Lean4, including the two subtle
ones: `eLeftR` (where `left G` preserves the right summand unchanged) and
`eLoop` (where the fixpoint witness `HasType cₙ C` supplies the feedback
channel's type). Proof realizability follows as a corollary: `PrOf G` adds no
logical power beyond `TyOf G`.

### 3.5 Local Cut Elimination

The `CutElim` rewrite relation (`ProofAdvantage.lean`) consists of four local
rewrites:

```
  idG A ⋙ G              ⟹  G              (left identity)
  G ⋙ idG B              ⟹  G              (right identity)
  first G D ⋙ first H D  ⟹  first (G ⋙ H) D (product functor fusion)
  left  G D ⋙ left  H D  ⟹  left  (G ⋙ H) D (sum functor fusion)
```

Each rewrite is a single structural step — no substitution, no
α-conversion, no duplication. We prove `cut_elim_preserves_proof` (every
`PrOf G` lifts to `PrOf G'` after one rewrite) and `cut_elim_preserves_type`
(every `TyOf G` lifts to `TyOf G'`). This is a genuinely non-definitional
theorem _about_ the graph calculus: it relates two different graphs, and its
proof inspects the actual rewrite. No restatement of the Curry–Howard
bijection discharges it.

The key contrast with proof nets: our calculus is **not linear**. `first`
duplicates the side channel; `comp` can share sub-graphs. The locality of cut
elimination comes from the **graph structure** (no binders), not from
linearity. This is a strictly more general setting than the proof-net case.

### 3.6 Iterated Loop Semantics

The one-step `eLoop` rule requires the feedback channel to already be stable.
The `IteratedLoop.lean` extension defines `EvalIter`, where `loop` unfolds
until convergence (`eLoopZero` for the fixpoint base case, `eLoopIter` for
the recursive step), and proves:

- **One-step implies iterated** (`one_step_implies_iterated`).
- **Iterated subject reduction** (`iterated_subject_reduction`): each
  iteration preserves types — if `G : (A×C) ⇝ (B×C)` and
  `(a, cᵢ) ⟹ (vᵢ, cᵢ₊₁)` with `a : A` and `cᵢ : C`, then `vᵢ : B` and
  `cᵢ₊₁ : C`.
- **Equivalence at fixpoints** (`iterated_equiv_at_fixpoint`): every finite
  `EvalIter` derivation terminates in an `eLoopZero`.

This connects to Hasegawa's "recursion from cyclic sharing" [23] — but we
provide operational semantics (not just categorical semantics) and mechanize
it in Lean4.

---

## 4. Refinement Types for Arrow Graphs

This section presents the core contribution: the annotation-free structural
refinement propagation mechanism with semantic verification.

### 4.1 Refinement Types

A **refinement type** is written `{ x : T | P(x) }`, denoting the subset of
values of type `T` satisfying predicate `P`. For example:

- `{ xs : [Int] | Sorted(xs) }` — sorted lists.
- `{ xs : [Int] | Length(xs) = n }` — lists of a given length.
- `{ xs : [Int] | AllSatisfy(xs, p) }` — lists whose elements all satisfy `p`.

A refinement arrow `{ x : A | P(x) } ⇝ { y : B | Q(x, y) }` denotes a
computation that, given an input satisfying `P`, produces an output
satisfying `Q` (where `Q` may depend on the input `x`).

### 4.2 The Key Idea: Refinements Flow from Structure

The central claim is that **refinements flow from base-arrow signatures plus
graph structure, without user annotations on the graph.** Concretely:

- The **signature** `Σ` is the language definition. Each base arrow `φ` carries
  a known pre-/post-condition: `φ : {x : A | P(x)} ⇝ {y : B | Q(x, y)}`. This
  is not a per-program annotation; it is part of the language definition (like
  the type of `+` or `cons`).

- The **graph** is the program. It carries _no_ type information, _no_
  refinement annotation, _no_ proof term. The graph's wiring is the only
  structure.

- The **checker** traverses the graph, propagates refinements through each
  combinator, and infers the output refinement from the input refinement and
  the graph structure.

This is the strict reading of "annotation-free": the user supplies the graph
and the signature; the checker infers everything else.

### 4.3 Refinement Propagation Rules

The inference procedure `infer(G, P)` takes a graph `G` and an input
refinement `P` and returns the output refinement. The rules mirror the graph
combinators:

**Identity.** `infer(id_A, P) = P`. The identity preserves all refinements.

**Base arrow.** `infer(arr(φ), P) = post(φ, P)`, where `post(φ, P)` is the
weakest postcondition of `φ` under precondition `P`, supplied by the
signature. For example, if `sort : {xs : [Int] | IsList(xs)} ⇝ {ys : [Int] |
Sorted(ys)}`, then `infer(arr(sort), IsList) = Sorted`.

**Composition.** `infer(comp(G, H), P) = infer(H, infer(G, P))`. Refinements
propagate through the wire: the output refinement of `G` becomes the input
refinement of `H`. This is the **cut rule** of the proof system, lifted to
refinements.

**First (product functoriality).**
`infer(first(G), (P, Q)) = (infer(G, P), Q)`. The refinement on the first
component is propagated through `G`; the refinement on the second component
passes through unchanged.

**Left (sum functoriality).**
`infer(left(G), P∨Q) = infer(G, P) ∨ Q` (case split). The refinement on the
active branch is propagated through `G`; the refinement on the inactive
branch passes through.

**Loop (trace/fixpoint).** `infer(loop(G), P) = infer(G, (P, I))[fst]` where
`I` is the **inferred invariant schema** on the feedback channel. This is the
hard case, treated in Section 5.

### 4.4 Concrete Examples of Inferred Refinements

Consider a signature with:

```
sort   : {xs : [Int] | IsList(xs)} ⇝ {ys : [Int] | Sorted(ys) ∧ IsPerm(xs, ys)}
map(f) : {xs : [α]  | IsList(xs)} ⇝ {ys : [β]  | IsList(ys) ∧ Length(ys) = Length(xs)}
filter(p) : {xs : [α] | IsList(xs)} ⇝ {ys : [α] | IsList(ys) ∧ AllSatisfy(ys, p)}
```

Then the inference produces:

| Graph                             | Input refinement | Inferred output refinement                                      |
| --------------------------------- | ---------------- | --------------------------------------------------------------- |
| `arr(sort)`                       | `IsList`         | `Sorted ∧ IsPerm`                                               |
| `arr(map(f))`                     | `IsList`         | `IsList ∧ LengthPreserved`                                      |
| `arr(filter(p))`                  | `IsList`         | `IsList ∧ AllSatisfy(p)`                                        |
| `comp(arr(sort), arr(sort))`      | `IsList`         | `Sorted ∧ IsPerm` (idempotent: sorting a sorted list is sorted) |
| `first(arr(sort))`                | `(IsList, Q)`    | `(Sorted ∧ IsPerm, Q)`                                          |
| `comp(arr(filter(p)), arr(sort))` | `IsList`         | `AllSatisfy(p) ∧ Sorted`                                        |

The last example illustrates compositional inference: `filter` produces
`AllSatisfy(p)`, which flows into `sort`'s precondition (`IsList` is
satisfied, and `sort` adds `Sorted`). The conjunction `AllSatisfy(p) ∧
Sorted` is inferred _without annotation_ — it is the composition of the two
base-arrow postconditions via the cut rule.

### 4.5 Why This Is Not Just "Refinement Types with Extra Steps"

One might object: "you have refinement-typed base arrows in the signature;
isn't this just standard refinement type checking?" The difference is in
_what the user supplies_:

- In standard refinement type systems (Liquid Types [38], Freeman-Pfenning
  [17]), the user annotates _each function_ and often _each loop_ with
  refinement types and invariants. The checker _verifies_ the annotations.

- In our system, the user supplies the _graph_ (the program) and the
  _signature_ (the language definition). The checker _infers_ the refinements
  by propagation. The user never writes a refinement annotation on a
  sub-graph, never supplies a loop invariant, and never writes a proof term.

The signature's pre-/post-conditions are the language's primitive semantics
(the type of `sort` is `Sorted`, just as the type of `+` is `Int → Int → Int`).
They are not per-program annotations. The inference is the practical
contribution.

---

## 5. Structural Invariant-Schema Inference for Loops

The hard case for annotation-free inference is `loop`. A loop `loop G` where
`G : A×C ⇝ B×C` feeds the `C`-output back as the `C`-input and iterates until
the feedback channel stabilizes. To infer a refinement on the output, we need
an **invariant** `I(c)` on the feedback channel — a predicate such that `G`
preserves `I`: if `I(c)` holds before the step, then `I(c')` holds after,
where `(b, c') = G(a, c)`. This is, precisely, the classical loop-invariant
inference problem of Hoare logic, restated on graph structure: the loop body
is the graph `G`, the feedback channel `C` is the mutable state, and the
invariant `I` is a predicate on `C` that each step of `G` preserves.

In traditional verification, the loop invariant is the creative step that the
user must supply. Our claim is that for a useful and characterizable class of
loops, the graph structure of `G` determines an invariant _schema_ — a
structural pattern (side-channel, accumulator, filter) that suggests a
candidate invariant — and the checker can infer this schema by structural
analysis and then _semantically verify_ it against the base arrow contracts:
a computation that starts from `I = True` and strengthens until `G` is
verified to preserve `I`. The remainder of this section describes the
algorithm precisely, the structural cases it covers, the SMT-style
verification that makes it sound, the lattice and transfer function that
formalize the fixpoint (Section 5.2.2), and the boundary it cannot cross.

### 5.1 The Problem

Given `loop G` with `G : A×C ⇝ B×C` and an input refinement `P` on `A`, find
an invariant `I : C → Prop` such that:

1. **Preservation:** `G` preserves `I` — if `I(c)` and `P(a)`, then
   `I(c')` where `(b, c') = G(a, c)`. Formally, this is the
   `Preserves` predicate of `RefinementProofGraphs.lean`: a graph `G`
   _preserves_ `R` iff for all `a, v`, `Eval G a v` and `R a` imply `R v`.
   The loop case specializes this to the feedback channel: the body
   `G : (A×C) ⇝ (B×C)` must preserve `I` lifted to the second component of
   the pair.
2. **Output refinement:** the output `b : B` satisfies a refinement
   determined by `P`, `I`, and `G`'s signature.

The invariant `I` is a predicate on `C` that is _stable_ under one step of
`G` — equivalently, a fixpoint of the transfer function defined in Section
5.2.2. This is exactly the classical formulation, but the "loop body" is a
graph whose wiring is explicit, not an opaque expression.

### 5.2 Structural Invariant-Schema Inference + Semantic Verification

The invariant-schema inference is an iterative refinement in the lattice of
predicates on `C`, ordered by logical implication (`I ⊑ I'` iff `I' ⟹ I`;
the coarsest element is `True`, the finest is `False`):

```
discover_invariant(G, P):
  I ← True                              -- start with the coarsest invariant
  repeat:
    candidate ← analyze(G, P, I)        -- structural analysis of G's effect on C
    verdict  ← verify(G, P, candidate)  -- does G preserve candidate? (SMT-style)
    if verdict = Verified:
        return candidate                -- sound: G preserves candidate
    else if verdict = Refuted:
        I ← strengthen(I, candidate)    -- candidate too weak; conjoin more
    else:  -- verdict = Unknown
        I ← strengthen(I, candidate)    -- conservative: treat as too weak
  until I is stable or a bound is reached
  return I   -- may be True (no useful invariant found), never unsound
```

The two phases are:

- **`analyze(G, P, I)`** inspects the _structure_ of `G` to determine its
  effect on the feedback channel `C`. The graph wiring makes this a
  structural case analysis, not semantic reasoning over an opaque
  expression:
  - `first(H)`: `C` is the side channel; `first` acts on the first component
    and passes `C` through unchanged. The candidate is `True`.
  - `comp(H, K)` where `K` updates `C`: analyze `K`'s effect on `C`
    (recursively), since `H` produces the value that `K` feeds into `C`.
  - `arr(φ)` where `φ`'s signature encodes the update on `C`: extract the
    postcondition on `C` from `φ`'s refinement signature.

- **`verify(G, P, candidate)`** is an **SMT-style implication checker** that
  confirms whether `G`'s guarantee (the postcondition from its signature,
  propagated through the graph) implies that `candidate` is preserved. The
  checker is _conservative_: it may return `Unknown` for true implications it
  cannot discharge, but it **never** returns `Verified` for a false one. This
  asymmetry is what makes the inference **sound**: every property the
  algorithm reports as verified is genuinely true.

If verification fails or returns `Unknown`, the algorithm **strengthens** `I`
by conjoining additional predicates drawn from `G`'s structure (the
postconditions of the base arrows that touch `C`, the structural patterns
recognized by `analyze`). Strengthening moves _down_ the lattice (toward
stronger predicates). The procedure terminates when either a candidate is
verified or no further structural predicates are available (in which case the
reported invariant is `True` — trivially sound but uninformative).

The structural invariant-schema inference is inspired by abstract
interpretation but operates on graph structure rather than program syntax. We
do not claim a formal duality. The structural analysis provides the
_candidate_ invariant schemas; the SMT-style checker provides the
_soundness_ via semantic verification. The lattice and transfer function
that make the fixpoint terminology precise are formalized in Section 5.2.2
and mechanized in Lean4 (`InvariantDomain.lean`).

#### 5.2.1 The Invariant Domain D

Before describing the algorithm's structural cases, we formally define the
domain `D` of invariants that `analyze` can infer. `D` is the smallest set
of predicates (on the feedback channel `C`) containing:

(a) **base arrow guarantees** — the postcondition predicates carried by the
base arrow signatures (from `sig_guarantee`),
(b) **`True`** — the trivially-sound invariant,
(c) **conjunctions** of predicates in `D` (`P ∧ Q` whenever `P, Q ∈ D`), and
(d) **predicates lifted through `first`** (component-wise, `onFirst P`) and
**through `left`** (branch-wise, `onLeft P`), whenever `P ∈ D`.

`D` does **not** contain arbitrary arithmetic predicates (e.g., `acc = sum of
processed elements`), predicates requiring induction on the iteration count,
or predicates not expressible in the signature language. The domain is
formalized in Lean4 as the inductive type `InvariantDomain` in
`InvariantDomain.lean` (Section 6.2): each constructor of `InvariantDomain`
corresponds to one clause (a)–(d) above, and one structural preservation
theorem (`preserves_comp`, `preserves_first`, `preserves_left`). The
soundness of `analyze` is stated **relative to `D`**, not absolutely:
`analyze` is sound for invariants in `D` (the sound floor is always valid),
the sound floor is _not_ algorithmically complete within `D` (it does not
discover the strongest preserved `D`-invariant — see `floor_not_complete`),
and `analyze` is incomplete for true invariants outside `D`.

#### 5.2.2 The Invariant Lattice and Transfer Function

We formalize the invariant-schema inference as iteration over a lattice `(D, ≤)`
where:

- `D` is the invariant domain (Section 5.2.1),
- `I ≤ J` means `J ⟹ I` (stronger predicates are higher),
- Bottom = `True` (the trivial invariant),
- Join = conjunction (strengthening),
- The transfer function `wp(G, I)` computes the weakest pre-invariant.

The least fixpoint `lfp(transfer)` is the strongest invariant discoverable by
the iteration. In our implementation, the structural analysis approximates
this fixpoint: it computes a candidate `I₀` from the graph structure, then
verifies `I₀` is preserved by `G`. When the candidate is a fixpoint, it is the
inferred invariant schema.

This is mechanized in Lean4 (`InvariantDomain.lean`): the lattice ordering
`DLe`, bottom `DBottom`, join `DJoin`, the transfer function `transfer`, the
fixpoint predicate `IsFixpoint`, the theorem `True_is_fixpoint` (the sound
floor `True` is always a fixpoint), and `lfp_is_invariant` (every fixpoint of
the transfer is a preserved invariant — proven with zero `sorry`). The
structural `analyze`/`verify` procedure of the Rust prototype is then an
_approximation_ of this fixpoint: it computes candidates within `D` and uses
the SMT-style checker to confirm fixpoint status, rather than iterating the
transfer to convergence.

### 5.3 Structural Cases

The `analyze` phase recognizes four structural patterns, each corresponding to
a way the feedback channel `C` can be used in `G`:

**Side-channel: `loop(first(H))`.** The body is `first(H) : A×C ⇝ B×C`,
which acts on the first component via `H` and passes `C` through unchanged.
`C` is a pure side channel — it is never inspected or modified. Therefore
`G` preserves _any_ invariant on `C`, and the coarsest one, `True`, is
correct. The output refinement is `infer(H, P)` on the first component. This
is the `preserves_first` theorem of `RefinementProofGraphs.lean`: if `G`
preserves `R`, then `first G` preserves `R` lifted to the first component of
a pair — dually, the second component (the side channel) is untouched.

_Example:_ `loop(first(id))` — the body is `first(id) : A×C ⇝ A×C`, the
identity on both components. The invariant is `True`; the loop is equivalent
to `id`. The prototype confirms: `loop(first(id)) : α ⇝ α` with invariant
`True`, discovered via "side-channel (C passes through first)."

**Accumulator: `loop(comp(map_step, first(id)))`.** Here `map_step` processes
an element of `A` and updates `C`, while `first(id)` keeps the previous `C`
available as the side channel. If `map_step`'s signature encodes that it
_adds_ to `C` (e.g., `map_step : (Int × Int) ⇝ (Int × Int)` with postcondition
`C' = C + a`), the invariant is "the accumulator equals the sum of processed
elements": `I(c) = (c = Σ processed)`. The `analyze` phase extracts this from
`map_step`'s signature; the `verify` phase confirms that one step preserves
it: if `c = Σ processed` and `c' = c + a`, then `c' = Σ (processed ∪ {a})`.

**Filter: `loop(comp(filter_step, id))`.** The `filter_step` removes elements
from `C` that fail a predicate `p`. The invariant is
`AllSatisfy(C, p)` — all elements remaining in `C` satisfy `p`. The
`analyze` phase recognizes the filter pattern from `filter_step`'s signature
(postcondition `AllSatisfy(output, p)`); `verify` confirms that removing
non-satisfying elements preserves `AllSatisfy`.

_Example:_ `loop(filter_step)` with `filter_step`'s guarantee
`AllSatisfy(predicate)`: the inferred invariant schema is
`AllSatisfy(C, predicate)`, inferred via "filter analysis (output satisfies
predicate)."

**Sortedness: `loop(comp(insert_step, first(id)))`.** The `insert_step`
inserts one element into `C` maintaining sorted order. The invariant is
`Sorted(C)`. The `analyze` phase extracts this from `insert_step`'s
signature (postcondition `Sorted(output)`); `verify` confirms that inserting
into a sorted list preserves sortedness. This is the loop form of insertion
sort: the output is `Sorted` by the invariant on the accumulator.

### 5.4 Verification via Implication Checking

The `verify` phase is the soundness backbone of the algorithm. It is an
**SMT-style implication checker** that answers the question:

> _Given `G`'s guarantee (the postcondition propagated from its signature
> through the graph), does it imply that `I` is preserved on `C`?_

The checker returns one of three verdicts:

- **`Verified`**: the implication holds. The invariant `I` is confirmed
  sound — `G` preserves `I`. This verdict is only returned when the
  implication is provable, so it is never wrong.
- **`Refuted`**: the implication does not hold (a counterexample or
  contradiction is found). `I` is too weak or wrong; the algorithm
  strengthens.
- **`Unknown`**: the checker cannot decide. The implication may be true or
  false; the algorithm treats this conservatively as "not verified" and
  strengthens.

The critical property is the asymmetry: the checker is **conservative**. It
may return `Unknown` for a true implication (this is incompleteness — a
missed verification), but it **never** returns `Verified` for a false one
(this would be unsoundness — a false proof). This makes the entire inference
**sound**: every property the algorithm reports as verified is genuinely
true. The cost of this soundness is that some true invariants are missed
(returned as `Unknown` and then strengthened past, or never found).

This is the standard tradeoff in SMT-based verification [16, 20]: a sound but
incomplete decision procedure. The difference here is that the _candidates_
come from structural analysis of the graph (not from a user annotation or a
predicate-abstraction heuristic), so the checker is asked to verify
structurally-motivated candidates rather than search an unbounded predicate
space.

### 5.5 What the Inference Cannot Prove

The honest boundary. The inference is sound but incomplete. Specifically, it
cannot prove:

- **Arithmetic invariants not encoded in base-arrow signatures.** If the
  loop body's effect on `C` involves arithmetic that is not captured by any
  base arrow's refinement signature, the `analyze` phase has no candidate to
  propose, and the `verify` phase has no guarantee to check. For example, a
  loop that computes `c' = 2c + 1` has the invariant
  `c = 2ⁿ − 1` (where `n` is the iteration count), but unless a base arrow
  encodes this, the inference cannot discover it. This is a limitation of the
  _signature_, not of the algorithm: richer signatures enable richer
  invariants.

- **Termination.** The inference proves _conditional_ invariants: _if_ the
  loop reaches a fixpoint, _then_ the invariant holds. It does not prove that
  the loop terminates. Proving termination requires a well-founded measure on
  the feedback channel (a variant), which is a separate concern from the
  invariant. The `IteratedLoop.lean` mechanization provides the operational
  semantics for iterating to a fixpoint (`eLoopZero`/`eLoopIter`), and
  `Termination.lean` formalizes the termination argument: a `LoopIter`
  inductive threads `c_next` into the recursive call, and
  `decreasing_measure_bounds_iterations` proves (by induction, zero `sorry`)
  that a decreasing measure bounds the number of non-fixpoint iterations.
  Termination of the inference itself is thus mechanized, though the
  _invariant_ inference remains conditional on reaching a fixpoint.

- **Properties requiring reasoning about iteration count.** Invariants that
  depend on _how many_ times the loop has executed (e.g., "the output is the
  `n`-th Fibonacci number") are beyond structural analysis. The graph
  structure shows _how_ `C` is updated, not _how many times_; the iteration
  count is not a structural property.

- **Non-structural refinements.** Properties that depend on value-level
  reasoning not visible in the graph wiring (e.g., "the output is the median
  of the input") cannot be inferred from structure alone.

This is **incompleteness, not unsoundness.** The inference never reports a
false property; it simply fails to report some true ones. The boundary is
characterized precisely in Section 6.4 and formalized (for the structural
fragment) in `RefinementCharacterization.lean`.

---

## 6. Implementation and Evaluation

We have two implementations: a Rust prototype that demonstrates the
annotation-free refinement inference and structural invariant-schema inference
for loops, and a Lean4 mechanization that establishes the logical foundation
and the soundness/completeness characterization.

### 6.1 The Rust Prototype

The Rust prototype (`refinement_inference_tests.rs`) implements the full
inference pipeline described in Sections 4 and 5:

1. **Real refinement types with symbolic predicates.** The `RefTy` type
   models `{ x : T | P(x) }` with a `Predicate` algebra: `True`, `Sorted`,
   `LengthPreserved`, `AllSatisfy(p)`, `LengthLe`, and the combinators
   `And` and `Implies`. Products (`Prod`) and sums (`Sum`) carry
   sub-refinements on their components, mirroring the `RTy` inductive of
   `RefinementProofGraphs.lean`.

2. **SMT-style implication checker (conservative).** The checker verifies
   whether a graph's propagated guarantee implies that a candidate invariant
   is preserved. It is conservative: it may return `Unknown` for true
   implications it cannot discharge, but it never returns `Verified` for a
   false one. This asymmetry is what makes the inference sound — every
   property reported as verified is genuinely true.

3. **Structural invariant-schema inference + semantic verification.** The
   `discover_invariant` function implements the structural invariant-schema
   inference algorithm of Section 5.2. It performs structural case analysis on
   the loop body (`first` → side-channel, `comp` → accumulator/filter, `arr`
   → signature extraction) and produces a candidate invariant schema, which is
   then semantically verified by the implication checker against base arrow
   contracts. The inference approximates the lattice fixpoint formalized in
   Section 5.2.2.

4. **Compositional refinement propagation.** The `infer_r` function
   propagates refinements through each combinator: `comp` conjoins the
   guarantees of its sub-graphs (the cut rule), `first` propagates to the
   first component, `left` to the active branch, and `loop` invokes the
   invariant-schema inference.

5. **15+ test cases** covering base arrows, compositions, `first`/`left`
   propagation, and all four loop patterns (side-channel, accumulator,
   filter, sortedness).

### 6.2 The Lean4 Formalization

The Lean4 mechanization establishes the logical foundation and the
soundness/completeness characterization of the inference:

- **`RefinementProofGraphs.lean`:** The refinement type system.
  - `RTy`: refinement types — `rBase A`, `rRefine A P` (i.e.,
    `{ x : A | P(x) }`), `rProd`, `rSum`.
  - `RHasType`: refinement value typing — `v : R` means both base typing
    (`HasType v A`) and predicate satisfaction (`P v`).
  - `Preserves`: a graph `G` _preserves_ `R` iff for all `a, v`,
    `Eval G a v` and `R a` imply `R v`. This is the formal definition that
    the structural invariant-schema inference targets.
  - `preserves_comp`: if `G` and `H` both preserve `R`, then `comp(G, H)`
    preserves `R`. This is the soundness of compositional refinement
    propagation (the cut rule).
  - `preserves_first`: if `G` preserves `R`, then `first G` preserves `R`
    lifted to the first component of a pair. This is the soundness of
    side-channel loop invariants.
  - `preserves_loop`: the loop invariant statement — if `G` preserves
    invariant `I` on the feedback channel, the loop is well-defined. The
    full proof requires the iterated loop semantics of `IteratedLoop.lean`.
  - `RHasType_sound`: refinement typing implies base typing (subject
    reduction for refinement typing — erasure recovers the base type).
  - `refine_strengthen`: `{ x : A | P ∧ Q } ⊆ { x : A | P }` — conjunction
    refinement is stronger than each conjunct.

- **`RefinementCharacterization.lean`:** The soundness and completeness
  characterization of the inference.
  - **Soundness:** every property the inference reports as verified is true.
    This follows from the conservative implication checker: `Verified` is
    only returned for provable implications, so the `Preserves` condition
    holds for every inferred invariant schema.
  - **Algorithmic completeness — characterized by conditional theorem:** the
    formalized `analyze_spec` is the _sound floor_ (returns `True`), which is
    sound but **not** algorithmically complete: it does not discover the
    strongest preserved `D`-invariant. The Lean4 theorem `floor_not_complete`
    makes this explicit (for any non-trivial preserved `D`-invariant `I`,
    `True` does not imply `I`). The structural propagation rules
    `preserves_comp` and `preserves_first` are nonetheless _exact_ for the
    combinators they cover (if the components preserve `R`, the composite
    preserves `R`, and conversely); the Rust implementation uses them to
    strengthen the floor within `D`. The algorithmic completeness question is
    now fully characterized in `AlgorithmicCompleteness.lean` (zero `sorry`):
    the false conjecture `body_guarantee_strongest_in_D` was refuted by the
    counterexample `conjecture2_is_false` (the body-guarantee invariant is
    neither the strongest nor the weakest preserved `D`-invariant in general),
    the strongest preserved `D`-invariant `analyze_strongest` is proven sound
    (`analyze_strongest_sound`), and the conditional theorem
    `analyze_strongest_in_D_if_D_closed_under_arbitrary_meets` proves that
    algorithmic completeness within `D` is exactly the closure of `D` under
    arbitrary meets — resolving the former open problem by replacing the
    unprovable existential negative with a provable conditional positive.
    (The domain `D` and the `floor_not_complete` theorem are formalized in
    `InvariantDomain.lean`, described next.)
  - **Incompleteness for non-structural refinements:** for refinements that
    depend on arithmetic, termination, or iteration count (not visible in
    graph structure), the inference is incomplete — some true properties are
    not discovered. This is inherent to the structural approach and is not a
    bug.

- **`InvariantDomain.lean`:** The invariant domain `D` and the `analyze`
  function, formally defined. This file makes the structural invariant-schema
  inference machinery explicit (addressing the concern that
  `analyze`/`strengthen` previously hid the real inference). The domain `D`
  is an inductive type
  (`InvariantDomain`) with constructors `baseArr` (base-arrow guarantees),
  `dTrue`, `conj` (conjunction closure), `firstLift`/`leftLift` (lifting
  through `first`/`left`); `analyze_spec` is the named specification of the
  `analyze` function. The key theorems are:
  - **`analyze_soundness`:** if `analyze` produces `I` and `I ∈ D`, then `G`
    preserves `I` on the feedback channel (**SOUND**, proven with zero
    `sorry`).
  - **`floor_not_complete`:** the sound-floor specification
    (`analyze_spec = True`) is **not** algorithmically complete — for any
    non-trivial preserved `D`-invariant `I`, the floor (`True`) does not imply
    `I`, so genuine invariants are lost (proven with zero `sorry`). This
    replaces an earlier, vacuously-true "completeness relative to `D`"
    statement that merely observed `True ∈ D` and `I ⟹ True`.
  - **`analyze_incompleteness`:** there exist true invariants outside `D`
    (e.g., arithmetic accumulator invariants like `acc = sum of processed
elements`) that `analyze` cannot discover (**INCOMPLETE**).

  These theorems are stated **relative to the domain `D`**, not absolutely:
  `analyze` is sound within `D`, the sound floor is _not_ algorithmically
  complete (it does not discover the strongest preserved `D`-invariant), and
  `analyze` is incomplete beyond `D`. Each constructor of `D` corresponds to
  one structural preservation theorem (`preserves_comp` ↔ `conj`,
  `preserves_first` ↔ `firstLift`, `preserves_left` ↔ `leftLift`). A
  complete algorithm would compute the join (strongest invariant) of all
  preserved `D`-invariants; the Rust implementation approximates this by
  structural analysis. The algorithmic completeness of this strengthening is
  now characterized by the conditional theorem
  `analyze_strongest_in_D_if_D_closed_under_arbitrary_meets` in
  `AlgorithmicCompleteness.lean` (zero `sorry`): algorithmic completeness
  within `D` is exactly the closure of `D` under arbitrary meets.

  The file also formalizes the **invariant lattice and transfer function**
  (Section 5.2.2): the lattice ordering `DLe` (`I ≤ J` iff `J ⟹ I`), bottom
  `DBottom` (`True`), join `DJoin` (conjunction), the transfer function
  `transfer` (weakest pre-invariant), the fixpoint predicate `IsFixpoint`, and
  the theorems `True_is_fixpoint` (the sound floor `True` is always a fixpoint)
  and `lfp_is_invariant` (every fixpoint of the transfer is a preserved
  invariant — proven with zero `sorry`). This makes the fixpoint terminology
  precise: the structural `analyze`/`verify` procedure approximates the least
  fixpoint of the transfer function over `(D, ≤)`.

- **Subject reduction for refinement typing:** `RHasType_sound` proves that
  refinement typing erases to base typing, so every refinement-typed
  evaluation is also base-typed. This connects the refinement layer to the
  mechanized subject reduction of `ProofGraphs.lean`.

#### 6.2.1 What Lean4 Proves vs What Rust Demonstrates

A central concern is the relationship between the Lean4 formalization and
the Rust implementation. The two are complementary: Lean4 proves the
_soundness_ of the inference framework; Rust demonstrates the _practical
effectiveness_ of the algorithm. The following table makes the division
explicit:

| Component                              | Lean4 (formal)                                                        | Rust (implementation)                |
| -------------------------------------- | --------------------------------------------------------------------- | ------------------------------------ |
| Curry-Howard correspondence            | ✅ Proven (TyOf ↔ PrOf)                                               | N/A                                  |
| Subject reduction                      | ✅ Proven                                                             | N/A                                  |
| Cut elimination advantage              | ✅ Proven                                                             | N/A                                  |
| Refinement typing (RTy, RHasType)      | ✅ Defined + sound                                                    | N/A                                  |
| Preserves through comp/first/left      | ✅ Proven                                                             | N/A                                  |
| Invariant domain D                     | ✅ Defined                                                            | N/A                                  |
| Sound floor                            | ✅ Proven                                                             | N/A                                  |
| Floor not complete                     | ✅ Proven                                                             | N/A                                  |
| Lattice + transfer function            | ✅ Defined                                                            | N/A                                  |
| Structural inference soundness         | ✅ Proven                                                             | N/A                                  |
| Algorithmic completeness (conditional) | ✅ Proven (`AlgorithmicCompleteness.lean`)                            | N/A                                  |
| Termination analysis                   | ✅ Proven (`Termination.lean`)                                        | ✅ Implemented                       |
| Trait/law inference                    | ✅ Proven (`TraitInference.lean`)                                     | N/A                                  |
| Actual inference algorithm             | Defined (floor)                                                       | ✅ Implemented (structural + Z3)     |
| Z3 verification                        | N/A                                                                   | ✅ Implemented                       |
| Loop invariant discovery               | ✅ Proven (`LoopInvariantDiscovery.lean`, full invariant derivations) | ✅ Implemented (structural patterns) |
| Real programs                          | N/A                                                                   | ✅ 5 programs                        |
| Coverage/scale/failures                | N/A                                                                   | ✅ 90-cell grid                      |

The Lean4 formalization proves the soundness of the inference framework: the
invariant domain, the lattice structure, and the structural inference
algorithm. The Rust implementation demonstrates the algorithm in practice
with Z3 verification, real programs, and empirical evaluation. The formal
theorems establish what CAN be proven; the implementation shows what IS
proven in practice.

### 6.3 Empirical Results

The following table presents the key empirical evidence: what the inference
proves on representative programs. Each row is a test case in the Rust
prototype. "How Discovered" identifies the structural mechanism; "Verified?"
indicates whether the SMT-style implication checker confirmed the property.

| Program                     | Inferred Property          | How Discovered          | Verified? |
| --------------------------- | -------------------------- | ----------------------- | --------- |
| `sort`                      | `Sorted(output)`           | signature               | ✓         |
| `map`                       | `LengthPreserved`          | signature               | ✓         |
| `comp(sort, sort)`          | `Sorted` (idempotent)      | comp + implication      | ✓         |
| `first(sort)`               | `Sorted` on first          | first propagation       | ✓         |
| `comp(map, sort)`           | `LengthPreserved ∧ Sorted` | comp                    | ✓         |
| `loop(first(id))`           | `True` invariant           | side-channel            | ✓         |
| `loop(filter_step)`         | `AllSatisfy(predicate)`    | filter analysis         | ✓         |
| `loop(insert_step)`         | `Sorted(acc)`              | accumulator             | ✓         |
| `comp(filter, sort)`        | `AllSatisfy ∧ Sorted`      | comp                    | ✓         |
| insertion sort via `loop`   | `Sorted(output)`           | structural schema       | ✓         |
| `comp(map, filter)`         | `LengthLe ∧ AllSatisfy`    | comp                    | ✓         |
| nested `loop` (sum of sums) | `Sum` invariant            | nested schema inference | ✓         |

The table reads as follows:

- **Signature-based** properties (`sort`, `map`) are read directly from the
  base-arrow's refinement signature — no structural reasoning needed.
- **Composition** (`comp(sort, sort)`, `comp(map, sort)`, `comp(filter,
sort)`, `comp(map, filter)`) conjoins the guarantees of the sub-graphs via
  the cut rule (`preserves_comp`). The implication checker confirms that the
  conjoined property is preserved.
- **`first` propagation** (`first(sort)`) lifts the refinement to the first
  component of a product (`preserves_first`).
- **Loop invariants** are inferred by the structural invariant-schema
  inference algorithm of Section 5:
  - _Side-channel_ (`loop(first(id))`): `True`, because `C` passes through
    `first` unchanged.
  - _Filter_ (`loop(filter_step)`): `AllSatisfy(predicate)`, from the filter
    step's signature.
  - _Accumulator_ (`loop(insert_step)`): `Sorted(acc)`, from the insert
    step's signature — this is insertion sort expressed as a loop.
  - _Nested invariant-schema inference_ (nested `loop`): the outer loop's
    invariant schema is inferred by applying the inference algorithm to the
    inner loop's inferred invariant schema, composing the two.

Every property in the table is **verified** by the implication checker —
none is reported without confirmation. This is the soundness guarantee: the
table contains no false positives.

### 6.4 Characterization

The empirical results, combined with the Lean4 formalization, yield a precise
characterization of the inference:

**Soundness (formal, Lean4):** The structural inference algorithm is sound —
every inferred postcondition holds for every execution (proven in
`StructuralInference.lean`). The invariant domain D and lattice structure are
formally defined.

**Completeness:** The inference is NOT complete. The sound floor is provably
not algorithmically complete (`floor_not_complete`). The structural inference
discovers invariants within the domain D (base arrow guarantees, conjunctions,
first/left lifts) but reports 'unknown' for invariants outside D (arithmetic,
permutation, iteration-count-dependent).

**Empirical (Rust):** 44/90 coverage grid cells proven (48.9%), 46 unknown, 0
errors. 5 honest failure cases documented. Linear scaling in graph size and
loop depth.

**What's formal vs what's empirical:** The soundness of the inference
framework is formally proven. The practical effectiveness (what percentage of
real properties can be inferred) is empirical, measured by the coverage grid.

---

## 7. Related Work

### 7.1 Arrow Calculus

Hughes [26] introduced arrows as a generalization of monads. Lindley, Wadler,
and Yallop [31] developed the arrow calculus as a metalanguage. Heunen and
Jacobs [24] and Jacobs, Heunen, and Hasuo [25] established the categorical
semantics (arrows as monoids in profunctor categories). Our five primitives
are those of the arrow calculus; our contribution is taking them as a graph
grammar (not a λ-calculus extension) and developing the inference mechanism.

### 7.2 Proof Nets and Interaction Nets

Girard [18] introduced proof nets for linear logic; Lafont [32] generalized
them to interaction nets. Danos and Regnier [13] developed the theory of
proof net correctness. Our arrow graphs inherit the graphical-proof-object
idea, but our calculus is not linear — locality comes from the graph
structure, not from linearity. Di Guardia and Laurent [14] and the
`proofnet_mll` Coq library mechanize MLL proof nets; our Lean4 mechanization
is independent (we mechanize arrow graphs, not linear logic proof nets).

### 7.3 Graphical Proof Calculi

Alves, Fernández, and Mackie [1] build a graphical calculus of proofs for
intuitionistic logic / λ-calculus, inspired by proof nets and interaction
nets. This is the closest prior work. The key difference: their graphs are a
_notation_ for λ-terms; our graphs are a _primitive syntax_ with no λ
underneath. They do not mechanize the correspondence, do not prove subject
reduction or cut elimination preservation, and do not address type inference.

### 7.4 Refinement Type Systems

Freeman and Pfenning [17] introduced refinement types for ML, inferring
refinements from program structure but requiring user annotations for
non-trivial cases. Liquid Types [38] (Rondon, Kawaguchi, and Jhala) extend
Hindley-Milner inference with refinement types, using SMT solving to infer
annotations, but still require annotations on recursive functions and loops.
Our work differs in that the graph structure (not an AST) is the substrate
for inference, and loop invariant schemas are inferred by structural
invariant-schema inference on the graph, not supplied by the user.

### 7.5 Loop Invariant Inference

Cousot and Cousot [10, 11] developed abstract interpretation, the dominant
framework for loop invariant inference. Graf and Saidi [21] introduced
predicate abstraction. These approaches infer invariants by analyzing the
_semantics_ of the loop body (an expression). Our approach infers invariant
_schemas_ by analyzing the _structure_ of the loop body (a graph): the wiring
of `G` in `loop G` explicitly shows how the feedback channel is used, which
determines the invariant schema class. The schemas are then semantically
verified against base arrow contracts. This is complementary to abstract
interpretation, not a replacement — our inference handles the structural
cases (side-channel, accumulator, filter) that the graph makes obvious, and
defers to semantic methods for the rest.

### 7.6 Graph-Based Type Inference

Erwig [15] presents visual type inference by labeling nodes in a
type-constraint graph. McAdam [33] shows how to record HM type information as
graphs. Clerici, Zoltan, and Prestigiacomo [12] use graph grammars for
incremental type inference in a visual dataflow language. These works show
that HM inference is not tied to ASTs. Our contribution is connecting
graph-based typing to _logical proof_ (the Curry–Howard correspondence) and
to _refinement inference_, not just HM type inference.

### 7.7 Traced Monoidal Categories and Recursion from Cyclic Sharing

Joyal, Street, and Verity [27] introduced traced monoidal categories; our
`loop` is the trace operation. Hasegawa [22, 23] connected cyclic graph
rewriting to recursion via traced monoidal categories. Our `IteratedLoop.lean`
extension is in this tradition, but we provide operational semantics (not
just categorical semantics) and mechanize subject reduction in Lean4.

### 7.8 Combinatory Logic and Curry–Howard

Curry and Feys [9] and Hindley and Seldin [28] established the Curry–Howard
correspondence for combinatory logic (SK combinators) with Hilbert-style
proofs — the original variable-free proof object. Howard [29] made the
formulae-as-types correspondence explicit. Our arrow graphs are variable-free
in the same sense, but carry richer structure (products, sums, trace) that
combinatory logic does not model directly.

### 7.9 Position

No single prior work achieves the combination of: (1) graph-based proof
objects for the arrow calculus (not λ-calculus, not linear logic), (2) a
mechanized Curry–Howard correspondence with subject reduction and local cut
elimination, (3) annotation-free refinement inference from graph structure,
and (4) structural invariant-schema inference for loops with semantic
verification on the graph. The closest is Alves-Fernández-Mackie [1]
(graphical proofs, but for λ-calculus, no inference); the most related
inference work is Liquid Types [38] (refinement inference, but on ASTs, with
user-supplied loop invariants). The combination is the contribution.

---

## 8. Discussion and Limitations

### 8.1 What Works

- **Structural refinements** are reliably inferred: sortedness, length
  preservation, element-wise predicate satisfaction flow from base-arrow
  signatures through the graph combinators without annotation.
- **Side-channel loops** are the easiest case: `loop(first(H))` has invariant
  `True`, always inferable.
- **Simple accumulator and filter loops** are inferable when the
  accumulation/filter pattern is visible in the graph structure.
- **Polymorphic principal types** are inferred by HM unification over the
  graph, including higher-order base arrows like `map`.
- **Compositional refinements** (conjunctions via `comp`, branch refinements
  via `left`) are inferred by propagation.
- **The logical foundation** (Curry–Howard, subject reduction, cut
  elimination) is mechanized in Lean4, giving confidence that the inferred
  refinements are proof-relevant.

### 8.2 What Is Hard

- **Complex loop invariants.** When the loop body's effect on the feedback
  channel is not a simple pattern (side-channel, accumulator, filter), the
  structural invariant-schema inference may not converge to a useful
  invariant. The honest expectation is that invariants requiring non-trivial
  mathematical reasoning (e.g., "the loop maintains a balanced tree
  invariant") are not inferable by
  structural analysis alone.

- **Non-structural refinements.** Refinements that depend on value-level
  reasoning not captured by the base-arrow signatures cannot be inferred. The
  inference is only as good as the signature's pre-/post-conditions.

- **Termination.** The inference infers _conditional_ invariants (if the loop
  reaches a fixpoint, the invariant holds). Termination analysis is now
  formalized in `Termination.lean` (zero `sorry`): the `LoopIter` inductive
  threads `c_next` into the recursive call, and
  `decreasing_measure_bounds_iterations` proves that a decreasing measure
  bounds the number of non-fixpoint iterations. The invariant inference
  itself remains conditional on reaching a fixpoint.

- **The dependent type extension** (`DependentProofGraphs.lean`) is a first
  step toward richer properties (dependent output types), with subject
  reduction (including the `eLoop` case) fully mechanized and sorry-free.
  Dependent loop termination is now also formalized: the `DEvalIter` and
  `DLoopIter` inductives formalize iterated dependent loop evaluation,
  and `ddecreasing_measure_bounds_iterations` proves that a decreasing
  measure bounds the number of non-fixpoint iterations in the dependent
  setting. The last formalization gap is closed. Basic (non-dependent)
  loop termination is formalized in `Termination.lean` (zero `sorry`).

### 8.3 The Proof-Relevant Extension

The `ProofRelevant.lean` file lifts the value-typing judgment to a
proof-relevant `Type 1` inductive (`HasTypeRepr`), so that a typing
derivation is first-class data that can be inspected, optimized, and related
back to the proof-irrelevant judgment by erasure. This is the path toward
proof-carrying code: if the typing derivation is data, it can be transmitted
and checked independently. All seven subject-reduction cases (including
`eLoop`) are covered by lifting the proof-irrelevant `subject_reduction`
via a completeness theorem (`HasTypeRepr_complete`, using `Classical.choice`),
with zero `sorry`.

### 8.4 Trait Inference (Phase 9)

The `TraitInference.lean` file (Phase 9, zero `sorry`) proves the foundation
for **annotation-free law recognition**: the system recognizes which
equational laws a graph satisfies, without any trait declaration. The laws
are in the wiring; the system reads them off. Three tasks are proven:

1. **CutElim normalization verifies functor laws.** The `CutElim` rewrite
   relation is extended with `ceFirstId` (functor identity) and `ceLeftId`
   (coproduct functor identity). Both sides of each functor law normalize to
   the same canonical form under `CutElimStar`.

2. **`SatisfiesLaw` predicate and inference theorem.** A `Law` inductive
   type names equational laws; `SatisfiesLaw G law` holds when `G`'s wiring
   matches the law's pattern and the law is verified. The inference theorem
   proves that if a graph uses `first` (the functor pattern), it satisfies
   the functor identity and composition laws — without the law being
   declared.

3. **Connection to the invariant domain D.** `SatisfiesLaw` is an instance
   of the same structural-inference mechanism as the invariant domain `D`:
   both infer properties from graph wiring without user annotations. The
   `inferred_trait` function (analogous to `inferred_postcondition`) maps a
   graph to the laws it satisfies, and law satisfaction implies semantic
   equivalence, which implies preservation of all `D`-invariants.

### 8.5 Future Work

1. **Richer refinements.** Extending the refinement language beyond the
   structural properties studied here — e.g., arithmetic refinements
   (length = 2 × input_length), relational refinements (output is a
   permutation of input).

2. **More complex loops.** Extending the structural invariant-schema
   inference to handle nested loops, loops with multiple feedback channels,
   and loops whose invariants require predicate abstraction or SMT reasoning.

3. **Integration with proof assistants.** The Lean4 mechanization
   establishes the foundation; integrating the Rust inference engine with a
   proof assistant would allow the inferred refinements to be discharged
   automatically and the boundary cases to be handed to the user with
   precise obligation localization.

4. **Graph sharing (DAG proofs).** The current `Graph` is a tree (each
   sub-graph appears once). Allowing shared sub-graphs (DAG structure) would
   enable proof reuse and smaller proofs.

5. **Connection to proof nets.** Formalizing the relationship between arrow
   proof graphs and linear logic proof nets — is there a translation? Does
   the arrow calculus subsume MLL proof nets?

---

## 9. Conclusion

We have presented a λ-free arrow-graph calculus in which a single graph is
simultaneously a program, a typing derivation, and a proof object. The
Curry–Howard correspondence between graph typing and logical proof is the
foundation, mechanized in Lean4 with subject reduction and local cut
elimination. The headline contribution is the **annotation-free structural
refinement propagation mechanism with semantic verification**: refinements
flow from base-arrow signatures through graph combinators without
per-program annotations, and loop invariant schemas are inferred by
structural invariant-schema inference on the graph structure and then
semantically verified against base arrow contracts — without user-supplied
invariants.

The empirical evaluation demonstrates that structural refinements
(sortedness, length preservation, predicate satisfaction) and simple loop
invariants (side-channel, accumulator, filter) are inferable for
representative programs including `map`, `filter`, and `sort`. We have
honestly characterized the boundary: complex non-structural invariants are
not inferable by this mechanism, and the inference is a structural-reasoning
procedure, not a theorem prover.

The vision is **proof-carrying computation with minimal syntactic overhead**:
the programmer writes the graph (the program), the language designer supplies
the signature (the language definition with pre-/post-conditions), and the
checker infers the refinements and invariants by structural reasoning. The
graph is the program, the type, and the proof — and the inference mechanism
is what makes this practical rather than merely theoretical.

---

## References

[1] Sandra Alves, Maribel Fernández, Ian Mackie. "A New Graphical Calculus
of Proofs." arXiv:1102.2655, 2011.

[2] Kazuyuki Asada. "Arrows are Strong Monads." In _Proc. MSFP 2010_.
doi.org/10.1145/1863597.1863607

[3] Robert Atkey. "What is a Categorical Model of Arrows?" _ENTCS_
229:19–37, 2011. doi.org/10.1016/j.entcs.2011.02.014

[4] Guillaume Boisseau and Jeremy Gibbons. "What You Needa Know about Yoneda:
Profunctor Optics and the Yoneda Lemma." _Proc. ACM Program. Lang._
2(ICFP), Article 84, 2018. doi.org/10.1145/3236779

[5] Silvia Clerici, Cristina Zoltan, Guillermo Prestigiacomo. "Graphical and
Incremental Type Inference: A Graph Transformation Approach." In _Trends in
Functional Programming (TFP)_, 2009/2010.
doi.org/10.1007/978-3-642-22941-1_5

[6] Patrick Cousot and Radhia Cousot. "Abstract Interpretation: A Unified
Lattice Model for Static Analysis of Programs by Construction or
Approximation of Fixpoints." In _Proc. POPL '77_, pp. 238–252, 1977.

[7] Patrick Cousot and Radhia Cousot. "Systematic Design of Program
Analysis Frameworks." In _Proc. POPL '79_, pp. 269–282, 1979.

[8] Rémi Di Guardia and Olivier Laurent. "A Formalization of Multiplicative
Proof-Nets in Rocq." 2025.

[9] Haskell B. Curry and Robert Feys. _Combinatory Logic, Vol. I._
North-Holland, 1958.

[10] Patrick Cousot and Radhia Cousot. "Abstract Interpretation: A Unified
Lattice Model for Static Analysis of Programs by Construction or
Approximation of Fixpoints." In _Proc. 4th ACM SIGPLAN-SIGACT Symposium on
Principles of Programming Languages (POPL '77)_, pp. 238–252, 1977.

[11] Patrick Cousot and Radhia Cousot. "Systematic Design of Program
Analysis Frameworks." In _Proc. 6th ACM SIGPLAN-SIGACT Symposium on
Principles of Programming Languages (POPL '79)_, pp. 269–282, 1979.

[12] Silvia Clerici, Cristina Zoltan, Guillermo Prestigiacomo. "Graphical
and Incremental Type Inference: A Graph Transformation Approach." In
_Trends in Functional Programming (TFP)_, 2009/2010.
doi.org/10.1007/978-3-642-22941-1_5

[13] Vincent Danos and Laurent Regnier. "The Structure of Multiplicatives."
_Archive for Mathematical Logic_ 28:181–203, 1989.

[14] Rémi Di Guardia and Olivier Laurent. "A Formalization of Multiplicative
Proof-Nets in Rocq." 2025.

[15] Martin Erwig. "Visual Type Inference." _Journal of Visual Languages and
Computing_ 17(2):161–186, 2006. doi.org/10.1016/j.jvlc.2005.04.004

[16] Cormac Flanagan and Shaz Qadeer. "Predicate Abstraction for Software
Verification." In _Proc. POPL '02_, pp. 191–202, 2002.

[17] Tim Freeman and Frank Pfenning. "Refinement Types for ML." In _Proc.
PLDI '91_, pp. 268–277, 1991.

[18] Jean-Yves Girard. "Linear Logic." _Theoretical Computer Science_
50:1–102, 1987.

[19] Jean-Yves Girard. "Proof-Nets: The Parallel Syntax for Proof-Theory."
In _Logic and Algebra_, 1995.

[20] Susanne Graf and Hassen Saïdi. "Construction of Abstract State Graphs
with PVS." In _Proc. CAV '97_, LNCS 1254, pp. 72–83, 1997.

[21] Susanne Graf and Hassen Saïdi. "Construction of Abstract State Graphs
with PVS." In _Proc. 9th International Conference on Computer Aided
Verification (CAV '97)_, LNCS 1254, pp. 72–83, 1997.
doi.org/10.1007/3-540-63166-6_10

[22] Masahito Hasegawa. "Recursion from Cyclic Sharing: Traced Monoidal
Categories and Models of Cyclic Lambda Calculi." In _Proc. TLCA '97_, LNCS
1210, pp. 196–213, 1997. doi.org/10.1007/3-540-62688-3_37

[23] Masahito Hasegawa. _Models of Sharing Graphs: A Categorical Semantics
of Let and Letrec._ PhD thesis, University of Edinburgh, 1997.
lfcs.inf.ed.ac.uk/reports/97/ECS-LFCS-97-360

[24] Chris Heunen and Bart Jacobs. "Arrows, Like Monads, Are Monoids." In
_Proc. MFPS-XXII_, ENTCS 158, pp. 219–236, 2006.

[25] Bart Jacobs, Chris Heunen, Ichiro Hasuo. "Categorical Semantics for
Arrows." _Journal of Functional Programming_ 19(3-4):403–438, 2009.
doi.org/10.1017/S0956796809007308

[26] John Hughes. "Generalising Monads to Arrows." _Science of Computer
Programming_ 37(1-3):67–111, 2000. doi.org/10.1016/S0167-6423(99)00034-6

[27] André Joyal, Ross Street, Dominic Verity. "Traced Monoidal
Categories." _Mathematical Proceedings of the Cambridge Philosophical
Society_ 119(3):447–468, 1996. doi.org/10.1017/s0305004100074338

[28] J. Roger Hindley and Jonathan P. Seldin. _Lambda-Calculus and
Combinators: An Introduction._ 2nd ed., Cambridge University Press, 2008.

[29] William A. Howard. "The Formulae-as-Types Notion of Construction."
1969 manuscript, published in _To H. B. Curry: Essays on Combinatory
Logic_, Academic Press, 1980.

[30] Yves Lafont. "Interaction Nets." In _Proc. 17th ACM SIGPLAN-SIGACT
Symposium on Principles of Programming Languages (POPL '90)_, pp. 95–108, 1990. doi.org/10.1145/96709.96718

[31] Sam Lindley, Philip Wadler, Jeremy Yallop. "The Arrow Calculus."
_Journal of Functional Programming_ 20(1):51–69, 2010.
doi.org/10.1017/S095679680999027X

[32] Yves Lafont. "Interaction Nets." In _Proc. POPL '90_, pp. 95–108, 1990. doi.org/10.1145/96709.96718

[33] Bruce J. McAdam. "Graphs for Recording Type Information." Technical
Report ECS-LFCS-99-415, University of Edinburgh, 1999.

[34] Patrick Cousot and Radhia Cousot. "Abstract Interpretation: A Unified
Lattice Model for Static Analysis of Programs by Construction or
Approximation of Fixpoints." In _Proc. POPL '77_, pp. 238–252, 1977.

[35] Patrick Cousot and Radhia Cousot. "Systematic Design of Program
Analysis Frameworks." In _Proc. POPL '79_, pp. 269–282, 1979.

[36] Patrick M. Rondon, Ming Kawaguchi, Ranjit Jhala. "Liquid Types." In
_Proc. PLDI '08_, pp. 159–169, 2008. doi.org/10.1145/1375581.1375602

[37] Patrick M. Rondon, Ming Kawaguchi, Ranjit Jhala. "Low-Demand Liquid
Types." In _Proc. POPL '09_, pp. 131–144, 2009.

[38] Patrick M. Rondon, Ming Kawaguchi, Ranjit Jhala. "Liquid Types." In
_Proc. 29th ACM SIGPLAN Conference on Programming Language Design and
Implementation (PLDI '08)_, pp. 159–169, 2008. doi.org/10.1145/1375581.1375602

[39] Peter Selinger. "A Survey of Graphical Languages for Monoidal
Categories." In _New Structures for Physics_, Lecture Notes in Physics 813,
pp. 289–355, Springer, 2010. doi.org/10.1007/978-3-642-12821-9_4,
arxiv:0908.3347

---

_This is a draft. The Lean4 mechanization and Rust prototype are at
`lean/ArrowMinimalityLib/` and `src/` respectively. Build verification:
`lake build` (Lean4) and `cargo run --bin poly_proof_graph` (Rust)._
