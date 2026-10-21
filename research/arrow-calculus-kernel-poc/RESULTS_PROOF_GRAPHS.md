# Phase 4 Results: Arrow Graphs as Proof Objects

## Status: ✅ COMPLETED

Date: 2026-09-02
Phase: 4 (Curry-Howard for Arrow Graphs — λ-free proof objects)
Focus: Make the arrow graph simultaneously the program, the typing
derivation, and the proof object. Establish the typing⇔proof
correspondence and soundness against execution semantics.

---

## Summary

This phase establishes that an arrow graph — built from the five
independent primitives (arr, comp, first, left, loop) — is
simultaneously:

1. **A program**: it executes via the `Eval` relation (`G · a ⟹ v`).
2. **A typing derivation**: the `TyOf` predicate witnesses that the
   graph is well-typed at its type indices.
3. **A proof**: the `PrOf` predicate witnesses a logical derivation
   (cut, ∧-functoriality, ∨-functoriality, trace) under the
   propositions-as-types reading.

The key result is that **the typing derivation and the proof derivation
are structurally identical** (rule-for-rule, notation-for-notation),
related by a bijection that is the identity on shape. This is the
**λ-free Curry-Howard correspondence**: the proof structure is carried
by graph wiring, not by λ-binders.

---

## Deliverables

| Artifact            | Location                                   | Status              |
| ------------------- | ------------------------------------------ | ------------------- |
| Formalism document  | `FORMALISM_PROOF_GRAPHS.md`                | ✅ Complete         |
| Lean4 mechanization | `lean/ArrowMinimalityLib/ProofGraphs.lean` | ✅ Builds clean     |
| Rust prototype      | `src/proof_graph_tests.rs`                 | ✅ 12/12 tests pass |
| Cargo.toml binary   | `proof_graph`                              | ✅ Wired up         |

---

## Lean4 Mechanization (`ProofGraphs.lean`)

### Theorems Proven

1. **Typing ⇔ Proof (correspondence)**:
   - `typing_to_proof : TyOf G → PrOf G` — forward direction
   - `proof_to_typing : PrOf G → TyOf G` — backward direction
   - `TyOf.toPrOf_toTyOf : d.toPrOf.toTyOf = d` — round-trip (forward)
   - `PrOf.toTyOf_toPrOf : d.toTyOf.toPrOf = d` — round-trip (backward)

   The round-trip theorems establish that the two maps are mutually
   inverse bijections on derivations. This is the precise content of
   "the typing derivation and the proof derivation are structurally
   identical."

2. **Subject Reduction (type soundness)**:
   `subject_reduction : TyOf G → Eval den G a v → HasType a A → HasType v B`

   All seven execution cases are discharged:
   - `eId`, `eComp`, `eFirst`, `eLeftL`, `eArr` — direct IH + inversion.
   - `eLeftR` — `left G` preserves the right summand (`inr b ⟹ inr b`);
     the output type's right summand `D` is recovered from the typing
     derivation's `leftT` constructor.
   - `eLoop` — the fixpoint witness `hcₙ : HasType cₙ C` (carried by the
     `eLoop` constructor) supplies the feedback channel's type.

3. **Proof Realizability**:
   `proof_realizability : PrOf G → Eval den G a v → HasType a A → HasType v B`

   This is literally subject reduction precomposed with the
   correspondence's backward direction. The proof judgment adds no
   logical power beyond the typing judgment.

### Key Design Decisions

- **Universe levels**: `Graph`, `TyOf`, `PrOf`, and `Eval` are all
  `Type 1` (because `Graph` stores `Sig : Ty → Ty → Type`, which lives
  in `Type 1`). The `HasType` predicate is `Prop` (it's a logical
  assertion, not data).

- **Explicit constructor args**: The `TyOf`/`PrOf` constructors carry
  `G`/`H` (the sub-graphs) and `D`/`C` (the preserved/feedback types)
  as explicit arguments, so the equation compiler can recover the
  internal type variables from their types.

- **`eLeftR` semantics**: `left G` preserves the right summand unchanged
  (`inr b ⟹ inr b`), rather than running `G` on it. The earlier draft
  ran `G` on the right payload, which was a type error — the type says
  the right summand `D` is preserved.

- **`eLoop` fixpoint witness**: The `eLoop` constructor carries
  `hcₙ : HasType cₙ C` as a field, so the feedback channel's type is
  recoverable without index surgery. This is the standard
  "fixpoint-state typing" lemma of traced-category soundness.

- **`match` vs `cases`**: In the `eLoop` case of `subject_reduction`,
  `cases d with` had trouble binding the constructor's implicit args
  after `induction e` generalized `d`. Using `match d with` (term-mode)
  resolved this — `match` handles the dependent types more gracefully.

- **`SigSound` as hypothesis, not class**: The signature soundness
  condition is carried as an explicit hypothesis (not a typeclass), so
  the `Atom`/`Sig` parameters remain inferrable from the goal.

---

## Rust Prototype (`proof_graph_tests.rs`)

### 12 Tests, All Passing

| Test | Description               | Key Result                                                       |
| ---- | ------------------------- | ---------------------------------------------------------------- |
| 1    | Identity graph            | `id[Int] : Int ⇝ Int` inferred                                   |
| 2    | Composition (succ;succ)   | `Int ⇝ Int`, 0 obligations                                       |
| 3    | First (×-functoriality)   | `(Int×Int) ⇝ (Int×Int)` inferred                                 |
| 4    | Left (+-functoriality)    | `(Int+Bool) ⇝ (Int+Bool)` inferred                               |
| 5    | Loop (trace/fixpoint)     | `Int ⇝ Int` from `Int×Int ⇝ Int×Int` body                        |
| 6    | Sort graph                | `([Int]×(Int×Int)) ⇝ [Int]` — sort preserves element type        |
| 7    | Filter-like predicate     | `(Int×Int) ⇝ Bool` — predicate type inferred without annotations |
| 8    | Complex graph (head;succ) | `[Int] ⇝ Int` — all properties inferred without annotations      |
| 9    | Ill-typed composition     | Correctly rejected: `Int ≠ [Int]`                                |
| 10   | Ill-typed loop            | Correctly rejected: feedback channel `Bool ≠ Int`                |
| 11   | Round-trip correspondence | All 7 well-typed graphs: typing→proof→typing ✓                   |
| 12   | Obligation scaling        | Well-typed graphs: 0 obligations; complexity scales              |

### Annotation-Free Inference

The prototype demonstrates that types flow from the signature through
the graph structure **without any annotations on the graph itself**.
The graph carries no type information; the `infer_type` function
recovers `(input_type, output_type)` purely from:

1. The signature's base-arrow types (the only place types appear).
2. The graph's wiring structure (comp = cut, first = ∧-functoriality,
   left = ∨-functoriality, loop = trace).

This is the core claim of the formalism: **structural reasoning on the
graph propagates types/facts and generates proof obligations**, without
requiring the programmer to annotate anything.

### Proof Obligation Generation

The `proof_obligations` function generates obligations from the graph
structure:

- **Composition**: the middle type must match (cut rule).
- **Loop**: the feedback channel type must be consistent.
- **Base arrow**: the signature entry must exist.

Well-typed graphs generate **zero** obligations — the proof is
discharged by the structure itself. Ill-typed graphs generate
obligations that pinpoint the exact mismatch.

### Typing ⇔ Proof Correspondence (Rust)

The Rust prototype mirrors the Lean4 correspondence:

- `typing_to_proof : &TypingDerivation → ProofDerivation` — rule-for-rule
- `proof_to_typing : &ProofDerivation → TypingDerivation` — rule-for-rule
- `verify_correspondence : &Graph → bool` — round-trip check

The `TypingDerivation` and `ProofDerivation` enums are structurally
identical (same constructors, same arguments), confirming the
correspondence at the implementation level.

---

## The λ-free Curry-Howard Slogan (Mechanized)

```
    one graph G
       │
       ├─ as program:   Eval den G a v      (execute)
       ├─ as type:      TyOf G              (typecheck)
       └─ as proof:     PrOf G              (reason)

    TyOf G  →  PrOf G                      (typing_to_proof)
    PrOf G  →  TyOf G                      (proof_to_typing)
    TyOf G  →  Eval G a v → a:A → v:B      (subject_reduction)
    PrOf G  →  Eval G a v → a:A → v:B      (proof_realizability)
```

The graph is λ-free (the `Graph` inductive has no binder), and yet it
is simultaneously a program, a typing derivation, and a proof. This is
the arrow-graph Curry-Howard correspondence.

---

## Relation to Prior Phases

| Phase | Focus                           | This Phase's Contribution          |
| ----- | ------------------------------- | ---------------------------------- |
| 1     | Freer arrows, handlers, effects | The 5 primitives are the substrate |
| 2     | Effect typing, recursion        | Typing judgments extend to effects |
| 3     | Language protocol, tooling      | Graphs are language-agnostic       |
| **4** | **Proof objects**               | **Graph = program = type = proof** |

The key insight connecting all phases: the **structural transparency**
of arrows (Phase 1-3) is what makes the Curry-Howard correspondence
work (Phase 4). An opaque monad can't be a proof object because its
structure is hidden in closures; an arrow graph's structure is explicit,
so it can serve as a derivation.

---

## Limitations & Future Work

1. **Dependent typing**: The formalism document (§6) sketches a
   dependent typing extension where `loop` can carry a termination
   proof. The dependent type system itself (`DTy` with `dPi`/`dSigma`),
   subject reduction (including `eLoop`), and dependent loop termination
   are now fully mechanized in `DependentProofGraphs.lean` (zero
   `sorry`): the `DEvalIter` and `DLoopIter` inductives formalize
   iterated dependent loop evaluation, and
   `ddecreasing_measure_bounds_iterations` proves that a decreasing
   measure bounds the number of non-fixpoint iterations in the dependent
   setting. The last formalization gap is closed.

2. **Iterated loop**: The `eLoop` constructor uses a one-step fixpoint
   rule (the feedback channel is already stable). The iterated form
   (loop unfolds until convergence) is now proven in `IteratedLoop.lean`
   (`EvalIter` with `eLoopZero`/`eLoopIter`, subject reduction across
   iterations), and loop termination is formalized in `Termination.lean`
   (zero `sorry`): the `LoopIter` inductive threads `c_next` into the
   recursive call, and `decreasing_measure_bounds_iterations` proves
   that a decreasing measure bounds the number of non-fixpoint
   iterations.

3. **Polymorphic signature**: The prototype uses a monomorphic
   signature (Int, Bool, List Int). A polymorphic signature with type
   variables would demonstrate the full power of annotation-free
   inference (Hindley-Milner style).

4. **Proof-relevant HasType**: The `HasType` predicate is `Prop`
   (proof-irrelevant). A proof-relevant version (where the typing
   derivation is first-class data) would enable stronger metaprogramming.

---

## Build Verification

```
Lean4:  lake build  →  Build completed successfully (5 jobs)
Rust:   cargo run --bin proof_graph  →  All 12 tests passed
```
