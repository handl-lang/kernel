# Thesis & Research Questions

## Refined Thesis

> **A small arrow calculus based on composition, choice, and feedback is
> sufficient to construct a substantial programming-language architecture
> without taking lambda abstraction or monadic structure as primitive.**

This is narrower than "arrows are a complete foundation for programming
languages." The experiments establish _sufficiency for construction_, not
_minimality_ or _necessity_. The distinction matters: sufficiency says
"you can build it"; minimality says "you need exactly these primitives";
necessity says "no smaller basis works."

---

## Evidence Structure

The 121 tests establish a construction arc, not a foundational proof:

```
                    Arrow calculus
                         │
          ┌──────────────┼──────────────┐
          ▼              ▼              ▼
      composition       choice       feedback
          │              │              │
          └──────┬───────┴───────┬──────┘
                 ▼               ▼
             abstraction     recursion
                 │
                 ▼
             computation
                 │
          ┌──────┴──────┐
          ▼             ▼
       effects       semantics
          │             │
          ▼             ▼
      handlers      Language
          │             │
          ▼             ▼
   effect typing   generic tooling
```

Each layer _emerges from the representation below_, not from a new primitive.
This is the strongest aspect of the result: the features are not bolted on,
they are _observed in_ the arrow substrate.

---

## The Central Formal Claim

The deepest result is the **runtime/static correspondence** for effects:

```
Runtime                         Static

UnhandledOp(op)        ↔       op ∈ ε

handler consumes op    ↔       op removed from ε

pass-through op        ↔       op remains in ε
```

An effect row is not an additional semantic layer. It is a **static
observation of the existing computation representation** — the set of
operations suspended in the freer-arrow tree. Handlers are effect
eliminators (`ε \ ops(H)`), and this typing rule falls directly out of the
pass-through semantics.

This correspondence is the project's central formal claim and should be
elevated accordingly.

---

## The IComp Question

The one architectural blemish is the duplication between `Comp` (runtime,
Church-encoded continuations via `Rc<dyn Fn>`) and `IComp` (static,
defunctionalized continuations via `Box<IComp>`).

**Precise framing:** These are the same object under different encodings of
the continuation. `Op(op, arg, k)` where `k : Value -> Comp` _is_ the Church
encoding of `Op(op, arg, K)` where `K` is a defunctionalized continuation
datatype. The closure is what you get when you re-functionalize.

The issue is not that effect inference is impossible over `Comp`; it is that
**opaque host-language closures destroy structural visibility**. The fix is
not a third representation — it is picking the defunctionalized form as
canonical and interpreting it. This is the standard freer-monad move.

- **Engineering choice:** keep both (Comp for execution, IComp for analysis)
- **Formal choice:** canonical freer AST, interpreted into executable arrows

The formal choice is what matters for minimality: you cannot prove
minimality over a representation that hides structure.

---

## The Structural Question (Challenge #9 — RESOLVED)

The 121 tests established that arrows _work_. Challenge #9 tested whether
their **structural advantages survive monadic translation**.

### Answer: The opaque monad is semantically adequate but structurally lossy

Three representations were compared (154/154 tests, 33 new):

| Property               | Arrow      | Opaque monad          | Freer monad |
| ---------------------- | ---------- | --------------------- | ----------- |
| Sequential composition | explicit   | explicit              | explicit    |
| Fanout / independence  | explicit   | **LOST**              | explicit    |
| Choice / branching     | explicit   | **LOST**              | explicit    |
| Effect set             | traversal  | **LOST**              | traversal   |
| Per-branch effects     | per branch | **LOST** (union only) | per branch  |
| Dependency graph       | buildable  | **LOST**              | buildable   |
| Feedback               | explicit   | **LOST**              | detectable  |
| Semantic results       | correct    | correct               | correct     |

The opaque monad produces the same results but loses all structural
information. The freer monad (a monad with explicit structure) recovers
everything, proving the loss is about **opacity** (closures hide
structure), not about monadic structure per se.

### The precise claim

The structural advantage belongs to **explicit, traversable
representations** (freer arrows, freer monads) over **opaque
representations** (conventional monads with function-based continuations).
The arrow calculus naturally produces explicit representations; the
monadic encoding naturally produces opaque ones.

This explains why the freer-arrow model has been useful throughout this
project: effect inference, generic tooling, and structural optimization
all exploit the explicit structure that the arrow representation preserves.

### The false-dependency phenomenon

When arrow fanout (`f &&& g` — independent) is translated to monadic bind,
the second computation appears to depend on the first's result — a false
dependency created by the bind chain. The arrow's dependency graph
correctly shows no edge; the monad cannot build the graph at all.

---

## Open Questions (Beyond Challenge #9)

### Minimality — RESOLVED ✅

The minimal arrow calculus for a total PL requires **five independent
primitives**: `arr`, `comp`, `first`, `loop`, `left`. No primitive can
be derived from the others.

- **`left` (choice)** — NOT derivable from `arr + comp + first + loop`.
  No constructor introduces `Sum` on the output. (Challenge #10, Lean4)
- **`first` (products)** — NOT derivable from `arr + comp + loop`.
  No constructor introduces `×` on the output. (Challenge #10, Lean4)
- **`loop` (feedback)** — NOT derivable from `arr + comp + first`
  (total setting). No constructor introduces feedback. (Challenge #10, Lean4)
- **`comp` (composition)** — NOT derivable from the rest. Without `comp`,
  no combinator chains two arrows sequentially.
- **`arr` (lifting)** — NOT derivable from the rest. Without `arr`, no
  combinator lifts a pure function into the arrow.

All five proven via the free-arrow (initiality) argument in Lean4. See
`lean/ArrowMinimalityLib/Basic.lean`.

**Caveat:** `loop` is independent only in a _total_ setting. In a
language with general recursion (`fix`), `loop` is derivable — but then
general recursion is the primitive, and `loop` is a pattern of use.

### Necessity of `lit` — RESOLVED ✅

`lit` (the `Value ~> AST` arrow, inverse of `eval` on literals) is
**necessary for optimization, not for tooling**. Confirmed empirically
with a "broken lit" language (5 tests):

- **Pretty-print** uses only `format` — works without `lit`. ✅
- **Error reporting** uses only `typecheck` + `eval` — works without `lit`. ✅
- **Parse-eval pipeline** uses only `parse` + `eval` — works without `lit`. ✅
- **Constant-folding optimizer** uses `eval` + `lit` — **requires `lit`**.
  With broken `lit`, folding fails gracefully (keeps the un-folded node). ✅
- **`lit` is the inverse of `eval` on literals**: `eval(lit(n)) = n` and
  `lit(eval(Int(n))) = Int(n)`. ✅

**Conclusion:** `lit` is the enabler for the generic constant-folding
optimizer — it re-embeds folded values back into syntax without
language-specific code. Without `lit`, you can still pretty-print,
report errors, and run programs; you just can't fold constants
generically. `lit` is necessary for optimization, not for basic
tooling.

### Translation asymmetry — RESOLVED ✅ (negative result)

- Can every lambda term encode as an arrow term of comparable size?
  **YES** — the standard translation T is linear: `|T(p)| ≤ 8·|p|`,
  proven in Lean4.
- Are there arrow programs (using `loop` or `choice` essentially) whose
  lambda encodings are awkward or non-compositional? **NO** — T is
  compositional: `T(f >>> g) = T(g) ∘ T(f)`, proven in Lean4.
- If arrows encode lambda cleanly but lambda encodes arrows awkwardly,
  that is the real argument for arrows as the foundation. **Does not
  hold** — the translation dimension is symmetric. The real asymmetries
  are **representation** (opacity, Challenge #9) and **expressive
  power** (ArrowApply, Challenge #11), both already established.

See `RESULTS_TRANSLATION_ASYMMETRY.md` and
`lean/ArrowMinimalityLib/Translation.lean`.

---

## Status

| Phase     | Challenges                                                           | Tests      | Status      |
| --------- | -------------------------------------------------------------------- | ---------- | ----------- |
| 1         | #1–5 (expressiveness, abstraction, parametricity, typing, recursion) | 44         | ✅ Complete |
| 2         | #6 (effects & handlers)                                              | 20         | ✅ Complete |
| 3         | #7–8 (language protocol, generic tooling)                            | 31         | ✅ Complete |
| Deep dive | Effect typing (row inference, handler elimination, polymorphic rows) | 31         | ✅ Complete |
| 4         | #9 (structural preservation under monadic translation)               | 33         | ✅ Complete |
| 5         | #10 (minimality — Lean4)                                             | 7 theorems | ✅ Complete |
| 6         | #11 (ArrowApply without opacity)                                     | 19         | ✅ Complete |
| 7         | Translation asymmetry — Lean4                                        | 8 theorems | ✅ Complete |
| 8         | #12 (structural preservation under profunctor translation)           | 28         | ✅ Complete |
| 9         | #13 (arrow vs freer monad asymmetry — REVISED)                       | 23         | ✅ Complete |

**Total: 229/229 Rust tests + 212 Lean4 theorems (17 modules, 9,165 lines), zero `sorry`, zero warnings.**

---

## The Profunctor Subsumption Question (Challenge #12 — RESOLVED)

Wikipedia claims: "Much of the utility of arrows is subsumed by more
general classes like profunctor... An arrow is essentially a strong
profunctor that is also a category."

### Answer: The subsumption is HOLLOW

A bare profunctor (dimap + composition) **cannot even express** the
structural features that make arrows useful: fanout, choice, and
feedback. To recover them, you add strength (`first`), choice (`left`),
and trace (`loop`) — which reconstructs the arrow interface exactly.
"Strong cocartesian traced profunctor" = Arrow.

Meanwhile, an opaque profunctor has the **same opacity problem** as an
opaque monad (Challenge #9). The profunctor interface (dimap/lmap/rmap)
does not help with structural inspection.

### The precise claim

The profunctor framing is more general (weaker): it drops exactly the
combinators (strength, choice, trace) that make arrows structurally
useful. Adding them back reconstructs the arrow calculus. The
"subsumption" is a renaming, not a replacement.

See `RESULTS_CHALLENGE12.md` for the full 28-test suite.

---

## The Arrow-vs-Freer-Monad Question (Challenge #13 — RESOLVED, FULLY MECHANIZED)

Is there ANY structural asymmetry between arrows and freer monads?

### Answer: YES — the asymmetry is real, two-fold, and FULLY MECHANIZED

The original Challenge #13 found "no asymmetry" — but it compared freer
arrows against a "full freer monad" with explicit Fanout/Choice/Loop
constructors. **That was a freer arrow in disguise.** The comparison was
circular.

The correct comparison (standard freer monad with opaque function
continuations) reveals a clear asymmetry:

1. **Expressiveness gap (MECHANIZED UNIVERSAL THEOREM, zero `sorry`):**
   The freer monad CANNOT correctly encode arrow fanout, choice, or
   loop. This is fully mechanized in Lean4 — not just for the canonical
   encoding, but for the _entire class_ of `bind`-based encodings. The
   key encoding-independent law (`bind_continuation_input_is_predecessor_output`,
   provable by `rfl`): in `bind m k`, the continuation `k` is invoked
   with `m`'s _output_, never the original input. Three universal
   theorems: `no_bind_encoding_preserves_fanout` (Get/Put semantics),
   `no_bind_encoding_preserves_choice` (Sum value domain),
   `no_bind_encoding_preserves_loop` (pair/feedback value domain). All
   quantify over ALL `(m, k)` and prove divergence when `input ≠ state`.
   24 theorems, all proven (see
   [FanoutUnencodable.lean](lean/ArrowMinimalityLib/FanoutUnencodable.lean)).
   The root cause is isolated by `impossibilityIsStructural`: arrows
   expose the input parameter to every branch; monadic `bind` exposes
   only the previous output.

2. **Static analysis gap (EMPIRICAL):** Even for sequential composition (which
   the monad CAN encode), the structure is opaque — continuations are
   functions, not traversable trees. Effect inference, per-branch analysis,
   speculative compilation, and fusion all fail (242 Rust tests verify this).

This confirms and formally strengthens VanDomelen et al. (Haskell 2025):
the gap is not just static analysis but also **semantic expressiveness**.
The arrow's explicit input parameter is the key structural feature that
monads fundamentally lack.

See `RESULTS_CHALLENGE13.md` and `FORMALIZATION_SUMMARY.md` for the full
242-test suite and the mechanized proof.

---

## Relationship to the Wikipedia Article on Arrows

The Wikipedia article on [Arrow (computer
science)](<https://en.wikipedia.org/wiki/Arrow_(computer_science)>) makes
several claims that this project directly addresses. The full analysis
is in `WRITEUP.md` §12; summary:

| Wikipedia claim                                                               | Our finding                                                                                                                                                                                                        | Challenge    |
| ----------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ | ------------ |
| "ArrowApply rarely used because equivalent to monads"                         | **Refuted**: equivalence is power, not representation. Explicit ArrowApply gives monadic power without opacity.                                                                                                    | #11          |
| "Utility of arrows subsumed by profunctor"                                    | **Refuted**: bare profunctor can't express fanout/choice/feedback. "Strong cocartesian traced profunctor" = Arrow.                                                                                                 | #12          |
| "FP enables static code analysis" (attributed to FP, not arrows specifically) | **Extended**: precise characterization of what explicit arrow structure preserves that opaque monadic structure destroys — effect inference, per-branch analysis, speculative compilation, fusion.                 | #9, #11, #13 |
| "Monads often preferable when arrow features unnecessary"                     | **Extended**: Wikipedia is right that monads are simpler when you don't need arrow features — but understates those features. Fanout/choice are expressiveness gaps monads can't bridge, not optional convenience. | #13          |
| 3 primitives (Haskell type class)                                             | **Extended**: 5 independent primitives needed for full PL (adds left, loop). Independence proven in Lean4.                                                                                                         | #10          |
| Choice/feedback are optional extensions                                       | **Extended**: necessary for PL (branching, recursion). Sufficiency demonstrated.                                                                                                                                   | #1–#8        |

---

## The Corrected Slogan (after Challenges #9, #11, #12, and #13)

The original thesis: "arrows can replace monads."

The corrected thesis:

> **ArrowApply (in the explicit/freer style) gives you monadic power
> WITHOUT the opacity penalty. Ordinary opaque monads bury structure
> in closures; the explicit ArrowApply presentation keeps the
> computation tree inspectable — effects, branching, per-branch
> analysis, and dependency graphs all remain recoverable.**

The isomorphism `ArrowApply ≅ Monad` is about **expressive power**, not
about **representation**. The classic translation produces an opaque
monadic computation. Our result (Challenge #11) shows there exists a
presentation of the same power that stays **transparent**. That is the
non-trivial part, and it is what makes the claim interesting.

It no longer says "arrows are better than monads"; it says "this explicit
ArrowApply presentation gives you monadic power _without_ the opacity
penalty."

Challenge #12 extends this: the structural advantages are not subsumed by
profunctors either. A bare profunctor cannot express fanout, choice, or
feedback; an opaque profunctor is as opaque as an opaque monad; and
"strong cocartesian traced profunctor" = Arrow. The "more general"
profunctor interface is weaker, not stronger — it drops exactly the
combinators that make arrows structurally useful.

Challenge #13 closes the loop: freer arrows ARE structurally superior
to freer monads. **This is now a formal theorem, not just an empirical
observation.** The original Challenge #13 found "no asymmetry" but
that was circular — it compared against a "full freer monad" that was
actually a freer arrow in disguise. The correct comparison (standard
freer monad with opaque function continuations) reveals a two-fold gap:
(1) expressiveness — freer monads can't correctly encode fanout or
choice because bind threads f's output, not the original input
(PROVEN in Lean4); (2) static analysis — opaque continuations prevent
effect inference, speculative compilation, and fusion (VERIFIED by 23
Rust tests). This confirms and strengthens VanDomelen et al. (Haskell 2025).

---

## Phase 4: Arrow Graphs as Proof Objects (λ-free Curry-Howard)

The deepest extension of the thesis: **the arrow graph is simultaneously
a program, a typing derivation, and a proof object**. This is a λ-free
Curry-Howard correspondence — the proof structure is carried by graph
wiring (comp = cut, first = ∧-functoriality, left = ∨-functoriality,
loop = trace/fixpoint), not by λ-binders.

### The Correspondence Theorem (PROVEN in Lean4)

For every arrow graph `G` built from the five independent primitives:

```
    TyOf G  ⟺  PrOf G     (typing derivation = proof derivation)
```

The two inductive predicates have the same indices, the same
constructors, and the same side conditions. The maps `TyOf.toPrOf` and
`PrOf.toTyOf` are mutually inverse bijections on derivations
(round-trip theorems proven). This is the precise content of "the
typing derivation and the proof derivation are structurally identical."

### Subject Reduction / Type Soundness (PROVEN in Lean4)

```
    ⊢ G : A ⇝ B  ∧  G · a ⟹ v  ∧  a : A   ⟹   v : B
```

All seven execution cases discharged, including the two subtle ones:

- `eLeftR`: `left G` preserves the right summand (`inr b ⟹ inr b`).
- `eLoop`: the fixpoint witness `HasType cₙ C` supplies the feedback
  channel's type.

### Proof Realizability (PROVEN in Lean4)

```
    ⊢ G ⊩ A ⊢ B  ∧  G · a ⟹ v  ∧  a : A   ⟹   v : B
```

This is literally subject reduction precomposed with the correspondence's
backward direction. The proof judgment adds no logical power beyond the
typing judgment — it is the same derivation under a different reading.

### Annotation-Free Inference (VERIFIED in Rust, 12 tests)

The Rust prototype demonstrates that types flow from the signature
through the graph structure **without any annotations on the graph
itself**. The graph carries no type information; `infer_type` recovers
`(input, output)` purely from the signature's base-arrow types + the
graph's wiring. Proof obligations are generated structurally: well-typed
graphs generate zero obligations; ill-typed graphs pinpoint the exact
mismatch.

### Why This Matters

Classical Curry-Howard identifies λ-terms with natural-deduction proofs.
The binding structure of λ is what carries the proof structure. Here,
there is no λ: the proof structure is carried by the **graph wiring**.
The graph is the proof object, and it is λ-free by construction (the
syntax has no binder). This connects the structural transparency of
arrows (Phases 1-3) to logical reasoning: an opaque monad can't be a
proof object because its structure is hidden in closures; an arrow
graph's structure is explicit, so it can serve as a derivation.

Full details: `FORMALISM_PROOF_GRAPHS.md`, `RESULTS_PROOF_GRAPHS.md`,
`lean/ArrowMinimalityLib/ProofGraphs.lean`, `src/proof_graph_tests.rs`.
