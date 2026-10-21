# Arrows ↔ Logic

## The short version

**Classical Curry–Howard:** λ-terms _are_ proofs. Binders carry the proof
structure.

**This project's claim:** graph wiring carries the proof structure — no λ
needed. This is a **λ-free Curry–Howard correspondence**.

## The translation table

| Arrow primitive        | Program     | Proof                |
| ---------------------- | ----------- | -------------------- |
| `id`                   | identity    | identity `A ⊢ A`     |
| `comp(f,g)`            | `f >>> g`   | **cut**              |
| `first(f)`             | act on 1st  | **∧-functoriality**  |
| `left(f)`              | act on Left | **∨-functoriality**  |
| `loop(f)`              | feedback    | **trace / fixpoint** |
| `arr(φ)`               | lift φ      | **axiom**            |
| `f &&& g` (derived)    | fanout      | **∧-introduction**   |
| `f \|\|\| g` (derived) | merge       | **∨-elimination**    |

## The theorem (proven in Lean4)

```
TyOf G  ⟺  PrOf G
```

Typing derivation and proof derivation are the _same inductive object_ —
same indices, same constructors, same side conditions, mutually inverse
round-trips. The proof judgment `⊩` adds **zero logical power** over the
typing judgment; it's the same derivation read differently.

Subject reduction and realizability both fall out for free.

## Why it works, categorically

An arrow = morphism in a **strong cocartesian traced category**:

- cartesian (`×`, `first`) ↔ ∧
- cocartesian (`+`, `left`) ↔ ∨
- traced (`loop`) ↔ fixpoint/μ
- closed (`app`/ArrowApply) ↔ implication ⇒ ← this is the
  `ArrowApply ≅ Monad` isomorphism

## Why it matters

The **same structural transparency** that makes arrows good for static
analysis (effect inference, fusion, per-branch analysis — Challenges
#9/#11/#13) is what makes them good **proof objects**. An opaque monad
can't be a proof — its structure is buried in closures and can't be
traversed into a derivation. An arrow graph's structure is explicit, so
it _is_ the derivation.

**One line:** the five minimally-independent arrow primitives are not
just sufficient to build a PL — they are exactly the structural rules of
a sequent proof calculus over ∧/∨ with fixpoints, and the graph wiring
_is_ the proof.

## Pointers

- Correspondence theorem + subject reduction + realizability:
  `lean/ArrowMinimalityLib/ProofGraphs.lean`
- Full formalism: `FORMALISM_PROOF_GRAPHS.md`
- Empirical (annotation-free inference, 12 tests): `src/proof_graph_tests.rs`
- Results summary: `RESULTS_PROOF_GRAPHS.md`
- Thesis framing: `THESIS.md` (Phase 4)
