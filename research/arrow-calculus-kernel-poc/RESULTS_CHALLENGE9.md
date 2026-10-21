# Challenge #9: Structural Preservation Under Monadic Translation

## Status: ✅ COMPLETE — 33/33 tests passing

Date: 2026-08-31
Challenge: #9 — Does monadic encoding preserve arrow structure?
Cumulative: 154/154 tests passing (121 prior + 33 new), zero warnings.

---

## The Question

The fact that a monad can be _encoded_ by an arrow system is not enough.
The important issue is whether doing so collapses the **structural
information that makes arrows valuable**.

> **Does deriving `bind` destroy information that the original arrow
> representation preserves?**

If yes, "monad is expressible" is a weak result. If the monadic encoding
is **semantically adequate but structurally lossy**, that explains why
the freer-arrow representation has been useful for effect inference: it
exploits structure that opaque functions don't expose.

---

## The Experiment

Three representations of the same computations were compared:

| Representation                | Structure                                                | Continuations              | Inspectable?            |
| ----------------------------- | -------------------------------------------------------- | -------------------------- | ----------------------- |
| **Freer arrow** (`ArrowComp`) | Explicit connectives (Seq, Fanout, Choice, Loop, OpNode) | Defunctionalized sub-trees | ✅ Yes — full traversal |
| **Opaque monad** (`OpaqueM`)  | Hidden inside closures                                   | `Rc<dyn Fn>` — black box   | ❌ No — can only run    |
| **Freer monad** (`FreeM`)     | Explicit (Pure, Ident, FreeOp, Bind, Fanout, Choice)     | Defunctionalized sub-trees | ✅ Yes — full traversal |

The key comparison is **freer arrow vs opaque monad**: what structural
properties can you observe from each?

The freer monad serves as a control: if it recovers structure, the loss
is about _opacity_, not monadic structure per se.

---

## Structural Properties Tested

For each property, we attempt recovery from each representation:

| Property                   | Arrow          | Opaque monad             | Freer monad        |
| -------------------------- | -------------- | ------------------------ | ------------------ |
| **Sequential composition** | ✅ explicit    | ✅ explicit (bind)       | ✅ explicit (Bind) |
| **Fanout / independence**  | ✅ recoverable | ❌ **LOST**              | ✅ recoverable     |
| **Choice / branching**     | ✅ recoverable | ❌ **LOST**              | ✅ recoverable     |
| **Effect set**             | ✅ traversal   | ❌ **LOST**              | ✅ traversal       |
| **Per-branch effects**     | ✅ per branch  | ❌ **LOST** (union only) | ✅ per branch      |
| **Dependency graph**       | ✅ buildable   | ❌ **LOST**              | ✅ buildable       |
| **Feedback / loop**        | ✅ explicit    | ❌ **LOST**              | ✅ detectable      |
| **Semantic results**       | ✅ correct     | ✅ correct               | ✅ correct         |

---

## Key Findings

### 1. The opaque monad is semantically adequate but structurally lossy

**Same program, same results** — the monadic encoding produces identical
outputs and state transitions:

```
arrow:  result=(), state=99
monad:  result=(), state=99
match:  true
```

**But structural information is lost:**

```
Arrow:               Opaque monad:
fanout:  YES         fanout:  NO — LOST
choice:  YES         choice:  NO — LOST
effects: {Get,...}   effects: NO — LOST
per-branch: YES      per-branch: NO — LOST
dep graph: 6 edges   dep graph: 0 edges
```

### 2. The loss is about opacity, not monadic structure

The freer monad — which IS a monad, but with explicit structure —
recovers ALL structural information:

```
Freer monad:
choice:  YES
left branch effects:  {Get, Throw}
right branch effects: {Put}
total effects:        {Get, Put, Throw}
dependency graph:     6 edges
```

This proves the structural loss is specific to **opaque closures**, not
to monadic structure per se. A freer monad is structurally equivalent to
a freer arrow — both expose their computation tree.

### 3. Fanout creates false dependencies in monadic bind

When arrow fanout (`f &&& g` — independent computations) is translated
to monadic bind, the second computation APPEARS to depend on the first's
result:

```
Arrow: f &&& g           → no edge between f and g in dependency graph
Monad: f >>= (\v1 -> g)  → g looks like it depends on v1
```

In the arrow's dependency graph, fanout children have **no edge between
them** — they are independent. In the opaque monad, the bind chain
creates an **apparent dependency** that doesn't exist semantically.

### 4. Per-branch effects are lost

The arrow can determine that a choice has different effect sets per
branch:

```
left branch:  {Get, Throw}    — if we go left, ONLY these
right branch: {Put}           — if we go right, ONLY this
```

The opaque monad can only report the **union** (if it could report at
all), losing the conditional information. This has practical
consequences: an optimizer that folds independent branches separately
works on the arrow but not on the opaque monad.

### 5. The loss has practical consequences

An optimizer that can fold independent branches separately works on the
arrow representation (it can SEE the branches and their effects) but
NOT on the opaque monad (branch structure is invisible).

---

## Test Summary

33 tests across 7 categories:

| Category                                     | Tests | Status |
| -------------------------------------------- | ----- | ------ |
| Semantic equivalence (arrow = monad = freer) | 6     | ✅     |
| Fanout / independence recovery               | 4     | ✅     |
| Choice / branching recovery                  | 3     | ✅     |
| Effect set inference                         | 3     | ✅     |
| Per-branch effect analysis                   | 3     | ✅     |
| Dependency graph                             | 3     | ✅     |
| Feedback / loop                              | 2     | ✅     |
| Key finding: semantically adequate but lossy | 3     | ✅     |
| Effect set properties                        | 4     | ✅     |
| False dependency in monadic fanout           | 2     | ✅     |

---

## Implications for the Arrow Calculus Thesis

### What this establishes

The arrow calculus thesis is not merely "arrows can encode monads."
It is:

> **The freer-arrow representation preserves structural information that
> the opaque monadic representation destroys. This structural
> information is practically useful: it enables static effect inference,
> per-branch analysis, dependency graph construction, and structural
> optimization — all of which are impossible on the opaque monadic
> representation without reifying additional structure.**

### What this does NOT establish

- It does not claim monads are _inherently_ structurally lossy — freer
  monads recover structure (proven here).
- It does not claim arrows are _minimal_ — that's the next question.
- It does not claim the structural advantage is _unique_ to arrows —
  freer monads share it.

### The precise claim

The structural advantage belongs to **explicit, traversable
representations** (freer arrows, freer monads) over **opaque
representations** (conventional monads with function-based continuations).
The arrow calculus naturally produces explicit representations; the
monadic encoding naturally produces opaque ones.

This explains why the freer-arrow model has been useful throughout this
project: effect inference (Phase 2 deep dive), generic tooling (Phase 3),
and structural optimization (this challenge) all exploit the explicit
structure that the arrow representation preserves.

---

## Comparison to the Arrow/Applicative/Monad Hierarchy

The Arrow/Applicative/Monad hierarchy in Haskell distinguishes:

- **Applicative**: independent computations (`<*>` preserves structure)
- **Monad**: dependent computations (`>>=` may hide structure)
- **Arrow**: both, with explicit connectives

Our results align with this hierarchy:

- **Fanout** (independent computations) is natural in Applicative/Arrow
  but awkward in Monad (requires `Applicative` wrapper or explicit
  input preservation)
- **Choice** is explicit in Arrow, hidden in Monad
- **Static analysis** works on Applicative/Arrow structure, not on
  opaque Monad

The arrow calculus makes ALL of these explicit, which is why it supports
structural analysis uniformly.

---

## Files

- `src/structural_preservation_tests.rs` — 33-test suite (new)
- `Cargo.toml` — added `structural_preservation` binary
- `FORMALISM.md` — appended "Structural Preservation (Challenge #9)" section
- `WORKING_NOTES.md` — updated verdict tracker, completion status, structural question resolved
- `THESIS.md` — updated Challenge #9 section with findings

---

## Cumulative Results

| Phase     | Challenge                                                            | Tests   | Status          |
| --------- | -------------------------------------------------------------------- | ------- | --------------- |
| 1         | #1–5 (expressiveness, abstraction, parametricity, typing, recursion) | 44      | ✅              |
| 2         | #6 (effects & handlers)                                              | 20      | ✅              |
| 3         | #7–8 (language protocol, generic tooling)                            | 26      | ✅              |
| Deep dive | Effect typing                                                        | 31      | ✅              |
| 4         | #9 (structural preservation)                                         | 33      | ✅              |
|           | **Total**                                                            | **154** | **All passing** |
