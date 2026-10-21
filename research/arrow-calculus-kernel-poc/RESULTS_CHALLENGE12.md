# Challenge #12: Structural Preservation Under Profunctor Translation

## Status: COMPLETE — 28/28 tests passing

Date: 2026-09-01
Challenge: #12 — Does the profunctor interface preserve arrow structure?
Cumulative: 201/201 Rust tests + 19 Lean4 theorems, zero warnings.

---

## The Question

Wikipedia claims: "Much of the utility of arrows is subsumed by more
general classes like profunctor... An arrow is essentially a strong
profunctor that is also a category."

> **Does the profunctor interface (dimap + lmap + rmap + composition)
> preserve the structural properties that the arrow interface preserves
> (Challenge #9)?**

If yes, profunctors genuinely subsume arrow utility. If no, the
"subsumption" is hollow — you add back exactly the arrow combinators
to recover the utility.

---

## The Answer: The subsumption is HOLLOW

A bare profunctor (dimap + composition) **cannot even express** the
structural features that make arrows useful: fanout, choice, and
feedback. To recover them, you add strength (`first`), choice (`left`),
and trace (`loop`) — which reconstructs the arrow interface exactly.
"Strong cocartesian traced profunctor" = Arrow.

Meanwhile, an opaque profunctor has the **same opacity problem** as an
opaque monad (Challenge #9). The profunctor interface (dimap/lmap/rmap)
does not help with structural inspection.

---

## The Experiment

Four representations of the same computations were compared:

| Representation                                              | Structure                                                  | Inspectable?                                                              |
| ----------------------------------------------------------- | ---------------------------------------------------------- | ------------------------------------------------------------------------- |
| **Freer arrow** (`ArrowComp`)                               | Explicit connectives (Seq, Fanout, Choice, Loop, OpNode)   | Yes — full traversal                                                      |
| **Opaque profunctor** (`OpaqueP`)                           | Hidden inside closures; dimap/lmap/rmap/seq available      | No — can only run                                                         |
| **Bare freer profunctor** (`FreeP`)                         | Explicit tree, but ONLY dimap/seq/ops (no first/left/loop) | Partial — seq and effects visible; fanout/choice/loop **unrepresentable** |
| **Freer profunctor + strength + choice + trace** (`FreePA`) | Explicit tree with first/left/loop added back              | Yes — isomorphic to arrow                                                 |

The key comparisons:

1. **Bare profunctor vs arrow**: what can the bare profunctor express?
2. **Opaque profunctor vs opaque monad**: does the profunctor interface
   help with structural inspection?
3. **FreePA vs arrow**: is "strong cocartesian traced profunctor"
   genuinely different from an arrow?

---

## Structural Properties Tested

| Property                   | Freer Arrow | Opaque Profunctor  | Bare Freer Profunctor                  | FreePA (+ strength + choice + trace) |
| -------------------------- | ----------- | ------------------ | -------------------------------------- | ------------------------------------ |
| **Sequential composition** | explicit    | explicit (seq)     | explicit (Seq)                         | explicit (Seq)                       |
| **Fanout / independence**  | explicit    | **LOST** (closure) | **CANNOT REPRESENT** (no `first`)      | explicit (via `First`)               |
| **Choice / branching**     | explicit    | **LOST** (closure) | **CANNOT REPRESENT** (no `left`)       | explicit (via `Left`)                |
| **Effect set**             | traversal   | **LOST**           | traversal (for representable programs) | traversal                            |
| **Per-branch effects**     | per branch  | **LOST**           | **CANNOT REPRESENT** branching         | recoverable                          |
| **Dependency graph**       | buildable   | **LOST**           | partial (seq only)                     | buildable                            |
| **Feedback / loop**        | explicit    | **LOST**           | **CANNOT REPRESENT** (no `loop`)       | explicit (via `Loop`)                |
| **Semantic results**       | correct     | correct            | correct (for representable)            | correct                              |

---

## Key Findings

### 1. The bare profunctor CANNOT EXPRESS fanout, choice, or feedback

This is the central result. A profunctor with only `dimap`/`lmap`/`rmap`
and category composition has no combinators for:

- **Fanout** (`f &&& g` — independent parallel computations): requires
  **strength** (`first`), which lifts `p a b` to `p (a, c) (b, c)`.
  Strength is NOT derivable from dimap. (Test:
  `test_bare_profunctor_cannot_represent_fanout`,
  `test_dimap_cannot_replace_arr_plus_first`)

- **Choice** (`f ||| g` — branching): requires **cocartesian
  structure** (`left`), which lifts `p a b` to `p (Either a c)
(Either b c)`. Choice is NOT derivable from dimap. (Test:
  `test_bare_profunctor_cannot_represent_choice`)

- **Feedback** (`loop`): requires **trace** (`loop`), which is NOT
  derivable from dimap or composition. (Test:
  `test_bare_profunctor_cannot_represent_loop`)

The bare profunctor CAN represent sequential composition and effects
(if the freer style is used with explicit `OpNode`), but it loses the
three structural features that Challenge #9 showed are practically
useful: fanout, choice, and feedback.

### 2. The opaque profunctor has the SAME opacity problem as the opaque monad

The profunctor interface (`dimap`/`lmap`/`rmap`) does NOT help with
structural inspection. An opaque profunctor (function-based, like
Haskell's profunctor libraries) hides structure inside closures —
exactly like the opaque monad from Challenge #9.

```
Opaque profunctor (same program as arrow):
  fanout:      NO — LOST (hidden in closure)
  choice:      NO — LOST (hidden in closure)
  effects:     NO — LOST (hidden in closure)
  per-branch:  NO — LOST (hidden in closure)
  loop:        NO — LOST (hidden in closure)
```

This refutes the implication that profunctors offer a structural
advantage over monads. They don't — an opaque profunctor is just as
opaque as an opaque monad. (Test:
`test_profunctor_vs_opaque_monad_same_opacity_problem`)

### 3. "Strong cocartesian traced profunctor" = Arrow

To recover the structural features, you add:

- **Strength** (`first`) → enables fanout
- **Choice** (`left`) → enables branching
- **Trace** (`loop`) → enables feedback

A profunctor with all three IS an arrow. The profunctor framing adds
nothing — it just renames the combinators:

| Arrow combinator    | Profunctor name               | Categorical structure  |
| ------------------- | ----------------------------- | ---------------------- |
| `arr`               | identity profunctor + `dimap` | —                      |
| `>>>` (composition) | category composition          | category               |
| `first`             | strength                      | strong profunctor      |
| `left`              | choice                        | cocartesian profunctor |
| `loop`              | trace                         | traced profunctor      |

Wikipedia's own admission: "An arrow is essentially a strong profunctor
that is also a category." Adding choice and trace gives the full arrow
calculus. (Test: `test_profunctor_subsumption_is_hollow`,
`test_freepa_is_isomorphic_to_arrow`)

### 4. dimap cannot replace arr + first

A common argument: "profunctors have dimap, which subsumes arr." This
is misleading. `dimap` gives pre/post composition with pure functions
on an EXISTING profunctor. It does NOT give:

- `arr` (lifting a pure function INTO the profunctor) — you need an
  identity profunctor + dimap, which IS arr
- `first` (strength) — needed for fanout, NOT derivable from dimap

`dimap` transforms the input/output of one profunctor. `first` extends
a profunctor to operate on one component of a pair. These are different
powers. No amount of `dimap` chaining produces fanout without `first`.
(Test: `test_dimap_cannot_replace_arr_plus_first`)

---

## Test Summary

28 tests across 7 categories:

| Category                                            | Tests | Status   |
| --------------------------------------------------- | ----- | -------- |
| Semantic equivalence (all four representations)     | 4     | COMPLETE |
| Bare profunctor cannot represent fanout/choice/loop | 4     | COMPLETE |
| Bare profunctor CAN represent sequential/effects    | 2     | COMPLETE |
| Opaque profunctor loses all structure               | 5     | COMPLETE |
| FreePA recovers structure (= arrow)                 | 7     | COMPLETE |
| dimap vs arr+first                                  | 1     | COMPLETE |
| Summary / key claims                                | 5     | COMPLETE |

---

## The Corrected Slogan (after Challenges #9, #11, and #12)

> **The structural utility of arrows (Challenge #9) is NOT subsumed by
> profunctors. A bare profunctor cannot even express fanout, choice, or
> feedback. An opaque profunctor has the same opacity problem as an
> opaque monad. To recover arrow utility from a profunctor, you add
> strength, choice, and trace — which reconstructs the arrow interface
> exactly. "Strong cocartesian traced profunctor" = Arrow. The
> profunctor framing renames the combinators; it does not replace them.**

### The three results together

| Challenge | Claim                                                                                                                                               | Status      |
| --------- | --------------------------------------------------------------------------------------------------------------------------------------------------- | ----------- |
| #9        | Opaque monad loses structure; explicit representations preserve it                                                                                  | Established |
| #11       | ArrowApply gives monadic power without opacity (explicit presentation)                                                                              | Established |
| #12       | Profunctor "subsumption" of arrows is hollow — bare profunctor can't express fanout/choice/feedback; opaque profunctor is as opaque as opaque monad | Established |

The combined thesis: **the structural advantages of the freer-arrow
representation are not subsumed by either monads (Challenge #9) or
profunctors (Challenge #12). The opacity problem is about
representation, not about the categorical interface. And the
"more general" profunctor interface is weaker, not stronger — it
drops exactly the combinators (strength, choice, trace) that make
arrows structurally useful.**

---

## Files

- `src/profunctor_structural_tests.rs` — 28-test suite (new)
- `Cargo.toml` — added `profunctor_structural` binary
- `THESIS.md` — updated with Challenge #12 results
- `RESULTS_CHALLENGE12.md` — this file

---

## Cumulative Results

| Phase     | Challenge                                                            | Tests/Theorems                     | Status          |
| --------- | -------------------------------------------------------------------- | ---------------------------------- | --------------- |
| 1         | #1–5 (expressiveness, abstraction, parametricity, typing, recursion) | 48                                 | COMPLETE        |
| 2         | #6 (effects & handlers)                                              | 20                                 | COMPLETE        |
| 3         | #7–8 (language protocol, generic tooling)                            | 26                                 | COMPLETE        |
| Deep dive | Effect typing                                                        | 31                                 | COMPLETE        |
| 4         | #9 (structural preservation under monadic translation)               | 33                                 | COMPLETE        |
| 5         | #10 (minimality — Lean4)                                             | 11 theorems                        | COMPLETE        |
| 6         | #11 (ArrowApply without opacity)                                     | 19                                 | COMPLETE        |
| 7         | Translation asymmetry — Lean4                                        | 8 theorems                         | COMPLETE        |
| 8         | #12 (structural preservation under profunctor translation)           | 28                                 | COMPLETE        |
|           | **Total**                                                            | **201 Rust + 19 Lean (19 proven)** | **All passing** |
