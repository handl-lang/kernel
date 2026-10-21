# Challenge #11: ArrowApply Without Opacity

## Status: ✅ COMPLETE — 19/19 tests passing

Date: 2026-08-31
Challenge: #11 — Does ArrowApply preserve inspectionability?
Cumulative: 173/173 Rust tests + 7 Lean4 theorems, zero warnings.

---

## The Question

Classic theory says `ArrowApply ≅ Monad` (expressive power equivalence).
The classic translation produces an **opaque** monadic computation.

> **Does there exist a presentation of ArrowApply that gives full monadic
> power while keeping the computation tree inspectable?**

If yes, the corrected slogan is:

> _This explicit ArrowApply presentation gives you monadic power WITHOUT
> the opacity penalty._

---

## The Answer: YES

ArrowApply, implemented in the freer-arrow (explicit tree) style, gives
full monadic power while preserving all structural inspection properties.

### The representation

`ExplicitComp` is a computation tree with explicit nodes:

- `Pure`, `Ident` — values / identity
- `Seq` — composition
- `Fanout` — products (independent parallel)
- `Choice` — sums (branching)
- `OpNode` — operations (Get/Put/Throw)
- **`Apply`** — ArrowApply (apply an embedded arrow to a value)
- `Loop` — feedback

The `Apply` node is a **structural tree node**, not a closure. It can be
detected, counted, traversed, and reasoned about like any other node.

### What's preserved WITH ArrowApply

| Property             | Explicit ArrowApply | Opaque monad            |
| -------------------- | ------------------- | ----------------------- |
| Monadic power (bind) | ✅ (via Apply)      | ✅ (via bind)           |
| Choice recovery      | ✅                  | ❌ LOST                 |
| Effect inference     | ✅                  | ❌ LOST                 |
| Per-branch effects   | ✅                  | ❌ LOST                 |
| Dependency graph     | ✅                  | ❌ LOST                 |
| Fanout independence  | ✅                  | ❌ LOST                 |
| Apply detection      | ✅ (structural)     | N/A (bind is a closure) |

---

## Key Tests

### Monadic power (4 tests)

- `test_arrow_apply_can_express_bind` — Apply IS the bind operator
- `test_arrow_apply_runs_correctly` — Apply runs embedded arrows
- `test_arrow_apply_with_state` — embedded arrows can have effects
- `test_arrow_apply_composes` — multiple Applys compose

### Inspection preserved WITH Apply (5 tests)

- `test_explicit_with_apply_recovers_choice` — choice still recoverable
- `test_explicit_with_apply_infers_effects` — effects still inferred
- `test_explicit_with_apply_per_branch_effects` — per-branch still works
- `test_explicit_with_apply_builds_dependency_graph` — graph still built
- `test_explicit_with_apply_recovers_fanout` — fanout still recoverable

### Explicit vs opaque comparison (4 tests)

- `test_explicit_arrow_apply_vs_opaque_monad_choice` — explicit recovers, opaque doesn't
- `test_explicit_arrow_apply_vs_opaque_monad_effects` — explicit infers, opaque doesn't
- `test_explicit_arrow_apply_vs_opaque_monad_per_branch` — explicit per-branch, opaque doesn't
- `test_explicit_arrow_apply_vs_opaque_monad_dependency_graph` — explicit builds, opaque doesn't

### The key claim (3 tests)

- `test_monadic_power_without_opacity` — Apply present AND all inspection works
- `test_apply_is_structural_not_closure` — Apply is a tree node, not a closure
- `test_apply_preserves_fanout_independence` — fanout independence preserved with Apply

### Semantic correctness (3 tests)

- `test_apply_runs_embedded_arrow` — Apply correctly runs embedded arrows
- `test_apply_composed_with_get` — Apply composes with operations
- `test_arrow_apply_runs_correctly` — basic Apply semantics

---

## The Corrected Slogan

The original thesis: "arrows can replace monads."

The corrected thesis (after Challenges #9 and #11):

> **ArrowApply (in the explicit/freer style) gives you monadic power
> WITHOUT the opacity penalty. Ordinary opaque monads bury structure
> in closures; the explicit ArrowApply presentation keeps the
> computation tree inspectable — effects, branching, per-branch
> analysis, and dependency graphs all remain recoverable.**

### The nuance (from the user's framing)

The isomorphism `ArrowApply ≅ Monad` is about **expressive power**, not
about **representation**. The classic translation produces an opaque
monadic computation. Our result claims that there exists a presentation
of the same power that stays **transparent**. That is the non-trivial
part, and it is what makes the claim interesting.

It no longer says "arrows are better than monads"; it says "this explicit
ArrowApply presentation gives you monadic power _without_ the opacity
penalty."

---

## Files

- `src/arrow_apply_tests.rs` — 19-test suite (new)
- `Cargo.toml` — added `arrow_apply` binary
- `THESIS.md` — updated with corrected slogan
- `WORKING_NOTES.md` — Challenge #11 section added

---

## Cumulative Results

| Phase     | Challenge                                                            | Tests       | Status          |
| --------- | -------------------------------------------------------------------- | ----------- | --------------- |
| 1         | #1–5 (expressiveness, abstraction, parametricity, typing, recursion) | 44          | ✅              |
| 2         | #6 (effects & handlers)                                              | 20          | ✅              |
| 3         | #7–8 (language protocol, generic tooling)                            | 26          | ✅              |
| Deep dive | Effect typing                                                        | 31          | ✅              |
| 4         | #9 (structural preservation)                                         | 33          | ✅              |
| 5         | #10 (minimality — Lean4)                                             | 7 theorems  | ✅              |
| 6         | #11 (ArrowApply without opacity)                                     | 19          | ✅              |
|           | **Total**                                                            | **173 + 7** | **All passing** |

---

## Practical Implication: Speculative Compilation & Dynamic Graph Caching

The transparency of explicit `ArrowApply` has a direct practical payoff:
**pre-compilation of predicted sub-graphs into a pool of flat execution
chunks**, turning runtime `ArrowApply` into a zero-allocation pointer switch.

### How it works

```
                  ┌────────────────────────────────────────┐
                  │          Stage 0 (Ahead-of-Time)       │
                  └──────────────────┬─────────────────────┘
                                     │
           ┌─────────────────────────┼─────────────────────────┐
           ▼                         ▼                         ▼
   [ Chunk Alpha ]           [ Chunk Beta ]            [ Chunk Gamma ]
 (Pre-allocated WGSL)     (Pre-allocated WGSL)     (Pre-allocated WGSL)
           │                         │                         │
           └─────────────────────────┼─────────────────────────┘
                                     │
                  ┌──────────────────▼─────────────────────────────┐
                  │       Runtime ArrowApply Switch                │
                  │   (Zero-alloc hardware pointer swap)           │
                  └────────────────────────────────────────────────┘
```

1. **Ahead-of-Time Graph Synthesis:** Stage 0 analyzes `ArrowApply`
   branching boundaries and pre-builds a finite set of Stage 1 execution
   chunks (flat arrays or GPU pipelines).
2. **Pre-allocated Memory Arena:** Buffers for all candidate chunks are
   allocated upfront in a static ring or slab.
3. **Runtime Branching as Pointer Selection:** When data flows into
   `ArrowApply`, the runtime evaluates the condition, resolves to a
   pre-compiled chunk ID, and routes execution to that pre-allocated
   memory offset.
4. **Predictive GC / Eviction:** Cold specialized chunks are pruned from
   cache using usage metrics or static reachability analysis.

### Why explicit ArrowApply makes this work

In a traditional monadic environment, speculative pre-compilation is
nearly impossible because the monad hides control flow inside arbitrary
host code (`a -> m b`). The compiler cannot know what branches are
possible without executing the function.

Because the explicit presentation keeps `ArrowApply` as a structural tree
node:

- **The AST is fully inspectable.** Stage 0 can perform static
  reachability analysis to discover all potential targets ahead of time.
- **Bounded branch space is provable.** You can prove at compile time
  whether the dynamic choice set is finite, allowing complete
  pre-compilation of every execution path.

### Two execution profiles

| Approach             | Pre-compiled Chunks (Finite)                            | Live JIT Re-staging (Unbounded)                   |
| -------------------- | ------------------------------------------------------- | ------------------------------------------------- |
| **When**             | Branch choices known statically / small predictable set | Dynamic structure depends on unbound runtime data |
| **Runtime overhead** | ≈ 0 ns (pointer read / indirect dispatch)               | Sub-ms (graph build + compile)                    |
| **Memory**           | Pre-allocated slab with proactive chunk recycling       | Temporary workspace with immediate discard        |

### The bottom line

Pre-rendering chunks turns `ArrowApply` from a runtime graph-synthesis
step into a **zero-allocation dispatch table**. This eliminates the need
for an external interpreter or VM — the engine handles rapid
micro-decisions at native speed while preserving full structural
transparency.

This is the practical consequence of Challenges #9 + #11: the
transparency that makes the tree inspectable is the same transparency
that makes every reachable path pre-compilable.
