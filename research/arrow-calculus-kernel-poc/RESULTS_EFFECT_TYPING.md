# Effect Typing Deep Dive — Experimental Results

## Status: ✅ EFFECT TYPING COMPLETED

Date: 2026-09-02
Current Phase: Deep Dive (Effect Typing for Arrows) — **COMPLETE**
Focus: Row types / effect inference for arrow operations; handlers as effect
eliminators; unhandled-effect detection; polymorphic effect rows

---

## Experiment Completed

### ✅ Effect Typing for Arrows

**Goal:** Show that we can statically infer the **effect row** of an arrow
computation — which operations it may perform — without running it, and that
handlers act as **effect eliminators** that remove their owned operations
from the row. This is the arrow-calculus analogue of effect inference in
algebraic-effect systems (Bauer & Pretnar, Frank, Koka).

**Model:** The freer-arrow `Comp = Pure v | Op op arg k` from Phase 2 uses
closure continuations (`Rc<dyn Fn>`), which are not statically traversable.
For inference we use a **static computation tree** `IComp` that mirrors
`Comp` but stores continuations as explicit sub-trees (`Box<IComp>`):

```rust
pub enum IComp {
    Pure(IValue),
    Op(IOp, IValue, Type, Box<IComp>),  // op, arg, result type, continuation
}
```

The effect of a tree is the set of operations appearing in it; the type is
the type of the rightmost `Pure`:

```rust
pub fn infer_effect(comp: &IComp) -> EffectType {
    match comp {
        IComp::Pure(v) => EffectType { ty: type_of_value(v), effect: Effect::empty() },
        IComp::Op(op, _arg, _rt, k) => {
            let k_et = infer_effect(k);
            EffectType {
                ty: k_et.ty,
                effect: Effect::singleton(*op).union(&k_et.effect),
            }
        }
    }
}
```

An effect row is a set of operations:

```rust
pub struct Effect { ops: HashSet<IOp> }   // ∅ | {Get, Put} | {Read, Write} | ...
```

A handler _removes_ its owned operations from the effect row (handler as
effect eliminator), and pass-through leaves foreign operations in place:

```rust
pub fn effect_after_handler(comp_effect: &Effect, handled_ops: &Effect) -> Effect {
    comp_effect.difference(handled_ops)   // ε \ handled
}
```

**Operation signatures (effect-typed):**

```
get    : ()       ~> State  / {Get}
put    : State    ~> ()     / {Put}
read   : ()       ~> String / {Read}
write  : String   ~> ()     / {Write}
throw  : String   ~> α      / {Throw}     -- α polymorphic; never returns
pure v : τ        ~> τ      / ∅
```

**Components implemented:**

- `Effect` — effect row (set of operations) with `empty`, `singleton`,
  `insert`, `contains`, `union`, `difference`, `is_subset`, `is_empty`
- `EffectType` — a value type paired with an effect row (`τ / ε`)
- `IComp` / `IValue` — static computation tree mirroring the freer arrow,
  with `Received(Type)` values for operation results handed to continuations
- `infer_effect` — effect + type inference by tree traversal
- `effect_after_handler` / `effect_after_stack` — handler effect elimination
- `check_safety` / `check_computation` — unhandled-effect detection (static
  counterpart of Phase 2's `RunError::UnhandledOp`)
- `RowEffect` — polymorphic effect rows with a row-variable tail `ρ`,
  including handler elimination that preserves the row variable and row
  unification

**Test Results:**

```
Effect set operations (4 tests):
✅ empty + insert + contains (display ∅)
✅ union of two effect sets
✅ difference (handler elimination): {Get,Put,Read} \ {Get,Put} = {Read}
✅ subset checking

Effect inference on pure computations (3 tests):
✅ pure 42            -> Int / ∅
✅ pure true          -> Bool / ∅
✅ pure product/list  -> (Int × Bool) / ∅, [Int] / ∅

Effect inference on single-operation computations (4 tests):
✅ get        -> State / {Get}
✅ put 5      -> () / {Put}
✅ read       -> String / {Read}
✅ throw "err": a / {Throw}  (polymorphic result type — never returns)

Effect inference on composed computations (4 tests):
✅ get >>> put        -> () / {Get, Put}
✅ read >>> write     -> () / {Read, Write}
✅ get >>> throw      -> a / {Get, Throw}
✅ all five ops       -> a / {Get, Put, Read, Write, Throw}

Handler effect elimination (5 tests):
✅ handle_state on {Get, Put}            -> ∅
✅ handle_state on {Get, Put, Read}      -> {Read}  (pass-through)
✅ handle_io on {Read, Write}            -> ∅
✅ handle_exception on {Throw}           -> ∅
✅ handle_exception on {Get, Throw}      -> {Get}   (pass-through)

Handler stacking (3 tests):
✅ state ∘ io on {Get, Put, Read, Write}          -> ∅
✅ state ∘ exception on {Get, Put, Throw}         -> ∅
✅ full stack on {Get, Put, Read, Write, Throw}   -> ∅

Effect safety / unhandled detection (3 tests):
✅ {Get} with no handler            -> unhandled: {Get}
✅ {Get, Read} handled by only state -> unhandled: {Read} remains
✅ all-five with full stack         -> safe (no unhandled effects)

Polymorphic effect rows (5 tests):
✅ row {Get, Put, ρ} display + structure
✅ handle_state on {Get, Put, ρ} -> {ρ}  (row var preserved; foreign ops pass through)
✅ unify {Get,Put} with {Get,Put} -> {Get,Put}  (ground equal)
✅ unify {Get} with {Put} -> ⊥  (ground unequal fails)
✅ unify {Get, ρ} with {Put} -> {Get, Put, ρ}  (ρ absorbs Put)

Total: 31/31 effect typing tests PASSED ✅
```

---

## Summary: Effect Typing for Arrows

### Claim Tested

> Can we statically infer the effect row of an arrow computation without
> running it? Are handlers effect eliminators? Can a handler stack be checked
> for completeness — is any effect left unhandled — purely from inferred
> effect rows?

### What We've Shown

- ✅ The effect row of a freer-arrow computation is inferred statically by
  traversing a static computation tree (`IComp`): `Pure` contributes `∅`,
  each `Op` contributes `{op} ∪ effect(k)`. Effects accumulate by union.
- ✅ Handlers are **effect eliminators**: `handle_state` removes `{Get, Put}`
  from the row, `handle_io` removes `{Read, Write}`, `handle_exception`
  removes `{Throw}`. This is exactly the typing counterpart of Phase 2's
  pass-through semantics.
- ✅ Pass-through is reflected in the types: foreign operations remain in the
  effect row after a handler runs (e.g. `handle_state` on `{Get, Put, Read}`
  leaves `{Read}`).
- ✅ A handler stack is checked for completeness by set difference: the
  computation is safe to run iff the remaining row is `∅`. A non-empty
  remaining row is the **static** counterpart of Phase 2's runtime
  `UnhandledOp` error — the same notion of "unhandled effect", caught before
  execution.
- ✅ Polymorphic effect rows with a row variable `ρ` model unknown tails of
  foreign operations; a handler eliminates its own ops from the known part
  and leaves `ρ` intact; rows unify by absorbing extra ops into `ρ`.

### What This Means

**Effect inference is not a monad-specific feature.** The same freer-arrow
tree that Phase 2 interprets at runtime can be traversed statically to infer
its effect row, and the handler-as-eliminator rule falls out directly from
pass-through: a handler removes exactly the operations it owns. This places
arrow operations + handlers on the same footing as algebraic-effect systems
(Bauer & Pretnar, Frank, Koka) with respect to static effect reasoning — no
monad, transformer, or effect-monad primitive is needed.

The unhandled-effect detection is particularly telling: Phase 2's `run`
returns `RunError::UnhandledOp(op)` at runtime when an operation reaches the
top of the stack unhandled; this deep dive's `check_safety` returns
`Unhandled(ops)` at **compile time** from the inferred effect row and the
handler stack. Same concept, two time scales — and the static check is
derivable purely from the structure of the freer arrow.

### Key Technical Achievements

- **Static computation tree (`IComp`):** the traversable analogue of the
  freer-arrow `Comp`, with continuations as explicit sub-trees and
  `Received(Type)` values for operation results handed to continuations
- **Effect-as-set inference:** `infer_effect` walks the tree collecting
  operations by union — the arrow analogue of effect accumulation in
  `bind`/`>>>`
- **Handler-as-eliminator:** `effect_after_handler = ε \ ops(handler)` — the
  typing rule that mirrors pass-through
- **Stack safety check:** `check_computation` infers the effect, applies the
  stack by repeated difference, and reports unhandled operations — the static
  counterpart of `run`'s `UnhandledOp`
- **Row-polymorphic effects (`RowEffect`):** row variable `ρ` for unknown
  tails, handler elimination preserving `ρ`, and row unification with
  absorption

---

## Comparison: Arrow Effect Typing vs Algebraic-Effect Systems

| Aspect            | Frank / Koka / Eff                | Arrow effect typing                                     |
| ----------------- | --------------------------------- | ------------------------------------------------------- |
| Effect primitive  | Algebraic operation + handler     | Arrow operation + handler (freer arrow)                 |
| Effect row        | Set/row of operation labels       | `Effect` = `HashSet<IOp>` (same structure)              |
| Inference         | Traverse computation, collect ops | `infer_effect` traverses `IComp`, unions ops            |
| Handler semantics | Eliminates handled ops from row   | `effect_after_handler = ε \ ops(H)` (identical)         |
| Pass-through      | Foreign ops remain in row         | Foreign ops remain in row (identical)                   |
| Polymorphism      | Row variable `ρ`                  | `RowEffect` with `ρ` tail + unification (identical)     |
| Unhandled effect  | Runtime / static error            | `check_safety` (static) ↔ `run` `UnhandledOp` (runtime) |
| Foundation        | Monad / free monad                | Freer arrow (no monad primitive)                        |

**Verdict:** Arrow operations + handlers support the same effect-row
inference and handler-as-eliminator discipline as algebraic-effect systems,
without introducing a monad or effect monad as a primitive. The effect row is
inferred from the structure of the freer arrow alone; handlers eliminate
their owned operations by the same pass-through rule that drives their
runtime semantics.

---

## Cumulative Results (Phases 1–3 + Effect Typing Deep Dive)

| Challenge          | Question                                      | Result       | Tests    |
| ------------------ | --------------------------------------------- | ------------ | -------- |
| #1 Expressiveness  | Can arrows express basic functional patterns? | ✅ YES       | 3/3      |
| #2 Abstraction     | Higher-order patterns without lambda?         | ✅ YES       | 10/10    |
| #3 Parametricity   | Generic programming without lambda?           | ✅ YES       | 14/14    |
| #4 Typing          | Hindley-Milner inference on arrows?           | ✅ YES       | 15/15    |
| #5 Recursion       | State machines replace recursive functions?   | ✅ YES       | 2/2      |
| #6 Effects         | Handler-based effects replace monads?         | ✅ YES       | 20/20    |
| #7 Metaprogramming | First-class Language protocol?                | ✅ YES       | 26/26    |
| #8 Tooling         | Generic language-agnostic tooling?            | ✅ (with #7) | (shared) |
| Deep Dive          | Effect typing / row inference for arrows?     | ✅ YES       | 31/31    |

**Total: 121/121 tests passing** (90 prior + 31 new), zero compiler warnings,
no external dependencies.

---

## Files Created/Updated

- `src/effect_typing_tests.rs` — 31-test effect typing engine (effect rows,
  inference, handler elimination, stacking, safety, polymorphic rows)
- `Cargo.toml` — added `effect_typing` binary
- `FORMALISM.md` — "Effect Typing (Deep Dive)" section with effect row
  syntax, typing rules for operations and handlers, inference algorithm, and
  polymorphic rows
- `WORKING_NOTES.md` — effect-typing completion status, key findings, verdict
  tracker updated
- `RESULTS_EFFECT_TYPING.md` — this file

---

## Conclusion

**The effect-typing deep dive is complete.** Static effect inference — long
presented as a benefit of algebraic-effect systems over monads — arises
naturally from the freer-arrow representation. The effect row of a
computation is the set of operations suspended in its tree, inferred by a
single traversal; handlers eliminate their owned operations from the row by
the same pass-through rule that governs their runtime behaviour; and a
handler stack is complete iff the remaining row is empty — the static
counterpart of Phase 2's unhandled-operation runtime error.

Row-polymorphic effects (the `ρ` tail) generalize this to unknown foreign
operations, matching Koka/Frank, again with no monad primitive — only arrow
operations, handlers, and set difference.

**Next direction:** Refinement/dependent types on arrow operations, larger
language instances, or a generic tracer/step-by-step evaluator as a fourth
tool.

---

**Date:** 2026-09-02
**Status:** Effect Typing Deep Dive COMPLETE ✅
**Next:** Refinement types, larger languages, or a generic tracer
