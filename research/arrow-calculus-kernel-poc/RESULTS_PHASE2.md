# Phase 2 Experimental Results

## Status: ✅ Challenge #6 COMPLETED

Date: 2026-08-31
Current Phase: 2 (Effects & Handlers — Challenge #6) — **COMPLETE**
Focus: Handler-based State, IO, Exception operations; multi-effect composition; comparison to monad transformers

---

## Experiment Completed

### ✅ Experiment 8: Effects & Handlers (CHALLENGE #6)

**Goal:** Show that monadic effects (State, IO, Exceptions) can be encoded as
arrow operations + handlers, that multiple effects compose as cleanly as
monad transformers, and that no monad primitive is required.

**Model:** A _freer arrow_. A computation is a tree of suspended operations,
each carrying a continuation:

```rust
pub enum Comp {
    Pure(Value),
    Op(Op, Value, Rc<dyn Fn(Value) -> Comp>),  // perform op, continue with k
}
```

A handler walks the tree, intercepting its own operations and **passing
through** foreign ones by rebuilding the continuation with itself re-applied.
Pass-through is what lets handlers stack independently.

```rust
pub fn handle_state(comp: Comp, state: Value) -> Comp {
    match comp {
        Comp::Pure(v) => Comp::Pure(v),
        Comp::Op(Op::Get, _, k)  => handle_state(k(state.clone()), state),
        Comp::Op(Op::Put, s, k)  => handle_state(k(Value::Unit), s),
        // Foreign op: rebuild, re-apply handler to the resumed continuation.
        Comp::Op(op, arg, k)     => Comp::Op(op, arg,
            Rc::new(move |r| handle_state(k(r), state.clone()))),
    }
}
```

**Operation signatures:**

```
operation Get   : ()     ~> State      -- read current state
operation Put   : State  ~> ()         -- overwrite state
operation Read  : ()     ~> String     -- read one input
operation Write : String ~> ()         -- emit one output
operation Throw : String ~> _          -- raise an exception (aborting)
```

**Handlers implemented:**

- `handle_state` — threads state through Get/Put
- `handle_state_pair` — like `handle_state` but returns `(result, final_state)`,
  making handler _order_ observable
- `handle_io` — threads inputs/outputs through Read/Write
- `handle_exception` — catches Throw, yields `Right v` / `Left msg`

**Test Results:**

```
State (4 tests):
✅ counter_program under handle_state(init=4)        = 5
✅ increment_n(3) from 0                              = 3
✅ put 7 >>> get                                      = 7
✅ pure passes through state handler unchanged

Exception (4 tests):
✅ safe_div(10, 2) under handle_exception             = Right 5
✅ safe_div(10, 0) under handle_exception             = Left "divide by zero"
✅ throw aborts the continuation (subsequent pure never runs)
✅ mid-program catch: handle_exception on a sub-comp, branch on Either

IO (3 tests):
✅ read returns the next input
✅ write collects outputs into the buffer
✅ read >>> write echoes one input

Multi-effect composition (5 tests):
✅ State + IO: read_and_accumulate twice (inputs 10, 20) from state 0 = 30
✅ State + Exception: success preserves state (Right 10)
✅ State + Exception: throw aborts before state update (Left)
✅ State + IO + Exception: capped accumulate, cap=100, inputs 30+40 = Right 70
✅ State + IO + Exception: cap=50, inputs 30+40       = Left "cap exceeded"

Handler ordering vs monad transformers (1 test):
✅ exception-outside-state (StateT(Except)):  throw discards state -> Left
✅ state-outside-exception (ExceptT(State)):  state preserved -> Product(Left, 10)

Pass-through & unhandled (3 tests):
✅ unhandled Get (no state handler) -> runtime error UnhandledOp(Get)
✅ state handler passes Read through intact for an outer IO handler
✅ arr (+1) >>> counter_program composes pure + effectful arrows

Total: 20/20 effects & handler tests PASSED ✅
```

---

## Summary: Challenge #6 (Effects & Handlers)

### Claim Tested

> Can handler-based effects (State, IO, Exception) replace monads? Do they
> compose as cleanly as monad transformers?

### What We've Shown

- ✅ State, IO, and Exception each arise from operations + a handler — no monad
  primitive, no `bind`, no transformer type
- ✅ Multiple effects compose by stacking handlers via ordinary function
  composition (pass-through does the threading)
- ✅ Handler order is observable and corresponds _exactly_ to monad
  transformer order (StateT(Except) vs ExceptT(State))
- ✅ Mid-program `try/catch` is just a handler applied to a sub-computation,
  branching on the resulting `Either` — no special syntax
- ✅ Unhandled operations surface as runtime errors, exactly like unhandled
  effects in algebraic-effect systems

### What This Means

**Monads are not a necessary primitive for effects.** All three effect
behaviours (state threading, IO, exceptions) and their composition emerge
from a single mechanism: operations suspended in a freer arrow, interpreted
by composable handlers. The handler stack plays the role of the transformer
stack, with the same observable semantics, but expressed as ordinary
function composition rather than a tower of newtypes.

### Key Technical Achievements

- **Freer-arrow representation:** `Comp = Pure v | Op op arg k` — the arrow
  analogue of a free monad, with continuations in arrow position
- **Pass-through semantics:** the single rule that makes handlers composable
  and order-aware
- **`handle_state_pair`:** exposes final state alongside the result, making
  transformer-order semantics directly observable
- **Mid-program catch:** demonstrates handlers are first-class functions over
  computations, not a separate language construct

---

## Comparison: Handlers vs Monad Transformers

| Aspect           | Monad transformers                       | Arrow handlers                          |
| ---------------- | ---------------------------------------- | --------------------------------------- |
| Effect primitive | `Monad`/`MonadTrans` type classes        | Operations + handler functions          |
| Stacking         | Newtype tower (`StateT s (ExceptT e m)`) | Function composition                    |
| Order semantics  | Determined by transformer order          | Determined by handler order (identical) |
| Reordering       | Rewrite the type                         | Reorder the composition                 |
| Adding an effect | New transformer + lift boilerplate       | Add a handler to the stack              |
| Per-effect code  | `lift`, `MonadState`, `MonadError`       | One handler per effect, no lifting      |
| Catch / recovery | `catchError`, `ExceptT` plumbing         | `handle_exception` on a sub-comp        |

**Verdict:** Handler composition is at least as clean as monad transformers,
with no loss of expressiveness, and strictly less boilerplate (no `lift`
nesting, no newtype wrapping). The same program text runs under any handler
stack; only the stack determines semantics.

---

## Cumulative Results (Phase 1 + Phase 2)

| Challenge         | Question                                      | Result | Tests |
| ----------------- | --------------------------------------------- | ------ | ----- |
| #1 Expressiveness | Can arrows express basic functional patterns? | ✅ YES | 3/3   |
| #2 Abstraction    | Higher-order patterns without lambda?         | ✅ YES | 10/10 |
| #3 Parametricity  | Generic programming without lambda?           | ✅ YES | 14/14 |
| #4 Typing         | Hindley-Milner inference on arrows?           | ✅ YES | 15/15 |
| #5 Recursion      | State machines replace recursive functions?   | ✅ YES | 2/2   |
| #6 Effects        | Handler-based effects replace monads?         | ✅ YES | 20/20 |

**Total: 64/64 tests passing** (100% success rate)

---

## Files Created/Updated

- `src/effects_handlers_tests.rs` — 20-test effects & handler engine
- `Cargo.toml` — added `effects_handlers` binary
- `FORMALISM.md` — operations + handler semantics section
- `WORKING_NOTES.md` — Challenge #6 verdict logged
- `RESULTS_PHASE2.md` — this file

---

## Conclusion

**Phase 2 is complete.** Effects — long considered the stronghold of monads
and monad transformers — arise naturally from arrow operations + handlers.
The freer-arrow + pass-through model recovers State, IO, and Exception
behaviour, composes them via ordinary function composition, and reproduces
the exact observable semantics of monad transformer stacks. No monad,
transformer, or `bind` primitive was introduced.

**Next direction:** Phase 3 (Real-World Features — Challenge #8: generic,
language-agnostic tooling via a first-class Language protocol), or a deep
dive into effect typing (row types / effect inference for arrows).

---

**Date:** 2026-08-31
**Status:** Phase 2 COMPLETE ✅
**Next:** Phase 3 (Real-World Features) or effect-typing deep dive
