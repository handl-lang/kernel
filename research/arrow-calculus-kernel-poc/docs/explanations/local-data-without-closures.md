# Local Data Without Closures

## The short version

The arrow calculus has no `λ`, so it has no binder, so it has nothing
to capture. "Closure" is a non-concept here. Local data is real and
first-class, but it lives in **product slots**, **feedback channels**,
and **handler state** — all explicit, all traversable, none hidden in a
captured environment.

This is not an accident or a limitation we work around. It is the
central design move that makes the calculus structurally inspectable.

---

## Why there are no closures

A closure is two things bundled: a function body and the environment it
captured. The arrow calculus has neither half:

- **No function body** — the syntax has no `λx. e` form. The five
  independent primitives are `arr`, `comp (>>>)`, `first`, `left`,
  `loop`. None of them binds a variable.
- **No environment to capture** — with no binder, there are no free
  variables, so there is nothing to close over.

What you might call a "function" here is an arrow `τ ~> σ`: a value that
takes a `τ` and produces a `σ`. It does not _remember_ anything beyond
what is wired into it. The wiring is the program.

This is the deliberate opposite of the monadic tradition, where `bind`
threads a continuation `k : Value -> Comp` and that `k` is an opaque
host-language closure. The direct-bind impossibility result
([`direct-bind-impossibility.md`](../../direct-bind-impossibility.md))
shows that this opacity is not cosmetic: a continuation that only sees
the predecessor's output (never the original input) _cannot_ faithfully
encode `fanout` or `loop`. Closures don't just hide structure — they
destroy the ability to represent certain arrow programs at all.

---

## Where local data lives instead

Three places, each a different scope of "local":

### 1. Product slots — `first`

`first f : (τ × ρ) ~> (σ × ρ)` runs `f` on one component and passes the
other through untouched. Your "local" is the `ρ` half of a tuple.

Stack `first`s and slip in `arr swap` to juggle several locals. The
data is right there in the wiring — visible to effect inference,
visible to the dependency graph, visible to the proof-graph reading.

### 2. Feedback channels — `loop`

```
loop f : τ ~> σ
  where f : (τ × ρ) ~> (σ × ρ)
```

The `ρ` is your mutable cell, threaded across iterations. This is how
factorial, counters, and recursion work: the accumulator _is_ the `ρ`.

```text
factorial : Int ~> Int
factorial = loop step
  where step : (Int, (Int, Int)) ~> (Int, (Int, Int))
        step = arr (λ(n, (acc, _)). …)   -- λ only inside arr; not a binder of the calculus
```

See [`FORMALISM.md` §Example 5](../../FORMALISM.md) for the full
factorial. The "local state" of the recursion — accumulator, counter,
termination flag — is a tuple in the `ρ` channel, updated each
iteration. Nothing is hidden.

### 3. Handler state — `Get` / `Put`

For local data that spans the whole program (not just one loop),
declare operations and let a handler own the cell:

```
operation Get : ()       ~> State
operation Put : State    ~> ()
```

`handle_state` threads `s` through pass-through; foreign operations
rebuild with the handler re-applied to the continuation. This is the
effectful version of (2), lifted out of the program text and into the
handler stack. The program just _mentions_ `Get`/`Put`; the cell lives
in the handler.

See [`FORMALISM.md` §Effects & Handlers](../../FORMALISM.md) for the
full pass-through semantics and handler-stacking rules.

---

## Why this matters

A closure hides data _and_ hides structure in one move. The arrow
calculus refuses to do either: the data is in a tuple, the structure is
in the wiring, and both are explicit.

That is why three otherwise-unrelated properties all hold at once:

- **Effect inference** — the effect row is just the set of operations
  suspended in the freer-arrow tree. You can walk it because there are
  no closures to walk _into_.
- **Dependency graphs** — `fanout` shows two independent branches; no
  closure obscures the edge structure.
- **λ-free Curry–Howard** — the graph _is_ the proof object. The proof
  structure is carried by wiring (`comp` = cut, `first` = ∧-functoriality,
  `left` = ∨-functoriality, `loop` = trace). An opaque monad cannot be a
  proof object because its structure is hidden in closures; an arrow
  graph can, because it has none.

The one place closures appear in the project — the Rust `Rc<dyn Fn>`
continuation in the runtime `Comp` — is called out as an "architectural
blemish" in [`THESIS.md` §The IComp Question](../../THESIS.md). The fix
is not a third representation; it is to defunctionalise that
continuation into the explicit sub-tree form `IComp`, and treat _that_
as canonical. The closure was always the thing to be eliminated, never
a primitive.

---

## In practice

| You want…                         | Use…                         | Where the data lives            |
| --------------------------------- | ---------------------------- | ------------------------------- |
| A local for one sub-computation   | `first f`                    | the `ρ` slot of a product       |
| A mutable cell across iterations  | `loop f`                     | the `ρ` channel of the feedback |
| A mutable cell across the program | `Get`/`Put` + `handle_state` | the handler's state parameter   |

No closure. No hidden environment. No opacity. That is the whole point.
