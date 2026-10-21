# Arrow `rec` Region Typing Rule v0.1

## Status

Authoritative — v0.1 `rec` typing rule per ADR-0074 follow-up #2. Formalizes
the typing of `rec` regions around Paterson's `loop` model (ID.3).

This document specifies the formal typing rule for `rec { binding; ... }`
regions in the handl v0.1 surface syntax. It is the surface-level version of
the kernel `Loop` typing rule (ADR-0052, FORMALISM.md). It is referenced by
[ADR-0074 — Arrow Surface Syntax v0.1 — Redesign](../../project/adrs/0074-arrow-syntax-v0_1-surface-redesign.md)
as follow-up task #2, and is consistent with the
[Arrow Language Specification v0.1 §12.1](./ARROW_LANGUAGE_SPEC_V0_1.md) and the
[Arrow Desugaring Specification v0.1 §2](./ARROW_DESUGARING_V0_1.md).

---

## 1. Overview

The goal of this document is to formalize the typing of `rec { binding; ... }`
regions per ID.3, around Paterson's `loop` model. The `rec` region is the
surface form of the kernel `Loop` combinator (ADR-0052). The typing rule
specified here is the surface-level version of the kernel `Loop` typing rule.

The key property from ID.3 is:

- The region has a **state wire** and an **exit wire**.
- The **fixpoint is over the state**: the compiler must be able to assign a
  well-typed fixpoint to the state transition.
- **Termination is NOT checked at the type level** — it is a runtime/effect
  concern. A well-typed `rec` region may diverge at runtime; the type system
  only checks that the feedback graph is well-typed.
- **The type is the fixpoint of the state transition.** The region's type is
  the exit wire's type, with the state abstracted away (hidden in the feedback
  channel, like `loop` hides `S`).
- **No guard/`return` is required for well-typedness.** A `rec` region is
  well-typed if and only if a well-typed fixpoint exists for its state wires.
  A guard or `return` affects runtime termination, not type-level
  well-typedness.
- **A `rec` without a well-typed fixpoint is a compile error**, not a runtime
  divergence. If the state type is not stable across the feedback (e.g. a state
  wire feeds back as a different type), the typechecker rejects the region.

This is the same discipline the kernel applies to `loop` (ADR-0052); `rec` is
the surface syntax for the same idea.

---

## 2. The kernel `Loop` typing rule (background)

### 2.1 The `Loop` combinator

The kernel `Loop` combinator (ADR-0052, Paterson's `loop`) has the shape:

```text
loop : Arrow (A, S) (B, S) → Arrow A B
```

`loop f` takes an arrow `f : (A × S) ~> (B × S)` and feeds the second output
`S` back into the second input `S`; the first component becomes the externally
visible output. **`loop` is feedback, not iteration** (ADR-0052, "the `loop`
correction"). The state `S` is hidden in the feedback channel; the externally
visible type is `A ~> B`.

### 2.2 The kernel `Loop` inference rule

From FORMALISM.md §Type System, the `Loop` inference rule is:

```text
  Γ ⊢ f : (τ × ρ) ~> (σ × ρ)
────────────────────────────────── (Loop)
  Γ ⊢ loop f : τ ~> σ
```

Given `f : (A × S) ~> (B × S)`, `loop f : A ~> B`. The state type `S` (written
`ρ` in FORMALISM.md) appears in both the input and output of `f`; `loop`
hides it, exposing only `A ~> B`. The critical constraint is that the state
type `ρ` is the **same** on both sides of the arrow — the feedback channel
carries a value of type `ρ` from one iteration's output to the next
iteration's input. This is the type-level fixpoint condition: the state type
must be stable across the feedback edge.

### 2.3 Feedback semantics — causal/strict vs lazy/fixpoint

ADR-0052 §Feedback semantics specifies two interpretation strategies for
`Loop`, which disagree on read-before-write:

- **Causal/strict semantics.** The `State` output of one step is the `State`
  input of the _next_ step. A read of `State` in step _n_ sees the value
  written in step _n−1_. A read-before-write in the _same_ step reads the
  prior step's output (or an initial seed) — well-defined, not bottom. This
  is the state-machine reading.

- **Lazy/fixpoint semantics.** The `State` is a fixpoint: `loop f` solves
  `s = snd(f(a, s))` for the state `s`, then produces `fst(f(a, s))`. Under
  this reading, a read-before-write in the same "iteration" is a demand for
  `s` before it is defined — ill-founded (bottom) unless the fixpoint is
  productive (coinductive/final-coalgebra semantics).

**Which semantics does the `rec` typing rule assume?** The typing rule is
the **same under both semantics**. The difference between causal/strict and
lazy/fixpoint is a runtime interpretation concern (the handler's job,
ADR-0052), not a typing concern. The typing rule checks that a **well-typed
fixpoint exists** — i.e. that the state type is stable across the feedback
edge. The runtime semantics (causal vs fixpoint) is the handler's concern,
not the typing rule's.

This is stated explicitly in ADR-0052: "What the kernel fixes: `Loop { body }`
is a feedback channel — `body` has shape `(In, State) ~> (Out, State)`,
`Loop` hides `State`, exposing `In ~> Out`. What the handler fixes: the
interpretation strategy." The `rec` typing rule inherits this separation: it
fixes the type-level fixpoint check; the handler fixes the runtime semantics.

---

## 3. The `rec` region: structure and wires

### 3.1 Syntax

A `rec` region is a brace-delimited sequence of bindings:

```text
rec {
  b₁
  b₂
  ...
  bₙ
}
```

Each `bᵢ` is `nameᵢ = expressionᵢ`. The region evaluates to its last binding
(or to an explicit `return`), like a graph block (Spec §7.2, §12.1). Bindings
inside the region may depend on other bindings in the same region, including
bindings textually defined later — the dependency is on the wire name, not
the textual order.

### 3.2 Wire classification

A `rec { b₁; b₂; ...; bₙ }` region is a set of bindings forming a (possibly
cyclic) subgraph. The bindings are classified into three roles:

- **State wires** (the feedback wires): the bindings that participate in a
  cycle. A binding `bᵢ` is a state wire if it (transitively) depends on a
  binding that (transitively) depends on `bᵢ` — i.e. it is involved in a
  cyclic dependency. These form the feedback channel `S`.

- **Exit wire**: the region's value — the last binding (or an explicit
  `return`). Its type is the region's type `B`.

- **Acyclic bindings**: bindings that depend only on the enclosing scope or
  on state wires (not part of a cycle). These are computed each iteration
  from the current state and external inputs. They are not fed back.

### 3.3 State-wire identification algorithm

The state wires are identified by dependency analysis:

1. **Build the dependency graph.** Construct a directed graph over the
   bindings `{b₁, ..., bₙ}`. There is an edge `bᵢ → bⱼ` if `expressionᵢ`
   references `bⱼ` (i.e. `bᵢ` depends on `bⱼ`).

2. **Compute strongly connected components (SCCs).** A binding `bᵢ` is a
   state wire iff:
   - it is in an SCC of size > 1 (a mutual cycle), OR
   - it depends on itself (a self-dependency: `bᵢ = ... bᵢ ...`).

   Equivalently: the state wires are the bindings involved in cycles.

3. **Acyclic bindings** are those not in any cycle — they form a DAG
   (possibly depending on state wires or external inputs).

This is the algorithm specified in the desugaring spec §2.2 (steps 1–2).

### 3.4 Worked example — mutual cycle

```text
rec {
  a = f b
  b = g a
}
```

- `a` depends on `b` (edge `a → b`); `b` depends on `a` (edge `b → a`).
- The SCC `{a, b}` has size 2 > 1, so both `a` and `b` are state wires.
- The exit wire is the last binding, `a` (or whatever is referenced after
  the region).

```text
      ┌──── f ← b
      │
      a
      │
      ↓
      g
      │
      └────→ b
```

### 3.5 Worked example — degenerate (no internal cycle)

```text
rec {
  result = if x <= 0 then 0 else countdown (x - 1)
}
```

Here `result` depends on `countdown` (the enclosing arrow) and `x` (the
enclosing scope), but **not on itself** within the region. There is no
internal cycle: the dependency graph has a single node `result` with no
self-edge. The SCC is `{result}` of size 1 with no self-dependency, so `result`
is **not** a state wire.

**Clarification: `rec` captures INTERNAL cycles.** A `rec` region's cycle is
internal to the region — a cyclic dependency among the region's own bindings.
If a binding depends on the enclosing arrow (e.g. `countdown`), that is
**recursion through the enclosing arrow**, not an internal cycle. The `rec`
region does not capture this; it is a separate mechanism (the enclosing arrow
is re-entered via `app` or composition, not via the `rec` feedback channel).

The countdown example with explicit feedback:

```text
countdown = x ~> {
  rec {
    next = x - 1
    result = if x <= 0
      0
      else countdown next
  }
  result
}
```

Here `next` and `result` do **not** form an internal cycle either: `next`
depends on `x` (external), `result` depends on `next` and `countdown`
(external). The recursion is through `countdown` (the enclosing arrow), not
through the `rec` feedback. This is a **degenerate** `rec` (no internal
cycle) — see §8. The feedback that makes countdown work is through the
enclosing arrow's re-entry, not the `rec` region's feedback channel.

A true feedback countdown would use the `rec` state wire explicitly:

```text
countdown = x ~> {
  rec {
    n = if n <= 0
      0
      else n - 1
  }
  n
}
```

Here `n` depends on itself (`n = ... n ...`), forming a self-cycle. `n` is a
state wire; the feedback carries the decremented `n` to the next iteration.
The exit wire is `n` (which is `0` when the loop exits). This is a true
feedback region. (Note: the initial seed for `n` is `x`, the enclosing
arrow's input — see §4 on seeding.)

### 3.6 Summary of the distinction

| Pattern                                                  | Internal cycle? | State wires | Behavior                                   |
| -------------------------------------------------------- | --------------- | ----------- | ------------------------------------------ |
| `rec { a = f b; b = g a }`                               | Yes (mutual)    | `a`, `b`    | True feedback region                       |
| `rec { n = if n <= 0 then 0 else n - 1 }`                | Yes (self)      | `n`         | True feedback region                       |
| `rec { result = if x <= 0 then 0 else countdown (x-1) }` | No              | none        | Degenerate (plain block)                   |
| `rec { next = x - 1; result = ... countdown next }`      | No              | none        | Degenerate (recursion via enclosing arrow) |

---

## 4. The typing rule

### 4.1 The formal inference rule

Let the `rec` region have state wires `s₁ : S₁, ..., sₖ : Sₖ` (the cyclic
bindings) and exit wire `e : B`. The region's bindings, given the state wires
as inputs, produce the state wires (as outputs, for the next iteration) and
the exit wire.

```text
  Γ, s₁:S₁, ..., sₖ:Sₖ  ⊢  b₁, ..., bₙ  produce  s₁':S₁, ..., sₖ':Sₖ, e:B
  (each sᵢ' is the "next" value of state wire sᵢ; e is the exit)
───────────────────────────────────────────────────────────────────────────── (Rec)
  Γ ⊢ rec { b₁; ...; bₙ } : B
```

Where:

- The state wires `sᵢ` are the **inputs** (the current state, from the
  previous iteration or the initial seed).
- The "next" state wires `sᵢ'` are the **outputs** (the feedback values, fed
  back as the next iteration's `sᵢ`).
- The exit wire `e` is the region's **result**.
- The **fixpoint condition**: there must exist types `S₁, ..., Sₖ` such that
  the bindings are well-typed given `sᵢ : Sᵢ` as inputs AND produce
  `sᵢ' : Sᵢ` as outputs (the state type is stable across the feedback).
  This is the well-typed-fixpoint check (§5).
- If no such `S₁, ..., Sₖ` exist (the state type is not stable — e.g.
  `s : Int` feeds back as `s' : String`), it is a **compile error** (not a
  runtime divergence).

### 4.2 Expression as the kernel `Loop` rule

The `rec` typing rule is the surface-level version of the kernel `Loop`
typing rule (§2.2). The region's body (with state inputs) is an arrow
`(Env × S) ~> (B × S)` where:

- `S = S₁ × ... × Sₖ` (the product of state types).
- `Env` is the enclosing scope (the wires from the enclosing arrow that the
  region reads — the external inputs).
- `B` is the exit wire's type.

`rec` applies `loop` to get `Env ~> B`:

```text
  Γ ⊢ body : (Env × S) ~> (B × S)
────────────────────────────────────── (Loop, applied to rec)
  Γ ⊢ rec { body } : Env ~> B
```

Since the `rec` region appears inside an arrow body (e.g.
`x ~> { rec { ... } }`), the `Env` is the enclosing arrow's input (available
in scope). The state wires are the internal feedback. The `loop` hides `S`,
giving `Env ~> B`. Inside the arrow body, the `rec` region's type is `B`
(the exit wire's type), because the `Env` input is already in scope — the
region produces the exit value `B` from the enclosing scope.

### 4.3 Clarification: does the region take the enclosing input?

A `rec` region inside `x ~> { rec { ... } }` — does the region take `x` as
input? **Yes, implicitly.** The region's external input is the enclosing
arrow's input (available in scope as `x`); the state wires are the internal
feedback. The region's body is `(Env × S) ~> (B × S)` where `Env` includes
`x` (and any other wires from the enclosing scope that the region reads).
`loop` hides `S`, giving `Env ~> B`. Since `Env` is already in scope, the
region's type as used in the arrow body is `B` — the exit wire's type.

### 4.4 Seeding the state

The initial values of the state wires (the seed) are determined as follows:

- A state wire that shadows an enclosing-scope name is seeded with that
  name's value. E.g. in `rec { n = if n <= 0 then 0 else n - 1 }` inside
  `x ~> { ... }` where `n` is bound to `x` before the `rec`, the state wire
  `n` is seeded with `x`'s value.
- A state wire that does not shadow an enclosing name requires an explicit
  seed. In v0.1, the seed is provided by the first binding of the state wire
  in the region (the initial value before the feedback takes over), or by
  an explicit annotation. The seeding mechanism is the handler's concern
  (ADR-0052 §Feedback semantics); the typing rule is agnostic to the seed
  value — it only requires that the state type is stable.

---

## 5. The well-typedness check (fixpoint of the state type)

### 5.1 The check

The well-typedness check is: find types `S₁, ..., Sₖ` such that the region's
bindings typecheck with `sᵢ : Sᵢ` as inputs and produce `sᵢ' : Sᵢ` as outputs
(the state type is stable across the feedback).

This is a **type-fixpoint problem**: solve for `S₁, ..., Sₖ` such that the
type equations close. The state type must be the same on both sides of the
feedback edge — the input type and output type of each state wire must
unify.

### 5.2 The algorithm

The algorithm uses Hindley–Milner unification (ADR-0054) over the state wires:

1. **Assign fresh type variables.** For each state wire `sᵢ`, assign a fresh
   type variable `αᵢ` for its input type (the current state) and a fresh
   type variable `βᵢ` for its output type (the next state).

2. **Typecheck the region's bindings.** Typecheck `b₁, ..., bₙ` in the
   context `Γ, s₁:α₁, ..., sₖ:αₖ` (the state wires as inputs, with fresh
   input type variables). This generates constraints:
   - Each binding `bⱼ` produces a type for its output.
   - For a state wire `sᵢ`, its output type is `βᵢ`.
   - For the exit wire `e`, its type is `B` (a type that may involve the
     `α`s and `β`s).

3. **Unify the feedback equations.** For each state wire `sᵢ`, unify the
   input type `αᵢ` with the output type `βᵢ` (the feedback equation
   `αᵢ = βᵢ`). This is the type-level fixpoint condition: the state type
   must be stable across the feedback.

4. **Check unification.** If unification succeeds, the fixpoint exists; the
   state type `Sᵢ` is the principal unifying type of `αᵢ` and `βᵢ`. The
   region's type is the exit wire's type `B` (with the state types
   resolved). If unification fails (no consistent state type), it is a
   compile error: **"rec region has no well-typed fixpoint."**

### 5.3 Worked example — mutual cycle

```text
rec {
  a = f b
  b = g a
}
```

with `f : S_b ~> S_a` and `g : S_a ~> S_b`.

1. State wires: `a` (input `α_a`, output `β_a`), `b` (input `α_b`, output
   `β_b`).
2. Typecheck bindings:
   - `a = f b`: `f : α_b ~> β_a`, so `α_b = S_b` (input of `f`) and
     `β_a = S_a` (output of `f`).
   - `b = g a`: `g : β_a ~> β_b` (since `a`'s output is `β_a`... but wait,
     `b = g a` uses `a` as input; under causal/strict semantics, `a`'s input
     is `α_a`, so `g : α_a ~> β_b`). Actually, the binding `a = f b` reads
     `b` (the state input `α_b`) and produces `a` (the state output `β_a`).
     The binding `b = g a` reads `a` — but which `a`? Under causal/strict
     semantics, it reads the **input** `a` (the previous iteration's `a`,
     i.e. `α_a`), producing `b` (the output `β_b`). So:
     - `a = f b` gives: `f : α_b ~> β_a`, so `α_b = S_b`, `β_a = S_a`.
     - `b = g a` gives: `g : α_a ~> β_b`, so `α_a = S_a`, `β_b = S_b`.
3. Feedback equations:
   - `α_a = β_a`: `S_a = S_a` — trivially satisfied.
   - `α_b = β_b`: `S_b = S_b` — trivially satisfied.
4. Unification succeeds. The state types are `S_a` (whatever `f` outputs /
   `g` inputs) and `S_b` (whatever `g` outputs / `f` inputs). The fixpoint
   exists. The exit wire is `a` (type `S_a`); the region's type is `S_a`.

### 5.4 Failure example — unstable state type

```text
rec {
  s = toString s
}
```

where `toString : Int ~> String`.

1. State wire: `s` (input `α`, output `β`).
2. Typecheck: `s = toString s` gives `toString : α ~> β`, so `α = Int`,
   `β = String`.
3. Feedback equation: `α = β`, i.e. `Int = String` — **unification fails**.
4. Compile error: "rec region has no well-typed fixpoint" (the state wire
   `s` has input type `Int` but feeds back as `String`).

### 5.5 The degenerate case (no state wires)

If the region has no state wires (`k = 0`), the feedback channel is `Unit`
(the empty product). The `loop` is over `Unit` state — a no-op feedback.
The region's body is `(Env × Unit) ~> (B × Unit)`, which simplifies to
`Env ~> B`. The region's type is `B` (the exit wire's type). There are no
feedback equations to unify (the state is `Unit` trivially). See §8 for the
degenerate case.

---

## 6. Termination is not a typing concern (ID.3)

The typing rule does **NOT** check termination. A well-typed `rec` region may
diverge at runtime (the feedback never reaches a fixpoint, or the loop never
exits). Termination is a **runtime/effect concern**, addressed by:

1. **The handler's feedback semantics** (ADR-0052 §Feedback semantics):
   - Causal/strict: the loop runs until an exit condition is met (the
     handler decides when to stop based on the runtime values).
   - Lazy/fixpoint: the loop computes a fixpoint or diverges (the handler
     detects demand cycles or productivity at runtime).

2. **A separate termination-analysis pass.** The PoC has
   `src/termination_analysis_tests.rs`, which implements genuine structural
   termination analysis: it discovers a decreasing measure on the feedback
   channel by examining the graph structure of the loop body, combined with
   the termination effects recorded in each base arrow's signature. Cases
   handled include side-channel loops (not guaranteed), list-consuming
   loops (|C| decreases, guaranteed), counter loops (C decreases,
   guaranteed), and fixed-point loops (no decreasing measure, not
   guaranteed). **This is the place termination is analyzed — NOT the
   typechecker.** The typechecker checks the type-level fixpoint
   (well-typedness); the termination analysis checks the runtime fixpoint
   (does the loop converge?).

3. **The programmer's responsibility.** The programmer provides an exit
   condition (a guard that breaks the feedback) or a decreasing measure
   (a well-founded order that the state decreases along). The type system
   does not enforce this; it is documented via the termination analysis or
   left to the programmer's discipline.

This is consistent with ID.3: "Termination is NOT checked at the type level
— it is a runtime/effect concern." The type system checks that the feedback
graph is **well-typed** (the state type is stable); it does not check that
the feedback graph **terminates** (the state reaches a fixpoint).

---

## 7. Interaction with `return` (ID.14)

### 7.1 The rule

A `return` inside a `rec` region exits the **innermost enclosing `~>` arrow**
(ID.14), NOT the `rec` region. The `rec` region is not a `~>` — it is a
region _inside_ a `~>`. So `return` must escape the `rec` and reach the
enclosing `~>`.

### 7.2 Effect on typing

The `return` expression must have the enclosing arrow's return type. The
`rec` region's exit wire type must be compatible with the arrow's return
type: the region's normal exit and the `return` both produce values of the
arrow's output type.

Formally, if the enclosing arrow has type `A ~> R` (return type `R`), and
the `rec` region's normal exit wire has type `B`, then:

- The `return e` inside the `rec` region requires `e : R`.
- The region's exit wire (normal path) must have type `B` such that `B` and
  `R` are compatible — specifically, the enclosing arrow's body unifies
  the normal exit (`B`) and the `return` path (`R`), so `B = R`.

The desugaring (desugaring spec §10) handles this by **tagging the exit
wire**:

```text
Exit = Normal result | ReturnRequested value
```

The `return e` is rewritten to `set exit = ReturnRequested e; break
feedback`. The enclosing arrow checks the tag after the `rec` region:

```text
match exit {
  Normal: result → result
  ReturnRequested: value → return value    -- exits the enclosing ~>
}
```

From a typing perspective, the exit wire's type is the sum
`Normal B + ReturnRequested R`, which must unify with the enclosing arrow's
output type `R`. In practice, the `Normal` arm's `result : B` and the
`ReturnRequested` arm's `value : R` must both be compatible with `R`, so
`B = R` (the region's normal exit type equals the arrow's return type).

### 7.3 Reference

The precise mechanism (exit-wire tagging, feedback breaking, the enclosing
arrow's tag check) is specified in the desugaring spec §10 ("return Inside
Loop Bodies"). The typing rule here is consistent with that mechanism: the
`return` does not change the `rec` region's type (it is still `B`); it
adds a `ReturnRequested` path that the enclosing arrow handles. The
typechecker checks that both paths produce values of the enclosing arrow's
return type.

---

## 8. Degenerate `rec` (no internal cycle)

### 8.1 Definition

A `rec` region with no internal cycle (all bindings are acyclic — no SCC of
size > 1 and no self-dependency) is **well-typed but degenerate**. The state
wire set is empty (`k = 0`), so `S = Unit`. The `loop` is over `Unit` state
(a no-op feedback), and the region's type is the exit wire's type `B`.

### 8.2 Typing

```text
  Γ ⊢ b₁, ..., bₙ  produce  e:B    (no cyclic bindings; S = Unit)
───────────────────────────────────────────────────────────────────── (Rec-Degenerate)
  Γ ⊢ rec { b₁; ...; bₙ } : B
```

The region is equivalent to a plain block `{ b₁; ...; bₙ }` — the `rec`
wrapper adds a trivial `Unit` feedback channel that does nothing. The
bindings are typechecked as a normal acyclic graph (standard Hindley–Milner
inference, no feedback equations).

### 8.3 Warning

The compiler **MAY warn** that a `rec` with no cycle is probably a mistake —
the programmer likely meant a plain block or forgot the feedback. This is a
**warning, not an error**: the region is well-typed (it typechecks as a
plain block), but it is suspicious (why use `rec` if there is no cycle?).

The warning message: "rec region has no internal cycle; it is equivalent to
a plain block. Did you mean to introduce a feedback wire?"

### 8.4 Example

```text
rec {
  result = if x <= 0 then 0 else countdown (x - 1)
}
```

No internal cycle (`result` does not depend on itself within the region).
State wires: none. `S = Unit`. The region typechecks as a plain block with
exit wire `result`. The compiler warns: the `rec` is degenerate (the
recursion is through `countdown`, the enclosing arrow, not through the
`rec` feedback).

---

## 9. Worked examples

### 9.1 Minimal cyclic region — `rec { a = f b; b = g a }`

```text
loop = x ~> {
  rec {
    a = f b
    b = g a
  }
  a
}
```

**Dependency analysis:** `a` depends on `b`; `b` depends on `a`. SCC
`{a, b}` of size 2. State wires: `a`, `b`. Exit wire: `a` (referenced after
the region).

**Typing derivation:**

```text
  Γ, a:α_a, b:α_b  ⊢  a = f b  :  β_a       (f : α_b ~> β_a)
  Γ, a:α_a, b:α_b  ⊢  b = g a  :  β_b       (g : α_a ~> β_b)
  Γ, a:α_a, b:α_b  ⊢  produce  a':β_a, b':β_b, exit:a:β_a
  feedback equations:  α_a = β_a,  α_b = β_b
  unify:  α_a = β_a = S_a,  α_b = β_b = S_b    (S_a, S_b from f, g signatures)
───────────────────────────────────────────────────────────────────────────── (Rec)
  Γ ⊢ rec { a = f b; b = g a } : S_a
```

With `f : S_b ~> S_a` and `g : S_a ~> S_b`:

- `a = f b` gives `α_b = S_b`, `β_a = S_a`.
- `b = g a` gives `α_a = S_a`, `β_b = S_b`.
- Feedback: `α_a = β_a` → `S_a = S_a` ✓; `α_b = β_b` → `S_b = S_b` ✓.
- Region type: `S_a` (the exit wire `a`'s type).

**Kernel `Loop` form:**

```text
Loop { body = arr (λ(x, (a, b)).
       let a' = f b
       let b' = g a'
       (a', (a', b'))) }
```

The feedback channel carries `(a, b)`; the output is `a'`. The state type is
`S = S_a × S_b`; `loop` hides it, exposing `Unit ~> S_a` (the external input
`x` is available but unused in this minimal example).

### 9.2 `iterate` — practical feedback loop

```text
iterate = x ~> {
  rec {
    next = step current
    current = if done next
      next
      else step next
  }
  current
}
```

**Dependency analysis:** `next` depends on `current`; `current` depends on
`next` (via both branches). SCC `{next, current}` of size 2. State wires:
`next`, `current`. Exit wire: `current`.

**Typing derivation:**

Let `step : T ~> T` and `done : T ~> Bool` (for some element type `T`).

```text
  Γ, next:α_n, current:α_c  ⊢  next = step current  :  β_n
       (step : α_c ~> β_n,  so α_c = T, β_n = T)
  Γ, next:α_n, current:α_c  ⊢  current = if done next then next else step next  :  β_c
       (done : β_n ~> Bool,  next : β_n,  step : β_n ~> β_c)
       (so β_n = T,  β_c = T)
  feedback equations:  α_n = β_n,  α_c = β_c
  unify:  α_n = β_n = T,  α_c = β_c = T
───────────────────────────────────────────────────────────────────────────── (Rec)
  Γ ⊢ rec { next = step current; current = if done next then next else step next } : T
```

- `next = step current` gives `α_c = T` (input of `step`), `β_n = T` (output
  of `step`).
- `current = if done next then next else step next`: `done next` requires
  `next : T` (so `β_n = T`, consistent); the `then` branch gives `next : T`;
  the `else` branch gives `step next : T` (so `β_c = T`).
- Feedback: `α_n = β_n` → `T = T` ✓; `α_c = β_c` → `T = T` ✓.
- Region type: `T` (the exit wire `current`'s type).

**Kernel `Loop` form:**

```text
Loop { body = arr (λ(x, (next, current)).
       let next' = step current
       let current' = if done next' then next' else step next'
       (current', (next', current'))) }
```

The feedback channel carries `(next, current)`; the output is `current'`.
State type `S = T × T`; `loop` hides it, exposing `Unit ~> T`.

### 9.3 `countdown` — with explicit feedback

```text
countdown = x ~> {
  rec {
    n = if n <= 0
      0
      else n - 1
  }
  n
}
```

(Here `n` is seeded with `x` — the state wire `n` shadows the enclosing
scope's `x`, so the initial value is `x`.)

**Dependency analysis:** `n` depends on itself (`n = ... n ...`). Self-cycle.
State wire: `n`. Exit wire: `n`.

**Typing derivation:**

Let `<= : [Int, Int] ~> Bool` and `- : [Int, Int] ~> Int`.

```text
  Γ, n:α  ⊢  n = if n <= 0 then 0 else n - 1  :  β
       (n <= 0 requires n : Int,  so α = Int)
       (then branch: 0 : Int;  else branch: n - 1 : Int,  so β = Int)
  feedback equation:  α = β
  unify:  α = β = Int
───────────────────────────────────────────────────────────────────────────── (Rec)
  Γ ⊢ rec { n = if n <= 0 then 0 else n - 1 } : Int
```

- `n = if n <= 0 then 0 else n - 1`: `n <= 0` requires `n : Int` (input
  `α = Int`); both branches produce `Int` (output `β = Int`).
- Feedback: `α = β` → `Int = Int` ✓.
- Region type: `Int` (the exit wire `n`'s type).

**Kernel `Loop` form:**

```text
Loop { body = arr (λ(x, n).
       let n' = if n <= 0 then 0 else n - 1
       (n', n')) }
```

The feedback channel carries `n'`; the output is `n'`. State type `S = Int`;
`loop` hides it, exposing `Unit ~> Int`. The seed for `n` is `x` (the
enclosing arrow's input). Termination (n reaches 0) is a runtime concern —
the typechecker only checks that `Int` is stable across the feedback.

### 9.4 `retry` — feedback through the enclosing arrow

```text
retry = request ~> {
  rec {
    result = send request
    exit = if result.ok
      result
      else if result.attempts >= 3
        err "failed"
        else retry result.next
  }
  exit
}
```

**Dependency analysis:** `result` depends on `request` (external, not a
state wire — `request` is the enclosing arrow's input). `exit` depends on
`result` and `retry` (the enclosing arrow). Neither `result` nor `exit`
depends on itself within the region. **No internal cycle.** This is a
**degenerate** `rec` — the recursion is through `retry` (the enclosing
arrow), not through the `rec` feedback.

**Typing derivation (degenerate):**

```text
  Γ ⊢ result = send request  :  R        (send : Req ~> R)
  Γ ⊢ exit = if result.ok then result else if result.attempts >= 3 then err "failed" else retry result.next  :  E
       (result.ok : Bool,  result : R,  err "failed" : E,  retry result.next : E)
       (so R = E,  all branches produce E)
  (no state wires; S = Unit)
───────────────────────────────────────────────────────────────────────────── (Rec-Degenerate)
  Γ ⊢ rec { result = send request; exit = ... } : E
```

- `result = send request`: `send : Req ~> R`, so `result : R`.
- `exit = if result.ok then result else ...`: `result.ok : Bool`, `result : R`
  (then branch), `err "failed" : E` and `retry result.next : E` (else
  branches). All branches must produce the same type, so `R = E`.
- No state wires, no feedback equations. Region type: `E` (the exit wire's
  type).
- **Warning:** the `rec` is degenerate (no internal cycle). The recursion is
  through `retry` (re-entering the enclosing arrow with `result.next`), not
  through the `rec` feedback.

**Note:** A true feedback version of `retry` would carry `request` as a
state wire:

```text
retry = request ~> {
  rec {
    req = request
    result = send req
    exit = if result.ok
      result
      else if result.attempts >= 3
        err "failed"
        else req' = result.next
  }
  exit
}
```

Here `req` depends on `request` (seed) and `req'` (feedback); `req'` depends
on `result` which depends on `req`. The cycle is `req → result → req' → req`
(if `req'` feeds back to `req`). State wire: `req` (seeded with `request`,
fed back with `result.next`). Exit wire: `exit`. The feedback equation is
`α_req = β_req'`, i.e. `Req = Req` (if `result.next : Req`). This is a true
feedback region. The degenerate version above achieves the same effect via
the enclosing arrow's re-entry, not the `rec` feedback.

### 9.5 Degenerate `rec` — no cycle

```text
rec {
  a = f x
  b = g a
}
```

where `x` is from the enclosing scope, `f : X ~> A`, `g : A ~> B`.

**Dependency analysis:** `a` depends on `x` (external); `b` depends on `a`.
No cycle. No state wires. `S = Unit`.

**Typing derivation:**

```text
  Γ ⊢ a = f x  :  A        (f : X ~> A)
  Γ ⊢ b = g a  :  B        (g : A ~> B)
  (no state wires; S = Unit)
───────────────────────────────────────────────────────────────────────────── (Rec-Degenerate)
  Γ ⊢ rec { a = f x; b = g a } : B
```

- No feedback equations. Region type: `B` (the exit wire `b`'s type).
- **Warning:** "rec region has no internal cycle; it is equivalent to a
  plain block. Did you mean to introduce a feedback wire?"

The region typechecks identically to the plain block `{ a = f x; b = g a }`.

---

## 10. Relationship to ADR-0070 and ADR-0073

### 10.1 ADR-0070 — Refinement inference scope

ADR-0070 defines the refinement inference engine, which derives semantic
guarantees from arrow graph structure with zero user annotations. The
inference works by reading the graph, looking up axioms (what the leaf atoms
guarantee), composing (Seq conjoins, First preserves side-channel, Choice
branches, **Loop finds fixpoint**), and checking implications.

The `rec` typing rule's fixpoint check relates to ADR-0070's refinement
inference as follows:

- **Type-level fixpoint (this document):** the state type `S` must be stable
  across the feedback edge (input type = output type, by unification). This
  is the **type-level** fixpoint — it checks that the feedback graph is
  well-typed.

- **Refinement-level fixpoint (ADR-0070):** if the state has a refinement
  invariant (e.g. `n : { x : Int | x ≥ 0 }`), the feedback must **preserve**
  that invariant. The refinement inference engine discovers this by fixpoint
  iteration: it starts with the body's guarantee, computes the weakest
  precondition needed to preserve it, conjoins, and iterates until a fixpoint
  is reached. This is the **refinement-level** fixpoint — it checks that the
  feedback preserves the state's refinement invariant.

The two fixpoints are at different levels: the type-level fixpoint (this
document) is checked by the typechecker (Hindley–Milner unification); the
refinement-level fixpoint (ADR-0070) is checked by the refinement inference
engine (fixpoint iteration over predicates). The type-level fixpoint is
necessary (the region must be well-typed); the refinement-level fixpoint is
additional (it discovers invariants like `Count ≥ 0` that hold across all
iterations). A `rec` region that passes the type-level fixpoint but whose
refinement invariant is not preserved by the feedback will still typecheck
— the refinement invariant is a stronger property that the refinement
engine checks separately.

### 10.2 ADR-0073 — State machine invariants

ADR-0073 defines how state machine invariants are discovered by fixpoint
iteration in the refinement inference engine. A state machine is
`State × Event ⇝ State` — it processes events and updates state. The key
verification question: what invariants hold on the state across all
transitions?

The state machine maps to an arrow graph:

```text
state_machine = loop(comp(handle_event, first(id)))
```

where `handle_event : (State × Event) ⇝ (State × Event)` updates the state
based on the event, and `first(id)` passes the event stream through as a
side channel.

The `rec` region is the **surface counterpart** to this kernel `loop`-based
state machine:

- The **state wires** of the `rec` region are the state machine's **state**.
  They form the feedback channel `S`, just as the kernel `loop`'s state is
  the feedback channel.
- The **acyclic bindings** are the event processing (they depend on the
  state and external inputs, producing the next state and the result).
- The **exit wire** is the state machine's output (the result of processing
  the events).
- The **state-machine invariant** is the state type's refinement: the
  refinement engine discovers invariants (e.g. `Count ≥ 0`) that hold on
  the state wires across all iterations, by fixpoint iteration over the
  transition's conditional contracts.

The `rec` typing rule (this document) checks the **type-level** fixpoint
(the state type is stable). The refinement engine (ADR-0073) checks the
**refinement-level** fixpoint (the state's invariant is preserved). The
two are complementary: the typechecker ensures the feedback graph is
well-typed; the refinement engine discovers the data invariants that hold
across the feedback.

---

## 11. Open questions / future work

### 11.1 Refinement-typed state (ADR-0070)

How to check that the feedback preserves the state's refinement invariant?
The type-level fixpoint (this document) checks that the state type is stable
(e.g. `Int` feeds back as `Int`). The refinement-level fixpoint (ADR-0070)
checks that the state's refinement is preserved (e.g. `{ x : Int | x ≥ 0 }`
feeds back as `{ x : Int | x ≥ 0 }`, not just `Int`). The mechanism is
fixpoint iteration over the transition's conditional contracts (ADR-0073),
but the precise integration of refinement types with the `rec` typing rule
— specifically, how the refinement invariant is threaded through the
feedback equations during unification — is future work.

### 11.2 Causal vs fixpoint semantics interaction with typing

The typing rule is the **same** under both causal/strict and lazy/fixpoint
semantics (§2.3). The typing rule checks that a well-typed fixpoint exists;
the runtime behavior (causal: state carries forward across steps; fixpoint:
state is a fixpoint) differs. This document is agnostic to the feedback
semantics — the typing rule does not depend on which semantics the handler
implements. However, the **practical** behavior of a `rec` region differs
significantly: under causal/strict semantics, read-before-write is normal
(reads the previous iteration's value); under lazy/fixpoint semantics,
read-before-write may be productive or ill-founded (detected at runtime).
The typing rule accepts both; the programmer must be aware of which
semantics the target handler implements.

### 11.3 Higher-rank state (state wires that are themselves arrows)

Does the fixpoint check handle arrow-typed state? E.g. a state wire
`s : A ~> B` (an arrow as the state value). **Yes, by unification** — the
feedback equation `α = β` unifies arrow types just as it unifies base types.
If `s` has input type `α = A ~> B` and output type `β = A ~> B`, the
feedback equation `α = β` is `A ~> B = A ~> B`, which trivially unifies.
However, the **runtime feedback** of an arrow-typed state is subtle: the
feedback channel carries an arrow value (a computational description), and
the handler must support feeding an arrow back into the next iteration.
Under causal/strict semantics, this is straightforward (the arrow is a
value, carried forward). Under lazy/fixpoint semantics, this may require
the arrow to be a fixpoint of itself — a more demanding condition. The
typing rule accepts arrow-typed state; the runtime semantics is the
handler's concern.

---

## Related

- [ADR-0052 — Arrow Calculus Kernel](../../project/adrs/0052-arrow-calculus-kernel.md)
  — defines the kernel `Loop` combinator (`loop : Arrow (A, S) (B, S) →
Arrow A B`) and the feedback semantics (causal/strict vs lazy/fixpoint).
  The `rec` typing rule is the surface-level version of the kernel `Loop`
  typing rule.
- [ADR-0054 — Generic Typecheck Engine](../../project/adrs/0054-generic-typecheck-engine.md)
  — the Hindley–Milner unification engine used for the well-typedness check
  (§5). The fixpoint check is unification of state input/output types over
  the type solver.
- [ADR-0070 — Refinement Inference Scope](../../project/adrs/0070-refinement-inference-scope.md)
  — the fixpoint discipline that `rec` regions rely on for refinement-level
  invariant checking. The type-level fixpoint (this document) is necessary;
  the refinement-level fixpoint (ADR-0070) is additional.
- [ADR-0073 — State Machine Invariants](../../project/adrs/0073-state-machine-invariants.md)
  — the `loop`-based fixpoint discovery for state machines. `rec` is the
  surface counterpart; the state wires are the state machine's state, and
  the invariant is the state type's refinement.
- [ADR-0074 — Arrow Surface Syntax v0.1 — Redesign](../../project/adrs/0074-arrow-syntax-v0_1-surface-redesign.md)
  — Correction 2 (`rec` as recursive region) and ID.3 (`rec` typing —
  Paterson loop). This document is follow-up task #2.
- [Arrow Language Specification v0.1 §12.1](./ARROW_LANGUAGE_SPEC_V0_1.md)
  — the surface spec for `rec` regions, including the defining property and
  the typing summary (ID.3).
- [Arrow Desugaring Specification v0.1 §2](./ARROW_DESUGARING_V0_1.md)
  — the desugaring of `rec` to kernel `Loop`, including state-wire
  identification, exit-wire identification, and the feedback graph
  construction. §10 specifies `return` inside loop bodies (exit-wire
  tagging).
- [FORMALISM.md](./FORMALISM.md) — the formal calculus, including the
  kernel `Loop` inference rule (§Type System) that the `rec` typing rule is
  the surface-level version of.
