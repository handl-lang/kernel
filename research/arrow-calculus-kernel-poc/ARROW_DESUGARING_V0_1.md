# Arrow Desugaring Specification v0.1

## Status

Authoritative — v0.1 desugaring specification per ADR-0074 follow-up #4.
Defines the precise expansion of the Addendum surface forms into the kernel
combinators.

This document specifies exactly how each surface form from ADR-0074
Addendum A.1–A.7 (and the `rec` region from Correction 2) expands into the
kernel combinators of ADR-0052 (`arr` / `>>>` / `first` / `choice` / `loop` /
`app`), expressed via the surface core (`~>` / `>>>` / `***` / `&&&` / `|||` /
`rec`). It defines the feedback-wire naming rules for `while` / `do while` /
`for`, the structural override rule for spread, the `return`-in-loop-body
rule, and the nested `if`/`else` expansion for multi-way `if`. §12 specifies
the normalization of import and export surface forms to projection and
module-reference nodes (ID.16, ADR-0069). It is the detailed,
implementation-ready companion to the desugaring summary table in §17.2 of
the Arrow Language Specification v0.1.

---

## 1. Overview and Target Language

### 1.1 When desugaring runs

Desugaring is a pass between parse and eval (per ADR-0053 §7, the desugar
pass). The parser produces the full v0.1 surface syntax — including all
Addendum forms (`while`, `do while`, `for`, `??`, `?.`, multi-way `if`,
spread) — and the desugar pass rewrites each sugar form into the surface
core (`~>` / `>>>` / `***` / `&&&` / `|||` / `rec` / `match` / structural
construction). The surface core itself denotes the six kernel combinators of
ADR-0052:

```text
~>      →  arr (arrow construction)
>>>     →  Seq (sequential composition)
***     →  first (product, over first)
&&&     →  fan-out (over first + arr)
|||     →  Choice (choice / branching)
rec     →  Loop (feedback)
```

`match` is `|||` (Choice) with pattern dispatch; structural construction is
`arr`. The desugar pass produces surface-core expressions; a subsequent
lowering pass (ADR-0052 lowering table) maps the surface core to the six
kernel combinators. This document specifies the first pass (surface → surface
core); the second pass is fixed by ADR-0052.

### 1.2 Semantics preservation

Desugaring is **semantics-preserving**: the desugared form has the same type
and the same graph semantics as the surface form. For every surface
expression `e`, if `⟦e⟧` is its desugaring, then:

```text
Γ ⊢ e : τ    ⟺    Γ ⊢ ⟦e⟧ : τ
```

and the graph denoted by `e` is observationally equivalent to the graph
denoted by `⟦e⟧` under every handler interpretation (ADR-0052, Sanada's
model). No sugar form introduces a new kernel combinator (ADR-0074
Addendum); desugaring only rearranges existing combinators.

### 1.3 Notation

We use the surface syntax for desugared output, since `rec` / `match` / `|||`
are themselves surface core that denote kernel combinators. The notation
`⟦e⟧` means "the desugaring of `e`." Where a desugaring introduces fresh
wire names, we use subscripted names like `n₀`, `n₁`, `state₁`, `exit₁` to
distinguish compiler-generated wires from user-named wires. In actual
compiler output these are gensym'd (guaranteed fresh).

Desugaring templates are shown in ```text blocks. Comments use `--`.

---

## 2. `rec` — the Recursive Region (Correction 2, ID.3)

### 2.1 Surface syntax

```text
rec {
  binding₁
  binding₂
  ...
  bindingₙ
}
```

Each `bindingᵢ` is `nameᵢ = expressionᵢ`. The region evaluates to its last
binding (or to an explicit `return`), like a graph block (Spec §12.1,
§7.2).

### 2.1.1 Relationship to the kernel `Loop`

`rec` is the surface form of Paterson's `loop` (ADR-0052, "the `loop`
correction"; ADR-0074 Correction 2). The kernel `Loop` combinator has the
shape:

```text
loop : Arrow (A, S) (B, S) → Arrow A B
```

`loop f` takes an arrow `f : (A, S) ~> (B, S)` and feeds the second output
`S` back into the second input `S`; the first component becomes the
externally visible output. `loop` is **feedback, not iteration**
(ADR-0052). The `rec` surface form makes this feedback explicit at the
syntax level: the cyclic dependencies in the region are the state wire `S`,
and the non-cyclic output is the exit wire `B`.

### 2.2 Precise desugaring to kernel `Loop`

Given a `rec` region:

```text
rec {
  a₁ = e₁
  a₂ = e₂
  ...
  aₙ = eₙ
}
```

The compiler performs the following steps:

1. **Dependency analysis.** Build the dependency graph over the bindings
   `{a₁, ..., aₙ}`. A binding `aᵢ` depends on `aⱼ` if `eᵢ` references `aⱼ`.
   Identify the **strongly connected components** (SCCs) of this graph.

2. **State-wire identification.** The bindings that participate in a cycle
   (an SCC of size > 1, or a self-dependency `aᵢ = ... aᵢ ...`) are the
   **state wires** — these form the feedback channel `S`. Bindings not in
   any cycle are evaluated once (they may depend on state wires or on
   external inputs, but they do not feed back).

3. **Exit-wire identification.** The region's result (the last binding, or
   the value of an explicit `return`) is the **exit wire** `B`. The exit
   wire may depend on state wires and non-cyclic bindings.

4. **Feedback graph construction.** The compiler constructs an arrow
   `f : (A, S) ~> (B, S)` where:
   - `A` is the tuple of external inputs (wires from the enclosing scope
     that the region reads).
   - `S` is the tuple of state wires (the cyclic bindings).
   - `B` is the exit wire.
   - The body of `f` computes each state wire from the previous iteration's
     state (the feedback input) and the external inputs, then computes the
     exit wire.

5. **Kernel form.** The `rec` region desugars to:

```text
⟦rec { a₁ = e₁; ...; aₙ = eₙ }⟧
  =  Loop { body = arr (λ(a, s₀). (⟦exit⟧, s₁)) }
```

where `s₀` is the feedback input (previous iteration's state), `s₁` is the
feedback output (this iteration's state), and `⟦exit⟧` is the desugared
exit expression. The `Loop` combinator hides `S` in the feedback channel,
exposing `A ~> B`.

In surface-core notation:

```text
⟦rec { ... }⟧  =  rec { ... }    -- rec IS the surface form of Loop
```

That is, `rec` does not desugar further at the surface level — it _is_ the
surface core form that denotes `Loop`. The desugaring of `while` / `do while`
/ `for` produces `rec` regions; the `rec` itself is lowered to `Loop` by the
ADR-0052 lowering pass.

### 2.3 Typing rule (ID.3)

`rec` regions follow Paterson's `loop` model (ID.3):

- The region has a **state wire** `S` (the cyclic dependencies) and an
  **exit wire** `B` (the result).
- The fixpoint is over the state: the compiler must be able to assign a
  well-typed fixpoint to the state transition `S ~> S`.
- **Termination is NOT checked at the type level** — it is a runtime/effect
  concern (ID.3). A `rec` region may diverge at runtime; the type system
  only checks that the feedback graph is well-typed.
- A `rec` without a well-typed fixpoint is a **compile error**, not a
  runtime divergence.

Typing rule:

```text
  Γ, S ⊢ body : (A, S) ~> (B, S)
  ──────────────────────────────────
  Γ ⊢ rec { body } : A ~> B
```

The state type `S` is hidden in the feedback channel, like `loop` hides
`S`. The region's type is `A ~> B` — the exit type, with the state
abstracted away.

If the region's bindings form a cyclic graph with state type `S` and exit
type `B`, the `rec` region has type `B` (the state `S` is hidden in the
feedback, like `loop`). No guard or `return` is required for
well-typedness; a `rec` without a well-typed fixpoint is a compile error.

### 2.4 Well-typedness check

The compiler checks:

1. Every cyclic binding has a consistent type across the feedback edge
   (the type of `aᵢ` on iteration _n_ must unify with the type of `aᵢ` on
   iteration _n+1_).
2. The exit wire's type is well-defined given the state and external inputs.
3. There are no "ill-founded" reads — a binding that reads a state wire
   before it is defined in the same iteration, under causal/strict semantics
   (ADR-0052 §Feedback semantics). Under causal/strict semantics,
   read-before-write reads the _previous_ iteration's value (or the initial
   seed), which is well-defined. Under lazy/fixpoint semantics,
   read-before-write may be productive or ill-founded, detected at runtime.

The reference handler implements causal/strict semantics (ADR-0052 Open
Question 1), so read-before-write in a `rec` region reads the prior
iteration's output (or the initial seed for the first iteration).

### 2.5 Worked examples

#### 2.5.1 Minimal cyclic region

```text
loop = x ~> {
  rec {
    a = f b
    b = g a
  }
  a
}
```

Here `a` and `b` form a cycle: `a` depends on `b`, `b` depends on `a`. The
state wire is `S = (a, b)`. The exit wire is `B = a` (the last binding
referenced after the region).

Kernel `Loop` form:

```text
Loop { body = arr (λ(x, (a, b)).
       let a' = f b
       let b' = g a'
       (a', (a', b'))) }
```

The feedback channel carries `(a, b)`; the output is `a'`. The external
input `x` is not used in this minimal example (it is available but the
cycle is self-contained).

Conceptual graph (from ADR-0074):

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

#### 2.5.2 `iterate` — practical feedback loop

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

Here `current` and `next` form a cycle. The state wire is
`S = current` (with `next` derived from it each iteration). The exit wire is
`B = current`.

Kernel `Loop` form:

```text
Loop { body = arr (λ(x, current).
       let next = step current
       let current' = if done next then next else step next
       (current', current')) }
```

The feedback channel carries `current`; the output is `current'`.

#### 2.5.3 `countdown`

```text
countdown = x ~> {
  rec {
    result = if x <= 0
      0
      else countdown (x - 1)
  }
  result
}
```

Or, with the feedback made explicit:

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

Here `result` (and `next`) form the cyclic dependency — `result` depends on
`countdown next`, which is the recursive call that re-enters the `rec`
region with `next` as the new input. The state wire is the input `x` itself
(carried through the feedback as `next`). The exit wire is `result`.

Kernel `Loop` form (feedback-explicit version):

```text
Loop { body = arr (λ(x, x).
       let next = x - 1
       let result = if x <= 0 then 0 else <re-enter with next>
       (result, next)) }
```

The feedback channel carries `next` (the decremented value); the output is
`result`. The loop terminates when `x <= 0` (runtime/effect concern, not
type-checked per ID.3).

#### 2.5.4 `retry`

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

Here `request` is the state wire (it changes each iteration via
`result.next`). The exit wire is `exit`. The feedback edge carries
`result.next` into the next iteration's `request`.

Kernel `Loop` form:

```text
Loop { body = arr (λ(request, request).
       let result = send request
       let exit = if result.ok
         then result
         else if result.attempts >= 3
           then err "failed"
           else <re-enter with result.next>
       (exit, result.next)) }
```

The feedback channel carries `result.next`; the output is `exit`.

---

## 3. `while` — Sugar over `rec` (Addendum A.1, ID.5)

### 3.1 Surface syntax

```text
while cond {
  body
}

-- or, without a block:
while cond
  body
```

`cond` is a boolean expression evaluated before each iteration. `body` is a
graph block (or single expression) evaluated when `cond` is true. The loop
exits when `cond` is false.

### 3.2 Precise desugaring

`while cond { body }` desugars to a `rec` region with an implicit feedback
wire. The compiler:

1. **Identifies the feedback wires.** The feedback wires are the names
   rebound in the body (see §11 for the general rule). For each name `n`
   that appears both as an input to the body (read from the enclosing scope
   or from a previous iteration) and is rebound (`n = ...` in the body),
   the last binding of `n` in the body feeds back into the next iteration's
   `n`.

2. **Constructs the `rec` region.** The region checks `cond` first; if
   false, it exits with the default (see §3.4); if true, it runs the body,
   and the body's rebound names feed back.

Desugaring template:

```text
⟦while cond { body }⟧
  =  rec {
       -- check condition on the current state
       keepGoing = cond
       -- if keepGoing, run body and feed back;
       -- if not, exit with the default
       result = if keepGoing
         ⟦body⟧
         else defaultᵦ
       -- feedback: the rebound names in body become the next iteration's
       -- inputs (the feedback wire is the tuple of rebound names)
     }
```

More precisely, the `rec` region has:

- **State wire `S`**: the tuple of feedback names (names rebound in the
  body). On the first iteration, these are seeded with their initial values
  from the enclosing scope.
- **Exit wire `B`**: the result — the last expression in the body,
  evaluated on the final iteration (the iteration where `cond` becomes
  false). If the body never runs (`cond` false on entry), the result is the
  default (§3.4).

The feedback graph:

```text
state₀ ──→ cond ──→ if ──┬──→ body ──→ state₁ ──→ feedback
                         │
                         └──→ exit ──→ output (result)
```

On each iteration:

- `cond` is evaluated on the current state `state₀`.
- If `cond` is true: the body runs, producing a new state `state₁` (the
  rebound names). `state₁` feeds back to become the next iteration's
  `state₀`.
- If `cond` is false: the loop exits. The result is the last expression in
  the body, evaluated on the _final_ iteration — i.e., the state at the
  point where `cond` became false. If the body never ran, the result is the
  default (§3.4).

### 3.3 Feedback-wire naming rule

**The last binding of a given name in the body feeds back into the next
iteration's binding of the same name.** (See §11 for the full rule.)

- If the body rebinds `n` (e.g. `n = n - 1`), the new `n` is the feedback
  value. The feedback edge connects this iteration's `n` to the next
  iteration's `n`.
- Names not rebound in the body are **loop-invariant** — carried through
  unchanged, read from the enclosing scope. They are not part of the
  feedback channel.
- Names introduced fresh in the body (not read from the enclosing scope
  and not rebound) are **local to each iteration** — not fed back.

### 3.4 Result and default (ID.5)

Per ID.5, `while cond { body }` returns the **last expression in the body,
evaluated on the final iteration** (the iteration where `cond` becomes
false). If the body never runs (`cond` false on entry), the result is a
**type-appropriate default inferred by the solver**.

The "type-appropriate default" is defined as follows:

- The result type `B` is the type of the body's last expression.
- The default is the **zero/identity value** of type `B`, inferred by the
  solver:
  - For **records**: an empty record of the right row — `{}` with the row
    variable constrained to the body's result row. If the result row has
    no required fields, `{}` is the default. If it has required fields, the
    solver attempts to fill them with their own defaults; if a field has no
    sensible default, the default is `⊥` (uninhabited) and the programmer
    must guard (e.g. with an `if` before the `while`, or by ensuring the
    loop runs at least once).
  - For **numbers** (`type.Int`, `type.Float`): this is a **library
    concern** — the numeric zero (`0` / `0.0`) is the conventional default,
    but the language does not bake this in; the library
    (`lib-num` or equivalent) provides the zero value. The solver infers the
    default from the library's zero instance for the numeric type.
  - For **`Option`** (`some`/`none`): `none` is the default.
  - For **sum types**: the default is the first nullary constructor, if
    one exists; otherwise `⊥`.
  - If the body type is **uninhabited** (`⊥`), the default is `⊥` and the
    `while` expression has type `⊥` — the programmer must guard or the type
    is uninhabited.

In practice, the most common case is that the programmer ensures the loop
runs at least once (or uses `do { body } while cond` for that purpose), so
the default is never observed. The default is solver-inferred and may be `⊥`
if the body type is uninhabited.

### 3.5 Worked example — countdown

```text
countdown = n ~> {
  while n > 0 {
    n = n - 1
  }
  n
}
```

Desugaring:

```text
⟦while n > 0 { n = n - 1 }⟧
  =  rec {
       -- feedback wire: n (rebound in the body)
       -- state wire S = n
       keepGoing = n > 0
       n' = if keepGoing
         n - 1          -- body: rebind n
         else n          -- exit: keep final n
       -- the feedback edge: n' becomes next iteration's n
       -- exit wire: n' (the last expression, on the final iteration)
     }
```

The feedback wire is `n`: the body rebinds `n = n - 1`, so the new `n`
feeds back. On the final iteration (where `n > 0` is false), the result is
`n` (which is `0`).

Conceptual graph (from ADR-0074):

```text
n ──→ cond ──→ if ──┬──→ n' = n - 1 ──→ feedback
                    │
                    └──→ exit ──→ output
```

The `n = n - 1` inside the body is a new wire per iteration (shadowing),
with the feedback edge connecting each iteration's `n` to the next. This is
exactly what `rec` does (ADR-0074 Addendum A.1); `while` is the common case
where there is one condition and one body, with the feedback made implicit.

Kernel `Loop` form:

```text
Loop { body = arr (λ(input, n).
       let keepGoing = n > 0
       let n' = if keepGoing then n - 1 else n
       (n', n')) }
```

The feedback channel carries `n'`; the output is `n'` (which is `0` when
the loop exits).

---

## 4. `do { body } while cond` — Sugar over `rec`, Body-First (Addendum A.6)

### 4.1 Surface syntax

```text
do {
  body
} while cond
```

The body executes **before** the first condition check — the loop runs at
least once. After each body execution, `cond` is evaluated; if true, the
body runs again; if false, the loop exits with the last body result.

### 4.2 Precise desugaring

`do { body } while cond` desugars to a `rec` region that runs the body
first, then branches on the condition:

```text
⟦do { body } while cond⟧
  =  rec {
       -- run the body first
       result = ⟦body⟧
       -- evaluate condition on the body's result
       continue = cond result
       -- if continue, feedback to re-run body
       -- if !continue, exit with result
       -- the feedback wire is the tuple of rebound names in body
       -- (same naming rule as while, §11)
     }
```

More precisely:

- **State wire `S`**: the tuple of feedback names (names rebound in the
  body, same rule as `while` — §11). On the first iteration, these are
  seeded with their initial values from the enclosing scope.
- **Body runs first**: the body is evaluated, producing a new state and a
  result.
- **Condition check**: `cond` is evaluated on the body's result. If true,
  the new state feeds back and the body runs again. If false, the loop
  exits with the body's result.
- **Exit wire `B`**: the last expression in the body, evaluated on the
  final iteration (same as `while`, ID.5). Since the body always runs at
  least once, there is no default case — the result is always a body
  result.

The feedback graph:

```text
state₀ ──→ body ──→ result ──→ cond ──→ if ──┬──→ state₁ ──→ feedback
                                             │
                                             └──→ exit ──→ output (result)
```

### 4.3 Feedback-wire naming

Same rule as `while` (§3.3, §11): **the last binding of a given name in
the body feeds back into the next iteration's binding of the same name.**
Names not rebound are loop-invariant; names introduced fresh are local to
each iteration.

### 4.4 Result

The result is the **last expression in the body, evaluated on the final
iteration** (same semantics as `while`, ID.5). Since the body always runs at
least once, the result is always a body result — there is no default case
(unlike `while`, which may never run).

### 4.5 Worked examples

#### 4.5.1 `readUntilEmpty`

```text
-- read until empty line (always reads at least once)
readUntilEmpty = input ~> {
  do {
    line = readLine input
  } while line != ""
  line
}
```

Desugaring:

```text
⟦do { line = readLine input } while line != ""⟧
  =  rec {
       -- body runs first
       line = readLine input
       -- check condition
       continue = line != ""
       -- if continue, feedback line and re-run;
       -- if !continue, exit with line
       -- feedback wire: line (rebound in the body)
     }
```

The feedback wire is `line`: the body rebinds `line = readLine input`, so
the new `line` feeds back. On the final iteration (where `line == ""`), the
result is `line` (the empty string).

Kernel `Loop` form:

```text
Loop { body = arr (λ(input, line).
       let line' = readLine input
       let continue = line' != ""
       -- if continue, feedback line'; if not, exit with line'
       (line', line')) }
```

The feedback channel carries `line'`; the output is `line'` (which is `""`
when the loop exits).

#### 4.5.2 `prompt`

```text
-- prompt at least once
prompt = input ~> {
  do {
    answer = askUser input
  } while answer != "yes"
  answer
}
```

Desugaring:

```text
⟦do { answer = askUser input } while answer != "yes"⟧
  =  rec {
       answer = askUser input
       continue = answer != "yes"
       -- if continue, feedback answer and re-run;
       -- if !continue, exit with answer
     }
```

The feedback wire is `answer`. On the final iteration (where
`answer == "yes"`), the result is `answer` (which is `"yes"`).

Kernel `Loop` form:

```text
Loop { body = arr (λ(input, answer).
       let answer' = askUser input
       let continue = answer' != "yes"
       (answer', answer')) }
```

---

## 5. `for x in xs` — Sugar over `rec` + Destructuring (Addendum A.2, ID.6)

### 5.1 Surface syntax

Two forms:

```text
-- map: produce a collection of body results
for x in xs {
  body
}

-- fold: produce a scalar accumulator
for x in xs, acc = init {
  body
}
```

### 5.2 `Iterator` trait requirement (ID.6, ADR-0075)

`for x in xs` requires the input `xs` to satisfy the `Iterator` trait
defined in ADR-0075 (Traits as Arrow Signatures). The `Iterator` trait
provides a `next` operation:

```text
trait Iterator t a {
  next : t ~> Option (a, t)     -- or: t ~> some [a, t] | none
}
```

Where:

- `t` is the iterator type (the collection or stream being iterated).
- `a` is the element type.
- `next` takes the current iterator state and returns either:
  - `some (value, rest)` — the next element and the remaining iterator, or
  - `none` — the iterator is exhausted.

The `for` desugaring calls `Iterator.next` and dispatches via `match` /
`|||` on the `some`/`none` result.

### 5.3 Map desugaring

`for x in xs { body }` desugars to a `rec` region that:

1. Calls `Iterator.next` on the current iterator.
2. Dispatches via `match` on `some(value, rest)` / `none`:
   - `some(value, rest)`: binds `x` to `value`, runs the body, collects the
     body result, and recurses on `rest` (the remaining iterator feeds
     back).
   - `none`: the iterator is exhausted; exit with the collected results.
3. The result is a **collection of body results** — map semantics.

Desugaring template:

```text
⟦for x in xs { body }⟧
  =  rec {
       -- call Iterator.next on the current iterator
       step = Iterator.next iter
       -- dispatch on some/none
       result = match step {
         some: [value, rest] ~> {
           x = value
           bodyResult = ⟦body⟧
           -- collect bodyResult into the output collection
           -- feedback: rest becomes the next iteration's iter
           -- the output collection accumulates bodyResult
         }
         none: collected    -- exit with the collected results
       }
       -- feedback wire: iter (the remaining iterator)
       -- the collected results are carried through (or built via the
       -- collection library)
     }
```

More precisely, the state wire is `S = (iter, collected)` where:

- `iter` is the remaining iterator (feeds back as `rest`).
- `collected` is the accumulated collection of body results (feeds back,
  growing by one `bodyResult` each iteration).

The exit wire is `B = collected` (the full collection when the iterator is
exhausted).

Feedback-wire naming:

- `iter` feeds back (the "rest" of the iterator).
- `collected` feeds back (the growing result collection).
- `x` is **local to each iteration** (bound fresh from `value`, not fed
  back).

### 5.4 Fold desugaring

`for x in xs, acc = init { body }` desugars to the same `rec` region, but
with an accumulator `acc`:

1. Calls `Iterator.next` on the current iterator.
2. Dispatches via `match` on `some(value, rest)` / `none`:
   - `some(value, rest)`: binds `x` to `value`, runs the body (which updates
     `acc`), and recurses on `rest` with the new `acc`.
   - `none`: exit with the final `acc`.
3. The result is the **final `acc`** — fold semantics.

Desugaring template:

```text
⟦for x in xs, acc = init { body }⟧
  =  rec {
       -- call Iterator.next on the current iterator
       step = Iterator.next iter
       -- dispatch on some/none
       result = match step {
         some: [value, rest] ~> {
           x = value
           acc' = ⟦body⟧      -- body updates acc (acc is in scope)
           -- feedback: rest becomes next iter, acc' becomes next acc
         }
         none: acc            -- exit with the final accumulator
       }
       -- feedback wires: iter (rest) and acc (updated)
     }
```

The state wire is `S = (iter, acc)` where:

- `iter` is the remaining iterator (feeds back as `rest`).
- `acc` is the accumulator (feeds back, updated by the body each iteration).

The exit wire is `B = acc` (the final accumulator when the iterator is
exhausted).

Feedback-wire naming:

- `iter` feeds back (the "rest" of the iterator).
- `acc` feeds back (the accumulator, updated by the body).
- `x` is **local to each iteration** (bound fresh from `value`, not fed
  back).

The type checker enforces that the fold form's body produces a value of the
accumulator's type (ADR-0074 Negative): the body's last expression must
have the same type as `acc`.

### 5.5 Worked examples

#### 5.5.1 `doubled` (map)

```text
doubled = xs ~> {
  for x in xs {
    x * 2
  }
}
```

Desugaring:

```text
⟦for x in xs { x * 2 }⟧
  =  rec {
       step = Iterator.next iter
       result = match step {
         some: [value, rest] ~> {
           x = value
           bodyResult = x * 2
           -- collect bodyResult into collected
           -- feedback: iter = rest, collected = collected + [bodyResult]
         }
         none: collected
       }
     }
```

The state wire is `S = (iter, collected)`. The exit wire is `collected`
(the list of doubled values). The feedback wires are `iter` (the remaining
iterator) and `collected` (the growing result list).

Conceptual graph (from ADR-0074):

```text
xs ──→ split ──┬──→ x ──→ f x ──→ collect
               │
               └──→ rest ──→ feedback
                                │
                          (exit when empty)
```

Here "split" is `Iterator.next`, which produces `some(value, rest)` or
`none`. `x` is bound to `value`; `f x` (here `x * 2`) is the body result,
collected into the output. `rest` feeds back to the next iteration. When
`Iterator.next` returns `none`, the loop exits with the collected results.

Kernel `Loop` form:

```text
Loop { body = arr (λ(xs, (iter, collected)).
       let step = Iterator.next iter
       match step {
         some: [value, rest] ~> {
           let x = value
           let bodyResult = x * 2
           (collected + [bodyResult], (rest, collected + [bodyResult]))
         }
         none: (collected, (iter, collected))
       }) }
```

#### 5.5.2 `sum` (fold)

```text
sum = xs ~> {
  for x in xs, acc = 0 {
    acc + x
  }
}
```

Desugaring:

```text
⟦for x in xs, acc = 0 { acc + x }⟧
  =  rec {
       step = Iterator.next iter
       result = match step {
         some: [value, rest] ~> {
           x = value
           acc' = acc + x       -- body updates acc
           -- feedback: iter = rest, acc = acc'
         }
         none: acc              -- exit with final accumulator
       }
     }
```

The state wire is `S = (iter, acc)`, seeded with `(xs, 0)`. The exit wire
is `acc` (the final sum). The feedback wires are `iter` (the remaining
iterator) and `acc` (the updated accumulator).

Kernel `Loop` form:

```text
Loop { body = arr (λ(xs, (iter, acc)).
       let step = Iterator.next iter
       match step {
         some: [value, rest] ~> {
           let x = value
           let acc' = acc + x
           (acc', (rest, acc'))
         }
         none: (acc, (iter, acc))
       }) }
```

### 5.6 Relationship to ADR-0072 and ADR-0073

The `for` form is the surface counterpart to the `loop`-over-event-stream
pattern described in ADR-0072 (Concurrent Arrow Calculus) and the
state-machine loop in ADR-0073 (State Machine Invariants). In ADR-0072, a
concurrent system is modeled as `loop(comp(handle_event, first(id)))` — a
loop over an event stream where the state is the feedback channel. The `for`
form is the surface syntax for this pattern when the "event stream" is a
collection being iterated: the iterator is the stream, the body is the
event handler, and the accumulator (in fold form) is the state. The
feedback-wire naming is consistent with the state-machine model in ADR-0073:
the state wire is the cyclic dependency, and the fixpoint is over the
state.

---

## 6. `??` — Nullish Coalescing (Addendum A.3, ID.9)

### 6.1 Surface syntax

```text
a ?? b
```

### 6.2 Precise desugaring

`a ?? b` desugars to a `match` over the option sum:

```text
⟦a ?? b⟧
  =  match a {
       some: value
       none: b
       _: b
     }
```

- If `a` is `some value`, the result is `value`.
- If `a` is `none`, the result is `b`.
- If `a` is any non-`some`/non-`none` value (defensive), the result is `b`.

This is a **choice operation** — it is `|||` over `some | none` with the
right branch being a constant arrow (`arr (λ_. b)`).

In kernel terms, this is:

```text
arr (λ_. a) >>> arr tag >>> Choice(
  arr (λ(some value). value),    -- left: some → unwrap
  arr (λ_. b)                     -- right: none → b
)
```

The `match` form dispatches via `|||` (Choice): the `some` arm unwraps the
value, the `none` arm (and `_` arm) produce `b`.

### 6.3 The `_` arm and exhaustiveness (ID.13)

The `_` arm is included per the ADR (ADR-0074 Addendum A.3). Per ID.13
(match exhaustiveness required), the match must be exhaustive. The three
arms `some` / `none` / `_` cover all cases:

- `some` — the option has a value.
- `none` — the option is empty.
- `_` — any non-`some`/non-`none` value (defensive, handles the case where
  `a` is not an `Option` at all, or is a different sum type with `some`/
  `none` variants).

The `_` arm is **required** for exhaustiveness when `a`'s type is not
statically known to be exactly `Option`. If `a` is statically typed as
`Option T`, the `some` / `none` arms are exhaustive and the `_` arm is
unreachable (but harmless). If `a`'s type is a row-polymorphic sum that
_might_ have other variants, the `_` arm is needed. The desugaring includes
`_` unconditionally for safety.

### 6.4 `Option` is a library type (ID.9)

`Option` (`some`/`none`) is a library type in `lib-option` (ID.9), not a
language primitive. The `??` operator is surface sugar that desugars to
`match` over the library's `Option` type. The variant names are lowercase
(`some` / `none`), matching the spec's pattern style (ID.4).

### 6.5 Worked example

```text
name = user.name ?? "anonymous"
```

Desugaring:

```text
⟦user.name ?? "anonymous"⟧
  =  match user.name {
       some: value
       none: "anonymous"
       _: "anonymous"
     }
```

If `user.name` is `some "Luis"`, the result is `"Luis"`. If `user.name` is
`none`, the result is `"anonymous"`.

---

## 7. `?.` — Optional Chaining (Addendum A.4)

### 7.1 Surface syntax

```text
user?.address?.city
```

### 7.2 Per-field arrow definition

Each `?.field` is an arrow:

```text
?.field = x ~> match x {
  some: v ~> v.field
  none: none
  _: none
}
```

- If `x` is `some v`, the result is `v.field` (wrapped back in `some` if
  `v.field` is itself an `Option`, or the raw value — the exact wrapping
  depends on the field's type; the arrow projects the field from the
  inner value).
- If `x` is `none`, the result is `none` (short-circuit).
- If `x` is any non-`some`/non-`none` value (defensive `_` arm), the result
  is `none`.

More precisely, `?.field` unwraps the option, accesses the field, and
re-wraps:

```text
?.field = x ~> match x {
  some: v ~> some (v.field)
  none: none
  _: none
}
```

The re-wrapping in `some` ensures the chain stays in `Option` — so a
subsequent `?.` can short-circuit on `none`. (If the field is itself an
`Option`, the re-wrapping is a no-op or flattens, depending on the library
convention; the key property is that `?.` propagates `none`.)

### 7.3 Chain composition via `>>>`

The chain composes via `>>>`:

```text
⟦user?.address?.city⟧
  =  user ~> (?.address >>> ?.city)
```

Once a `?.` hits `none`, every subsequent `?.` returns `none` — composition
short-circuits through `none` because `>>>` propagates `none`: the `?.field`
arrow returns `none` on `none` input, so `?.address >>> ?.city` returns
`none` if `?.address` returned `none`.

This is clean because `>>>` already propagates `none` through the chain —
no special short-circuit machinery is needed. The `?.` arrow is a regular
arrow; composition handles the rest.

### 7.4 Worked example — combining with `??`

```text
city = user?.address?.city ?? "unknown"
```

Desugaring:

```text
⟦user?.address?.city ?? "unknown"⟧
  =  ⟦(user ~> (?.address >>> ?.city)) ?? "unknown"⟧
  =  match (user ~> (?.address >>> ?.city)) {
       some: value
       none: "unknown"
       _: "unknown"
     }
```

Step by step:

1. `user?.address` → `user ~> ?.address` — if `user` is `some u`, returns
   `some u.address`; if `none`, returns `none`.
2. `?.city` — if the previous result is `some addr`, returns
   `some addr.city`; if `none`, returns `none`.
3. `?? "unknown"` — if the result is `some city`, returns `city`; if
   `none`, returns `"unknown"`.

So `city` is `"unknown"` if any link in the chain is `none`, otherwise it
is the city value.

---

## 8. Spread — Construction (Addendum A.5)

### 8.1 What spread is and is not

Spread is a **construction form**, not control-flow sugar. It does **not**
desugar to `match` or `rec`; it is the direct counterpart to rest
destructuring, which is also a primitive pattern form (Spec §11.5). The
kernel sees it as an `arr` node that merges two structural values
(ADR-0074 Addendum A.5).

### 8.2 Surface syntax

```text
-- object spread
{ ...a, b: 2 }

-- multiple spreads (merge)
{ ...a, ...b, c: 3 }

-- positional spread
[...a, b]

-- computed keys + spread
{ ...a, [key]: value }
```

### 8.3 Precise desugaring

Spread desugars to an `arr` merge node. The kernel form is:

```text
⟦{ ...a, b: 2 }⟧
  =  arr (λinput. merge(a, { b: 2 }))
```

where `merge` is a structural merge operation: take all fields of `a`, then
add/override `b: 2`. The `arr` node takes the input (which provides `a` and
any other values in scope) and produces the merged record.

For multiple spreads:

```text
⟦{ ...a, ...b, c: 3 }⟧
  =  arr (λinput. merge(merge(a, b), { c: 3 }))
```

For positional spread:

```text
⟦[...a, b]⟧
  =  arr (λinput. concat(a, [b]))
```

For computed keys + spread:

```text
⟦{ ...a, [key]: value }⟧
  =  arr (λinput. merge(a, { [key]: value }))
```

### 8.4 Structural override rule — "last wins, structurally"

The merge semantics: **later keys/spreads win on conflicts.** This is a
**structural override rule, not a subtyping rule** (ADR-0074 Negative).

Precisely:

- **`{ ...a, b: 2 }`**: the type is "all fields of `a`, plus `b: Int`". If
  `a` already has `b`, the type is **narrowed to `Int`** (the override
  wins). The field `b` from the explicit `b: 2` overrides `a`'s `b`.

- **`{ b: 2, ...a }`**: the type is "all fields of `a`, plus `b: 2`". If
  `a` already has `b`, **`a`'s `b` wins** (because `...a` comes later). The
  spread overrides the earlier explicit field.

- **`{ ...a, ...b }`**: the type is "union of `a`'s and `b`'s fields, with
  `b`'s types winning on conflicts". `b`'s fields override `a`'s fields
  where they overlap, because `...b` comes later.

- **`{ ...a, ...b, c: 3 }`**: union of `a`'s and `b`'s fields (with `b`
  winning on conflicts), plus `c: Int` (which overrides any `c` from `a`
  or `b`, because it comes last).

- **`[...a, b]`**: the type is "positional structure of `a`'s element
  type, plus `b`'s type". The elements of `a` come first, followed by `b`.

The solver derives these from the spread operands' structural types — no
new type machinery, just structural unification with override semantics.
On a field type conflict, the **later operand's type is taken**. This is
the "last wins, structurally" rule (ADR-0074 Negative): it is a structural
override, not a subtyping rule. Programmers who expect subtyping-based
merging (where a narrower type might be widened to a supertype) will find
that the override replaces the type entirely.

### 8.5 The round-trip — immutable record update

Rest destructuring captures `...rest` on the binding side. Spread
re-inserts it on the construction side. They are duals, and the round-trip
is the immutable record update pattern:

```text
{ b, ...rest } = a          -- extract b, capture the rest
newA = { ...rest, b: 2 }    -- re-insert with updated b
```

This is how a field is "mutated" without mutation. The `...rest` captured
on the left is spread back on the right. The `b: 2` override wins because
it comes after `...rest`.

Desugaring of the round-trip:

```text
-- destructuring side:
⟦{ b, ...rest } = a⟧
  =  arr (λa. (a.b, a \ { b }))    -- project b, capture rest (a without b)

-- construction side:
⟦{ ...rest, b: 2 }⟧
  =  arr (λ(rest, b). merge(rest, { b: 2 }))
```

### 8.6 Worked examples

#### 8.6.1 Object spread

```text
{ ...a, b: 2 }
```

Desugaring:

```text
arr (λinput. merge(a, { b: 2 }))
```

Type: all fields of `a`, plus `b: Int`. If `a` has `b`, narrowed to `Int`.

#### 8.6.2 Order matters — later wins

```text
{ ...a, b: 2 }   -- b: 2 wins if a has b
{ b: 2, ...a }   -- a's b wins if a has b
```

Desugaring:

```text
⟦{ ...a, b: 2 }⟧ = arr (λinput. merge(a, { b: 2 }))    -- b: 2 overrides a.b
⟦{ b: 2, ...a }⟧ = arr (λinput. merge({ b: 2 }, a))    -- a.b overrides b: 2
```

#### 8.6.3 Multiple spreads (merge)

```text
{ ...a, ...b, c: 3 }
```

Desugaring:

```text
arr (λinput. merge(merge(a, b), { c: 3 }))
```

Type: union of `a`'s and `b`'s fields (with `b` winning on conflicts),
plus `c: Int`.

#### 8.6.4 Record merge pattern

```text
merged = { ...defaults, ...overrides }
```

Desugaring:

```text
merged = arr (λinput. merge(defaults, overrides))
```

Type: union of `defaults`' and `overrides`' fields, with `overrides`'
types winning on conflicts.

#### 8.6.5 Positional spread

```text
[...a, b]
```

Desugaring:

```text
arr (λinput. concat(a, [b]))
```

Type: positional structure of `a`'s element type, plus `b`'s type.

#### 8.6.6 Computed keys + spread

```text
{ ...a, [key]: value }
```

Desugaring:

```text
arr (λinput. merge(a, { [key]: value }))
```

Spread first, then computed key overrides. The computed key `key` (a
runtime value) overrides any field with that name from `a`.

#### 8.6.7 Round-trip (immutable record update)

```text
{ b, ...rest } = a
newA = { ...rest, b: 2 }
```

Desugaring:

```text
-- destructuring:
arr (λa. (a.b, a \ { b }))     -- project b, capture rest

-- construction:
arr (λ(rest, b). merge(rest, { b: 2 }))
```

#### 8.6.8 Spread in arrow position

```text
withDefaults = input ~> {
  { ...defaults, ...input }
}
```

Desugaring:

```text
withDefaults = input ~> arr (λinput. merge(defaults, input))
```

The arrow takes `input` and merges it over `defaults`. `input`'s fields
win on conflicts (because `...input` comes later).

#### 8.6.9 Composed spread

```text
parseAndMerge = x ~> {
  parsed = parse x
  { ...defaults, ...parsed }
}
```

Desugaring:

```text
parseAndMerge = x ~> {
  parsed = parse x
  arr (λ(parsed. merge(defaults, parsed))
}
```

The arrow parses `x`, then merges the parsed result over `defaults`.

---

## 9. Multi-way `if` — Flat Guard Chains (Addendum A.7)

### 9.1 Surface syntax

```text
if {
  c₁: e₁
  c₂: e₂
  ...
  cₙ: eₙ
  _: eₙ₊₁
}
```

Each arm is a condition expression followed by `:` and a result
expression. The `_` arm is the catch-all (else). This mirrors `match`
syntax — same `{ }` delimiters, same `:` separator, same `_` wildcard —
but each arm is a _guard condition_ rather than a pattern. The `if`
keyword (vs `match`) signals the difference.

The parser distinguishes multi-way `if` from regular `if` by the token
immediately following `if`: if it is `{`, the form is multi-way; if it is
an expression, the form is the regular `if cond body` (Spec §8.2).

### 9.2 Precise desugaring

Multi-way `if` desugars to nested `if`/`else`:

```text
⟦if {
  c₁: e₁
  c₂: e₂
  ...
  cₙ: eₙ
  _: eₙ₊₁
}⟧
  =  if c₁
       e₁
     else if c₂
       e₂
     else ...
     else if cₙ
       eₙ
     else
       eₙ₊₁
```

The general n-arm template:

```text
⟦if { c₁: e₁, c₂: e₂, ..., cₙ: eₙ, _: e_default }⟧
  =  if c₁
       ⟦e₁⟧
     else
       if c₂
         ⟦e₂⟧
       else
         ...
         if cₙ
           ⟦eₙ⟧
         else
           ⟦e_default⟧
```

Each `if`/`else` further desugars to `arr` + `choice` (per the §17.2
table: `if c e1 else e2` → `arr c >>> choice ⟦e1⟧ ⟦e2⟧`).

### 9.3 Exhaustiveness (ID.13)

Exhaustiveness is **required** (ID.13): the compiler requires a catch-all
`_` arm or proof that the conditions cover all cases, exactly as for
`match`. A multi-way `if` without a `_` arm is accepted only if the
compiler can prove the conditions are exhaustive (e.g. `x > 0`, `x < 0`,
`x == 0` covers all integers). Otherwise, a `_` catch-all is mandatory.

### 9.4 Worked example

```text
if
  x > 0: "positive"
  x < 0: "negative"
  x == 0: "zero"
  _: "unknown"
```

Desugaring:

```text
⟦if { x > 0: "positive", x < 0: "negative", x == 0: "zero", _: "unknown" }⟧
  =  if x > 0
       "positive"
     else if x < 0
       "negative"
     else if x == 0
       "zero"
     else
       "unknown"
```

Further desugaring (to kernel):

```text
arr (λx. x > 0) >>> Choice(
  arr (λ_. "positive"),
  arr (λx. x < 0) >>> Choice(
    arr (λ_. "negative"),
    arr (λx. x == 0) >>> Choice(
      arr (λ_. "zero"),
      arr (λ_. "unknown")
    )
  )
)
```

---

## 10. `return` Inside Loop Bodies

### 10.1 The rule

Per ADR-0074 Negative, a `return` inside a `while` / `do while` / `for`
body should **exit the enclosing arrow, NOT just the loop**. This is the
interaction of ID.14 (`return` scope = innermost enclosing `~>`) with the
loop desugaring: since `while` / `do while` / `for` desugar to `rec`
regions, and `rec` is NOT an arrow (it is a region _inside_ an arrow), a
`return` in the loop body must propagate through the feedback/exit
machinery to exit the enclosing `~>` arrow, not the `rec` region.

### 10.2 The precise mechanism — exit-wire tagging

The desugaring handles `return` in a loop body by **tagging the exit wire**
of the `rec` region. The `rec` region's exit wire carries a tagged value:

```text
Exit = Normal result | ReturnRequested value
```

Where:

- `Normal result` is the normal loop result (the last body expression on
  the final iteration).
- `ReturnRequested value` is a signal that a `return` was executed in the
  body, carrying the return value.

The desugaring rewrites each `return e` inside the loop body to:

```text
return e  →  set exit = ReturnRequested e; break feedback
```

And the enclosing arrow checks the exit wire after the `rec` region:

```text
⟦x ~> { ... while cond { ... return e ... } ... }⟧
  =  x ~> {
       rec {
         -- ... loop body with return rewritten ...
         -- if return e is hit: exit = ReturnRequested e, break feedback
         -- if normal exit: exit = Normal result
       }
       -- check exit tag
       match exit {
         Normal: result → result
         ReturnRequested: value → return value    -- exits the enclosing ~>
       }
     }
```

The `return value` in the `ReturnRequested` arm exits the enclosing `~>`
arrow (ID.14), propagating the return value out of the arrow. The `rec`
region terminates (the feedback is broken by the `ReturnRequested` tag),
and the arrow exits with the returned value.

### 10.3 Justification

This mechanism is chosen over alternatives for the following reasons:

1. **It respects ID.14.** `return` exits the innermost enclosing `~>`. The
   `rec` region is not a `~>` — it is a region inside a `~>`. So `return`
   must escape the `rec` and reach the enclosing `~>`. The exit-wire
   tagging does exactly this: the `return` is propagated through the
   `rec`'s exit wire to the enclosing arrow, which then executes the
   `return`.

2. **It does not require new kernel combinators.** The tagging is a
   desugaring-time transformation: the `return` is rewritten to a
   `ReturnRequested` tag, and the enclosing arrow checks the tag. No new
   kernel combinator is needed — just `match` / `|||` (Choice) on the
   tagged exit wire.

3. **It composes with the feedback machinery.** The `ReturnRequested` tag
   breaks the feedback (the loop terminates) and carries the return value
   out. This is consistent with how `return` works in graph blocks
   (Spec §7.3): `return` terminates a path early. In a loop, "early"
   means "before the loop would naturally exit."

4. **It is simpler than hoisting.** An alternative would be to hoist the
   `return` to the enclosing arrow level via a continuation/call-cc
   mechanism. This is more complex and requires higher-order control flow
   that the arrow calculus does not provide natively. The exit-wire
   tagging is a local transformation within the `rec` region.

### 10.4 Worked example

```text
findFirst = xs ~> {
  for x in xs {
    if x > 0
      return x
  }
  0
}
```

Desugaring (simplified, showing the `return` handling):

```text
⟦xs ~> { for x in xs { if x > 0 return x } 0 }⟧
  =  xs ~> {
       rec {
         step = Iterator.next iter
         exit = match step {
           some: [value, rest] ~> {
             x = value
             -- body: if x > 0, return x
             if x > 0
               ReturnRequested x      -- return rewritten to tag
             else
               Normal bodyResult      -- continue loop
             -- feedback: iter = rest (if Normal), break (if ReturnRequested)
           }
           none: Normal collected      -- normal exit: return collected
         }
       }
       -- check exit tag
       match exit {
         Normal: result → result
         ReturnRequested: value → return value    -- exits the enclosing ~>
       }
     }
```

If a positive `x` is found, the loop body sets `exit = ReturnRequested x`,
breaking the feedback. The enclosing arrow checks the tag and executes
`return x`, exiting the arrow with `x`. If no positive `x` is found, the
loop exits normally with `Normal collected`, and the arrow returns `0` (the
fallback after the loop).

### 10.5 `return` in `while` and `do while`

The same mechanism applies to `while` and `do while`: a `return` in the
body is rewritten to a `ReturnRequested` tag on the `rec` region's exit
wire, and the enclosing arrow checks the tag. The feedback is broken
(the loop terminates) and the arrow exits with the returned value.

---

## 11. Feedback-Wire Naming — The General Rule

### 11.1 The rule

This section consolidates the feedback-wire naming rule for `while` / `do
while` / `for`, which was an explicit ADR-0074 Negative item ("the precise
interaction with parallel independent wires in the body needs to be
written down").

**The last binding of a given name in the loop body feeds back into the
next iteration's binding of the same name.**

### 11.2 Detailed specification

1. **Rebound names feed back.** If a name `n` appears as an input to the
   loop body (read from the enclosing scope, or from a previous
   iteration's binding) and is rebound in the body (`n = ...`), the
   **last binding** of `n` in the body is the feedback value. The feedback
   edge connects this iteration's `n` to the next iteration's `n`.

2. **Loop-invariant names are carried through.** Names read from the
   enclosing scope but **not rebound** in the body are loop-invariant —
   they are carried through unchanged on each iteration. They are NOT part
   of the feedback channel; they are read from the enclosing scope on
   every iteration (or, equivalently, they are constant across iterations).

3. **Fresh names are local to each iteration.** Names introduced fresh in
   the body (not read from the enclosing scope and not a rebind of an
   existing name) are **local to each iteration** — they are not fed back.
   Each iteration gets a fresh binding. (Exception: in a `for` fold, the
   accumulator `acc` is fed back even though it is "introduced" by the
   `acc = init` syntax — the `acc = init` is the initial seed, and the
   body's rebind of `acc` feeds back.)

4. **Shadowing is per-iteration.** `n = n - 1` inside a loop is a new wire
   `n` per iteration (shadowing), with the feedback edge connecting each
   iteration's `n` to the next. This is exactly what `rec` does (ADR-0074
   Addendum A.1): the `rec` region creates a new wire per iteration, and
   the feedback edge connects them. The "old" `n` (from the previous
   iteration or the enclosing scope) is read on the right-hand side; the
   "new" `n` (the rebind) is the feedback value.

### 11.3 Interaction with parallel independent wires

If the body has multiple independent bindings (wires with no dependency
between them), each is evaluated per iteration. Only the ones that are
**rebound** (same name as an input or a previous iteration's binding) feed
back. The feedback graph is over the rebound names.

Example:

```text
while cond {
  a = f a          -- a is rebound: feeds back
  b = g b          -- b is rebound: feeds back
  c = a + b        -- c is fresh (not an input): local to each iteration
  d = h x          -- d is fresh (x is loop-invariant): local to each iteration
}
```

Feedback wires: `a` and `b` (both rebound). `c` and `d` are local to each
iteration (not fed back). `x` is loop-invariant (read from the enclosing
scope, not rebound).

The state wire is `S = (a, b)`. The feedback edge connects this iteration's
`(a, b)` to the next iteration's `(a, b)`. `c` and `d` are computed fresh
each iteration from the current `a`, `b`, and `x`.

### 11.4 Multiple rebinds of the same name

If a name is rebound multiple times in the body, the **last** binding is
the feedback value:

```text
while cond {
  n = n + 1        -- first rebind of n
  n = n * 2        -- second rebind of n (last): this is the feedback value
}
```

The feedback value is the `n` from `n = n * 2` (the last binding). The
first `n = n + 1` is an intermediate wire within the iteration.

### 11.5 Consistency with the state-machine model (ADR-0073)

The feedback-wire naming rule is consistent with the state-machine model in
ADR-0073: the state wire is the cyclic dependency (the rebound names), and
the fixpoint is over the state. In ADR-0073, a state machine is
`loop(comp(handle_event, first(id)))` — the state is the feedback channel,
and `handle_event` updates the state. The `while` / `do while` / `for`
desugarings follow the same pattern: the feedback channel carries the
rebound names (the state), and the body updates them.

---

## 12. Imports and Exports — Normalization to Projection (ID.16, ADR-0069)

This section specifies the precise normalization of the import and export
surface forms into the kernel's projection and module-reference nodes. The
semantic model is fixed by ADR-0069: **import = projection**, **export =
visibility sugar**. The normalization strategy (§12.5) is an implementation
choice; the desugaring below is strategy-independent.

ADR-0069 §6 originally specified no `export` keyword in v0.1 — all named
arrows in a record are accessible via projection. `export` is now added as
opt-in visibility sugar, which the ADR explicitly permits as a future sugar
addition. The `export` layer does not introduce a new runtime concept; it
filters which fields of the file's record arrow are exposed to importers.

### 12.1 Surface syntax

The import forms (top-level only, conventionally before bindings):

```text
import name from "path"
import name1, name2 from "path"
import name as local from "path"
import "path" as alias
```

The export forms (top-level, may appear anywhere among bindings):

```text
export name                      -- mark an existing binding as public
export name = expr               -- binding + export in one
export name1, name2              -- mark several existing bindings public
export *                         -- all bindings in the file are public
export name from "path"          -- re-export: sugar for import + export
export * from "path"             -- re-export all of a module's public names
```

### 12.2 Desugaring of import forms

Each import form normalizes to a `Project` binding (field projection) or a
`ModuleRef` binding (whole module reference). `Project` is `first` + `arr`
(field projection); `ModuleRef` is an opaque reference to a module's arrow,
resolved by a normalization strategy (§12.5).

```text
⟦import name from "path"⟧
  =  name = Project { field: "name", record: ModuleRef { path: "path" } }

⟦import name1, name2 from "path"⟧
  =  name1 = Project { field: "name1", record: ModuleRef { path: "path" } }
     name2 = Project { field: "name2", record: ModuleRef { path: "path" } }

⟦import name as local from "path"⟧
  =  local = Project { field: "name", record: ModuleRef { path: "path" } }

⟦import "path" as alias⟧
  =  alias = ModuleRef { path: "path" }
```

For a single-expression file (no record), the `Project` of the module's arrow
yields the module's arrow itself — the projection of a non-record arrow is
the arrow. The `import "path" as alias` form binds the whole record arrow,
enabling `alias.field` via the existing field-access syntax (spec §11.2).

Multi-name import produces one `Project` binding per name, all referencing
the same `ModuleRef`. Imports are idempotent: repeated imports of the same
name from the same path normalize to the same projection node (deduplicated by
the compiler under Strategy A/B, or served from cache under Strategy C).

`App` (already a kernel combinator, ADR-0052) is used when an imported name
is applied: `sort([3, 1, 2])` becomes `App { callee: "sort", args:
[const([3, 1, 2])] }`, where `"sort"` resolves to the `Project` binding's
cached arrow/contract.

### 12.3 Desugaring of export forms

`export` constructs an **export set** — the set of public names that filter
the file's record arrow. It does not introduce a new runtime concept.

```text
⟦export name⟧
  =  (add "name" to the export set)
     -- "name" must be a binding in the file

⟦export name = expr⟧
  =  name = expr            -- the binding
     (add "name" to the export set)

⟦export name1, name2⟧
  =  (add "name1", "name2" to the export set)

⟦export *⟧
  =  (add all named bindings in the file to the export set)

⟦export name from "path"⟧
  =  name = Project { field: "name", record: ModuleRef { path: "path" } }
     (add "name" to the export set)

⟦export * from "path"⟧
  =  (for each public name nᵢ of "path":
       nᵢ = Project { field: "nᵢ", record: ModuleRef { path: "path" } }
     add all nᵢ to the export set)
```

**Record filtering.** A file's record arrow is a record literal of the
exported names (or all names if no `export` declarations are present). If the
file has `export` declarations, only the names in the export set appear as
fields of the file's record arrow; non-exported bindings are private helpers
that do not appear in the record. If the file has no `export` declarations,
all named bindings are public (the arrow-native default, ADR-0069 §6).

### 12.4 The file-arrow rule

A file's arrow is determined by its structure:

- **Single-expression file** (no bindings, no exports): the file's arrow is
  that expression's arrow. Its type is the expression's arrow type.

```text
-- file: sort.hnl
loop(comp(insert, first(id)))
-- file's arrow = loop(comp(insert, first(id)))
-- type: List α ~> List α
```

- **Multi-name file** (bindings, with or without exports): the file's arrow
  is a record literal of the exported names (or all named bindings if no
  `export` declarations). Its type is `Unit ~> Record`.

```text
-- file: collection.hnl
export sort, head
cons = arr("list.cons")       -- private helper (not exported)
head = arr("list.head")
sort = loop(comp(insert, first(id)))
-- file's arrow = { head: arr("list.head"), sort: loop(...) }
-- type: Unit ~> { head: Arrow, sort: Arrow }
-- "cons" is private: not in the record, not accessible to importers
```

- **Re-export file** (only `export ... from` declarations): the file's arrow
  is a record literal of the re-exported names, each a `Project` binding.

### 12.5 Normalization strategies (ADR-0069 §5)

The semantic abstraction — import = projection — is fixed. The realization
is an implementation choice. Three strategies:

#### Strategy A: compile-time desugar (eager, static)

Imports are resolved during parsing/normalization. Each `import` becomes a
`Project { field, record: ModuleRef { path } }` node in the Scheme IR. After
normalization, no import syntax remains — only projections and `App`
references. The `ModuleRef` is resolved to the module's `Scheme` at
normalize time.

```text
source: import sort from "collection/sort"
  ↓ normalize
Scheme:  sort = Project { field: "sort", record: <collection/sort's Scheme> }
```

- **Pros**: No runtime module loading. The IR is self-contained. Inference
  sees the full graph structure (projections are transparent).
- **Cons**: Every import is resolved upfront. Large dependency trees produce
  large IR. No dynamic loading.

#### Strategy B: whole-program flattening (eager, inlined)

The entire multi-file program normalizes into a single arrow graph. All
`Project` / `App` / `ModuleRef` nodes resolve to inlined subgraphs. One
graph, no module boundaries, no indirection.

```text
main.hnl + collection/sort.hnl + collection/insert.hnl
  ↓ flatten
single Scheme graph (no Project, no App — all inlined)
```

- **Pros**: Maximally simple IR — one graph, no indirection. Inference
  traces the entire program in one pass.
- **Cons**: No separate compilation. Re-flatten on any change. The graph can
  be very large. Loses module boundaries for debugging.

#### Strategy C: runtime module loading (lazy, cached)

Imports are resolved on first access. The module loader (§12.6) parses the
file, infers its contract, caches both, and returns the projected arrow.
`ModuleRef` is resolved at runtime.

```text
source: import sort from "collection/sort"
  ↓ at first access
load collection/sort.hnl → parse → infer → cache
return Project { field: "sort", record: <cached Scheme> }
```

- **Pros**: Lazy — only load what's used. Supports dynamic loading and REPL
  workflows. Module boundaries preserved for debugging.
- **Cons**: Runtime loading overhead (amortized by cache). Inference must
  handle `App` references to cached contracts.

The three strategies are not mutually exclusive. A toolchain may use Strategy
A for production builds, Strategy B for whole-program inference, and Strategy
C for REPL/development. The contract cache (§12.6) is used in all three —
even flattening benefits from caching inferred contracts for shared
subgraphs.

### 12.6 Pluggable resolvers and the two caches

Module resolution is a **host capability boundary**
([ADR-0046](../../project/adrs/0046-capability-discipline-at-the-language-level.md)).
A `ModuleResolver` trait resolves a module path to its source:

```text
ModuleResolver {
  resolve(path) -> ResolvedModule { path, source, origin }
}
```

Built-in resolvers:

- **`FileResolver`** — resolves paths against a filesystem root. The default
  for compiled builds and file-based projects.
- **`MemoryResolver`** — resolves paths against an in-memory map of path to
  source. Used for REPL, tests, and virtual environments.
- **`ChainResolver`** — tries resolvers in order, returning the first match.
- **`CachingResolver`** — wraps another resolver and caches resolved modules
  by path.

The resolver set is a host capability: a host may allow filesystem-only
resolution, deny HTTP/git resolution, etc. This keeps module loading within
the host's security boundary. The pluggable resolver architecture follows
[ADR-0028 — Pluggable Module Composition](../../project/adrs/0028-pluggable-module-composition.md)
and
[ADR-0035 — Loaders as Plugins](../../project/adrs/0035-loaders-as-plugins.md).

A `ModuleLoader` maintains two caches keyed by module path (ADR-0069 §4):

- **Graph cache**: `path → Scheme` — the parsed arrow graph, used for
  execution.
- **Contract cache**: `path → Contract` — the inferred contract, used for
  verification.

Both caches are populated when a module is first imported. Subsequent imports
return the cached entries. This enables **compositional inference**: each
module is inferred once, and its contract is reused by importers. The
inference engine does not re-trace imported arrows — it looks up their cached
contracts.

### 12.7 Worked examples

#### 12.7.1 Simple import

```text
-- main.hnl
import sort from "collection/sort"
sort([3, 1, 2])
```

Desugars to:

```text
sort = Project { field: "sort", record: ModuleRef { path: "collection/sort" } }
App { callee: "sort", args: [const([3, 1, 2])] }
```

Under Strategy A, `ModuleRef` is resolved to `collection/sort`'s `Scheme` at
normalize time. Under Strategy C, it is resolved on first access via the
loader (parse → infer → cache).

#### 12.7.2 Multi-name import

```text
-- main.hnl
import sort, head from "collection"
head(sort([3, 1, 2]))
```

Desugars to:

```text
sort = Project { field: "sort", record: ModuleRef { path: "collection" } }
head = Project { field: "head", record: ModuleRef { path: "collection" } }
App { callee: "head", args: [App { callee: "sort", args: [const([3, 1, 2])] }] }
```

Both projections reference the same `ModuleRef`; the loader parses
`collection` once (under Strategy C).

#### 12.7.3 Import with alias

```text
-- main.hnl
import "collection" as coll
coll.sort([3, 1, 2])
```

Desugars to:

```text
coll = ModuleRef { path: "collection" }
App { callee: "coll.sort", args: [const([3, 1, 2])] }
```

`coll.sort` is field access on the module's record arrow (spec §11.2),
desugaring to `Project { field: "sort", record: coll }` followed by `App`.

#### 12.7.4 Export visibility (private helper)

```text
-- collection.hnl
export sort, head
cons = arr("list.cons")              -- private helper
head = arr("list.head")
sort = loop(comp(insert, first(id)))
```

The export set is `{ sort, head }`. The file's record arrow is:

```text
{ head: arr("list.head"), sort: loop(comp(insert, first(id))) }
```

`cons` is a private helper — it is not in the record, so
`import cons from "collection"` is a compile error. Without the `export`
declarations, all three names would be public (the arrow-native default).

#### 12.7.5 Re-export

```text
-- utils.hnl
export sort from "collection/sort"
export head from "collection"
```

Desugars to:

```text
sort = Project { field: "sort", record: ModuleRef { path: "collection/sort" } }
head = Project { field: "head", record: ModuleRef { path: "collection" } }
-- export set = { sort, head }
-- file's arrow = { sort: Project{...}, head: Project{...} }
```

An importer of `utils` gets `sort` and `head` without needing to know they
originate from `collection/sort` and `collection` respectively.

#### 12.7.6 Contracts compose across files

```text
-- collection/insert.hnl
loop(comp(compare, choice(cons, cons)))
-- Inferred contract: Sorted(output)

-- collection/sort.hnl
import insert from "collection/insert"
loop(comp(insert, first(id)))
-- Inferred contract: Sorted(output) — derived from insert's cached contract

-- main.hnl
import sort from "collection/sort"
import map from "fn/map"
import filter from "fn/filter"
comp(comp(map(double), filter(is_even)), sort)
-- Inferred contract: Sorted(output) — derived from sort's cached contract
```

Each file is inferred once. Contracts compose via the contract cache. No
re-inference of imported arrows. This holds under all three strategies —
even flattening benefits from caching inferred contracts for shared
subgraphs (e.g., when `map` is imported by multiple files).

---

## 13. Desugaring Summary Table

The table below maps each surface form to its desugared form, with a
reference to the section in this document. This is the detailed version of
the Spec §17.2 desugaring summary table.

| Surface form                                  | Desugars to                                                             | Section | Notes                                                                                 |
| --------------------------------------------- | ----------------------------------------------------------------------- | ------- | ------------------------------------------------------------------------------------- |
| `rec { ... }`                                 | `Loop` region (kernel)                                                  | §2      | Paterson `loop`; state wire = cyclic deps, exit wire = result (ID.3)                  |
| `while cond { body }`                         | `rec` with implicit feedback                                            | §3      | Result = last body expr on final iteration (ID.5); default if body never runs         |
| `while cond body`                             | `rec` with implicit feedback                                            | §3      | Same as braced form                                                                   |
| `do { body } while cond`                      | `rec`, body-first                                                       | §4      | Runs at least once; result = last body expr (ID.5)                                    |
| `for x in xs { body }`                        | `rec` + `Iterator.next` + `match`                                       | §5      | Map semantics; requires Iterator (ID.6, ADR-0075)                                     |
| `for x in xs, acc = init { body }`            | `rec` fold                                                              | §5      | Fold semantics; body must produce acc's type                                          |
| `a ?? b`                                      | `match a { some: value, none: b, _: b }`                                | §6      | `                                                                                     |     |     | `over Option;`_` arm for exhaustiveness (ID.13) |
| `user?.field`                                 | `>>> (?.field)` arrow                                                   | §7      | `?.field = x ~> match x { some: v ~> v.field, none: none }`; short-circuits on `none` |
| `user?.address?.city`                         | `user ~> (?.address >>> ?.city)`                                        | §7      | Chain composes via `>>>`; `none` propagates                                           |
| `{ ...a, b: 2 }`                              | `arr` merge node                                                        | §8      | Construction form, NOT control-flow sugar; last wins structurally                     |
| `{ ...a, ...b, c: 3 }`                        | `arr` merge node                                                        | §8      | Merge; later spreads override earlier on conflicts                                    |
| `[...a, b]`                                   | `arr` merge node                                                        | §8      | Positional spread; concat                                                             |
| `{ ...a, [key]: value }`                      | `arr` merge node                                                        | §8      | Computed key overrides spread                                                         |
| `{ b, ...rest } = a` then `{ ...rest, b: 2 }` | `arr` project + `arr` merge                                             | §8.5    | Round-trip immutable record update                                                    |
| `if { c₁: e₁, ..., _: eₙ }`                   | nested `if`/`else`                                                      | §9      | Exhaustiveness required (ID.13)                                                       |
| `if c e1 else e2`                             | `arr c >>> choice ⟦e1⟧ ⟦e2⟧`                                            | §9      | Conditional routing (kernel)                                                          |
| `match v { p: e }`                            | `arr v >>> choice ...`                                                  | —       | Pattern dispatch via `                                                                |     |     | `                                               |
| `return` in loop body                         | exit-wire tagging (`ReturnRequested`)                                   | §10     | Exits enclosing `~>`, not just the loop (ID.14)                                       |
| `import name from "path"`                     | `name = Project { field: "name", record: ModuleRef { path: "path" } }`  | §12     | ID.16, ADR-0069; normalization to projection                                          |
| `import name1, name2 from "path"`             | one `Project` binding per name                                          | §12     | ID.16, ADR-0069; multi-name projection                                                |
| `import name as local from "path"`            | `local = Project { field: "name", record: ModuleRef { path: "path" } }` | §12     | ID.16, ADR-0069; project + rename                                                     |
| `import "path" as alias`                      | `alias = ModuleRef { path: "path" }`                                    | §12     | ID.16, ADR-0069; bind whole record arrow                                              |
| `export name`                                 | `name` added to export set                                              | §12     | ADR-0069 §6; visibility sugar; `name` must be a binding                               |
| `export name = expr`                          | binding `name = expr` AND `name` in export set                          | §12     | ADR-0069 §6; binding + export                                                         |
| `export *`                                    | all bindings added to export set                                        | §12     | ADR-0069 §6; all-public via explicit declaration                                      |
| `export name from "path"`                     | `name = Project { ... }` AND `name` in export set                       | §12     | ADR-0069 §6; re-export (import + export)                                              |
| `export * from "path"`                        | import all public names as `Project` bindings, all in export set        | §12     | ADR-0069 §6; re-export all                                                            |

### 13.1 Surface core forms (not desugared further at the surface level)

These are the surface core forms that denote kernel combinators directly.
They are the target of all desugaring above, and are lowered to the kernel
by the ADR-0052 lowering pass.

| Surface core  | Kernel combinator      | ADR-0052        |
| ------------- | ---------------------- | --------------- |
| `x ~> e`      | `arr (λx. ⟦e⟧)`        | `Arr`           |
| `f >>> g`     | `Seq f g`              | `Seq`           |
| `f *** g`     | `first f` over product | `First`         |
| `f &&& g`     | fan-out to pair        | `First` + `Arr` |
| `f \|\|\| g`  | `Choice f g`           | `Choice`        |
| `rec { ... }` | `Loop` region          | `Loop`          |
| `app(f, x)`   | `App { callee, args }` | `App`           |

---

## Related

- [ADR-0052 — Arrow Calculus Kernel](../../project/adrs/0052-arrow-calculus-kernel.md)
  — defines the kernel (`arr` / `>>>` / `first` / `choice` / `loop` /
  `app`) that all surface forms desugar to. The `loop` correction
  (feedback, not iteration), the derived forms section, and the `proc`
  notation / `x = y` binding section are the primary references for the
  `rec` desugaring. `App` is the combinator used when an imported name is
  applied (§12).
- [ADR-0069 — Files Are Arrows](../../project/adrs/0069-arrow-native-modules.md)
  — the module model: import normalizes to projection, export is opt-in
  visibility sugar, and the three normalization strategies (§12.5) are
  defined here. §6 originally specified no `export` in v0.1; `export` is
  now added as opt-in visibility sugar, which the ADR explicitly permits.
- [ADR-0028 — Pluggable Module Composition](../../project/adrs/0028-pluggable-module-composition.md)
  — the pluggable module composition architecture that the resolver
  framework (§12.6) follows.
- [ADR-0035 — Loaders as Plugins](../../project/adrs/0035-loaders-as-plugins.md)
  — loaders as plugins, complementing the pluggable resolver architecture
  (§12.6).
- [ADR-0046 — Capability Discipline at the Language Level](../../project/adrs/0046-capability-discipline-at-the-language-level.md)
  — the capability boundary that module resolvers (§12.6) operate within.
- [ADR-0072 — Concurrent Arrow Calculus](../../project/adrs/0072-concurrent-arrow-calculus.md)
  — the loop-over-event-stream pattern that `for x in xs` is the surface
  counterpart of for collection iteration.
- [ADR-0073 — State Machine Invariants](../../project/adrs/0073-state-machine-invariants.md)
  — `loop`-based fixpoint discovery; `rec` is the surface counterpart, and
  `while` / `for` desugar to it. The feedback-wire naming rule is
  consistent with the state-machine model here.
- [ADR-0074 — Arrow Surface Syntax v0.1 — Redesign](../../project/adrs/0074-arrow-syntax-v0_1-surface-redesign.md)
  — the decision ADR. Addendum A.1–A.7 are the primary source for the
  desugaring; ID.3 (rec typing — Paterson loop), ID.5 (while result — last
  expression), ID.6 (for requires Iterator trait), ID.13 (match
  exhaustiveness), ID.14 (return scope = innermost `~>`), and the
  Negative consequences about feedback-wire naming and `return` in loop
  bodies are the primary references.
- [ADR-0075 — Traits as Arrow Signatures](../../project/adrs/0075-traits-as-arrow-signatures.md)
  — the trait system (`trait` / `impl` / `law`, trait inference, catalog).
  Required for `for x in xs` (Iterator trait) and in scope for v0.1.
- [Arrow Language Specification v0.1](./ARROW_LANGUAGE_SPEC_V0_1.md) — the
  authoritative source for the v0.1 surface syntax. §3.3 (Imports), §3.4
  (Exports), §3.5 (Module Resolvers), §3.6 (Normalization Strategies),
  §12 (Control Flow), §11 (Spread), and §17.2 (desugaring summary table)
  are the primary references. This document is the detailed companion to
  §17.2.
