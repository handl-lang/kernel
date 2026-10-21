# Arrow Calculus Formalization (Phase 1)

## Overview

This document formalizes the Arrow Calculus variant we'll use as the basis for the PoC. We adopt the core from **Lindley–Wadler–Yallop (2008)** with integration of **Sanada (2024)** for handler semantics.

---

## Syntax

### Abstract Syntax

```
Types:
  τ, σ ∈ Type ::= α                    -- type variable
                 | τ → σ               -- function type
                 | τ ~> σ              -- arrow type
                 | (τ × σ)             -- product
                 | (τ + σ)             -- sum
                 | [τ]                 -- list
                 | ⊤                   -- unit type

Terms:
  e ∈ Expr ::= x                       -- variable
             | c                       -- constant (literals, primitives)
             | arr e                   -- lift function to arrow
             | e >>> f                 -- composition (seq)
             | first e                 -- fanout first component
             | choice e f              -- if-then-else for sums
             | loop e                  -- feedback
             | app                     -- dynamic application (ArrowApply)
             | e e'                    -- function application (in lifted context)
             | λx. e                   -- lambda (for comparison only; we'll translate these to arrows)
             | let x = e in e'         -- let-binding

Values:
  v ∈ Value ::= c                      -- constant
              | (v, v)                 -- product value
              | Left v | Right v       -- sum value
              | []  | (v : vs)         -- list
              | Arrow e                -- arrow as value (for app)

```

### Informal Semantics

| Construct    | Meaning                                                                          |
| ------------ | -------------------------------------------------------------------------------- |
| `arr f`      | Lift pure function `f : τ → σ` to arrow `τ ~> σ`                                 |
| `f >>> g`    | Compose arrows: output of `f` feeds to input of `g`                              |
| `first f`    | Apply `f` to first component of product, pass through second                     |
| `choice f g` | On `Left x`, apply `f`; on `Right y`, apply `g`                                  |
| `loop f`     | Feedback: given `f : (τ × ρ) ~> (σ × ρ)`, produce `τ ~> σ` with state `ρ` hidden |
| `app`        | Dynamic application: arrow takes another arrow as input and applies it           |

---

## Type System

### Judgments

```
Γ ⊢ e : τ         -- term e has type τ in context Γ
```

### Inference Rules

#### Variables and Constants

```
                  x : τ ∈ Γ
────────────────────────────── (Var)
  Γ ⊢ x : τ


────────────────────────────── (Const-Int)
  Γ ⊢ n : Int

────────────────────────────── (Const-String)
  Γ ⊢ "s" : String
```

#### Arrow Primitives

```
  Γ ⊢ f : τ → σ
────────────────────────────── (Arr)
  Γ ⊢ arr f : τ ~> σ


  Γ ⊢ f : τ ~> σ    Γ ⊢ g : σ ~> ρ
────────────────────────────────────── (Composition)
  Γ ⊢ f >>> g : τ ~> ρ


  Γ ⊢ f : τ ~> σ
────────────────────────────────────────── (First)
  Γ ⊢ first f : (τ × ρ) ~> (σ × ρ)


  Γ ⊢ f : τ ~> σ    Γ ⊢ g : ρ ~> σ
────────────────────────────────────── (Choice)
  Γ ⊢ choice f g : (τ + ρ) ~> σ


  Γ ⊢ f : (τ × ρ) ~> (σ × ρ)
────────────────────────────────── (Loop)
  Γ ⊢ loop f : τ ~> σ


────────────────────────────────────────── (App)
  Γ ⊢ app : (τ ~> σ, τ) ~> σ
```

#### Lambda and Application

```
  Γ, x : τ ⊢ e : σ
────────────────────────────── (Lambda)
  Γ ⊢ λx. e : τ → σ


  Γ ⊢ f : τ → σ    Γ ⊢ e : τ
────────────────────────────── (Application)
  Γ ⊢ f e : σ


  Γ ⊢ e : τ    Γ, x : τ ⊢ e' : σ
────────────────────────────────── (Let)
  Γ ⊢ let x = e in e' : σ
```

#### Operators & Primitives

```
  Γ ⊢ e1 : Int    Γ ⊢ e2 : Int
────────────────────────────────────── (Plus)
  Γ ⊢ e1 + e2 : Int

  [similar for -, *, /, ==, <, >, etc.]


  Γ ⊢ e : Bool    Γ ⊢ e1 : τ    Γ ⊢ e2 : τ
────────────────────────────────────────────── (IfThenElse)
  Γ ⊢ if e then e1 else e2 : τ
```

---

## Operational Semantics (Big-Step)

### Evaluation

```
Evaluation judgment:  e ⟹ v
(Read: "e evaluates to value v")
```

#### Arrow Values

Arrows are represented as closures during evaluation. We need to extend our value domain:

```
Values:
  v ∈ Value ::= n : Int
              | s : String
              | (v, v)              -- product
              | Left v | Right v    -- sum
              | []  | v : vs        -- list
              | ⟨arr, f⟩            -- arrow value (stores function)
              | ⟨comp, f, g⟩        -- composed arrows (explicit)
              | ⟨first, f⟩          -- first arrow (explicit)
              | ⟨choice, f, g⟩      -- choice arrow (explicit)
              | ⟨loop, f⟩           -- loop arrow (explicit)
```

### Arrow Evaluation Rules

```
  f ⟹ v
────────────────────────────── (Arr)
  arr f ⟹ ⟨arr, f⟩


  f ⟹ ⟨arrow, _⟩    g ⟹ ⟨arrow, _⟩
──────────────────────────────────────── (Composition)
  f >>> g ⟹ ⟨comp, f, g⟩


  f ⟹ ⟨arrow, _⟩
──────────────────────────── (First)
  first f ⟹ ⟨first, f⟩


  f ⟹ ⟨arrow, _⟩    g ⟹ ⟨arrow, _⟩
────────────────────────────────────── (Choice)
  choice f g ⟹ ⟨choice, f, g⟩


  f ⟹ ⟨arrow, _⟩
──────────────────────────── (Loop)
  loop f ⟹ ⟨loop, f⟩
```

### Arrow Application (Running Arrows)

These rules define how arrows are **executed** given input.

```
Execution judgment:  arrow_value · input_value ⟹ output_value

  f ⟹ ⟨arr, func⟩    func(x) ⟹ v
──────────────────────────────────────── (Exec-Arr)
  ⟨arr, func⟩ · x ⟹ v


  f ⟹ ⟨comp, f', g⟩    ⟨f'⟩ · x ⟹ v'    ⟨g⟩ · v' ⟹ v
────────────────────────────────────────────────────────── (Exec-Comp)
  ⟨comp, f', g⟩ · x ⟹ v


  f ⟹ ⟨first, f'⟩    let (a, b) = x in ⟨f'⟩ · a ⟹ v'
────────────────────────────────────────────────────────────── (Exec-First)
  ⟨first, f'⟩ · (a, b) ⟹ (v', b)


  x = Left a    f ⟹ ⟨choice, f', g'⟩    ⟨f'⟩ · a ⟹ v
──────────────────────────────────────────────────────────────── (Exec-Choice-L)
  ⟨choice, f', g'⟩ · x ⟹ v

  x = Right b    g ⟹ ⟨choice, f', g'⟩    ⟨g'⟩ · b ⟹ v
──────────────────────────────────────────────────────────────── (Exec-Choice-R)
  ⟨choice, f', g'⟩ · x ⟹ v


  f ⟹ ⟨loop, step⟩    let (a, s0) = (x, s_init) in
  ⟨step⟩ · (a, s0) ⟹ (v1, s1)  ...  ⟨step⟩ · (v_n, s_n) ⟹ (v_final, s_final)
  until termination condition
────────────────────────────────────────────────────────────────────────────────────── (Exec-Loop)
  ⟨loop, step⟩ · x ⟹ v_final
```

Note: `loop` requires a **termination condition** or a handler to decide when to stop iterating.

### Function Application

```
  f ⟹ λx. e    e' ⟹ v'    [v'/x] e ⟹ v
──────────────────────────────────────── (App-Lambda)
  (f e') ⟹ v
```

---

## Semantics: Arrow Laws

The Arrow Calculus satisfies these algebraic laws:

### Identity

```
arr id >>> f  ≡  f
f >>> arr id  ≡  f
```

### Composition Associativity

```
(f >>> g) >>> h  ≡  f >>> (g >>> h)
```

### First Homomorphism

```
first (arr f)  ≡  arr (λ(x,y). (f x, y))
```

### Composition through First

```
first (f >>> g)  ≡  (first f) >>> (first g)
```

### Exchange Law

```
first f >>> arr (λ((x,y),z). ((x,z),y)) >>> first g
  ≡  arr (λ((x,y),z). ((x,z),y)) >>> first (f >>> g)
```

(These ensure arrows form a category with additional structure.)

---

## Translation: Lambda to Arrow

Given a lambda term `e : τ → σ`, we want to produce an arrow term `e' : τ ~> σ`.

### Translation Rules

```
Translation judgment:  ⟦ e ⟧_arr = e'
(Read: "lambda term e translates to arrow term e'")

⟦ λx. x ⟧_arr  =  arr id

⟦ λx. c ⟧_arr  =  arr (λ_. c)    -- constant function

⟦ λx. e ⟧_arr  =  arr (λx. ⟦ e ⟧_λ)    -- lift the body

⟦ e1 e2 ⟧_arr  =  ⟦ e1 ⟧_arr >>> (app with ⟦ e2 ⟧_arr)    -- function application

⟦ e1 >>> e2 ⟧_arr  =  ⟦ e1 ⟧_arr >>> ⟦ e2 ⟧_arr    -- already an arrow

⟦ if cond then e1 else e2 ⟧_arr
  =  arr cond >>> choice ⟦ e1 ⟧_arr ⟦ e2 ⟧_arr
```

**Key insight:** Each lambda is wrapped in `arr`, treating the function body as a pure computation. Application is handled by combining arrows.

---

## Example Programs

### Example 1: Identity

**Lambda version:**

```
id = λx. x : a → a
```

**Arrow version:**

```
id = arr (λx. x) : a ~> a
```

**Evaluation:**

```
id · 5 ⟹ 5
```

---

### Example 2: Composition of Functions

**Lambda version:**

```
add1 = λx. x + 1 : Int → Int
mul2 = λx. x * 2 : Int → Int
compose f g = λx. g (f x) : (Int → Int) → (Int → Int) → (Int → Int)
result = compose add1 mul2  5  ≡  (5 + 1) * 2 = 12
```

**Arrow version:**

```
add1 = arr (λx. x + 1) : Int ~> Int
mul2 = arr (λx. x * 2) : Int ~> Int
composed = add1 >>> mul2 : Int ~> Int
result = composed · 5 ⟹ 12
```

---

### Example 3: Higher-Order (Apply Twice)

**Lambda version:**

```
applyTwice f x = f (f x) : (a → a) → (a → a)
applyTwice (λx. x + 1) 5  ≡  ((5 + 1) + 1) = 7
```

**Arrow version:**

```
applyTwice f = f >>> f : (a ~> a) → (a ~> a)
applyTwice (arr (λx. x + 1)) · 5 ⟹ 7
```

---

### Example 4: Feedback (Counter)

**Arrow version (canonical):**

```
counter : () ~> Int
counter = loop step
  where step : ((), Int) ~> (Int, Int)
        step = arr (λ((), s). (s, s + 1))
```

**Execution:** `counter · () ⟹ 0`, `counter · () ⟹ 1`, ...

(State is threaded internally by `loop`.)

---

### Example 5: Factorial via Feedback

**Recursive function (for reference):**

```
fact : Int → Int
fact n = if n <= 1 then 1 else n * fact (n - 1)
```

**Arrow version (state machine):**

```
factorial : Int ~> Int
factorial = loop step
  where
    step : (Int, (Int, Int)) ~> (Int, (Int, Int))
    step = arr (λ(n, (acc, _)).
      if n <= 1
        then (acc, (n, acc))
        else ((n-1) * acc, (n-1, (n-1)*acc)))
```

**Evaluation:**

```
factorial · 5
  ⟹ step executes multiple times
  ⟹ returns 120
```

---

## Open Questions for Implementation

1. **Termination:** How does `loop` know when to stop?
   - Option A: Fixed iteration count
   - Option B: Explicit termination arrow
   - Option C: Handler-based (lazy evaluation, step-by-step control)

2. **Higher-order arrows:** Can arrows take arrows as input (for `applyTwice`)?
   - How does the type system work?
   - Does `app` handle this, or do we need special syntax?

3. **Effects (Operations):** How do we integrate Sanada's operations + handlers?
   - Extend arrow syntax with `operation` declarations?
   - Extend handler syntax?

4. **Type inference:** How do we infer types for arrow programs?
   - Adapt Hindley–Milner to arrow types?
   - Constraint-based approach?

These will be addressed in the prototype implementation phase.

---

## Summary

We've formalized:

- **Syntax:** Arrow primitives, lifted functions, products, sums
- **Types:** Arrow types, function types, polymorphism (placeholder)
- **Semantics:** Big-step evaluation, arrow execution
- **Laws:** Arrow algebra (identity, composition, etc.)
- **Translation:** From lambda to arrow
- **Examples:** Identity, composition, higher-order, feedback, recursion

Next: Build a prototype interpreter to test these examples.

---

## Effects & Handlers (Phase 2)

We extend the calculus with **operations** and **handlers** following
Sanada (2024). The central idea: a program mentions _operations_ without
committing to an interpretation; a _handler_ supplies the interpretation.
Handlers compose by **pass through** — a handler intercepts its own
operations and rebuilds foreign ones with itself re-applied to the
continuation, so an outer handler eventually sees them.

### Syntax extension

```
Operations:
  op ∈ Op ::= Get | Put | Read | Write | Throw      -- effect signatures

Computations (freer arrow):
  C ∈ Comp ::= Pure v
             | Op op arg k                          -- perform op, continue with k
             | bind C k                             -- sequence (C then k)

  v ∈ Value, k : Value -> Comp                      -- continuation
```

An operation node `Op op arg k` is _suspended_: it carries its argument and
a continuation waiting for the operation's result. This is the arrow analogue
of a free-monad `Pure`/`Free` pair, with continuations in arrow position.

### Operation signatures

```
operation Get   : ()       ~> State      -- read current state
operation Put   : State    ~> ()         -- overwrite state
operation Read  : ()       ~> String     -- read one input
operation Write : String   ~> ()         -- emit one output
operation Throw : String   ~> _          -- raise an exception (aborting)
```

### Handler semantics

A handler `H` interprets a subset of operations. The defining rule is
**pass-through** for operations it does not own:

```
                                  H handles op
────────────────────────────────────────────────────────────── (Handle-Op)
  H (Op op arg k)  =  Op op arg (λr. H (k r))


  H handles Get, state = s
────────────────────────────────────────── (Handle-Get)
  H_s (Op Get _ k)  =  H_s (k s)


  H handles Put, state = s
────────────────────────────────────────── (Handle-Put)
  H_s (Op Put s' k)  =  H_{s'} (k ())


  H handles Throw
────────────────────────────────────────── (Handle-Throw)
  H (Op Throw msg k)  =  Pure (Left msg)        -- continuation discarded


  H (Pure v)  =  Pure v                          (Handle-Pure)
```

### Handler stacking

Because of pass-through, handlers stack by ordinary function composition:

```
run = handle_exception ∘ handle_io ∘ handle_state      (outermost last)
```

The **order** of handlers is observable and corresponds exactly to monad
transformer order:

| Handler order           | Transformer analogue  | On throw            |
| ----------------------- | --------------------- | ------------------- |
| exception outside state | `StateT s (Except e)` | state **lost**      |
| state outside exception | `ExceptT e (State s)` | state **preserved** |

The program text is identical in both cases; only the handler stack differs.
This is the arrow-calculus counterpart of choosing a transformer stack, with
no monad primitive required.

### Mid-program catch

A `try/catch` is just a handler applied to a sub-computation, branching on
the resulting `Either`:

```
try_catch body handler =
  case handle_exception body of
    Right v  -> v
    Left err -> handler err
```

No special syntax or primitive is needed — handlers are first-class
functions over computations.

### Relation to monads

Each handler recovers a monad's behaviour:

| Effect    | Monad      | Arrow handler                                         |
| --------- | ---------- | ----------------------------------------------------- |
| State     | `State s`  | `handle_state` threads `s` through Get/Put            |
| IO        | `IO`       | `handle_io` threads inputs/outputs through Read/Write |
| Exception | `Except e` | `handle_exception` catches Throw → `Either`           |

The monad **laws** are recovered from handler laws (identity, composition,
association of pass-through). No monad, transformer, or `bind` primitive is
introduced — only operations and handler functions over the freer arrow.

---

## Language Protocol & Generic Tooling (Phase 3)

We extend the calculus with a first-class **Language** protocol: a record of
arrows. Because every language operation is an arrow `Value ~> Comp`, the
operations compose with `>>>` (`seq`), and a generic tool can be assembled
as an arrow pipeline parameterized only by the `Language` record. The same
tool code then runs unchanged over any language instance.

### The Language protocol

```
Language =
  { name      : String
  , parse     : Text         ~> AST          -- source text -> abstract syntax tree
  , eval      : (AST, Env)   ~> Value        -- evaluate an AST in an environment
  , format    : AST          ~> Text         -- pretty-print an AST back to text
  , typecheck : AST          ~> Type         -- check an AST, yielding its type
  , lit       : Value        ~> AST          -- embed a primitive value as a
                                             -- literal AST node (inverse of
                                             -- eval on literals)
  }
```

Each field is an arrow `Rc<dyn Fn(Value) -> Comp>` in the freer-arrow model.
Errors (parse failure, unbound variables, type mismatches) are raised with
the `Throw` operation and caught with `handle_exception`, reusing the Phase 2
handler machinery — no new effect primitive is introduced.

### AST representation

ASTs are tagged `Value`s, so they are first-class data that arrows can
inspect and rebuild:

```
AST  ::= Product(Str tag, List [arg1, ..., argn])

-- Arithmetic instance:
--   Product("Int", [Int n]) | Product("Var", [Str x])
--   Product("Add", [a, b])  | Product("Mul", [a, b])

-- Boolean instance:
--   Product("Bool", [Bool b]) | Product("Var", [Str x])
--   Product("And", [a, b])    | Product("Or", [a, b]) | Product("Not", [a])
```

### Typing of the protocol

The protocol operations have arrow types, so they compose by ordinary arrow
composition:

```
parse     : Text  ~> AST
format    : AST   ~> Text
eval      : (AST × Env) ~> Value
typecheck : AST   ~> Type
lit       : Value ~> AST
```

Derived pipelines (all are arrows, by composition):

```
parse >>> format >>> parse          : Text  ~> AST        -- round-trip
parse >>> typecheck                 : Text  ~> Type       -- check a source file
parse >>> (arr (λast. (ast, env))) >>> eval : Text ~> Value  -- run a source file
```

### Generic tooling semantics

A generic tool is a function `&Language -> ...` that builds arrow pipelines
from the language's own arrows. Three are defined:

**Pretty-printer.** `pretty_print L ast = run (L.format ast)`. Uses only the
language's `format` arrow.

**Error reporter.** Runs `L.typecheck ast` then `L.eval (ast, env)`, each
under `handle_exception`, branching on the resulting `Either`:

```
report_error L ast env =
  case handle_exception (L.typecheck ast) of
    Left msg -> "Type error: "   ++ msg
    Right ty -> case handle_exception (L.eval (ast, env)) of
                  Left msg  -> "Runtime error: " ++ msg
                  Right v   -> "OK (" ++ ty ++ "): " ++ show v
```

**Optimizer (constant folding).** Recursively optimizes children, then
attempts to evaluate the node with an empty environment. If evaluation
succeeds, the node is replaced by its literal value via `L.lit`; otherwise
the node is kept with its optimized children:

```
optimize L (Product tag args) =
  let args' = map (optimize L) args
      node' = Product tag args'
  in case handle_exception (L.eval (node', empty_env)) of
       Right v -> (case handle_exception (L.lit v) of
                     Right lit -> lit | Left _ -> node')
       Left  _ -> node'
optimize L leaf = leaf
```

The crucial property: `optimize`, `pretty_print`, and `report_error` mention
**no language-specific detail**. They are assembled entirely from the
language's own arrows plus the generic tagged-AST structure. The same
function applied to two different `Language` instances produces
language-specific results.

### Genericity law

For any two languages `L1`, `L2` and any generic tool `T`:

```
T L1  ≠  T L2            (in general — results are language-specific)
T L1 (parse_L1 s)        is well-defined for any source s in L1
T L2 (parse_L2 s)        is well-defined for any source s in L2
```

The tool code is identical in both cases; only the `Language` parameter
differs. This is the arrow-calculus analogue of a compiler/tooling plugin
interface, expressed without any new primitive — only arrow composition over
a record of arrows.

---

## Effect Typing (Deep Dive)

We extend the type system so that arrow types carry an **effect row** — the
set of operations a computation may perform. This is the arrow-calculus
analogue of effect inference in algebraic-effect systems (Bauer & Pretnar,
Frank, Koka): the effect row is inferred statically by traversing the
computation tree, and handlers act as **effect eliminators** that remove
their owned operations from the row.

### Effect row syntax

```
Effect ε ::= ∅                         -- pure (no operations)
           | {op₁, ..., opₙ}           -- ground row of known operations
           | {op₁, ..., opₙ, ρ}        -- row with a polymorphic tail ρ

op ∈ Op ::= Get | Put | Read | Write | Throw
```

An effect-typed computation has the form `τ / ε`: a value type `τ` paired
with an effect row `ε`.

### Effect-typed arrow types

Arrow types are extended to carry an effect:

```
τ ~> σ / ε    (arrow from τ to σ with effect ε)
```

Operation signatures (each operation contributes its effect singleton):

```
get    : ()       ~> State  / {Get}
put    : State    ~> ()     / {Put}
read   : ()       ~> String / {Read}
write  : String   ~> ()     / {Write}
throw  : String   ~> α      / {Throw}     -- α polymorphic; never returns
pure v : τ        ~> τ      / ∅
```

### Static computation tree

The freer-arrow `Comp = Pure v | Op op arg k` uses closure continuations
(`Rc<dyn Fn>`), which are not statically traversable. For inference we use a
**static computation tree** `IComp` that mirrors `Comp` but stores
continuations as explicit sub-trees:

```
IComp ::= Pure IValue
        | Op IOp IValue Type IComp      -- op, arg, result type, continuation
```

The result type annotates what the operation hands to its continuation; the
continuation is an explicit `IComp` sub-tree, so the whole computation can be
walked.

### Inference rules

The effect of a tree is the set of operations appearing in it; the type is
the type of the rightmost `Pure`:

```
────────────────────────────────────── (Eff-Pure)
  Pure v : type_of_value(v) / ∅


  k : τ / ε
────────────────────────────────────────── (Eff-Op)
  Op op arg ρ k : τ / ({op} ∪ ε)
```

where `ρ` is the operation's result type (the type handed to `k`), and
`type_of_value` recovers the type of a leaf value. Effects **accumulate** by
union as we descend the continuation chain — the arrow analogue of effect
accumulation in `bind`/`>>>`.

### Handler as effect eliminator

A handler _removes_ its owned operations from the effect row; foreign
operations remain (pass-through). This is the typing counterpart of the
Phase 2 pass-through semantics:

```
  c : τ / ε
────────────────────────────────────────────────── (Handle-State)
  handle_state c : τ / (ε \ {Get, Put})


  c : τ / ε
────────────────────────────────────────────────── (Handle-IO)
  handle_io c : τ / (ε \ {Read, Write})


  c : τ / ε
────────────────────────────────────────────────── (Handle-Exception)
  handle_exception c : τ' / (ε \ {Throw})
```

(`τ'` differs from `τ` for the exception handler, which wraps results in
`Either`; the effect-elimination rule is what matters here.)

### Handler stacking

A handler stack eliminates operations left to right (innermost first):

```
  c : τ / ε
────────────────────────────────────────────────────────────── (Handle-Stack)
  (Hₙ ∘ ... ∘ H₁) c : τ / (ε \ (ops(H₁) ∪ ... ∪ ops(Hₙ)))
```

### Effect safety

A computation is **safe to run** when its remaining effect row is empty after
the handler stack has been applied. A non-empty remaining row is the static
counterpart of Phase 2's runtime error `UnhandledOp`:

```
  c : τ / ε      ε \ (ops(stack)) = ∅
────────────────────────────────────────── (Safe)
  run (stack c) : τ

  c : τ / ε      ε \ (ops(stack)) ≠ ∅
────────────────────────────────────────── (Unhandled)
  run (stack c) : error (unhandled: ε \ ops(stack))
```

### Polymorphic effect rows

A row may carry a **row variable** `ρ` standing for an unknown tail of
foreign operations:

```
ε ::= {op₁, ..., opₙ, ρ}
```

A handler eliminates its own operations from the _known_ part and **leaves
the row variable intact** (the unknown tail may still contain foreign ops
that pass through). Two rows unify when their known operations are
compatible and at least one side has a row variable that can absorb the
other's extra operations:

```
  {Get, ρ} ⊔ {Put}  =  {Get, Put, ρ}      -- ρ absorbs Put
  {Get}    ⊔ {Put}  =  ⊥                   -- ground rows must agree
```

This is the row-polymorphic effect system of Koka/Frank, recast for arrow
operations: a polymorphic arrow may have effect `{Get, Put, ρ}` — it performs
State operations plus whatever `ρ` is instantiated to by its context.

## Structural Preservation (Challenge #9)

### The question

Does translating an arrow computation into monadic (Kleisli) form preserve
the structural information that makes the arrow representation useful for
static analysis?

### Three representations

```
Freer arrow:
  Comp = Pure v | Seq f g | Fanout f g | Choice f g | Op op k | Loop f
  — continuations are explicit sub-trees (defunctionalized)
  — fully traversable: structure is data

Opaque monad:
  M<B> = { run : (input, state) -> (B, state) }
  — continuation is a closure (Rc<dyn Fn>)
  — black box: can only run, cannot inspect

Freer monad:
  FreeM = Pure v | Ident | FreeOp op k | Bind m k | Fanout f g | Choice f g
  — continuations are explicit sub-trees (defunctionalized)
  — fully traversable: structure is data
```

### Translation: Arrow → Opaque monad

```
Pure v        →  pure v
Ident         →  \input state -> (input, state)
Seq f g       →  f >>= g                    (bind: g depends on f's output)
Fanout f g    →  \input state ->            (both consume same input)
                  let (v1, s1) = run f input state
                  let (v2, s2) = run g input s1
                  (Pair v1 v2, s2)
Choice f g    →  \input state ->            (branch hidden in closure)
                  case input of
                    Left v  -> run f v state
                    Right v -> run g v state
Op Get k      →  \input state -> run k state state
Op Put k      →  \input state -> run k Unit input
Op Throw      →  \_ _ -> error
```

### Preservation / loss rules

| Property               | Arrow      | Opaque monad                 | Freer monad     |
| ---------------------- | ---------- | ---------------------------- | --------------- |
| Sequential composition | explicit   | explicit (bind)              | explicit (Bind) |
| Fanout / independence  | explicit   | **LOST** (hidden in closure) | explicit        |
| Choice / branching     | explicit   | **LOST** (hidden in closure) | explicit        |
| Effect set             | traversal  | **LOST** (cannot inspect)    | traversal       |
| Per-branch effects     | per branch | **LOST** (union only)        | per branch      |
| Dependency graph       | buildable  | **LOST** (no structure)      | buildable       |
| Feedback               | explicit   | **LOST**                     | detectable      |
| Semantic results       | correct    | correct                      | correct         |

### The central finding

The opaque monad is **semantically adequate** (same results) but
**structurally lossy** (independence, branching, per-branch effects,
dependency graph — all lost). The freer monad recovers all structure,
proving the loss is about **opacity** (closures hide structure), not
about monadic structure per se.

### The false-dependency phenomenon

When arrow fanout (`f &&& g` — independent) is translated to monadic
bind, the second computation appears to depend on the first's result:

```
Arrow: f &&& g           → no edge f→g in dependency graph (independent)
Monad: f >>= (\v1 -> g)  → g appears to depend on v1 (false dependency)
```

The bind chain creates an apparent dependency that doesn't exist
semantically. This is the structural cost of encoding fanout through
`>>=`.

## Minimality: Independence of the Five Primitives (Challenge #10)

### The five primitives

```
arr   : (A → B) → α A B               (lifting)
comp  : α A B → α B C → α A C         (composition)
first : α A B → α (A × C) (B × C)     (products / fanout)
loop  : α (A × C) (B × C) → α A B     (feedback)
left  : α A B → α (Sum A C) (Sum B C) (sums / choice)
```

### Independence proof (free-arrow / initiality argument)

For each primitive, define the free arrow WITHOUT that constructor and
show no remaining constructor introduces the relevant type structure.

**`left` not derivable from `arr + comp + first + loop`:**
No structural constructor produces `Sum` on the output.

- `firstF` produces `(B × C)` — a product, never a sum
- `loopF` produces `B` — no `Sum`
- `compF` produces `C` — no `Sum` from `compF` itself
- Only `arrF` can produce `Sum`, requiring user-supplied `Sum`-handling

**`first` not derivable from `arr + comp + loop`:**
No constructor produces `×` on the output.

- `compNF` produces `C` — no `×`
- `loopNF` produces `B` — no `×`
- Only `arrNF` can produce `×`, requiring user-supplied product-handling

**`loop` not derivable from `arr + comp + first` (total setting):**
No constructor introduces feedback. The free arrow without `loop` is
strictly acyclic — every term is a finite tree with forward data flow.
No constructor has the feedback shape `α (A × C) (B × C) → α A B`.

**`comp` not derivable from the rest:**
No other combinator chains two arrows sequentially.

**`arr` not derivable from the rest:**
No other combinator lifts a pure function into the arrow.

### Mechanization

7 theorems in Lean4 (`lean/ArrowMinimalityLib/Basic.lean`), all proved
by `rfl` — the type signatures ARE the proof.

### Caveat on `loop`

`loop` is independent only in a _total_ setting. In a language with
general recursion (`fix`), `loop` is derivable:
`loop f a = let (b, c) = fix (λ c => f (a, c)) in b`.
But then `fix` is the primitive. For a total arrow calculus (type-level
guarantees), `loop` is independent.

### The minimality theorem

> The minimal arrow calculus for a total PL requires exactly five
> independent primitives: `arr`, `comp`, `first`, `loop`, `left`.
> No primitive can be derived from the others.
