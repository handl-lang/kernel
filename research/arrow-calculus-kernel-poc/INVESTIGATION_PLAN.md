# PoC Investigation Plan

## Phase 1: Foundation & Basics (Challenges 1–2)

### 1.1 Formalize Arrow Calculus Variant

**Objective:** Define our specific arrow calculus with precise syntax and typing.

**Scope:**

- Core syntax: `arr`, `>>>`, `first`, `choice`, `loop`, `app`
- Type rules based on Lindley–Wadler–Yallop and Sanada
- Operational semantics (big-step or small-step)

**Deliverables:**

- Formal grammar (EBNF or similar)
- Inference rules (typing)
- Reduction rules (semantics)
- Example programs (simple: composition, feedback, choice)

**Success:** We can type-check and evaluate simple arrow programs.

---

### 1.2 Translate Lambda Programs → Arrows

**Objective:** Show that lambda patterns can be systematically encoded as arrows.

**Approach:**

- Start with a minimal lambda-calculus core (variables, abstraction, application, let-binding)
- Define a translation function: `λ-term → arrow-term`
- Test on increasingly complex lambdas (identity, const, composition, higher-order)

**Key translation decisions to investigate:**

- How does `λx. e` become an arrow construct?
- How does function application `f e` become arrow application?
- How do we handle currying and partial application?

**Test cases:**

```
λx. x                  -- identity
λx. λy. x              -- const
λf. λx. f (f x)        -- functional abstraction
λf. λl. map f l        -- higher-order
(λx. x + 1) 5          -- application
```

**Success:** Each λ-term translates to an equivalent arrow term with the same observable behavior.

---

## Phase 2: Abstraction & Parametricity (Challenges 2–3)

### 2.1 Define Parametric Arrow Constructs

**Objective:** Invent an arrow-based primitive that plays the role of `λ` without using lambda.

**Candidates to explore:**

- **Partial application via `arr`:** Can we use `arr f` to "bake in" a function, then compose it?
- **Implicit parameters via type class/handler:** Use the type system to supply implicit arguments?
- **Multi-shot arrows:** Define arrows that can be instantiated multiple times with different parameters?
- **Generic combinators:** Define `map`, `fold`, `traverse` as primitive arrow combinators?

**Experiments:**

- Encode `map :: (a -> b) -> [a] -> [b]` as an arrow
- Encode `fold :: (b -> a -> b) -> b -> [a] -> b` as an arrow
- Test that these can be composed with other arrows

**Success:** We have a construct that allows parametric definitions and can be applied dynamically (like lambda), and it composes well with arrow primitives.

---

### 2.2 Polymorphism in Arrow Types

**Objective:** Extend the arrow type system with type variables.

**Scope:**

- Type variables: `forall a. a ~> a`
- Arrow polymorphism: `forall a b. (a ~> b) -> (a ~> b)`
- Generic combinators: `map :: forall a b. (a ~> b) -> [a] ~> [b]`

**Test:**

- Can we infer principal types for polymorphic arrows?
- Do type variable instantiations work as expected?

**Success:** Polymorphic arrow types are well-defined, and we can instantiate them correctly.

---

## Phase 3: Recursion & Iteration (Challenge 5)

### 3.1 Encode Recursion via Feedback (`loop`)

**Objective:** Show that recursive functions can be lowered to arrows + feedback.

**Pattern:** A recursive function is typically a fixpoint:

```haskell
fact n = if n == 0 then 1 else n * fact (n-1)
```

We want to express this as a state machine (feedback):

```
State = (n, accumulator)
Step: (n, acc) ~> (result, (n', acc'))
fact = loop step
```

**Test cases:**

- Factorial (linear recursion)
- Fibonacci (tree recursion)
- List fold (tail recursion)
- Tree walk (nested recursion)
- Mutual recursion (A calls B calls A)

**Encoding approach:**

1. Identify the recursion structure (tail, tree, mutual)
2. Encode as a state machine with feedback
3. Prove equivalence to the original recursive definition

**Success:** Each recursive pattern translates to arrow + feedback cleanly, with the same termination and complexity properties.

---

### 3.2 Derive Fixpoint Combinator from Arrows

**Objective:** Show that `fix` / Y-combinator can be defined, not primitively.

**Goal:**

```
fix : (a ~> b) -> (a ~> b)
```

Such that `fix f` repeatedly applies `f` according to some termination condition.

**Investigation:**

- Can we express Y-combinator as an arrow program?
- What is the relationship between `loop` and `fix`?
- Can we use `loop` to define `fix`?

**Success:** We can define `fix` (or a functional equivalent) using arrow primitives.

---

## Phase 4: Effects & Handlers (Challenge 6)

### 4.1 Encode Monadic Effects via Arrow Operations

**Objective:** Show that monadic effects (IO, State, Exceptions) can be encoded as arrow operations + handlers.

**Approach:**

1. Define a small set of **operations** (e.g., `read : () -> Env`, `write : Env -> ()`)
2. Define **handlers** that interpret these operations (Sanada's model)
3. Show that monadic effect patterns (state threading, error handling) emerge from this

**Test effects:**

- **IO:** Read/write operations, sequencing
- **State:** Get/put operations, state threading
- **Exceptions:** Throw/catch operations, error propagation

**Encoding example (State):**

```
operation Get : Unit ~> State
operation Put : State ~> Unit

handler stateHandler =
  { Get -> λ s. (s, s)
  , Put -> λ s. ((), s)
  }
```

**Success:** We can express IO, State, and Exceptions via operations + handlers, and the result behaves like the equivalent monad.

---

### 4.2 Compare to Monad Transformers

**Objective:** Assess whether handler-based composition is cleaner than monad transformers.

**Comparison:**

- Monad transformer: `newtype StateT s m a = StateT (s -> m (a, s))`
- Handler approach: Operations define interface, handlers implement it

**Questions:**

- Do multiple effects compose as easily?
- Is the order of effects (i.e., which effect runs "on top"?) as explicit?
- Can we recover monad transformer patterns from handlers?

**Success:** Handler composition is at least as clean as monad transformers, with no loss of expressiveness.

---

## Phase 5: Metaprogramming & Tooling (Challenges 7–8)

### 5.1 Sketch First-Class Language Protocol

**Objective:** Define what it means for a language to be "first-class" and manipulable.

**Core operations:**

```
type Language =
  { parse : Text ~> AST
  , eval : AST ~> Value
  , format : AST ~> Text
  , typecheck : AST ~> Type
  , ... other operations
  }
```

**Invariant:** All operations are arrows, so they can be composed, modified, and chained generically.

**Test:**

- Can we define a language instance (even minimal)?
- Can we apply a single generic handler/transformer to multiple language instances?

**Success:** The protocol is coherent, and we can instantiate it for at least two different languages.

---

### 5.2 Generic Tooling Demo

**Objective:** Build one language-agnostic tool to demonstrate the concept.

**Candidates:**

- **Pretty-printer:** Format any language's AST
- **Evaluator:** Evaluate any language with a standard semantics
- **Tracer/debugger:** Trace evaluation of any language

**Example: Generic pretty-printer**

```
prettyPrint : forall lang. Language lang -> AST lang ~> Text
```

**Success:** The tool works on multiple language instances without duplication.

---

## Phase 6: Falsification & Friction Points

### 6.1 Search for Gaps

**For each challenge, document:**

- What works smoothly?
- Where is the friction?
- What had to be added (beyond core arrows) to make it work?
- Is the addition arrow-compatible or does it violate the foundation?

### 6.2 Propose Resolutions

**For each friction point:**

- Is it a fundamental limitation, or a gap in the design?
- Can it be resolved by tweaking the arrow calculus, the handler model, or the metaprogramming layer?
- Would resolving it require primitives outside the arrow universe?

### 6.3 Document the Verdict

**Outcome:** For each challenge, write a brief verdict:

- ✓ **Smooth:** Challenge is well-addressed by arrow primitives
- ⚠ **Manageable:** Challenge requires some care, but can be solved within the framework
- ✗ **Problematic:** Challenge reveals a gap that arrow calculus cannot easily bridge

---

## Deliverables by Phase

| Phase | Deliverable                                     | Form                                            |
| ----- | ----------------------------------------------- | ----------------------------------------------- |
| 1     | Arrow calculus formalization + translator       | Formal grammar, inference rules, implementation |
| 2     | Parametric arrow constructs                     | Definition + examples                           |
| 3     | Recursion encoding (factorial, fold, tree walk) | Arrow programs + proof of equivalence           |
| 4     | State/IO/Exception handlers                     | Handler implementations + example programs      |
| 5     | Language protocol + generic tool                | Protocol definition + working tool              |
| 6     | Friction analysis                               | Friction report + resolutions                   |

---

## Success Criteria

The PoC succeeds if:

1. **Challenges 1–5** are addressed with no fundamental gaps requiring lambda calculus.
2. **Challenges 6–8** are addressed with a coherent protocol and at least one working tool.
3. **No irreducible primitive** outside the arrow universe is discovered to be necessary.
4. **Friction points** are identified but resolvable within the arrow framework.

If the answer to all 8 challenges is "yes with minor caveats," the hypothesis is supported and worthy of a full formal development.

If a fundamental gap emerges (e.g., "you need lambda for X"), the hypothesis is _refined_, not abandoned—we identify precisely what lambda gives us and assess whether it's loadbearing.

---

## Timeline (Estimate)

- **Phase 1–2:** 1–2 weeks (foundation, translation, parametricity)
- **Phase 3:** 1 week (recursion patterns)
- **Phase 4:** 1 week (effects + handlers)
- **Phase 5:** 2 weeks (language protocol + tooling)
- **Phase 6:** 1 week (analysis + writeup)

**Total:** ~8 weeks for a solid PoC, assuming dedicated effort.
