# Arrow Calculus PoC: Research Hypothesis

## The Question

**Is lambda calculus necessary as a foundational primitive in a general-purpose programming language, or can we invert the traditional foundation to make Arrow Calculus primitive and recover function-like abstractions as derived concepts?**

This is not a claim that "arrows are better than functions." Rather:

> **Can we build a language where `A ~> B` (arrows) are the primitive computational objects, and where the usual roles of lambda abstraction and function application are expressed as pure/parametric arrows?**

If yes, then lambda calculus becomes an _implementation technique_ rather than a _conceptual foundation_. The language's semantics, type system, and metaprogramming all ground in arrows, not in function application.

---

## Foundation Inversion

Traditional language foundation:

```
values
  ↓
functions (λ-abstraction, application)
  ↓
effects (monads, exceptions, state)
  ↓
programs
```

Proposed arrow-native foundation:

```
values
  ↓
arrows (composition, feedback, choice, application)
  ↓
effects (handlers, operations)
  ↓
programs
  ↓
languages (first-class, manipulable)
  ↓
generic tooling
```

The key insight: if the Arrow Calculus already provides composition (`>>>`), structure (`first`, `choice`), feedback (`loop`), higher-order capabilities (`app`), and a handler-based effects system (Sanada), **what unique capability does lambda calculus provide that cannot be recovered from arrows?**

---

## Concrete Research Challenges

The hypothesis succeeds if we can address all eight of these challenges:

### 1. Expressiveness

**Claim:** The Arrow-first calculus can express everything we need.

**What to investigate:**

- Can all programs in a lambda-calculus language be systematically translated to the Arrow Calculus?
- Are there algorithms, data structure manipulations, or control flows that arrows cannot represent?
- Can recursive definitions, iteration, state management all be expressed via arrows + feedback (`loop`)?

**Success criterion:** Document a translation scheme (even if not fully formalized) showing that λ-terms map to arrow terms without loss of expressiveness.

### 2. Abstraction

**Claim:** Lambda abstraction/application can be replaced by arrow constructions.

**What to investigate:**

- How do we express parametricity without `λ`?
- Can `first`, `arr`, and `>>>` compose to yield function-like abstractions?
- What does "abstracting over a parameter" mean in arrow calculus?

**Success criterion:** Define a construct (e.g., a parametric arrow combinator) that plays the role of `λx. e`. Show that it can be applied dynamically (like function application) and statically (like lambda lifting).

### 3. Parametricity

**Claim:** We can recover generic abstractions without primitive `λ`.

**What to investigate:**

- Can type variables and polymorphic types be integrated into the arrow type system?
- Does the Arrow Calculus's type discipline (as formalized by Lindley–Wadler–Yallop) extend cleanly to generics?
- Can we express things like `forall a. a -> a` and `forall a b. (a -> b) -> [a] -> [b]` naturally?

**Success criterion:** Show that parametric arrows have parametricity properties (identity, abstraction, instantiation) equivalent to lambda-calculus generics.

### 4. Typing

**Claim:** A comparably powerful type system emerges.

**What to investigate:**

- Can we build a Hindley–Milner–style type inference system over arrows?
- Do we get the same principal types as lambda-calculus languages?
- How do arrow-specific types (`A ~> B`, recursive types via feedback) interact with polymorphism?
- Can we express dependent types or refine types?

**Success criterion:** Formalize a type system (even minimally); show that ordinary lambda-typed programs have arrow-calculus counterparts with equivalent types.

### 5. Recursion

**Claim:** `loop` (feedback) can replace the role of recursive functions.

**What to investigate:**

- Does `loop` + `choice` express tail recursion, mutual recursion, and tree recursion?
- Can we derive `fix` / Y-combinator from the arrow primitives?
- How do we encode fixpoint-based definitions naturally?
- What is the relationship between feedback and recursion semantically?

**Success criterion:** Show that recursive patterns (factorial, Fibonacci, list fold, tree walk) can be expressed via arrows + feedback without introducing a separate `rec` or `fix` construct.

### 6. Effects

**Claim:** Sanada-style operations/handlers provide a cleaner foundation than monads.

**What to investigate:**

- Can we express monadic effects (IO, state, exceptions) via arrow operations + handlers?
- Do handlers compose and commute as cleanly as monad transformers?
- Can we recover error handling, state threading, and asynchrony?
- Does the handler-based model give us better control over effect order?

**Success criterion:** Implement a small effect system (e.g., IO + State + Exceptions) via arrow operations and handlers; show that it supports the same patterns as monad transformers.

### 7. Metaprogramming

**Claim:** First-class `Language` makes the system more expressive and uniform.

**What to investigate:**

- Can language operations (lex, parse, eval, format, lint, typecheck) be uniformly expressed as arrows?
- Does first-class `Language` enable uniform generic tooling over any language?
- Can we express homoiconicity (code as data) and macros/compile-time computation naturally?
- Does this simplify or complicate the foundation?

**Success criterion:** Demonstrate at least one language operation (parse, eval, or typecheck) as an arrow handler; show that it can be instantiated over different languages via the first-class protocol.

### 8. Tooling

**Claim:** Generic tooling can operate uniformly over any language satisfying the protocol.

**What to investigate:**

- Can we define a `Language` protocol that all languages implement?
- Does this protocol enable debuggers, profilers, and formatters to work uniformly across languages?
- Can we build a single type-checker/linter/optimizer that works for all languages?
- What would an IDE built on this abstraction look like?

**Success criterion:** Build a simple language-agnostic tool (e.g., a generic pretty-printer or evaluator) that works over multiple language instances without language-specific code.

---

## Methodology: Testing via Falsification

The approach is to **actively try to break the hypothesis** by searching for:

1. **Irreducible gap:** Something lambda calculus _fundamentally_ provides that arrows cannot.
   - If found, characterize it precisely and assess whether it's necessary for the thesis to hold.

2. **Awkwardness:** A feature that _technically_ can be expressed as arrows but is so unnatural that it undermines the foundation.
   - If found, investigate whether a new primitive (not lambda, but something arrow-compatible) would be cleaner.

3. **Expressiveness loss:** A class of programs that can be written in a lambda-based language but not in the arrow-native one.
   - If found, determine whether it's fundamental or a gap in our design.

4. **Type system incompleteness:** A typing scenario (polymorphism, dependent types, subtyping) that doesn't work well with arrow types.
   - If found, investigate whether arrow-specific typing rules can recover it.

5. **Performance cliff:** An arrow encoding that has dramatically worse complexity than lambda-based equivalents.
   - If found, assess whether it's a fundamental limitation or an implementation issue.

The goal is _not_ to produce a proof (too formal for this stage) but to:

- Document what works smoothly
- Identify friction points
- Propose resolution for each friction
- Converge on a falsifiable claim

---

## Evidence for Success

If we can demonstrate:

- ✓ A core calculus (arrows + handlers + first-class Language)
- ✓ A type system that infers types for arrow programs
- ✓ That lambda patterns (map, fold, currying, composition) emerge naturally from arrow primitives
- ✓ That recursive and iterative algorithms lower cleanly to arrows + feedback
- ✓ That effects (IO, state, exceptions) are expressible via handlers
- ✓ That generic tooling operates uniformly over different language instances
- ✓ That we cannot find an irreducible feature that lambda calculus has and arrows lack

Then the thesis becomes:

> **A programming-language foundation in which computation is arrow-native and lambda calculus is not primitive, combined with first-class languages and generic language tooling, is semantically complete and practically viable.**

This is far more interesting than "arrows instead of functions."

---

## Current Status

This PoC is designed to investigate challenges **1–6** in depth (expressiveness, abstraction, parametricity, typing, recursion, effects) and to sketch **7–8** (metaprogramming, tooling).

### Next Steps

1. **Formalize a small arrow calculus** with inference rules (based on Lindley–Wadler–Yallop, Sanada).
2. **Implement a prototype** that interprets arrow terms.
3. **Translate lambda-calculus examples** to arrows; document the translation.
4. **Test against challenge #5** (recursion via feedback).
5. **Sketch the handler model** for effects.
6. **Identify friction points** and propose mitigations.

---

## References

- Hughes: _Generalising Monads to Arrows_ (2000)
- Paterson: _A New Notation for Arrows_ (2001)
- Paterson: _Arrows and Computation_ (2003)
- Hughes: _Programming with Arrows_ (2004)
- Lindley, Wadler, Yallop: _The Arrow Calculus_ (2008/2010)
- Jacobs, Heunen, Hasuo: _Categorical Semantics for Arrows_ (2009)
- Sanada: _Algebraic Effects and Handlers for Arrows_ (2024)
- Cimini: _A Calculus for Multi-language Operational Semantics_ (2018/2022)
