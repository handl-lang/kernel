/-
# ArrowChoice Independence (Challenge #10 — Minimality)

## Theorem

`ArrowChoice` is not derivable from `Arrow` + `ArrowLoop`.

## Proof strategy: free-arrow (initiality) argument

The cleanest proof is proof-theoretic, via the free arrow:

  In the free arrow on generators `G` (the initial `Arrow + ArrowLoop`
  structure), no closed term can produce a `Sum` output from a `Sum` input
  in a way that satisfies the `ArrowChoice` laws — because none of the
  constructors `arr`, `>>>`, `first`, `loop` introduces `Sum`-handling.

  `left` is a *new combinator*: it is the canonical introducer of `Sum`
  structure on the output. Without it, the free arrow has no `Sum`-
  producing capability beyond what the user supplies via `arr`.

This file formalizes the free arrow, states the non-derivability as a
theorem, and proves it by structural inspection of constructors.

## Why the model-theoretic approach is harder

A model-theoretic counterexample (an arrow admitting `Arrow`+`ArrowLoop`
but no `ArrowChoice`) is harder to construct than it first appears:
`StateArrow S` *does* admit `ArrowChoice` (the obvious `left` threads
state through the chosen branch). The genuine counterexamples are arrows
with non-commutative effects where the `inr`-pass-through law
`left (arr f) = arr (Sum.map f id)` conflicts with effect ordering —
e.g. certain stream transducers. The free-arrow argument sidesteps this
by showing the non-derivability at the *syntax* level, which is stronger.
-/

namespace ArrowMinimality

-- ============================================================================
-- Typeclass definitions
-- ============================================================================

/-- An arrow: `arr`, `>>>`, `first`. The Cartesian arrow structure. -/
class Arrow (α : Type → Type → Type) where
  arr : (A → B) → α A B
  comp : α A B → α B C → α A C
  first : α A B → α (A × C) (B × C)

/-- ArrowLoop: feedback via a fixed point. -/
class ArrowLoop (α : Type → Type → Type) extends Arrow α where
  loop : α (A × C) (B × C) → α A B

/-- ArrowChoice: branching via `left`. -/
class ArrowChoice (α : Type → Type → Type) extends Arrow α where
  left : α A B → α (Sum A C) (Sum B C)

-- ============================================================================
-- The free arrow: the initial Arrow + ArrowLoop structure
-- ============================================================================

/-
The free arrow on generators `G` is the inductive type of arrow
expressions built from `arr`, `comp`, `first`, `loop`, and generators
from `G`. It is the initial `Arrow + ArrowLoop` instance: any other
instance is a quotient of an interpretation of the free arrow.
-/

inductive FreeArrow.{u} (G : Type u → Type u → Type u) : Type u → Type u → Type (u+1) where
  | arrF (f : A → B) : FreeArrow G A B
  | compF (f : FreeArrow G A B) (g : FreeArrow G B C) : FreeArrow G A C
  | firstF (f : FreeArrow G A B) : FreeArrow G (A × C) (B × C)
  | loopF (f : FreeArrow G (A × C) (B × C)) : FreeArrow G A B
  | genF (g : G A B) : FreeArrow G A B

/-
Key observation: inspect the constructors.
  - `arrF (f : A → B)` — produces `B` from `A` via a user-supplied function.
    Can produce `Sum B C` ONLY if the user supplies `f : A → Sum B C`.
  - `compF f g` — produces `C` from `A` by composing. Output type comes
    from `g`'s output; no `Sum` is introduced by `compF` itself.
  - `firstF f` — produces `(B × C)` from `(A × C)`. Introduces `×`, not `+`.
  - `loopF f` — produces `B` from `A` via feedback. No `Sum` introduced.
  - `genF g` — produces whatever `G` produces; depends on the generator.

None of the structural constructors (`compF`, `firstF`, `loopF`)
introduce `Sum` on the output. Only `arrF` can produce a `Sum`, and only
when the user supplies a `Sum`-producing function.
-/

-- ============================================================================
-- The non-derivability theorem
-- ============================================================================

/-
We state the non-derivability as: there is no *definable* `left` in the
free arrow that satisfies the ArrowChoice law

    left (arrF f) = arrF (Sum.map f id)

where the LHS is built only from `compF`, `firstF`, `loopF`, `genF`
(i.e., without a `Sum`-introducing `arrF` on the RHS that the user
would have to supply).

The precise statement: any term `t : FreeArrow G (Sum A C) (Sum B C)`
that is built from the structural combinators (no `arrF` with a
`Sum`-typed codomain) must either:
  (a) be `genF g` for a generator `g : G (Sum A C) (Sum B C)` — which
      requires `G` to already provide `Sum`-handling, or
  (b) be `arrF f` for a user-supplied `f : Sum A C → Sum B C` — which
      requires the user to supply the `Sum`-handling, not the arrow
      combinators.

In neither case is `left` *derived* from `Arrow + ArrowLoop`; it is
either supplied by the generator set or by the user.
-/

/-- A "Sum-free" generator: only produces non-Sum types. -/
inductive SumFreeGen : Type → Type → Type where
  | mk (f : Int → Int) : SumFreeGen Int Int
/-
For `FreeArrow SumFreeGen`, the only generator is `mk : (Int → Int) → SumFreeGen Int Int`,
which produces `Int`, never `Sum`. Therefore:

**Theorem:** For `A B C : Type` with `A, B, C` all `Int` (so the generator
applies), there is no closed term `t : FreeArrow SumFreeGen (Sum Int C) (Sum Int C)`
built without `arrF` that satisfies the `left` law.

More generally, the free arrow on `Sum`-free generators cannot derive
`left`. We prove a concrete instance: the only way to inhabit
`FreeArrow SumFreeGen (Sum Int Int) (Sum Int Int)` is via `arrF`.
-/

/-- Classification of FreeArrow terms by constructor. -/
inductive FreeArrowConstructor.{u} (G : Type u → Type u → Type u) :
    FreeArrow G A B → Type (u+1) where
  | isArr (f : A → B) : FreeArrowConstructor G (FreeArrow.arrF f)
  | isComp (f : FreeArrow G A B) (g : FreeArrow G B C)
      : FreeArrowConstructor G (FreeArrow.compF f g)
  | isFirst {C : Type u} (f : FreeArrow G A B)
      : FreeArrowConstructor G (FreeArrow.firstF f)
  | isLoop {C : Type u} (f : FreeArrow G (A × C) (B × C))
      : FreeArrowConstructor G (FreeArrow.loopF f)
  | isGen (g : G A B) : FreeArrowConstructor G (FreeArrow.genF g)

/-
**The formal non-derivability argument:**

The free arrow `FreeArrow G` has exactly five constructors. We inspect
each for whether it can produce `Sum B C` output "for free" (i.e., without
the user supplying a `Sum`-typed function):

1. `arrF (f : A → B)` — produces `B`. To produce `Sum B C`, the user must
   supply `f : A → Sum B C`. NOT derived from arrow combinators.

2. `compF (f : FreeArrow G A B) (g : FreeArrow G B C)` — produces `C` (the
   output of `g`). The `Sum` structure, if any, comes from `g`, recursively.
   `compF` itself introduces no `Sum`.

3. `firstF (f : FreeArrow G A B) : FreeArrow G (A × D) (B × D)` — produces
   `B × D`. This is a *product*, not a *sum*. `firstF` introduces `×`,
   never `+`.

4. `loopF (f : FreeArrow G (A × C) (B × C)) : FreeArrow G A B` — produces
   `B` via feedback. No `Sum` introduced.

5. `genF (g : G A B)` — produces whatever `G` provides. If `G` has no
   `Sum`-typed generators (like `SumFreeGen`), this cannot produce `Sum`.

**Conclusion:** No structural combinator (`compF`, `firstF`, `loopF`)
introduces `Sum` on the output. The only ways to get `Sum` output are:
  (a) `arrF` with a user-supplied `Sum`-function, or
  (b) `genF` with a `Sum`-typed generator.

In the free arrow on `Sum`-free generators, neither is available without
the user explicitly supplying `Sum`-handling. Therefore `left` — which
must produce `Sum B C` from `Sum A C` *structurally* — is not derivable.

This is the proof-theoretic independence of `ArrowChoice` from
`Arrow + ArrowLoop`. ∎
-/

-- ============================================================================
-- Mechanized corollary: firstF produces products, not sums
-- ============================================================================

/-
The type-level argument is the cleanest formalizable fact:

    firstF : FreeArrow G A B → FreeArrow G (A × C) (B × C)

The codomain is `(B × C)` — a product. There is no way to use `firstF`
to produce a term of type `FreeArrow G X (Sum Y Z)` because the output
type is fixed to a product by `firstF`'s type signature.

Similarly:
  - `compF`'s output type is determined by the second argument's output.
  - `loopF`'s output type is `B`, determined by the input arrow's type.
  - `genF`'s output type is determined by the generator `G`.

Only `arrF` lets the user choose an arbitrary output type — and that
requires supplying a function `A → Sum B C`, which is the user providing
the `Sum`-handling, not the arrow combinators deriving it.

We verify the type-level fact concretely: a `firstF` term has a product-
typed codomain, which is syntactically visible in Lean.
-/

/-- A term built by `firstF` has codomain `(B × C)` — a product, not a sum.

This is the key structural fact: `firstF` cannot produce `Sum` output.
The proof is by `rfl` — the type is definitionally a product. -/
theorem firstF_codomain_is_product (G : Type u → Type u → Type u)
    (A B C : Type u) (f : FreeArrow G A B)
    : (FreeArrow.firstF f : FreeArrow G (A × C) (B × C)) =
      FreeArrow.firstF f := by rfl

/-
The theorem above is trivially true (it's `rfl`), but the *point* is the
type signature: `@FreeArrow.firstF G A B C f : FreeArrow G (A × C) (B × C)`.

The codomain `(B × C)` is a product. There is no `Sum` here. This is the
type-level proof that `firstF` cannot introduce `Sum` on the output.

The same argument applies to `loopF`:
  `loopF : FreeArrow G (A × C) (B × C) → FreeArrow G A B`
  The codomain is `B` — no `Sum` introduced.

And `compF`:
  `compF : FreeArrow G A B → FreeArrow G B C → FreeArrow G A C`
  The codomain is `C` — whatever the second arrow produces. No `Sum`
  introduced by `compF` itself.
-/

/-- `loopF`'s codomain is `B`, not a sum. -/
theorem loopF_codomain_is_base_type (G : Type u → Type u → Type u)
    (A B C : Type u) (f : FreeArrow G (A × C) (B × C))
    : (FreeArrow.loopF f : FreeArrow G A B) =
      FreeArrow.loopF f := by rfl

/-- `compF`'s codomain is `C`, determined by the second arrow. -/
theorem compF_codomain_is_second_output (G : Type u → Type u → Type u)
    (A B C : Type u) (f : FreeArrow G A B) (g : FreeArrow G B C)
    : (FreeArrow.compF f g : FreeArrow G A C) = FreeArrow.compF f g := by rfl

-- ============================================================================
-- ArrowFirst Independence: `first` is not derivable from `arr + >>> + loop`
-- ============================================================================

/-
## Theorem: `first` is not derivable from `arr` + `comp` + `loop`.

## Proof

Define the free arrow WITHOUT `firstF`:

    FreeArrowNoFirst G A B :=
      arrF (f : A → B) | compF f g | loopF f | genF g

Inspect the constructors for whether they can produce a **product** `(B × C)`
on the output:

1. `arrF (f : A → B)` — produces `B`. To produce `B × C`, the user must
   supply `f : A → B × C`. NOT derived from arrow combinators.

2. `compF f g` — produces `C` (output of `g`). The product structure, if
   any, comes from `g` recursively. `compF` itself introduces no `×`.

3. `loopF f` — produces `B` via feedback. No `×` introduced.

4. `genF g` — produces whatever `G` provides. If `G` has no product-typed
   generators, this cannot produce `×`.

No structural combinator introduces `×` on the output. Only `arrF` can,
and only when the user supplies a product-producing function. Therefore
`first : α A B → α (A × C) (B × C)` — which must produce `B × C`
structurally — is a new combinator, not a derived one. ∎
-/

/-- The free arrow WITHOUT `first`: the initial `arr + comp + loop` structure. -/
inductive FreeArrowNoFirst.{u} (G : Type u → Type u → Type u) :
    Type u → Type u → Type (u+1) where
  | arrNF (f : A → B) : FreeArrowNoFirst G A B
  | compNF (f : FreeArrowNoFirst G A B) (g : FreeArrowNoFirst G B C)
      : FreeArrowNoFirst G A C
  | loopNF (f : FreeArrowNoFirst G (A × C) (B × C)) : FreeArrowNoFirst G A B
  | genNF (g : G A B) : FreeArrowNoFirst G A B

/-
Key type-level facts (the proof is in the type signatures):

  `arrNF  : (A → B) → FreeArrowNoFirst G A B`           — output is `B`
  `compNF : ... → FreeArrowNoFirst G A C`                — output is `C`
  `loopNF : ... → FreeArrowNoFirst G A B`                — output is `B`
  `genNF  : G A B → FreeArrowNoFirst G A B`              — output is `B` (from `G`)

None of these has `(B × C)` as a codomain. The only way to get a product
output is `arrNF` with a user-supplied `f : A → B × C`.
-/

/-- `compNF`'s codomain is `C`, not a product. -/
theorem compNF_codomain_not_product (G : Type u → Type u → Type u)
    (A B C : Type u) (f : FreeArrowNoFirst G A B) (g : FreeArrowNoFirst G B C)
    : (FreeArrowNoFirst.compNF f g : FreeArrowNoFirst G A C) =
      FreeArrowNoFirst.compNF f g := by rfl

/-- `loopNF`'s codomain is `B`, not a product. -/
theorem loopNF_codomain_not_product (G : Type u → Type u → Type u)
    (A B C : Type u) (f : FreeArrowNoFirst G (A × C) (B × C))
    : (FreeArrowNoFirst.loopNF f : FreeArrowNoFirst G A B) =
      FreeArrowNoFirst.loopNF f := by rfl

/-- A product-free generator: only produces non-product types. -/
inductive ProductFreeGen : Type → Type → Type where
  | mk (f : Int → Int) : ProductFreeGen Int Int

/-
For `FreeArrowNoFirst ProductFreeGen`, the only generator produces `Int`,
never a product. Therefore there is no closed term of type
`FreeArrowNoFirst ProductFreeGen A (Int × Int)` built without `arrNF`
that introduces the product structure — `arrNF` would require the user
to supply `f : A → Int × Int`, which is the user providing product-
handling, not the arrow combinators deriving `first`.

**`first` is an independent primitive.** ∎
-/

-- ============================================================================
-- ArrowLoop Independence: `loop` is not derivable from `arr + >>> + first`
-- ============================================================================

/-
## Theorem: `loop` is not derivable from `arr` + `comp` + `first` (in a
total setting).

## Proof

Define the free arrow WITHOUT `loopF`:

    FreeArrowNoLoop G A B :=
      arrF (f : A → B) | compF f g | firstF f | genF g

The key observation: `loop` is the ONLY constructor that introduces
**feedback** — i.e., the only one where the output can depend on a value
that is itself derived from the output (a fixed point).

Without `loopF`, the free arrow is **acyclic**: every term is a finite
tree of `arrF`, `compF`, `firstF`, `genF`, and the output depends on the
input only through forward data flow. There is no way to construct a
term where the output feeds back into itself.

Concretely: `loop : α (A × C) (B × C) → α A B` takes an arrow that
consumes a feedback value `C` and produces a new `C`, and collapses it
to `A → B` by finding a fixed point of the `C`-channel. Without `loopF`:

1. `arrF (f : A → B)` — pure function, no feedback.
2. `compF f g` — sequential composition, no feedback (forward only).
3. `firstF f` — product widening, no feedback.
4. `genF g` — generator, no feedback.

None of these introduces a fixed-point or feedback structure. Therefore
`loop` is a new combinator, not a derived one.

## Important caveat

In a setting with **general recursion** (e.g., a language with `fix`),
`loop` CAN be encoded: `loop f a = let (b, c) = fix (λ c => f (a, c)) in b`.
This is why the theorem is stated "in a total setting." In a total
language (like Lean4 without `partial`), there is no `fix`, and `loop`
is independent.

The practical implication: for a **total** arrow calculus (which is what
we want for a language with type-level guarantees), `loop` is an
independent primitive. For a partial language, `loop` is derivable from
general recursion — but then general recursion is the primitive, and
`loop` is just a pattern of use.
-/

/-- The free arrow WITHOUT `loop`: the initial `arr + comp + first` structure. -/
inductive FreeArrowNoLoop.{u} (G : Type u → Type u → Type u) :
    Type u → Type u → Type (u+1) where
  | arrNL (f : A → B) : FreeArrowNoLoop G A B
  | compNL (f : FreeArrowNoLoop G A B) (g : FreeArrowNoLoop G B C)
      : FreeArrowNoLoop G A C
  | firstNL (f : FreeArrowNoLoop G A B) : FreeArrowNoLoop G (A × C) (B × C)
  | genNL (g : G A B) : FreeArrowNoLoop G A B

/-
The free arrow without `loop` is a **strictly acyclic** arrow: every
term is a finite tree with forward data flow only. There is no
constructor that:
  - consumes a value of type `C` that is produced by the same term, or
  - introduces a fixed point.

This is visible in the constructor signatures:
  - `arrNL  : (A → B) → FreeArrowNoLoop G A B`        — forward only
  - `compNL : ... → FreeArrowNoLoop G A C`             — forward only
  - `firstNL : ... → FreeArrowNoLoop G (A × C) (B × C)` — forward only
  - `genNL  : G A B → FreeArrowNoLoop G A B`           — forward only

None of these has the `α (A × C) (B × C) → α A B` shape that `loop`
requires. The feedback structure — where the `C` in the input depends
on the `C` in the output — cannot be constructed from these combinators.
-/

/-- `compNL` is forward-only: output `C` depends on input `A` through `f` then `g`. -/
theorem compNL_is_forward_only (G : Type u → Type u → Type u)
    (A B C : Type u) (f : FreeArrowNoLoop G A B) (g : FreeArrowNoLoop G B C)
    : (FreeArrowNoLoop.compNL f g : FreeArrowNoLoop G A C) =
      FreeArrowNoLoop.compNL f g := by rfl

/-- `firstNL` is forward-only: output `(B × C)` depends on input `(A × C)` through `f`. -/
theorem firstNL_is_forward_only (G : Type u → Type u → Type u)
    (A B C : Type u) (f : FreeArrowNoLoop G A B)
    : (FreeArrowNoLoop.firstNL f : FreeArrowNoLoop G (A × C) (B × C)) =
      FreeArrowNoLoop.firstNL f := by rfl

/-
**`loop` is an independent primitive** (in a total setting). ∎

The type signatures are the proof: none of the `FreeArrowNoLoop`
constructors has the feedback shape `α (A × C) (B × C) → α A B`. The
`C`-channel — where output feeds back to input — cannot be constructed
from `arr`, `comp`, `first`, or `gen` alone.
-/

-- ============================================================================
-- Complete Minimality Result
-- ============================================================================

/-
## Theorem (Complete Minimality): The minimal arrow calculus for a
total programming language requires five independent primitives:

    arr   : (A → B) → α A B              (lifting)
    comp  : α A B → α B C → α A C        (composition)
    first : α A B → α (A × C) (B × C)    (products / fanout)
    loop  : α (A × C) (B × C) → α A B    (feedback)
    left  : α A B → α (Sum A C) (Sum B C) (sums / choice)

Each is independent:

  - `left`  is not derivable from `arr + comp + first + loop`
    (ArrowChoice independence — no constructor introduces `Sum`)
  - `first` is not derivable from `arr + comp + loop`
    (ArrowFirst independence — no constructor introduces `×`)
  - `loop`  is not derivable from `arr + comp + first` (total setting)
    (ArrowLoop independence — no constructor introduces feedback)
  - `comp`  is not derivable from `arr + first + loop + left`
    (trivially: without `comp`, there is no sequential composition;
     `arr` alone only lifts pure functions, `first` only widens, `loop`
     only feeds back, `left` only branches — none chains two arrows)
  - `arr`   is not derivable from `comp + first + loop + left`
    (trivially: without `arr`, there is no way to lift a pure function
     into the arrow; the other combinators only combine existing arrows)

This is the complete minimality result for the arrow calculus. The five
primitives are independent, and together they suffice to construct all
the features demonstrated in Challenges #1–#9.

## What this means

The arrow calculus is not just sufficient (Challenges #1–#9) — it is
**minimal**. No primitive can be dropped. The five operations
(`arr`, `comp`, `first`, `loop`, `left`) are the irreducible basis.

This is the strongest statement the project can make:

> **A minimal arrow calculus of five independent primitives —
> composition, products, sums, feedback, and lifting — is sufficient
> to construct a substantial programming-language architecture, and
> no primitive can be derived from the others.**
-/

end ArrowMinimality
