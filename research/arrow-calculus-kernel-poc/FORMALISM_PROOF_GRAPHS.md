# Arrow Graphs as Proof Objects (Phase 4 — Curry-Howard for Arrow Graphs)

## Overview

This document formalizes the central new claim of the proof-graphs
research program:

> **An arrow graph is simultaneously a program, a typing derivation, and
> a proof. The three readings are not three interpretations of one
> object — they are the same judgment under three notations.**

This is the arrow-graph analogue of the Curry-Howard correspondence.
Where classical Curry-Howard identifies λ-terms with natural-deduction
proofs, arrow-graph Curry-Howard identifies **λ-free graph combinators**
with **sequent-style proofs** over products (∧) and sums (∨), with
`loop` supplying fixpoint/invariant reasoning.

The program builds on the five-primitive minimality result
(Challenge #10, Lean4): `arr`, `comp`, `first`, `left`, `loop`. We reuse
exactly those five as graph constructors and show that they are also
proof constructors.

```
Arrow graph G
    │
    ├── operational semantics  →  execute      (G · a ⟹ v)
    ├── type rules              →  typecheck    (Γ ⊢ G : A ⇝ B)
    └── proof rules             →  reason       (Γ ⊢ G ⊩ A ⊢ B)
```

The correspondence:

| Graph combinator | Program reading | Type reading | Proof reading                       |
| ---------------- | --------------- | ------------ | ----------------------------------- |
| `id_A`           | identity arrow  | `A ⇝ A`      | `A ⊢ A` (identity)                  |
| `comp(f, g)`     | `f >>> g`       | `A ⇝ C`      | cut: `A⊢B, B⊢C ⟹ A⊢C`               |
| `first(f)`       | act on 1st      | `A×C ⇝ B×C`  | ∧-functoriality (context weakening) |
| `left(f)`        | act on Left     | `A+C ⇝ B+C`  | ∨-functoriality (case structure)    |
| `loop(f)`        | feedback        | `A ⇝ B`      | trace / fixpoint invariant          |
| `arr(φ)`         | lift pure φ     | `A ⇝ B`      | axiom (primitive inference step φ)  |

Derived combinators (defined from the five):

| Derived      | From            | Proof reading                      |
| ------------ | --------------- | ---------------------------------- |
| `f &&& g`    | `first` + `arr` | ∧-introduction: `A⊢B, A⊢C ⟹ A⊢B∧C` |
| `f \|\|\| g` | `left` + `arr`  | ∨-elimination: `B⊢A, C⊢A ⟹ B∨C⊢A`  |

---

## 1. The Calculus: Arrow Graphs

### 1.1 Graph syntax

An **arrow graph** is a finite, directed, port-typed graph built from
five combinators and a signature of base arrows. We present it as an
inductive type (the free arrow graph); the graph reading is recovered
by viewing `comp` as edge-sequencing, `first`/`left` as
functorial-boxing, and `loop` as a back-edge (cycle).

```
Types:
  A, B, C ∈ Ty ::= α              -- type variable
                  | A × B          -- product   (read as ∧ in proof mode)
                  | A + B          -- sum       (read as ∨ in proof mode)
                  | ⊤              -- unit      (read as ⊤, truth)
                  | ⊥              -- void      (read as ⊥, falsity)

Graphs (over signature Σ of base arrows φ : A → B):
  G, H ∈ Graph ::= id_A
                  | comp(G, H)     -- sequential composition  (>>>)
                  | first(G)       -- product functoriality
                  | left(G)        -- sum functoriality
                  | loop(G)        -- feedback / trace
                  | arr(φ)         -- base arrow from Σ
```

This is exactly the five-primitive calculus of Challenge #10, restated
as a graph grammar. **No λ-abstraction, no application, no `app`
combinator appears.** The calculus is λ-free by construction.

### 1.2 Derived combinators

```
-- Parallel / fanout: both branches receive the SAME input.
f &&& g  ≜  comp(first(f), comp(arr(swap), first(g)))  -- after arr(dup)
-- more directly, with explicit duplication:
dup      ≜  arr(λa. (a, a))                          -- Σ-primitive
swap     ≜  arr(λ(a, b). (b, a))                     -- Σ-primitive
f &&& g  ≜  comp(dup, comp(first(f), comp(swap, first(g))))
           : A ⇝ B × C   when f : A ⇝ B, g : A ⇝ C

-- Merge / choice: branch on the input sum.
f ||| g  ≜  comp(left(f), left(g))  -- via distributivity; or directly:
           : A + B ⇝ C   when f : A ⇝ C, g : B ⇝ C
```

The derived combinators exist for notational convenience in the proof
correspondence; the five primitives are the canonical constructors.

### 1.3 Operational semantics

Execution judgment: `G · a ⟹ v` (graph `G` run on input value `a`
yields output `v`).

```
────────────────────────── (E-Id)
  id_A · a ⟹ a


  G · a ⟹ b      H · b ⟹ v
────────────────────────────────── (E-Comp)
  comp(G, H) · a ⟹ v


  G · a ⟹ b
────────────────────────────────────────── (E-First)
  first(G) · (a, c) ⟹ (b, c)


  G · a ⟹ b
────────────────────────────────────────────── (E-Left-L)
  left(G) · inl(a) ⟹ inl(b)

  G · b ⟹ c
────────────────────────────────────────────── (E-Left-R)
  left(G) · inr(b) ⟹ inr(c)


  G · (a, c₀) ⟹ (b₁, c₁)
  G · (a, c₁) ⟹ (b₂, c₂)
  ...                          (iterate until cₙ₊₁ = cₙ, the fixpoint)
  G · (a, cₙ) ⟹ (v, cₙ)
────────────────────────────────────────────────────────── (E-Loop)
  loop(G) · a ⟹ v


  φ(a) = v
────────────────────────────── (E-Arr)
  arr(φ) · a ⟹ v
```

`E-Loop` is the **fixpoint rule**: iterate the step arrow on the
feedback channel `c` until it stabilises; the value channel yields the
result. Termination is not guaranteed in general (this is the partial
setting); in the total setting we require a well-founded measure on `c`
that decreases each iteration (see §4.3).

---

## 2. Typing Judgments for Arrow Graphs

### 2.1 Judgment

```
Γ ⊢ G : A ⇝ B
```

Read: "in context `Γ` (a set of type-variable bindings), graph `G` has
arrow type `A ⇝ B`." We write `⇝` for the graph arrow to distinguish it
from the term-calculus `~>` of FORMALISM.md, though the two coincide
under the obvious embedding.

### 2.2 Typing rules

```
────────────────────────────── (T-Id)
  Γ ⊢ id_A : A ⇝ A


  Γ ⊢ G : A ⇝ B      Γ ⊢ H : B ⇝ C
────────────────────────────────────────── (T-Comp)
  Γ ⊢ comp(G, H) : A ⇝ C


  Γ ⊢ G : A ⇝ B
────────────────────────────────────────────────── (T-First)
  Γ ⊢ first(G) : A × C ⇝ B × C


  Γ ⊢ G : A ⇝ B
────────────────────────────────────────────────────── (T-Left)
  Γ ⊢ left(G) : A + C ⇝ B + C


  Γ ⊢ G : A × C ⇝ B × C
────────────────────────────────────────── (T-Loop)
  Γ ⊢ loop(G) : A ⇝ B


  φ : A → B ∈ Σ
────────────────────────────────────── (T-Arr)
  Γ ⊢ arr(φ) : A ⇝ B
```

These are the standard arrow-calculus typing rules (Lindley–Wadler–
Yallop) restated over the graph grammar. **Subject reduction** (typing
is preserved by execution) and **progress** (well-typed graphs either
produce a value or diverge on `loop`) hold by the standard argument;
§4 proves both.

---

## 3. Proof Judgments for Arrow Graphs

### 3.1 The Curry-Howard interpretation

We interpret arrow types as **propositions** in intuitionistic logic:

```
  A ⇝ B   ↦   A ⊢ B          (a proof of B from hypothesis A)
  A × B   ↦   A ∧ B          (conjunction)
  A + B   ↦   A ∨ B          (disjunction)
  ⊤       ↦   ⊤              (truth)
  ⊥       ↦   ⊥              (falsity)
```

A graph `G : A ⇝ B` is read as a **proof of the sequent `A ⊢ B`**. The
graph's structure IS the proof's structure: each combinator is a rule
application, each `arr(φ)` is an axiom, each `loop` is a fixpoint
reasoning step.

### 3.2 Proof judgment

```
Γ ⊢ G ⊩ A ⊢ B
```

Read: "graph `G` is a proof of sequent `A ⊢ B` in context `Γ`."

### 3.3 Proof rules

```
────────────────────────────── (P-Id)
  Γ ⊢ id_A ⊩ A ⊢ A


  Γ ⊢ G ⊩ A ⊢ B      Γ ⊢ H ⊩ B ⊢ C
────────────────────────────────────────── (P-Cut)
  Γ ⊢ comp(G, H) ⊩ A ⊢ C


  Γ ⊢ G ⊩ A ⊢ B
────────────────────────────────────────────────── (P-And-Func)
  Γ ⊢ first(G) ⊩ A ∧ C ⊢ B ∧ C


  Γ ⊢ G ⊩ A ⊢ B
────────────────────────────────────────────────────── (P-Or-Func)
  Γ ⊢ left(G) ⊩ A ∨ C ⊢ B ∨ C


  Γ ⊢ G ⊩ A ∧ C ⊢ B ∧ C
────────────────────────────────────────── (P-Trace)
  Γ ⊢ loop(G) ⊩ A ⊢ B


  φ : A → B ∈ Σ   (φ is a valid inference step)
────────────────────────────────────────────────── (P-Axiom)
  Γ ⊢ arr(φ) ⊩ A ⊢ B
```

### 3.4 Derived proof rules (the user's headline correspondence)

From the primitive rules + the derived combinators of §1.2:

```
  Γ ⊢ f ⊩ A ⊢ B      Γ ⊢ g ⊩ A ⊢ C
────────────────────────────────────────── (P-And-Intro)
  Γ ⊢ f &&& g ⊩ A ⊢ B ∧ C


  Γ ⊢ f ⊩ B ⊢ A      Γ ⊢ g ⊩ C ⊢ A
────────────────────────────────────────── (P-Or-Elim)
  Γ ⊢ f ||| g ⊩ B ∨ C ⊢ A
```

These are exactly the ∧-introduction and ∨-elimination rules of
intuitionistic logic, with the **graph combinator as the proof term**.

### 3.5 The status of `loop`

`loop` is the graph analogue of **trace** in a traced symmetric
monoidal category (Joyal–Street–Verity 1996). In proof terms it is the
**fixpoint / invariant rule**: to prove `A ⊢ B`, exhibit an invariant
`C` and a proof `G : A ∧ C ⊢ B ∧ C` such that the `C`-component is
preserved at the fixpoint (`cₙ₊₁ = cₙ`). This is the proof-theoretic
counterpart of `E-Loop`'s iteration-to-fixpoint.

In the total setting (well-founded measure on `C`), `loop` corresponds
to **induction**: the measure decreases each step, the fixpoint is the
base case, and the proof is the induction step. In the partial setting,
`loop` is **coinduction / general fixpoint reasoning** — sound but not
terminating.

This is the arrow-graph replacement for the role that `fix` / the
induction principle plays in λ-calculus-based dependent type theory:
**fixpoint reasoning is graph feedback, not lambda abstraction**.

---

## 4. The Correspondence Theorem (Typing ⇔ Proof)

### 4.1 Statement

**Theorem (Typing ⇔ Proof).** For every arrow graph `G` and types
`A, B`:

```
  Γ ⊢ G : A ⇝ B    ⟺    Γ ⊢ G ⊩ A ⊢ B
```

The typing judgment and the proof judgment are interderivable. Moreover
the derivations have identical structure: rule-for-rule, premise-for-
premise.

### 4.2 Proof

By mutual induction on the structure of `G`. Each direction is the
identity on derivation shape.

**(⇒) Typing ⟹ Proof.** Induct on the typing derivation `D : Γ ⊢ G : A ⇝ B`.

- `T-Id` ⟹ `P-Id`. The derivation `Γ ⊢ id_A : A ⇝ A` maps to
  `Γ ⊢ id_A ⊩ A ⊢ A`. Same conclusion under the interpretation
  `⇝ ↦ ⊢`.
- `T-Comp` ⟹ `P-Cut`. From `D₁ : Γ ⊢ G : A ⇝ B` and
  `D₂ : Γ ⊢ H : B ⇝ C`, the IH gives `Γ ⊢ G ⊩ A ⊢ B` and
  `Γ ⊢ H ⊩ B ⊢ C`; apply `P-Cut`.
- `T-First` ⟹ `P-And-Func`. IH gives `Γ ⊢ G ⊩ A ⊢ B`; apply
  `P-And-Func` with `C` from the typing rule.
- `T-Left` ⟹ `P-Or-Func`. Symmetric to the above.
- `T-Loop` ⟹ `P-Trace`. IH gives `Γ ⊢ G ⊩ A ∧ C ⊢ B ∧ C`; apply
  `P-Trace`.
- `T-Arr` ⟹ `P-Axiom`. The signature membership `φ : A → B ∈ Σ` is
  the same side condition; apply `P-Axiom`.

**(⇐) Proof ⟹ Typing.** Induct on the proof derivation; each rule
maps back to its typing counterpart by the inverse of the above table.

The derivations are **structurally identical**: the only difference
between a typing derivation and a proof derivation is the reading of
`⇝` (as a type arrow) versus `⊢` (as a sequent turnstile) and `×/+`
(as type constructors) versus `∧/∨` (as logical connectives). ∎

### 4.3 Corollary: the graph is one object with three readings

The theorem says more than "types and proofs agree." It says they are
**the same derivation** under two notational conventions. Combined with
the operational semantics of §1.3, we have:

```
  one graph G
     │
     ├─ as program:   G · a ⟹ v          (execute)
     ├─ as type:      Γ ⊢ G : A ⇝ B      (typecheck)
     └─ as proof:     Γ ⊢ G ⊩ A ⊢ B      (reason)
```

The graph is not _interpreted as_ a program, a type derivation, and a
proof; it **is** all three. This is the precise content of the slogan
"the arrow graph is both the program and the proof object."

---

## 5. Soundness Against Execution Semantics

We now connect the type/proof reading to the operational reading: a
well-typed (equivalently, well-proved) graph, when executed, produces a
value of the promised type (equivalently, a proof of the promised
proposition).

### 5.1 Type soundness (preservation + progress)

**Theorem (Subject Reduction).** If `⊢ G : A ⇝ B` and `G · a ⟹ v`
with `a : A`, then `v : B`.

_Proof._ By induction on the execution derivation `E : G · a ⟹ v`,
inverting the typing derivation `D : ⊢ G : A ⇝ B` at each step.

- `E-Id`: `D` is `T-Id`, `a : A`, `v = a`, so `v : A = B`. ✓
- `E-Comp`: `D` is `T-Comp` with premises `⊢ G : A ⇝ B'` and
  `⊢ H : B' ⇝ B`. `E` gives `G · a ⟹ b` and `H · b ⟹ v`. By IH on
  the first, `b : B'`; by IH on the second with `b : B'`, `v : B`. ✓
- `E-First`: `D` is `T-First` with `⊢ G : A' ⇝ B'` and the product
  type `A' × C ⇝ B' × C`. `E` gives `G · a ⟹ b` with `a : A'`, so
  `b : B'` by IH; the result `(b, c) : B' × C`. ✓
- `E-Left-L`/`E-Left-R`: symmetric, using `T-Left`. ✓
- `E-Loop`: `D` is `T-Loop` with `⊢ G : A × C ⇝ B × C`. Each
  iteration step `G · (a, cᵢ) ⟹ (bᵢ₊₁, cᵢ₊₁)` preserves `cᵢ₊₁ : C`
  by IH on the product typing; at the fixpoint `cₙ₊₁ = cₙ`, the value
  `v = bₙ₊₁ : B`. ✓
- `E-Arr`: `D` is `T-Arr` with `φ : A → B`; `φ(a) = v` and `a : A`
  gives `v : B` by the type of `φ`. ✓

**Theorem (Progress).** If `⊢ G : A ⇝ B` and `a : A`, then either
`G · a ⟹ v` for some `v : B`, or `G` diverges on `a` (only possible
via `loop` whose feedback channel does not reach a fixpoint).

_Proof._ By induction on `G`. All cases except `loop` are deterministic
and terminate (the sub-graphs are smaller). For `loop`, either the
feedback channel stabilises (yields `v`) or it does not (divergence);
no stuck state is reachable because each step is itself a smaller
well-typed graph. ∎

### 5.2 Proof soundness (realizability)

**Theorem (Proof Realizability).** If `⊢ G ⊩ A ⊢ B` and `a` is a
proof (realizer) of `A`, then `G · a ⟹ v` where `v` is a proof of
`B`.

_Proof._ By the Correspondence Theorem (§4), `⊢ G ⊩ A ⊢ B` iff
`⊢ G : A ⇝ B`. By Subject Reduction, `G · a ⟹ v` with `v : B`. Under
the Curry-Howard interpretation, `v : B` _is_ "`v` is a proof of `B`."
The two soundness theorems are the same theorem. ∎

### 5.3 Combined soundness statement

```
  ⊢ G : A ⇝ B   ⟺   ⊢ G ⊩ A ⊢ B
        │                  │
        ▼                  ▼
   G · a ⟹ v        v is a proof of B
   (a : A)           (a is a proof of A)
```

The single graph `G` is simultaneously:

- a total function from values of type `A` to values of type `B`
  (program reading),
- a derivation of `A ⇝ B` (type reading),
- a derivation of `A ⊢ B` (proof reading),

and the three are consistent: running the program on a proof of `A`
yields a proof of `B`.

---

## 6. Dependent Typing for Arrow Graphs

We now extend the type system so that **output types may depend on
input values**. This is the dependent-arrow-graph calculus, and the
locus of the novel hypothesis:

> **A λ-free arrow graph yields dependent types directly, via value
> propagation through the graph and fixpoint reasoning via `loop`.**

### 6.1 Dependent arrow types

A dependent arrow type is written:

```
  (a : A) ⇝ B(a)
```

where `B` is a **type family** indexed by values of type `A`. The
output type is not a fixed `B` but the type `B(a)` obtained by
evaluating `B` at the actual input value `a`.

Dependent typing judgment:

```
  Γ ⊢ G : (a : A) ⇝ B(a)
```

Read: "for all `a : A`, executing `G` on `a` yields a value of type
`B(a)`."

### 6.2 Dependent typing rules

```
────────────────────────────────────────────── (D-Id)
  Γ ⊢ id_A : (a : A) ⇝ A


  Γ ⊢ G : (a : A) ⇝ B(a)
  Γ ⊢ H : (b : B(a)) ⇝ C(a, b)
────────────────────────────────────────────────────────────────── (D-Comp)
  Γ ⊢ comp(G, H) : (a : A) ⇝ C(a, [G·a])    -- [G·a] = the value G produces


  Γ ⊢ G : (a : A) ⇝ B(a)
────────────────────────────────────────────────────────────────────────── (D-First)
  Γ ⊢ first(G) : ((a, c) : A × C) ⇝ (B(a), c)


  Γ ⊢ G : (a : A) ⇝ B(a)
────────────────────────────────────────────────────────────────────────────────── (D-Left)
  Γ ⊢ left(G) : (s : A + C) ⇝ case s of inl(a) ⇒ inl(B(a)) | inr(c) ⇒ inr(c)


  Γ ⊢ G : ((a, c) : A × C) ⇝ (B(a, c), C'(a, c))
  invariant:  C'(a, c) = c   at the fixpoint c*
────────────────────────────────────────────────────────────────────────── (D-Loop)
  Γ ⊢ loop(G) : (a : A) ⇝ B(a, c*)


  φ : (a : A) → B(a) ∈ Σ   (φ is a dependent base arrow)
────────────────────────────────────────────────────────────────────────── (D-Arr)
  Γ ⊢ arr(φ) : (a : A) ⇝ φ(a) : B(a)
```

### 6.3 The λ-free mechanism

The crucial observation: **dependent typing emerges from value
propagation, not from lambda abstraction.** The checker establishes a
dependent type by:

1. **Traversing the graph** from input port to output port.
2. **Propagating values** (symbolic values, not just types) through
   each node. For `comp(G, H)`, the value flowing into `H` is the
   actual output of `G`, so `H`'s output type is `C(a, G·a)` — the
   type family `C` evaluated at the _realised_ intermediate value.
3. **Computing type families** by applying the signature's dependent
   base arrows `φ : (a : A) → B(a)`. Each `arr(φ)` refines the output
   type as a function of the input.
4. **Establishing fixpoints** for `loop`: the invariant `C'(a, c) = c`
   is the condition that the feedback channel stabilises; the output
   type `B(a, c*)` is the type family evaluated at the fixpoint value
   `c*`.

No λ-abstraction is introduced at any step. The dependencies are
tracked by the **graph wiring** (which output port feeds which input
port), not by a binding construct. This is the precise sense in which
the dependent-arrow-graph calculus is λ-free.

### 6.4 Why this is not just "dependent types in a trench coat"

One might object: "you have dependent base arrows `φ : (a : A) → B(a)`
in the signature `Σ`; isn't that just hiding lambda in the signature?"
No, for three reasons:

1. **The signature is a parameter, not a constructor.** `Σ` is the
   collection of primitive operations the language exposes (e.g.
   `cons : (x : A, xs : [A]) → [A]`, `le : (x : A, y : A) → Bool`).
   These are the same primitives any language has. The calculus does
   not introduce a binding construct to _combine_ them; combination is
   graph composition.

2. **Dependent combination is structural.** The dependent type of
   `comp(G, H)` is `C(a, G·a)` — the type family `C` evaluated at the
   _output of `G`_. This dependency is created by the **wire** from
   `G`'s output to `H`'s input, not by a λ-binder. Cut the wire and
   the dependency vanishes; the dependency _is_ the wire.

3. **Fixpoint reasoning is feedback, not recursion.** In λ-calculus
   dependent type theory, induction is a scheme involving a motive
   (a type family) and a λ-term for the step. Here, the motive is the
   feedback type `C`, the step is the graph `G`, and the induction is
   the iteration of `loop` to its fixpoint. The graph _is_ the
   induction proof.

### 6.5 Dependent proof rules

By the Curry-Howard reading of the dependent types (propositions-as-
types, now with dependency), the dependent typing rules are also
dependent proof rules:

```
  Γ ⊢ G ⊩ (a : A) ⊢ B(a)        -- G proves ∀a:A. B(a)
```

- `D-Comp` is **dependent cut**: from `A ⊢ B(a)` and
  `B(a) ⊢ C(a, b)` derive `A ⊢ C(a, G·a)`.
- `D-Loop` is **dependent induction / fixpoint**: from
  `A ∧ C ⊢ B ∧ C'` with invariant `C' = C` at the fixpoint, derive
  `A ⊢ B(a, c*)`.
- `D-Arr` is a **dependent axiom**: `φ` is a primitive inference
  schema `∀a:A. B(a)`.

The Correspondence Theorem (§4) lifts verbatim: dependent typing ⟺
dependent proof, by the same rule-for-rule argument.

---

## 7. Annotation-Free Inference: The Falsifiable Prediction

### 7.1 The hypothesis

The novel empirical claim:

> **Useful properties of arrow graphs (sortedness, length preservation,
> element-wise satisfaction, loop invariants) can be inferred by the
> checker from the graph structure alone, without user-supplied type
> annotations or proof terms.**

The mechanism is **structural reasoning**: the checker traverses the
graph, propagates types and facts (predicates on values) through each
node, and generates proof obligations at the boundaries. The graph's
wiring determines which facts propagate where; the signature's
dependent base arrows determine how predicates transform.

### 7.2 The inference algorithm

```
infer(G, input_predicate P):
  match G:
    id_A        → P                                    -- identity preserves facts
    arr(φ)      → post(φ, P)                           -- signature's postcondition for φ under P
    comp(G, H)  → infer(H, infer(G, P))                -- propagate through the wire
    first(G)    → (infer(G, P), _)                     -- fact on first component
    left(G)     → case split: inl ⇒ infer(G, P) | inr ⇒ _   -- fact on chosen branch
    loop(G)     → fixpoint of infer(G, (P, Q)) on Q    -- find invariant Q
```

`post(φ, P)` is the **weakest postcondition** of base arrow `φ` given
precondition `P`, supplied by the signature (e.g. `post(cons, _·sorted)
= sorted` because `cons` of a sorted tail with a head ≤ all elements
is sorted — but only if the head satisfies the bound; the obligation is
generated).

### 7.3 Test predicates (the empirical part)

For each of the following graphs, the checker should infer the listed
output predicate **without being told it**:

| Graph               | Input predicate | Expected inferred output predicate                           |
| ------------------- | --------------- | ------------------------------------------------------------ |
| `sort = loop(step)` | `is_list`       | `sorted` (via the loop invariant)                            |
| `map(f) = ...`      | `is_list`       | `is_list ∧ length_preserved`                                 |
| `filter(p) = ...`   | `is_list`       | `is_list ∧ all_satisfy(p)`                                   |
| `f &&& g`           | `P`             | `P ∧ Q` where `Q = infer(g, P)` (conjunction intro)          |
| `f \|\|\| g`        | `P ∨ R`         | `S` where `infer(f, P) = infer(g, R) = S` (disjunction elim) |
| `loop(sort_step)`   | `is_list`       | `sorted ∧ is_permutation` (invariant + permutation)          |

The falsifiable prediction: **at least the first three** (sort, map,
filter) are inferred without annotations. If the checker cannot infer
them, the hypothesis is weakened to "structural reasoning helps but
requires annotation hints for non-trivial invariants."

### 7.4 What "without annotations" means

- The user supplies the **graph** (the program).
- The user supplies the **signature** `Σ` of base arrows with their
  dependent types / pre-post conditions (this is the language
  definition, not a per-program annotation).
- The user does **not** supply:
  - the output type of any sub-graph,
  - the loop invariant,
  - any proof term,
  - any refinement-type annotation.

The checker infers all of these by traversal and propagation. This is
the strict reading of "without annotations"; §RESULTS relaxes it where
the inference requires a hint (e.g. the loop invariant is guessed by
fixpoint iteration and checked, not supplied).

---

## 8. Relation to Prior Work

- **Curry–Howard (1934–1958):** λ-terms ↔ natural-deduction proofs.
  This work is the arrow-graph analogue: graph combinators ↔
  sequent-style proofs. The λ-free aspect is the differentiator.
- **Lambek (1972) / categorical proof theory:** free cartesian closed
  category ≅ STLC ≅ intuitionistic logic. We extend to free
  **traced** bicartesian category (adding `loop` = trace) as the proof
  system, with fixpoint reasoning via the trace.
- **Joyal–Street–Verity (1996):** traced monoidal categories and the
  Int-construction. `loop` is the trace; the proof reading of trace is
  fixpoint/invariant reasoning.
- **Lindley–Wadler–Yallop (2008):** the arrow calculus. Our five
  primitives are theirs; we add the proof reading and the dependent
  extension.
- **Hughes (2000):** arrows generalise monads. The structural
  advantage (Challenge #9, #13) is what makes the graph a traversable
  proof object — an opaque monad cannot be a proof object because its
  structure is hidden.
- **Dependent type theory (Martin-Löf, CoC, etc.):** dependent types
  are built on λ-abstraction (Π-types are dependent functions). Our
  claim is that the _combination_ of dependent base arrows + graph
  composition + loop fixpoints recovers the expressiveness of
  dependent types without a λ-binder. This is the hypothesis to test,
  not a settled result.

---

## 9. Open Questions / Falsification Targets

1. **Is `loop`'s fixpoint inference decidable?** For non-trivial
   invariants (e.g. sortedness), guessing the invariant by fixpoint
   iteration may not terminate. The empirical test (§7) determines
   which invariants are inferable.

2. **Does the dependent extension retain subject reduction?** The
   `D-Comp` rule substitutes `G·a` (a value) into the type family
   `C(a, ·)`. This requires the type family to be defined at the
   _symbolic_ output of `G`, not just the realised value — i.e. the
   checker must compute a symbolic normal form of `G·a`. This is
   decidable for the graph fragment without `loop` (it is composition
   of base arrows); with `loop` it requires the fixpoint to be
   expressible, which is the hard case.

3. **Can the correspondence be made into a categorical equivalence?**
   The free traced bicartesian category should be equivalent to the
   free λ-free dependent proof system sketched here. This is the
   natural next formalisation target (beyond this PoC).

4. **Where does annotation-free inference break?** The honest
   expectation is that simple invariants (length, sortedness of
   comparison-sort, element-satisfaction of filter) are inferable,
   while complex ones (full correctness of arbitrary algorithms,
   termination of non-obvious loops) are not. The boundary is the
   research finding.

---

## Summary

This formalization defines:

1. **The calculus** (§1): arrow graphs over five primitives, with
   operational semantics.
2. **Typing judgments** (§2): `Γ ⊢ G : A ⇝ B`.
3. **Proof judgments** (§3): `Γ ⊢ G ⊩ A ⊢ B`, with the Curry-Howard
   reading `⇝ ↦ ⊢`, `× ↦ ∧`, `+ ↦ ∨`.
4. **The correspondence theorem** (§4): typing ⟺ proof, rule-for-rule.
5. **Soundness** (§5): subject reduction + progress + proof
   realizability, all from the one graph.
6. **Dependent typing** (§6): `(a : A) ⇝ B(a)`, λ-free via value
   propagation and `loop` fixpoints.
7. **The falsifiable prediction** (§7): annotation-free inference of
   sortedness, length, element-satisfaction, and loop invariants from
   graph structure alone.

The Lean4 mechanization (`lean/ArrowMinimalityLib/ProofGraphs.lean`)
proves the Correspondence Theorem and Subject Reduction. The Rust
prototype (`src/proof_graph_tests.rs`) tests the annotation-free
inference prediction on sort, map, filter, and loop graphs.
