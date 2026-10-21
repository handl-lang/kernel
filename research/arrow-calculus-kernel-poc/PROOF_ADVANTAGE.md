# A Non-Definitional Proof-Theoretic Advantage of Arrow Graphs

This document accompanies `lean/ArrowMinimalityLib/ProofAdvantage.lean`, which
mechanizes a result that is **genuinely non-definitional**: cut elimination for
arrow graphs is a system of _local graph rewrites_, and those rewrites preserve
both proofs and typings — without ever invoking a substitution lemma, an
α-equivalence algorithm, or a binder.

---

## 1. The problem: the existing correspondence is "too easy"

`ProofGraphs.lean` establishes the Curry–Howard correspondence for arrow graphs:

```
    TyOf G  ⟺  PrOf G
```

The two inductive predicates `TyOf` and `PrOf` are _notation-for-notation
identical_: same indices, same constructors, same side conditions. The
bijection between them is proved by a rule-for-rule induction that is, frankly,
a restatement of the definitions. A skeptic can reasonably object:

> "The correspondence holds because you _defined_ two copies of the same
> thing. It is a theorem about your definitions, not a theorem _about_ arrow
> graphs."

That objection is correct as far as it goes. The `TyOf ↔ PrOf` bijection is
essentially **definitional** in flavor. To demonstrate a real proof-theoretic
advantage of arrow graphs over λ-calculus, we need a result that does _not_
follow from "we defined two identical things."

---

## 2. The result: cut elimination is local graph simplification

### 2.1 What cut elimination looks like in natural deduction

In natural deduction, a **cut** is the rule

```
    Γ ⊢ A      A, Δ ⊢ B
    ──────────────────── cut
          Γ, Δ ⊢ B
```

Eliminating the cut means **substituting** the proof of `A` into the proof of
`B` (replacing every assumption of `A` in the second derivation with the first
derivation). This substitution:

1. **requires a binder** (λ) — the assumption `A` is a bound variable;
2. **requires α-equivalence / capture-avoiding substitution** to be
   well-defined, because the two derivations may share variable names;
3. **can duplicate** the proof of `A` — if `A` is used `n` times in the proof
   of `B`, the cut-elimination step copies the first derivation `n` times,
   potentially blowing up the derivation exponentially.

The metatheory of cut elimination for λ-calculus / natural deduction is
therefore non-trivial. It hinges on a **substitution lemma** (a separate
theorem proving that substitution preserves typing), an **α-equivalence
algorithm** (to make substitution capture-avoiding), and a separate
**termination measure** (to show the rewriting process terminates). None of
these are free; they are substantial machinery that the calculus pays for
having a binder.

### 2.2 What cut elimination looks like for arrow graphs

Arrow graphs have **no binder**. The `Graph` inductive has six constructors
(`idG`, `comp`, `first`, `left`, `loop`, `arr`) and none of them binds a
variable. Cut is just `Graph.comp` (sequential composition), and cut
elimination is a finite set of **local rewrites on the graph skeleton** —
rewrites that mention only graph constructors, never a term, a variable, or a
substitution:

```
  idG A ⋙ G              ⟹  G                  (left identity)
  G ⋙ idG B              ⟹  G                  (right identity)
  first G D ⋙ first H D  ⟹  first (G ⋙ H) D    (product functor fusion)
  left  G D ⋙ left  H D  ⟹  left  (G ⋙ H) D    (sum functor fusion)
```

Each rewrite is a **single structural step**. There is:

- **no substitution** — nothing to substitute, because there is no binder;
- **no α-conversion** — there are no variable names to clash;
- **no duplication** — the rewrites rearrange constructors; they never copy a
  sub-graph.

The graph _is_ the proof, and simplifying the graph _is_ simplifying the proof.

### 2.3 The mechanized theorems

`ProofAdvantage.lean` defines the rewrite relation `CutElim G G'` (one step)
and its reflexive-transitive closure `CutElimStar G G'` (zero or more steps),
then proves:

| Theorem                         | Statement                             |
| ------------------------------- | ------------------------------------- |
| `cut_elim_preserves_proof`      | `CutElim G G' → PrOf G → PrOf G'`     |
| `cut_elim_preserves_type`       | `CutElim G G' → TyOf G → TyOf G'`     |
| `cut_elim_star_preserves_proof` | `CutElimStar G G' → PrOf G → PrOf G'` |
| `cut_elim_star_preserves_type`  | `CutElimStar G G' → TyOf G → TyOf G'` |

**The proof of `cut_elim_preserves_proof` is by case analysis on the _rewrite_
`h : CutElim G G'`, not on the derivation.** For each rewrite, one inverts the
`compP` (cut) derivation at the redex, recovers the sub-proofs, and recombines
them under the constructor the rewrite produces. Concretely:

- **Identity rules** (`ceIdLeft`, `ceIdRight`): a cut `idG ⋙ G` (resp.
  `G ⋙ idG`) is a `compP` whose first (resp. second) sub-derivation is an
  identity proof `idP`. Discard the identity half; keep the body. One
  inversion, no rebuilding.

- **Fusion rules** (`ceFirstFusion`, `ceLeftFusion`): a cut
  `first G D ⋙ first H D` is a `compP` of two `firstP` derivations. Strip both
  `firstP`s to recover the body proofs `pG : PrOf G` and `pH : PrOf H`, then
  recombine them as `compP G H pG pH` under a single `firstP`. The shared
  side-channel type `D` is carried through explicitly.

**No substitution lemma is invoked — there is nothing to substitute.** The
proof never mentions a variable, a binder, or a renaming. This is the
mechanized content of "cut elimination for arrow graphs is local and
binder-free."

`cut_elim_preserves_type` is **derived** from the proof case via the
Curry–Howard correspondence: transport the typing derivation `TyOf G` to a
proof derivation `PrOf G` (using `TyOf.toPrOf`), apply
`cut_elim_preserves_proof`, and transport back (using `PrOf.toTyOf`). This is a
genuine **use** of the `TyOf ↔ PrOf` bijection — it reduces a
typing-preservation problem to a proof-preservation problem — rather than a
restatement of it.

---

## 3. Why this is non-definitional

The result does **not** follow from `TyOf G ↔ PrOf G`. That bijection says the
two judgments agree _on a fixed graph_ `G`; it says nothing about what happens
when the graph **changes**. Cut-elimination preservation is a statement
relating **two different graphs** (`G` and `G'`), and its proof inspects the
actual rewrite `h : CutElim G G'` that connects them:

```
    CutElim G G'  →  PrOf G  →  PrOf G'
         ↑              ↑         ↑
     the rewrite    old graph   new graph
     (inspected)    (changes)   (changes)
```

No re-statement of the `TyOf ↔ PrOf` bijection discharges this. One must do
the case analysis on `CutElim`. The bijection is used only as a _transport_
(typing ↔ proof), not as the substance of the theorem.

Contrast with λ-calculus: the analogous theorem — subject reduction under
β-reduction, `Γ ⊢ M : A → Γ ⊢ M[x:=N] : A` — **requires** the substitution
lemma as a prerequisite, because a β-step _is_ a substitution. You cannot
prove "β-reduction preserves typing" without first proving "substitution
preserves typing." Arrow graphs have no such prerequisite, because a
`CutElim` step is not a substitution — it is a local graph rewrite.

---

## 4. A second non-definitional advantage: decidable equality without α

There is a second, equally non-definitional advantage that is worth stating
explicitly, because it is baked into the _syntax_ rather than the _theorems_.

### 4.1 λ-terms: equality is a quotient

Two λ-terms are equal **up to α-equivalence**. The terms `λx. x` and `λy. y`
are the same term, even though they are syntactically distinct. Formally,
λ-terms live in a quotient of the raw syntax by the α-equivalence relation.
Consequences:

- **Structural (decidable) equality is not the equality.** You cannot decide
  `M = N` for λ-terms by recursively comparing constructors — `λx. x` and
  `λy. y` would come out unequal. You need a separate **α-equivalence
  algorithm** (e.g., De Bruijn indices, or a capture-avoiding renaming pass).
- **Substitution must be capture-avoiding.** `[x:=N] (λy. M)` must rename `y`
  if `y` occurs free in `N`. This is the source of the substitution lemma's
  complexity.

### 4.2 Arrow graphs: equality is structural

`Graph` is a **first-order algebraic data type with no binder**. Two graphs
are equal **iff** they are built from the same constructors in the same order.
There is no quotient, no α-equivalence, and no variable to rename:

- **Structural equality _is_ the equality.** `deriving DecidableEq` on `Graph`
  gives a decision procedure for `G = H` by recursively comparing constructors.
  No separate algorithm is needed.
- **There is no substitution**, so there is no capture to avoid.

The graph syntax pays **no α-tax**. This is not a theorem one proves; it is a
property of the syntax itself, and it is what makes the cut-elimination
theorem above so simple: the rewrites operate on a quotient-free first-order
data type, so they are ordinary structural rewrites.

---

## 5. Summary

|                                  | λ-calculus / natural deduction         | arrow graphs                             |
| -------------------------------- | -------------------------------------- | ---------------------------------------- |
| **Binder**                       | λ (binds variables)                    | none                                     |
| **Cut elimination step**         | a substitution                         | a local graph rewrite                    |
| **Substitution lemma**           | required (prerequisite)                | not needed (nothing to substitute)       |
| **α-equivalence**                | required (equality is a quotient)      | not needed (equality is structural)      |
| **Decidable equality**           | needs a separate α-algorithm           | `deriving DecidableEq` (structural)      |
| **Cut-elimination preservation** | subject reduction + substitution lemma | case analysis on the rewrite (this file) |

The mechanized theorems in `ProofAdvantage.lean` establish that cut
elimination for arrow graphs — unlike for λ-calculus — is a system of local,
binder-free, quotient-free rewrites that preserve proofs and typings by pure
structural case analysis. This is a real proof-theoretic advantage of the graph
calculus, and it is **non-definitional**: it does not follow from the
`TyOf ↔ PrOf` correspondence, it is not a restatement of the definitions, and
it would fail (or require substantial auxiliary machinery — substitution
lemmas, α-equivalence, termination measures) for any λ-based proof object.

The graph is λ-free by construction, and it pays no substitution tax and no
α-tax. That is the advantage.
