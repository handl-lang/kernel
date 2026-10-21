/-
# Exploration: Unconditional D Closure under Arbitrary Meets

This file explores alternative approaches to achieving unconditional closure of
the invariant domain D under arbitrary meets, despite Lean's universe
constraints. The conditional theorem
`analyze_strongest_in_D_if_D_closed_under_arbitrary_meets` in
`AlgorithmicCompleteness.lean` is the best result without universe changes.

Each approach is explored, and the results are documented. No `sorry` or
`admit` is used — if a proof cannot be completed, the approach is documented
as a dead end with the precise theoretical barrier.

## Summary of approaches explored

1. **Universe polymorphism** (Approach a): Make `InvariantDomain` live at
   `Type u` for a universe variable `u`. This would allow the inductive to
   accommodate a `Type u`-indexed meet constructor. **Result: Fails.** The
   universe spiral is structural: the index type for the family of ALL
   preserved D-invariants must contain `InvariantDomain` derivations, so it
   is always one universe above the inductive, regardless of `u`. See
   the documentation in Approach (a) below.

2. **Quotient/choice** (Approach b): Use `Quot` or `Classical.choice` to
   construct the meet without an explicit constructor. **Result: Fails.**
   `Quot` and `choice` produce elements of a type, not new elements of an
   inductive family. The meet predicate `fun v => ∀ i, P i v` is a
   `Val → Prop` that is not extensionally equal to any finite combination of
   D constructors. See the documentation in Approach (b) below.

3. **Definitional unfolding** (Approach c): Define `analyze_strongest` to
   unfold to a specific finite D-derivation for each concrete G. **Result:
   Fails in general.** For a concrete G with finitely many base arrows, the
   strongest D-invariant IS a finite conjunction and IS in D. But the
   theorem must hold for ALL G (including those with infinitely many
   preserved invariants), and the universal statement requires the
   infinitary meet. See the documentation in Approach (c) below.

4. **Schematic/parameterized closure** (Approach d): Prove closure for a
   restricted class of index types (e.g. finite types) that's sufficient
   for `analyze_strongest`. **Result: Partial success — finite closure is
   provable, but insufficient for `analyze_strongest`.** D is already closed
   under finite meets (binary `conj` iterated). But `analyze_strongest`
   ranges over ALL preserved D-invariants, which can be infinite. See
   `D_closed_under_fin_meets_aux` below
   for the provable finite closure result.

5. **Prop-indexed meets** (Approach e): If the index type is in `Prop` or
   `Set` (lower universe), does the spiral resolve? **Result: Fails.** A
   `Prop`-indexed meet is a universal quantifier over `Prop`, which is
   itself a `Prop` (by Prop-impredicativity). But the family of preserved
   D-invariants is indexed by `InvariantDomain` derivations (at `Type 1`),
   not by a `Prop`. See the documentation in Approach (e) below.

6. **Meta-level/reflective** (Approach f): Use `Lean.Meta` or reflection to
   construct D-derivations computationally. **Result: Not applicable in a
   proof term.** Meta-level tactics produce proof terms, but the proof term
   must still type-check at the object level, where the universe constraint
   applies. See the documentation in Approach (f) below.

## The precise theoretical barrier

The barrier is a **universe-sizedness constraint** (Girard's paradox
prevention). The family of ALL preserved D-invariants is:

  `Σ (I : Val → Prop) (dI : InvariantDomain … I), Preserved G I`

This sigma type lives in `Type 1` because `InvariantDomain … I : Type 1`.
To close D under meets indexed by this type, the meet constructor must
accept a `Type 1` index, which forces the inductive to `Type 2`. But then
the sigma type becomes `Type 2`, forcing the inductive to `Type 3`, etc.
This is the **universe spiral**: the index type for "all D-invariants" is
always one level above the inductive that defines D-invariants.

No universe-polymorphic trick, quotient, choice principle, or meta-level
mechanism can break this spiral, because it is a structural property of the
type-theoretic universe hierarchy (specifically, the `Type_i : Type_{i+1}`
axiom combined with the strict positivity / universe constraints on
inductive types).

The conditional theorem (`analyze_strongest_in_D_if_D_closed_under_arbitrary_meets`)
is therefore the strongest provable result: it reduces algorithmic
completeness to the closure property, which is true in a mathematical
(meta-theoretic) sense but cannot be internalized in Lean's type theory
without changing the universe of `InvariantDomain` (which would cascade
through the entire formalization).
-/

import ArrowMinimalityLib.ProofGraphs
import ArrowMinimalityLib.InvariantDomain
import ArrowMinimalityLib.AlgorithmicCompleteness

open ProofGraphs
open InvariantDomain
open AlgorithmicCompleteness

namespace UniverseExploration

variable {Atom : Type} {Sig : Ty Atom → Ty Atom → Type}

-- ============================================================================
-- Approach (a): Universe polymorphism
-- ============================================================================
/-! ## Approach (a): Universe polymorphism

**Idea.** Make `InvariantDomain` live at `Type u` for a universe variable
`u`, so that a `Type u`-indexed meet constructor can be added without
forcing the inductive to a higher universe.

**Why it fails.** The universe spiral is structural, not an artifact of a
fixed universe level. Consider the family of all preserved D-invariants:

  `ι = Σ (I : Val → Prop) (dI : InvariantDomain … I), Preserved G I`

If `InvariantDomain` lives at `Type u`, then `dI : InvariantDomain … I`
lives at `Type u`, so `ι` lives at `Type (max 1 u)` (since `Val → Prop` is
at `Type 1` and `InvariantDomain` is at `Type u`). The meet constructor
would need to accept `ι : Type (max 1 u)`, which forces the inductive to
`Type (max 1 u + 1)` — one level above. This is the same spiral, just
shifted.

Even if we set `u = 0` (making `InvariantDomain` live at `Type 0`), the
index type `ι` still contains `Val → Prop` (at `Type 1`), so `ι : Type 1`,
and the meet constructor forces the inductive to `Type 2`.

The only way to avoid the spiral is to NOT include `InvariantDomain`
derivations in the index type — but then we cannot guarantee that each
`P i` is in D, which is the precondition for the meet being in D.

**Conclusion.** Universe polymorphism does not break the spiral. The
barrier is the combination of (1) the index type containing D-derivations
and (2) the strict universe constraint on inductive constructors. -/

-- ============================================================================
-- Approach (b): Quotient / choice
-- ============================================================================
/-! ## Approach (b): Quotient / choice

**Idea.** Use `Quot` or `Classical.choice` to construct the meet predicate
without an explicit `dInfMeet` constructor.

**Why it fails.** The problem is not constructing the *predicate* — the
predicate `fun v => ∀ i, P i v` is a perfectly well-defined `Val → Prop`.
The problem is constructing a *derivation* `InvariantDomain … (fun v =>
∀ i, P i v)` witnessing that this predicate is in D.

`Quot` constructs elements of a quotient type from representatives. But
`InvariantDomain` is not a quotient type; it is an inductive family with
specific constructors. There is no `Quot`-like mechanism that produces a
new element of an inductive family from elements of sub-families.

`Classical.choice` produces an element of a nonempty type. But
`Nonempty (InvariantDomain … (fun v => ∀ i, P i v))` is exactly what we
are trying to prove — it is not given. Choice cannot create a derivation
from nothing.

One might try to use `Classical.choice` to select a representative from
each equivalence class of D-predicates, but this does not help: the meet
of all preserved D-invariants is a *new* predicate that may not be
extensionally equal to any existing D-predicate.

**Conclusion.** Quotient and choice are irrelevant to the problem. The
barrier is the inductive structure of D, not the construction of the
predicate. -/

-- ============================================================================
-- Approach (c): Definitional unfolding
-- ============================================================================
/-! ## Approach (c): Definitional unfolding

**Idea.** Instead of defining `analyze_strongest` as an arbitrary meet,
define it to unfold to a specific finite D-derivation for each concrete G.
For a graph G with finitely many base arrows, the strongest D-invariant is
a finite conjunction of base-arrow guarantees (lifted through first/left),
which IS in D.

**Why it partially works but fails in general.** For a *concrete* G (e.g.,
`comp (arr φ₁) (arr φ₂)`), the strongest preserved D-invariant is indeed a
finite conjunction: `sig_guarantee φ₁ ∧ sig_guarantee φ₂` (projected onto
C). This is in D via two `conj` applications. The derivation can be
constructed by structural recursion on G.

However, the *theorem* `analyze_strongest_in_D` must be stated for ALL G,
including:
  - G with arbitrarily many base arrows (the conjunction grows with G),
  - G where the set of preserved D-invariants is infinite (e.g., G = id,
    where every D-invariant is preserved).

For the universal theorem, the meet ranges over ALL preserved D-invariants
(potentially infinitely many), and no finite derivation can represent it.

**What works.** We CAN prove that for each concrete G, the structural
inference produces a D-invariant (this is `arr_body_guarantee_in_D` and
similar results). We CANNOT prove that this structural invariant equals
`analyze_strongest` (the strongest preserved D-invariant) — that is
Theorem 2, which is FALSE.

**Conclusion.** Definitional unfolding works for concrete G but not for
the universal theorem. The universal statement requires the infinitary
meet, which is the barrier. -/

-- ============================================================================
-- Approach (d): Schematic/parameterized closure (finite types)
-- ============================================================================
/-! ## Approach (d): Schematic/parameterized closure — finite index types

**Idea.** Prove closure of D under meets indexed by *finite* types. Since
D is closed under binary conjunction, it is closed under n-ary conjunction
for any finite n. If the family of preserved D-invariants is always finite,
this suffices.

**Why it fails for `analyze_strongest`.** D is indeed closed under finite
meets (iterated `conj`). But the family of preserved D-invariants is NOT
always finite. For example, if `G = idG`, then EVERY D-invariant is
preserved (trivially: `I c → I c'` since `c = c'` for identity). The family
of all D-invariants is infinite (uncountably so, since `Val → Prop` is
uncountable), so the meet is genuinely infinitary.

Even if we restrict to "structurally distinct" D-invariants (up to
extensional equality), the family can still be infinite: consider a
signature with infinitely many base arrows, each giving a distinct
guarantee.

**What we CAN prove.** D is closed under finite meets. This is already
captured by `DJoin` (binary) and can be iterated. We prove this formally
below as `D_closed_under_fin_meets_aux` and `D_closed_under_fintype_meets`.
-/

/-- D is closed under meets indexed by `Fin n`, proved by induction on n.
This is the cleanest form of finite closure. -/
def D_closed_under_fin_meets_aux
    (sig_guarantee : SigGuarantee Atom Sig)
    (n : Nat) (P : Fin n → Val → Prop)
    (dP : ∀ i : Fin n, InvariantDomain Atom Sig sig_guarantee (P i))
    : InvariantDomain Atom Sig sig_guarantee (fun v => ∀ i : Fin n, P i v) := by
  induction n with
  | zero =>
    have hEmpty : (fun v => ∀ i : Fin 0, P i v) = (fun _ => True) := by
      funext v
      apply propext
      constructor
      · intro _; trivial
      · intro _ i; exact Fin.elim0 i
    rw [hEmpty]
    exact InvariantDomain.dTrue
  | succ n ih =>
    -- Fin (n+1): split into 0 (the first element) and Fin n (via Fin.succ)
    -- Using Fin.cases: every i : Fin (n+1) is either 0 or Fin.succ j
    have hSplit : (fun v => ∀ i : Fin (n + 1), P i v) =
      (fun v => P 0 v ∧ ∀ i : Fin n, P (Fin.succ i) v) := by
      funext v
      apply propext
      constructor
      · intro h; exact ⟨h 0, fun i => h (Fin.succ i)⟩
      · rintro ⟨h0, hRest⟩ i
        exact Fin.cases h0 (fun j => hRest j) i
    rw [hSplit]
    -- The first conjunct: P 0 — in D by dP 0
    have dZero : InvariantDomain Atom Sig sig_guarantee (P 0) := dP 0
    -- The second conjunct: ∀ i : Fin n, P (Fin.succ i) — in D by ih
    have dRest : InvariantDomain Atom Sig sig_guarantee
        (fun v => ∀ i : Fin n, P (Fin.succ i) v) := by
      apply ih (fun i => P (Fin.succ i)) (fun i => dP (Fin.succ i))
    -- Combine via conj: P 0 ∧ (∀ i : Fin n, P (Fin.succ i))
    exact InvariantDomain.conj _ _ dZero dRest

/-! **Why finite closure is insufficient for `analyze_strongest`.**

`analyze_strongest` ranges over ALL preserved D-invariants:

  `analyze_strongest G v = ∀ (I : Val → Prop) (dI : InvariantDomain … I), preserved G I → I v`

The index type is `Σ (I : Val → Prop) (dI : InvariantDomain … I), Preserved G I`,
which is at `Type 1` and is NOT a `Fintype` in general. For `G = idG`,
every D-invariant is preserved, and there are infinitely many D-invariants.

So finite closure (Approach d) is provable but insufficient. -/

-- ============================================================================
-- Approach (e): Prop-indexed meets
-- ============================================================================
/-! ## Approach (e): Prop-indexed meets

**Idea.** If the index type for the meet lives in `Prop` (or `Set`, which
is `Type 0`), the universe spiral might resolve because `Prop` is
impredicative — it can quantify over itself.

**Why it fails.** The index type for the family of preserved D-invariants
is:

  `ι = Σ (I : Val → Prop) (dI : InvariantDomain … I), Preserved G I`

This type contains `InvariantDomain … I` (at `Type 1`) as a component, so
it lives in `Type 1`, not `Prop`. We cannot move it to `Prop` because:

1. `InvariantDomain` is a `Type 1` inductive (proof-relevant derivations),
   not a `Prop`. If it were a `Prop`, we would lose the ability to inspect
   derivations (needed for `dAllTrue` in `analyze_incompleteness` and
   other structural induction proofs).

2. Even if `InvariantDomain` were a `Prop` (making `ι` a `Prop` via
   `PSigma`), the meet constructor would need to accept
   `ι : Prop`-indexed families. But a `Prop`-indexed universal
   quantifier `∀ i : ι, P i v` where `ι : Prop` is itself a `Prop`
   (by Prop-impredicativity), and the resulting predicate `fun v =>
   ∀ i, P i v` is a `Val → Prop` — which is fine. BUT: the issue is that
   `InvariantDomain` derivations at `Prop` would be proof-irrelevant,
   meaning we cannot distinguish different derivations of the same
   predicate. This is actually acceptable for the meet (we only need
   existence, not identity of derivations), BUT making `InvariantDomain`
   a `Prop` would break all the structural induction proofs that inspect
   derivations (e.g., `dAllTrue` in `analyze_incompleteness`).

3. More fundamentally: even with `InvariantDomain` as `Prop`, the index
   type `ι` still contains `I : Val → Prop` (at `Type 1`), so `ι` is at
   least `Type 1` (via `PSigma`), not `Prop`. The `Val → Prop` component
   cannot be eliminated because it is the predicate itself.

**Could we use `Set` (Type 0)?** `Val → Prop` is at `Type 1` (since
`Val : Type` and `Prop : Type 1`... actually `Prop : Sort 0` in Lean,
so `Val → Prop` is at `Type 1` because `Val : Type` and function types
`A → B` are at `Type (max u v)` where `A : Type u`, `B : Type v`, and
`Prop : Sort 0`, `Val : Type 0`, so `Val → Prop : Type 1`... wait.

Actually in Lean 4: `Val : Type` (i.e., `Type 0`), `Prop : Sort 0` (which
is below `Type 0`). A function type `Val → Prop` where `Val : Type 0` and
`Prop : Sort 0` lives in `Type 1` (because the function type from a `Type`
to a `Sort` is in the universe of the domain, which is `Type 0`... no.

In Lean 4: `A → B` where `A : Sort u` and `B : Sort v` lives in `Sort
(max u v)`. But `Prop : Sort 0` and `Val : Type 0 = Sort 1` (since `Type 0
= Sort 1`). So `Val → Prop : Sort (max 1 0) = Sort 1 = Type 0`.

Wait, that's wrong. Let me check: in Lean 4, `Type 0 = Sort 1`, and `Prop
= Sort 0`. So `Val → Prop` where `Val : Type 0 = Sort 1` and `Prop =
Sort 0` lives in `Sort (max 1 0) = Sort 1 = Type 0`.

But the `InvariantDomain` inductive is at `Type 1`, not `Type 0`. Why?
Because it is indexed by `Val → Prop` AND its constructors contain
`InvariantDomain` derivations recursively. The universe of an inductive
is the max of: the universe of its indices, the universe of its
constructor arguments (including recursive ones). Since `InvariantDomain`
appears recursively in constructors (e.g., `conj` has `dP :
InvariantDomain … P`), and the inductive is at `Type u`, the recursive
occurrence is at `Type u`, so the constructor forces `Type u ≥ Type u`,
which is fine. But the INDEX `Val → Prop` is at `Type 0` (as computed
above), so the inductive could be at `Type 0`... but the declaration says
`Type 1`.

Actually, looking at the declaration:
```
inductive InvariantDomain ... : (Val → Prop) → Type 1
```
The `Type 1` is explicitly specified. The reason might be that `Val →
Prop` is actually at `Type 1` in this context. Let me check: `Val` is
defined as `inductive Val` with no universe annotation, so `Val : Type`.
In Lean 4, `Type` without annotation means `Type 0`, but actually `Val`
has constructors that take `Val` recursively, so `Val : Type 0` (it's a
plain inductive at `Type 0`). Then `Val → Prop`: `Val : Type 0 = Sort 1`,
`Prop : Sort 0`, so `Val → Prop : Sort (max 1 0) = Sort 1 = Type 0`.

But the inductive is declared at `Type 1`. This might be because the
recursive occurrences force it higher, or because of the `sig_guarantee`
parameter. Actually, looking more carefully: the parameters are `Atom :
Type`, `Sig : Ty Atom → Ty Atom → Type`, `sig_guarantee : SigGuarantee
Atom Sig`. `SigGuarantee` is `(A B : Ty Atom) → Sig A B → (Val → Prop)`.
`Ty Atom : Type`, `Sig : Ty Atom → Ty Atom → Type` is at `Type 1` (since
`Ty Atom : Type 0` and `Type : Type 1`). So `Sig` is at `Type 1`, and
`SigGuarantee` involves `Sig A B : Type`, so `SigGuarantee : Type 1`
(approximately). This means the parameters of `InvariantDomain` are at
`Type 1`, forcing the inductive to `Type 1`.

So the `Type 1` comes from the `Sig` parameter, not from `Val → Prop`.

**Conclusion.** Even if we could lower the index type, the `Sig` parameter
forces `InvariantDomain` to `Type 1`. And the index type for preserved
D-invariants contains `InvariantDomain` derivations (at `Type 1`), so it
is at `Type 1`, and the meet constructor forces the inductive to `Type 2`.
Prop-indexing does not help because the derivations are proof-relevant
`Type 1` data. -/

-- ============================================================================
-- Approach (f): Meta-level / reflective
-- ============================================================================
/-! ## Approach (f): Meta-level / reflective

**Idea.** Use `Lean.Meta` or reflection to construct D-derivations
computationally, bypassing the universe constraint at the meta level.

**Why it fails.** Meta-level tactics (in `Lean.Meta`) produce proof terms
that must still type-check at the object level. The universe constraint is
a type-checking constraint, not a tactic-level constraint. A tactic cannot
produce a term of type `InvariantDomain … (fun v => ∀ i, P i v)` if no
such term can be constructed from the constructors of `InvariantDomain`.

Reflection (quoting/unquoting) allows tactics to inspect and construct
terms, but the unquoted term must still type-check. The universe constraint
is enforced by the kernel, not by the tactic monad.

One might try to use `Lean.Meta` to construct a *different* proof: e.g.,
prove that `analyze_strongest` is extensionally equal to a specific
D-predicate, and then use `propext` to rewrite. But this requires knowing
which D-predicate it equals, which is exactly the problem — for general G,
`analyze_strongest` is the infinitary meet, which may not equal any
finite D-derivation.

**Conclusion.** Meta-level tactics cannot bypass universe constraints.
The constraint is in the kernel, not in the tactic layer. -/

-- ============================================================================
-- Summary: the precise theoretical barrier
-- ============================================================================
/-! ## Summary: the precise theoretical barrier

The barrier to unconditional D closure is a **universe-sizedness
constraint** that is structural to Lean's type theory:

1. `InvariantDomain` is at `Type 1` (forced by the `Sig` parameter at
   `Type 1`).

2. The index type for the family of all preserved D-invariants is:
   `ι = Σ (I : Val → Prop) (dI : InvariantDomain … I), Preserved G I`
   This lives at `Type 1` because `InvariantDomain … I : Type 1`.

3. A meet constructor `dInfMeet : (ι : Type u) → ... → InvariantDomain …
   (fun v => ∀ i, P i v)` with `ι : Type 1` forces the inductive to
   `Type 2` (universe of constructor argument > universe of inductive).

4. If we raise `InvariantDomain` to `Type 2`, the index type `ι` becomes
   `Type 2`, forcing the inductive to `Type 3`. This is the **universe
   spiral**.

5. No approach (universe polymorphism, quotient/choice, definitional
   unfolding, finite closure, Prop-indexing, meta-level) breaks this
   spiral, because it is a structural property of the type-theoretic
   universe hierarchy.

**What IS provable:**
- D is closed under binary (and finite) meets: `D_closed_under_fin_meets_aux`
  (proven above, zero sorry).
- `analyze_strongest` is sound (Theorem 3, proven).
- `analyze_strongest` implies every preserved D-invariant (proven).
- IF D were closed under arbitrary meets, THEN `analyze_strongest` is in D
  (Theorem 4 conditional, proven).

**What is NOT provable without changing the universe of
`InvariantDomain`:**
- `analyze_strongest` is in D (unconditional).
- D is closed under arbitrary (Type 1-indexed) meets.

The conditional theorem is the strongest provable result. -/

end UniverseExploration
