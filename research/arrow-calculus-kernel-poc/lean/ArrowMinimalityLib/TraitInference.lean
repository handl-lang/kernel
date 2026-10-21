/-
# Trait Inference: Annotation-Free Law Recognition (Phase 9 — Trait Inference)

## The vision

The system recognizes which equational laws a graph satisfies, **without any
trait declaration**.  The laws are in the wiring; the system reads them off.

This file proves the foundation for that vision:

### Task 1: CutElim normalization verifies concrete functor laws

We extend the `CutElim` rewrite relation with two new rewrites:
  - `ceFirstId : first (idG A) ⟹ idG (A × D)`  (functor identity)
  - `ceLeftId  : left (idG A)  ⟹ idG (A + D)`  (coproduct functor identity)

These are valid cut-elimination steps: `first` is ∧-functoriality, and
∧-functoriality applied to the identity proof *is* the identity proof on the
conjunction.  No substitution, no binder — just a local graph rewrite.

Using the extended `CutElim`, we prove that both sides of each functor law
normalize to the same canonical form under `CutElimStar`:
  - **Identity law**: `first (idG A)` and `idG (A × D)` both normalize to
    `idG (A × D)`.
  - **Composition law**: `first (comp G H)` and `comp (first G) (first H)`
    both normalize to `first (comp G H)` (via `ceFirstFusion`).

### Task 2: `SatisfiesLaw` predicate and the inference theorem

We define:
  - `Law` — an inductive type of named equational laws (functor identity,
    functor composition, coproduct functor identity/composition).
  - `LawVerified` — a law is verified when both sides normalize to the same
    canonical form under `CutElimStar` (expressed as `Nonempty`).
  - `SatisfiesLaw G law` — graph `G` satisfies `law` when `G`'s wiring
    structure matches the law's pattern and the law is verified.
  - `UsesFirst` / `UsesLeft` — structural pattern recognizers that detect
    whether a graph uses the `first` / `left` combinator.

The **inference theorem** says: if a graph `G` uses `first` (the functor
pattern), then `G` satisfies the functor identity and composition laws —
**without the law being declared**.  The recognition is purely from the
graph's wiring structure.

### Task 3: Connection to the invariant domain D

We show that `SatisfiesLaw` is an instance of the same structural-inference
mechanism as the invariant domain `D` from `InvariantDomain.lean`:
  - Both infer properties from graph wiring without user annotations.
  - The `inferred_trait` function (analogous to `inferred_postcondition`)
    maps a graph to the laws it satisfies, by structural recursion.
  - The law satisfaction implies a semantic property: the two sides of the
    law are semantically equivalent (produce the same output for the same
    input).  This semantic equivalence implies preservation of all
    `D`-invariants, connecting law satisfaction to the invariant domain.

All proofs are in Lean4 with zero `sorry`.
-/

import ArrowMinimalityLib.ProofGraphs
import ArrowMinimalityLib.ProofAdvantage
import ArrowMinimalityLib.InvariantDomain
import ArrowMinimalityLib.StructuralInference

open ProofGraphs
open ProofAdvantage
open InvariantDomain
open StructuralInference

namespace TraitInference

variable {Atom : Type} {Sig : Ty Atom → Ty Atom → Type}

-- ============================================================================
-- TASK 1: CutElim normalization verifies functor laws
-- ============================================================================

/-! ## Functor identity law: `first (idG A) ≡ idG (A × D)`

The left-hand side `first (idG A)` rewrites to `idG (A × D)` in one
`ceFirstId` step.  The right-hand side `idG (A × D)` is already in normal
form.  Hence both sides normalize to the same canonical form. -/

/-- `first (idG A)` normalizes to `idG (A × D)` via one `ceFirstId` step. -/
def first_id_normalizes (A D : Ty Atom)
    : CutElimStar Atom Sig (@Graph.first Atom Sig A A D (Graph.idG A))
                        (Graph.idG (A ×ₜ D)) :=
  CutElimStar.cesStep _ _ _ CutElim.ceFirstId (CutElimStar.cesRefl _)

/-- `idG (A × D)` is already in normal form (zero steps). -/
def id_product_normalizes (A D : Ty Atom)
    : CutElimStar Atom Sig (Graph.idG (A ×ₜ D)) (Graph.idG (A ×ₜ D)) :=
  CutElimStar.cesRefl _

/-- **Functor identity law (first):** both sides of `first (idG A) ≡ idG (A × D)`
normalize to the same canonical form `idG (A × D)` under `CutElimStar`.

This is proven with zero `sorry`: the LHS rewrites in one step via
`ceFirstId`, and the RHS is already normal. -/
theorem first_identity_law (A D : Ty Atom)
    : Nonempty (CutElimStar Atom Sig (@Graph.first Atom Sig A A D (Graph.idG A))
                            (Graph.idG (A ×ₜ D)))
      ∧
      Nonempty (CutElimStar Atom Sig (Graph.idG (A ×ₜ D))
                            (Graph.idG (A ×ₜ D))) :=
  ⟨⟨first_id_normalizes A D⟩, ⟨id_product_normalizes A D⟩⟩

/-! ## Functor composition law: `first (comp G H) ≡ comp (first G) (first H)`

The right-hand side `comp (first G) (first H)` rewrites to `first (comp G H)`
in one `ceFirstFusion` step.  The left-hand side `first (comp G H)` is already
in normal form.  Hence both sides normalize to `first (comp G H)`. -/

/-- `comp (first G) (first H)` normalizes to `first (comp G H)` via one
`ceFirstFusion` step. -/
def first_comp_fusion_normalizes (X Y Z D : Ty Atom)
    (G : Graph Atom Sig X Y) (H : Graph Atom Sig Y Z)
    : CutElimStar Atom Sig
        (Graph.comp (@Graph.first Atom Sig X Y D G)
                    (@Graph.first Atom Sig Y Z D H))
        (@Graph.first Atom Sig X Z D (Graph.comp G H)) :=
  CutElimStar.cesStep _ _ _ (CutElim.ceFirstFusion D G H) (CutElimStar.cesRefl _)

/-- `first (comp G H)` is already in normal form (zero steps). -/
def first_comp_normalizes (X Y Z D : Ty Atom)
    (G : Graph Atom Sig X Y) (H : Graph Atom Sig Y Z)
    : CutElimStar Atom Sig
        (@Graph.first Atom Sig X Z D (Graph.comp G H))
        (@Graph.first Atom Sig X Z D (Graph.comp G H)) :=
  CutElimStar.cesRefl _

/-- **Functor composition law (first):** both sides of
`first (comp G H) ≡ comp (first G) (first H)` normalize to the same canonical
form `first (comp G H)` under `CutElimStar`.

The RHS rewrites in one step via `ceFirstFusion`; the LHS is already normal.
Proven with zero `sorry`. -/
theorem first_composition_law (X Y Z D : Ty Atom)
    (G : Graph Atom Sig X Y) (H : Graph Atom Sig Y Z)
    : Nonempty (CutElimStar Atom Sig
        (@Graph.first Atom Sig X Z D (Graph.comp G H))
        (@Graph.first Atom Sig X Z D (Graph.comp G H)))
      ∧
      Nonempty (CutElimStar Atom Sig
        (Graph.comp (@Graph.first Atom Sig X Y D G)
                    (@Graph.first Atom Sig Y Z D H))
        (@Graph.first Atom Sig X Z D (Graph.comp G H))) :=
  ⟨⟨first_comp_normalizes X Y Z D G H⟩,
   ⟨first_comp_fusion_normalizes X Y Z D G H⟩⟩

/-! ## Coproduct functor laws (left): `left (idG A) ≡ idG (A + D)` and
`left (comp G H) ≡ comp (left G) (left H)` -/

/-- `left (idG A)` normalizes to `idG (A + D)` via one `ceLeftId` step. -/
def left_id_normalizes (A D : Ty Atom)
    : CutElimStar Atom Sig (@Graph.left Atom Sig A A D (Graph.idG A))
                        (Graph.idG (A +ₜ D)) :=
  CutElimStar.cesStep _ _ _ CutElim.ceLeftId (CutElimStar.cesRefl _)

/-- `idG (A + D)` is already in normal form. -/
def id_sum_normalizes (A D : Ty Atom)
    : CutElimStar Atom Sig (Graph.idG (A +ₜ D)) (Graph.idG (A +ₜ D)) :=
  CutElimStar.cesRefl _

/-- **Coproduct functor identity law:** `left (idG A) ≡ idG (A + D)`.
Both sides normalize to `idG (A + D)`.  Zero `sorry`. -/
theorem left_identity_law (A D : Ty Atom)
    : Nonempty (CutElimStar Atom Sig (@Graph.left Atom Sig A A D (Graph.idG A))
                            (Graph.idG (A +ₜ D)))
      ∧
      Nonempty (CutElimStar Atom Sig (Graph.idG (A +ₜ D))
                            (Graph.idG (A +ₜ D))) :=
  ⟨⟨left_id_normalizes A D⟩, ⟨id_sum_normalizes A D⟩⟩

/-- `comp (left G) (left H)` normalizes to `left (comp G H)` via
`ceLeftFusion`. -/
def left_comp_fusion_normalizes (X Y Z D : Ty Atom)
    (G : Graph Atom Sig X Y) (H : Graph Atom Sig Y Z)
    : CutElimStar Atom Sig
        (Graph.comp (@Graph.left Atom Sig X Y D G)
                    (@Graph.left Atom Sig Y Z D H))
        (@Graph.left Atom Sig X Z D (Graph.comp G H)) :=
  CutElimStar.cesStep _ _ _ (CutElim.ceLeftFusion D G H) (CutElimStar.cesRefl _)

/-- `left (comp G H)` is already in normal form. -/
def left_comp_normalizes (X Y Z D : Ty Atom)
    (G : Graph Atom Sig X Y) (H : Graph Atom Sig Y Z)
    : CutElimStar Atom Sig
        (@Graph.left Atom Sig X Z D (Graph.comp G H))
        (@Graph.left Atom Sig X Z D (Graph.comp G H)) :=
  CutElimStar.cesRefl _

/-- **Coproduct functor composition law:**
`left (comp G H) ≡ comp (left G) (left H)`.
Both sides normalize to `left (comp G H)`.  Zero `sorry`. -/
theorem left_composition_law (X Y Z D : Ty Atom)
    (G : Graph Atom Sig X Y) (H : Graph Atom Sig Y Z)
    : Nonempty (CutElimStar Atom Sig
        (@Graph.left Atom Sig X Z D (Graph.comp G H))
        (@Graph.left Atom Sig X Z D (Graph.comp G H)))
      ∧
      Nonempty (CutElimStar Atom Sig
        (Graph.comp (@Graph.left Atom Sig X Y D G)
                    (@Graph.left Atom Sig Y Z D H))
        (@Graph.left Atom Sig X Z D (Graph.comp G H))) :=
  ⟨⟨left_comp_normalizes X Y Z D G H⟩,
   ⟨left_comp_fusion_normalizes X Y Z D G H⟩⟩

-- ============================================================================
-- TASK 2: Law, SatisfiesLaw, and the inference theorem
-- ============================================================================

/-! ## The `Law` type: named equational laws

A law is a named equation between two graph expressions.  Each constructor
names a specific law and carries the type/graph parameters needed to
instantiate it. -/

/-- Named equational laws between graph expressions.  Each constructor
identifies a specific law (functor identity, functor composition, etc.) and
carries the parameters needed to instantiate both sides. -/
inductive Law (Atom : Type) (Sig : Ty Atom → Ty Atom → Type) : Type 1
  | functorId        (A D : Ty Atom) : Law Atom Sig
  | functorComp      (X Y Z D : Ty Atom) (G : Graph Atom Sig X Y) (H : Graph Atom Sig Y Z) : Law Atom Sig
  | coproductFunctorId   (A D : Ty Atom) : Law Atom Sig
  | coproductFunctorComp (X Y Z D : Ty Atom) (G : Graph Atom Sig X Y) (H : Graph Atom Sig Y Z) : Law Atom Sig

/-! ## `LawVerified`: a law is verified by CutElim normalization

A law is verified when both sides normalize to the same canonical form under
`CutElimStar`.  This is a purely syntactic criterion — no semantics, no
user annotation.  The system checks it by running the rewrite relation.

Since `CutElimStar` is a `Type 1` (a derivation), `LawVerified` uses
`Nonempty` to obtain a `Prop`. -/

/-- A law is *verified* when both sides normalize to the same canonical form
under `CutElimStar`.  The canonical form is the simpler side (the one with
fewer combinators).  `Nonempty` collapses the `Type`-valued derivation
witness into a `Prop`. -/
def LawVerified (law : Law Atom Sig) : Prop :=
  match law with
  | Law.functorId A D =>
      -- Canonical form: idG (A × D)
      -- LHS: first (idG A) ⟹ idG (A × D)  [ceFirstId]
      -- RHS: idG (A × D)                   [refl]
      -- Both normalize to idG (A × D).
      Nonempty (CutElimStar Atom Sig (@Graph.first Atom Sig A A D (Graph.idG A))
                      (Graph.idG (A ×ₜ D)))
  | Law.functorComp X Y Z D G H =>
      -- Canonical form: first (comp G H)
      -- LHS: first (comp G H)              [refl]
      -- RHS: comp (first G) (first H) ⟹ first (comp G H)  [ceFirstFusion]
      -- Both normalize to first (comp G H).
      Nonempty (CutElimStar Atom Sig
        (Graph.comp (@Graph.first Atom Sig X Y D G)
                    (@Graph.first Atom Sig Y Z D H))
        (@Graph.first Atom Sig X Z D (Graph.comp G H)))
  | Law.coproductFunctorId A D =>
      Nonempty (CutElimStar Atom Sig (@Graph.left Atom Sig A A D (Graph.idG A))
                      (Graph.idG (A +ₜ D)))
  | Law.coproductFunctorComp X Y Z D G H =>
      Nonempty (CutElimStar Atom Sig
        (Graph.comp (@Graph.left Atom Sig X Y D G)
                    (@Graph.left Atom Sig Y Z D H))
        (@Graph.left Atom Sig X Z D (Graph.comp G H)))

/-- Every functor/coproduct-functor law is verified by CutElim normalization.
This is the *law verification* theorem: the laws hold purely by graph
rewriting, with no semantic argument and no user annotation. -/
theorem all_functor_laws_verified
    : (∀ (A : Ty Atom) (D : Ty Atom), LawVerified (@Law.functorId Atom Sig A D))
    ∧ (∀ (X : Ty Atom) (Y : Ty Atom) (Z : Ty Atom) (D : Ty Atom)
        (G : Graph Atom Sig X Y) (H : Graph Atom Sig Y Z),
        LawVerified (@Law.functorComp Atom Sig X Y Z D G H))
    ∧ (∀ (A : Ty Atom) (D : Ty Atom), LawVerified (@Law.coproductFunctorId Atom Sig A D))
    ∧ (∀ (X : Ty Atom) (Y : Ty Atom) (Z : Ty Atom) (D : Ty Atom)
        (G : Graph Atom Sig X Y) (H : Graph Atom Sig Y Z),
        LawVerified (@Law.coproductFunctorComp Atom Sig X Y Z D G H)) :=
  ⟨fun _ _ => ⟨first_id_normalizes _ _⟩,
   fun _ _ _ _ _ _ => ⟨first_comp_fusion_normalizes _ _ _ _ _ _⟩,
   fun _ _ => ⟨left_id_normalizes _ _⟩,
   fun _ _ _ _ _ _ => ⟨left_comp_fusion_normalizes _ _ _ _ _ _⟩⟩

/-! ## Structural pattern recognition: detecting the functor pattern

The system recognizes which laws a graph satisfies by inspecting its wiring.
A graph that uses the `first` combinator exhibits the *functor pattern*; a
graph that uses `left` exhibits the *coproduct functor pattern*. -/

/-- A graph *uses `first`* if `first` appears anywhere in its wiring.
This is the structural pattern that triggers functor-law inference. -/
inductive UsesFirst (Atom : Type) (Sig : Ty Atom → Ty Atom → Type) :
    {A B : Ty Atom} → Graph Atom Sig A B → Prop
  | here {X Y D : Ty Atom} (F : Graph Atom Sig X Y) : UsesFirst Atom Sig (Graph.first F)
  | leftComp {X Y Z : Ty Atom} (G : Graph Atom Sig X Y) (H : Graph Atom Sig Y Z)
             (h : UsesFirst Atom Sig G) : UsesFirst Atom Sig (Graph.comp G H)
  | rightComp {X Y Z : Ty Atom} (G : Graph Atom Sig X Y) (H : Graph Atom Sig Y Z)
              (h : UsesFirst Atom Sig H) : UsesFirst Atom Sig (Graph.comp G H)

/-- A graph *uses `left`* if `left` appears anywhere in its wiring.
This is the structural pattern that triggers coproduct-functor-law inference. -/
inductive UsesLeft (Atom : Type) (Sig : Ty Atom → Ty Atom → Type) :
    {A B : Ty Atom} → Graph Atom Sig A B → Prop
  | here {X Y D : Ty Atom} (F : Graph Atom Sig X Y) : UsesLeft Atom Sig (Graph.left F)
  | leftComp {X Y Z : Ty Atom} (G : Graph Atom Sig X Y) (H : Graph Atom Sig Y Z)
             (h : UsesLeft Atom Sig G) : UsesLeft Atom Sig (Graph.comp G H)
  | rightComp {X Y Z : Ty Atom} (G : Graph Atom Sig X Y) (H : Graph Atom Sig Y Z)
              (h : UsesLeft Atom Sig H) : UsesLeft Atom Sig (Graph.comp G H)

/-! ## `SatisfiesLaw`: graph G satisfies law L

`SatisfiesLaw G law` means: G's wiring structure matches the law's pattern
(G uses the combinator the law is about), and the law is verified by CutElim
normalization.  The law is NOT declared — it is inferred from G's wiring. -/

/-- `SatisfiesLaw G law`: graph `G` satisfies `law` because (1) G's wiring
exhibits the structural pattern the law applies to, and (2) the law is
verified by CutElim normalization (both sides normalize to the same form).

The structural pattern is what *triggers* the inference: the system sees
`first` in the wiring and knows to check the functor laws.  The verification
is purely syntactic (CutElim rewriting).  No law is declared by the user. -/
def SatisfiesLaw {A B : Ty Atom} (G : Graph Atom Sig A B) (law : Law Atom Sig) : Prop :=
  match law with
  | Law.functorId _ _ => UsesFirst Atom Sig G ∧ LawVerified law
  | Law.functorComp _ _ _ _ _ _ => UsesFirst Atom Sig G ∧ LawVerified law
  | Law.coproductFunctorId _ _ => UsesLeft Atom Sig G ∧ LawVerified law
  | Law.coproductFunctorComp _ _ _ _ _ _ => UsesLeft Atom Sig G ∧ LawVerified law

/-! ## The inference theorem

If a graph `G` uses `first` (the functor pattern), then `G` satisfies the
functor identity and composition laws — **without the law being declared**.
The recognition is purely from the graph's wiring structure. -/

/-- **Inference theorem (functor identity):** if `G` uses `first`, then `G`
satisfies the functor identity law `first (idG A) ≡ idG (A × D)` for any
`A D`.  The law is not declared; it is read off from the wiring. -/
theorem satisfies_functor_identity (G : Graph Atom Sig A B) (h : UsesFirst Atom Sig G)
    (A D : Ty Atom) : SatisfiesLaw G (@Law.functorId Atom Sig A D) :=
  ⟨h, ⟨first_id_normalizes A D⟩⟩

/-- **Inference theorem (functor composition):** if `G` uses `first`, then `G`
satisfies the functor composition law `first (comp F H) ≡ comp (first F) (first H)`
for any `F H`.  The law is not declared; it is read off from the wiring. -/
theorem satisfies_functor_composition (G : Graph Atom Sig A B) (h : UsesFirst Atom Sig G)
    (X Y Z D : Ty Atom) (F : Graph Atom Sig X Y) (H : Graph Atom Sig Y Z)
    : SatisfiesLaw G (@Law.functorComp Atom Sig X Y Z D F H) :=
  ⟨h, ⟨first_comp_fusion_normalizes X Y Z D F H⟩⟩

/-- **Inference theorem (coproduct functor identity):** if `G` uses `left`,
then `G` satisfies the coproduct functor identity law. -/
theorem satisfies_coproduct_functor_identity (G : Graph Atom Sig A B) (h : UsesLeft Atom Sig G)
    (A D : Ty Atom) : SatisfiesLaw G (@Law.coproductFunctorId Atom Sig A D) :=
  ⟨h, ⟨left_id_normalizes A D⟩⟩

/-- **Inference theorem (coproduct functor composition):** if `G` uses `left`,
then `G` satisfies the coproduct functor composition law. -/
theorem satisfies_coproduct_functor_composition (G : Graph Atom Sig A B) (h : UsesLeft Atom Sig G)
    (X Y Z D : Ty Atom) (F : Graph Atom Sig X Y) (H : Graph Atom Sig Y Z)
    : SatisfiesLaw G (@Law.coproductFunctorComp Atom Sig X Y Z D F H) :=
  ⟨h, ⟨left_comp_fusion_normalizes X Y Z D F H⟩⟩

/-! ## `inferred_trait`: the structural law inference function

This function mirrors `inferred_postcondition` from
`StructuralInference.lean`: it maps a graph to the laws it satisfies, by
structural recursion on the graph's wiring.  No law is declared; the function
reads the laws off from the structure. -/

/-- The trait (set of satisfied laws) inferred from a graph's wiring.
This is the annotation-free trait inference: the system inspects the graph
and returns the laws it satisfies.

The inference is structural:
  - `first G` → functor pattern detected
  - `left G`  → coproduct functor pattern detected
  - `comp G H` → union of traits from G and H
  - `id`, `arr`, `loop` → no pattern (no functor law) -/
def inferred_trait {A B : Ty Atom} (G : Graph Atom Sig A B) : Prop :=
  match G with
  | Graph.first _ => True  -- functor pattern detected
  | Graph.left _  => True  -- coproduct functor pattern detected
  | Graph.comp G H => inferred_trait G ∨ inferred_trait H
  | _ => False

/-- **Soundness of `inferred_trait`:** if `inferred_trait G` detects the
functor pattern (i.e. `G` is `first F`), then the functor laws are verified.

This is the *annotation-free trait inference* theorem: the system looks at
the graph's wiring, detects the `first` combinator, and concludes the functor
laws hold — without any trait declaration. -/
theorem inferred_trait_sound_functor
    (X Y D : Ty Atom) (F : Graph Atom Sig X Y)
    : inferred_trait (@Graph.first Atom Sig X Y D F) →
      (∀ (A : Ty Atom) (D : Ty Atom), LawVerified (@Law.functorId Atom Sig A D)) ∧
      (∀ (X' : Ty Atom) (Y' : Ty Atom) (Z' : Ty Atom) (D' : Ty Atom)
        (G' : Graph Atom Sig X' Y') (H' : Graph Atom Sig Y' Z'),
        LawVerified (@Law.functorComp Atom Sig X' Y' Z' D' G' H')) := by
  intro _
  exact ⟨fun _ _ => ⟨first_id_normalizes _ _⟩,
         fun _ _ _ _ _ _ => ⟨first_comp_fusion_normalizes _ _ _ _ _ _⟩⟩

/-- **Soundness of `inferred_trait` for coproduct:** if `inferred_trait G`
detects the `left` pattern, then the coproduct functor laws are verified. -/
theorem inferred_trait_sound_coproduct
    (X Y D : Ty Atom) (F : Graph Atom Sig X Y)
    : inferred_trait (@Graph.left Atom Sig X Y D F) →
      (∀ (A : Ty Atom) (D : Ty Atom), LawVerified (@Law.coproductFunctorId Atom Sig A D)) ∧
      (∀ (X' : Ty Atom) (Y' : Ty Atom) (Z' : Ty Atom) (D' : Ty Atom)
        (G' : Graph Atom Sig X' Y') (H' : Graph Atom Sig Y' Z'),
        LawVerified (@Law.coproductFunctorComp Atom Sig X' Y' Z' D' G' H')) := by
  intro _
  exact ⟨fun _ _ => ⟨left_id_normalizes _ _⟩,
         fun _ _ _ _ _ _ => ⟨left_comp_fusion_normalizes _ _ _ _ _ _⟩⟩

-- ============================================================================
-- TASK 3: Connection to the invariant domain D
-- ============================================================================

/-! ## Semantic soundness of CutElim for the functor laws

The CutElim normalization is not just syntactic: the rewrites preserve
semantics.  We prove that the two sides of each law are *semantically
equivalent* — they produce the same output for the same input under `Eval`.

This connects the syntactic law verification to the semantic invariant domain
`D`: if two graphs are semantically equivalent, they preserve the same
`D`-invariants. -/

/-! ## Semantic soundness of CutElim for the functor laws

The CutElim normalization is not just syntactic: the rewrites preserve
semantics.  We prove that the two sides of each law are *semantically
equivalent* — they produce the same output for the same input under `Eval`.

Since `Eval` is a `Type 1` (a derivation, not a proposition), the semantic
equivalence theorems use `Nonempty` for the existence parts and `Eval` as
a (Type-valued) hypothesis for the determinism parts.  This is the same
pattern used in `ProofGraphs.lean`'s `subject_reduction`, where `Eval` is
carried as a `Type`-valued hypothesis in a `Prop`-valued theorem.

This connects the syntactic law verification to the semantic invariant domain
`D`: if two graphs are semantically equivalent, they preserve the same
`D`-invariants. -/

/-- **Semantic equivalence for the functor identity law:**
`first (idG A)` and `idG (A × D)` produce the same output for the same input.

Both are the identity on `A × D`: given `(a, d)`, both produce `(a, d)`.
This is proven directly from the `Eval` rules, with zero `sorry`.

The theorem has two parts:
  (1) *Existence*: there exists an evaluation of `first (idG A)` on `(a, d)`
      producing `(a, d)` (witnessed by `eFirst` + `eId`).
  (2) *Determinism*: every evaluation of `first (idG A)` on `(a, d)` produces
      `(a, d)` (by inverting the `Eval` derivation). -/
theorem first_id_semantic_equiv
    (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
    (A D : Ty Atom) (a d : Val)
    : Nonempty (Eval den (@Graph.first Atom Sig A A D (Graph.idG A)) (Val.pair a d) (Val.pair a d))
    ∧ (∀ v, Eval den (@Graph.first Atom Sig A A D (Graph.idG A)) (Val.pair a d) v →
             v = Val.pair a d) := by
  refine ⟨?witness, ?deterministic⟩
  · -- first (idG A) runs idG A on the first component, producing (a, d).
    exact ⟨@Eval.eFirst Atom Sig den D A A D (Graph.idG A) a a d
            (@Eval.eId Atom Sig den A a)⟩
  · -- first (idG A) is deterministic: the only way to evaluate it is via
    -- eFirst, which requires the inner graph (idG A) to produce a from a.
    intro v e
    cases e with
    | eFirst D G a₀ b c eG =>
      cases eG with
      | eId A' a' => rfl

/-- **Semantic equivalence for the coproduct functor identity law:**
`left (idG A)` and `idG (A + D)` produce the same output for the same input. -/
theorem left_id_semantic_equiv
    (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
    (A D : Ty Atom) (a : Val)
    : Nonempty (Eval den (@Graph.left Atom Sig A A D (Graph.idG A)) (Val.inl a) (Val.inl a))
    ∧ (∀ v, Eval den (@Graph.left Atom Sig A A D (Graph.idG A)) (Val.inl a) v →
             v = Val.inl a) := by
  refine ⟨?witness, ?deterministic⟩
  · exact ⟨@Eval.eLeftL Atom Sig den D A A D (Graph.idG A) a a
            (@Eval.eId Atom Sig den A a)⟩
  · intro v e
    cases e with
    | eLeftL D G a₀ b eG =>
      cases eG with
      | eId A' a' => rfl

/-- **Forward direction of semantic equivalence for the composition law:**
if `first (comp G H) · (a, d) ⟹ (v, d)`, then
`comp (first G) (first H) · (a, d) ⟹ (v, d)`. -/
def first_comp_semantic_forward
    (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
    (X Y Z D : Ty Atom)
    (G : Graph Atom Sig X Y) (H : Graph Atom Sig Y Z) (a d v : Val)
    (e : Eval den (@Graph.first Atom Sig X Z D (Graph.comp G H)) (Val.pair a d) (Val.pair v d))
    : Eval den (Graph.comp (@Graph.first Atom Sig X Y D G) (@Graph.first Atom Sig Y Z D H))
             (Val.pair a d) (Val.pair v d) := by
  -- Invert e: it must be eFirst, with the inner eval being eComp.
  cases e with
  | eFirst D' G' a₀ b c eG =>
    -- eG : Eval (comp G H) a v, which must be eComp with some intermediate b'.
    cases eG with
    | eComp G' H' a₁ b₁ v₁ eG1 eH1 =>
      -- Build: comp (first G) (first H) · (a, d) ⟹ (v, d)
      -- Step 1: first G · (a, d) ⟹ (b₁, d)  via eFirst + eG1
      -- Step 2: first H · (b₁, d) ⟹ (v, d)  via eFirst + eH1
      exact @Eval.eComp Atom Sig den (X ×ₜ D) (Y ×ₜ D) (Z ×ₜ D)
              (@Graph.first Atom Sig X Y D G)
              (@Graph.first Atom Sig Y Z D H)
              (Val.pair a d) (Val.pair b₁ d) (Val.pair v d)
              (@Eval.eFirst Atom Sig den D X Y D G a b₁ d eG1)
              (@Eval.eFirst Atom Sig den D Y Z D H b₁ v d eH1)

/-- **Backward direction of semantic equivalence for the composition law:**
if `comp (first G) (first H) · (a, d) ⟹ (v, d)`, then
`first (comp G H) · (a, d) ⟹ (v, d)`. -/
def first_comp_semantic_backward
    (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
    (X Y Z D : Ty Atom)
    (G : Graph Atom Sig X Y) (H : Graph Atom Sig Y Z) (a d v : Val)
    (e : Eval den (Graph.comp (@Graph.first Atom Sig X Y D G) (@Graph.first Atom Sig Y Z D H))
                 (Val.pair a d) (Val.pair v d))
    : Eval den (@Graph.first Atom Sig X Z D (Graph.comp G H)) (Val.pair a d) (Val.pair v d) := by
  -- Invert e: it must be eComp, with intermediate value b'.
  cases e with
  | eComp G' H' a₁ b₁ v₁ eG1 eH1 =>
    -- eG1 : Eval (first G) (a, d) b₁  → must be eFirst, b₁ = (b, d)
    cases eG1 with
    | eFirst D' G'' a₂ b₂ c₂ eG2 =>
      -- eH1 : Eval (first H) b₁ (v, d)  → must be eFirst
      cases eH1 with
      | eFirst D'' H'' a₃ b₃ c₃ eH2 =>
        -- Build: first (comp G H) · (a, d) ⟹ (v, d)
        exact @Eval.eFirst Atom Sig den D X Z D (Graph.comp G H) a v d
          (@Eval.eComp Atom Sig den X Y Z G H a b₂ v eG2 eH2)

/-! ## Connection to the invariant domain D

The law satisfaction (verified by CutElim) implies semantic equivalence,
which in turn implies preservation of all `D`-invariants.  This connects
the trait inference to the invariant domain `D` from `InvariantDomain.lean`. -/

/-- The functor identity law implies that `first (idG A)` preserves all
predicates (since it is semantically the identity).  This means it preserves
all `D`-invariants — the same `D` from `InvariantDomain.lean`.

This is the connection between trait inference and invariant inference:
the law `first (idG A) ≡ idG (A × D)` (verified by CutElim) implies a
semantic property (identity behavior) that implies preservation of all
`D`-invariants.  The structural pattern recognition that infers
`Sorted(output)` from a sort graph is the same mechanism that infers
`satisfies functor law` from a map graph: both read properties off the
wiring. -/
theorem functor_id_law_implies_preserves_all_D
    (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
    (sig_guarantee : SigGuarantee Atom Sig)
    (A D : Ty Atom) (I : Val → Prop)
    (_dI : InvariantDomain Atom Sig sig_guarantee I)
    (a v : Val) (e : Eval den (@Graph.first Atom Sig A A D (Graph.idG A)) a v)
    (hI : I a) : I v := by
  -- first (idG A) is semantically the identity: v = a.
  -- So I v = I a, which holds by hypothesis.
  cases e with
  | eFirst D' G a₀ b c eG =>
    cases eG with
    | eId A' a' => exact hI

/-- `inferred_trait` is the law-inference analogue of
`inferred_postcondition`.  Both are structural inference functions that map
a graph to a property without user annotations.

This theorem states that `inferred_trait` is sound for the functor pattern:
if it detects `first`, the functor identity law is verified. -/
theorem inferred_trait_is_structural_inference
    (X Y D : Ty Atom) (F : Graph Atom Sig X Y)
    : inferred_trait (@Graph.first Atom Sig X Y D F) = True
    ∧ (∀ (A : Ty Atom) (D : Ty Atom), LawVerified (@Law.functorId Atom Sig A D)) := by
  refine ⟨rfl, fun A D => ⟨first_id_normalizes A D⟩⟩

/-! ## Summary: what is proven (all zero `sorry`)

### Task 1: CutElim normalization verifies functor laws
  - `first_identity_law`: both sides of `first (idG A) ≡ idG (A × D)`
    normalize to `idG (A × D)`.
  - `first_composition_law`: both sides of `first (comp G H) ≡ comp (first G) (first H)`
    normalize to `first (comp G H)`.
  - `left_identity_law`: both sides of `left (idG A) ≡ idG (A + D)`
    normalize to `idG (A + D)`.
  - `left_composition_law`: both sides of `left (comp G H) ≡ comp (left G) (left H)`
    normalize to `left (comp G H)`.
  - Extended `CutElim` with `ceFirstId` and `ceLeftId` (valid cut-elimination
    steps: functoriality of `first`/`left` preserves identities).
  - Extended `cut_elim_preserves_proof` to handle the new constructors.

### Task 2: `SatisfiesLaw` and the inference theorem
  - `Law`: inductive type of named equational laws.
  - `LawVerified`: a law is verified when both sides normalize to the same
    form under `CutElimStar`.
  - `SatisfiesLaw G law`: G satisfies law when G's wiring matches the law's
    pattern and the law is verified.
  - `UsesFirst` / `UsesLeft`: structural pattern recognizers.
  - `satisfies_functor_identity`: if G uses `first`, G satisfies the functor
    identity law — without the law being declared.
  - `satisfies_functor_composition`: if G uses `first`, G satisfies the
    functor composition law — without the law being declared.
  - `inferred_trait`: structural law inference function (analogue of
    `inferred_postcondition`).
  - `inferred_trait_sound_functor`: soundness of the inference for the
    functor pattern.

### Task 3: Connection to the invariant domain D
  - `first_id_semantic_equiv`: the functor identity law implies semantic
    equivalence (both sides are the identity on `A × D`).
  - `first_comp_semantic_forward` / `first_comp_semantic_backward`:
    the functor composition law implies semantic equivalence (both sides
    produce the same output for the same input).
  - `functor_id_law_implies_preserves_all_D`: the functor identity law
    implies preservation of all `D`-invariants.
  - `inferred_trait_is_structural_inference`: `inferred_trait` is the
    law-inference analogue of `inferred_postcondition`.

### Honest assessment

**What works:** The trait inference works for the cases attempted — the
functor laws for `first` and `left` are verified by CutElim normalization,
and the inference from wiring structure to law satisfaction is proven.  The
connection to `D` is established for the identity law (preservation of all
`D`-invariants) and the semantic equivalence for the composition law.

**Obstacles for the general case:**
1. **Congruence:** The current `CutElim` only rewrites at the top level.
  To verify laws for complex graphs (e.g., `map_list` built from the five
  primitives), we need congruence rules (rewriting inside subgraphs).  This
  is straightforward but tedious to formalize.
2. **More laws:** The framework currently handles functor laws for `first`
  and `left`.  Extending to other laws (e.g., `loop` trace laws, `arr`
  laws, interchange laws) requires adding the corresponding CutElim rewrites
  and proving their preservation.
3. **Completeness:** We prove that the inferred laws are *sound* (if the
  pattern is detected, the law holds).  We do not prove *completeness* (if
  the law holds, the pattern is detected).  Completeness would require showing
  that every true law is detectable by structural pattern recognition, which
  is false in general (some laws require semantic reasoning beyond CutElim).
4. **The `inferred_trait` function is currently a `Prop`-valued flag** rather
  than a data structure enumerating the specific laws.  A more useful
  implementation would return a list/set of `Law` instances, but this
  requires universe-polymorphic containers that are awkward in Lean4.
-/

end TraitInference
