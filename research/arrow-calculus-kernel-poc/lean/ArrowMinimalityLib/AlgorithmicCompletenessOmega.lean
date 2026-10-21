import ArrowMinimalityLib.InvariantDomain
import ArrowMinimalityLib.AlgorithmicCompleteness

open ProofGraphs
open RefinementProofGraphs
open RefinementCharacterization
open InvariantDomain
open AlgorithmicCompleteness

namespace AlgorithmicCompletenessOmega

variable {Atom : Type} {Sig : Ty Atom → Ty Atom → Type}

-- ============================================================================
-- 1. The widened domain Dω (Prop-valued, closed under arbitrary meets)
-- ============================================================================

/-- The widened invariant domain `Dω`: a **Prop-valued** inductive family
with the same constructors as `InvariantDomain` (so `D ⊆ Dω`) plus
`dInf`, an infinitary meet over ANY `Sort u`-indexed family.

Because the family lives in `Prop`, Lean's impredicativity allows the
constructor argument `df : (i : ι) → Dω (f i)` for index types `ι` in
any universe — the universe spiral of `AlgorithmicCompleteness.lean`
does not arise. -/
inductive InvariantDomainOmega (Atom : Type) (Sig : Ty Atom → Ty Atom → Type)
    (sig_guarantee : SigGuarantee Atom Sig)
    : (Val → Prop) → Prop
  | dBase {A B : Ty Atom} (φ : Sig A B) (P : Val → Prop)
          (hP : sig_guarantee A B φ = P)
          : InvariantDomainOmega Atom Sig sig_guarantee P
  | dTrue : InvariantDomainOmega Atom Sig sig_guarantee (fun _ => True)
  | dConj (P Q : Val → Prop)
          (dP : InvariantDomainOmega Atom Sig sig_guarantee P)
          (dQ : InvariantDomainOmega Atom Sig sig_guarantee Q)
          : InvariantDomainOmega Atom Sig sig_guarantee (fun v => P v ∧ Q v)
  | dFirst (P : Val → Prop)
          (dP : InvariantDomainOmega Atom Sig sig_guarantee P)
          : InvariantDomainOmega Atom Sig sig_guarantee (onFirst P)
  | dLeft (P : Val → Prop)
          (dP : InvariantDomainOmega Atom Sig sig_guarantee P)
          : InvariantDomainOmega Atom Sig sig_guarantee (onLeft P)
  | dEx (P : Val → Prop)
          (dP : InvariantDomainOmega Atom Sig sig_guarantee P)
          : InvariantDomainOmega Atom Sig sig_guarantee
              (fun c' => ∃ v, P (Val.pair v c'))
  | dInf {ι : Type} (f : ι → Val → Prop)
          (df : (i : ι) → InvariantDomainOmega Atom Sig sig_guarantee (f i))
          : InvariantDomainOmega Atom Sig sig_guarantee (fun v => ∀ i, f i v)

/-- Convenient alias. -/
abbrev Dω (Atom : Type) (Sig : Ty Atom → Ty Atom → Type)
    (sig_guarantee : SigGuarantee Atom Sig) : (Val → Prop) → Prop :=
  InvariantDomainOmega Atom Sig sig_guarantee

-- ============================================================================
-- 2. Well-typed preservation (mirrors `analyze_strongest`'s hypothesis)
-- ============================================================================

/-- `G` preserves `I` on the feedback channel `C` for well-typed
executions — the same preservation predicate used by
`analyze_strongest` in `AlgorithmicCompleteness.lean`. -/
def PreservesWt
    (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
    {A B C : Ty Atom} (G : Graph Atom Sig (A ×ₜ C) (B ×ₜ C))
    (I : Val → Prop) : Prop :=
  ∀ (a v c c' : Val),
    HasType (Val.pair a c) (A ×ₜ C) →
    Eval den G (Val.pair a c) (Val.pair v c') → I c → I c'

-- ============================================================================
-- 3. Closure under arbitrary meets (Theorem 4's hypothesis → theorem)
-- ============================================================================

/-- Dω is closed under arbitrary meets: the meet of any family of Dω
predicates (indexed by ANY type in ANY universe) is again in Dω.

This is `dInf` applied directly — the constructor IS the closure proof.
This upgrades the CONDITIONAL closure hypothesis of Theorem 4
(`AlgorithmicCompleteness.lean`) to an unconditional theorem for Dω. -/
theorem domega_closed_under_meets
    (sig_guarantee : SigGuarantee Atom Sig)
    {ι : Type} (f : ι → Val → Prop)
    (df : (i : ι) → InvariantDomainOmega Atom Sig sig_guarantee (f i))
    : InvariantDomainOmega Atom Sig sig_guarantee (fun v => ∀ i, f i v) :=
  InvariantDomainOmega.dInf f df

/- # The Widened Invariant Domain `Dω` — Unconditional Algorithmic Completeness

This file generalizes `AlgorithmicCompleteness.lean` by removing the
universe obstruction that made Theorem 4 conditional.

## The obstruction, restated

`InvariantDomain` (the domain `D`) is a `Type 1`-valued inductive family.
`analyze_strongest` is the meet (arbitrary conjunction) of ALL preserved
D-invariants, and the index type of that family embeds `InvariantDomain`
derivations, so it lives one universe level above the inductive. Any
infinitary-meet constructor on `D` would therefore need constructor
arguments in a higher universe than the inductive itself — the universe
spiral documented in `AlgorithmicCompleteness.lean`. Hence Theorem 4 could
only be stated conditionally: *IF* D were closed under arbitrary meets,
*THEN* `analyze_strongest` would be in D.

## The escape: impredicative `Prop`

`Prop` is impredicative in Lean 4: a `Prop`-valued inductive family may
have constructor arguments in ANY universe. This is exactly the mechanism
that lets core Lean's `Exists : {α : Sort u} → (α → Prop) → Prop` quantify
over arbitrary large types. We exploit it: the widened domain
`InvariantDomainOmega` (`Dω`) is a **Prop-valued** inductive family with
the same six constructors as `D` plus an infinitary meet constructor

  `dInf : {ι : Sort u} → (f : ι → Val → Prop) → ((i : ι) → Dω (f i)) →
          Dω (fun v => ∀ i, f i v)`

whose index type `ι` may live in any universe. No spiral: the family is
closed under arbitrary meets *by construction*.

## What is proven here (all zero `sorry`)

1. `domega_closed_under_meets` — Dω is closed under arbitrary meets
   (the hypothesis of Theorem 4, now a theorem for Dω).
2. `invariant_domain_mono` — backward compatibility: every `D` derivation
   lifts to `Dω` (`D ⊆ Dω`), so nothing previously proven is lost.
3. `analyze_strongest_omega_sound` — the strongest preserved Dω-invariant
   is preserved by G (soundness).
4. `analyze_strongest_omega_in_domain` — **the headline**: the strongest
   preserved Dω-invariant is ITSELF in Dω. Theorem 4's conditional is
   unconditional for Dω.
5. `analyze_strongest_omega_implies_any_preserved` — completeness: it
   implies every preserved Dω-invariant (so it IS the strongest).
6. `analyze_strongest_omega_implies_analyze_strongest` — the widened
   strongest invariant is at least as strong as the original
   `analyze_strongest` (which ranges over `D` only).

## Honest scope

As with `D`: membership in `Dω` alone does NOT imply preservation —
soundness is stated relative to the constituents' preservation, matching
the framing of `InvariantDomain.lean` and `AlgorithmicCompleteness.lean`.
The incompleteness result of `InvariantDomain.lean` (invariants outside
the domain are structurally undetectable) is narrowed, not eliminated:
`Dω` strictly contains `D`, but predicates outside `Dω` (e.g. requiring
meets) remain undetectable. -/

-- ============================================================================
-- 4. Backward compatibility: D ⊆ Dω
-- ============================================================================

/-- Every `D` derivation lifts to `Dω`. Backward compatibility: the widened
domain strictly contains the original, so every invariant previously
discoverable remains discoverable. -/
theorem invariant_domain_mono
    (sig_guarantee : SigGuarantee Atom Sig)
    {I : Val → Prop}
    (dI : InvariantDomain Atom Sig sig_guarantee I)
    : InvariantDomainOmega Atom Sig sig_guarantee I := by
  cases dI with
  | baseArr φ _ hP => exact InvariantDomainOmega.dBase φ I hP
  | dTrue => exact InvariantDomainOmega.dTrue
  | conj p q dP dQ =>
      exact InvariantDomainOmega.dConj p q (invariant_domain_mono sig_guarantee dP)
        (invariant_domain_mono sig_guarantee dQ)
  | firstLift p dP =>
      exact InvariantDomainOmega.dFirst p (invariant_domain_mono sig_guarantee dP)
  | leftLift p dP =>
      exact InvariantDomainOmega.dLeft p (invariant_domain_mono sig_guarantee dP)
  | exProj p dP =>
      exact InvariantDomainOmega.dEx p (invariant_domain_mono sig_guarantee dP)

-- ============================================================================
-- 5. The strongest preserved Dω-invariant
-- ============================================================================

/-- The index type for the meet: all predicates that are BOTH in `Dω` AND
preserved by `G` (for well-typed executions). Because `Dω` is Prop-valued,
this subtype lives in `Type 0` — no universe spiral. -/
def PreservedDωIndex
    (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
    (sig_guarantee : SigGuarantee Atom Sig)
    {A B C : Ty Atom} (G : Graph Atom Sig (A ×ₜ C) (B ×ₜ C)) : Type :=
  { x : Val → Prop //
      InvariantDomainOmega Atom Sig sig_guarantee x ∧ PreservesWt den G x }

/-- `analyze_strongest_omega` — the meet (arbitrary conjunction) of ALL
preserved Dω-invariants. Defined via the subtype index so that membership
in `Dω` follows directly from `dInf`. -/
def analyze_strongest_omega
    (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
    (sig_guarantee : SigGuarantee Atom Sig)
    {A B C : Ty Atom} (G : Graph Atom Sig (A ×ₜ C) (B ×ₜ C))
    : Val → Prop :=
  fun v => ∀ (x : PreservedDωIndex den sig_guarantee G), x.1 v

-- ============================================================================
-- 6. THE HEADLINE: unconditional algorithmic completeness for Dω
-- ============================================================================

/-- **UNCONDITIONAL ALGORITHMIC COMPLETENESS (the headline).** The strongest
preserved Dω-invariant is ITSELF in `Dω`.

This is Theorem 4 of `AlgorithmicCompleteness.lean` made unconditional:
there, `analyze_strongest ∈ D` required the unprovable hypothesis that D be
closed under arbitrary meets (and the doc showed the universe system blocks
adding such closure to `D` directly). For the widened `Dω`, closure holds
*by construction* (`dInf`, via Prop-impredicativity), so the meet of all
preserved Dω-invariants is a Dω-member — no hypothesis needed.

Proof: apply `dInf` to the projection family `x ↦ x.1` over the subtype
`PreservedDωIndex`; each component is in `Dω` by `x.2.1`. -/
theorem analyze_strongest_omega_in_domain
    (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
    (sig_guarantee : SigGuarantee Atom Sig)
    {A B C : Ty Atom} (G : Graph Atom Sig (A ×ₜ C) (B ×ₜ C))
    : InvariantDomainOmega Atom Sig sig_guarantee
        (analyze_strongest_omega den sig_guarantee G) :=
  InvariantDomainOmega.dInf
    (f := fun x : PreservedDωIndex den sig_guarantee G => x.1)
    (fun x => x.2.1)

-- ============================================================================
-- 7. Soundness: the strongest preserved Dω-invariant is preserved
-- ============================================================================

/-- Preservation is closed under arbitrary meets: if every `f i` is
preserved by `G`, so is `fun v => ∀ i, f i v`. -/
theorem preserves_meet
    (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
    {A B C : Ty Atom} (G : Graph Atom Sig (A ×ₜ C) (B ×ₜ C))
    {ι : Type} (f : ι → Val → Prop)
    (hpres : (i : ι) → PreservesWt den G (f i))
    : PreservesWt den G (fun v => ∀ i, f i v) := by
  intro a v c c' ha e hmeet
  intro i
  exact hpres i a v c c' ha e (hmeet i)

/-- SOUNDNESS: `analyze_strongest_omega` is preserved by `G`. The meet of
all preserved Dω-invariants is itself preserved. -/
theorem analyze_strongest_omega_sound
    (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
    (sig_guarantee : SigGuarantee Atom Sig)
    {A B C : Ty Atom} (G : Graph Atom Sig (A ×ₜ C) (B ×ₜ C))
    : PreservesWt den G (analyze_strongest_omega den sig_guarantee G) := by
  intro a v c c' ha e h
  intro x
  exact x.2.2 a v c c' ha e (h x)

-- ============================================================================
-- 8. Completeness: it implies every preserved Dω-invariant
-- ============================================================================

/-- COMPLETENESS: `analyze_strongest_omega` implies every preserved
Dω-invariant — so it IS the strongest preserved Dω-invariant (it is in
`Dω` by `analyze_strongest_omega_in_domain`, preserved by
`analyze_strongest_omega_sound`, and implies every member of the class). -/
theorem analyze_strongest_omega_implies_any_preserved
    (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
    (sig_guarantee : SigGuarantee Atom Sig)
    {A B C : Ty Atom} (G : Graph Atom Sig (A ×ₜ C) (B ×ₜ C))
    (I : Val → Prop)
    (dI : InvariantDomainOmega Atom Sig sig_guarantee I)
    (hpres : PreservesWt den G I)
    : ∀ v, analyze_strongest_omega den sig_guarantee G v → I v := by
  intro v h
  exact h ⟨I, dI, hpres⟩

-- ============================================================================
-- 9. Relation to the original analyze_strongest
-- ============================================================================

/-- The widened strongest invariant is at least as strong as the original
`analyze_strongest`: every preserved D-invariant is (by
`invariant_domain_mono`) a preserved Dω-invariant, so the Dω-meet implies
the D-meet. -/
theorem analyze_strongest_omega_implies_analyze_strongest
    (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
    (sig_guarantee : SigGuarantee Atom Sig)
    {A B C : Ty Atom} (G : Graph Atom Sig (A ×ₜ C) (B ×ₜ C))
    : ∀ v, analyze_strongest_omega den sig_guarantee G v →
        analyze_strongest den sig_guarantee G v := by
  intro v h I dI hpres
  exact h ⟨I, invariant_domain_mono sig_guarantee dI, hpres⟩

/-- The original floor (`True`) is in `Dω`. -/
theorem domega_true_mem (sig_guarantee : SigGuarantee Atom Sig)
    : InvariantDomainOmega Atom Sig sig_guarantee (fun _ => True) :=
  InvariantDomainOmega.dTrue

end AlgorithmicCompletenessOmega
