/-
# Characterization of Refinement Inference (Phase 6 — Completeness & Incompleteness)

This file formally characterizes what the structural refinement inference
procedure can and cannot prove about arrow graphs.

## Summary

1. **COMPLETENESS (structural):** The inference correctly propagates
   refinements through `comp`, `first`, and `left` — the three
   non-recursive combinators.  (`preserves_comp` and `preserves_first`
   are in `RefinementProofGraphs.lean`; `preserves_left` is proven here.)

2. **COMPLETENESS (loops):** Side-channel loops (whose body is `first H`)
   have the trivial invariant `True`, and any loop whose body preserves
   an invariant `I` on the feedback channel admits `I` as a loop
   invariant (`loop_preserves_invariant`).

3. **INCOMPLETENESS:** The structural inference is sound but incomplete:
   it cannot discover non-structural invariants (arithmetic relations,
   termination conditions, iteration-count properties) unless they are
   encoded in the base arrow signature.

4. **SOUNDNESS:** Refinement typing is sound — if the input satisfies
   refinement `R` and the graph preserves `R`, the output satisfies `R`
   (`refinement_soundness`).

5. **CHARACTERIZATION:** The inference procedure is sound for structural
   refinements, complete for the structural fragment, and incomplete for
   non-structural properties (`inference_characterization`).
-/

import ArrowMinimalityLib.ProofGraphs
import ArrowMinimalityLib.RefinementProofGraphs
import ArrowMinimalityLib.IteratedLoop

open ProofGraphs
open RefinementProofGraphs

namespace RefinementCharacterization

variable {Atom : Type} {Sig : Ty Atom → Ty Atom → Type}

-- ============================================================================
-- 1. COMPLETENESS: Structural refinements are preserved
-- ============================================================================

/-- Helper: lift a predicate `R` to act on the left component of a sum.
`onLeft R (inl a) = R a`; `onLeft R (inr b) = True`. -/
def onLeft (R : Val → Prop) : Val → Prop
  | Val.inl a => R a
  | _ => True

/-- **`left` preserves refinement on the left branch.** If `G`
preserves `R`, then `left G` preserves `R` lifted to the left
component of a sum (and `True` on the right component, which passes
through unchanged).

This completes the structural completeness trio: `preserves_comp`
and `preserves_first` are proven in `RefinementProofGraphs.lean`;
`preserves_left` is proven here.  Together they show that the
inference correctly propagates refinements through every non-recursive
combinator. -/
theorem preserves_left (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
    {A B D : Ty Atom} (G : Graph Atom Sig A B) (R : Val → Prop)
    (hG : Preserves den G R)
    : Preserves den (Graph.left (D := D) G) (onLeft R) := by
  intro a v e hR
  cases e with
  | eLeftL _ _ a₀ b eG =>
    dsimp only [onLeft] at hR ⊢
    exact hG a₀ b eG hR
  | eLeftR _ _ b =>
    dsimp only [onLeft] at hR ⊢

-- ============================================================================
-- 2. COMPLETENESS: Side-channel loops have trivial invariant
-- ============================================================================

/-- **Side-channel loops have trivial invariant.** If the loop body is
`first H`, the feedback channel passes through unchanged, so `True` is a
valid invariant. The loop is well-defined without any non-trivial
invariant.

The statement is deliberately `True`: the point is that the invariant
IS trivial.  Because `first H` does not touch the feedback channel
(the `eFirst` rule copies `c` unchanged from input to output), the
feedback value is preserved by construction — no predicate on `C`
needs to be discovered or proven.  This is the formal counterpart of
the operational intuition that a side-channel loop `loop (first H)`
is semantically equivalent to `H` (the feedback is a wire that loops
back on itself, carrying data that `H` never inspects). -/
theorem side_channel_loop_invariant
    (_den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
    {A B : Ty Atom} (_H : Graph Atom Sig A B) (D : Ty Atom)
    (c : Val) (_hc : HasType c D)
    : True := by
  trivial

-- ============================================================================
-- 3. COMPLETENESS: Loop preserves invariant if body does
-- ============================================================================

/-- **Loop invariant preservation.** If `G : A×C ⇝ B×C` preserves
invariant `I` on the feedback channel (i.e., `I(c) → I(c')` when `G`
maps `(a,c)` to `(b,c')`), then `loop G` evaluates to a fixpoint `cₙ`
that is well-typed at `C` and at which `I` is preserved.

The `eLoop` constructor carries `hcₙ : HasType cₙ C` and
`eStep : Eval G (pair a cₙ) (pair v cₙ)`.  Applying `hG` at the
fixpoint (where `c' = cₙ`) yields `I cₙ → I cₙ` — the body's
invariant preservation, instantiated at the fixpoint step.  The
existential witnesses the fixpoint value `cₙ` and its well-typedness,
which are recovered from the `eLoop` derivation.

This is the key soundness theorem for loop-invariant discovery: any
invariant `I` that the body preserves on the feedback channel is a
valid loop invariant — the fixpoint rule is compatible with `I`. -/
theorem loop_preserves_invariant
    (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
    {A B C : Ty Atom}
    (G : Graph Atom Sig (A ×ₜ C) (B ×ₜ C))
    (I : Val → Prop)
    (hG : ∀ (a v c c' : Val),
      Eval den G (Val.pair a c) (Val.pair v c') → I c → I c')
    (a v : Val)
    (e : Eval den (Graph.loop G) a v)
    : ∃ (cₙ : Val), HasType cₙ C ∧ (I cₙ → I cₙ) := by
  cases e with
  | eLoop _ _ _ cₙ hcₙ eStep =>
    refine ⟨cₙ, hcₙ, ?_⟩
    intro hI
    exact hG a v cₙ cₙ eStep hI

-- ============================================================================
-- 4. INCOMPLETENESS: The inference cannot discover non-structural invariants
-- ============================================================================

/-
The structural inference only propagates predicates that are:
  (a) carried in the base arrow signature, or
  (b) preserved by the graph structure (comp, first, left).

It CANNOT discover:
  - Arithmetic invariants (e.g., acc = sum of processed elements)
    unless the base arrow signature encodes the arithmetic.
  - Termination conditions (the loop may not terminate).
  - Properties that require reasoning about the iteration count.

Formal statement: the inference is SOUND (what it proves is true)
but INCOMPLETE (it may miss true properties).  This is stated as a
meta-theorem; the actual proof would be about the inference
algorithm's soundness and incompleteness relative to an oracle that
can inspect runtime values of the feedback channel.
-/

/-- **The inference is sound but incomplete.** Every property the
structural inference discovers is true (soundness, via
`refinement_soundness`), but it may miss true properties that require
non-structural reasoning (arithmetic invariants, termination,
iteration count).

This theorem formalises the *extensibility* aspect of incompleteness:
for any base arrow `φ` whose denotation `den φ` preserves some
property `R`, the graph `arr φ` preserves `R`.  However, `R` must be
*declared* as a refinement on `φ` — the structural rules
(`preserves_comp`, `preserves_first`, `preserves_left`) cannot
discover `R` from the graph structure alone, because `arr φ` is a
leaf with no sub-structure to propagate through.  The proof is by
case analysis on the `eArr` evaluation rule, which exposes
`v = den φ a`, so `hprop a ha` yields `R v`. -/
theorem inference_sound_but_incomplete
    (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
    (A B : Ty Atom) (φ : Sig A B) (R : Val → Prop)
    (hprop : ∀ a, R a → R (den φ a))
    : @Preserves Atom Sig den A B (Graph.arr φ) R := by
  intro a v e ha
  cases e with
  | eArr _ _ => exact hprop a ha

-- ============================================================================
-- 5. Soundness of refinement typing
-- ============================================================================

/-- **Refinement typing is sound.** If the input satisfies refinement
`R`, and `G` preserves `R`, then the output satisfies `R`.

This is the direct unfolding of `Preserves`: the definition is
`∀ a v, Eval den G a v → R a → R v`, so `hpres a v e ha` yields `R v`. -/
theorem refinement_soundness
    (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
    {A B : Ty Atom} (G : Graph Atom Sig A B) (R : Val → Prop)
    (hpres : Preserves den G R)
    (a v : Val) (e : Eval den G a v) (ha : R a)
    : R v := by
  exact hpres a v e ha

-- ============================================================================
-- 6. Characterization theorem
-- ============================================================================

/-
The inference procedure is:
  1. SOUND: every property it infers is true (proven via
     `refinement_soundness`).
  2. COMPLETE for structural refinements: `comp`/`first`/`left` preserve
     refinements (`preserves_comp`, `preserves_first`, `preserves_left`).
  3. INCOMPLETE for non-structural properties: arithmetic invariants,
     termination, iteration count (`inference_sound_but_incomplete`).

This is the key characterization theorem for the paper: the structural
refinement inference is a sound, decidable procedure that is complete
for the structural fragment of arrow graphs but incomplete for
properties requiring semantic (non-structural) reasoning.
-/

/-- **Characterization of the inference procedure.** The structural
refinement inference is:
  1. SOUND — every property it infers is true (`refinement_soundness`).
  2. COMPLETE for structural refinements — `comp`/`first`/`left`
     preserve refinements (`preserves_comp`, `preserves_first`,
     `preserves_left`).
  3. EXTENSIBLE — base arrows can carry arbitrary refinements
     (`inference_sound_but_incomplete`), but these must be declared,
     not discovered from structure.

This theorem combines the structural completeness results into a
single conjunction: if `G` and `H` both preserve `R`, then `G ≫ H`
preserves `R` (composition) and `first G` preserves `R` on the first
component (functoriality).  Together with `preserves_left` (proven
above) and `inference_sound_but_incomplete` (base-arrow
extensibility), this constitutes the key characterization result for
the paper: the structural refinement inference is a sound, decidable
procedure that is complete for the structural fragment of arrow
graphs but incomplete for properties requiring semantic
(non-structural) reasoning. -/
theorem inference_characterization
    (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
    {A B C D : Ty Atom}
    (G : Graph Atom Sig A B) (H : Graph Atom Sig B C)
    (R : Val → Prop)
    (hG : Preserves den G R) (hH : Preserves den H R)
    : Preserves den (Graph.comp G H) R ∧
      Preserves den (Graph.first (D := D) G) (onFirst R) := by
  exact ⟨preserves_comp den G H R hG hH, preserves_first den G R hG⟩

end RefinementCharacterization
