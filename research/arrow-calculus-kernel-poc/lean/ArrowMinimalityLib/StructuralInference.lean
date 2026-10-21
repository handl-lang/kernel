/-
# Structural Inference: Soundness of the Actual Algorithm (Phase 8)

## What this file proves

The `InvariantDomain.lean` file defines the *sound floor* (`analyze_spec = True`)
and proves it sound.  That is trivially correct but does not connect to the
actual Rust inference algorithm, which does **structural candidate generation
+ semantic verification**: for each graph combinator it computes a
postcondition from the graph's structure and the base-arrow signatures, then
verifies that postcondition holds for every execution.

This file formalizes that actual algorithm and proves it sound:

1. **`inferred_postcondition`** — the structural candidate.  For each graph
   combinator, compute a postcondition `P` on the output value:
   - `id`         → `True`  (no constraint)
   - `arr(φ)`     → `sig_guarantee φ`  (the base arrow's output contract)
   - `comp(G, H)` → `inferred_postcondition H`  (propagate through H)
   - `first(G)`   → `True`  (conservative: side channel unconstrained)
   - `left(G)`    → `True`  (conservative)
   - `loop(G)`    → `True`  (conservative: floor for feedback)

2. **`inferred_postcondition_sound_full`** — the SOUNDNESS theorem: for every
   well-typed execution `G · a ⟹ v` (with `a : A`, `⊢ G : A ⇝ B`, signature
   sound), the inferred postcondition holds of `v`.  Proven by induction on
   `Eval`, using `subject_reduction` for the `comp` case and `sig_sound` for
   the `arr` case.  **Zero `sorry`.**

3. **`inferred_postcondition_in_domain`** — the inferred postcondition is
   always in the invariant domain `D`.  **Zero `sorry`.**

4. **`floor_does_not_imply_inferred`** — the structural inference is strictly
   stronger than the sound floor.  **Zero `sorry`.**

## Relationship to the Rust implementation

The Rust `infer_r` function mirrors `inferred_postcondition`:
- `arr(φ)` → `sig_guarantee(φ)`
- `comp(G, H)` → propagate through `H`
- `first`/`left`/`loop` → conservative (`True`)

The Rust implementation additionally does loop-invariant discovery via
fixpoint iteration (structural pattern recognition + Z3 verification), which
is NOT formalized here.  The theorem below proves the *compositional
postcondition propagation* part — the core of the inference — is sound.
-/

import ArrowMinimalityLib.ProofGraphs
import ArrowMinimalityLib.RefinementProofGraphs
import ArrowMinimalityLib.InvariantDomain

open ProofGraphs
open RefinementProofGraphs
open InvariantDomain

namespace StructuralInference

variable {Atom : Type} {Sig : Ty Atom → Ty Atom → Type}

-- ============================================================================
-- 1. The structural candidate: inferred postcondition
-- ============================================================================

/-- The inferred postcondition of a graph: a predicate on the output value
that holds for every execution of the graph.

This mirrors the Rust `infer_r` function:
- `id`         → `True`  (identity: no constraint beyond input = output)
- `arr(φ)`     → `sig_guarantee φ`  (the base arrow's output contract)
- `comp(G, H)` → `inferred_postcondition H`  (propagate through H)
- `first(G)`   → `True`  (conservative: side channel is unconstrained)
- `left(G)`    → `True`  (conservative)
- `loop(G)`    → `True`  (conservative: floor for feedback channel)

For `comp(G, H)`, the postcondition of the composition is the postcondition
of `H`: if `H` guarantees `Q` of its output, then `comp(G, H)` guarantees
`Q` of its output (since `H` produces the final output).

This is NOT the sound floor: for `arr(φ)`, it produces `sig_guarantee φ`,
which is non-trivial.  It is the actual structural inference algorithm. -/
def inferred_postcondition
    (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
    (sig_guarantee : SigGuarantee Atom Sig)
    {A B : Ty Atom} (G : Graph Atom Sig A B) : (Val → Prop) :=
  match G with
  | Graph.idG _    => fun _ => True
  | Graph.arr φ    => sig_guarantee _ _ φ
  | Graph.comp _ H => inferred_postcondition den sig_guarantee H
  | Graph.first _  => fun _ => True
  | Graph.left _   => fun _ => True
  | Graph.loop _   => fun _ => True

-- ============================================================================
-- 2. Soundness: the inferred postcondition holds for every well-typed execution
-- ============================================================================

/-- **Full soundness of structural inference with subject reduction.**
For every well-typed execution (input well-typed, graph well-typed, signature
sound), the inferred postcondition holds of the output.

This is the complete soundness theorem: it connects the structural inference
algorithm to the type system via subject reduction, ensuring that the
`arr` case has the well-typedness needed for the signature guarantee, and
the `comp` case has the well-typedness of the intermediate value.

Proof by induction on the execution relation `Eval`:
- `eId`: `True` holds trivially.
- `eComp`: the postcondition of `comp(G, H)` is the postcondition of `H`;
  subject reduction on `G` gives `HasType b Y`, which feeds the IH for `H`.
- `eArr`: the postcondition is `sig_guarantee φ`; `sig_sound` gives it
  when the input is well-typed.
- `eFirst`/`eLeft`/`eLoop`: the postcondition is `True` (conservative). -/
theorem inferred_postcondition_sound_full
    (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
    (sig_guarantee : SigGuarantee Atom Sig)
    (sig_sound : ∀ {A B : Ty Atom} (φ : Sig A B) (a : Val),
      HasType a A → sig_guarantee A B φ (den φ a))
    (sig_type_sound : @ProofGraphs.SigSound Atom Sig den)
    : ∀ {A B : Ty Atom} (G : Graph Atom Sig A B) (dG : TyOf G) (a v : Val),
      HasType a A → Eval den G a v →
      inferred_postcondition den sig_guarantee G v := by
  intro A B G dG a v ha e
  exact @Eval.rec Atom Sig den
    (fun {A B} G a v _ => HasType a A → TyOf G → inferred_postcondition den sig_guarantee G v)
    -- eId
    (fun A a ha _ => by trivial)
    -- eComp
    (fun G H a b v eG eH ihG ihH ha dG => by
      cases dG with | compT G H dG' dH' =>
        have hb := @ProofGraphs.subject_reduction Atom Sig den sig_type_sound _ _ _ _ _ dG' eG ha
        exact ihH hb dH')
    -- eFirst
    (fun D G a b c eG ihG ha dG => by trivial)
    -- eLeftL
    (fun D G a b eG ihG ha dG => by trivial)
    -- eLeftR
    (fun D G b ha dG => by trivial)
    -- eLoop
    (fun G a v cₙ hcₙ eStep ih ha dG => by trivial)
    -- eArr
    (fun φ a ha _ => sig_sound φ a ha)
    A B G a v e ha dG

-- ============================================================================
-- 3. The inferred postcondition is in the invariant domain D
-- ============================================================================

/-- The inferred postcondition is always a member of the invariant domain `D`.
This connects the structural inference to the domain formalized in
`InvariantDomain.lean`.

Proof by induction on the graph:
- `idG`: `True` ∈ D via `dTrue`.
- `arr φ`: `sig_guarantee φ` ∈ D via `baseArr`.
- `comp G H`: `inferred_postcondition H` ∈ D by IH.
- `first`/`left`/`loop`: `True` ∈ D via `dTrue`. -/
noncomputable def inferred_postcondition_in_domain
    (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
    (sig_guarantee : SigGuarantee Atom Sig)
    : ∀ {A B : Ty Atom} (G : Graph Atom Sig A B),
      InvariantDomain Atom Sig sig_guarantee
        (inferred_postcondition den sig_guarantee G) := by
  intro A B G
  induction G with
  | idG _ => exact InvariantDomain.dTrue
  | arr φ =>
      have h : inferred_postcondition den sig_guarantee (Graph.arr φ) = sig_guarantee _ _ φ := by rfl
      rw [h]
      exact InvariantDomain.baseArr φ (sig_guarantee _ _ φ) (by rfl)
  | comp G H ihG ihH => exact ihH
  | first G ihG => exact InvariantDomain.dTrue
  | left G ihG => exact InvariantDomain.dTrue
  | loop G ihG => exact InvariantDomain.dTrue

-- ============================================================================
-- 4. The inferred postcondition is stronger than the sound floor
-- ============================================================================

/-- The inferred postcondition is at least as strong as the sound floor (`True`).
This is trivially true (everything implies True) but documents the relationship. -/
theorem inferred_postcondition_implies_floor
    (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
    (sig_guarantee : SigGuarantee Atom Sig)
    {A B : Ty Atom} (G : Graph Atom Sig A B)
    : ∀ v, inferred_postcondition den sig_guarantee G v → True := by
  intro v _
  trivial

/-- The sound floor does NOT imply the inferred postcondition (in general).
For `arr(φ)`, the inferred postcondition is `sig_guarantee φ`, which is
stronger than `True`.  So the structural inference is strictly better than
the sound floor. -/
theorem floor_does_not_imply_inferred
    (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
    (sig_guarantee : SigGuarantee Atom Sig)
    {A B : Ty Atom} (φ : Sig A B)
    (hnontrivial : ∃ v, ¬ sig_guarantee A B φ v)
    : ¬ (∀ v, True → sig_guarantee A B φ v) := by
  obtain ⟨v, hv⟩ := hnontrivial
  intro h
  exact hv (h v trivial)

-- ============================================================================
-- 5. Summary: what is proven
-- ============================================================================

/-
## Summary of theorems (all zero `sorry`)

1. **`inferred_postcondition_sound_full`** — the actual structural inference
   algorithm is sound: every inferred postcondition holds for every
   well-typed execution.

2. **`inferred_postcondition_in_domain`** — the inferred postcondition is
   always in the invariant domain `D`.

3. **`floor_does_not_imply_inferred`** — the structural inference is strictly
   stronger than the sound floor (for `arr(φ)`, it produces `sig_guarantee φ`,
   not `True`).

These three theorems together establish:
- The structural inference algorithm (as formalized) is SOUND.
- Its results are in the invariant domain D.
- It is strictly stronger than the trivial sound floor.

What is NOT proven here (and is honestly acknowledged):
- The loop invariant discovery (fixpoint iteration) — only the floor is
  formalized for `loop`.
- Algorithmic completeness — the inference finds *a* sound postcondition,
  not necessarily the *strongest* one.
- The Z3 verification step — this is an implementation detail of the Rust
  prototype, not formalized in Lean4.
-/

end StructuralInference
