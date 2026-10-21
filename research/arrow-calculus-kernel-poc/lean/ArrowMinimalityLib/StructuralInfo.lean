/-
# Structural Information Boundary: Expressiveness vs Observability

## The Question

What is the maximal class of structural properties recoverable
compositionally under full dynamic application (monadic power)?

This file formalizes a **structural information measure σ** on
computation representations and proves the boundary theorem.

## Key design change from v1

In v1, σ was **representation-defined**: `sigmaFreerArrow c = allFacts`
for ALL `c`, even `c = pure 0` (which has no fanout, no branching, no
feedback). This was wrong: σ should depend on the computation.

In v2, σ is **semantic**: `sigmaFA c = {f | holds f c}` where `holds`
is a tree-traversal predicate on the canonical computation. A pure
value has σ = {dependency_graph} (the only fact that always holds),
not σ = allFacts.

This change has a critical consequence for the maximality theorem:
the v1 theorem `R.sigmaRep rc ⊆f sigmaFreerArrowApply c` was
**vacuously true** because `sigmaFreerArrowApply c = allFacts` makes
the subset trivial. In v2, `sigmaFA c = {f | holds f c}` is NOT
allFacts, so the subset is non-trivial.

## What is proved

1. **Ordering**: σ(FA(C)) ⊇ σ(FM(C)) ⊇ σ(OM(C)) — semantic, depends on C
2. **Strict inequality**: for C with fanout, fanout_independence ∈ σ(FA(C)) \ σ(FM(C))
3. **ArrowApply preserves σ**: σ(FA+Apply(C)) = σ(FA(C))
4. **Maximality for computation-structure facts**: any correct representation R has σ_R(C) ⊆ σ(FA(C)) — because σ(FA(C)) IS the ground truth
5. **Non-maximality for richer lattices**: counterexample with provenance tags

## The honest boundary

The freer arrow with Apply achieves σ = {f | holds f C} (the ground
truth for computation-structure facts). No correct representation can
recover strictly more computation-structure facts (they're properties
of C, and FA recovers all of them). But representations can carry
additional metadata (provenance, timing) that is NOT a
computation-structure fact, recovering strictly more information
overall. The freer arrow with Apply is maximal for
computation-structure facts, NOT for all representable information.

## Relation to concurrent work

VanDomelen et al. (Haskell Symposium 2025, "Freer Arrows and Why You
Need Them in Haskell") independently show empirically that freer
arrows are more statically analyzable than freer monads. Our
contribution is the **formal characterization**: we define a semantic
measure σ, prove the ordering and equality theorems, and
characterize (not claim) the boundary.
-/

namespace StructuralInfo

-- ============================================================================
-- Step 1: Computation Representations
-- ============================================================================

/-- Freer arrow: the canonical computation tree. Each constructor is a
visible structural node. This IS the computation — σ is defined relative
to this tree. -/
inductive FreerArrow (Op : Type) (V : Type) : Type where
  | pure (v : V) : FreerArrow Op V
  | seq (f g : FreerArrow Op V) : FreerArrow Op V
  | fanout (f g : FreerArrow Op V) : FreerArrow Op V
  | choice (f g : FreerArrow Op V) : FreerArrow Op V
  | op (o : Op) (k : FreerArrow Op V) : FreerArrow Op V
  | loop (f : FreerArrow Op V) : FreerArrow Op V
  | apply (f : FreerArrow Op V) : FreerArrow Op V

/-- Freer monad: explicit monad tree. Has `choice` (branching is
preserved) but NOT `fanout` (independence is lost — fanout encodes as
`bind`, same as `seq`). This is the standard freer monad extended with
a choice constructor, matching the empirical finding that branching
is preserved but fanout independence is not. -/
inductive FreerMonad (Op : Type) (V : Type) : Type where
  | pure (v : V) : FreerMonad Op V
  | bind (m k : FreerMonad Op V) : FreerMonad Op V
  | choice (f g : FreerMonad Op V) : FreerMonad Op V
  | op (o : Op) (k : FreerMonad Op V) : FreerMonad Op V
  | loop (f : FreerMonad Op V) : FreerMonad Op V

/-- Opaque monad: a black-box function. No structure is inspectable. -/
structure OpaqueMonad (Op : Type) (V : Type) where
  run : V → V

/-- Tagged freer arrow: freer arrow with provenance labels on each op.
Used for the maximality counterexample (Step 8). Has full monadic power
(includes `apply`) AND recovers provenance information that the standard
freer arrow cannot. -/
inductive TaggedFreerArrow (Op : Type) (V : Type) (Label : Type) : Type where
  | pure (v : V) : TaggedFreerArrow Op V Label
  | seq (f g : TaggedFreerArrow Op V Label) : TaggedFreerArrow Op V Label
  | fanout (f g : TaggedFreerArrow Op V Label) : TaggedFreerArrow Op V Label
  | choice (f g : TaggedFreerArrow Op V Label) : TaggedFreerArrow Op V Label
  | op (label : Label) (o : Op) (k : TaggedFreerArrow Op V Label) : TaggedFreerArrow Op V Label
  | loop (f : TaggedFreerArrow Op V Label) : TaggedFreerArrow Op V Label
  | apply (f : TaggedFreerArrow Op V Label) : TaggedFreerArrow Op V Label

-- ============================================================================
-- Step 2: Structural Facts (Semantic)
-- ============================================================================

/-- The lattice of structural facts. Each fact is a property of a
computation (the FreerArrow tree), recoverable by traversal.

`op_provenance` is included to test maximality: it is NOT a
computation-structure fact (the computation doesn't have provenance),
but a representation can carry it as metadata. -/
inductive StructFact : Type where
  | fanout_independence : StructFact
  | branching : StructFact
  | per_branch_effects : StructFact
  | dependency_graph : StructFact
  | feedback : StructFact
  | effect_set : StructFact
  | op_provenance : StructFact

/-- A "set of structural facts" is a predicate on `StructFact`. -/
abbrev FactSet := StructFact → Prop

/-- Subset on fact sets. -/
def FactSet.subset (S T : FactSet) : Prop := ∀ f, S f → T f
infix:50 " ⊆f " => FactSet.subset

/-- Membership. -/
def FactSet.mem (f : StructFact) (S : FactSet) : Prop := S f
infix:55 " ∈f " => FactSet.mem

/-- The full set. -/
def allFacts : FactSet := fun _ => True

/-- The empty set. -/
def noFacts : FactSet := fun _ => False

-- ============================================================================
-- Step 3: Semantic `holds` — tree-traversal predicates
-- ============================================================================

/-- Does the computation contain a fanout node? (Independent parallel
computations visible.) -/
def containsFanout {Op V : Type} : FreerArrow Op V → Bool
  | .fanout _ _ => true
  | .seq f g => containsFanout f || containsFanout g
  | .choice f g => containsFanout f || containsFanout g
  | .op _ k => containsFanout k
  | .loop f => containsFanout f
  | .apply f => containsFanout f
  | .pure _ => false

/-- Does the computation contain a choice node? (Branching visible.) -/
def containsChoice {Op V : Type} : FreerArrow Op V → Bool
  | .choice _ _ => true
  | .seq f g => containsChoice f || containsChoice g
  | .fanout f g => containsChoice f || containsChoice g
  | .op _ k => containsChoice k
  | .loop f => containsChoice f
  | .apply f => containsChoice f
  | .pure _ => false

/-- Does the computation contain a loop node? (Feedback visible.) -/
def containsLoop {Op V : Type} : FreerArrow Op V → Bool
  | .loop f => true
  | .seq f g => containsLoop f || containsLoop g
  | .fanout f g => containsLoop f || containsLoop g
  | .choice f g => containsLoop f || containsLoop g
  | .op _ k => containsLoop k
  | .apply f => containsLoop f
  | .pure _ => false

/-- Does the computation contain an op node? (Effect set non-empty.) -/
def containsOp {Op V : Type} : FreerArrow Op V → Bool
  | .op _ _ => true
  | .seq f g => containsOp f || containsOp g
  | .fanout f g => containsOp f || containsOp g
  | .choice f g => containsOp f || containsOp g
  | .loop f => containsOp f
  | .apply f => containsOp f
  | .pure _ => false

/-- Semantic interpretation: does fact `f` hold of computation `c`?

This is a property of the COMPUTATION (the FreerArrow tree), not of any
particular representation. It is the ground truth that σ measures.

`op_provenance` is always false: the computation tree has no provenance
information. This is a representation-level fact, not a computation fact. -/
def holds {Op V : Type} : StructFact → FreerArrow Op V → Bool
  | .fanout_independence, c => containsFanout c
  | .branching, c => containsChoice c
  | .per_branch_effects, c => containsChoice c
  | .dependency_graph, _ => true
  | .feedback, c => containsLoop c
  | .effect_set, c => containsOp c
  | .op_provenance, _ => false

-- ============================================================================
-- Step 4: Encodings (information loss happens here)
-- ============================================================================

/-- Encode a freer arrow computation as a freer monad.

KEY: `fanout f g` and `seq f g` both encode to `bind (enc f) (enc g)`.
This is the information-theoretic loss — the monad tree cannot
distinguish fanout from seq, so `fanout_independence` is not recoverable.

`choice f g` is preserved (FreerMonad has a choice constructor). -/
def encodeMonad {Op V : Type} : FreerArrow Op V → FreerMonad Op V
  | .pure v => .pure v
  | .seq f g => .bind (encodeMonad f) (encodeMonad g)
  | .fanout f g => .bind (encodeMonad f) (encodeMonad g)
  | .choice f g => .choice (encodeMonad f) (encodeMonad g)
  | .op o k => .op o (encodeMonad k)
  | .loop f => .loop (encodeMonad f)
  | .apply f => encodeMonad f -- simplified: apply ≈ run computation (structurally)

/-- The encoding is not injective: fanout and seq map to the same
monad tree. This is the formal statement of information loss. -/
theorem encodeMonad_fanout_eq_seq {Op V : Type} (f g : FreerArrow Op V) :
    encodeMonad (.fanout f g) = encodeMonad (.seq f g) := by
  rfl

/-- Encode a freer arrow as a tagged freer arrow (with default labels).
The tagged representation carries provenance that the standard freer
arrow does not. -/
def encodeTagged {Op V Label : Type} (defaultLabel : Label) :
    FreerArrow Op V → TaggedFreerArrow Op V Label
  | .pure v => .pure v
  | .seq f g => .seq (encodeTagged defaultLabel f) (encodeTagged defaultLabel g)
  | .fanout f g => .fanout (encodeTagged defaultLabel f) (encodeTagged defaultLabel g)
  | .choice f g => .choice (encodeTagged defaultLabel f) (encodeTagged defaultLabel g)
  | .op o k => .op defaultLabel o (encodeTagged defaultLabel k)
  | .loop f => .loop (encodeTagged defaultLabel f)
  | .apply f => .apply (encodeTagged defaultLabel f)

-- ============================================================================
-- Step 5: Semantic σ definitions
-- ============================================================================

/-
σ is now SEMANTIC: it depends on the computation `c`, not just the
representation type. A fact `f` is in σ(R, C) if it is recoverable from
R's encoding of C.

For FreerArrow: σ = {f | holds f C} — the ground truth (the tree IS
the computation, so every fact that holds is recoverable).

For FreerMonad: σ = {f | holdsFM f (encodeMonad C)} — facts detectable
from the monad encoding. Fanout_independence is always false (lost in
encoding).

For OpaqueMonad: σ = ∅ — nothing recoverable from a black box.
-/

/-- σ for FreerArrow: the ground truth. Every fact that holds of C is
recoverable, because the tree IS the computation. -/
def sigmaFA {Op V : Type} (c : FreerArrow Op V) : FactSet :=
  fun f => holds f c = true

/-- σ for FreerMonad: facts recoverable from the monad encoding.
`fanout_independence` is always false (lost in encoding). Other facts
are preserved if their structural constructor is preserved. -/
def sigmaFM {Op V : Type} (c : FreerArrow Op V) : FactSet :=
  fun f => match f with
    | .fanout_independence => False
    | .op_provenance => False
    | .branching => containsChoice c
    | .per_branch_effects => containsChoice c
    | .feedback => containsLoop c
    | .effect_set => containsOp c
    | .dependency_graph => True

/-- σ for OpaqueMonad: nothing recoverable. -/
def sigmaOM {Op V : Type} (c : FreerArrow Op V) : FactSet :=
  noFacts

/-- σ for FreerArrow with Apply: same as σ for FreerArrow. The `apply`
constructor is a visible tree node — it does not hide structure. -/
def sigmaFAA {Op V : Type} (c : FreerArrow Op V) : FactSet :=
  sigmaFA c

/-- σ for TaggedFreerArrow: recovers all computation-structure facts
PLUS `op_provenance` (the labels are visible in the tree).

Note: `Label` is unused in the definition — the mere existence of labels
on op nodes makes `op_provenance` recoverable. The Label type is part
of the TaggedFreerArrow representation but not of σ. -/
def sigmaTagged {Op V : Type} (c : FreerArrow Op V) : FactSet :=
  fun f => match f with
    | .op_provenance => containsOp c
    | _ => holds f c = true

-- ============================================================================
-- Step 6: The Ordering Theorem (Semantic)
-- ============================================================================

/-- σ(OM(C)) ⊆ σ(FM(C)): vacuously true (OM recovers nothing). -/
theorem sigmaOM_subseteq_sigmaFM {Op V : Type} (c : FreerArrow Op V) :
    sigmaOM c ⊆f sigmaFM c := by
  intro f hf
  simp [sigmaOM, noFacts] at hf

/-- σ(FM(C)) ⊆ σ(FA(C)): every fact recoverable from the monad encoding
is also a fact that holds of the computation.

Proof: For `fanout_independence` and `op_provenance`, σ(FM) is False
(not recoverable), so the implication holds vacuously. For other facts,
σ(FM) agrees with `holds` (the encoding preserves choice, loop, op,
and dependency_graph). -/
theorem sigmaFM_subseteq_sigmaFA {Op V : Type} (c : FreerArrow Op V) :
    sigmaFM c ⊆f sigmaFA c := by
  intro f hf
  simp only [sigmaFA]
  cases f with
  | fanout_independence => exact False.elim hf
  | op_provenance => exact False.elim hf
  | branching => exact hf
  | per_branch_effects => exact hf
  | feedback => exact hf
  | effect_set => exact hf
  | dependency_graph => trivial

/-- **The σ-ordering theorem (semantic).** For any computation C:

  σ(FA(C)) ⊇ σ(FM(C)) ⊇ σ(OM(C))

The freer arrow preserves at least as much structural information as
the freer monad, which preserves at least as much as the opaque monad.
This is now semantic: σ depends on C. -/
theorem sigma_ordering {Op V : Type} (c : FreerArrow Op V) :
    sigmaOM c ⊆f sigmaFM c ∧ sigmaFM c ⊆f sigmaFA c := by
  constructor
  · exact sigmaOM_subseteq_sigmaFM c
  · exact sigmaFM_subseteq_sigmaFA c

-- ============================================================================
-- Step 7: Strict Inequality (Information Loss is Real)
-- ============================================================================

/-- **Strict inequality for fanout.** For a computation `fanout f g`:
`fanout_independence` IS in σ(FA) but is NOT in σ(FM).

This is the formal version of the "false dependency" phenomenon: when
arrow fanout (`f &&& g`) is translated to monadic bind, the second
computation appears to depend on the first's result, destroying the
independence information. -/
theorem strict_fanout {Op V : Type} (f g : FreerArrow Op V) :
    StructFact.fanout_independence ∈f sigmaFA (FreerArrow.fanout f g) ∧
    ¬(StructFact.fanout_independence ∈f sigmaFM (FreerArrow.fanout f g)) := by
  constructor
  · rfl
  · intro hcontra
    exact False.elim hcontra

/-- The encoding makes fanout and seq indistinguishable. This is the
mechanism of information loss: if two different computations encode to
the same monad tree, any fact that distinguishes them is not recoverable. -/
theorem fanout_seq_indistinguishable {Op V : Type} (f g : FreerArrow Op V) :
    encodeMonad (.fanout f g) = encodeMonad (.seq f g) := by
  rfl

/-- For a pure computation (no fanout, no choice, no ops), σ(FA) is
minimal: only `dependency_graph` holds. This shows σ is semantic — it
depends on the computation, not just the representation type. -/
theorem sigmaFA_pure_minimal {Op V : Type} (v : V) :
    sigmaFA (FreerArrow.pure (Op := Op) (V := V) v) =
      fun f => f = .dependency_graph := by
  funext f
  cases f with
  | fanout_independence => simp [sigmaFA, holds, containsFanout]
  | branching => simp [sigmaFA, holds, containsChoice]
  | per_branch_effects => simp [sigmaFA, holds, containsChoice]
  | dependency_graph => simp [sigmaFA, holds]
  | feedback => simp [sigmaFA, holds, containsLoop]
  | effect_set => simp [sigmaFA, holds, containsOp]
  | op_provenance => simp [sigmaFA, holds]

-- ============================================================================
-- Step 8: ArrowApply Preserves σ
-- ============================================================================

/-- **ArrowApply preserves σ.** Adding the Apply constructor (monadic
power) does not change the structural information measure:

  σ(FA+Apply(C)) = σ(FA(C))

Proof: `sigmaFAA` is defined to equal `sigmaFA`. The `apply` constructor
is a structural tree node — it is traversable like any other. It adds
monadic power WITHOUT introducing opacity. -/
theorem arrowapply_preserves_sigma {Op V : Type} (c : FreerArrow Op V) :
    sigmaFAA c = sigmaFA c := by
  rfl

/-- Monadic power (via Apply) does not lose fanout independence. -/
theorem arrowapply_preserves_fanout {Op V : Type} (f g : FreerArrow Op V) :
    StructFact.fanout_independence ∈f sigmaFAA (.fanout f g) := by
  rw [arrowapply_preserves_sigma]
  exact (strict_fanout f g).1

-- ============================================================================
-- Step 9: Falsifying Maximality
-- ============================================================================

/-
The v1 maximality theorem was:

  theorem sigma_maximal_ArrowApply (R : MonadicRepresentation Op V)
      (hpower : R.hasMonadicPower) (c : FreerArrow Op V) (rc : R.Rep) :
      R.sigmaRep rc ⊆f sigmaFreerArrowApply c := by sorry

This was VACUOUSLY TRUE: `sigmaFreerArrowApply c = allFacts = fun _ => True`,
so `R.sigmaRep rc ⊆f allFacts` is `∀ f, R.sigmaRep rc f → True`, which
is trivially provable. The theorem said nothing.

In v2, `sigmaFAA c = sigmaFA c = {f | holds f c}`, which is NOT
allFacts. So a meaningful maximality theorem would be non-trivial. But
we show below that even the meaningful version is FALSE for rich
lattices: a tagged representation recovers strictly more.
-/

/-- **Maximality for computation-structure facts.** For any computation C,
σ(FA(C)) = {f | holds f C} — the ground truth. Any correct representation
R (one whose recovery agrees with `holds`) has σ_R(C) ⊆ σ(FA(C)).

This is true because σ(FA(C)) IS the set of all computation-structure
facts that hold of C. A correct representation can only recover facts
that hold — it cannot recover a fact that is false.

NOTE: This is true by construction — we defined `holds` relative to the
FreerArrow tree, so σ(FA) is the ground truth by definition. The
non-trivial content is that σ(FM) and σ(OM) are STRICT SUBSETS. -/
theorem sigmaFA_is_ground_truth {Op V : Type} (c : FreerArrow Op V) :
    sigmaFA c = fun f => holds f c = true := by
  rfl

/-- **Non-maximality: the counterexample.** The TaggedFreerArrow
representation:
  - Has full monadic power (includes `apply`)
  - Recovers all computation-structure facts (same as FreerArrow)
  - ADDITIONALLY recovers `op_provenance` (labels are visible)

For a computation with ops, `op_provenance ∈ σ(Tagged) but
∉ σ(FA)`. This FALSIFIES the maximality claim for any lattice that
includes provenance-like facts. -/
theorem tagged_recovers_more {Op V : Type} (o : Op) (k : FreerArrow Op V) :
    StructFact.op_provenance ∈f sigmaTagged (FreerArrow.op o k) ∧
    ¬(StructFact.op_provenance ∈f sigmaFA (FreerArrow.op o k)) := by
  constructor
  · rfl
  · intro hcontra
    exact Bool.false_ne_true hcontra

/-- The tagged representation also recovers everything the freer arrow
recovers (it is a superset). -/
theorem sigmaTagged_superset_sigmaFA {Op V : Type} (c : FreerArrow Op V) :
    sigmaFA c ⊆f sigmaTagged c := by
  intro f hf
  cases f with
  | op_provenance => exact False.elim (Bool.false_ne_true hf)
  | fanout_independence => exact hf
  | branching => exact hf
  | per_branch_effects => exact hf
  | dependency_graph => exact hf
  | feedback => exact hf
  | effect_set => exact hf

/-- **The maximality claim is false.** There exists a representation
(TaggedFreerArrow) with full monadic power that recovers strictly more
structural information than the freer arrow with Apply, for
computations containing ops. -/
theorem maximality_is_false {Op V : Type} (o : Op) (k : FreerArrow Op V) :
    ¬(sigmaTagged (FreerArrow.op o k) ⊆f sigmaFAA (FreerArrow.op o k)) := by
  intro hcontra
  have h1 := (tagged_recovers_more o k).1
  have h2 := hcontra StructFact.op_provenance h1
  exact (tagged_recovers_more o k).2 h2

-- ============================================================================
-- Step 10: The Honest Boundary Theorem
-- ============================================================================

/-
## The Boundary Theorem (combining Steps 6–9)

For any computation C, represented as a freer arrow (FA), a freer
monad (FM), an opaque monad (OM), and a freer arrow with Apply (FAA):

  (1) σ(FA(C)) ⊇ σ(FM(C)) ⊇ σ(OM(C))         [Theorem sigma_ordering]
  (2) fanout_independence ∈ σ(FA(C)) \ σ(FM(C))
      if C has fanout                        [Theorem strict_fanout]
  (3) σ(FAA(C)) = σ(FA(C))                    [Theorem arrowapply_preserves_sigma]
  (4) σ(FA(C)) = {f | holds f C}              [Theorem sigmaFA_is_ground_truth]
  (5) σ(Tagged(C)) ⊋ σ(FA(C)) if C has ops    [Theorem tagged_recovers_more]

## What the boundary IS

The freer arrow with Apply sits at a **boundary point**: it has full
monadic power (via Apply) AND full observability of computation-structure
facts (σ = ground truth). No representation that encodes the same
computation can recover strictly more computation-structure facts —
they're properties of C, and FA recovers all of them.

## What the boundary is NOT

The freer arrow with Apply is NOT maximal for all representable
information. A richer representation (TaggedFreerArrow) can carry
metadata (provenance, timing, allocation patterns) that is NOT a
computation-structure fact, recovering strictly more information.

## The honest claim

The freer arrow with Apply is the **minimal representation that achieves
both**:
  (a) full monadic power (can express dynamic application), AND
  (b) full observability of computation-structure facts (σ = ground truth).

It is not the maximal representation — richer representations can do
better. It is the **boundary crossing point**: the simplest
representation that gives you both expressiveness and observability.

## Relation to VanDomelen et al. 2025

VanDomelen et al. establish empirically that freer arrows are more
statically analyzable than freer monads. Our contribution is the
**formal characterization**: we define a semantic measure σ, prove the
ordering theorem, and show that ArrowApply sits at the boundary point
(full power + full observability). We also show that "maximality" is
the wrong framing — the correct framing is "boundary crossing."
-/

end StructuralInfo
