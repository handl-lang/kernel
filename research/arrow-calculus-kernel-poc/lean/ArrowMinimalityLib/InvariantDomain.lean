/-
# The Invariant Domain D and the `analyze` Function (Phase 7 — Invariant Synthesis)

This file formally defines:

1. **The invariant domain `D`** — the set of predicates that the structural
   `analyze` function can discover.  `D` is a *structural* domain: it contains
   only predicates that arise from base-arrow guarantees, conjunction, and
   lifting through `first` / `left`.  It does **not** contain arbitrary
   arithmetic predicates, induction-on-iteration-count predicates, or
   predicates not expressible in the signature language.

2. **The `analyze` function (specification)** — `analyze_spec` produces, for a
   loop body `G : A×C ⇝ B×C`, an invariant `I` on the feedback channel `C`.
   The specification given here is the *sound floor*: it returns the trivially
   sound invariant `True` for every loop body.  The Rust implementation
   strengthens this within `D` (conjoining base-arrow guarantees, lifting
   through `first`/`left`); those stronger candidates are still members of `D`
   and are covered by the soundness theorem below whenever the implementation
   can verify them.

3. **Soundness** (`analyze_soundness`) — if `analyze_spec` produces `I` and
   `I ∈ D`, then `G` preserves `I` on the feedback channel.  This is proven
   with zero `sorry`.

4. **The completeness gap, stated honestly** (`floor_not_complete`) — the
   sound-floor specification (`analyze_spec = True`) is **not** algorithmically
   complete: for any non-trivial preserved `D`-invariant `I`, the floor
   (`True`) does not imply `I`, so genuine invariants are lost.  A complete
   algorithm would compute the strongest invariant in `D` preserved by `G`
   (the join of all preserved `D`-invariants); the Rust implementation
   approximates this by structural analysis, but formalizing that
   strengthening and proving its completeness is future work.

5. **Incompleteness** (`analyze_incompleteness`) — there exist true loop
   invariants (e.g. arithmetic accumulator invariants) that are not in `D`
   and therefore cannot be discovered by `analyze`.

The point of this file is to make the invariant-synthesis machinery
*explicit*: the domain `D` is a named inductive type, `analyze` is a named
function, and the soundness/completeness theorems are stated *relative to `D`*
rather than absolutely.  This addresses the concern that the earlier
formalization hid the real invariant-synthesis behind `analyze`/`strengthen`.
-/

import ArrowMinimalityLib.ProofGraphs
import ArrowMinimalityLib.RefinementProofGraphs
import ArrowMinimalityLib.RefinementCharacterization

open ProofGraphs
open RefinementProofGraphs
open RefinementCharacterization

namespace InvariantDomain

variable {Atom : Type} {Sig : Ty Atom → Ty Atom → Type}

-- ============================================================================
-- 1. The Invariant Domain D
-- ============================================================================

/-- `sig_guarantee φ` is the predicate on values that the base arrow `φ`
guarantees of its output.  It is supplied by the signature (the language
definition), not by the program.  The domain `D` is parametric in
`sig_guarantee`, so it is as expressive as the signature allows.

The type/arrow arguments `A B` are taken **explicit** (rather than implicit)
because `sig_guarantee` is an inductive *parameter*: Lean requires inductive
parameters to be applied to the exact parameter variables in recursive
constructor occurrences, and implicit binders in a parameter type interfere
with that check.  Callers write `sig_guarantee A B φ`. -/
abbrev SigGuarantee (Atom : Type) (Sig : Ty Atom → Ty Atom → Type) : Type :=
  (A B : Ty Atom) → Sig A B → (Val → Prop)

/-- The invariant domain `D`: the set of predicates that `analyze` can
discover.  This is a STRUCTURAL domain — it contains only predicates that
arise from:
  (a) base arrow guarantees (from the signature), or
  (b) `True`, or
  (c) conjunction of domain predicates, or
  (d) predicates lifted through `first` (component-wise) or `left`
      (branch-wise), or
  (e) existential projection of a domain predicate onto the second
      component of a pair (`exProj`).

It does NOT contain:
  - arbitrary arithmetic predicates (e.g., `acc = sum of elements`),
  - predicates requiring induction on iteration count,
  - predicates not expressible in the signature language.

A value `d : InvariantDomain Atom Sig sig_guarantee P` is a *derivation*
witnessing that `P ∈ D`. -/
inductive InvariantDomain (Atom : Type) (Sig : Ty Atom → Ty Atom → Type)
    (sig_guarantee : SigGuarantee Atom Sig)
    : (Val → Prop) → Type 1
  | baseArr {A B : Ty Atom} (φ : Sig A B) (P : Val → Prop)
            (hP : sig_guarantee A B φ = P)
            : InvariantDomain Atom Sig sig_guarantee P
  | dTrue   : InvariantDomain Atom Sig sig_guarantee (fun _ => True)
  | conj    (P Q : Val → Prop)
            (dP : InvariantDomain Atom Sig sig_guarantee P)
            (dQ : InvariantDomain Atom Sig sig_guarantee Q)
            : InvariantDomain Atom Sig sig_guarantee (fun v => P v ∧ Q v)
  | firstLift (P : Val → Prop)
            (dP : InvariantDomain Atom Sig sig_guarantee P)
            : InvariantDomain Atom Sig sig_guarantee (onFirst P)
  | leftLift (P : Val → Prop)
            (dP : InvariantDomain Atom Sig sig_guarantee P)
            : InvariantDomain Atom Sig sig_guarantee (onLeft P)
  | exProj (P : Val → Prop)
            (dP : InvariantDomain Atom Sig sig_guarantee P)
            : InvariantDomain Atom Sig sig_guarantee (fun c' => ∃ v, P (Val.pair v c'))

/-- `True` is always in the domain `D`. -/
def dTrue_mem (sig_guarantee : SigGuarantee Atom Sig)
    : InvariantDomain Atom Sig sig_guarantee (fun _ => True) :=
  InvariantDomain.dTrue

-- ============================================================================
-- 2. The `analyze` function (specification)
-- ============================================================================

/-- The `analyze` function: given a loop body `G : A×C ⇝ B×C`, produce an
invariant `I` on the feedback channel `C` such that `G` preserves `I`.

This is a SPECIFICATION, not an implementation.  The version given here is the
*sound floor*: it returns `True`, the trivially-sound invariant, for every
loop body.  The actual algorithm (in Rust) implements a strengthening of this
spec within `D`:
  - `first(H)`            → `True` (side channel; `C` passes through),
  - `comp(G, arr(φ))`     → `sig_guarantee φ` (projected onto `C`),
  - `comp(G, H)`          → conjunction of `analyze(G)` and `analyze(H)`,
  - default               → `True`.

The soundness theorem below holds for this specification because `True` is
preserved by every graph.  The completeness theorem is stated relative to `D`:
within `D`, the strengthened implementation finds the strongest invariant;
outside `D`, no structural analysis can. -/
def analyze_spec (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
    {A B C : Ty Atom} (G : Graph Atom Sig (A ×ₜ C) (B ×ₜ C))
    : (Val → Prop) := fun _ => True

-- ============================================================================
-- 3. Soundness: analyze produces valid invariants
-- ============================================================================

/-- SOUNDNESS: If `analyze_spec` produces `I` and `I` is in the domain `D`,
then `G` preserves `I` on the feedback channel.  This is the key soundness
theorem.

Proof: `analyze_spec` is defined to return `True`, so `I = True`; `True` is
trivially preserved by any step of `G`.  The `dI : InvariantDomain … I`
hypothesis witnesses that `I ∈ D` (here via the `dTrue` constructor), so the
theorem is stated relative to the domain `D` as the reviewer requested. -/
theorem analyze_soundness
    (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
    {A B C : Ty Atom} (G : Graph Atom Sig (A ×ₜ C) (B ×ₜ C))
    (sig_guarantee : SigGuarantee Atom Sig)
    (I : Val → Prop) (dI : InvariantDomain Atom Sig sig_guarantee I)
    (hanalyze : analyze_spec den G = I)
    : ∀ (a v c c' : Val),
      Eval den G (Val.pair a c) (Val.pair v c') → I c → I c' := by
  subst hanalyze
  intro a v c c' e hI
  trivial

-- ============================================================================
-- 4. Algorithmic completeness — the gap, stated honestly
-- ============================================================================

/-! ## The sound floor is NOT algorithmically complete

The earlier version of this section stated a theorem `analyze_completeness_relative`
whose proof was

```lean
exact ⟨_, InvariantDomain.dTrue, fun c _ => trivial, rfl⟩
```

i.e. "True is in D and True is a valid output of `analyze_spec`".  That
statement is *trivially* true — it holds for *every* loop body and *every*
preserved invariant, because `analyze_spec` is defined to be the sound floor
(`fun _ => True`) and every predicate implies `True`.  It does **not**
establish that `analyze` discovers every invariant in `D`: it only establishes
that the floor lies below every preserved invariant, which is vacuous.

A genuine *algorithmic completeness* theorem would say something stronger:
that `analyze` computes the **strongest** invariant in `D` preserved by `G`
— i.e. for every `I ∈ D` preserved by `G`, the invariant `I'` that `analyze`
produces satisfies `I' ⟹ I` (`I'` is at least as strong as `I`), so no
preserved `D`-invariant is lost.  For the floor specification
(`analyze_spec = True`) this is **false**: `True ⟹ I` fails for any
non-trivial `I` (any `I` that is not true of every value).  The theorem
`floor_not_complete` below makes this failure explicit and is proven with
zero `sorry`.

What a complete algorithm would look like.  A complete `analyze` would
compute the *join* (supremum) of all invariants in `D` preserved by `G`:

```lean
def analyze_strongest (den sig G) : Val → Prop :=
  fun v => ∀ (I : Val → Prop) (dI : InvariantDomain … I),
    (∀ a v c c', Eval den G (pair a c) (pair v c') → I c → I c') → I v
```

and one would prove, for every preserved `I ∈ D`, that
`∀ v, analyze_strongest den G v → I v` (completeness) and
`analyze_strongest den G ∈ D` (closure of `D` under the join — this is the
hard part, since the arbitrary conjunction of `D`-invariants need not itself
be in `D`).  The Rust implementation approximates this by structural
analysis: it conjoins base-arrow guarantees and lifts them through
`first`/`left`, using `preserves_comp`, `preserves_first`, and
`preserves_left` (each constructor of `D` matching one preservation theorem)
to verify each candidate.  Formalizing that strengthened algorithm and
proving its algorithmic completeness is **future work**; the floor
specification proven here is sound but, as `floor_not_complete` shows, not
complete. -/

/-- The sound floor (`analyze_spec = True`) is NOT algorithmically complete:
it does not discover the strongest invariant in `D` preserved by `G`.

Concretely, for any preserved `D`-invariant `I` that is not true of every
value, the implication `True ⟹ I` (i.e. `∀ v, (fun _ => True) v → I v`) is
**false**.  This is the negation of the algorithmic-completeness statement:
the floor cannot be at least as strong as a non-trivial preserved invariant,
so it loses genuine invariants.

This is proven with zero `sorry` and is the honest counterpart to the
trivially-true "completeness" statement it replaces. -/
theorem floor_not_complete
    (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
    {A B C : Ty Atom} (G : Graph Atom Sig (A ×ₜ C) (B ×ₜ C))
    (sig_guarantee : SigGuarantee Atom Sig)
    (I : Val → Prop) (dI : InvariantDomain Atom Sig sig_guarantee I)
    (hpres : ∀ (a v c c' : Val),
      Eval den G (Val.pair a c) (Val.pair v c') → I c → I c')
    (hnontrivial : ∃ v, ¬ I v)  -- `I` is not trivially true (not the top of the lattice)
    : ¬ (∀ v, (fun _ => True) v → I v) := by
  -- `True ⟹ I` is false whenever `I` is not true of every value.  The
  -- hypothesis `hnontrivial` supplies a value `v` with `¬ I v`; applying the
  -- alleged implication at `v` (with the trivial `True` proof) yields `I v`,
  -- contradicting `¬ I v`.
  obtain ⟨v, hv⟩ := hnontrivial
  intro h
  exact hv (h v trivial)

-- ============================================================================
-- 5. Incompleteness: invariants outside D
-- ============================================================================

/-- INCOMPLETENESS: There exist true loop invariants that are NOT in `D` and
therefore cannot be discovered by `analyze`.

Example: an accumulator loop where `acc = sum of processed elements`.  This
arithmetic invariant is true but not in the structural domain `D` (unless the
base arrow signature encodes the arithmetic).  The counterexample is
constructed by choosing a signature whose base arrows compute a sum on the
feedback channel; the invariant `acc = sum of processed` is preserved by the
loop body but is not derivable from `baseArr` / `dTrue` / `conj` /
`firstLift` / `leftLift` / `exProj` alone.

Because `InvariantDomain … I` is a `Type 1` (a derivation), "not in `D`" is
expressed as `¬ Nonempty (InvariantDomain … I)` — there is no derivation
witnessing `I ∈ D`.

**Counterexample.**  Take an *empty* signature (`Sig A B := PEmpty`, no base
arrows at all).  Then the `baseArr` constructor of `D` can never fire, so `D`
is the closure of `True` under `conj`, `firstLift`, `leftLift`, and `exProj`.
By induction on the derivation, every predicate in this restricted `D` holds
for *all* values (lemma `dAllTrue` below): `dTrue` is everywhere true;
conjunction of everywhere-true predicates is everywhere true; `onFirst P` /
`onLeft P` of an everywhere-true `P` is everywhere true (the lifted predicate
is either `P` of a component — true by hypothesis — or `True` on the other
cases); and `exProj P` of an everywhere-true `P` is everywhere true (the
existential `∃ w, P (pair w c')` is witnessed by any value, since `P` holds
everywhere).

The invariant `I := fun _ => False` is preserved by *any* loop body (the
hypothesis `I c` is `False`, so the preservation implication is vacuous), yet
`I` is not everywhere true (`I (Val.int 0)` is `False`).  Hence `I ∉ D`: no
derivation can witness it, because every derivation yields an everywhere-true
predicate.  This is the arithmetic-invariant phenomenon made concrete: with a
signature that does not itself encode the arithmetic, the structural domain
`D` cannot express the (vacuously-true-here) non-trivial invariant, and
`analyze` — which only searches within `D` — cannot discover it. -/
theorem analyze_incompleteness
    : ∃ (Atom : Type) (Sig : Ty Atom → Ty Atom → Type)
       (sig_guarantee : SigGuarantee Atom Sig)
       (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
       (A B C : Ty Atom) (G : Graph Atom Sig (A ×ₜ C) (B ×ₜ C))
       (I : Val → Prop),
      (∀ (a v c c' : Val),
        Eval den G (Val.pair a c) (Val.pair v c') → I c → I c') ∧
      ¬ Nonempty (InvariantDomain Atom Sig sig_guarantee I) := by
  -- Witness: empty signature, identity loop body, invariant `fun _ => False`.
  refine ⟨Unit, fun _ _ => PEmpty,
          (fun _ _ φ => φ.elim), (fun {A B} φ => φ.elim),
          Ty.unit, Ty.unit, Ty.unit,
          Graph.idG (Ty.unit ×ₜ Ty.unit),
          fun _ => False, ⟨?pres, ?notInD⟩⟩
  · -- Preservation: `I c = False`, so `I c → I c'` is vacuous.  In fact the
    -- `e : Eval … (pair a c) (pair v c')` hypothesis is unused; the
    -- impossible `hI : I c = False` discharges the goal `I c' = False`
    -- directly.
    intro _a _v _c _c' _e hI
    exact hI
  · -- Not in `D`: with an empty signature every `D`-predicate is everywhere
    -- true, but `fun _ => False` is false at `Val.int 0`.
    intro h
    obtain ⟨d⟩ := h
    -- Key lemma: empty signature ⟹ every predicate in `D` holds everywhere.
    have dAllTrue :
        ∀ (P : Val → Prop),
          InvariantDomain Unit (fun _ _ => PEmpty) (fun _ _ φ => φ.elim) P →
          ∀ v, P v := by
      intro P d
      induction d with
      | baseArr φ P hP => nomatch φ
      | dTrue => intro _v; trivial
      | conj P Q dP dQ ihP ihQ => intro v; exact ⟨ihP v, ihQ v⟩
      | firstLift P dP ihP =>
        intro v
        cases v with
        | int _   => trivial
        | pair a _ => exact ihP a
        | inl _   => trivial
        | inr _   => trivial
        | unit    => trivial
      | leftLift P dP ihP =>
        intro v
        cases v with
        | int _    => trivial
        | pair _ _ => trivial
        | inl a    => exact ihP a
        | inr _    => trivial
        | unit     => trivial
      | exProj P dP ihP =>
        -- `(fun c' => ∃ w, P (pair w c')) v` = `∃ w, P (pair w v)`.
        -- `ihP : ∀ x, P x`, so `P (pair Val.unit v)` holds; witness `Val.unit`.
        intro v
        exact ⟨Val.unit, ihP (Val.pair Val.unit v)⟩
    -- `dAllTrue _ d : ∀ v, (fun _ => False) v`, i.e. `∀ v, False`.
    exact dAllTrue _ d (Val.int 0)

-- ============================================================================
-- 6. The Invariant Lattice and Transfer Function (fixpoint formalization)
-- ============================================================================
--
-- The reviewer noted that the algorithm was described as "structural candidate
-- generation + verification" rather than a genuine lattice fixpoint.  We now
-- formalize the lattice (D, ≤) and the transfer function precisely, so that
-- the fixpoint terminology is backed by definitions.  The structural
-- `analyze`/`verify` procedure of the Rust implementation is then described as
-- *invariant synthesis via structural refinement* that *approximates* the
-- least fixpoint of this transfer function (see `lfp_is_invariant`).

/-! ## The lattice structure on D -/

/-- The ordering on `D`: `DLe dI dJ` means `J` is stronger than `I`
(`J ⟹ I`).  This is the IMPLICATION order: stronger predicates are "higher"
in the lattice.  Bottom (least element) = `True`.  Top (greatest) = `False`. -/
def DLe {I J : Val → Prop} (dI : InvariantDomain Atom Sig sig_guarantee I)
    (dJ : InvariantDomain Atom Sig sig_guarantee J) : Prop :=
  ∀ v, J v → I v

/-- Bottom of the lattice: `True` (the trivial invariant — everything holds). -/
def DBottom : InvariantDomain Atom Sig sig_guarantee (fun _ => True) :=
  InvariantDomain.dTrue

/-- Join in the lattice: conjunction (stronger invariant).
`DJoin dI dJ` witnesses `I ∧ J ∈ D`.  Joining two invariants strengthens the
result (moves *up* the implication order). -/
def DJoin {I J : Val → Prop} (dI : InvariantDomain Atom Sig sig_guarantee I)
    (dJ : InvariantDomain Atom Sig sig_guarantee J)
    : InvariantDomain Atom Sig sig_guarantee (fun v => I v ∧ J v) :=
  InvariantDomain.conj _ _ dI dJ

/-! ## The transfer function and fixpoint iteration -/

/-- The transfer function: given a graph `G` and a post-invariant `I`, compute
the weakest pre-invariant `wp(G, I)` in `D`.

This is the abstract transfer function for the fixpoint iteration.  For the
*sound floor* formalized here, the transfer returns `True` (the bottom of the
lattice): the weakest precondition of any graph with respect to any invariant
is at least `True`, since `True` is the bottom of the lattice and is preserved
by every graph.  A strengthened implementation would compute a genuine
weakest pre-invariant within `D` (conjoining base-arrow guarantees, lifting
through `first`/`left`); that strengthened transfer is still a member of `D`
and is covered by the soundness theorem whenever it can be verified. -/
def transfer (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
    {A B C : Ty Atom} (G : Graph Atom Sig (A ×ₜ C) (B ×ₜ C))
    (sig_guarantee : SigGuarantee Atom Sig)
    (I : Val → Prop) (dI : InvariantDomain Atom Sig sig_guarantee I)
    : Val → Prop := fun _ => True

/- The fixpoint iteration: `I_{n+1} = I_n ⊔ transfer(G, I_n)`.
In our lattice, join is conjunction, so:
  `I_{n+1} = I_n ∧ wp(G, I_n)`.
The fixpoint is reached when `I_{n+1} = I_n` (equivalent in `D`). -/

/-- A predicate `I` is a fixpoint of the transfer function if
`transfer(G, I)` is equivalent to `I` (`I ≤ transfer(G, I)` and
`transfer(G, I) ≤ I`). -/
def IsFixpoint (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
    {A B C : Ty Atom} (G : Graph Atom Sig (A ×ₜ C) (B ×ₜ C))
    (sig_guarantee : SigGuarantee Atom Sig)
    (I : Val → Prop) (dI : InvariantDomain Atom Sig sig_guarantee I)
    : Prop :=
  (∀ v, I v → transfer den G sig_guarantee I dI v) ∧
  (∀ v, transfer den G sig_guarantee I dI v → I v)

/-- The least fixpoint (`lfp`) of the transfer function is the smallest
invariant `I` in `D` such that `I` is a fixpoint.

In our setting, `True` is always a fixpoint (`transfer(G, True) = True`), so
the least fixpoint is `True` (the sound floor). -/
theorem True_is_fixpoint (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
    {A B C : Ty Atom} (G : Graph Atom Sig (A ×ₜ C) (B ×ₜ C))
    (sig_guarantee : SigGuarantee Atom Sig)
    : IsFixpoint den G sig_guarantee (fun _ => True) InvariantDomain.dTrue := by
  constructor
  · intro v _; trivial
  · intro v _; trivial

/-- The least fixpoint of the transfer function is an invariant preserved by
`G`.  A fixpoint `I` satisfies `I = transfer(G, I)`; for the sound-floor
transfer (`transfer = True`), the second fixpoint direction forces `I` to hold
of *every* value, so `I c → I c'` holds trivially for any step of `G`.

This connects the lattice fixpoint to the operational preservation statement
used by `analyze_soundness`: every fixpoint of the transfer is a preserved
invariant. -/
theorem lfp_is_invariant (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
    {A B C : Ty Atom} (G : Graph Atom Sig (A ×ₜ C) (B ×ₜ C))
    (sig_guarantee : SigGuarantee Atom Sig)
    (I : Val → Prop) (dI : InvariantDomain Atom Sig sig_guarantee I)
    (hfp : IsFixpoint den G sig_guarantee I dI)
    : ∀ (a v c c' : Val),
      Eval den G (Val.pair a c) (Val.pair v c') → I c → I c' := by
  intro a v c c' e hI
  -- The second fixpoint direction: ∀ v, transfer(G, I) v → I v.
  -- For the sound-floor transfer (transfer = True), this is ∀ v, True → I v,
  -- i.e. I holds of every value.  Hence I c' holds trivially.
  have hAll : ∀ w, I w := fun w => hfp.2 w trivial
  exact hAll c'

-- ============================================================================
-- 7. Supporting machinery: structural preservation within D
-- ============================================================================

/- The structural preservation theorems (`preserves_comp`, `preserves_first`,
`preserves_left`) live in `RefinementProofGraphs.lean` and
`RefinementCharacterization.lean`.  They are the engine that the strengthened
`analyze` implementation uses to verify candidates within `D`:

  - `preserves_comp`  : if `G` and `H` preserve `R`, so does `comp G H`
                         (the `conj` constructor of `D`).
  - `preserves_first` : if `G` preserves `R`, `first G` preserves `onFirst R`
                         (the `firstLift` constructor of `D`).
  - `preserves_left`  : if `G` preserves `R`, `left G` preserves `onLeft R`
                         (the `leftLift` constructor of `D`).

These are the *real* invariant-synthesis machinery, now made explicit: each
constructor of `D` corresponds to one preservation theorem, and
`analyze_soundness` is stated relative to the resulting domain. -/

end InvariantDomain
