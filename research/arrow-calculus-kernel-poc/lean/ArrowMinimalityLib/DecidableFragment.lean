/- # A Sound, Terminating, Complete Decider for the Loop-Free Arrow Fragment

This file mechanizes the "restricted fragment" claim: for the arrow fragment

  `A₀ = arr · composition · identity`        (loop-free, finite domain,
                                              `arr` restricted to EXPLICIT
                                              base arrows `Fin n → Fin n`)

there is a decision procedure that, given an arrow program (graph) and a
property (in a decidable property language: true / "semantics equals f" /
conjunction), returns TRUE or FALSE, and is:

  1. SOUND       — `decider_sound`       : TRUE   → property holds
  2. COMPLETE    — `decider_complete`    : property holds → TRUE
  3. TERMINATING — `decider_terminates`  : always returns TRUE or FALSE
                                            (total, structurally recursive)

The pipeline "normalize/analyze → exact semantics → prove property" is the
pair (`Graph.sem`, `PropF.decide`); semantic equality of programs is itself
decidable (`Graph.deq_true_iff`).

## What is deliberately excluded, and why (honest scope)

- `ArrowLoop` is EXCLUDED because feedback makes the semantics a fixpoint;
  over infinite domains fixpoint properties are undecidable in general
  (this is the boundary the "specified class" lives on). Over a FINITE
  domain even `loop` becomes model-checkable — but the fixpoint iteration
  is no longer the simple structural recursion used here.
- `arr` is restricted to explicit base arrows with decidable semantics.
  This restriction is NOT optional: allowing arbitrary computable functions
  inside `arr` makes every nontrivial semantic property undecidable (Rice).
- `first` / `second` / `fanout` and `ArrowChoice` are conservative
  extensions semantically (products/sums of finite domains are finite, and
  componentwise/branchwise semantics preserve decidability), so their
  omission here is for brevity of the mechanization, not a decidability
  boundary. The monomorphic single-sorted presentation (`Fin n`) encodes
  products by standard finite pairings.
- Completeness is relative to the PROPERTY LANGUAGE `PropF`: the decider
  is complete for exactly the properties expressible in it. This is the
  precise sense of "complete for a specified class of programs/properties".

All theorems are zero `sorry` (checked by `#print axioms`). -/

namespace DecidableFragment

-- ============================================================================
-- 1. Decidable pointwise equality of functions out of a finite domain
-- ============================================================================

/-- Pointwise comparison of `f g : Fin m → Fin n`, by enumerating the
finite domain `Fin m`. Structural recursion on `m`: TERMINATES. -/
def funEqAux {n m : Nat} (f g : Fin m → Fin n) : Bool :=
  match m with
  | 0 => true
  | k+1 =>
    decide (f ⟨k, Nat.lt_succ_self k⟩ = g ⟨k, Nat.lt_succ_self k⟩) &&
    funEqAux (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
             (fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)

/-- CORRECTNESS of the enumeration: `funEqAux f g = true ↔ ∀ i, f i = g i`.
This is the soundness+completeness lemma the whole decider rests on. -/
theorem funEqAux_eq {n m : Nat} (f g : Fin m → Fin n) :
    funEqAux f g = true ↔ ∀ i : Fin m, f i = g i := by
  induction m with
  | zero =>
    constructor
    · intro _ i
      exact absurd i.isLt (Nat.not_lt_zero i.val)
    · intro _; rfl
  | succ k ih =>
    constructor
    · intro hall i
      simp only [funEqAux] at hall
      have hpair : decide (f ⟨k, Nat.lt_succ_self k⟩ = g ⟨k, Nat.lt_succ_self k⟩) = true ∧
                   funEqAux (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
                            (fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) = true :=
        Iff.of_eq (Bool.and_eq_true _ _) |>.mp hall
      have hlast : f ⟨k, Nat.lt_succ_self k⟩ = g ⟨k, Nat.lt_succ_self k⟩ :=
        of_decide_eq_true hpair.1
      by_cases h : i = ⟨k, Nat.lt_succ_self k⟩
      · rw [h]
        exact hlast
      · have hne : i.val ≠ k := fun hc => h (Fin.ext hc)
        have hlt : i.val < k :=
          Nat.lt_of_le_of_ne (Nat.le_of_lt_succ i.isLt) hne
        exact (ih (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
                  (fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)).mp
            hpair.2 ⟨i.val, hlt⟩
    · intro hall
      simp only [funEqAux]
      refine Iff.of_eq (Bool.and_eq_true _ _) |>.mpr ⟨?_, ?_⟩
      · exact decide_eq_true (hall ⟨k, Nat.lt_succ_self k⟩)
      · exact (ih (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
                  (fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)).mpr
          (fun i => hall ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)

/-- Decidable pointwise equality for full-domain functions. -/
def funEq {n : Nat} (f g : Fin n → Fin n) : Bool := funEqAux f g

theorem funEq_eq {n : Nat} (f g : Fin n → Fin n) :
    funEq f g = true ↔ ∀ i : Fin n, f i = g i :=
  funEqAux_eq f g

/-- Functional equality over a finite domain is DECIDABLE. -/
instance {n : Nat} (f g : Fin n → Fin n) : Decidable (f = g) :=
  decidable_of_decidable_of_iff (p := funEq f g = true) (by
    constructor
    · intro h; exact funext ((funEq_eq f g).mp h)
    · intro h; exact (funEq_eq f g).mpr (fun i => congrFun h i))

-- ============================================================================
-- 2. The loop-free arrow fragment: programs and their exact semantics
-- ============================================================================

/-- Loop-free arrow programs over a finite domain `Fin n`:
`arr` (restricted to explicit base arrows), identity, and composition.
No `ArrowLoop` — this is what makes the semantics a plain function. -/
inductive Graph (n : Nat) : Type where
  | idG : Graph n
  | baseG (f : Fin n → Fin n) : Graph n
  | compG (a b : Graph n) : Graph n

/-- The EXACT semantics of a loop-free graph: a plain function
`Fin n → Fin n`, obtained by structural recursion (total, terminating). -/
def Graph.sem {n : Nat} (g : Graph n) : Fin n → Fin n :=
  match g with
  | .idG => id
  | .baseG f => f
  | .compG a b => fun v => b.sem (a.sem v)

/-- Semantic equality of programs is decidable. -/
def Graph.deq {n : Nat} (a b : Graph n) : Bool := funEq a.sem b.sem

theorem Graph.deq_true_iff {n : Nat} (a b : Graph n) :
    a.deq b = true ↔ a.sem = b.sem :=
  Iff.trans (funEq_eq a.sem b.sem)
    ⟨fun h => funext h, fun h i => congrFun h i⟩

-- ============================================================================
-- 3. The property language and its decider
-- ============================================================================

/-- Decidable property language: `true`, "the program's semantics equals
the witness f", and conjunction. Completeness below is RELATIVE to this
language — the precise sense of "complete for a specified class". -/
inductive PropF (n : Nat) : Type where
  | pTrue : PropF n
  | pEq (f : Fin n → Fin n) : PropF n
  | pAnd (p q : PropF n) : PropF n

/-- Semantic satisfaction. -/
def PropF.holds {n : Nat} (p : PropF n) (g : Fin n → Fin n) : Prop :=
  match p with
  | .pTrue => True
  | .pEq f => g = f
  | .pAnd p q => p.holds g ∧ q.holds g

/-- THE DECIDER: normalize to exact semantics (`Graph.sem`), then decide
the property by finite enumeration. Total, structurally recursive. -/
def PropF.decide {n : Nat} (p : PropF n) (g : Fin n → Fin n) : Bool :=
  match p with
  | .pTrue => true
  | .pEq f => funEq g f
  | .pAnd p q => p.decide g && q.decide g

-- ============================================================================
-- 4. THE THREE GUARANTEES: sound, complete, terminating
-- ============================================================================

/-- SOUNDNESS: TRUE → the property holds. -/
theorem PropF.decider_sound {n : Nat} (p : PropF n) (g : Fin n → Fin n) :
    p.decide g = true → p.holds g := by
  induction p with
  | pTrue => intro _; trivial
  | pEq f => intro h; exact funext ((funEq_eq g f).mp h)
  | pAnd p q ihp ihq =>
      intro h
      have hpair : p.decide g = true ∧ q.decide g :=
        Iff.of_eq (Bool.and_eq_true _ _) |>.mp h
      obtain ⟨h1, h2⟩ := hpair
      exact ⟨ihp h1, ihq h2⟩

/-- COMPLETENESS: property holds → TRUE (relative to `PropF`). -/
theorem PropF.decider_complete {n : Nat} (p : PropF n) (g : Fin n → Fin n) :
    p.holds g → p.decide g = true := by
  induction p with
  | pTrue => intro _; rfl
  | pEq f => intro h; exact (funEq_eq g f).mpr (fun i => congrFun h i)
  | pAnd p q ihp ihq =>
      intro ⟨h1, h2⟩
      exact Iff.of_eq (Bool.and_eq_true _ _) |>.mpr ⟨ihp h1, ihq h2⟩

/-- TERMINATION / DECIDEDNESS: the decider ALWAYS returns exactly one of
TRUE or FALSE — it is a total, structurally recursive function. -/
theorem PropF.decider_terminates {n : Nat} (p : PropF n) (g : Fin n → Fin n) :
    p.decide g = true ∨ p.decide g = false := by
  match h : p.decide g with
  | true => exact Or.inl rfl
  | false => exact Or.inr rfl

end DecidableFragment
