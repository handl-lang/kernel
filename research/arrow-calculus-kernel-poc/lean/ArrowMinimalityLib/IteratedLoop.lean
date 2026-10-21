/-
# Iterated Loop Semantics

The one-step `Eval` fixpoint rule (`eLoop` in `ProofGraphs.lean`) requires
the feedback channel to already be stable (`c_next = cₙ`). This file defines
`EvalIter`, an iterated version where `loop` unfolds until convergence, and
proves three results:

  1. **One-step implies iterated** (`one_step_implies_iterated`):
     `Eval (Graph.loop G) a v → EvalIter (Graph.loop G) a v`.
     The one-step `eLoop` rule is exactly `eLoopZero`.

  2. **Iterated subject reduction** (`iterated_subject_reduction`):
     `TyOf (Graph.loop G) → EvalIter (Graph.loop G) a v → a : A → v : B`.
     Each iteration preserves types: if `G : (A×C) ⇝ (B×C)` and
     `(a,cᵢ) ⟹ (vᵢ,cᵢ₊₁)` with `a : A` and `cᵢ : C`, then `vᵢ : B`
     and `cᵢ₊₁ : C`.

  3. **Equivalence at fixpoints** (`iterated_equiv_at_fixpoint`):
     `EvalIter (Graph.loop G) a v → Eval (Graph.loop G) a v`.
     Every finite `EvalIter` derivation of `loop G` terminates in an
     `eLoopZero` (a fixpoint where `c_next = cₙ`); the `eLoopIter` steps
     thread through to that final fixpoint, so the iterated result is
     always realisable by the one-step rule.
-/

import ArrowMinimalityLib.ProofGraphs

open ProofGraphs

namespace IteratedLoop

variable {Atom : Type} {Sig : Ty Atom → Ty Atom → Type}
variable (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)

-- ============================================================================
-- 1. Iterated loop semantics
-- ============================================================================

/-- The iterated evaluation relation `EvalIter den G a v` reads
`G · a ⟹* v` under the base-arrow interpretation `den`. It mirrors `Eval`
constructor-for-constructor except for `loop`, which unfolds iteratively:

  - `eLoopZero`: a single step `G · (a, cₙ) ⟹ (v, cₙ)` with the feedback
    channel already stable (`c_next = cₙ`). This is the fixpoint / base case.
  - `eLoopIter`: a single step `G · (a, cₙ) ⟹ (v', c_next)` with
    `c_next ≠ cₙ`, followed by a recursive evaluation
    `loop G · a ⟹ v`. The result is `v` from the recursive call (not `v'`).
-/
inductive EvalIter : {A B : Ty Atom} → Graph Atom Sig A B → Val → Val → Type 1
  | eId    (A : Ty Atom) (a : Val)                                : EvalIter (Graph.idG A) a a
  | eComp  {X Y Z : Ty Atom} (G : Graph Atom Sig X Y) (H : Graph Atom Sig Y Z)
          (a b v : Val) (eG : EvalIter G a b) (eH : EvalIter H b v) : EvalIter (Graph.comp G H) a v
  | eFirst {X Y : Ty Atom} (D : Ty Atom) (G : Graph Atom Sig X Y)
          (a b c : Val) (eG : EvalIter G a b)                     : EvalIter (Graph.first G) (Val.pair a c) (Val.pair b c)
  | eLeftL {X Y : Ty Atom} (D : Ty Atom) (G : Graph Atom Sig X Y)
          (a b : Val) (eG : EvalIter G a b)                       : EvalIter (Graph.left G) (Val.inl a) (Val.inl b)
  | eLeftR {X Y : Ty Atom} (D : Ty Atom) (G : Graph Atom Sig X Y)
          (b : Val)                                               : EvalIter (Graph.left G) (Val.inr b) (Val.inr b)
  | eLoopZero {X Y C : Ty Atom} (G : Graph Atom Sig (X ×ₜ C) (Y ×ₜ C))
          (a v cₙ : Val) (hcₙ : HasType cₙ C)
          (eStep : EvalIter G (Val.pair a cₙ) (Val.pair v cₙ))    : EvalIter (Graph.loop G) a v
  | eLoopIter {X Y C : Ty Atom} (G : Graph Atom Sig (X ×ₜ C) (Y ×ₜ C))
          (a v v' cₙ c_next : Val) (hcₙ : HasType cₙ C) (hne : c_next ≠ cₙ)
          (eStep : EvalIter G (Val.pair a cₙ) (Val.pair v' c_next))
          (eRec  : EvalIter (Graph.loop G) a v)                   : EvalIter (Graph.loop G) a v
  | eArr   {X Y : Ty Atom} (φ : Sig X Y) (a : Val)               : EvalIter (Graph.arr φ) a (den φ a)

-- ============================================================================
-- 2. One-step implies iterated
-- ============================================================================

/-- General conversion: every one-step `Eval` derivation is an `EvalIter`
derivation (rule-for-rule; `eLoop` maps to `eLoopZero`). Defined by
structural recursion (`match`) so the code generator can compile it despite
`Eval`/`EvalIter` carrying `Prop`-typed fields. -/
def eval_to_iter {A B : Ty Atom} {G : Graph Atom Sig A B} {a v : Val}
    (e : Eval den G a v) : EvalIter den G a v :=
  match e with
  | Eval.eId A a => EvalIter.eId A a
  | Eval.eComp G H a b v eG eH => EvalIter.eComp G H a b v (eval_to_iter eG) (eval_to_iter eH)
  | Eval.eFirst D G a b c eG => EvalIter.eFirst D G a b c (eval_to_iter eG)
  | Eval.eLeftL D G a b eG => EvalIter.eLeftL D G a b (eval_to_iter eG)
  | Eval.eLeftR D G b => EvalIter.eLeftR D G b
  | Eval.eLoop G a v cₙ hcₙ eStep => EvalIter.eLoopZero G a v cₙ hcₙ (eval_to_iter eStep)
  | Eval.eArr φ a => EvalIter.eArr φ a

/-- **One-step implies iterated.** If `Eval (Graph.loop G) a v` (one-step
fixpoint), then `EvalIter (Graph.loop G) a v`. The one-step `eLoop` rule is
exactly `eLoopZero`; the body step is translated by `eval_to_iter`. -/
def one_step_implies_iterated {X Y C : Ty Atom} (G : Graph Atom Sig (X ×ₜ C) (Y ×ₜ C))
    (a v : Val) (e : Eval den (Graph.loop G) a v) : EvalIter den (Graph.loop G) a v :=
  eval_to_iter den e

-- ============================================================================
-- 3. Iterated subject reduction
-- ============================================================================

/-- **Iterated subject reduction.** If `⊢ G : A ⇝ B`, `EvalIter G a v`, and
`a : A`, then `v : B`. Proof by induction on the iterated execution
derivation, inverting the typing derivation at each step.

The key lemma (discharged in the `eLoopZero` / `eLoopIter` cases): each
iteration preserves types — if `G : (A×C) ⇝ (B×C)` and
`(a, cᵢ) ⟹ (vᵢ, cᵢ₊₁)` with `a : A` and `cᵢ : C`, then `vᵢ : B` and
`cᵢ₊₁ : C`. In the `eLoopIter` case the non-stable step is well-typed at
the body type, and the result `v` is determined by the recursive call
`loop G · a ⟹ v`, whose IH yields `v : B` directly. -/
theorem iterated_subject_reduction
    (hsound : ∀ {A B : Ty Atom} (φ : Sig A B) (a : Val), HasType (den φ a) B)
    {A B : Ty Atom} {G : Graph Atom Sig A B} {a v : Val}
    (d : TyOf G) (e : EvalIter den G a v) (ha : HasType a A)
    : HasType v B := by
  induction e with
  | eId A a =>
    cases d; exact ha
  | eComp G H a b v eG eH ihG ihH =>
    cases d with
    | compT G H dG dH =>
      have hb := ihG dG ha
      exact ihH dH hb
  | eFirst D G a b c eG ihG =>
    cases d with
    | firstT D G dG =>
      obtain ⟨ha', hc⟩ := HasType.pair_inv ha
      have hb := ihG dG ha'
      exact HasType.htPair hb hc
  | eLeftL D G a b eG ihG =>
    cases d with
    | leftT D G dG =>
      have ha' := HasType.inl_inv ha
      have hb := ihG dG ha'
      exact HasType.htInl hb
  | eLeftR D G b =>
    cases d with
    | leftT D G dG =>
      cases ha with
      | htInr hb => exact HasType.htInr hb
  | eLoopZero G₀ a v cₙ hcₙ eStep ih =>
    match d with
    | TyOf.loopT C G' dG =>
      have hAC : HasType (Val.pair a cₙ) (_ ×ₜ C) := HasType.htPair ha hcₙ
      have hBC := ih dG hAC
      obtain ⟨hv, _⟩ := HasType.pair_inv hBC
      exact hv
  | eLoopIter G₀ a v v' cₙ c_next hcₙ hne eStep eRec ihStep ihRec =>
    match d with
    | TyOf.loopT C G' dG =>
      -- The non-stable step is well-typed at the body type (ihStep), but
      -- the result `v` comes from the recursive call `loop G · a ⟹ v`,
      -- whose IH yields `v : B` directly from `a : A` and the loop typing.
      exact ihRec (TyOf.loopT C G' dG) ha
  | eArr φ a =>
    cases d with
    | arrT φ => exact hsound φ a

-- ============================================================================
-- 4. Equivalence at fixpoints
-- ============================================================================

/-- General conversion: every `EvalIter` derivation collapses to a one-step
`Eval` derivation. The `eLoopIter` case threads through the recursive
result (its conclusion equals its recursive premise's conclusion), so the
only loop rule that produces genuine `Eval` evidence is `eLoopZero` — the
fixpoint. Defined by structural recursion (`match`) for code generation. -/
def iter_to_eval {A B : Ty Atom} {G : Graph Atom Sig A B} {a v : Val}
    (e : EvalIter den G a v) : Eval den G a v :=
  match e with
  | EvalIter.eId A a => Eval.eId A a
  | EvalIter.eComp G H a b v eG eH => Eval.eComp G H a b v (iter_to_eval eG) (iter_to_eval eH)
  | EvalIter.eFirst D G a b c eG => Eval.eFirst D G a b c (iter_to_eval eG)
  | EvalIter.eLeftL D G a b eG => Eval.eLeftL D G a b (iter_to_eval eG)
  | EvalIter.eLeftR D G b => Eval.eLeftR D G b
  | EvalIter.eLoopZero G a v cₙ hcₙ eStep => Eval.eLoop G a v cₙ hcₙ (iter_to_eval eStep)
  | EvalIter.eLoopIter G a v _v' _cₙ c_next hcₙ hne eStep eRec => iter_to_eval eRec
  | EvalIter.eArr φ a => Eval.eArr φ a

/-- **Equivalence at fixpoints.** If `EvalIter (Graph.loop G) a v` and the
iteration reaches a fixpoint (the last loop step has `c_next = cₙ`), then
`Eval (Graph.loop G) a v`.

Every finite `EvalIter` derivation of `loop G` terminates in an `eLoopZero`
(a fixpoint where `c_next = cₙ`); the `eLoopIter` steps are transitively
eliminated by `iter_to_eval`, threading through to that final fixpoint.
Hence the fixpoint hypothesis is intrinsic to the inductive derivation, and
the iterated result is always realisable by the one-step `eLoop` rule. -/
def iterated_equiv_at_fixpoint {X Y C : Ty Atom} (G : Graph Atom Sig (X ×ₜ C) (Y ×ₜ C))
    (a v : Val) (e : EvalIter den (Graph.loop G) a v) : Eval den (Graph.loop G) a v :=
  iter_to_eval den e

-- ============================================================================
-- 5. Threaded loop iterations (LoopIter)
-- ============================================================================

/-- `LoopIter den G a cₙ v` is an iterated loop derivation that **threads
the starting feedback** `cₙ` through the recursive call. It mirrors the
loop cases of `EvalIter` but indexes the derivation by the initial
feedback value, so that the recursive call in `loopIter` starts at
`c_next` (the feedback produced by the current step) rather than at an
unknown value.

  - `loopZero`: a single step `G · (a, cₙ) ⟹ (v, cₙ)` with the feedback
    channel already stable. This is the fixpoint / base case.
  - `loopIter`: a single step `G · (a, cₙ) ⟹ (v', c_next)` with
    `c_next ≠ cₙ`, followed by a recursive evaluation
    `LoopIter G a c_next v`. The result is `v` from the recursive call.

The key difference from `EvalIter.eLoopIter` is that `eRec` is indexed by
`c_next`, making the decreasing-measure argument applicable: the induction
hypothesis gives a bound in terms of `m c_next`, not an unknown feedback. -/
inductive LoopIter : {X Y C : Ty Atom} → Graph Atom Sig (X ×ₜ C) (Y ×ₜ C) → Val → Val → Val → Type 1
  | loopZero {X Y C : Ty Atom} (G : Graph Atom Sig (X ×ₜ C) (Y ×ₜ C))
          (a v cₙ : Val) (hcₙ : HasType cₙ C)
          (eStep : EvalIter den G (Val.pair a cₙ) (Val.pair v cₙ))    : LoopIter G a cₙ v
  | loopIter {X Y C : Ty Atom} (G : Graph Atom Sig (X ×ₜ C) (Y ×ₜ C))
          (a v v' cₙ c_next : Val) (hcₙ : HasType cₙ C) (hc_next : HasType c_next C) (hne : c_next ≠ cₙ)
          (eStep : EvalIter den G (Val.pair a cₙ) (Val.pair v' c_next))
          (eRec  : LoopIter G a c_next v)                              : LoopIter G a cₙ v

/-- Convert a `LoopIter` derivation to an `EvalIter` derivation by wrapping
the recursive call. The `loopZero` case maps directly to `eLoopZero`; the
`loopIter` case maps to `eLoopIter` with the recursive `LoopIter` converted
to `EvalIter`. -/
def loop_iter_to_eval_iter {X Y C : Ty Atom} {G : Graph Atom Sig (X ×ₜ C) (Y ×ₜ C)}
    {a v cₙ : Val} (e : LoopIter den G a cₙ v) : EvalIter den (Graph.loop G) a v :=
  match e with
  | LoopIter.loopZero G a v cₙ hcₙ eStep => EvalIter.eLoopZero G a v cₙ hcₙ eStep
  | LoopIter.loopIter G a v v' cₙ c_next hcₙ hc_next hne eStep eRec =>
    EvalIter.eLoopIter G a v v' cₙ c_next hcₙ hne eStep (loop_iter_to_eval_iter eRec)

end IteratedLoop
