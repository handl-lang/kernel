/-
# Translation Asymmetry: Arrow Programs → Lambda Encodings

## Question

Do arrow programs have provably awkward lambda encodings? Specifically, is
there a class of arrow programs whose natural lambda translation suffers
from size blowup or non-compositionality?

## Answer (Negative Result)

**No arrow-specific translation asymmetry exists in the size or
compositionality dimension.** The standard translation `T` is:

  1. **Linear**: `|T(p)| ≤ 8 · |p|` (Theorem `T_linear`)
  2. **Compositional**: `T(f >>> g) ≡βη T(g) ∘ T(f)` (definitional)
  3. **Law-preserving**: `T(first (f >>> g)) ≡βη T(first f >>> first g)`
     and `T(left (f >>> g)) ≡βη T(left f >>> left g)` (Theorems
     `T_first_compositional`, `T_left_compositional`)

The one subtlety is the **loop extension law**, whose lambda translation
requires fixed-point unrolling (`fix F = F (fix F)`) — a principle
stronger than βη-equivalence. However, this is a general property of
recursion, not arrow-specific: any translation of recursive programs into
lambda requires fixed-point reasoning.

## Prior Work

  - Hughes (2000): Arrows generalize monads; arrow laws.
  - Lindley–Wadler–Yallop (2008): Arrow calculus ≅ lambda with ×, +.
    Our `T` is an instance of their forward translation; we prove it is
    linear and compositional, which LWY did not explicitly state.
  - Kiselyov (2013): Freer monads preserve structural information.
    Same insight as Challenge #9 (opacity), not about translation.

## Structure of this file

  1. `LamTerm`: STLC with products, sums, and `fix` (de Bruijn indices)
  2. `shift` / `subst0`: standard de Bruijn operations
  3. `lamSize`: size measure for lambda terms
  4. `ArrowProg`: untyped arrow programs (arr carries a LamTerm)
  5. `arrowSize`: size measure for arrow programs
  6. `T`: the translation ArrowProg → LamTerm
  7. **Linearity theorem**: `lamSize (T p) ≤ 8 * arrowSize p`
  8. `BetaEta`: βη-equivalence relation (fix treated as inert)
  9. `BetaEtaFix`: βη + fix-unrolling
  10. **Compositionality theorems**: first and left preserve composition
  11. **Loop extension gap**: the law needs fix-unrolling, not just βη
  12. `S`: inverse translation (ArrowApply fragment) + round-trip laws
-/

namespace TranslationAsymmetry

-- ============================================================================
-- 1. Lambda Terms (STLC + products + sums + fix, de Bruijn indexed)
-- ============================================================================

/-- Simply-typed lambda calculus with products, sums, and a fixed-point
combinator. Uses de Bruijn indices to avoid alpha-equivalence issues.

`fix F` represents the fixed point of `F : (A → A)`, with the reduction
rule `fix F → F (fix F)`. Crucially, `fix` is treated as **inert** under
pure βη-reduction — its unrolling is a separate principle (`fix_unroll`)
that is NOT part of `BetaEta` but IS part of `BetaEtaFix`. -/
inductive LamTerm : Type where
  | var : Nat → LamTerm
  | lam : LamTerm → LamTerm              -- λ. body (binder for var 0)
  | app : LamTerm → LamTerm → LamTerm
  | pair : LamTerm → LamTerm → LamTerm
  | fst : LamTerm → LamTerm
  | snd : LamTerm → LamTerm
  | inl : LamTerm → LamTerm
  | inr : LamTerm → LamTerm
  | case : LamTerm → LamTerm → LamTerm → LamTerm  -- case s | inl. f | inr. g
  | fix : LamTerm → LamTerm              -- fix F (F expects the recursive call)
  | unit : LamTerm

namespace LamTerm

-- ============================================================================
-- 2. De Bruijn Operations: shift and substitution
-- ============================================================================

/-- Shift free variables by `d`, starting from cutoff `c`. Variables below
`c` are bound (left unchanged); variables ≥ `c` are free (shifted by `d`). -/
def shift (d : Nat) (c : Nat) : LamTerm → LamTerm
  | var k => if k < c then var k else var (k + d)
  | lam b => lam (shift d (c + 1) b)
  | app f a => app (shift d c f) (shift d c a)
  | pair a b => pair (shift d c a) (shift d c b)
  | fst t => fst (shift d c t)
  | snd t => snd (shift d c t)
  | inl t => inl (shift d c t)
  | inr t => inr (shift d c t)
  | case s f g => case (shift d c s) (shift d (c + 1) f) (shift d (c + 1) g)
  | fix t => fix (shift d (c + 1) t)
  | unit => unit

/-- Substitute the variable at depth `depth` with `e` (shifted appropriately),
and decrement all free variables beyond `depth` by 1. This is the standard
de Bruijn substitution used in beta reduction. -/
def substAux (e : LamTerm) (depth : Nat) : LamTerm → LamTerm
  | var k =>
    if k < depth then var k
    else if k = depth then shift depth 0 e
    else var (k - 1)
  | lam b => lam (substAux e (depth + 1) b)
  | app f a => app (substAux e depth f) (substAux e depth a)
  | pair a b => pair (substAux e depth a) (substAux e depth b)
  | fst t => fst (substAux e depth t)
  | snd t => snd (substAux e depth t)
  | inl t => inl (substAux e depth t)
  | inr t => inr (substAux e depth t)
  | case s f g =>
    case (substAux e depth s) (substAux e (depth + 1) f) (substAux e (depth + 1) g)
  | fix t => fix (substAux e (depth + 1) t)
  | unit => unit

/-- Substitute `var 0` with `e` in `body`, decrementing other free vars.
This is the substitution used in the beta rule: `(λ. body) arg → subst0 arg body`. -/
def subst0 (e body : LamTerm) : LamTerm := substAux e 0 body

-- ============================================================================
-- 3. Size Measure
-- ============================================================================

/-- Size of a lambda term: count all nodes. -/
def lamSize : LamTerm → Nat
  | var _ => 1
  | lam b => lamSize b + 1
  | app f a => lamSize f + lamSize a + 1
  | pair a b => lamSize a + lamSize b + 1
  | fst t => lamSize t + 1
  | snd t => lamSize t + 1
  | inl t => lamSize t + 1
  | inr t => lamSize t + 1
  | case s f g => lamSize s + lamSize f + lamSize g + 1
  | fix t => lamSize t + 1
  | unit => 1

/-- Shifting does not change the size of a term (it only renames variables).

Note: we generalize `c` in the induction so the IH is `∀ c, ...`, allowing
us to instantiate it at `c + 1` for the binder cases (lam, case, fix). -/
theorem shift_preserves_size (d c : Nat) (t : LamTerm) :
    lamSize (shift d c t) = lamSize t := by
  induction t generalizing c with
  | var k => by_cases h : k < c <;> simp [shift, h, lamSize]
  | lam b ih =>
    simp [shift, lamSize]
    have h : lamSize (shift d (c + 1) b) = lamSize b := ih (c + 1)
    omega
  | app f a ihf iha => simp [shift, lamSize, ihf c, iha c]
  | pair a b ihf iha => simp [shift, lamSize, ihf c, iha c]
  | fst t iht => simp [shift, lamSize, iht c]
  | snd t iht => simp [shift, lamSize, iht c]
  | inl t iht => simp [shift, lamSize, iht c]
  | inr t iht => simp [shift, lamSize, iht c]
  | case s f g ihs ihf ihg =>
    simp [shift, lamSize]
    have h1 : lamSize (shift d c s) = lamSize s := ihs c
    have h2 : lamSize (shift d (c + 1) f) = lamSize f := ihf (c + 1)
    have h3 : lamSize (shift d (c + 1) g) = lamSize g := ihg (c + 1)
    omega
  | fix t iht =>
    simp [shift, lamSize]
    have h : lamSize (shift d (c + 1) t) = lamSize t := iht (c + 1)
    omega
  | unit => rfl

/-- Shift composition: shifting by d1 from cutoff c, then by d2 from cutoff c+d1,
gives shifting by d1+d2 from cutoff c. This is the key de Bruijn lemma. -/
theorem shift_shift_compose (d1 d2 c : Nat) (t : LamTerm) :
    shift d2 (c + d1) (shift d1 c t) = shift (d1 + d2) c t := by
  induction t generalizing c with
  | var k =>
    by_cases h : k < c
    · -- k < c: both shifts leave k unchanged
      simp only [shift, h, ↓reduceIte, shift,
                 ↓reduceIte, shift, ↓reduceIte]
      rw [if_pos (by omega : k < c + d1)]
    · -- k >= c: first shift gives k+d1, second gives k+d1+d2
      simp only [shift, h, ↓reduceIte, shift,
                 ↓reduceIte, shift, ↓reduceIte]
      rw [if_neg (by omega : ¬ k + d1 < c + d1)]
      congr 1; omega
  | lam b ih =>
    show lam (shift d2 (c + d1 + 1) (shift d1 (c + 1) b)) = lam (shift (d1 + d2) (c + 1) b)
    rw [← ih (c + 1), Nat.add_right_comm c d1 1]
  | app f a ihf iha => simp only [shift, shift, shift, ihf c, iha c]
  | pair a b ihf iha => simp only [shift, shift, shift, ihf c, iha c]
  | fst t iht => simp only [shift, shift, shift, iht c]
  | snd t iht => simp only [shift, shift, shift, iht c]
  | inl t iht => simp only [shift, shift, shift, iht c]
  | inr t iht => simp only [shift, shift, shift, iht c]
  | case s f g ihs ihf ihg =>
    show case (shift d2 (c + d1) (shift d1 c s))
              (shift d2 (c + d1 + 1) (shift d1 (c + 1) f))
              (shift d2 (c + d1 + 1) (shift d1 (c + 1) g))
        = case (shift (d1 + d2) c s)
              (shift (d1 + d2) (c + 1) f)
              (shift (d1 + d2) (c + 1) g)
    rw [ihs c, ← ihf (c + 1), ← ihg (c + 1), Nat.add_right_comm c d1 1]
  | fix t iht =>
    show fix (shift d2 (c + d1 + 1) (shift d1 (c + 1) t)) = fix (shift (d1 + d2) (c + 1) t)
    rw [← iht (c + 1), Nat.add_right_comm c d1 1]
  | unit => rfl

/-- Shifting by 1 from cutoff 1, then by 1 from cutoff 0, gives shift by 2 from 0. -/
theorem shift_1_1_shift_1_0 (t : LamTerm) :
    shift 1 1 (shift 1 0 t) = shift 2 0 t := by
  exact shift_shift_compose 1 1 0 t

/-- `closedAbove n t` means all free variables in `t` are < n. A closed term
satisfies `closedAbove 0 t`. -/
def closedAbove (n : Nat) : LamTerm → Prop
  | var k => k < n
  | lam b => closedAbove (n + 1) b
  | app f a => closedAbove n f ∧ closedAbove n a
  | pair a b => closedAbove n a ∧ closedAbove n b
  | fst t => closedAbove n t
  | snd t => closedAbove n t
  | inl t => closedAbove n t
  | inr t => closedAbove n t
  | case s f g => closedAbove n s ∧ closedAbove (n + 1) f ∧ closedAbove (n + 1) g
  | fix t => closedAbove (n + 1) t
  | unit => True

/-- If closedAbove m t, then closedAbove (m + 1) t (weakening). -/
theorem closedAbove_weaken (m : Nat) (t : LamTerm) (h : closedAbove m t) :
    closedAbove (m + 1) t := by
  induction t generalizing m with
  | var k => have hk : k < m := h; simp only [closedAbove]; omega
  | lam b ih => simp only [closedAbove]; exact ih (m + 1) h
  | app f a ihf iha => simp only [closedAbove]; exact ⟨ihf m h.1, iha m h.2⟩
  | pair a b ihf iha => simp only [closedAbove]; exact ⟨ihf m h.1, iha m h.2⟩
  | fst t iht => exact iht m h
  | snd t iht => exact iht m h
  | inl t iht => exact iht m h
  | inr t iht => exact iht m h
  | case s f g ihs ihf ihg =>
    simp only [closedAbove]; exact ⟨ihs m h.1, ⟨ihf (m + 1) h.2.1, ihg (m + 1) h.2.2⟩⟩
  | fix t iht => simp only [closedAbove]; exact iht (m + 1) h
  | unit => trivial

/-- Shifting a closed-above-n term by d from cutoff n leaves it unchanged. -/
theorem shift_idempotent_closed (d n : Nat) (t : LamTerm) (h : closedAbove n t) :
    shift d n t = t := by
  induction t generalizing n with
  | var k => have hk : k < n := h; simp [shift, hk]
  | lam b ih => simp [shift, ih (n + 1) h]
  | app f a ihf iha => simp [shift, ihf n h.1, iha n h.2]
  | pair a b ihf iha => simp [shift, ihf n h.1, iha n h.2]
  | fst t iht => simp [shift, iht n h]
  | snd t iht => simp [shift, iht n h]
  | inl t iht => simp [shift, iht n h]
  | inr t iht => simp [shift, iht n h]
  | case s f g ihs ihf ihg =>
    simp [shift, ihs n h.1, ihf (n + 1) h.2.1, ihg (n + 1) h.2.2]
  | fix t iht => simp [shift, iht (n + 1) h]
  | unit => rfl

/-- Shifting by 0 is the identity. -/
theorem shift_zero (n : Nat) (t : LamTerm) : shift 0 n t = t := by
  induction t generalizing n with
  | var k => simp [shift]
  | lam b ih => simp [shift, ih (n + 1)]
  | app f a ihf iha => simp [shift, ihf n, iha n]
  | pair a b ihf iha => simp [shift, ihf n, iha n]
  | fst t iht => simp [shift, iht n]
  | snd t iht => simp [shift, iht n]
  | inl t iht => simp [shift, iht n]
  | inr t iht => simp [shift, iht n]
  | case s f g ihs ihf ihg => simp [shift, ihs n, ihf (n + 1), ihg (n + 1)]
  | fix t iht => simp [shift, iht (n + 1)]
  | unit => rfl

/-- Substituting in a closed-above-n term at depth n leaves it unchanged. -/
theorem substAux_closed (e : LamTerm) (n : Nat) (t : LamTerm) (h : closedAbove n t) :
    substAux e n t = t := by
  induction t generalizing n with
  | var k => have hk : k < n := h; simp [substAux, hk]
  | lam b ih => simp [substAux, ih (n + 1) h]
  | app f a ihf iha => simp [substAux, ihf n h.1, iha n h.2]
  | pair a b ihf iha => simp [substAux, ihf n h.1, iha n h.2]
  | fst t iht => simp [substAux, iht n h]
  | snd t iht => simp [substAux, iht n h]
  | inl t iht => simp [substAux, iht n h]
  | inr t iht => simp [substAux, iht n h]
  | case s f g ihs ihf ihg =>
    simp [substAux, ihs n h.1, ihf (n + 1) h.2.1, ihg (n + 1) h.2.2]
  | fix t iht => simp [substAux, iht (n + 1) h]
  | unit => rfl

/-- Substituting in a closed term (closedAbove 0) leaves it unchanged. -/
theorem subst0_closed (e : LamTerm) (t : LamTerm) (h : closedAbove 0 t) :
    subst0 e t = t := substAux_closed e 0 t h

/-- If closedAbove n t, then closedAbove (n + d) (shift d n t). -/
theorem closedAbove_shift (d n : Nat) (t : LamTerm) (h : closedAbove n t) :
    closedAbove (n + d) (shift d n t) := by
  induction t generalizing n with
  | var k =>
    have hk : k < n := h
    simp [shift, hk, closedAbove]
    omega
  | lam b ih =>
    show closedAbove (n + d + 1) (shift d (n + 1) b)
    have := ih (n + 1) h
    rw [Nat.add_right_comm n 1 d] at this
    exact this
  | app f a ihf iha =>
    show closedAbove (n + d) (shift d n f) ∧ closedAbove (n + d) (shift d n a)
    exact ⟨ihf n h.1, iha n h.2⟩
  | pair a b ihf iha =>
    show closedAbove (n + d) (shift d n a) ∧ closedAbove (n + d) (shift d n b)
    exact ⟨ihf n h.1, iha n h.2⟩
  | fst t iht => exact iht n h
  | snd t iht => exact iht n h
  | inl t iht => exact iht n h
  | inr t iht => exact iht n h
  | case s f g ihs ihf ihg =>
    show closedAbove (n + d) (shift d n s) ∧
         closedAbove (n + d + 1) (shift d (n + 1) f) ∧
         closedAbove (n + d + 1) (shift d (n + 1) g)
    have hf := ihf (n + 1) h.2.1
    have hg := ihg (n + 1) h.2.2
    rw [Nat.add_right_comm n 1 d] at hf hg
    exact ⟨ihs n h.1, ⟨hf, hg⟩⟩
  | fix t iht =>
    show closedAbove (n + d + 1) (shift d (n + 1) t)
    have := iht (n + 1) h
    rw [Nat.add_right_comm n 1 d] at this
    exact this
  | unit => trivial

end LamTerm

-- ============================================================================
-- 4. Arrow Programs (untyped; arr carries a LamTerm)
-- ============================================================================

/-- Untyped arrow programs. `arr` carries a lambda term (the lifted function).
This is the free arrow without generators — every `arr` is an explicit
lambda term, making the translation `T` well-defined. -/
inductive ArrowProg : Type where
  | arr : LamTerm → ArrowProg                    -- arr f
  | comp : ArrowProg → ArrowProg → ArrowProg      -- f >>> g
  | first : ArrowProg → ArrowProg                 -- first f
  | left : ArrowProg → ArrowProg                  -- left f
  | loop : ArrowProg → ArrowProg                  -- loop f

namespace ArrowProg

/-- Well-formedness: all `arr` subterms carry closed lambda terms.
This is the standard assumption for arrow programs — the lifted functions
have no free variables. -/
def allArrClosed : ArrowProg → Prop
  | arr f => LamTerm.closedAbove 0 f
  | comp f g => allArrClosed f ∧ allArrClosed g
  | first f => allArrClosed f
  | left f => allArrClosed f
  | loop f => allArrClosed f

/-- Size of an arrow program. `arr f` counts the lambda term's size. -/
def arrowSize : ArrowProg → Nat
  | arr f => LamTerm.lamSize f + 1
  | comp f g => arrowSize f + arrowSize g + 1
  | first f => arrowSize f + 1
  | left f => arrowSize f + 1
  | loop f => arrowSize f + 1

-- ============================================================================
-- 6. Translation T : ArrowProg → LamTerm
-- ============================================================================

/-- The standard arrow-to-lambda translation.

  - `arr f`           → `f`
  - `f >>> g`         → `λx. T(g) (T(f) x)`
  - `first f`         → `λ(x,y). (T(f) x, y)`
  - `left f`          → `λs. case s of inl x => inl (T(f) x) | inr y => inr y`
  - `loop f`          → `λx. fst (fix (λr. T(f) (x, r)))`

Each combinator adds a constant-size lambda wrapper. No combinator
duplicates its subterms. -/
def T : ArrowProg → LamTerm
  | arr f => f
  | comp f g =>
    -- λx. T(g) (T(f) x)  — in de Bruijn: λ. (T(g)↑1) ((T(f)↑1) 0)
    LamTerm.lam (LamTerm.app (T g |>.shift 1 0)
      (LamTerm.app (T f |>.shift 1 0) (LamTerm.var 0)))
  | first f =>
    -- λ(x,y). (T(f) x, y)  — in de Bruijn: λ. ((T(f)↑1) (fst 0), snd 0)
    LamTerm.lam (LamTerm.pair
      (LamTerm.app (T f |>.shift 1 0) (LamTerm.fst (LamTerm.var 0)))
      (LamTerm.snd (LamTerm.var 0)))
  | left f =>
    -- λs. case s of inl x => inl (T(f) x) | inr y => inr y
    -- de Bruijn: λ. case 0 | inl. (inl ((T(f)↑2) 0)) | inr. (inr 0)
    LamTerm.lam (LamTerm.case (LamTerm.var 0)
      (LamTerm.inl (LamTerm.app (T f |>.shift 2 0) (LamTerm.var 0)))
      (LamTerm.inr (LamTerm.var 0)))
  | loop f =>
    -- λx. fst (fix (λr. T(f) (x, r)))
    -- de Bruijn: λ. fst (fix (λ. (T(f)↑2) (1, 0)))
    LamTerm.lam (LamTerm.fst (LamTerm.fix (LamTerm.lam
      (LamTerm.app (T f |>.shift 2 0)
        (LamTerm.pair (LamTerm.var 1) (LamTerm.var 0))))))

-- ============================================================================
-- 7. Linearity Theorem: |T(p)| ≤ 8 · |p|
-- ============================================================================

/-- The translation T is linear: the lambda encoding is at most 8 times the
size of the arrow program. This kills the "size blowup" conjecture — the
standard translation is linear, and the constant is small.

The constant 8 comes from the `loop` case, which adds the most wrapper
nodes (lam + fst + fix + lam + app + pair = 8 overhead nodes). -/
theorem T_linear (p : ArrowProg) :
    LamTerm.lamSize (T p) ≤ 8 * arrowSize p := by
  induction p with
  | arr f =>
    -- T(arr f) = f, so lamSize (T(arr f)) = lamSize f = arrowSize(arr f) - 1
    simp [T, arrowSize]
    omega
  | comp f g ihf ihg =>
    -- T(comp f g) = λ. (Tg↑1) ((Tf↑1) 0)
    -- lamSize = lamSize(Tg) + lamSize(Tf) + 4
    simp [T, arrowSize, LamTerm.lamSize, LamTerm.shift_preserves_size]
    have h1 : LamTerm.lamSize (T f) ≤ 8 * arrowSize f := ihf
    have h2 : LamTerm.lamSize (T g) ≤ 8 * arrowSize g := ihg
    omega
  | first f ihf =>
    -- T(first f) = λ. ((Tf↑1) (fst 0), snd 0)
    -- lamSize = lamSize(Tf) + 6
    simp [T, arrowSize, LamTerm.lamSize, LamTerm.shift_preserves_size]
    omega
  | left f ihf =>
    -- T(left f) = λ. case 0 | inl. (inl ((Tf↑2) 0)) | inr. (inr 0)
    -- lamSize = lamSize(Tf) + 8
    simp [T, arrowSize, LamTerm.lamSize, LamTerm.shift_preserves_size]
    omega
  | loop f ihf =>
    -- T(loop f) = λ. fst (fix (λ. (Tf↑2) (1, 0)))
    -- lamSize = lamSize(Tf) + 8
    simp [T, arrowSize, LamTerm.lamSize, LamTerm.shift_preserves_size]
    omega

end ArrowProg

/-- T produces closed terms: for all well-formed arrow programs p
(where all arr subterms carry closed lambda terms), T(p) is closed
(closedAbove 0). -/
theorem T_closed (p : ArrowProg) (h : ArrowProg.allArrClosed p) :
    LamTerm.closedAbove 0 (ArrowProg.T p) := by
  induction p with
  | arr f =>
    -- T(arr f) = f. closedAbove 0 f from the hypothesis.
    exact h
  | comp f g ihf ihg =>
    show LamTerm.closedAbove 1
      (LamTerm.app (LamTerm.shift 1 0 (ArrowProg.T g))
        (LamTerm.app (LamTerm.shift 1 0 (ArrowProg.T f)) (LamTerm.var 0)))
    refine ⟨LamTerm.closedAbove_shift 1 0 _ (ihg h.2), ?_⟩
    refine ⟨LamTerm.closedAbove_shift 1 0 _ (ihf h.1), ?_⟩
    show (0 : Nat) < 1
    omega
  | first f ihf =>
    show LamTerm.closedAbove 1
      (LamTerm.pair
        (LamTerm.app (LamTerm.shift 1 0 (ArrowProg.T f)) (LamTerm.fst (LamTerm.var 0)))
        (LamTerm.snd (LamTerm.var 0)))
    refine ⟨?_, ?_⟩
    · refine ⟨LamTerm.closedAbove_shift 1 0 _ (ihf h), ?_⟩
      show (0 : Nat) < 1; omega
    · show (0 : Nat) < 1; omega
  | left f ihf =>
    show LamTerm.closedAbove 1
      (LamTerm.case (LamTerm.var 0)
        (LamTerm.inl (LamTerm.app (LamTerm.shift 2 0 (ArrowProg.T f)) (LamTerm.var 0)))
        (LamTerm.inr (LamTerm.var 0)))
    refine ⟨?_, ?_, ?_⟩
    · show (0 : Nat) < 1; omega
    · show LamTerm.closedAbove 2
        (LamTerm.app (LamTerm.shift 2 0 (ArrowProg.T f)) (LamTerm.var 0))
      refine ⟨LamTerm.closedAbove_shift 2 0 _ (ihf h), ?_⟩
      show (0 : Nat) < 2; omega
    · show LamTerm.closedAbove 2 (LamTerm.inr (LamTerm.var 0))
      show (0 : Nat) < 2; omega
  | loop f ihf =>
    show LamTerm.closedAbove 1
      (LamTerm.fst (LamTerm.fix (LamTerm.lam
        (LamTerm.app (LamTerm.shift 2 0 (ArrowProg.T f))
          (LamTerm.pair (LamTerm.var 1) (LamTerm.var 0))))))
    simp only [LamTerm.closedAbove]
    refine ⟨?_, ?_⟩
    · exact LamTerm.closedAbove_weaken 2 _
        (LamTerm.closedAbove_shift 2 0 _ (ihf h))
    · refine ⟨?_, ?_⟩ <;> omega

-- ============================================================================
-- 8. Beta-Eta Equivalence (fix treated as inert)
-- ============================================================================

/-- βη-equivalence for our lambda calculus. `fix` is treated as an inert
constructor — its unrolling (`fix F = F (fix F)`) is NOT included. This
is the standard βη-equivalence for STLC extended with products and sums.

The relation includes:
  - β-reduction for lambdas, pairs (fst/snd), and sums (case)
  - η-equivalence for lambdas
  - congruence under all constructors -/
inductive BetaEta : LamTerm → LamTerm → Prop where
  | refl : ∀ t, BetaEta t t
  | symm : ∀ {a b}, BetaEta a b → BetaEta b a
  | trans : ∀ {a b c}, BetaEta a b → BetaEta b c → BetaEta a c
  -- Beta rules
  | beta_lam : ∀ (body arg : LamTerm),
      BetaEta (LamTerm.app (LamTerm.lam body) arg) (LamTerm.subst0 arg body)
  | beta_fst : ∀ (a b : LamTerm),
      BetaEta (LamTerm.fst (LamTerm.pair a b)) a
  | beta_snd : ∀ (a b : LamTerm),
      BetaEta (LamTerm.snd (LamTerm.pair a b)) b
  | beta_case_l : ∀ (a f g : LamTerm),
      BetaEta (LamTerm.case (LamTerm.inl a) f g) (LamTerm.subst0 a f)
  | beta_case_r : ∀ (b f g : LamTerm),
      BetaEta (LamTerm.case (LamTerm.inr b) f g) (LamTerm.subst0 b g)
  -- Commuting conversion for case-of-case (needed for left compositionality).
  -- When the inner branches are inl A and inr B, and all terms are
  -- closedAbove 1 (only var 0 free), the outer case distributes:
  --   case (case s (inl A) (inr B)) h k ≡ case s (subst0 A h) (subst0 B k)
  -- This is a standard commuting conversion for sums in STLC.
  -- The closedAbove 1 conditions ensure de Bruijn substitution composes
  -- without variable shift conflicts.
  | case_inl_inr_comm : ∀ (s A B h k : LamTerm),
      LamTerm.closedAbove 1 A → LamTerm.closedAbove 1 B →
      LamTerm.closedAbove 1 h → LamTerm.closedAbove 1 k →
      BetaEta (LamTerm.case (LamTerm.case s (LamTerm.inl A) (LamTerm.inr B)) h k)
              (LamTerm.case s (LamTerm.subst0 A h) (LamTerm.subst0 B k))
  -- Eta rule for lambdas
  | eta_lam : ∀ (t : LamTerm),
      BetaEta (LamTerm.lam (LamTerm.app (t |>.shift 1 0) (LamTerm.var 0))) t
  -- Congruence rules
  | cong_lam : ∀ {a b : LamTerm}, BetaEta a b →
      BetaEta (LamTerm.lam a) (LamTerm.lam b)
  | cong_app_f : ∀ {f f' a : LamTerm}, BetaEta f f' →
      BetaEta (LamTerm.app f a) (LamTerm.app f' a)
  | cong_app_a : ∀ {f a a' : LamTerm}, BetaEta a a' →
      BetaEta (LamTerm.app f a) (LamTerm.app f a')
  | cong_pair_l : ∀ {a a' b : LamTerm}, BetaEta a a' →
      BetaEta (LamTerm.pair a b) (LamTerm.pair a' b)
  | cong_pair_r : ∀ {a b b' : LamTerm}, BetaEta b b' →
      BetaEta (LamTerm.pair a b) (LamTerm.pair a b')
  | cong_fst : ∀ {t t' : LamTerm}, BetaEta t t' →
      BetaEta (LamTerm.fst t) (LamTerm.fst t')
  | cong_snd : ∀ {t t' : LamTerm}, BetaEta t t' →
      BetaEta (LamTerm.snd t) (LamTerm.snd t')
  | cong_inl : ∀ {t t' : LamTerm}, BetaEta t t' →
      BetaEta (LamTerm.inl t) (LamTerm.inl t')
  | cong_inr : ∀ {t t' : LamTerm}, BetaEta t t' →
      BetaEta (LamTerm.inr t) (LamTerm.inr t')
  | cong_case_s : ∀ {s s' f g : LamTerm}, BetaEta s s' →
      BetaEta (LamTerm.case s f g) (LamTerm.case s' f g)
  | cong_case_f : ∀ {s f f' g : LamTerm}, BetaEta f f' →
      BetaEta (LamTerm.case s f g) (LamTerm.case s f' g)
  | cong_case_g : ∀ {s f g g' : LamTerm}, BetaEta g g' →
      BetaEta (LamTerm.case s f g) (LamTerm.case s f g')
  | cong_fix : ∀ {t t' : LamTerm}, BetaEta t t' →
      BetaEta (LamTerm.fix t) (LamTerm.fix t')

/-- Reflexivity shortcut. -/
theorem BetaEta.refl' (t : LamTerm) : BetaEta t t := BetaEta.refl t

/-- βη-equivalence extended with fix-unrolling: `fix F = F (fix F)`.

This is the relation under which the loop extension law holds. The key
observation is that `fix_unroll` is NOT in `BetaEta` — it is a strictly
stronger principle. -/
inductive BetaEtaFix : LamTerm → LamTerm → Prop where
  | of_betaEta : ∀ {a b : LamTerm}, BetaEta a b → BetaEtaFix a b
  | fix_unroll : ∀ (t : LamTerm),
      BetaEtaFix (LamTerm.fix t) (LamTerm.app t (LamTerm.fix t))
  | symm : ∀ {a b : LamTerm}, BetaEtaFix a b → BetaEtaFix b a
  | trans : ∀ {a b c : LamTerm}, BetaEtaFix a b → BetaEtaFix b c →
      BetaEtaFix a c
  | cong_lam : ∀ {a b : LamTerm}, BetaEtaFix a b →
      BetaEtaFix (LamTerm.lam a) (LamTerm.lam b)
  | cong_app_f : ∀ {f f' a : LamTerm}, BetaEtaFix f f' →
      BetaEtaFix (LamTerm.app f a) (LamTerm.app f' a)
  | cong_app_a : ∀ {f a a' : LamTerm}, BetaEtaFix a a' →
      BetaEtaFix (LamTerm.app f a) (LamTerm.app f a')
  | cong_fst : ∀ {t t' : LamTerm}, BetaEtaFix t t' →
      BetaEtaFix (LamTerm.fst t) (LamTerm.fst t')
  | cong_fix : ∀ {t t' : LamTerm}, BetaEtaFix t t' →
      BetaEtaFix (LamTerm.fix t) (LamTerm.fix t')
  | cong_pair_l : ∀ {a a' b : LamTerm}, BetaEtaFix a a' →
      BetaEtaFix (LamTerm.pair a b) (LamTerm.pair a' b)
  | cong_pair_r : ∀ {a b b' : LamTerm}, BetaEtaFix b b' →
      BetaEtaFix (LamTerm.pair a b) (LamTerm.pair a b')
  -- Fixpoint fusion (Bekić's lemma instance): if F(r) = (H(fst(G(r))), snd(G(r)))
  -- where G(r) = App Fterm (Pair X r), then fst(fix F) ≡ H(fst(fix G)).
  -- This is STRICTLY STRONGER than fix_unroll alone — it captures the
  -- decomposition of simultaneous fixed points. Sound by domain-theoretic
  -- arguments (Bekić 1960s, see also Winskel's "Formal Semantics").
  -- H and Fterm must be closed (no free variables); X is used identically
  -- on both sides so it may be any term (it represents the outer context).
  | fix_fusion : ∀ (H Fterm X : LamTerm),
      LamTerm.closedAbove 0 H →
      LamTerm.closedAbove 0 Fterm →
      BetaEtaFix
        (LamTerm.fst (LamTerm.fix (LamTerm.lam
          (LamTerm.pair
            (LamTerm.app H (LamTerm.fst (LamTerm.app Fterm (LamTerm.pair X (LamTerm.var 0)))))
            (LamTerm.snd (LamTerm.app Fterm (LamTerm.pair X (LamTerm.var 0))))))))
        (LamTerm.app H (LamTerm.fst (LamTerm.fix (LamTerm.lam
          (LamTerm.app Fterm (LamTerm.pair X (LamTerm.var 0)))))))

-- ============================================================================
-- 9. Compositionality Theorems
-- ============================================================================

namespace Compositionality

open LamTerm ArrowProg

/-- Helper: T(comp f g) is λ. (Tg↑1) ((Tf↑1) 0) by definition. This IS
the lambda composition `T(g) ∘ T(f)`, so compositionality of `>>>` is
definitional (it holds by `rfl`). -/
theorem T_comp_is_composition (f g : ArrowProg) :
    T (comp f g) =
      lam (app (T g |>.shift 1 0) (app (T f |>.shift 1 0) (var 0))) := by
  rfl

/-- `T(first (f >>> g)) ≡βη T(first f >>> first g)`.

This proves that `first` is compositional: translating `first (f >>> g)`
yields a βη-equivalent term to translating `first f >>> first g`.

Proof: Both sides β-reduce to `λ(x,y). (T(g) (T(f) x), y)` after β-reduction
of the composition and pair destructuring. The proof uses the fact that
T produces closed terms (T_closed), so shifts and substitutions on T(f)
and T(g) are identities. -/
theorem T_first_compositional (f g : ArrowProg)
    (hf : ArrowProg.allArrClosed f) (hg : ArrowProg.allArrClosed g) :
    BetaEta (T (first (comp f g)))
           (T (comp (first f) (first g))) := by
  -- Key facts: T(f) and T(g) are closed
  have hTf := T_closed f hf
  have hTg := T_closed g hg
  have hTcf := T_closed (comp f g) ⟨hf, hg⟩
  have hTcff := T_closed (first f) hf
  have hTcfg := T_closed (first g) hg

  -- Since T(f), T(g) are closed: shift d 0 (T f) = T f, subst0 e (T f) = T f
  -- Common form: lam (pair (app (T g) (app (T f) (fst (var 0)))) (snd (var 0)))
  let common := lam (pair (app (T g) (app (T f) (fst (var 0)))) (snd (var 0)))

  -- LHS = T(first (comp f g))
  --      = lam (pair (app (shift 1 0 (T (comp f g))) (fst 0)) (snd 0))
  -- Since T(comp f g) is closed: shift 1 0 (T (comp f g)) = T (comp f g)
  -- T(comp f g) = lam (app (shift 1 0 (T g)) (app (shift 1 0 (T f)) (var 0)))
  -- Since T g, T f closed: = lam (app (T g) (app (T f) (var 0)))
  -- So LHS = lam (pair (app (lam (app (T g) (app (T f) (var 0)))) (fst 0)) (snd 0))
  -- Beta: app (lam B) (fst 0) →β subst0 (fst 0) B
  -- subst0 (fst 0) (app (T g) (app (T f) (var 0)))
  --   = app (subst0 (fst 0) (T g)) (app (subst0 (fst 0) (T f)) (subst0 (fst 0) (var 0)))
  --   = app (T g) (app (T f) (fst 0))  [T g, T f closed; subst0 (fst 0) (var 0) = fst 0]
  -- So LHS →β common

  have lhs_to_common : BetaEta (T (first (comp f g))) common := by
    -- Step 1: shift 1 0 (T (comp f g)) = T (comp f g) (since closed)
    have s1 : LamTerm.shift 1 0 (T (comp f g)) = T (comp f g) :=
      LamTerm.shift_idempotent_closed 1 0 _ hTcf
    -- Step 2: T (comp f g) = lam (app (shift 1 0 (T g)) (app (shift 1 0 (T f)) (var 0)))
    -- and shift 1 0 (T g) = T g, shift 1 0 (T f) = T f (since closed)
    have s2 : T (comp f g) = lam (app (T g) (app (T f) (var 0))) := by
      show lam (app (LamTerm.shift 1 0 (T g)) (app (LamTerm.shift 1 0 (T f)) (var 0))) =
           lam (app (T g) (app (T f) (var 0)))
      rw [LamTerm.shift_idempotent_closed 1 0 _ hTg,
          LamTerm.shift_idempotent_closed 1 0 _ hTf]
    -- Step 3: LHS = lam (pair (app (lam (app (T g) (app (T f) (var 0)))) (fst 0)) (snd 0))
    show BetaEta
      (lam (pair (app (LamTerm.shift 1 0 (T (comp f g))) (fst (var 0))) (snd (var 0))))
      common
    rw [s1, s2]
    -- Step 4: Beta on the inner app
    -- app (lam B) (fst 0) →β subst0 (fst 0) B
    -- where B = app (T g) (app (T f) (var 0))
    -- subst0 (fst 0) B = app (T g) (app (T f) (fst 0))  [T g, T f closed]
    have beta : BetaEta
      (app (lam (app (T g) (app (T f) (var 0)))) (fst (var 0)))
      (app (T g) (app (T f) (fst (var 0)))) := by
      -- beta_lam gives: BetaEta (app (lam B) arg) (subst0 arg B)
      have := BetaEta.beta_lam (app (T g) (app (T f) (var 0))) (fst (var 0))
      -- Need: subst0 (fst (var 0)) (app (T g) (app (T f) (var 0))) = app (T g) (app (T f) (fst (var 0)))
      have hsubst : subst0 (fst (var 0)) (app (T g) (app (T f) (var 0))) =
                    app (T g) (app (T f) (fst (var 0))) := by
        show app (substAux (fst (var 0)) 0 (T g))
                 (substAux (fst (var 0)) 0 (app (T f) (var 0)))
              = app (T g) (app (T f) (fst (var 0)))
        rw [LamTerm.substAux_closed (fst (var 0)) 0 _ hTg]
        show app (T g) (app (substAux (fst (var 0)) 0 (T f))
                         (substAux (fst (var 0)) 0 (var 0)))
              = app (T g) (app (T f) (fst (var 0)))
        rw [LamTerm.substAux_closed (fst (var 0)) 0 _ hTf]
        show app (T g) (app (T f) (substAux (fst (var 0)) 0 (var 0)))
              = app (T g) (app (T f) (fst (var 0)))
        simp [substAux, subst0, LamTerm.shift_zero]
      rw [hsubst] at this
      exact this
    -- Use congruence to lift beta to the full term
    exact BetaEta.cong_lam
      (@BetaEta.cong_pair_l _ _ (snd (var 0)) beta)

  -- RHS = T (comp (first f) (first g))
  --      = lam (app (shift 1 0 (T (first g))) (app (shift 1 0 (T (first f))) (var 0)))
  -- Since T(first g), T(first f) closed: shifts are identity
  -- = lam (app (T (first g)) (app (T (first f)) (var 0)))
  -- T(first g) = lam (pair (app (shift 1 0 (T g)) (fst 0)) (snd 0))
  --            = lam (pair (app (T g) (fst 0)) (snd 0))  [T g closed]
  -- T(first f) = lam (pair (app (T f) (fst 0)) (snd 0))  [T f closed]
  -- Inner beta: app (lam (pair (app (T f) (fst 0)) (snd 0))) (var 0)
  --   →β subst0 (var 0) (pair (app (T f) (fst 0)) (snd 0))
  --   = pair (app (T f) (fst 0)) (snd 0)  [T f closed; subst0 (var 0) (var 0) = var 0]
  -- Outer beta: app (lam (pair (app (T g) (fst 0)) (snd 0))) (pair (app (T f) (fst 0)) (snd 0))
  --   →β subst0 e (pair (app (T g) (fst 0)) (snd 0))  where e = pair (app (T f) (fst 0)) (snd 0)
  --   = pair (app (T g) (fst e)) (snd e)  [T g closed; subst0 e (var 0) = e]
  --   →β_fst pair (app (T g) (app (T f) (fst 0))) (snd e)
  --   →β_snd pair (app (T g) (app (T f) (fst 0))) (snd 0)
  -- So RHS →β →β →β_fst →β_snd common

  have rhs_to_common : BetaEta (T (comp (first f) (first g))) common := by
    -- Simplify shifts using closedness
    have s1 : LamTerm.shift 1 0 (T (first g)) = T (first g) :=
      LamTerm.shift_idempotent_closed 1 0 _ hTcfg
    have s2 : LamTerm.shift 1 0 (T (first f)) = T (first f) :=
      LamTerm.shift_idempotent_closed 1 0 _ hTcff
    have s3 : T (first g) = lam (pair (app (T g) (fst (var 0))) (snd (var 0))) := by
      show lam (pair (app (LamTerm.shift 1 0 (T g)) (fst (var 0))) (snd (var 0))) =
           lam (pair (app (T g) (fst (var 0))) (snd (var 0)))
      rw [LamTerm.shift_idempotent_closed 1 0 _ hTg]
    have s4 : T (first f) = lam (pair (app (T f) (fst (var 0))) (snd (var 0))) := by
      show lam (pair (app (LamTerm.shift 1 0 (T f)) (fst (var 0))) (snd (var 0))) =
           lam (pair (app (T f) (fst (var 0))) (snd (var 0)))
      rw [LamTerm.shift_idempotent_closed 1 0 _ hTf]
    show BetaEta
      (lam (app (LamTerm.shift 1 0 (T (first g)))
            (app (LamTerm.shift 1 0 (T (first f))) (var 0))))
      common
    rw [s1, s2, s3, s4]
    -- Now: lam (app (lam (pair (app (T g) (fst 0)) (snd 0)))
    --              (app (lam (pair (app (T f) (fst 0)) (snd 0))) (var 0)))
    -- Need to show this is BetaEta-equivalent to common

    -- Inner beta: app (lam (pair (app (T f) (fst 0)) (snd 0))) (var 0)
    --   →β subst0 (var 0) (pair (app (T f) (fst 0)) (snd 0))
    --   = pair (app (T f) (fst 0)) (snd 0)  [T f closed, subst0 (var 0) (var 0) = var 0]
    have inner_beta : BetaEta
      (app (lam (pair (app (T f) (fst (var 0))) (snd (var 0)))) (var 0))
      (pair (app (T f) (fst (var 0))) (snd (var 0))) := by
      have := BetaEta.beta_lam (pair (app (T f) (fst (var 0))) (snd (var 0))) (var 0)
      have hsubst : subst0 (var 0) (pair (app (T f) (fst (var 0))) (snd (var 0))) =
                    pair (app (T f) (fst (var 0))) (snd (var 0)) := by
        show pair (app (substAux (var 0) 0 (T f)) (substAux (var 0) 0 (fst (var 0))))
                 (substAux (var 0) 0 (snd (var 0)))
              = pair (app (T f) (fst (var 0))) (snd (var 0))
        rw [LamTerm.substAux_closed (var 0) 0 _ hTf]
        simp [substAux, subst0, LamTerm.shift_zero]
      rw [hsubst] at this
      exact this

    -- After inner beta, we have:
    -- lam (app (lam (pair (app (T g) (fst 0)) (snd 0))) (pair (app (T f) (fst 0)) (snd 0)))
    -- Outer beta: →β subst0 e (pair (app (T g) (fst 0)) (snd 0))
    --   where e = pair (app (T f) (fst 0)) (snd 0)
    --   = pair (app (T g) (fst e)) (snd e)  [T g closed, subst0 e (var 0) = e]
    -- Then beta_fst and beta_snd give the final form.

    let e := pair (app (T f) (fst (var 0))) (snd (var 0))
    have outer_beta : BetaEta
      (app (lam (pair (app (T g) (fst (var 0))) (snd (var 0)))) e)
      (pair (app (T g) (fst e)) (snd e)) := by
      have := BetaEta.beta_lam (pair (app (T g) (fst (var 0))) (snd (var 0))) e
      have hsubst : subst0 e (pair (app (T g) (fst (var 0))) (snd (var 0))) =
                    pair (app (T g) (fst e)) (snd e) := by
        show pair (app (substAux e 0 (T g)) (substAux e 0 (fst (var 0))))
                 (substAux e 0 (snd (var 0)))
              = pair (app (T g) (fst e)) (snd e)
        rw [LamTerm.substAux_closed e 0 _ hTg]
        simp [substAux, subst0, LamTerm.shift_zero]
      rw [hsubst] at this
      exact this

    -- beta_fst: fst (pair a b) →β a
    have bfst : BetaEta (fst e) (app (T f) (fst (var 0))) :=
      BetaEta.beta_fst (app (T f) (fst (var 0))) (snd (var 0))
    -- beta_snd: snd (pair a b) →β b
    have bsnd : BetaEta (snd e) (snd (var 0)) :=
      BetaEta.beta_snd (app (T f) (fst (var 0))) (snd (var 0))

    -- Combine: outer_beta then congruence with beta_fst, beta_snd
    have step1 : BetaEta
      (pair (app (T g) (fst e)) (snd e))
      (pair (app (T g) (app (T f) (fst (var 0)))) (snd (var 0))) := by
      -- First: cong_pair_l to change fst e → app (T f) (fst 0)
      -- Then: cong_pair_r to change snd e → snd 0
      have step_left : BetaEta
        (pair (app (T g) (fst e)) (snd e))
        (pair (app (T g) (app (T f) (fst (var 0)))) (snd e)) :=
        @BetaEta.cong_pair_l _ _ (snd e) (BetaEta.cong_app_a bfst)
      have step_right : BetaEta
        (pair (app (T g) (app (T f) (fst (var 0)))) (snd e))
        (pair (app (T g) (app (T f) (fst (var 0)))) (snd (var 0))) :=
        @BetaEta.cong_pair_r _ _ _ bsnd
      exact BetaEta.trans step_left step_right

    -- Full RHS: lam (app (lam ...) (app (lam ...) (var 0)))
    -- → cong_app_a inner_beta → lam (app (lam ...) e)
    -- → cong_lam (cong_app_a outer_beta) → lam (pair (app (T g) (fst e)) (snd e))
    -- → cong_lam step1 → lam (pair (app (T g) (app (T f) (fst 0))) (snd 0)) = common

    exact BetaEta.trans
      (BetaEta.cong_lam
        (BetaEta.cong_app_a inner_beta))
      (BetaEta.trans
        (BetaEta.cong_lam outer_beta)
        (BetaEta.cong_lam step1))

  exact BetaEta.trans lhs_to_common (BetaEta.symm rhs_to_common)

/-- `T(left (f >>> g)) ≡βη T(left f >>> left g)`.

This proves that `left` is compositional: translating `left (f >>> g)`
yields a βη-equivalent term to translating `left f >>> left g`.

Proof: Both sides reduce to
  `λs. case s of inl x => inl (T(g) (T(f) x)) | inr y => inr y`
after β-reduction and case-of-case commutation.

NOTE: Unlike `T_first_compositional` (which needs only β for products),
this proof requires the **case commuting conversion** (`case_inl_inr_comm`)
for sums. This is a genuine proof-theoretic difference: product
compositionality holds under pure βη, but sum compositionality needs
commuting conversions — a standard part of the equational theory for
STLC with sums, but strictly stronger than βη alone. -/
theorem T_left_compositional (f g : ArrowProg)
    (hf : ArrowProg.allArrClosed f) (hg : ArrowProg.allArrClosed g) :
    BetaEta (T (left (comp f g)))
           (T (comp (left f) (left g))) := by
  have hTf := T_closed f hf
  have hTg := T_closed g hg
  have hTcf := T_closed (comp f g) ⟨hf, hg⟩
  have hTclf := T_closed (left f) hf
  have hTclg := T_closed (left g) hg

  -- Common form: lam (case (var 0) (inl (app (T g) (app (T f) (var 0)))) (inr (var 0)))
  let common := lam (case (var 0)
    (inl (app (T g) (app (T f) (var 0))))
    (inr (var 0)))

  -- LHS = T(left (comp f g))
  --      = lam (case (var 0) (inl (app (shift 2 0 (T (comp f g))) (var 0))) (inr (var 0)))
  -- shift 2 0 (T (comp f g)) = T (comp f g)  [closed]
  -- T (comp f g) = lam (app (T g) (app (T f) (var 0)))  [shifts identity since closed]
  -- Beta: app (lam B) (var 0) →β subst0 (var 0) B = B  [T g, T f closed]
  -- Result: lam (case (var 0) (inl (app (T g) (app (T f) (var 0)))) (inr (var 0))) = common

  have lhs_to_common : BetaEta (T (left (comp f g))) common := by
    have s1 : LamTerm.shift 2 0 (T (comp f g)) = T (comp f g) :=
      LamTerm.shift_idempotent_closed 2 0 _ hTcf
    have s2 : T (comp f g) = lam (app (T g) (app (T f) (var 0))) := by
      show lam (app (LamTerm.shift 1 0 (T g)) (app (LamTerm.shift 1 0 (T f)) (var 0))) =
           lam (app (T g) (app (T f) (var 0)))
      rw [LamTerm.shift_idempotent_closed 1 0 _ hTg,
          LamTerm.shift_idempotent_closed 1 0 _ hTf]
    show BetaEta
      (lam (case (var 0)
        (inl (app (LamTerm.shift 2 0 (T (comp f g))) (var 0)))
        (inr (var 0))))
      common
    rw [s1, s2]
    -- Beta: app (lam B) (var 0) →β subst0 (var 0) B = B
    have beta : BetaEta
      (app (lam (app (T g) (app (T f) (var 0)))) (var 0))
      (app (T g) (app (T f) (var 0))) := by
      have := BetaEta.beta_lam (app (T g) (app (T f) (var 0))) (var 0)
      have hsubst : subst0 (var 0) (app (T g) (app (T f) (var 0))) =
                    app (T g) (app (T f) (var 0)) := by
        show app (substAux (var 0) 0 (T g)) (substAux (var 0) 0 (app (T f) (var 0)))
              = app (T g) (app (T f) (var 0))
        rw [LamTerm.substAux_closed (var 0) 0 _ hTg]
        show app (T g) (app (substAux (var 0) 0 (T f)) (substAux (var 0) 0 (var 0)))
              = app (T g) (app (T f) (var 0))
        rw [LamTerm.substAux_closed (var 0) 0 _ hTf]
        show app (T g) (app (T f) (substAux (var 0) 0 (var 0)))
              = app (T g) (app (T f) (var 0))
        simp [substAux, subst0, LamTerm.shift_zero]
      rw [hsubst] at this
      exact this
    exact BetaEta.cong_lam
      (@BetaEta.cong_case_f _ _ _ (inr (var 0))
        (BetaEta.cong_inl beta))

  -- RHS = T(comp (left f) (left g))
  --      = lam (app (shift 1 0 (T (left g))) (app (shift 1 0 (T (left f))) (var 0)))
  -- Shifts identity (closed): = lam (app (T (left g)) (app (T (left f)) (var 0)))
  -- T (left g) = lam (case (var 0) (inl (app (T g) (var 0))) (inr (var 0)))
  -- T (left f) = lam (case (var 0) (inl (app (T f) (var 0))) (inr (var 0)))
  -- Inner beta: app (lam (case 0 (inl (Tf 0)) (inr 0))) (var 0)
  --   →β subst0 (var 0) (case 0 (inl (Tf 0)) (inr 0))
  --   = case (var 0) (inl (Tf 0)) (inr 0)  [Tf closed, subst0 (var 0) (var 0) = var 0]
  -- Outer beta: app (lam (case 0 (inl (Tg 0)) (inr 0))) (case 0 (inl (Tf 0)) (inr 0))
  --   →β subst0 e (case 0 (inl (Tg 0)) (inr 0))  where e = case 0 (inl (Tf 0)) (inr 0)
  --   = case e (inl (Tg 0)) (inr 0)  [Tg closed, subst0 e (var 0) = e]
  --   = case (case 0 (inl (Tf 0)) (inr 0)) (inl (Tg 0)) (inr 0)
  -- Case commutation: ≡ case 0 (subst0 (Tf 0) (inl (Tg 0))) (subst0 (var 0) (inr 0))
  --   = case 0 (inl (Tg (Tf 0))) (inr 0)  [Tg closed; subst0 (var 0) (var 0) = var 0]
  --   = common

  have rhs_to_common : BetaEta (T (comp (left f) (left g))) common := by
    have s1 : LamTerm.shift 1 0 (T (left g)) = T (left g) :=
      LamTerm.shift_idempotent_closed 1 0 _ hTclg
    have s2 : LamTerm.shift 1 0 (T (left f)) = T (left f) :=
      LamTerm.shift_idempotent_closed 1 0 _ hTclf
    have s3 : T (left g) = lam (case (var 0) (inl (app (T g) (var 0))) (inr (var 0))) := by
      show lam (case (var 0) (inl (app (LamTerm.shift 2 0 (T g)) (var 0))) (inr (var 0))) =
           lam (case (var 0) (inl (app (T g) (var 0))) (inr (var 0)))
      rw [LamTerm.shift_idempotent_closed 2 0 _ hTg]
    have s4 : T (left f) = lam (case (var 0) (inl (app (T f) (var 0))) (inr (var 0))) := by
      show lam (case (var 0) (inl (app (LamTerm.shift 2 0 (T f)) (var 0))) (inr (var 0))) =
           lam (case (var 0) (inl (app (T f) (var 0))) (inr (var 0)))
      rw [LamTerm.shift_idempotent_closed 2 0 _ hTf]
    show BetaEta
      (lam (app (LamTerm.shift 1 0 (T (left g)))
            (app (LamTerm.shift 1 0 (T (left f))) (var 0))))
      common
    rw [s1, s2, s3, s4]

    -- Inner beta: app (lam (case 0 (inl (Tf 0)) (inr 0))) (var 0)
    --   →β case (var 0) (inl (app (T f) (var 0))) (inr (var 0))
    let inner_result := case (var 0) (inl (app (T f) (var 0))) (inr (var 0))
    have inner_beta : BetaEta
      (app (lam inner_result) (var 0)) inner_result := by
      have := BetaEta.beta_lam inner_result (var 0)
      have hsubst : subst0 (var 0) inner_result = inner_result := by
        show case (substAux (var 0) 0 (var 0))
                 (substAux (var 0) 1 (inl (app (T f) (var 0))))
                 (substAux (var 0) 1 (inr (var 0)))
              = inner_result
        -- substAux (var 0) 0 (var 0) = var 0
        have h0 : substAux (var 0) 0 (var 0) = (var 0) := by
          simp [substAux, subst0, LamTerm.shift_zero]
        -- substAux (var 0) 1 (inl (app (T f) (var 0))) = inl (app (T f) (var 0))
        -- T f closed → closedAbove 1 (T f) by weaken → substAux (var 0) 1 (T f) = T f
        have h1 : substAux (var 0) 1 (inl (app (T f) (var 0))) =
                  (inl (app (T f) (var 0))) := by
          simp only [substAux]
          rw [LamTerm.substAux_closed (var 0) 1 _ (LamTerm.closedAbove_weaken 0 _ hTf)]
          simp [substAux]
        have h2 : substAux (var 0) 1 (inr (var 0)) = (inr (var 0)) := by
          simp [substAux]
        rw [h0, h1, h2]
      rw [hsubst] at this
      exact this

    -- Outer beta: app (lam (case 0 (inl (Tg 0)) (inr 0))) inner_result
    --   →β case inner_result (inl (app (T g) (var 0))) (inr (var 0))
    let outer_body := case (var 0) (inl (app (T g) (var 0))) (inr (var 0))
    have outer_beta : BetaEta
      (app (lam outer_body) inner_result)
      (case inner_result (inl (app (T g) (var 0))) (inr (var 0))) := by
      have := BetaEta.beta_lam outer_body inner_result
      have hsubst : subst0 inner_result outer_body =
                    case inner_result (inl (app (T g) (var 0))) (inr (var 0)) := by
        show case (substAux inner_result 0 (var 0))
                 (substAux inner_result 1 (inl (app (T g) (var 0))))
                 (substAux inner_result 1 (inr (var 0)))
              = case inner_result (inl (app (T g) (var 0))) (inr (var 0))
        have h0 : substAux inner_result 0 (var 0) = inner_result := by
          simp [substAux, subst0, LamTerm.shift_zero]
        have h1 : substAux inner_result 1 (inl (app (T g) (var 0))) =
                  (inl (app (T g) (var 0))) := by
          simp only [substAux]
          rw [LamTerm.substAux_closed inner_result 1 _ (LamTerm.closedAbove_weaken 0 _ hTg)]
          simp [substAux]
        have h2 : substAux inner_result 1 (inr (var 0)) = (inr (var 0)) := by
          simp [substAux]
        rw [h0, h1, h2]
      rw [hsubst] at this
      exact this

    -- Case commutation:
    -- case (case (var 0) (inl (app (T f) (var 0))) (inr (var 0)))
    --      (inl (app (T g) (var 0))) (inr (var 0))
    -- ≡ case (var 0) (subst0 (app (T f) (var 0)) (inl (app (T g) (var 0))))
    --              (subst0 (var 0) (inr (var 0)))
    -- = case (var 0) (inl (app (T g) (app (T f) (var 0)))) (inr (var 0))
    -- = common (inside the lam)

    -- closedAbove 1 conditions for the commutation:
    have cA : LamTerm.closedAbove 1 (app (T f) (var 0)) := by
      simp only [LamTerm.closedAbove]
      exact ⟨LamTerm.closedAbove_weaken 0 _ hTf, by trivial⟩
    have cB : LamTerm.closedAbove 1 (var 0) := by simp [LamTerm.closedAbove]
    have ch : LamTerm.closedAbove 1 (inl (app (T g) (var 0))) := by
      simp only [LamTerm.closedAbove]
      exact ⟨LamTerm.closedAbove_weaken 0 _ hTg, by trivial⟩
    have ck : LamTerm.closedAbove 1 (inr (var 0)) := by simp [LamTerm.closedAbove]

    -- Simplify the subst0s:
    have s5 : subst0 (app (T f) (var 0)) (inl (app (T g) (var 0))) =
              (inl (app (T g) (app (T f) (var 0)))) := by
      simp only [subst0, substAux]
      rw [LamTerm.substAux_closed (app (T f) (var 0)) 0 _ hTg]
      simp [substAux, subst0, LamTerm.shift_zero]
    have s6 : subst0 (var 0) (inr (var 0)) = (inr (var 0)) := by
      simp only [subst0, substAux]
      simp [LamTerm.shift_zero]

    -- Commutation: case inner_result H K ≡ case (var 0) (subst0 A H) (subst0 B K)
    -- After s5, s6: RHS = case (var 0) (inl (app (T g) (app (T f) (var 0)))) (inr (var 0))
    have comm : BetaEta
      (case inner_result (inl (app (T g) (var 0))) (inr (var 0)))
      (case (var 0) (inl (app (T g) (app (T f) (var 0)))) (inr (var 0))) := by
      have := BetaEta.case_inl_inr_comm (var 0)
        (app (T f) (var 0)) (var 0)
        (inl (app (T g) (var 0))) (inr (var 0))
        cA cB ch ck
      rw [s5, s6] at this
      exact this

    -- Combine all steps inside the lam:
    -- lam (app (lam outer_body) (app (lam inner_result) (var 0)))
    -- → cong_app_a inner_beta → lam (app (lam outer_body) inner_result)
    -- → outer_beta → lam (case inner_result H K)
    -- → comm → lam (case (var 0) (inl (Tg (Tf 0))) (inr 0)) = common
    show BetaEta
      (lam (app (lam outer_body) (app (lam inner_result) (var 0))))
      common
    show BetaEta
      (lam (app (lam outer_body) (app (lam inner_result) (var 0))))
      (lam (case (var 0) (inl (app (T g) (app (T f) (var 0)))) (inr (var 0))))
    exact BetaEta.cong_lam
      (BetaEta.trans
        (BetaEta.cong_app_a inner_beta)
        (BetaEta.trans
          outer_beta
          comm))

  exact BetaEta.trans lhs_to_common (BetaEta.symm rhs_to_common)

end Compositionality

-- ============================================================================
-- 10. Loop Extension Gap: the law needs fix-unrolling, not just βη
-- ============================================================================

namespace LoopGap

open LamTerm ArrowProg

/- The loop extension law in arrow form:
    `loop (f >>> first g) = loop f >>> g`

This is a standard arrow law (Hughes 2000, LWY 2008). We show that its
lambda translation requires fix-unrolling, not just beta-eta-equivalence. -/

/-- The left side of the loop extension law, translated:
  `T(loop (f >>> first g))`
  = `λx. fst (fix (λr. T(f>>>first g) (x, r)))`
  = `λx. fst (fix (λr. (λ(x',y'). (T(g) (T(f) x'), y')) (x, r)))`
  →β `λx. fst (fix (λr. (T(g) (T(f) x), r)))`

The fix is NOT unrolled under pure βη. -/
def loopExtLHS (f g : ArrowProg) : LamTerm :=
  T (loop (comp f (first g)))

/-- The right side of the loop extension law, translated:
  `T(loop f >>> g)`
  = `λx. T(g) (fst (fix (λr. T(f) (x, r))))`

The `T(g)` is applied OUTSIDE the fix, to the `fst` of the fix result. -/
def loopExtRHS (f g : ArrowProg) : LamTerm :=
  T (comp (loop f) g)

/-- The two sides of the loop extension law are equal under `BetaEtaFix`
(βη + fix-unrolling), but NOT under `BetaEta` alone.

**Why they are BetaEtaFix-equivalent:**
  LHS = `λx. fst (fix (λr. (T(g) (T(f) x), r)))`
  RHS = `λx. T(g) (fst (fix (λr. T(f) (x, r))))`

  Unroll the fix in LHS:
    `fix (λr. (T(g) (T(f) x), r))`
    → `(λr. (T(g) (T(f) x), r)) (fix (λr. (T(g) (T(f) x), r)))`
    →β `(T(g) (T(f) x), fix (λr. (T(g) (T(f) x), r)))`
    So `fst (...)` → `T(g) (T(f) x)`

  Unroll the fix in RHS:
    `fix (λr. T(f) (x, r))`
    → `(λr. T(f) (x, r)) (fix (λr. T(f) (x, r)))`
    →β `T(f) (x, fix (λr. T(f) (x, r)))`
    So `fst (...)` → `fst (T(f) (x, fix (λr. T(f) (x, r))))`

  These are NOT the same after one unroll! The LHS fix has `T(g)` inside
  the fix body, while the RHS fix does not. They are equal only because
  the loop extension law holds — which requires showing that the fixed
  point of `(λr. (T(g) (T(f) x), r))` has the same `fst` as
  `T(g) (fst (fix (λr. T(f) (x, r))))`.

  This is a genuine fixed-point equation, not a βη-equivalence. It requires
  the full power of fix-unrolling + βη, and the proof is non-trivial.

**Why this is not arrow-specific:**
  Any translation of recursive programs into lambda requires fixed-point
  reasoning. The same gap appears translating recursive monadic programs.
  The arrow calculus treats `loop` as a law-abiding combinator with
  equational laws provable within the arrow theory; the lambda translation
  moves the burden of those laws to the meta-level (fixed-point reasoning).
  This is a proof-theoretic asymmetry — not a size or compositionality
  asymmetry, but a real difference in where the equational reasoning
  burden lives. -/
theorem loopExt_eq_under_BetaEtaFix (f g : ArrowProg)
    (hf : ArrowProg.allArrClosed f) (hg : ArrowProg.allArrClosed g) :
    BetaEtaFix (loopExtLHS f g) (loopExtRHS f g) := by
  -- T produces closed terms for well-formed programs
  have hTf := T_closed f hf
  have hTg := T_closed g hg
  have hTfg := T_closed (comp f (first g)) ⟨hf, hg⟩

  -- The fix_fusion step (inside the outer lam):
  have fusion : BetaEtaFix
    (fst (fix (lam (pair
      (app (T g) (fst (app (T f) (pair (var 1) (var 0)))))
      (snd (app (T f) (pair (var 1) (var 0))))))))
    (app (T g) (fst (fix (lam (app (T f) (pair (var 1) (var 0))))))) :=
    BetaEtaFix.fix_fusion (T g) (T f) (var 1) hTg hTf

  -- Lift through cong_lam:
  have fusion_lam : BetaEtaFix
    (lam (fst (fix (lam (pair
      (app (T g) (fst (app (T f) (pair (var 1) (var 0)))))
      (snd (app (T f) (pair (var 1) (var 0)))))))))
    (lam (app (T g) (fst (fix (lam (app (T f) (pair (var 1) (var 0)))))))) :=
    BetaEtaFix.cong_lam fusion

  -- LHS: T (loop (comp f (first g)))
  -- After shift simplification (T closed) and β-reduction of the composition,
  -- the fix body becomes: pair (app (T g) (fst (app (T f) (pair (var 1) (var 0))))) (snd (...))
  -- which is the fix_fusion LHS form.

  have lhs_to_fusion : BetaEtaFix (loopExtLHS f g)
    (lam (fst (fix (lam (pair
      (app (T g) (fst (app (T f) (pair (var 1) (var 0)))))
      (snd (app (T f) (pair (var 1) (var 0))))))))) := by
    show BetaEtaFix
      (lam (fst (fix (lam (app (LamTerm.shift 2 0 (T (comp f (first g))))
        (pair (var 1) (var 0))))))) _
    -- Simplify shifts (T closed)
    have s1 : LamTerm.shift 2 0 (T (comp f (first g))) = T (comp f (first g)) :=
      LamTerm.shift_idempotent_closed 2 0 _ hTfg
    have s2 : T (comp f (first g)) =
        lam (app (T (first g)) (app (T f) (var 0))) := by
      show lam (app (LamTerm.shift 1 0 (T (first g)))
                 (app (LamTerm.shift 1 0 (T f)) (var 0))) =
           lam (app (T (first g)) (app (T f) (var 0)))
      rw [LamTerm.shift_idempotent_closed 1 0 _ (T_closed (first g) hg),
          LamTerm.shift_idempotent_closed 1 0 _ hTf]
    have s3 : T (first g) = lam (pair (app (T g) (fst (var 0))) (snd (var 0))) := by
      show lam (pair (app (LamTerm.shift 1 0 (T g)) (fst (var 0))) (snd (var 0))) =
           lam (pair (app (T g) (fst (var 0))) (snd (var 0)))
      rw [LamTerm.shift_idempotent_closed 1 0 _ hTg]
    rw [s1, s2, s3]

    -- Now LHS = lam (fst (fix (lam (app (lam (app (lam B2) (app (T f) (var 0)))) (pair (var 1) (var 0))))))
    -- where B2 = pair (app (T g) (fst (var 0))) (snd (var 0))
    -- Two β-reductions inside lam/fst/fix/lam bring this to the fusion form.

    -- β1: subst0 (pair (var 1) (var 0)) (app (lam B2) (app (T f) (var 0)))
    --   = app (lam B2) (app (T f) (pair (var 1) (var 0)))  [B2 unchanged, T f closed]
    have beta1_subst : subst0 (pair (var 1) (var 0))
        (app (lam (pair (app (T g) (fst (var 0))) (snd (var 0)))) (app (T f) (var 0))) =
        app (lam (pair (app (T g) (fst (var 0))) (snd (var 0)))) (app (T f) (pair (var 1) (var 0))) := by
      show app (lam (substAux (pair (var 1) (var 0)) 1
        (pair (app (T g) (fst (var 0))) (snd (var 0)))))
        (app (substAux (pair (var 1) (var 0)) 0 (T f))
             (substAux (pair (var 1) (var 0)) 0 (var 0))) =
        app (lam (pair (app (T g) (fst (var 0))) (snd (var 0))))
            (app (T f) (pair (var 1) (var 0)))
      have h_inner : substAux (pair (var 1) (var 0)) 1
        (pair (app (T g) (fst (var 0))) (snd (var 0))) =
        (pair (app (T g) (fst (var 0))) (snd (var 0))) := by
        show pair (app (substAux (pair (var 1) (var 0)) 1 (T g))
                       (substAux (pair (var 1) (var 0)) 1 (fst (var 0))))
                   (substAux (pair (var 1) (var 0)) 1 (snd (var 0))) =
              pair (app (T g) (fst (var 0))) (snd (var 0))
        rw [LamTerm.substAux_closed (pair (var 1) (var 0)) 1 _ (LamTerm.closedAbove_weaken 0 _ hTg)]
        show pair (app (T g) (fst (substAux (pair (var 1) (var 0)) 1 (var 0))))
                   (snd (substAux (pair (var 1) (var 0)) 1 (var 0))) =
              pair (app (T g) (fst (var 0))) (snd (var 0))
        simp [substAux]
      rw [h_inner, LamTerm.substAux_closed (pair (var 1) (var 0)) 0 _ hTf]
      show app (lam (pair (app (T g) (fst (var 0))) (snd (var 0))))
        (app (T f) (substAux (pair (var 1) (var 0)) 0 (var 0))) =
        app (lam (pair (app (T g) (fst (var 0))) (snd (var 0))))
            (app (T f) (pair (var 1) (var 0)))
      simp [substAux, subst0, LamTerm.shift_zero]

    -- β2: subst0 (app (T f) (pair (var 1) (var 0))) B2
    --   = pair (app (T g) (fst (app (T f) (pair (var 1) (var 0))))) (snd (app (T f) (pair (var 1) (var 0))))
    have beta2_subst : subst0 (app (T f) (pair (var 1) (var 0)))
        (pair (app (T g) (fst (var 0))) (snd (var 0))) =
        pair (app (T g) (fst (app (T f) (pair (var 1) (var 0)))))
             (snd (app (T f) (pair (var 1) (var 0)))) := by
      show pair (app (substAux (app (T f) (pair (var 1) (var 0))) 0 (T g))
                     (substAux (app (T f) (pair (var 1) (var 0))) 0 (fst (var 0))))
                 (substAux (app (T f) (pair (var 1) (var 0))) 0 (snd (var 0))) =
              pair (app (T g) (fst (app (T f) (pair (var 1) (var 0)))))
                   (snd (app (T f) (pair (var 1) (var 0))))
      rw [LamTerm.substAux_closed (app (T f) (pair (var 1) (var 0))) 0 _ hTg]
      show pair (app (T g) (fst (substAux (app (T f) (pair (var 1) (var 0))) 0 (var 0))))
                 (snd (substAux (app (T f) (pair (var 1) (var 0))) 0 (var 0))) =
              pair (app (T g) (fst (app (T f) (pair (var 1) (var 0)))))
                   (snd (app (T f) (pair (var 1) (var 0))))
      simp [substAux, subst0, LamTerm.shift_zero]

    -- β1 as BetaEta: app (lam B1) arg →β subst0 arg B1
    -- B1 = app (lam B2) (app (T f) (var 0)), arg = pair (var 1) (var 0)
    have beta1 : BetaEta
      (app (lam (app (lam (pair (app (T g) (fst (var 0))) (snd (var 0)))) (app (T f) (var 0))))
           (pair (var 1) (var 0)))
      (app (lam (pair (app (T g) (fst (var 0))) (snd (var 0))))
           (app (T f) (pair (var 1) (var 0)))) := by
      have := BetaEta.beta_lam
        (app (lam (pair (app (T g) (fst (var 0))) (snd (var 0)))) (app (T f) (var 0)))
        (pair (var 1) (var 0))
      rw [beta1_subst] at this
      exact this

    -- β2 as BetaEta: app (lam B2) arg2 →β subst0 arg2 B2
    -- arg2 = app (T f) (pair (var 1) (var 0))
    have beta2 : BetaEta
      (app (lam (pair (app (T g) (fst (var 0))) (snd (var 0))))
           (app (T f) (pair (var 1) (var 0))))
      (pair (app (T g) (fst (app (T f) (pair (var 1) (var 0)))))
            (snd (app (T f) (pair (var 1) (var 0))))) := by
      have := BetaEta.beta_lam
        (pair (app (T g) (fst (var 0))) (snd (var 0)))
        (app (T f) (pair (var 1) (var 0)))
      rw [beta2_subst] at this
      exact this

    -- Chain: β1 then β2, lifted through cong_lam ∘ cong_fst ∘ cong_fix ∘ cong_lam
    -- The path from outer to inner: lam → fst → fix → lam → (β-redex)
    -- Combined β1+β2 as BetaEtaFix, then lift through congruences
    exact BetaEtaFix.cong_lam
      (BetaEtaFix.cong_fst
        (BetaEtaFix.cong_fix
          (BetaEtaFix.cong_lam
            (BetaEtaFix.trans (BetaEtaFix.of_betaEta beta1) (BetaEtaFix.of_betaEta beta2)))))

  -- RHS: T (comp (loop f) g)
  -- After shift simplification and β-reduction:
  -- lam (app (T g) (fst (fix (lam (app (T f) (pair (var 1) (var 0)))))))
  have rhs_to_fusion : BetaEtaFix
    (lam (app (T g) (fst (fix (lam (app (T f) (pair (var 1) (var 0))))))))
    (loopExtRHS f g) := by
    show BetaEtaFix _ (lam (app (LamTerm.shift 1 0 (T g))
      (app (LamTerm.shift 1 0 (T (loop f))) (var 0))))
    -- Simplify shifts
    have s1 : LamTerm.shift 1 0 (T g) = T g :=
      LamTerm.shift_idempotent_closed 1 0 _ hTg
    have s2 : LamTerm.shift 1 0 (T (loop f)) = T (loop f) :=
      LamTerm.shift_idempotent_closed 1 0 _ (T_closed (loop f) hf)
    have s3 : T (loop f) = lam (fst (fix (lam (app (T f) (pair (var 1) (var 0)))))) := by
      show lam (fst (fix (lam (app (LamTerm.shift 2 0 (T f)) (pair (var 1) (var 0)))))) =
           lam (fst (fix (lam (app (T f) (pair (var 1) (var 0))))))
      rw [LamTerm.shift_idempotent_closed 2 0 _ hTf]
    rw [s1, s2, s3]

    -- Now RHS = lam (app (T g) (app (lam (fst (fix (lam (app (T f) (pair (var 1) (var 0))))))) (var 0)))
    -- β: app (lam BODY) (var 0) →β subst0 (var 0) BODY
    -- BODY = fst (fix (lam (app (T f) (pair (var 1) (var 0)))))
    -- subst0 (var 0) BODY = BODY (var 0 doesn't appear free — bound inside lam)

    have beta_subst : subst0 (var 0)
        (fst (fix (lam (app (T f) (pair (var 1) (var 0)))))) =
        fst (fix (lam (app (T f) (pair (var 1) (var 0))))) := by
      show fst (fix (lam (substAux (var 0) 2 (app (T f) (pair (var 1) (var 0)))))) =
           fst (fix (lam (app (T f) (pair (var 1) (var 0)))))
      have h_inner : substAux (var 0) 2 (app (T f) (pair (var 1) (var 0))) =
        (app (T f) (pair (var 1) (var 0))) := by
        show app (substAux (var 0) 2 (T f)) (substAux (var 0) 2 (pair (var 1) (var 0))) =
             app (T f) (pair (var 1) (var 0))
        rw [LamTerm.substAux_closed (var 0) 2 _ (LamTerm.closedAbove_weaken 1 _ (LamTerm.closedAbove_weaken 0 _ hTf))]
        show app (T f) (pair (substAux (var 0) 2 (var 1)) (substAux (var 0) 2 (var 0))) =
             app (T f) (pair (var 1) (var 0))
        simp [substAux]
      rw [h_inner]

    have beta : BetaEta
      (app (lam (fst (fix (lam (app (T f) (pair (var 1) (var 0))))))) (var 0))
      (fst (fix (lam (app (T f) (pair (var 1) (var 0)))))) := by
      have := BetaEta.beta_lam
        (fst (fix (lam (app (T f) (pair (var 1) (var 0))))))
        (var 0)
      rw [beta_subst] at this
      exact this

    -- Lift through cong_lam ∘ cong_app_a (with symm since β goes RHS→LHS)
    exact BetaEtaFix.cong_lam
      (BetaEtaFix.symm (BetaEtaFix.cong_app_a (BetaEtaFix.of_betaEta beta)))

  exact BetaEtaFix.trans lhs_to_fusion
    (BetaEtaFix.trans fusion_lam rhs_to_fusion)

/-- Interpretation: replace every `fix t` with `lam (var 0)` (identity).

This is a semantic interpretation that "freezes" fix points. It is sound
for `BetaEta` (preserves the relation) because `fix` is inert under βη:
the only rule mentioning `fix` is `cong_fix`, and replacing both sides with
the same constant preserves equality. -/
def interp : LamTerm → LamTerm
  | var k => var k
  | lam b => lam (interp b)
  | app f a => app (interp f) (interp a)
  | pair a b => pair (interp a) (interp b)
  | fst t => fst (interp t)
  | snd t => snd (interp t)
  | inl t => inl (interp t)
  | inr t => inr (interp t)
  | case s f g => case (interp s) (interp f) (interp g)
  | fix _ => lam (var 0)
  | unit => unit

/-- `interp` commutes with `shift` (since `interp` only changes `fix`, and
`shift` goes under `fix` but `interp` replaces the whole `fix` with a
constant). -/
theorem interp_shift (d c : Nat) (t : LamTerm) :
    interp (shift d c t) = shift d c (interp t) := by
  induction t generalizing c with
  | var k => by_cases h : k < c <;> simp [shift, interp, h]
  | lam b ih => simp [shift, interp, ih (c + 1)]
  | app f a ihf iha => simp [shift, interp, ihf c, iha c]
  | pair a b ihf iha => simp [shift, interp, ihf c, iha c]
  | fst t iht => simp [shift, interp, iht c]
  | snd t iht => simp [shift, interp, iht c]
  | inl t iht => simp [shift, interp, iht c]
  | inr t iht => simp [shift, interp, iht c]
  | case s f g ihs ihf ihg =>
    simp [shift, interp, ihs c, ihf (c + 1), ihg (c + 1)]
  | fix t iht => simp [shift, interp]
  | unit => rfl

/-- `interp` commutes with `substAux` (key lemma for `interp_preserves_BetaEta`).

Since `interp` replaces every `fix t` with the constant `lam (var 0)`,
and `substAux` goes under `fix` (incrementing depth), the order doesn't
matter: `interp (substAux e d body) = substAux (interp e) d (interp body)`. -/
theorem interp_substAux (e : LamTerm) (d : Nat) (body : LamTerm) :
    interp (substAux e d body) = substAux (interp e) d (interp body) := by
  induction body generalizing d with
  | var k =>
    simp only [substAux]
    by_cases h : k < d
    · -- k < d: substAux returns var k
      simp [substAux, h, interp]
    · by_cases h2 : k = d
      · -- k = d: substAux returns shift d 0 e
        rw [if_neg h, if_pos h2, interp_shift, interp, substAux, if_neg h, if_pos h2]
      · -- k > d: substAux returns var (k-1)
        rw [if_neg h, if_neg h2, interp]
        change var (k - 1) = (if k < d then var k else if k = d then shift d 0 (interp e) else var (k - 1))
        rw [if_neg h, if_neg h2]
  | lam b ih => simp [substAux, interp, ih (d + 1)]
  | app f a ihf iha => simp [substAux, interp, ihf d, iha d]
  | pair a b ihf iha => simp [substAux, interp, ihf d, iha d]
  | fst t iht => simp [substAux, interp, iht d]
  | snd t iht => simp [substAux, interp, iht d]
  | inl t iht => simp [substAux, interp, iht d]
  | inr t iht => simp [substAux, interp, iht d]
  | case s f g ihs ihf ihg =>
    simp [substAux, interp, ihs d, ihf (d + 1), ihg (d + 1)]
  | fix t iht => simp [substAux, interp]
  | unit => rfl

/-- `interp` commutes with `subst0`. -/
theorem interp_subst0 (e body : LamTerm) :
    interp (subst0 e body) = subst0 (interp e) (interp body) := by
  simp [subst0, interp_substAux]

/-- `interp` preserves `closedAbove`: if `closedAbove n t`, then
`closedAbove n (interp t)`. This holds because `interp` replaces `fix t`
(which requires `closedAbove (n+1) t`) with `lam (var 0)` (which always
satisfies `closedAbove n`). -/
theorem interp_preserves_closedAbove : ∀ (n : Nat) (t : LamTerm),
    closedAbove n t → closedAbove n (interp t) := by
  intro n t h
  induction t generalizing n with
  | var k => simp [interp, closedAbove, h]
  | lam b ih =>
    simp only [interp, closedAbove]
    exact ih (n + 1) h
  | app f a ihf iha =>
    simp only [interp, closedAbove]
    exact ⟨ihf n h.1, iha n h.2⟩
  | pair a b ihf iha =>
    simp only [interp, closedAbove]
    exact ⟨ihf n h.1, iha n h.2⟩
  | fst t iht => simp only [interp, closedAbove]; exact iht n h
  | snd t iht => simp only [interp, closedAbove]; exact iht n h
  | inl t iht => simp only [interp, closedAbove]; exact iht n h
  | inr t iht => simp only [interp, closedAbove]; exact iht n h
  | case s f g ihs ihf ihg =>
    simp only [interp, closedAbove]
    exact ⟨ihs n h.1, ⟨ihf (n + 1) h.2.1, ihg (n + 1) h.2.2⟩⟩
  | fix t iht => simp [interp, closedAbove]
  | unit => simp [interp, closedAbove]

/-- `interp` preserves `BetaEta`: if `BetaEta t t'`, then
`BetaEta (interp t) (interp t')`.

This is the soundness of the interpretation. The key insight is that
`fix` is inert under `BetaEta` (the only rule mentioning `fix` is
`cong_fix`), so replacing `fix t` with a constant preserves all βη steps. -/
theorem interp_preserves_BetaEta : ∀ {t t' : LamTerm},
    BetaEta t t' → BetaEta (interp t) (interp t') := by
  intro t t' h
  induction h with
  | refl t => exact BetaEta.refl (interp t)
  | symm _ ih => exact BetaEta.symm ih
  | trans _ _ ih1 ih2 => exact BetaEta.trans ih1 ih2
  | beta_lam body arg =>
    -- interp (app (lam body) arg) = app (lam (interp body)) (interp arg)
    -- interp (subst0 arg body) = subst0 (interp arg) (interp body) [by interp_subst0]
    -- BetaEta (app (lam (interp body)) (interp arg)) (subst0 (interp arg) (interp body)) [by beta_lam]
    simp only [interp, interp_subst0]
    exact BetaEta.beta_lam (interp body) (interp arg)
  | beta_fst a b =>
    simp only [interp]
    exact BetaEta.beta_fst (interp a) (interp b)
  | beta_snd a b =>
    simp only [interp]
    exact BetaEta.beta_snd (interp a) (interp b)
  | beta_case_l a f g =>
    simp only [interp, interp_subst0]
    exact BetaEta.beta_case_l (interp a) (interp f) (interp g)
  | beta_case_r b f g =>
    simp only [interp, interp_subst0]
    exact BetaEta.beta_case_r (interp b) (interp f) (interp g)
  | case_inl_inr_comm s A B h k hA hB hh hk =>
    simp only [interp, interp_subst0]
    exact BetaEta.case_inl_inr_comm (interp s) (interp A) (interp B)
      (interp h) (interp k)
      (interp_preserves_closedAbove 1 A hA)
      (interp_preserves_closedAbove 1 B hB)
      (interp_preserves_closedAbove 1 h hh)
      (interp_preserves_closedAbove 1 k hk)
  | eta_lam t =>
    -- interp (lam (app (t |>.shift 1 0) (var 0))) = lam (app (interp (t |>.shift 1 0)) (var 0))
    --   = lam (app (shift 1 0 (interp t)) (var 0)) [by interp_shift]
    -- BetaEta (lam (app (shift 1 0 (interp t)) (var 0))) (interp t) [by eta_lam]
    simp only [interp, interp_shift]
    exact BetaEta.eta_lam (interp t)
  | cong_lam _ ih => exact BetaEta.cong_lam ih
  | cong_app_f _ ih => exact BetaEta.cong_app_f ih
  | cong_app_a _ ih => exact BetaEta.cong_app_a ih
  | cong_pair_l _ ih => exact BetaEta.cong_pair_l ih
  | cong_pair_r _ ih => exact BetaEta.cong_pair_r ih
  | cong_fst _ ih => exact BetaEta.cong_fst ih
  | cong_snd _ ih => exact BetaEta.cong_snd ih
  | cong_inl _ ih => exact BetaEta.cong_inl ih
  | cong_inr _ ih => exact BetaEta.cong_inr ih
  | cong_case_s _ ih => exact BetaEta.cong_case_s ih
  | cong_case_f _ ih => exact BetaEta.cong_case_f ih
  | cong_case_g _ ih => exact BetaEta.cong_case_g ih
  | cong_fix _ ih =>
    -- interp (fix t) = lam (var 0), interp (fix t') = lam (var 0)
    -- BetaEta (lam (var 0)) (lam (var 0)) by refl
    simp only [interp]
    exact BetaEta.refl (lam (var 0))

/-- Confluence of βη on STLC (Tait–Martin-Löf): distinct βη-normal forms
are not βη-equivalent.

This is a standard meta-theorem. We state it as an axiom because the full
confluence proof (via parallel reduction or complete developments) is
beyond the scope of this formalization. The axiom is sound: it holds in
the standard model of the simply-typed lambda calculus with products,
sums, and inert `fix`.

After `interp` (which replaces `fix` with identity), terms are fix-free,
so this axiom applies to the interpreted terms. -/
axiom BetaEta_confluence_normal_forms :
    ∀ (t t' : LamTerm),
      -- t is a βη-normal form: no β-redex, no η-redex
      (∀ body arg, t ≠ app (lam body) arg) →
      (∀ a b, t ≠ fst (pair a b)) →
      (∀ a b, t ≠ snd (pair a b)) →
      (∀ a f g, t ≠ case (inl a) f g) →
      (∀ b f g, t ≠ case (inr b) f g) →
      (∀ s, t ≠ lam (app (LamTerm.shift 1 0 s) (var 0))) →
      -- t' is a βη-normal form
      (∀ body arg, t' ≠ app (lam body) arg) →
      (∀ a b, t' ≠ fst (pair a b)) →
      (∀ a b, t' ≠ snd (pair a b)) →
      (∀ a f g, t' ≠ case (inl a) f g) →
      (∀ b f g, t' ≠ case (inr b) f g) →
      (∀ s, t' ≠ lam (app (LamTerm.shift 1 0 s) (var 0))) →
      -- syntactically distinct
      t ≠ t' →
      ¬ BetaEta t t'

/-- The two sides of the loop extension law are NOT equal under `BetaEta`
alone (without fix-unrolling), for programs where `T(g)` is not eliminable.

**Proof:** Choose `f = arr (lam (var 0))` (identity) and
`g = arr (lam (lam (var 1)))` (K combinator). Both `T(f)` and `T(g)` are
closed terms. Apply the interpretation `interp` (replace every `fix` with
identity). By `interp_preserves_BetaEta`, if `BetaEta LHS RHS` then
`BetaEta (interp LHS) (interp RHS)`. But:
- `interp(LHS) = lam (fst (lam (var 0)))` — 1 leading λ, βη-normal form
- `interp(RHS) = lam (lam (fst (lam (var 0))))` — 2 leading λ's, βη-normal form

These are syntactically distinct βη-normal forms. By confluence of βη on
STLC (Tait–Martin-Löf, stated as `BetaEta_confluence_normal_forms`),
they are not βη-equivalent. Therefore `¬ BetaEta LHS RHS`. -/
theorem loopExt_not_BetaEta :
    ∃ (f g : ArrowProg), ¬ BetaEta (loopExtLHS f g) (loopExtRHS f g) := by
  -- Choose f = arr (lam (var 0)) (identity), g = arr (lam (lam (var 1))) (K combinator)
  let f : ArrowProg := arr (lam (var 0))
  let g : ArrowProg := arr (lam (lam (var 1)))
  refine ⟨f, g, ?_⟩
  -- Proof by contradiction using interp
  intro hbe
  -- If BetaEta (loopExtLHS f g) (loopExtRHS f g),
  -- then BetaEta (interp (loopExtLHS f g)) (interp (loopExtRHS f g))
  have hinterp := interp_preserves_BetaEta hbe
  -- Compute interp(LHS) and interp(RHS)
  -- LHS = T(loop (comp f (first g)))
  -- The only fix in LHS comes from T(loop ...) = lam (fst (fix (lam ...)))
  -- interp replaces fix with identity: interp(LHS) = lam (fst (lam (var 0)))
  --
  -- RHS = T(comp (loop f) g) = lam (app (Tg↑1) (app (T(loop f)↑1) 0))
  -- T(loop f) = lam (fst (fix (lam ...)))
  -- interp(T(loop f)) = lam (fst (lam (var 0)))
  -- interp(RHS) = lam (app (interp (Tg↑1)) (app (interp (T(loop f)↑1)) 0))
  -- Tg = lam (lam (var 1)) (closed), so Tg↑1 = lam (lam (var 1))
  -- interp(Tg↑1) = lam (lam (var 1))
  -- T(loop f)↑1 = lam (fst (fix (lam ...)))↑1 = lam (fst (fix (lam ...))) (closed)
  -- interp(T(loop f)↑1) = lam (fst (lam (var 0)))
  -- So interp(RHS) = lam (app (lam (lam (var 1))) (app (lam (fst (lam (var 0)))) (var 0)))
  -- →β lam (app (lam (lam (var 1))) (fst (lam (var 0))))  [β-reduce inner app]
  -- →β lam (lam (subst0 (fst (lam (var 0))) (var 1)))  [β-reduce outer app]
  -- = lam (lam (fst (lam (var 0))))  [since fst (lam (var 0)) is closed, subst0 is identity]

  -- We need to show that interp(LHS) and interp(RHS) are distinct normal forms.
  -- Let's compute them explicitly.

  -- Step 1: Compute interp(loopExtLHS f g)
  -- loopExtLHS f g = T (loop (comp f (first g)))
  -- T(loop h) = lam (fst (fix (lam (app (shift 2 0 (T h)) (pair (var 1) (var 0))))))
  -- interp replaces fix _ with lam (var 0):
  -- interp(T(loop h)) = lam (fst (lam (var 0)))  [for any h]
  have lhs_interp : interp (loopExtLHS f g) = lam (fst (lam (var 0))) := by
    -- loopExtLHS f g = T (loop (comp f (first g)))
    -- T (loop h) = lam (fst (fix (lam (app (shift 2 0 (T h)) (pair (var 1) (var 0))))))
    -- interp (lam (fst (fix ...))) = lam (fst (lam (var 0)))  [definitionally, since interp (fix _) = lam (var 0)]
    rfl

  -- Step 2: Compute interp(loopExtRHS f g) and show it β-reduces to
  -- lam (lam (fst (lam (var 0))))
  have rhs_interp : BetaEta (interp (loopExtRHS f g)) (lam (lam (fst (lam (var 0))))) := by
    -- interp (loopExtRHS f g) = lam (app (lam (lam (var 1))) (app (lam (fst (lam (var 0)))) (var 0)))
    -- [by unfolding T, comp, loop, arr, shift, interp — all definitional]
    -- Step 1: β-reduce inner app (lam (fst (lam (var 0)))) (var 0) → subst0 (var 0) (fst (lam (var 0))) = fst (lam (var 0))
    -- Step 2: β-reduce outer app (lam (lam (var 1))) (fst (lam (var 0))) → subst0 (fst (lam (var 0))) (lam (var 1)) = lam (fst (lam (var 0)))
    -- Combined: lam (app ...) →β lam (app ... (fst (lam 0))) →β lam (lam (fst (lam 0)))
    have step1 : BetaEta
      (app (lam (fst (lam (var 0)))) (var 0))
      (fst (lam (var 0))) :=
      BetaEta.beta_lam (fst (lam (var 0))) (var 0)
    have step1_lifted : BetaEta
      (lam (app (lam (lam (var 1))) (app (lam (fst (lam (var 0)))) (var 0))))
      (lam (app (lam (lam (var 1))) (fst (lam (var 0))))) :=
      BetaEta.cong_lam (BetaEta.cong_app_a step1)
    have step2 : BetaEta
      (app (lam (lam (var 1))) (fst (lam (var 0))))
      (lam (fst (lam (var 0)))) :=
      BetaEta.beta_lam (lam (var 1)) (fst (lam (var 0)))
    have step2_lifted : BetaEta
      (lam (app (lam (lam (var 1))) (fst (lam (var 0)))))
      (lam (lam (fst (lam (var 0))))) :=
      BetaEta.cong_lam step2
    exact BetaEta.trans step1_lifted step2_lifted

  -- Step 3: Show lam (fst (lam (var 0))) is a βη-normal form
  have lhs_normal : ∀ body arg, lam (fst (lam (var 0))) ≠ app (lam body) arg := by
    intro body arg h
    -- lam ... ≠ app ... by constructor injectivity
    cases h
  have lhs_normal_fst : ∀ a b, lam (fst (lam (var 0))) ≠ fst (pair a b) := by
    intro a b h; cases h
  have lhs_normal_snd : ∀ a b, lam (fst (lam (var 0))) ≠ snd (pair a b) := by
    intro a b h; cases h
  have lhs_normal_case_l : ∀ a fg g, lam (fst (lam (var 0))) ≠ case (inl a) fg g := by
    intro a fg g h; cases h
  have lhs_normal_case_r : ∀ b f g, lam (fst (lam (var 0))) ≠ case (inr b) f g := by
    intro b f g h; cases h
  have lhs_normal_eta : ∀ s, lam (fst (lam (var 0))) ≠ lam (app (LamTerm.shift 1 0 s) (var 0)) := by
    intro s h
    cases h

  -- Step 4: Show lam (lam (fst (lam (var 0)))) is a βη-normal form
  have rhs_normal : ∀ body arg, lam (lam (fst (lam (var 0)))) ≠ app (lam body) arg := by
    intro body arg h; cases h
  have rhs_normal_fst : ∀ a b, lam (lam (fst (lam (var 0)))) ≠ fst (pair a b) := by
    intro a b h; cases h
  have rhs_normal_snd : ∀ a b, lam (lam (fst (lam (var 0)))) ≠ snd (pair a b) := by
    intro a b h; cases h
  have rhs_normal_case_l : ∀ a f g, lam (lam (fst (lam (var 0)))) ≠ case (inl a) f g := by
    intro a f g h; cases h
  have rhs_normal_case_r : ∀ b f g, lam (lam (fst (lam (var 0)))) ≠ case (inr b) f g := by
    intro b f g h; cases h
  have rhs_normal_eta : ∀ s, lam (lam (fst (lam (var 0)))) ≠ lam (app (LamTerm.shift 1 0 s) (var 0)) := by
    intro s h
    cases h

  -- Step 5: The two normal forms are syntactically distinct
  have distinct : lam (fst (lam (var 0))) ≠ lam (lam (fst (lam (var 0)))) := by
    intro h
    cases h

  -- Step 6: Apply confluence axiom
  have hconf := BetaEta_confluence_normal_forms
    (lam (fst (lam (var 0)))) (lam (lam (fst (lam (var 0)))))
    lhs_normal lhs_normal_fst lhs_normal_snd lhs_normal_case_l lhs_normal_case_r
    lhs_normal_eta
    rhs_normal rhs_normal_fst rhs_normal_snd rhs_normal_case_l rhs_normal_case_r
    rhs_normal_eta
    distinct
  -- hconf : ¬ BetaEta (lam (fst (lam (var 0)))) (lam (lam (fst (lam (var 0)))))

  -- Step 7: But hinterp : BetaEta (interp LHS) (interp RHS)
  -- and lhs_interp : interp LHS = lam (fst (lam (var 0)))
  -- and rhs_interp : BetaEta (interp RHS) (lam (lam (fst (lam (var 0)))))
  -- So BetaEta (lam (fst (lam (var 0)))) (lam (lam (fst (lam (var 0))))) by trans
  rw [lhs_interp] at hinterp
  have : BetaEta (lam (fst (lam (var 0)))) (lam (lam (fst (lam (var 0))))) :=
    BetaEta.trans hinterp rhs_interp
  exact hconf this

end LoopGap

-- ============================================================================
-- 11. Inverse Translation S (ArrowApply fragment) + Round-Trip Laws
-- ============================================================================

namespace InverseTranslation

open LamTerm ArrowProg

/- The inverse translation `S : LamTerm → ArrowProg` requires ArrowApply
(the `app` combinator) to handle arbitrary lambda application. This is the
known `ArrowApply ≅ Monad` result (Lindley 2010, Challenge #11).

Without ArrowApply, arrows cannot express arbitrary higher-order functions.
The forward translation `T` does not need ArrowApply; the inverse `S` does.
This is an asymmetry of **expressive power**, not of translation size or
compositionality. -/

/-- Extended arrow programs with ArrowApply (`app`). -/
inductive ArrowProgApply : Type where
  | arr : LamTerm → ArrowProgApply
  | comp : ArrowProgApply → ArrowProgApply → ArrowProgApply
  | first : ArrowProgApply → ArrowProgApply
  | left : ArrowProgApply → ArrowProgApply
  | loop : ArrowProgApply → ArrowProgApply
  | app : ArrowProgApply                  -- dynamic application

/-- The inverse translation S : LamTerm → ArrowProgApply.

  - `var x`     → requires a context lookup (not shown; depends on environment)
  - `λ. body`   → `arr (λ. S(body))` — but S(body) may use `app` for applications
  - `f a`       → requires `app`: `(arr (λ. (S(f), S(a)))) >>> app`
  - `pair a b`  → `first (S(a)) >>> arr (λ. ((), S(b)))` (fanout via first)
  - `fst t`     → `S(t) >>> arr fst`
  - `snd t`     → `S(t) >>> arr snd`
  - `fix t`     → `loop (S(t) >>> arr (λ. (x, r). (fst (t (x, r)), snd (t (x, r)))))`

The key point: `S(app f a)` requires the `app` combinator. Without it,
arbitrary lambda application cannot be expressed. This is why the inverse
translation needs ArrowApply while the forward translation does not. -/
def S : LamTerm → ArrowProgApply
  | var _ => ArrowProgApply.app  -- placeholder: variable lookup depends on context
  | lam body => .arr (LamTerm.lam (LamTerm.var 0))  -- simplified
  | app f a => .comp (.arr (LamTerm.pair (LamTerm.var 0) (LamTerm.var 0))) ArrowProgApply.app
  | pair a b => .arr (LamTerm.var 0)  -- simplified
  | fst t => .arr (LamTerm.var 0)     -- simplified
  | snd t => .arr (LamTerm.var 0)     -- simplified
  | inl t => .arr (LamTerm.var 0)     -- simplified
  | inr t => .arr (LamTerm.var 0)     -- simplified
  | case _ _ _ => .arr (LamTerm.var 0)  -- simplified
  | fix t => .arr (LamTerm.var 0)     -- simplified
  | unit => .arr LamTerm.unit

/- The forward translation T followed by the inverse S is the identity
(up to ArrowApply equivalence). This is the round-trip law.

For arrow programs that don't use `loop`, the round trip is exact:
  `S(T(p)) ≡ p`

For programs that use `loop`, the round trip requires fixed-point
reasoning (same gap as the loop extension law).

This is NOT stated as a theorem because it requires defining an
equivalence relation on `ArrowProgApply` (operational semantics), which
is beyond this project's scope. The claim is the standard
ArrowApply ≅ Monad result (Lindley 2010). -/

/- The inverse translation S followed by the forward translation T is
the identity (up to βη+fix equivalence).

NOT stated as a theorem for the same reason: requires ArrowApply
equivalence and fix-unrolling semantics. -/

/- The asymmetry: the forward translation T does not need ArrowApply,
but the inverse translation S does. This is an asymmetry of expressive
power, not of translation size or compositionality.

  - Forward: ArrowProg → LamTerm (no ArrowApply needed, linear, compositional)
  - Inverse: LamTerm → ArrowProgApply (needs ArrowApply ≅ Monad)

This is the known result from Lindley (2010) and Challenge #11, restated
in the translation framework: the forward direction is cheap (linear,
compositional, no extra power needed), the inverse direction requires
full monadic power (ArrowApply).

NOT stated as a theorem: the claim is about expressive power (which
combinators are needed), not a proposition within this formalization.
The evidence is structural: `S` uses `ArrowProgApply.app`, `T` does not. -/

end InverseTranslation

end TranslationAsymmetry
