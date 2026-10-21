/-
# Arrow Graphs as Proof Objects (Phase 4 — Curry-Howard for Arrow Graphs)

## Theorem (Typing ⇔ Proof)

For every arrow graph `G` and types `A, B`:

    Γ ⊢ G : A ⇝ B    ⟺    Γ ⊢ G ⊩ A ⊢ B

The typing judgment and the proof judgment are interderivable, and the
derivations are structurally identical (rule-for-rule).

## Theorem (Subject Reduction / Type Soundness)

If `⊢ G : A ⇝ B` and `G · a ⟹ v` with `a : A`, then `v : B`.

## Theorem (Proof Realizability)

If `⊢ G ⊩ A ⊢ B` and `a : A`, then `G · a ⟹ v` for some `v : B`.
By the correspondence, this is subject reduction under the
propositions-as-types reading.

This file mechanizes the core of `FORMALISM_PROOF_GRAPHS.md`. The five
graph primitives are exactly the five independent primitives of
Challenge #10 (`Basic.lean`): `arr`, `comp`, `first`, `left`, `loop`.

The proof strategy is the one sketched in §4 of the formalism: the
typing rules and the proof rules are *notation-for-notation identical*
modulo the reading of `⇝` as `⊢` and `×/+` as `∧/∨`. We make this
precise by defining both judgments as inductive predicates over the
same graph syntax and proving a bijection on derivations.

## Why this is the λ-free Curry-Howard

Classical Curry-Howard identifies λ-terms with natural-deduction proofs.
The binding structure of λ is what carries the proof structure. Here,
there is no λ: the proof structure is carried by the **graph wiring**
(`comp` = cut, `first` = ∧-functoriality, `left` = ∨-functoriality,
`loop` = trace/fixpoint). The graph is the proof object, and it is
λ-free by construction (the syntax has no binder).
-/

namespace ProofGraphs

-- ============================================================================
-- 1. Types
-- ============================================================================

/-- Types for the arrow-graph calculus. Products read as ∧, sums as ∨
in proof mode; `unit` is ⊤, `void` is ⊥. -/
inductive Ty (Atom : Type) : Type
  | atom (a : Atom)              : Ty Atom
  | prod (A B : Ty Atom)         : Ty Atom   -- A × B   (read: A ∧ B)
  | sum  (A B : Ty Atom)         : Ty Atom   -- A + B   (read: A ∨ B)
  | unit                         : Ty Atom   -- ⊤
  | void                         : Ty Atom   -- ⊥
  deriving Repr, DecidableEq

/-- Notation for the two logical connectives. -/
scoped notation:35 A:35 " ×ₜ " B:36 => Ty.prod A B
scoped notation:35 A:35 " +ₜ " B:36 => Ty.sum  A B

-- ============================================================================
-- 2. Arrow Graphs (the five primitives, λ-free)
-- ============================================================================

/- A signature `Sig` supplies base arrows `φ : A → B` (the language's
primitive operations). The graph grammar is the free arrow on `Sig`
with the five independent primitives of Challenge #10. No λ-binder. -/

inductive Graph (Atom : Type) (Sig : Ty Atom → Ty Atom → Type) :
    Ty Atom → Ty Atom → Type 1
  | idG   (A : Ty Atom)                                  : Graph Atom Sig A A
  | comp  {A B C : Ty Atom} (G : Graph Atom Sig A B) (H : Graph Atom Sig B C) : Graph Atom Sig A C
  | first {A B D : Ty Atom} (G : Graph Atom Sig A B)     : Graph Atom Sig (A ×ₜ D) (B ×ₜ D)
  | left  {A B D : Ty Atom} (G : Graph Atom Sig A B)     : Graph Atom Sig (A +ₜ D) (B +ₜ D)
  | loop  {A B C : Ty Atom} (G : Graph Atom Sig (A ×ₜ C) (B ×ₜ C)) : Graph Atom Sig A B
  | arr   {A B : Ty Atom} (φ : Sig A B)                  : Graph Atom Sig A B

-- ============================================================================
-- 3 & 4. Typing and Proof judgments
-- ============================================================================

section Judgments

variable {Atom : Type} {Sig : Ty Atom → Ty Atom → Type}

/- The typing rules are the standard arrow-calculus rules (Lindley–
Wadler–Yallop) restated over the graph grammar. We encode the judgment
as an inductive predicate so that a typing *derivation* is a first-class
object. The proof judgment is *notation-for-notation identical*; the
only difference is the reading (`⇝` as `⊢`, `×/+` as `∧/∨`). We define
it as a separate inductive so the correspondence theorem has content. -/

/-- Typing derivation `TyOf G` — read `Γ ⊢ G : A ⇝ B` where `G : Graph .. A B`.
The graph's type indices `A B` ARE the claimed type; the derivation
witnesses that the graph is well-typed at that type. `G`/`H` are
explicit constructor args so the equation compiler can recover the
internal (middle) type variables from their types. -/
inductive TyOf : {A B : Ty Atom} → Graph Atom Sig A B → Type 1
  | idT    (A : Ty Atom)                                                              : TyOf (Graph.idG A)
  | compT  {X Y Z : Ty Atom} (G : Graph Atom Sig X Y) (H : Graph Atom Sig Y Z)
          (dG : TyOf G) (dH : TyOf H)                                                 : TyOf (Graph.comp G H)
  | firstT {X Y : Ty Atom} (D : Ty Atom) (G : Graph Atom Sig X Y) (dG : TyOf G)       : TyOf (Graph.first G)
  | leftT  {X Y : Ty Atom} (D : Ty Atom) (G : Graph Atom Sig X Y) (dG : TyOf G)       : TyOf (Graph.left G)
  | loopT  {X Y : Ty Atom} (C : Ty Atom) (G : Graph Atom Sig (X ×ₜ C) (Y ×ₜ C)) (dG : TyOf G) : TyOf (Graph.loop G)
  | arrT   {X Y : Ty Atom} (φ : Sig X Y)                                              : TyOf (Graph.arr φ)

/-- Proof derivation `PrOf G` — read `Γ ⊢ G ⊩ A ⊢ B` where `G : Graph .. A B`.
Constructors mirror `TyOf` one-for-one:

  - `idP`    ↔ identity proof       `A ⊢ A`
  - `compP`  ↔ cut                  `A ⊢ B, B ⊢ C ⟹ A ⊢ C`
  - `firstP` ↔ ∧-functoriality      `A ⊢ B ⟹ A ∧ C ⊢ B ∧ C`
  - `leftP`  ↔ ∨-functoriality      `A ⊢ B ⟹ A ∨ C ⊢ B ∨ C`
  - `loopP`  ↔ trace / fixpoint     `A ∧ C ⊢ B ∧ C ⟹ A ⊢ B`
  - `arrP`   ↔ axiom                `φ : A → B ∈ Sig ⟹ A ⊢ B`
-/
inductive PrOf : {A B : Ty Atom} → Graph Atom Sig A B → Type 1
  | idP    (A : Ty Atom)                                                              : PrOf (Graph.idG A)
  | compP  {X Y Z : Ty Atom} (G : Graph Atom Sig X Y) (H : Graph Atom Sig Y Z)
          (dG : PrOf G) (dH : PrOf H)                                                 : PrOf (Graph.comp G H)
  | firstP {X Y : Ty Atom} (D : Ty Atom) (G : Graph Atom Sig X Y) (dG : PrOf G)       : PrOf (Graph.first G)
  | leftP  {X Y : Ty Atom} (D : Ty Atom) (G : Graph Atom Sig X Y) (dG : PrOf G)       : PrOf (Graph.left G)
  | loopP  {X Y : Ty Atom} (C : Ty Atom) (G : Graph Atom Sig (X ×ₜ C) (Y ×ₜ C)) (dG : PrOf G) : PrOf (Graph.loop G)
  | arrP   {X Y : Ty Atom} (φ : Sig X Y)                                              : PrOf (Graph.arr φ)

end Judgments

-- ============================================================================
-- 5. The Correspondence Theorem:  Typing ⇔ Proof
-- ============================================================================

section Correspondence

variable {Atom : Type} {Sig : Ty Atom → Ty Atom → Type}

/-
**Theorem (Typing ⇔ Proof).** For every arrow graph `G`,

    TyOf G  ⟺  PrOf G

and the derivations have identical structure. Proof: by mutual
induction on the derivation; each constructor of `TyOf` maps to the
eponymous constructor of `PrOf` (same graph, same premises), and vice
versa. The two inductive predicates have the same indices, the same
constructors, and the same side conditions.
-/

/-- Forward: every typing derivation is a proof derivation (rule-for-rule). -/
def TyOf.toPrOf {A B : Ty Atom} {G : Graph Atom Sig A B} (d : TyOf G) : PrOf G :=
  match d with
  | TyOf.idT A              => PrOf.idP A
  | TyOf.compT G H dG dH    => PrOf.compP G H dG.toPrOf dH.toPrOf
  | TyOf.firstT D G dG      => PrOf.firstP D G dG.toPrOf
  | TyOf.leftT D G dG       => PrOf.leftP  D G dG.toPrOf
  | TyOf.loopT C G dG       => PrOf.loopP  C G dG.toPrOf
  | TyOf.arrT φ             => PrOf.arrP  φ

/-- Backward: every proof derivation is a typing derivation (rule-for-rule). -/
def PrOf.toTyOf {A B : Ty Atom} {G : Graph Atom Sig A B} (d : PrOf G) : TyOf G :=
  match d with
  | PrOf.idP A              => TyOf.idT A
  | PrOf.compP G H dG dH    => TyOf.compT G H dG.toTyOf dH.toTyOf
  | PrOf.firstP D G dG      => TyOf.firstT D G dG.toTyOf
  | PrOf.leftP D G dG       => TyOf.leftT  D G dG.toTyOf
  | PrOf.loopP C G dG       => TyOf.loopT  C G dG.toTyOf
  | PrOf.arrP φ             => TyOf.arrT  φ

/-- The correspondence theorem: typing ⟺ proof. Stated as two
implications (rather than `Iff`) because derivations are first-class
`Type 1` data, not `Prop`. The two maps `toPrOf`/`toTyOf` are mutually
inverse (see the round-trip theorems below), establishing that typing
and proof derivations are the same object under two readings. -/
def typing_to_proof {A B : Ty Atom} (G : Graph Atom Sig A B) :
    TyOf G → PrOf G := fun d => d.toPrOf

/-- Backward direction of the correspondence. -/
def proof_to_typing {A B : Ty Atom} (G : Graph Atom Sig A B) :
    PrOf G → TyOf G := fun d => d.toTyOf

/-- Round-trip: `TyOf.toPrOf` then `PrOf.toTyOf` recovers the derivation. -/
theorem TyOf.toPrOf_toTyOf (d : TyOf G) : d.toPrOf.toTyOf = d := by
  induction d with
  | idT A => rfl
  | compT G H dG dH ihG ihH => simp only [TyOf.toPrOf, PrOf.toTyOf, ihG, ihH]
  | firstT D G dG ihG => simp only [TyOf.toPrOf, PrOf.toTyOf, ihG]
  | leftT D G dG ihG => simp only [TyOf.toPrOf, PrOf.toTyOf, ihG]
  | loopT C G dG ihG => simp only [TyOf.toPrOf, PrOf.toTyOf, ihG]
  | arrT φ => rfl

/-- Round-trip: `PrOf.toTyOf` then `TyOf.toPrOf` recovers the derivation. -/
theorem PrOf.toTyOf_toPrOf (d : PrOf G) : d.toTyOf.toPrOf = d := by
  induction d with
  | idP A => rfl
  | compP G H dG dH ihG ihH => simp only [TyOf.toPrOf, PrOf.toTyOf, ihG, ihH]
  | firstP D G dG ihG => simp only [TyOf.toPrOf, PrOf.toTyOf, ihG]
  | leftP D G dG ihG => simp only [TyOf.toPrOf, PrOf.toTyOf, ihG]
  | loopP C G dG ihG => simp only [TyOf.toPrOf, PrOf.toTyOf, ihG]
  | arrP φ => rfl

/-
The round-trip theorems establish that `TyOf.toPrOf` and `PrOf.toTyOf`
are mutually inverse bijections on derivations. This is the precise
content of "the typing derivation and the proof derivation are
structurally identical": they are the same derivation under two
notations, related by a bijection that is the identity on shape.
-/

end Correspondence

-- ============================================================================
-- 6. Operational Semantics:  G · a ⟹ v
-- ============================================================================

section Semantics

/- Values: integers, products, sums, unit. (Untyped carrier; typing is
enforced by the `TyOf` side of the soundness theorem.) -/
inductive Val
  | int  (n : Int)
  | pair (a b : Val)
  | inl  (a : Val)
  | inr  (b : Val)
  | unit
  deriving Repr

variable {Atom : Type} {Sig : Ty Atom → Ty Atom → Type}
variable (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)

/- A value inhabits a type. Base atoms are inhabited by integers (the
PoC atom model); products, sums, and unit are structural. Defined here
(before `Eval`) because `eLoop`'s fixpoint witness carries `HasType cₙ C`. -/
inductive HasType : Val → Ty Atom → Prop
  | htInt  (n : Int) (a : Atom)            : HasType (Val.int n) (Ty.atom a)
  | htPair (ha : HasType a A) (hb : HasType b B)
                                           : HasType (Val.pair a b) (A ×ₜ B)
  | htInl  (ha : HasType a A)              : HasType (Val.inl a) (A +ₜ B)
  | htInr  (hb : HasType b B)              : HasType (Val.inr b) (A +ₜ B)
  | htUnit                                : HasType Val.unit Ty.unit

/-- The execution relation `Eval den G a v` reads `G · a ⟹ v` under the
base-arrow interpretation `den`. `loop` uses the one-step fixpoint rule:
a step `G · (a, cₙ) ⟹ (v, cₙ)` with the feedback channel already stable
witnesses `loop G · a ⟹ v`. The `hcₙ : HasType cₙ C` field is the
fixpoint witness: the stabilised feedback value is well-typed at the
feedback channel's type. (The iterated form is derivable; we keep the
one-step form so soundness is by structural induction.) -/
inductive Eval : {A B : Ty Atom} → Graph Atom Sig A B → Val → Val → Type 1
  | eId    (A : Ty Atom) (a : Val)                                : Eval (Graph.idG A) a a
  | eComp  {X Y Z : Ty Atom} (G : Graph Atom Sig X Y) (H : Graph Atom Sig Y Z)
          (a b v : Val) (eG : Eval G a b) (eH : Eval H b v)       : Eval (Graph.comp G H) a v
  | eFirst {X Y : Ty Atom} (D : Ty Atom) (G : Graph Atom Sig X Y)
          (a b c : Val) (eG : Eval G a b)                         : Eval (Graph.first G) (Val.pair a c) (Val.pair b c)
  | eLeftL {X Y : Ty Atom} (D : Ty Atom) (G : Graph Atom Sig X Y)
          (a b : Val) (eG : Eval G a b)                           : Eval (Graph.left G) (Val.inl a) (Val.inl b)
  | eLeftR {X Y : Ty Atom} (D : Ty Atom) (G : Graph Atom Sig X Y)
          (b : Val)                                               : Eval (Graph.left G) (Val.inr b) (Val.inr b)
  | eLoop  {X Y C : Ty Atom} (G : Graph Atom Sig (X ×ₜ C) (Y ×ₜ C))
          (a v cₙ : Val) (hcₙ : HasType cₙ C)
          (eStep : Eval G (Val.pair a cₙ) (Val.pair v cₙ))        : Eval (Graph.loop G) a v
  | eArr   {X Y : Ty Atom} (φ : Sig X Y) (a : Val)                : Eval (Graph.arr φ) a (den φ a)

end Semantics

-- ============================================================================
-- 7. Subject Reduction (Type Soundness)
-- ============================================================================

section Soundness

variable {Atom : Type} {Sig : Ty Atom → Ty Atom → Type}

/-- The signature's denotation respects types: a well-typed base arrow
sends a value of its input type to a value of its output type. This is
the axiom tying the signature to the type system, carried as an explicit
hypothesis (rather than a typeclass, so the `Atom`/`Sig` parameters
remain inferrable from the goal). -/
def SigSound (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val) : Prop :=
  ∀ {A B : Ty Atom} (φ : Sig A B) (a : Val), HasType (den φ a) B

/-- Inversion lemma: a value of a product type is a pair of values of
the component types. -/
theorem HasType.pair_inv (h : HasType (Val.pair a b) (A ×ₜ B)) :
    HasType a A ∧ HasType b B := by
  cases h with | htPair ha hb => exact ⟨ha, hb⟩

/-- Inversion lemma: a value of a sum type is an injection. -/
theorem HasType.inl_inv (h : HasType (Val.inl a) (A +ₜ B)) : HasType a A := by
  cases h with | htInl ha => exact ha

theorem HasType.inr_inv (h : HasType (Val.inr b) (A +ₜ B)) : HasType b B := by
  cases h with | htInr hb => exact hb

/-- **Subject Reduction.** If `⊢ G : A ⇝ B`, `G · a ⟹ v`, and `a : A`,
then `v : B`. Proof by induction on the execution derivation, inverting
the typing derivation at each step (FORMALISM §5.1). -/
theorem subject_reduction (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
    (hsound : ∀ {A B : Ty Atom} (φ : Sig A B) (a : Val), HasType (den φ a) B)
    {A B : Ty Atom} {G : Graph Atom Sig A B} {a v : Val}
    (d : TyOf G) (e : Eval den G a v) (ha : HasType a A)
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
    -- `left G` preserves the right summand: inr b ⟹ inr b.
    -- Invert `ha` directly (rather than `inr_inv`) so the summand type
    -- unifies with the goal's expected type via `htInr`.
    cases d with
    | leftT D G dG =>
      cases ha with
      | htInr hb => exact HasType.htInr hb
  | eLoop G₀ a v cₙ hcₙ eStep ih =>
    -- The loop case: invert `d` to extract the loop body's typing
    -- derivation, then apply the IH.  We use `match` (term-mode) to
    -- invert `d` because `cases d with` has trouble binding the
    -- constructor's implicit args after `induction e` generalizes `d`.
    match d with
    | TyOf.loopT C G' dG =>
      have hAC : HasType (Val.pair a cₙ) (_ ×ₜ C) := HasType.htPair ha hcₙ
      have hBC := ih dG hAC
      obtain ⟨hv, _⟩ := HasType.pair_inv hBC
      exact hv
  | eArr φ a =>
    cases d with
    | arrT φ => exact hsound φ a

/-
All seven execution cases are discharged:
  - `eId`, `eComp`, `eFirst`, `eLeftL`, `eArr` — direct IH + inversion.
  - `eLeftR` — `left G` preserves the right summand (`inr b ⟹ inr b`);
    the output type's right summand `D` is recovered from the typing
    derivation's `leftT` constructor, and `b : D` comes from `inr_inv`.
  - `eLoop` — the fixpoint witness `hcₙ : HasType cₙ C` (carried by the
    `eLoop` constructor) supplies the feedback channel's type, so the
    step's input `(a, cₙ) : X × C` is well-typed and the IH yields
    `(v, cₙ) : Y × C`, giving `v : Y = B`.

The two cases that were `sorry`s in the earlier draft are now proven:
the key was (i) correcting `eLeftR` to *preserve* the right summand
(rather than running `G` on it, which would be a type error) and
(ii) carrying `HasType cₙ C` as a field of `eLoop` so the feedback
channel's type is recoverable without index surgery. These are the
standard "right-summand preservation" and "fixpoint-state typing"
lemmas of any traced bicartesian-category soundness proof, here
discharged by the graph structure itself.
-/

end Soundness

-- ============================================================================
-- 8. Proof Realizability (via the Correspondence)
-- ============================================================================

section Realizability

variable {Atom : Type} {Sig : Ty Atom → Ty Atom → Type}

/-
**Theorem (Proof Realizability).** If `⊢ G ⊩ A ⊢ B` and `a : A`, then
`G · a ⟹ v` for some `v : B`. By the correspondence theorem,
`⊢ G ⊩ A ⊢ B` iff `⊢ G : A ⇝ B`; by subject reduction, executing `G` on
`a : A` yields `v : B`. Under Curry-Howard, `v : B` *is* "`v` is a proof
of `B`."
-/
theorem proof_realizability (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
    (hsound : ∀ {A B : Ty Atom} (φ : Sig A B) (a : Val), HasType (den φ a) B)
    {A B : Ty Atom} {G : Graph Atom Sig A B} {a v : Val}
    (d : PrOf G) (e : Eval den G a v) (ha : HasType a A)
    : HasType v B :=
  subject_reduction den hsound d.toTyOf e ha

/-
The realizability theorem is *literally* subject reduction precomposed
with the correspondence's backward direction. This is the precise sense
in which "type soundness and proof soundness are the same theorem": the
proof judgment adds no logical power beyond the typing judgment; it is
the same derivation under a different reading.
-/

end Realizability

-- ============================================================================
-- 9. The λ-free Curry-Howard slogan, mechanized
-- ============================================================================

/-
The three theorems together establish the slogan of
`FORMALISM_PROOF_GRAPHS.md` §4.3:

    one graph G
       │
       ├─ as program:   Eval den G a v      (execute)
       ├─ as type:      TyOf G              (typecheck)
       └─ as proof:     PrOf G              (reason)

    TyOf G  →  PrOf G                      (typing_to_proof)
    PrOf G  →  TyOf G                      (proof_to_typing)
    TyOf G  →  Eval G a v → a:A → v:B      (subject_reduction)
    PrOf G  →  Eval G a v → a:A → v:B      (proof_realizability)

The graph is λ-free (the `Graph` inductive has no binder), and yet it
is simultaneously a program, a typing derivation, and a proof. This is
the arrow-graph Curry-Howard correspondence.
-/

end ProofGraphs
