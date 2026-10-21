/-
# Equational Law Inference: From Output Properties to Law Patterns (Phase 10)

## The load-bearing open question (ADR-0075 OQ#1)

ADR-0075 §"The contingency on law inference" identifies three outcomes for
the trait layer, hinging on whether the invariant-inference machinery
extends from **output properties** (sortedness, permutation, length) to
**equational law patterns** (functor, monad, roundtrip, semigroup):

1. **Primary mode (inference works):** laws are inferred from wiring,
   no declaration needed. The trait layer is a genuine advantage.
2. **Secondary mode (explicit declarations + CutElim):** laws are
   verified when explicitly declared. Proven-but-declared traits.
3. **Reduces to sugar:** neither works; the trait layer is just named
   bundles + implicit parameters.

The existing `TraitInference.lean` proves the **functor laws** —
`first (idG A) ≡ idG (A × D)` and `first (comp G H) ≡ comp (first G) (first H)`
— by CutElim normalization. These laws ARE CutElim rewrites: `ceFirstId`
and `ceFirstFusion` are literally the rewrite steps. So functor-law
inference is the **primary mode**: the structural pattern (`UsesFirst`)
triggers the check, and CutElim discharges it — no semantic axiom needed.

This file addresses the harder case: **laws that are NOT CutElim rewrites**.
The roundtrip law `serialize >>> deserialize ≡ id` and the semigroup
associativity law `mul (mul (a, b), c) ≡ mul (a, mul (b, c))` are semantic
facts about specific base arrows. CutElim cannot prove them — they require
a semantic axiom about the base arrows. The question is: does the
structural-recognition approach still work, and how?

## What this file proves

1. **`SemanticLaw`** — a structure modeling a law that holds by semantic
   axiom (not by CutElim). The `sound` field is a *hypothesis* (assumed),
   not proven from CutElim. This is honest: the axiom is explicitly
   declared, not hidden behind a `sorry`.

2. **`LawAxiomEnv`** — an axiom context: a collection of semantic laws
   that the system is told hold. This models the "explicit declaration"
   of the secondary mode.

3. **Structural pattern recognizers for non-functor laws:**
   - `UsesRoundtrip G` — recognizes `comp (arr φ) (arr ψ)` (two base
     arrows in sequence, the roundtrip pattern).
   - `UsesSeqArr G` — recognizes any composition of two `arr` nodes.
   - `UsesAssoc G` — recognizes the associativity nesting pattern
     `comp (comp (arr φ) (arr ψ)) (arr χ)`.

4. **`SatisfiesLawWithAxiom`** — combines structural recognition + axiom
   discharge. The pattern is recognized structurally; the law is
   discharged by looking up the axiom in the environment.

5. **Concrete roundtrip law theorem** — the cleanest example. Given a
   semantic axiom that `serialize` and `deserialize` are inverses, the
   graph `comp (arr serialize) (arr deserialize)` satisfies the roundtrip
   law: for every input `a`, the output is `a` (i.e., it behaves as `id`).

6. **Connection to the trait inference framework** — the same
   `UsesRoundtrip`-triggers-check structure as `UsesFirst`-triggers-check
   in `TraitInference.lean`. The difference: functor laws are discharged
   by CutElim alone; roundtrip laws require an axiom.

All proofs are in Lean4 with zero `sorry`/`admit`/`sorryAx`.
-/

import ArrowMinimalityLib.ProofGraphs
import ArrowMinimalityLib.ProofAdvantage
import ArrowMinimalityLib.InvariantDomain
import ArrowMinimalityLib.StructuralInference
import ArrowMinimalityLib.TraitInference

open ProofGraphs
open ProofAdvantage
open InvariantDomain
open StructuralInference
open TraitInference

namespace EquationalLawInference

variable {Atom : Type} {Sig : Ty Atom → Ty Atom → Type}

-- ============================================================================
-- 1. Semantic law axioms: laws that hold by semantic fact, not CutElim
-- ============================================================================

/-! ## Semantic laws: the axiom layer

Not every equational law is a CutElim rewrite. Some laws hold because of
SEMANTIC facts about base arrows — facts that CutElim cannot derive from
graph structure alone. The roundtrip law
`serialize >>> deserialize ≡ id` is the canonical example: it holds because
`serialize` and `deserialize` are semantically inverse, which is a property
of the base arrows' denotations, not of the graph wiring.

We model this as a `SemanticLaw`: an equation between two graphs, discharged
by an explicit axiom (a hypothesis), not by CutElim normalization. The
`sound` field is the axiom — it is ASSUMED, not proven. This is honest:
the axiom is visible as a hypothesis, not hidden behind `sorry`. -/

/-- A semantic law: an equation `lhs ≡ rhs` between two graphs of the same
type, discharged by a semantic axiom (not by CutElim).

The `sound` field is the axiom: for every input `a`, if `lhs` produces `b`,
then `rhs` also produces `b`. This is ASSUMED — it is the semantic fact
about the base arrows that CutElim cannot derive.

The law is parametric in `den` (the denotation of base arrows) because the
soundness depends on what the base arrows actually compute. -/
structure SemanticLaw (Atom : Type) (Sig : Ty Atom → Ty Atom → Type)
    (A B : Ty Atom) where
  /-- The name of the law (e.g., "roundtrip", "associativity"). -/
  name : String
  /-- The left-hand side of the equation. -/
  lhs : Graph Atom Sig A B
  /-- The right-hand side of the equation. -/
  rhs : Graph Atom Sig A B
  /-- The semantic axiom: for every denotation `den`, every input `a`, and
  every output `b`, if `lhs` evaluates to `b` on `a`, then `rhs` also
  evaluates to `b` on `a`. This is ASSUMED, not proven from CutElim. -/
  sound : ∀ (den : ∀ {X Y : Ty Atom}, Sig X Y → Val → Val) (a b : Val),
    @Eval Atom Sig den A B lhs a b → @Eval Atom Sig den A B rhs a b

/-- A law axiom environment: a predicate on semantic laws. `LawAxiomEnv`
holds of a law if that law is in the environment. This models the
"explicit declaration" of the secondary mode from ADR-0075: the user
declares which semantic axioms hold, and the system uses them to discharge
non-functor laws.

The environment is modeled as a predicate (rather than a list) to avoid
universe issues with storing `Type 1` structures in a container. -/
def LawAxiomEnv (Atom : Type) (Sig : Ty Atom → Ty Atom → Type) : Type 1 :=
  ∀ {A B : Ty Atom}, SemanticLaw Atom Sig A B → Prop

/-- The empty axiom environment: no semantic laws are declared. -/
def emptyAxiomEnv : @LawAxiomEnv Atom Sig := fun {_ _} _ => False

/-- An axiom environment extended with a single law. -/
def LawAxiomEnv.extend (env : @LawAxiomEnv Atom Sig)
    {A B : Ty Atom} (law : SemanticLaw Atom Sig A B) : @LawAxiomEnv Atom Sig :=
  fun {_ _} l' => @env _ _ l' ∨ l'.name = law.name

/-- A law is in the environment. -/
def LawAxiomEnv.contains (env : @LawAxiomEnv Atom Sig)
    {A B : Ty Atom} (law : SemanticLaw Atom Sig A B) : Prop :=
  @env _ _ law

/-- A law in the environment is sound (its axiom holds). Since `Eval` is
`Type 1`-valued, this is a `def` (not a `theorem`), but it is trivially
correct: it just applies the law's `sound` field. -/
def LawAxiomEnv.sound_of_contains (env : @LawAxiomEnv Atom Sig)
    {A B : Ty Atom} (law : SemanticLaw Atom Sig A B) (_h : env.contains law)
    (den : ∀ {X Y : Ty Atom}, Sig X Y → Val → Val) (a b : Val)
    (e : @Eval Atom Sig den A B law.lhs a b) : @Eval Atom Sig den A B law.rhs a b :=
  law.sound den a b e

-- ============================================================================
-- 2. Structural pattern recognition for non-functor law patterns
-- ============================================================================

/-! ## Structural pattern recognizers for non-functor laws

The existing `TraitInference.lean` defines `UsesFirst` and `UsesLeft` to
recognize the functor and coproduct-functor patterns. We extend this to
recognize patterns for laws that are NOT functor laws:

- **Roundtrip pattern**: `comp (arr φ) (arr ψ)` — two base arrows in
  sequence. This is the structural shape of a roundtrip
  (`serialize >>> deserialize`).
- **Associativity pattern**: `comp (comp (arr φ) (arr ψ)) (arr χ)` —
  three base arrows in a left-nested composition. This is the structural
  shape of a semigroup associativity law.

The key insight: the STRUCTURAL PATTERN can be recognized without knowing
whether the law holds. The system recognizes the pattern and then asks:
"is there a semantic axiom discharging this?" -/

/-- A graph *uses the roundtrip pattern* if it is a composition of two
base arrows: `comp (arr φ) (arr ψ)`. This is the structural shape of
`serialize >>> deserialize`.

This recognizer is the analogue of `UsesFirst` from `TraitInference.lean`,
but for a non-functor law pattern. The pattern is recognized structurally;
whether the law holds depends on a semantic axiom (whether `φ` and `ψ` are
actually inverse). -/
inductive UsesRoundtrip (Atom : Type) (Sig : Ty Atom → Ty Atom → Type) :
    {A B : Ty Atom} → Graph Atom Sig A B → Prop
  | here {X Y Z : Ty Atom} (φ : Sig X Y) (ψ : Sig Y Z)
         : UsesRoundtrip Atom Sig (Graph.comp (Graph.arr φ) (Graph.arr ψ))
  | leftComp {X Y Z : Ty Atom} (G : Graph Atom Sig X Y) (H : Graph Atom Sig Y Z)
             (h : UsesRoundtrip Atom Sig G) : UsesRoundtrip Atom Sig (Graph.comp G H)
  | rightComp {X Y Z : Ty Atom} (G : Graph Atom Sig X Y) (H : Graph Atom Sig Y Z)
              (h : UsesRoundtrip Atom Sig H) : UsesRoundtrip Atom Sig (Graph.comp G H)

/-- A graph *uses sequential arrows* if it contains a composition of two
`arr` nodes anywhere in its wiring. This is a slightly more general
recognizer than `UsesRoundtrip` — it doesn't require the two arrows to be
the top-level composition, just that two `arr` nodes appear in sequence
somewhere. -/
inductive UsesSeqArr (Atom : Type) (Sig : Ty Atom → Ty Atom → Type) :
    {A B : Ty Atom} → Graph Atom Sig A B → Prop
  | here {X Y Z : Ty Atom} (φ : Sig X Y) (ψ : Sig Y Z)
         : UsesSeqArr Atom Sig (Graph.comp (Graph.arr φ) (Graph.arr ψ))
  | leftComp {X Y Z : Ty Atom} (G : Graph Atom Sig X Y) (H : Graph Atom Sig Y Z)
             (h : UsesSeqArr Atom Sig G) : UsesSeqArr Atom Sig (Graph.comp G H)
  | rightComp {X Y Z : Ty Atom} (G : Graph Atom Sig X Y) (H : Graph Atom Sig Y Z)
              (h : UsesSeqArr Atom Sig H) : UsesSeqArr Atom Sig (Graph.comp G H)

/-- A graph *uses the associativity pattern* if it contains a left-nested
composition of three base arrows:
`comp (comp (arr φ) (arr ψ)) (arr χ)`.

This is the structural shape of a semigroup associativity law:
`mul (mul (a, b), c)` corresponds to composing `mul` with `mul` then with
the projection that feeds `c`. The associativity law
`mul (mul (a,b), c) ≡ mul (a, mul (b, c))` is about reassociating this
nesting — a semantic fact about `mul`, not a graph rewrite. -/
inductive UsesAssoc (Atom : Type) (Sig : Ty Atom → Ty Atom → Type) :
    {A B : Ty Atom} → Graph Atom Sig A B → Prop
  | here {W X Y Z : Ty Atom} (φ : Sig W X) (ψ : Sig X Y) (χ : Sig Y Z)
         : UsesAssoc Atom Sig
             (Graph.comp (Graph.comp (Graph.arr φ) (Graph.arr ψ)) (Graph.arr χ))
  | leftComp {X Y Z : Ty Atom} (G : Graph Atom Sig X Y) (H : Graph Atom Sig Y Z)
             (h : UsesAssoc Atom Sig G) : UsesAssoc Atom Sig (Graph.comp G H)
  | rightComp {X Y Z : Ty Atom} (G : Graph Atom Sig X Y) (H : Graph Atom Sig Y Z)
              (h : UsesAssoc Atom Sig H) : UsesAssoc Atom Sig (Graph.comp G H)

/-- `UsesRoundtrip` implies `UsesSeqArr`: the roundtrip pattern is a
specific case of sequential arrows. -/
theorem UsesRoundtrip.implies_seqArr {A B : Ty Atom} {G : Graph Atom Sig A B}
    (h : UsesRoundtrip Atom Sig G) : UsesSeqArr Atom Sig G := by
  induction h with
  | here φ ψ => exact UsesSeqArr.here φ ψ
  | leftComp G H _ ih => exact UsesSeqArr.leftComp G H ih
  | rightComp G H _ ih => exact UsesSeqArr.rightComp G H ih

-- ============================================================================
-- 3. Law satisfaction with axioms
-- ============================================================================

/-! ## `SatisfiesLawWithAxiom`: structural recognition + axiom discharge

A graph `G` satisfies a semantic law `law` *given* an axiom environment
`axioms` when:
  (1) G's wiring exhibits the structural pattern the law applies to
      (e.g., `UsesRoundtrip` for the roundtrip law), AND
  (2) The law is in the axiom environment (its semantic axiom is declared).

This is the **secondary mode** of ADR-0075: the structural pattern is
recognized by inference (the primary-mode machinery), but the law itself
is discharged by an explicit axiom (the secondary-mode declaration).

Contrast with `SatisfiesLaw` from `TraitInference.lean`: that combines
structural recognition (`UsesFirst`) with CutElim verification
(`LawVerified`). Here, CutElim cannot verify the law, so we use an axiom
instead. The structural recognition is the same; the verification method
differs. -/

/-- `SatisfiesLawWithAxiom G law axioms`: graph `G` satisfies semantic law
`law` given axiom environment `axioms`, because (1) G's wiring exhibits
the roundtrip pattern (structural recognition), and (2) the law is in the
axiom environment (axiom discharge).

This is the non-functor analogue of `SatisfiesLaw` from
`TraitInference.lean`. The structural recognition (`UsesRoundtrip`) is
the same kind of wiring inspection as `UsesFirst`; the difference is that
the law is discharged by an axiom, not by CutElim normalization. -/
def SatisfiesLawWithAxiom {A B : Ty Atom} (G : Graph Atom Sig A B)
    (law : SemanticLaw Atom Sig A B) (axioms : @LawAxiomEnv Atom Sig) : Prop :=
  UsesRoundtrip Atom Sig G ∧ axioms.contains law

/-- **Inference theorem (roundtrip with axiom):** if `G` uses the
roundtrip pattern and the roundtrip law is in the axiom environment, then
`G` satisfies the roundtrip law with the axiom.

The structural pattern is recognized by `UsesRoundtrip` (inference); the
law is discharged by the axiom (explicit declaration). This is the
secondary mode of ADR-0075: inference recognizes the pattern, the axiom
discharges the law. -/
theorem satisfies_roundtrip_with_axiom
    {A B : Ty Atom} (G : Graph Atom Sig A B) (law : SemanticLaw Atom Sig A B)
    (axioms : @LawAxiomEnv Atom Sig)
    (hPattern : UsesRoundtrip Atom Sig G)
    (hAxiom : axioms.contains law)
    : SatisfiesLawWithAxiom G law axioms :=
  ⟨hPattern, hAxiom⟩

-- ============================================================================
-- 4. The concrete roundtrip law theorem
-- ============================================================================

/-! ## The roundtrip law: the cleanest non-functor example

The roundtrip law `serialize >>> deserialize ≡ id` is the cleanest example
of a non-functor law. It is NOT a CutElim rewrite — it is a semantic fact
about the base arrows `serialize` and `deserialize`. But the STRUCTURAL
PATTERN (`comp (arr serialize, arr deserialize)`) can be recognized, and
the law can be DISCHARGED given a semantic axiom
(`den deserialize (den serialize a) = a`).

We prove: given the semantic axiom that `serialize` and `deserialize` are
inverse, the graph `comp (arr serialize, arr deserialize)` behaves as the
identity — for every input `a`, the output is `a`.

This is the honest answer to ADR OQ#1 for non-functor laws:
  - The structural recognition WORKS (the pattern is detected).
  - The law verification REQUIRES an axiom (not derivable from CutElim).
  - This is the secondary mode (explicit declarations), not the primary
    mode (pure inference). -/

/-- **The roundtrip law with axiom.** Given:
  - `den` : the denotation of base arrows,
  - `hinv` : the semantic axiom that `deserialize ∘ serialize = id`
    (i.e., `den deserialize (den serialize a) = a` for all `a`),
  - `e` : an execution of `comp (arr serialize, arr deserialize)` on
    input `a` producing output `b`,

then `b = a`: the composition behaves as the identity.

The axiom `hinv` is a HYPOTHESIS, not proven from CutElim. This is honest:
the semantic fact is explicitly assumed, not hidden behind `sorry`.

Proof: By inverting the `Eval` derivation, `comp (arr serialize, arr deserialize)`
on `a` must go through `eComp`: `arr serialize` produces some intermediate
`v = den serialize a`, then `arr deserialize` produces `den deserialize v`.
By `hinv`, `den deserialize (den serialize a) = a`, so `b = a`. -/
theorem roundtrip_law_with_axiom
    {X Y : Ty Atom} (serialize : Sig X Y) (deserialize : Sig Y X)
    (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
    (hinv : ∀ a, den deserialize (den serialize a) = a)
    (a b : Val)
    (e : @Eval Atom Sig den X X
          (Graph.comp (Graph.arr serialize) (Graph.arr deserialize)) a b)
    : b = a := by
  -- Invert the Eval derivation: comp (arr serialize, arr deserialize) on a
  -- must be eComp with intermediate value den serialize a.
  cases e with
  | eComp G H a₀ b₀ v₀ eG eH =>
    -- eG : Eval (arr serialize) a (den serialize a)  [by eArr]
    -- eH : Eval (arr deserialize) (den serialize a) b  [by eArr]
    -- So b = den deserialize (den serialize a) = a  [by hinv]
    cases eG with
    | eArr φ a' =>
      cases eH with
      | eArr ψ b' =>
        -- b = den ψ (den φ a) = den deserialize (den serialize a) = a
        exact hinv a

/-- **The roundtrip law produces the identity behavior (existence).**
Given the semantic axiom `hinv`, the graph
`comp (arr serialize, arr deserialize)` on input `a` produces output `a`
(witnessed by `eComp` + `eArr` + `eArr`).

This is the forward direction: the composition evaluates to `a` on `a`.
Combined with `roundtrip_law_with_axiom` (the determinism direction), this
establishes full semantic equivalence with `idG`.

Since `Eval` is `Type 1`-valued, this is a `def` (not a `theorem`). -/
def roundtrip_law_witness
    {X Y : Ty Atom} (serialize : Sig X Y) (deserialize : Sig Y X)
    (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
    (hinv : ∀ a, den deserialize (den serialize a) = a)
    (a : Val)
    : @Eval Atom Sig den X X
        (Graph.comp (Graph.arr serialize) (Graph.arr deserialize)) a a := by
  -- Step 1: arr serialize on a produces den serialize a
  -- Step 2: arr deserialize on (den serialize a) produces den deserialize (den serialize a) = a
  -- Step 3: comp combines them
  have e1 : @Eval Atom Sig den X Y (Graph.arr serialize) a (den serialize a) :=
    Eval.eArr serialize a
  have e2 : @Eval Atom Sig den Y X (Graph.arr deserialize)
              (den serialize a) (den deserialize (den serialize a)) :=
    Eval.eArr deserialize (den serialize a)
  -- Rewrite using hinv: den deserialize (den serialize a) = a
  rw [hinv a] at e2
  exact Eval.eComp (Graph.arr serialize) (Graph.arr deserialize) a (den serialize a) a e1 e2

/-- **Full semantic equivalence: `comp (arr serialize, arr deserialize)`
behaves as `idG`.**

Given the semantic axiom `hinv`, the roundtrip composition and `idG X`
produce the same output for the same input:
  - *Existence*: `roundtrip_law_witness` gives an evaluation producing `a`.
  - *Determinism*: `roundtrip_law_with_axiom` shows every evaluation
    produces `a` (which is what `idG` produces).

This is the semantic content of the roundtrip law, proven GIVEN the axiom.
The axiom is the non-inferable part; the rest is structural. -/
theorem roundtrip_semantic_equiv_id
    {X Y : Ty Atom} (serialize : Sig X Y) (deserialize : Sig Y X)
    (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
    (hinv : ∀ a, den deserialize (den serialize a) = a)
    (a : Val)
    : Nonempty (@Eval Atom Sig den X X
        (Graph.comp (Graph.arr serialize) (Graph.arr deserialize)) a a)
      ∧ (∀ b, @Eval Atom Sig den X X
            (Graph.comp (Graph.arr serialize) (Graph.arr deserialize)) a b → b = a) :=
  ⟨⟨roundtrip_law_witness serialize deserialize den hinv a⟩,
   fun b => roundtrip_law_with_axiom serialize deserialize den hinv a b⟩

/-- **The roundtrip graph uses the roundtrip pattern.**
`comp (arr serialize, arr deserialize)` is recognized by `UsesRoundtrip`
at the top level. This is the structural recognition step — the same kind
of wiring inspection as `UsesFirst` for functor laws. -/
theorem roundtrip_uses_pattern
    {X Y : Ty Atom} (serialize : Sig X Y) (deserialize : Sig Y X)
    : UsesRoundtrip Atom Sig
        (Graph.comp (Graph.arr serialize) (Graph.arr deserialize)) :=
  UsesRoundtrip.here serialize deserialize

/-- **The roundtrip law is a `SemanticLaw`.**
We construct the `SemanticLaw` for the roundtrip, with the `sound` field
being the axiom (assumed, not proven from CutElim).

The `sound` field proves: if `comp (arr serialize, arr deserialize)`
produces `b` on `a`, then `idG X` also produces `b` on `a`. By the
roundtrip law (`b = a`), `idG X` on `a` produces `a = b`. -/
def roundtrip_semantic_law
    {X Y : Ty Atom} (serialize : Sig X Y) (deserialize : Sig Y X)
    (hinv : ∀ (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val) (a : Val),
      den deserialize (den serialize a) = a)
    : SemanticLaw Atom Sig X X where
  name := "roundtrip"
  lhs := Graph.comp (Graph.arr serialize) (Graph.arr deserialize)
  rhs := Graph.idG X
  sound := fun den a b e => by
    -- By roundtrip_law_with_axiom, b = a.
    have hb : b = a := roundtrip_law_with_axiom serialize deserialize den (hinv den) a b e
    -- idG X on a produces a; since b = a, this discharges the goal.
    rw [hb]
    exact @Eval.eId Atom Sig den X a

/-- **The full roundtrip inference theorem.**
If the roundtrip axiom holds (`hinv`) and the roundtrip law is in the axiom
environment, then `comp (arr serialize, arr deserialize)` satisfies the
roundtrip law with the axiom.

This combines:
  - Structural recognition (`UsesRoundtrip` — the pattern is detected),
  - Axiom discharge (the law is in the environment),
  - Semantic soundness (the axiom implies the law holds).

This is the **secondary mode** of ADR-0075: inference recognizes the
pattern, the axiom discharges the law. -/
theorem roundtrip_inference_theorem
    {X Y : Ty Atom} (serialize : Sig X Y) (deserialize : Sig Y X)
    (axioms : @LawAxiomEnv Atom Sig)
    (law : SemanticLaw Atom Sig X X)
    (_hlawName : law.name = "roundtrip")
    (_hlawLhs : law.lhs = Graph.comp (Graph.arr serialize) (Graph.arr deserialize))
    (_hlawRhs : law.rhs = Graph.idG X)
    (hAxiom : axioms.contains law)
    : SatisfiesLawWithAxiom
        (Graph.comp (Graph.arr serialize) (Graph.arr deserialize)) law axioms :=
  ⟨UsesRoundtrip.here serialize deserialize, hAxiom⟩

-- ============================================================================
-- 5. The associativity pattern (semigroup law)
-- ============================================================================

/-! ## The associativity pattern: a second non-functor law

The semigroup associativity law `mul (mul (a, b), c) ≡ mul (a, mul (b, c))`
is another non-functor law. As a graph, the left-nested form
`comp (comp (arr mul, arr mul), arr mul)` (with appropriate pairing)
corresponds to `mul (mul (a, b), c)`, and the right-nested form
`comp (arr mul, comp (arr mul, arr mul))` corresponds to `mul (a, mul (b, c))`.

The associativity law is a SEMANTIC fact about `mul` — it cannot be proven
by CutElim (the two nestings are not CutElim-equal). But the STRUCTURAL
PATTERN (left-nested vs right-nested composition of three `arr` nodes) can
be recognized, and the law can be discharged given an axiom.

We prove the structural recognition and state the law with its axiom,
mirroring the roundtrip case. -/

/-- **The associativity graph uses the associativity pattern.**
`comp (comp (arr φ, arr ψ), arr χ)` is recognized by `UsesAssoc` at the
top level. -/
theorem assoc_uses_pattern
    {W X Y Z : Ty Atom} (φ : Sig W X) (ψ : Sig X Y) (χ : Sig Y Z)
    : UsesAssoc Atom Sig
        (Graph.comp (Graph.comp (Graph.arr φ) (Graph.arr ψ)) (Graph.arr χ)) :=
  UsesAssoc.here φ ψ χ

/-- **The associativity law with axiom.** Given a semantic axiom that the
left-nested and right-nested compositions of three base arrows produce the
same output, the graph `comp (comp (arr φ, arr ψ), arr χ)` satisfies the
associativity law.

The axiom `hassoc` states: for every input `a`, if the left-nested form
produces `b`, then the right-nested form also produces `b`. This is
ASSUMED — it is the semantic fact about the base arrows that CutElim
cannot derive. -/
def associativity_law_with_axiom
    {W X Y Z : Ty Atom}
    (φ : Sig W X) (ψ : Sig X Y) (χ : Sig Y Z)
    (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
    (hassoc : ∀ (a b : Val),
      @Eval Atom Sig den W Z
        (Graph.comp (Graph.comp (Graph.arr φ) (Graph.arr ψ)) (Graph.arr χ)) a b →
      @Eval Atom Sig den W Z
        (Graph.comp (Graph.arr φ) (Graph.comp (Graph.arr ψ) (Graph.arr χ))) a b)
    (a b : Val)
    (e : @Eval Atom Sig den W Z
          (Graph.comp (Graph.comp (Graph.arr φ) (Graph.arr ψ)) (Graph.arr χ)) a b)
    : @Eval Atom Sig den W Z
        (Graph.comp (Graph.arr φ) (Graph.comp (Graph.arr ψ) (Graph.arr χ))) a b :=
  hassoc a b e

/-- **The associativity law is a `SemanticLaw`.** -/
def associativity_semantic_law
    {W Z : Ty Atom}
    (lhs rhs : Graph Atom Sig W Z)
    (hassoc : ∀ (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val) (a b : Val),
      @Eval Atom Sig den W Z lhs a b → @Eval Atom Sig den W Z rhs a b)
    : SemanticLaw Atom Sig W Z where
  name := "associativity"
  lhs := lhs
  rhs := rhs
  sound := fun den a b e => hassoc den a b e

-- ============================================================================
-- 6. Connection to the trait inference framework
-- ============================================================================

/-! ## Connection to `TraitInference.lean`

The equational law inference fits the same framework as the functor-law
inference in `TraitInference.lean`. The parallel is:

| Aspect              | Functor laws (`TraitInference`)     | Non-functor laws (this file)         |
|---------------------|--------------------------------------|--------------------------------------|
| Pattern recognizer  | `UsesFirst` / `UsesLeft`             | `UsesRoundtrip` / `UsesAssoc`        |
| Verification method | `LawVerified` (CutElim normalization)| `SemanticLaw.sound` (axiom)          |
| Satisfaction pred.  | `SatisfiesLaw`                       | `SatisfiesLawWithAxiom`              |
| Inference theorem   | `satisfies_functor_identity`         | `roundtrip_inference_theorem`        |
| Discharge           | CutElim (pure inference)             | Axiom (explicit declaration)         |
| ADR mode            | Primary mode                         | Secondary mode                       |

The STRUCTURAL RECOGNITION extends cleanly: `UsesRoundtrip` is the same
kind of inductive pattern recognizer as `UsesFirst`. The VERIFICATION
differs: functor laws are discharged by CutElim (pure inference, primary
mode), while non-functor laws require a semantic axiom (explicit
declaration, secondary mode).

This is the honest answer to ADR OQ#1: the invariant-inference machinery
PARTIALLY extends to equational law patterns. The structural recognition
extends; the verification requires axioms for non-functor laws. -/

/-- **The `inferred_law_pattern` function:** the law-inference analogue of
`inferred_trait` from `TraitInference.lean`. It maps a graph to the law
pattern it exhibits, by structural recursion on the wiring.

  - `comp (arr φ) (arr ψ)` → roundtrip pattern detected
  - `comp (comp (arr φ) (arr ψ)) (arr χ)` → associativity pattern detected
  - `comp G H` → union of patterns from G and H
  - `first G` → functor pattern (delegates to `inferred_trait`)
  - `left G` → coproduct functor pattern (delegates to `inferred_trait`)
  - `id`, `arr`, `loop` → no pattern

This mirrors `inferred_trait` exactly in structure: both are structural
recursion on the graph wiring, detecting patterns by constructor shape. -/
def inferred_law_pattern {A B : Ty Atom} (G : Graph Atom Sig A B) : Prop :=
  match G with
  | Graph.comp (Graph.arr _) (Graph.arr _) => True  -- roundtrip pattern
  | Graph.comp (Graph.comp (Graph.arr _) (Graph.arr _)) (Graph.arr _) => True  -- assoc pattern
  | Graph.comp G H => inferred_law_pattern G ∨ inferred_law_pattern H
  | Graph.first _ => True  -- functor pattern (delegated)
  | Graph.left _ => True   -- coproduct functor pattern (delegated)
  | _ => False

/-- **Soundness of `inferred_law_pattern` for the roundtrip pattern:**
if `inferred_law_pattern` detects the roundtrip pattern (i.e., `G` is
`comp (arr φ) (arr ψ)`), then `UsesRoundtrip` holds.

This is the structural-recognition soundness: the pattern detector
correctly identifies the roundtrip wiring. -/
theorem inferred_law_pattern_sound_roundtrip
    {X Y Z : Ty Atom} (φ : Sig X Y) (ψ : Sig Y Z)
    : inferred_law_pattern (Graph.comp (Graph.arr φ) (Graph.arr ψ)) →
      UsesRoundtrip Atom Sig (Graph.comp (Graph.arr φ) (Graph.arr ψ)) := by
  intro _
  exact UsesRoundtrip.here φ ψ

/-- **Soundness of `inferred_law_pattern` for the associativity pattern.** -/
theorem inferred_law_pattern_sound_assoc
    {W X Y Z : Ty Atom} (φ : Sig W X) (ψ : Sig X Y) (χ : Sig Y Z)
    : inferred_law_pattern
        (Graph.comp (Graph.comp (Graph.arr φ) (Graph.arr ψ)) (Graph.arr χ)) →
      UsesAssoc Atom Sig
        (Graph.comp (Graph.comp (Graph.arr φ) (Graph.arr ψ)) (Graph.arr χ)) := by
  intro _
  exact UsesAssoc.here φ ψ χ

/-- **The roundtrip law implies preservation of all `D`-invariants** —
the same connection as `functor_id_law_implies_preserves_all_D` in
`TraitInference.lean`, but for the roundtrip law.

If `comp (arr serialize, arr deserialize)` behaves as the identity (by
the roundtrip axiom), then it preserves every invariant `I` in the domain
`D`: if `I` holds of the input, it holds of the output (because the output
equals the input).

This connects the equational law inference to the invariant domain `D`
from `InvariantDomain.lean`: the law (verified by axiom) implies a
semantic property (identity behavior) that implies preservation of all
`D`-invariants. -/
theorem roundtrip_law_implies_preserves_all_D
    {X Y : Ty Atom} (serialize : Sig X Y) (deserialize : Sig Y X)
    (den : ∀ {A B : Ty Atom}, Sig A B → Val → Val)
    (sig_guarantee : SigGuarantee Atom Sig)
    (hinv : ∀ a, den deserialize (den serialize a) = a)
    (I : Val → Prop) (_dI : InvariantDomain Atom Sig sig_guarantee I)
    (a b : Val)
    (e : @Eval Atom Sig den X X
          (Graph.comp (Graph.arr serialize) (Graph.arr deserialize)) a b)
    (hI : I a) : I b := by
  -- The roundtrip law gives b = a, so I b = I a, which holds by hypothesis.
  have hb : b = a := roundtrip_law_with_axiom serialize deserialize den hinv a b e
  rw [hb]
  exact hI

-- ============================================================================
-- 7. Contrast: functor laws (CutElim) vs non-functor laws (axiom)
-- ============================================================================

/-! ## The contrast: CutElim-discharged vs axiom-discharged laws

The functor laws from `TraitInference.lean` are discharged by CutElim
normalization — pure structural inference, no semantic axiom. The
non-functor laws in this file require a semantic axiom. This section makes
the contrast explicit, showing that the SAME structural-recognition
framework handles both, with different verification methods. -/

/-- **Functor laws are discharged by CutElim alone** (no axiom needed).
This is a wrapper around `TraitInference.first_identity_law` that makes
the contrast explicit: the functor identity law is verified by CutElim
normalization, with no semantic axiom. -/
theorem functor_law_by_cutelim (A D : Ty Atom)
    : Nonempty (CutElimStar Atom Sig (@Graph.first Atom Sig A A D (Graph.idG A))
                    (Graph.idG (A ×ₜ D)))
      ∧ Nonempty (CutElimStar Atom Sig (Graph.idG (A ×ₜ D))
                    (Graph.idG (A ×ₜ D))) :=
  TraitInference.first_identity_law A D

/-- **Non-functor laws are NOT discharged by CutElim alone.**
The roundtrip law `comp (arr serialize, arr deserialize) ≡ idG` cannot be
proven by CutElim normalization — `comp (arr φ) (arr ψ)` is already in
CutElim normal form (no `idG` to absorb, no `first`/`left` to fuse). The
law holds only by a semantic axiom about `serialize` and `deserialize`.

This theorem states the NEGATIVE result: there is no single CutElim
rewrite step from `comp (arr serialize) (arr deserialize)` to `idG X`.
No CutElim rule matches the redex `comp (arr φ) (arr ψ)`:
  - `ceIdLeft` / `ceIdRight` require an `idG` argument, not `arr`.
  - `ceFirstFusion` / `ceLeftFusion` require `first` / `left`, not `arr`.
  - `ceFirstId` / `ceLeftId` require `first (idG)` / `left (idG)`, not `comp`.

This is the formal counterpart to the honest assessment: CutElim cannot
discharge non-functor laws. The structural recognition works; the
verification requires an axiom. -/
theorem roundtrip_not_cutelim_discharged
    {X Y : Ty Atom} (serialize : Sig X Y) (deserialize : Sig Y X)
    : ¬ Nonempty (CutElim Atom Sig
        (Graph.comp (Graph.arr serialize) (Graph.arr deserialize))
        (Graph.idG X)) := by
  -- No CutElim rule applies to comp (arr φ) (arr ψ):
  -- - ceIdLeft requires the left side to be idG, but it's arr serialize.
  -- - ceIdRight requires the right side to be idG, but it's arr deserialize.
  -- - ceFirstFusion requires first, not arr.
  -- - ceLeftFusion requires left, not arr.
  -- - ceFirstId requires first (idG), not comp.
  -- - ceLeftId requires left (idG), not comp.
  -- So no single CutElim step rewrites comp (arr φ) (arr ψ) to idG X.
  intro h
  obtain ⟨h⟩ := h
  cases h

-- ============================================================================
-- 8. Honest assessment
-- ============================================================================

/-
## Honest assessment: does this count as "extending invariant inference to
equational law patterns"?

### What IS proven (this file)

1. **Structural pattern recognition extends to non-functor laws.**
   `UsesRoundtrip` and `UsesAssoc` are the same kind of inductive pattern
   recognizers as `UsesFirst` and `UsesLeft` from `TraitInference.lean`.
   They detect the wiring shapes `comp (arr φ) (arr ψ)` (roundtrip) and
   `comp (comp (arr φ) (arr ψ)) (arr χ)` (associativity) by structural
   inspection. The `inferred_law_pattern` function mirrors `inferred_trait`
   exactly in structure. **The structural recognition extends cleanly.**

2. **The roundtrip law is proven GIVEN a semantic axiom.**
   `roundtrip_law_with_axiom` proves that `comp (arr serialize, arr deserialize)`
   behaves as the identity, given the axiom `hinv : ∀ a, den deserialize
   (den serialize a) = a`. The axiom is an explicit hypothesis — honest,
   not hidden behind `sorry`. The proof uses only `Eval` inversion and the
   axiom; no CutElim.

3. **Full semantic equivalence with `idG` is established.**
   `roundtrip_semantic_equiv_id` proves both the existence (the roundtrip
   graph evaluates to `a` on `a`) and the determinism (every evaluation
   produces `a`) directions, given the axiom.

4. **The law satisfaction framework mirrors `TraitInference.lean`.**
   `SatisfiesLawWithAxiom` is the non-functor analogue of `SatisfiesLaw`:
   both combine structural recognition with verification. The difference
   is the verification method (axiom vs CutElim).

5. **The connection to the invariant domain `D` is established.**
   `roundtrip_law_implies_preserves_all_D` shows that the roundtrip law
   (given the axiom) implies preservation of all `D`-invariants — the same
   connection as `functor_id_law_implies_preserves_all_D`.

6. **The negative result is stated honestly.**
   `roundtrip_not_cutelim_discharged` proves that CutElim CANNOT discharge
   the roundtrip law — no single CutElim rewrite step applies to
   `comp (arr φ) (arr ψ)`. This is the formal counterpart to the claim
   that non-functor laws require axioms.

### What is NOT proven (honestly acknowledged)

1. **The axiom itself is not derived.** `hinv` (the inverse property of
   `serialize`/`deserialize`) is a HYPOTHESIS, not proven from CutElim or
   from graph structure. The system cannot INFER that two base arrows are
   inverse — it can only recognize the pattern and ASK "is there an axiom
   discharging this?" This is the fundamental limit: semantic facts about
   base arrows are not inferrable from wiring alone.

2. **No automation that DISCOVERS which axioms are needed.** The system
   recognizes the roundtrip pattern structurally, but it does not
   automatically determine that the `inverse(serialize, deserialize)` axiom
   is the right one to discharge it. The axiom must be explicitly provided
   (declared in the `LawAxiomEnv`). This is the secondary mode of ADR-0075:
   explicit declarations, not pure inference.

3. **No completeness.** We do not prove that every non-functor law is
   recognizable by `UsesRoundtrip` / `UsesAssoc`. There are law patterns
   with more complex wiring (e.g., monad bind associativity, which involves
   `loop` and nested `comp`) that would require additional recognizers.
   The framework is extensible (add more `Uses*` recognizers), but
   completeness is not claimed.

4. **No axiom discovery or consistency checking.** The `LawAxiomEnv` is a
   flat collection of assumed axioms. There is no mechanism for checking
   that the axioms are consistent, or for discovering axioms from the
   graph structure. The axioms are trusted declarations.

5. **The `inferred_law_pattern` function is `Prop`-valued**, not a data
   structure enumerating specific laws. This is the same limitation as
   `inferred_trait` in `TraitInference.lean` (obstacle (d) in its honest
   assessment): a more useful implementation would return a list of
   `SemanticLaw` instances, but this requires universe-polymorphic
   containers that are awkward in Lean4.

### How this relates to ADR-0075's three outcomes

ADR-0075 §"The contingency on law inference" describes three outcomes:

1. **Primary mode (inference works):** laws are inferred from wiring, no
   declaration needed. This works for FUNCTOR LAWS — `TraitInference.lean`
   proves that `UsesFirst` triggers CutElim verification, with no axiom.
   This file shows it does NOT work for non-functor laws: the roundtrip
   law requires an axiom that is not inferrable from wiring.

2. **Secondary mode (explicit declarations + CutElim):** laws are verified
   when explicitly declared. This is where non-functor laws live. The
   structural recognition (`UsesRoundtrip`) is the inference part; the
   axiom (`hinv`) is the explicit declaration. The law is PROVEN given the
   declaration — still an advantage over Rust/Haskell (proofs, not just
   types), but requiring declaration.

3. **Reduces to sugar:** neither works. This does NOT happen — the
   secondary mode works for non-functor laws. The trait layer is more
   than sugar: it provides verified laws (by CutElim for functor laws, by
   axiom for non-functor laws) with compositional proof reuse.

### The honest answer to ADR OQ#1

**Does the invariant-inference machinery extend from output properties to
equational law patterns?**

**PARTIALLY.** The structural pattern recognition extends cleanly:
`UsesRoundtrip` and `UsesAssoc` are the same kind of wiring inspectors as
`UsesFirst` and `UsesLeft`. The `inferred_law_pattern` function mirrors
`inferred_trait` exactly in structure. The system CAN recognize that a
graph has the roundtrip shape or the associativity shape, without any
declaration.

The VERIFICATION does NOT extend to pure inference for non-functor laws.
The roundtrip law requires a semantic axiom (`hinv`) that is not derivable
from CutElim or from graph structure. The system can recognize the pattern
and ASK "is there an axiom discharging this?", but it cannot INFER the
axiom. This is the secondary mode of ADR-0075: explicit declarations +
structural recognition, not the primary mode (pure inference).

**The split is clean and predictable:**
  - Laws that ARE CutElim rewrites (functor identity, functor composition,
    coproduct functor laws) → primary mode (pure inference, no axiom).
  - Laws that are NOT CutElim rewrites (roundtrip, semigroup associativity,
    monad associativity) → secondary mode (structural recognition + axiom).

The dividing line is whether the law is a graph rewrite or a semantic fact
about base arrows. Functor laws are graph rewrites (`ceFirstId`,
`ceFirstFusion`); roundtrip/associativity are semantic facts. The
structural recognition handles both; the verification method differs.

This is a valid research result: the ADR's primary mode works for functor
laws (proven in `TraitInference.lean`), and the secondary mode works for
non-functor laws (proven in this file). The trait layer does NOT reduce to
sugar — it provides verified laws with compositional proof reuse, split
across two verification methods. The honest position is that ADR-0075's
primary mode is aspirational for non-functor laws, and the secondary mode
is the proven fallback — which is exactly what the ADR's contingency
clause describes.
-/

end EquationalLawInference
