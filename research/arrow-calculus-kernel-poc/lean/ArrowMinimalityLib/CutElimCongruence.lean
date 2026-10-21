/-
# Congruence Rules for CutElim, and Termination of the Six-Rewrite System

ADR-0075 §11 (Law verification: the CutElim connection) and Open
Question #2 (CutElim termination) identify two gaps in the mechanization:

1. **Congruence.** The `CutElim` rewrite relation in `ProofAdvantage.lean`
   fires ONLY AT THE ROOT. There are no congruence rules, so a rewrite
   that applies inside a subgraph (e.g. `ceIdLeft` inside
   `first (comp id g)`) cannot fire. The "Honest assessment" in
   `TraitInference.lean` (lines ~637-640) lists this explicitly:
   "The current CutElim only rewrites at the top level. To verify laws
   for complex graphs (e.g. map_list built from the five primitives), we
   need congruence rules (rewriting inside subgraphs). This is
   straightforward but tedious to formalize."

2. **Termination.** The ADR's Negative section (line ~819) notes:
   "CutElim normalization may not terminate. The rewrite relation is not
   known to be strongly normalizing for all graphs."

This file closes both gaps for the six-rewrite system:

- We define `CutElimCong`, a new rewrite relation that wraps the six
  original `CutElim` rewrites (via `ceBase`) and adds congruence rules
  for `comp`, `first`, `left`, and `loop`. `CutElimCong` subsumes
  `CutElim`: every `CutElim` step is a `CutElimCong` step (`ceBase`), and
  congruence lifts any step through the four graph formers. This mirrors
  the Rust prototype's `rewrite_pass` (`src/trait_catalog.rs`, ~line 641),
  which does bottom-up congruence (recurse into children first, then
  rewrite at the root).

- We prove `CutElimCong` preserves proofs and types (lifting
  `cut_elim_preserves_proof` from `ProofAdvantage.lean` through the
  congruence cases by inverting the `PrOf` derivation).

- We prove several concrete laws that the OLD root-only `CutElim` could
  NOT prove but `CutElimCong` can, e.g. `first (comp id g) ≡ first g`.

- We prove termination: every `CutElimCong` step strictly decreases a
  combinator-count size measure, so `CutElimCong` is STRONGLY NORMALIZING
  — any rewrite sequence from `G` has at most `graphSize G - 1` steps.
  This is a complete (not merely partial) termination result for the
  six-rewrite system. The ADR's non-termination concern applies to a
  RICHER system (e.g. one with loop-unrolling or expansion rewrites that
  are not size-decreasing); for the present six rewrites + congruence,
  strong normalization holds outright.

This file uses option (B) from the task: a NEW inductive `CutElimCong`
that wraps `CutElim` plus congruence, leaving `ProofAdvantage.lean`
untouched.
-/

import ArrowMinimalityLib.ProofGraphs
import ArrowMinimalityLib.ProofAdvantage

open ProofGraphs
open ProofAdvantage

namespace CutElimCongruence

variable {Atom : Type} {Sig : Ty Atom → Ty Atom → Type}

-- ============================================================================
-- 1. CutElimCong: CutElim + congruence rules
-- ============================================================================

/- `CutElimCong G G'` reads "the graph `G` rewrites to `G'` by one
cut-elimination step, EITHER at the root (via `ceBase`, wrapping any of
the six `CutElim` rewrites) OR inside a subgraph (via a congruence rule).
The congruence rules are recursive on `CutElimCong`, so a rewrite can be
lifted through arbitrarily many graph formers — exactly the bottom-up
congruence the Rust `rewrite_pass` performs. -/
inductive CutElimCong (Atom : Type) (Sig : Ty Atom → Ty Atom → Type) :
    {A B : Ty Atom} → Graph Atom Sig A B → Graph Atom Sig A B → Type 1
  | ceBase {A B : Ty Atom} {G G' : Graph Atom Sig A B}
      (h : CutElim Atom Sig G G') : CutElimCong Atom Sig G G'
  | ceCompLeft {A B C : Ty Atom} (G G' : Graph Atom Sig A B) (H : Graph Atom Sig B C)
      (h : CutElimCong Atom Sig G G') : CutElimCong Atom Sig (Graph.comp G H) (Graph.comp G' H)
  | ceCompRight {A B C : Ty Atom} (G : Graph Atom Sig A B) (H H' : Graph Atom Sig B C)
      (h : CutElimCong Atom Sig H H') : CutElimCong Atom Sig (Graph.comp G H) (Graph.comp G H')
  | ceFirstCong {A B D : Ty Atom} (G G' : Graph Atom Sig A B)
      (h : CutElimCong Atom Sig G G') : CutElimCong Atom Sig (Graph.first G) (Graph.first G')
  | ceLeftCong {A B D : Ty Atom} (G G' : Graph Atom Sig A B)
      (h : CutElimCong Atom Sig G G') : CutElimCong Atom Sig (Graph.left G) (Graph.left G')
  | ceLoopCong {A B C : Ty Atom} (G G' : Graph Atom Sig (A ×ₜ C) (B ×ₜ C))
      (h : CutElimCong Atom Sig G G') : CutElimCong Atom Sig (Graph.loop G) (Graph.loop G')

/-- Reflexive-transitive closure of `CutElimCong`: zero or more rewrite
steps. `CutElimCongStar G G'` reads "the graph `G` simplifies to `G'`"
under the congruence-extended relation. -/
inductive CutElimCongStar (Atom : Type) (Sig : Ty Atom → Ty Atom → Type) :
    {A B : Ty Atom} → Graph Atom Sig A B → Graph Atom Sig A B → Type 1
  | cecsRefl {A B : Ty Atom} (G : Graph Atom Sig A B) : CutElimCongStar Atom Sig G G
  | cecsStep {A B : Ty Atom} (G G' G'' : Graph Atom Sig A B)
      (h1 : CutElimCong Atom Sig G G') (h2 : CutElimCongStar Atom Sig G' G'')
      : CutElimCongStar Atom Sig G G''

/-- Every `CutElim` step is a `CutElimCong` step (via `ceBase`), so
`CutElimCong` subsumes `CutElim`. -/
def CutElim.toCutElimCong {A B : Ty Atom} {G G' : Graph Atom Sig A B}
    (h : CutElim Atom Sig G G') : CutElimCong Atom Sig G G' :=
  CutElimCong.ceBase h

-- ============================================================================
-- 2. CutElimCong preserves proofs and types
-- ============================================================================

/- **Theorem (CutElimCong preserves proofs).** If `G ⟹ G'` by one
`CutElimCong` step and `G` is a proof of `A ⊢ B`, then `G'` is too. The
base case reuses `cut_elim_preserves_proof` from `ProofAdvantage.lean`;
the congruence cases invert the `PrOf` derivation at the outer
constructor, apply the IH to the rewritten sub-proof, and recombine. No
substitution lemma is invoked — there is nothing to substitute. -/
noncomputable def cut_elim_cong_preserves_proof {A B : Ty Atom} {G G' : Graph Atom Sig A B}
    (h : CutElimCong Atom Sig G G') (d : PrOf G) : PrOf G' := by
  induction h
  case ceBase h => exact cut_elim_preserves_proof h d
  case ceCompLeft G G' H h ih =>
    cases d with
    | compP _ _ dG dH => exact PrOf.compP G' H (ih dG) dH
  case ceCompRight G H H' h ih =>
    cases d with
    | compP _ _ dG dH => exact PrOf.compP G H' dG (ih dH)
  case ceFirstCong G G' h ih =>
    cases d with
    | firstP D _ dG => exact PrOf.firstP D G' (ih dG)
  case ceLeftCong G G' h ih =>
    cases d with
    | leftP D _ dG => exact PrOf.leftP D G' (ih dG)
  case ceLoopCong G G' h ih =>
    cases d with
    | loopP _ _ dG => exact PrOf.loopP _ G' (ih dG)

/- **Theorem (CutElimCong preserves types).** Derived from the proof
case via the Curry–Howard correspondence, exactly as
`cut_elim_preserves_type` is derived from `cut_elim_preserves_proof` in
`ProofAdvantage.lean`. -/
noncomputable def cut_elim_cong_preserves_type {A B : Ty Atom} {G G' : Graph Atom Sig A B}
    (h : CutElimCong Atom Sig G G') (d : TyOf G) : TyOf G' :=
  (cut_elim_cong_preserves_proof h d.toPrOf).toTyOf

/- Preservation lifts from one step to any number of steps by induction
on the closure derivation. -/
noncomputable def cut_elim_cong_star_preserves_proof {A B : Ty Atom}
    {G G' : Graph Atom Sig A B} (h : CutElimCongStar Atom Sig G G')
    (d : PrOf G) : PrOf G' := by
  induction h
  case cecsRefl G => exact d
  case cecsStep G G' G'' h1 h2 ih => exact ih (cut_elim_cong_preserves_proof h1 d)

/-- Typing preservation under the closure, derived as in the one-step
case. -/
noncomputable def cut_elim_cong_star_preserves_type {A B : Ty Atom}
    {G G' : Graph Atom Sig A B} (h : CutElimCongStar Atom Sig G G')
    (d : TyOf G) : TyOf G' :=
  (cut_elim_cong_star_preserves_proof h d.toPrOf).toTyOf

-- ============================================================================
-- 3. Concrete laws that REQUIRE congruence
-- ============================================================================

/- The OLD root-only `CutElim` can prove `first (id) ≡ id` (`ceFirstId`
fires at the root) but CANNOT prove `first (comp id g) ≡ first g`:
`ceIdLeft` fires on `comp id g`, but only at the root, and
`first (comp id g)` has `first` at the root. The new congruence rule
`ceFirstCong` lifts `ceIdLeft` through `first`, discharging the law in
one step. -/

/-- `first (comp id g) ≡ first g` — requires congruence: `ceIdLeft`
inside `first`. The root-only `CutElim` cannot fire here. -/
theorem first_comp_id_law (A B D : Ty Atom) (G : Graph Atom Sig A B)
    : Nonempty (CutElimCongStar Atom Sig
        (@Graph.first Atom Sig A B D (Graph.comp (Graph.idG A) G))
        (@Graph.first Atom Sig A B D G)) :=
  ⟨CutElimCongStar.cecsStep _ _ _
    (CutElimCong.ceFirstCong (D := D)
        (Graph.comp (Graph.idG A) G) G
        (CutElimCong.ceBase (CutElim.ceIdLeft G)))
    (CutElimCongStar.cecsRefl _)⟩

/-- `left (comp id g) ≡ left g` — the `left` analogue of the above,
requiring `ceLeftCong` to lift `ceIdLeft` through `left`. -/
theorem left_comp_id_law (A B D : Ty Atom) (G : Graph Atom Sig A B)
    : Nonempty (CutElimCongStar Atom Sig
        (@Graph.left Atom Sig A B D (Graph.comp (Graph.idG A) G))
        (@Graph.left Atom Sig A B D G)) :=
  ⟨CutElimCongStar.cecsStep _ _ _
    (CutElimCong.ceLeftCong (D := D)
        (Graph.comp (Graph.idG A) G) G
        (CutElimCong.ceBase (CutElim.ceIdLeft G)))
    (CutElimCongStar.cecsRefl _)⟩

/-- `comp (first id) g ≡ g` — a TWO-STEP rewrite using congruence.
Step 1: `ceCompLeft` lifts `ceFirstId` through `comp`, rewriting
`comp (first id) g` to `comp (id (A × D)) g`. Step 2: `ceIdLeft` fires
at the (new) root, rewriting `comp (id (A × D)) g` to `g`. The root-only
`CutElim` cannot do step 1. -/
theorem comp_first_id_law (A C D : Ty Atom) (G : Graph Atom Sig (A ×ₜ D) C)
    : Nonempty (CutElimCongStar Atom Sig
        (Graph.comp (@Graph.first Atom Sig A A D (Graph.idG A)) G)
        G) :=
  ⟨CutElimCongStar.cecsStep _ _ _
    (CutElimCong.ceCompLeft (@Graph.first Atom Sig A A D (Graph.idG A))
        (Graph.idG (A ×ₜ D)) G
      (CutElimCong.ceBase CutElim.ceFirstId))
    (CutElimCongStar.cecsStep _ _ _
      (CutElimCong.ceBase (CutElim.ceIdLeft G))
      (CutElimCongStar.cecsRefl _))⟩

/-- `first (comp g id) ≡ first g` — the right-identity analogue,
requiring `ceFirstCong` to lift `ceIdRight` through `first`. -/
theorem first_comp_id_right_law (A B D : Ty Atom) (G : Graph Atom Sig A B)
    : Nonempty (CutElimCongStar Atom Sig
        (@Graph.first Atom Sig A B D (Graph.comp G (Graph.idG B)))
        (@Graph.first Atom Sig A B D G)) :=
  ⟨CutElimCongStar.cecsStep _ _ _
    (CutElimCong.ceFirstCong (D := D)
        (Graph.comp G (Graph.idG B)) G
        (CutElimCong.ceBase (CutElim.ceIdRight G)))
    (CutElimCongStar.cecsRefl _)⟩

-- ============================================================================
-- 4. Termination: a size measure and strong normalization
-- ============================================================================

/- **Size measure.** `graphSize G` counts every graph constructor
(`idG`, `comp`, `first`, `left`, `loop`, `arr`) as one node, summing
recursively over subgraphs. It is always ≥ 1. -/

def graphSize {A B : Ty Atom} (G : Graph Atom Sig A B) : Nat :=
  match G with
  | Graph.idG _   => 1
  | Graph.comp G H => 1 + graphSize G + graphSize H
  | Graph.first G  => 1 + graphSize G
  | Graph.left G   => 1 + graphSize G
  | Graph.loop G   => 1 + graphSize G
  | Graph.arr _    => 1

theorem graphSize_pos {A B : Ty Atom} (G : Graph Atom Sig A B) : 1 ≤ graphSize G := by
  cases G <;> simp only [graphSize] <;> omega

/- **Each base `CutElim` rewrite strictly decreases size.** The six
rewrites all remove combinator nodes:
  - `ceIdLeft` / `ceIdRight` remove a `comp` and an `idG` (−2);
  - `ceFirstFusion` / `ceLeftFusion` merge two `first`s / `left`s and a
    `comp` into one `first` / `left` and a `comp` (−1);
  - `ceFirstId` / `ceLeftId` collapse `first (id)` / `left (id)` to `id`
    (−1). -/
theorem cut_elim_base_size_decrease {A B : Ty Atom} {G G' : Graph Atom Sig A B}
    (h : CutElim Atom Sig G G') : graphSize G' < graphSize G := by
  cases h with
  | ceIdLeft G        => simp only [graphSize]; omega
  | ceIdRight G       => simp only [graphSize]; omega
  | ceFirstFusion D G H => simp only [graphSize]; omega
  | ceLeftFusion D G H  => simp only [graphSize]; omega
  | ceFirstId         => simp only [graphSize]; omega
  | ceLeftId          => simp only [graphSize]; omega

/- **Every `CutElimCong` step strictly decreases size.** A congruence
rule keeps the outer constructor (so its node is unchanged) and only
rewrites a subgraph; by the IH the subgraph strictly shrinks, so the
whole graph strictly shrinks. Combined with the base case above, this
shows NO `CutElimCong` step is size-preserving or size-increasing —
every single step removes at least one node. -/
theorem cut_elim_cong_size_decrease {A B : Ty Atom} {G G' : Graph Atom Sig A B}
    (h : CutElimCong Atom Sig G G') : graphSize G' < graphSize G := by
  induction h with
  | ceBase h => exact cut_elim_base_size_decrease h
  | ceCompLeft G G' H h ih   => simp only [graphSize]; omega
  | ceCompRight G H H' h ih  => simp only [graphSize]; omega
  | ceFirstCong G G' h ih    => simp only [graphSize]; omega
  | ceLeftCong G G' h ih     => simp only [graphSize]; omega
  | ceLoopCong G G' h ih     => simp only [graphSize]; omega

/- **Step count.** The number of `CutElimCong` steps in a
`CutElimCongStar` derivation. -/
noncomputable def cutElimCongStarSteps {A B : Ty Atom} {G G' : Graph Atom Sig A B}
    (h : CutElimCongStar Atom Sig G G') : Nat :=
  match h with
  | CutElimCongStar.cecsRefl _        => 0
  | CutElimCongStar.cecsStep _ _ _ _ h2 => 1 + cutElimCongStarSteps h2

/- **Termination / strong normalization.** For any `CutElimCongStar`
derivation from `G` to `G'`, the number of rewrite steps plus the final
size is at most the initial size. Since the final size is ≥ 1, the
number of steps is at most `graphSize G - 1`. Hence there are NO
infinite `CutElimCong` rewrite sequences: `CutElimCong` is strongly
normalizing.

This is a COMPLETE termination result for the six-rewrite system (with
congruence), not merely a fuel-bounded partial result. The proof is by
induction on the closure derivation, using
`cut_elim_cong_size_decrease` at each step. -/
theorem cutElimCongStar_steps_bound {A B : Ty Atom} {G G' : Graph Atom Sig A B}
    (h : CutElimCongStar Atom Sig G G') :
    cutElimCongStarSteps h + graphSize G' ≤ graphSize G := by
  induction h with
  | cecsRefl G => simp only [cutElimCongStarSteps]; omega
  | cecsStep G G' G'' h1 h2 ih =>
    simp only [cutElimCongStarSteps]
    have hsize := cut_elim_cong_size_decrease h1
    omega

/-- **Step bound.** Any `CutElimCongStar` derivation from `G` has at
most `graphSize G - 1` rewrite steps. This is the quantitative form of
strong normalization: normalization terminates in at most
`graphSize G - 1` steps, regardless of strategy. -/
theorem cutElimCongStar_steps_le_size {A B : Ty Atom} {G G' : Graph Atom Sig A B}
    (h : CutElimCongStar Atom Sig G G') : cutElimCongStarSteps h ≤ graphSize G - 1 := by
  have hb := cutElimCongStar_steps_bound h
  have hp := graphSize_pos G'
  omega

/-
## 5. Honest assessment

### What congruence rules are added and what laws they enable

We add five congruence rules to the rewrite relation (as a new
`CutElimCong` inductive that wraps `CutElim`):

  - `ceCompLeft`  : `G ⟹ G'` ⇒ `comp G H ⟹ comp G' H`
  - `ceCompRight` : `H ⟹ H'` ⇒ `comp G H ⟹ comp G H'`
  - `ceFirstCong` : `G ⟹ G'` ⇒ `first G ⟹ first G'`
  - `ceLeftCong`  : `G ⟹ G'` ⇒ `left G ⟹ left G'`
  - `ceLoopCong`  : `G ⟹ G'` ⇒ `loop G ⟹ loop G'`

These lift any rewrite (base or congruence) through the four graph
formers, exactly mirroring the Rust prototype's bottom-up `rewrite_pass`
(`src/trait_catalog.rs` ~line 641), which recurses into children first
and then rewrites at the root. Concrete laws now provable that the
root-only `CutElim` could NOT prove:

  - `first (comp id g) ≡ first g`        (`first_comp_id_law`)
  - `left  (comp id g) ≡ left g`         (`left_comp_id_law`)
  - `comp (first id) g ≡ g`              (`comp_first_id_law`, two-step)
  - `first (comp g id) ≡ first g`        (`first_comp_id_right_law`)

### What termination fragment is proven

We prove a COMPLETE termination result for the six-rewrite system (with
congruence), not a partial / fuel-bounded one:

  - `cut_elim_base_size_decrease`: each of the six base `CutElim`
    rewrites strictly decreases `graphSize` (the combinator-node count).
  - `cut_elim_cong_size_decrease`: every `CutElimCong` step (base OR
    congruence) strictly decreases `graphSize` — congruence preserves
    the size delta of the inner rewrite.
  - `cutElimCongStar_steps_bound` / `cutElimCongStar_steps_le_size`:
    any `CutElimCongStar` derivation from `G` has at most
    `graphSize G - 1` steps. Hence `CutElimCong` is STRONGLY NORMALIZING
    (no infinite rewrite sequences), for ALL graphs — including those
    containing `loop`.

This is honest: strong normalization holds here because all six base
rewrites are size-DECREASING and congruence is size-PRESERVING (it
rewrites inside, keeping the outer node). No rewrite in the system
increases size, so size is a well-founded termination measure.

### What remains open (ADR §11 / Open Question #2)

  - **Full termination for a RICHER rewrite system.** The ADR's Negative
    section warns that "CutElim normalization may not terminate" and
    that the relation "is not known to be strongly normalizing for all
    graphs." That concern is about a MORE EXPRESSIVE system than the six
    rewrites mechanized here — e.g. one with loop-unrolling rewrites
    (`loop (comp G H) ⟹ …`), expansion rewrites, associativity/
    commutativity, or `arr`-interchange laws. Such rewrites can be
    size-INCREASING or size-PRESERVING and may admit cycles; the size
    measure here would NOT bound them. Our result certifies the present
    six-rewrite fragment, not an arbitrary future extension.
  - **Strong vs weak normalization under strategy.** We prove strong
    normalization (every sequence terminates), which implies weak
    normalization (a normalizing strategy exists). We do NOT prove
    confluence / unique normal forms, which would be needed to turn
    "both sides normalize" into a decision procedure for law equality.
  - **Termination WITH loops (operational).** This file's termination is
    about the REWRITE relation (syntactic graph simplification), not
    about the operational `Eval` semantics of `loop` (which is handled
    separately in `Termination.lean` via decreasing measures). The
    rewrite `ceLoopCong` only rewrites INSIDE a loop body; there is no
    rewrite that unrolls or duplicates a loop, which is why size still
    decreases.
  - **Connection to the trait checker.** Per ADR §11, the law checker
    must be connected to trait-law verification (catalog search step 3,
    "CutElim verify"). This file supplies the rewrite machinery and its
    metatheory (preservation + termination); wiring it into the trait
    catalog's law-checking path is the remaining integration work.

### Comparison to the Rust prototype

The Rust `rewrite_pass` (`src/trait_catalog.rs`) performs bottom-up
congruence with a FUEL bound as a safety net, because it does not prove
termination. This Lean mechanization lifts that to a FORMAL result: the
bottom-up congruence is captured by the `CutElimCong` congruence rules,
and termination is PROVEN (strong normalization via the size measure),
so no fuel bound is needed for the six-rewrite fragment — the bound
`graphSize G - 1` is derived, not assumed. The Rust fuel bound remains
appropriate as a defensive measure for any future size-increasing
rewrites added to the prototype.
-/

end CutElimCongruence
