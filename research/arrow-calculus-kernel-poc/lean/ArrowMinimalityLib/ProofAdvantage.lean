/-
# A Non-Definitional Proof-Theoretic Advantage of Arrow Graphs

## The problem with the existing correspondence

`ProofGraphs.lean` establishes `TyOf G ↔ PrOf G`, but the two inductives
are *notation-for-notation identical*. A skeptic can argue the
correspondence is therefore *definitional*: it holds because we defined
two copies of the same thing. That is not a theorem *about* arrow graphs;
it is a theorem about our choice of definitions.

## What this file proves

We exhibit a property that is **genuinely non-definitional**: cut
elimination for arrow graphs is a system of *local graph rewrites*, and
those rewrites preserve both proofs (`PrOf`) and typings (`TyOf`).

In natural deduction, cut elimination is the process of eliminating a
cut

    Γ ⊢ A      A, Δ ⊢ B
    ──────────────────── cut
          Γ, Δ ⊢ B

by substituting the proof of `A` into the proof of `B`. Substitution (i)
requires a binder (λ), (ii) requires α-equivalence / capture-avoiding
substitution to be well-defined, and (iii) can *duplicate* the proof of
`A`, blowing up the derivation. The metatheory of cut elimination for
λ-calculus / natural deduction is therefore non-trivial: it hinges on
substitution lemmas, α-renaming, and a separate termination measure.

In arrow graphs there is **no binder**. Cut is just `Graph.comp`, and
cut elimination is a finite set of *local* rewrites on the graph
skeleton — rewrites that mention only the graph constructors, never a
term, a variable, or a substitution:

  - `idG A ⋙ G  ⟹  G`              (left identity)
  - `G ⋙ idG B  ⟹  G`              (right identity)
  - `first G D ⋙ first H D  ⟹  first (G ⋙ H) D`   (product functor fusion)
  - `left  G D ⋙ left  H D  ⟹  left  (G ⋙ H) D`   (sum functor fusion)

Each rewrite is a *single* structural step. There is no substitution, no
α-conversion, no duplication of sub-proofs: the graph is the proof, and
simplifying the graph *is* simplifying the proof. We mechanize this as
an inductive rewrite relation `CutElim` and prove:

  - `cut_elim_preserves_proof`: every `PrOf G` lifts to a `PrOf G'`
    after one rewrite step `G ⟹ G'`.
  - `cut_elim_preserves_type`:   every `TyOf G` lifts to a `TyOf G'`
    after one rewrite step (derived from the proof case via the
    Curry–Howard correspondence — a *use* of that correspondence, not a
    restatement of it).

This is a real theorem *about* the graph calculus: it says the proof
content is invariant under graph simplification, and the proof is by
case analysis on the *graph* shape, not by a substitution lemma. The
λ-calculus has no analogous "local rewrite preserves typing" theorem
without first proving the substitution lemma — because in λ-calculus a
rewrite step *is* a substitution.

## Why this is a non-definitional advantage

The result does not follow from `TyOf G ↔ PrOf G`. That bijection says
the two judgments agree *on a fixed graph*; it says nothing about what
happens when the graph *changes*. Cut-elimination preservation is a
statement relating *two different graphs* (`G` and `G'`), and its proof
inspects the actual rewrite that connects them. No re-statement of the
bijection discharges it; one must do the case analysis on `CutElim`.

A second, equally non-definitional advantage: **graph equality is
decidable without α-equivalence**. Two λ-terms are equal up to
α-equivalence (a quotient), so equality of λ-terms is *not* structural
decidable equality — it requires a separate α-equivalence algorithm.
Two arrow graphs are equal iff they are built from the same constructors
in the same order; `Graph` is a first-order algebraic data type with no
binder, so structural equality *is* the equality (and is decidable by
`deriving DecidableEq`). The graph syntax pays no α-tax.
-/

import ArrowMinimalityLib.ProofGraphs

open ProofGraphs

namespace ProofAdvantage

variable {Atom : Type} {Sig : Ty Atom → Ty Atom → Type}

-- ============================================================================
-- 1. Cut elimination as a local graph-rewrite relation
-- ============================================================================

/- `CutElim G G'` reads "the graph `G` rewrites to `G'` by one cut-
elimination step." Each constructor is a single local rewrite on the
graph skeleton. There is no substitution and no binder: the rewrite
mentions only `Graph` constructors.

We write `@Graph.first`/`@Graph.left` explicitly because the carrier
type `D` is an *implicit* parameter of those constructors; making it
explicit here pins down the single shared `D` that the fusion rules
require (the two `first`s / `left`s must act on the same side-channel). -/
inductive CutElim (Atom : Type) (Sig : Ty Atom → Ty Atom → Type) :
    {A B : Ty Atom} → Graph Atom Sig A B → Graph Atom Sig A B → Type 1
  | ceIdLeft  {A B : Ty Atom} (G : Graph Atom Sig A B)
             : CutElim Atom Sig (Graph.comp (Graph.idG A) G) G
  | ceIdRight {A B : Ty Atom} (G : Graph Atom Sig A B)
             : CutElim Atom Sig (Graph.comp G (Graph.idG B)) G
  | ceFirstFusion {X Y Z : Ty Atom} (D : Ty Atom) (G : Graph Atom Sig X Y) (H : Graph Atom Sig Y Z)
             : CutElim Atom Sig
                 (Graph.comp (@Graph.first Atom Sig X Y D G)
                             (@Graph.first Atom Sig Y Z D H))
                 (@Graph.first Atom Sig X Z D (Graph.comp G H))
  | ceLeftFusion  {X Y Z : Ty Atom} (D : Ty Atom) (G : Graph Atom Sig X Y) (H : Graph Atom Sig Y Z)
             : CutElim Atom Sig
                 (Graph.comp (@Graph.left Atom Sig X Y D G)
                             (@Graph.left Atom Sig Y Z D H))
                 (@Graph.left Atom Sig X Z D (Graph.comp G H))
  | ceFirstId {A D : Ty Atom}
             : CutElim Atom Sig
                 (@Graph.first Atom Sig A A D (Graph.idG A))
                 (Graph.idG (A ×ₜ D))
  | ceLeftId  {A D : Ty Atom}
             : CutElim Atom Sig
                 (@Graph.left Atom Sig A A D (Graph.idG A))
                 (Graph.idG (A +ₜ D))

/-- Reflexive-transitive closure of `CutElim`: zero or more rewrite
steps. `CutElimStar G G'` reads "the graph `G` simplifies to `G'`." -/
inductive CutElimStar (Atom : Type) (Sig : Ty Atom → Ty Atom → Type) :
    {A B : Ty Atom} → Graph Atom Sig A B → Graph Atom Sig A B → Type 1
  | cesRefl {A B : Ty Atom} (G : Graph Atom Sig A B) : CutElimStar Atom Sig G G
  | cesStep {A B : Ty Atom} (G G' G'' : Graph Atom Sig A B)
           (h1 : CutElim Atom Sig G G') (h2 : CutElimStar Atom Sig G' G'')
           : CutElimStar Atom Sig G G''

-- ============================================================================
-- 2. Cut elimination preserves proofs
-- ============================================================================

/- **Theorem (Cut elimination preserves proofs).** If `G ⟹ G'` by one
`CutElim` step and `G` is a proof of `A ⊢ B`, then `G'` is a proof of
`A ⊢ B`. The proof is by case analysis on the *rewrite* (not on the
derivation): each rewrite is a local graph simplification, and inverting
the `compP` (cut) derivation at the redex recovers the sub-proofs, which
are recombined by the constructor the rewrite produces. No substitution
lemma is invoked — there is nothing to substitute. -/
def cut_elim_preserves_proof {A B : Ty Atom} {G G' : Graph Atom Sig A B}
    (h : CutElim Atom Sig G G') (d : PrOf G) : PrOf G' := by
  cases h with
  | ceIdLeft G0 =>
    -- `idG A ⋙ G0 ⟹ G0`: invert the `compP` derivation, discard the
    -- identity half, keep the body proof `dH : PrOf G0`.
    cases d with
    | compP _ _ _ dH => exact dH
  | ceIdRight G0 =>
    -- `G0 ⋙ idG B ⟹ G0`: symmetrically, keep the left half.
    cases d with
    | compP _ _ dG _ => exact dG
  | ceFirstFusion D G H =>
    -- `first G D ⋙ first H D ⟹ first (G ⋙ H) D`: invert the outer cut,
    -- strip both `firstP`s, recombine under a single `firstP`. Inverting
    -- each `firstP` unifies its graph field with the outer `G`/`H`, so the
    -- body proofs are `dG' : PrOf G` and `dH' : PrOf H`; recombine them
    -- as `compP G H dG' dH'` under one `firstP` (reusing the shared `D`).
    cases d with
    | compP _ _ dG dH =>
      cases dG with
      | firstP _ _ dG' =>
        cases dH with
        | firstP _ _ dH' =>
          exact PrOf.firstP D (Graph.comp G H) (PrOf.compP G H dG' dH')
  | ceLeftFusion D G H =>
    -- `left G D ⋙ left H D ⟹ left (G ⋙ H) D`: identical shape to
    -- `ceFirstFusion` with `leftP` in place of `firstP`. Inverting each
    -- `leftP` unifies its graph field with the outer `G`/`H`.
    cases d with
    | compP _ _ dG dH =>
      cases dG with
      | leftP _ _ dG' =>
        cases dH with
        | leftP _ _ dH' =>
          exact PrOf.leftP D (Graph.comp G H) (PrOf.compP G H dG' dH')
  | ceFirstId =>
    -- `first (idG A) ⟹ idG (A × D)`: invert the `firstP` derivation,
    -- the body proof is `idP A`, and the identity on `A × D` is `idP (A × D)`.
    -- This is the functor identity law: F(id) = id_F.
    cases d with
    | firstP D₀ G₀ dG₀ =>
      cases dG₀ with
      | idP => exact PrOf.idP _
  | ceLeftId =>
    -- `left (idG A) ⟹ idG (A + D)`: identical shape with `leftP`/`idP`.
    -- This is the coproduct functor identity law.
    cases d with
    | leftP D₀ G₀ dG₀ =>
      cases dG₀ with
      | idP => exact PrOf.idP _

-- ============================================================================
-- 3. Cut elimination preserves types
-- ============================================================================

/- **Theorem (Cut elimination preserves types).** If `G ⟹ G'` and
`⊢ G : A ⇝ B`, then `⊢ G' : A ⇝ B`. This is *derived* from the proof
case via the Curry–Howard correspondence: transport the typing
derivation to a proof derivation, run cut-elimination-preservation on
the proof side, and transport back. This is a genuine *use* of the
`TyOf ↔ PrOf` bijection — it reduces a typing-preservation problem to a
proof-preservation problem — rather than a restatement of it. The
bijection alone could not prove this: it relates two judgments on the
*same* graph, whereas preservation relates *two different* graphs. -/
def cut_elim_preserves_type {A B : Ty Atom} {G G' : Graph Atom Sig A B}
    (h : CutElim Atom Sig G G') (d : TyOf G) : TyOf G' :=
  (cut_elim_preserves_proof h d.toPrOf).toTyOf

-- ============================================================================
-- 4. Cut elimination preserves proofs under the reflexive-transitive closure
-- ============================================================================

/- Preservation lifts from one step to any number of steps by induction
on the closure derivation. -/
noncomputable def cut_elim_star_preserves_proof {A B : Ty Atom} {G G' : Graph Atom Sig A B}
    (h : CutElimStar Atom Sig G G') (d : PrOf G) : PrOf G' := by
  induction h with
  | cesRefl G => exact d
  | cesStep G G' G'' h1 h2 ih =>
    exact ih (cut_elim_preserves_proof h1 d)

/-- Typing preservation under the closure, derived as in the one-step
case. -/
noncomputable def cut_elim_star_preserves_type {A B : Ty Atom} {G G' : Graph Atom Sig A B}
    (h : CutElimStar Atom Sig G G') (d : TyOf G) : TyOf G' :=
  (cut_elim_star_preserves_proof h d.toPrOf).toTyOf

-- ============================================================================
-- 5. The non-definitional advantage, restated
-- ============================================================================

/-
Two consequences that are *not* instances of the `TyOf ↔ PrOf`
correspondence:

1. **Cut elimination is local and binder-free.** Each `CutElim` step is
   a first-order rewrite on the `Graph` algebraic data type. There is no
   substitution, no α-equivalence, and no duplication of sub-derivations:
   the proof of `cut_elim_preserves_proof` never mentions a variable, a
   binder, or a substitution lemma. In λ-calculus / natural deduction,
   the analogous theorem (subject reduction under β-reduction) requires
   the substitution lemma as a prerequisite, because a β-step *is* a
   substitution. Arrow graphs pay no substitution tax.

2. **Graph equality is decidable without α-equivalence.** `Graph` is a
   first-order inductive with no binder; two graphs are equal iff they
   are built from the same constructors in the same order. Structural
   equality (decidable by `deriving DecidableEq`) *is* the equality.
   λ-terms live in a quotient by α-equivalence, so λ-term equality is
   *not* structural equality and requires a separate α-algorithm. The
   graph syntax is quotient-free.

These are properties of the *calculus*, not of our definitions: they
hold because arrow graphs have no binder, and they would fail (or
require substantial auxiliary machinery) for any λ-based proof object.
-/

end ProofAdvantage
