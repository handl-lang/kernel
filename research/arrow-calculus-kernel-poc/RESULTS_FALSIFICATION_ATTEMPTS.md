# Falsification Attempts: The Maximality Claim for Structural Information

## Status: ADVERSARIAL ANALYSIS COMPLETE

Date: 2026-08-31

This document reports the results of an aggressive, adversarial attempt to
falsify the maximality claim from `StructuralInfo.lean`:

> **The Claim.** The freer arrow with Apply is the maximal compositional
> representation: no representation with full monadic power can recover
> strictly more structural information compositionally.

**Verdict: The maximality claim as stated is FALSE.** Two of six attack
vectors succeed. The theorem as formalized is vacuously true (Attack 2),
and the claim fails for any open or extendable lattice of facts (Attack 1).
The strongest surviving claim is significantly weaker — and honestly
trivial — compared to what is claimed.

---

## Setup: What the Formalization Actually Says

Before attacking, let us state precisely what is formalized.

### The lattice of facts (StructuralInfo.lean, lines 128–134)

The `StructFact` lattice is a **closed inductive type** with exactly six
constructors:

```lean
inductive StructFact : Type where
  | fanout_independence : StructFact
  | branching : StructFact
  | per_branch_effects : StructFact
  | dependency_graph : StructFact
  | feedback : StructFact
  | effect_set : StructFact
```

A `FactSet` is a predicate `StructFact → Prop`. The top element is
`allFacts := fun _ => True` (every fact is recoverable). The bottom is
`noFacts := fun _ => False` (nothing is recoverable).

### The measure σ (lines 176–194)

- `sigmaFreerArrow c = allFacts` — the freer arrow recovers ALL six facts.
- `sigmaFreerMonad c` = `{branching, dependency_graph, feedback, effect_set}`
  — `fanout_independence` and `per_branch_effects` are `False`.
- `sigmaOpaqueMonad c = noFacts` — nothing is recoverable.
- `sigmaFreerArrowApply c = sigmaFreerArrow c = allFacts` — Apply doesn't
  change σ.

### The maximality theorem (lines 416–427)

```lean
theorem sigma_maximal_ArrowApply {Op V : Type}
    (R : MonadicRepresentation Op V)
    (hpower : R.hasMonadicPower)
    (c : FreerArrow Op V) (rc : R.Rep) :
    R.sigmaRep rc ⊆f sigmaFreerArrowApply c := by
  sorry
```

This states: for any monadic representation `R` and any computation `c`,
`σ_R(c) ⊆ σ(FreerArrow_with_Apply(c))`.

---

## Attack 1: Provenance/Metadata Counterexample

### The counterexample

Define a **tagged freer arrow** `FreerArrowTagged` that is identical to
`FreerArrow` except each `op` node carries a source label (provenance):

```
FreerArrowTagged Op V :=
  | pure (v : V)
  | seq (f g : FreerArrowTagged Op V)
  | fanout (f g : FreerArrowTagged Op V)
  | choice (f g : FreerArrowTagged Op V)
  | op (o : Op) (loc : SourceLoc) (k : FreerArrowTagged Op V)  -- ← carries provenance
  | loop (f : FreerArrowTagged Op V)
  | apply (f : FreerArrowTagged Op V)
```

This representation:

- **Has full monadic power**: includes `apply` (ArrowApply ≅ Monad).
- **Recovers all standard structural facts**: `fanout_independence`,
  `branching`, `per_branch_effects`, `dependency_graph`, `feedback`,
  `effect_set` — all are recoverable by tree traversal, exactly as in the
  standard freer arrow.
- **ADDITIONALLY recovers `op_provenance`**: the source location of each
  operation. A traversal of `FreerArrowTagged` can report, for each `op`
  node, its `SourceLoc`. The standard `FreerArrow` has no source labels and
  cannot recover this.

### Is this a valid counterexample?

**Yes, if the lattice of facts is open or extendable.** The tagged freer
arrow recovers strictly more structural information than the standard freer
arrow: it recovers everything the standard one does, plus provenance. It has
full monadic power. It is compositional (a fold over the tree recovers
provenance compositionally — each `op` node contributes its `SourceLoc`).

The only way to escape this counterexample is to **fix the lattice** to
exactly the six `StructFact` constructors and declare that provenance is
not a "structural fact." But this is a stipulation, not a theorem. There is
no principled reason why `op_provenance` is not a structural fact — it is a
property of the computation's structure recoverable by traversal.

### Does it falsify the claim?

**YES — for any open or extendable lattice.** The maximality claim says "no
representation with full monadic power can recover strictly more structural
information." The tagged freer arrow does recover strictly more. The claim
is false unless the lattice is artificially closed.

### What the claim should be reduced to

The claim is only true **relative to a specific, fixed, closed lattice of
facts**. It should be stated as:

> Within the fixed lattice L = {fanout_independence, branching,
> per_branch_effects, dependency_graph, feedback, effect_set}, the freer
> arrow with Apply recovers all facts in L.

This is a much weaker claim. It says "the freer arrow hits the top of this
particular lattice," not "the freer arrow is maximal in any absolute sense."

### Why the defense fails

The formalization's own commentary (lines 363–365) acknowledges this:

> Adding more constructors would add more `StructFact`s to the lattice —
> but those would be new facts, not facts about the same computation.

This defense is invalid. Provenance IS a fact about the same computation —
it is a structural property of where each operation appears in the source.
The tagged freer arrow represents the same computation (same semantics,
same effects, same structure) but additionally records provenance. The
defense conflates "facts about the computation" with "facts in our
arbitrarily chosen lattice."

---

## Attack 2: The Theorem Is Vacuously True

### The argument

The maximality theorem states:

```
R.sigmaRep rc ⊆f sigmaFreerArrowApply c
```

By definition (lines 304–305):

```lean
def sigmaFreerArrowApply (c : FreerArrow Op V) : FactSet :=
  sigmaFreerArrow c
```

And (lines 176–177):

```lean
def sigmaFreerArrow (_ : FreerArrow Op V) : FactSet :=
  allFacts
```

And (line 149):

```lean
def allFacts : FactSet := fun _ => True
```

Therefore:

```
sigmaFreerArrowApply c = allFacts = fun _ => True
```

The subset relation `R.sigmaRep rc ⊆f allFacts` unfolds to:

```
∀ f : StructFact, R.sigmaRep rc f → True
```

This is **trivially true for any `R.sigmaRep rc`**, because the consequent
is `True`. The theorem places **no constraint whatsoever** on `R.sigmaRep`.
It would hold if `R.sigmaRep` recovered all six facts, none of them, or
anything in between. It would hold if `R` were the opaque monad, the freer
monad, the tagged freer arrow, or a representation that recovers facts that
don't even exist in the `StructFact` lattice (which is impossible since
`StructFact` is a closed type, but the point stands: the theorem doesn't
care).

### Is this correct?

**YES.** The theorem is vacuously true. The proof is one line:

```lean
intro f _; trivial
```

No `sorry` is needed. The theorem proves nothing about maximality. It is a
tautology: "every fact set is a subset of the universal set."

### Does it falsify the claim?

**YES — it falsifies the formal theorem.** The theorem
`sigma_maximal_ArrowApply` does not encode maximality. It encodes
"everything is a subset of the top element," which is true by definition of
"top element." The theorem needs to be replaced with something that
actually constrains `R`.

The `sorry` in the formalization is misleading: it suggests the proof is
hard but the statement is correct. In reality, the statement is trivially
provable (no `sorry` needed), but it doesn't say what it claims to say.

### What the claim should be reduced to

The theorem should be replaced. The vacuous statement
`R.sigmaRep rc ⊆f allFacts` should not be called a "maximality theorem."
The actual content is in the ordering theorem and the strict inequalities,
which are non-trivial and proved.

---

## Attack 3: Same Facts but Compositionally Cheaper

### The counterexample

Consider a representation `FreerArrowCompact` that merges `seq` and `fanout`
into a single constructor `par_seq (n : Nat) (branches : List (FreerArrowCompact Op V))`
where `n = 1` means sequential composition and `n ≥ 2` means fanout. This
representation:

- Recovers the same six structural facts (fanout is detectable when `n ≥ 2`).
- Has full monadic power (includes `apply`).
- Has a simpler traversal (one constructor instead of two, potentially
  fewer tree nodes for computations that mix seq and fanout).

### Does it falsify the claim?

**No — but it weakens its significance.** The claim is about information
content (which facts are recoverable), not about efficiency. If two
representations recover the same facts, the claim holds (neither recovers
strictly more). But the claim's significance is reduced: "maximality" in
information content is the wrong metric if the practical question is about
analysis cost.

### Why the claim survives (but is less interesting)

The claim is about the _set_ of recoverable facts, not the _cost_ of
recovery. A representation that recovers the same facts more cheaply does
not falsify the claim. But it does suggest that the interesting question is
not "which representation is maximal in σ?" but "which representation
minimizes the cost of recovering a given set of facts?" — a question the
current formalization does not address.

### What this reveals

"Maximality" as stated is a claim about the _height_ in the fact lattice,
not about _efficiency_ or _expressiveness of the recovery process_. This
makes the claim technically defensible but practically less interesting
than it appears.

---

## Attack 4: Finer-Grained Facts

### The counterexample

The `StructFact` lattice has `fanout_independence` as a single fact. But
there are at least two distinct sub-types:

1. **Independent fanout**: `f &&& g` where `f` and `g` share no state
   (truly independent, e.g., pure computations).
2. **State-sharing fanout**: `f &&& g` where `f` and `g` share mutable
   state (independent in data flow, but not in effect ordering).

The freer arrow's `fanout` constructor does not distinguish these — it
just says "fanout." A representation with separate constructors
`fanout_independent` and `fanout_state_sharing` would recover strictly more
information: it could distinguish the two cases, while the freer arrow
cannot.

Similarly, `branching` could be refined into:

- **Exhaustive branching** (all branches reachable).
- **Non-exhaustive branching** (some branches are dead code).

The freer arrow's `choice` constructor does not distinguish these.

### Does it falsify the claim?

**YES — for any refined lattice.** If the lattice includes
`fanout_independent` and `fanout_state_sharing` as separate facts, the
freer arrow recovers both (it can detect fanout but not the sub-type), so
it recovers strictly less than a representation with separate constructors.

Wait — more precisely: the freer arrow's `fanout` constructor would recover
the _coarse_ fact "some kind of fanout is present" but not the _fine_ fact
"this is independent fanout" vs "this is state-sharing fanout." A
representation with separate constructors would recover both the coarse
fact and the fine fact.

### Why the claim survives only for the fixed coarse lattice

This is the same structural issue as Attack 1: the claim is only true for
the specific, fixed, coarse lattice. Refine the lattice and the freer arrow
is no longer maximal. The freer arrow's constructors are **coarse-grained**
— `fanout` is one constructor, not two. A representation with finer
constructors recovers strictly more structural information.

### What the claim should be reduced to

The freer arrow is maximal **only for the specific coarse lattice L**. For
any refinement of L, the freer arrow may not be maximal. The claim should
explicitly state the lattice it is relative to and acknowledge that
refining the lattice may break maximality.

---

## Attack 5: Dynamic Information / Execution Traces

### The counterexample

Define a **traced freer arrow** `FreerArrowTraced` that augments the freer
arrow with an execution trace: after running the computation, each node is
annotated with runtime information (which branch was taken, how many times
a loop iterated, what values flowed through each edge).

```
FreerArrowTraced Op V :=
  | pure (v : V)
  | seq (f g : FreerArrowTraced Op V) (trace : SeqTrace)
  | fanout (f g : FreerArrowTraced Op V) (trace : FanoutTrace)
  | choice (f g : FreerArrowTraced Op V) (trace : ChoiceTrace)  -- ← which branch was taken
  | op (o : Op) (k : FreerArrowTraced Op V) (trace : OpTrace)   -- ← runtime value
  | loop (f : FreerArrowTraced Op V) (trace : LoopTrace)        -- ← iteration count
  | apply (f : FreerArrowTraced Op V) (trace : ApplyTrace)
```

This representation:

- Has full monadic power (includes `apply`).
- Recovers all six standard structural facts (the tree structure is
  preserved).
- ADDITIONALLY recovers dynamic facts: `branch_taken` (which branch of a
  choice was actually executed), `loop_iterations` (how many times a loop
  ran), `runtime_values` (what values flowed through each edge).

The standard freer arrow is a **static tree** — it cannot recover any of
these dynamic facts.

### Does it falsify the claim?

**YES — if "structural information" includes dynamic/trace information.**
The claim says "no representation with full monadic power can recover
strictly more structural information." The traced freer arrow does recover
strictly more — it recovers dynamic structural information that the static
freer arrow cannot.

### Why the claim survives only for static facts

The defense is that "structural information" means **static** structural
information — properties recoverable by traversing the syntax tree without
running the computation. Dynamic information (traces) is not "structural"
in this sense.

This is a reasonable defense, but it must be stated explicitly. The current
formalization does not define "structural information" precisely enough to
exclude dynamic facts. The `StructFact` lattice happens to contain only
static facts, but this is a design choice, not a theorem.

### What the claim should be reduced to

The claim should explicitly restrict to **static** structural information:
facts recoverable by compositional traversal of the syntax tree without
execution. Dynamic information is out of scope. This restriction should be
stated as a hypothesis, not left implicit.

---

## Attack 6: The Freer Arrow Is Not Unique

### The counterexample

The empirical Challenge #9 results show that the **freer monad with
explicit `Fanout` and `Choice` constructors** (the `FreeM` representation
in the Rust tests) recovers ALL structural information:

> The freer monad — which IS a monad, but with explicit structure —
> recovers ALL structural information. (RESULTS_CHALLENGE9.md, lines 88–89)

This representation:

- Has full monadic power (it IS a monad, with `Bind`).
- Recovers all six structural facts (σ = allFacts).
- Is compositional (explicit tree, fully traversable).

Therefore, the freer monad with explicit `Fanout`/`Choice` is ALSO maximal
— it achieves σ = allFacts, same as the freer arrow with Apply.

### Does it falsify the claim?

**It falsifies uniqueness, but not maximality.** The claim says the freer
arrow with Apply is "the maximal compositional representation." If
"maximal" means "a maximal element" (i.e., no element is strictly above
it), then multiple representations can be maximal, and the claim survives.

If "the maximal" implies uniqueness, then the claim is false — the freer
monad with explicit constructors is also maximal.

### Why the claim survives (with a wording fix)

The results document already acknowledges this (line 372–375):

> It does not claim that the freer arrow is the _unique_ maximal
> representation — only that it is _a_ maximal representation.

So the claim is already hedged. But the theorem statement uses the
definite article ("the maximal compositional representation"), which is
misleading. The claim should say "a maximal compositional representation,"
not "the maximal."

### What this reveals

Maximality in a lattice is a property of an element (being at the top),
not a unique characterization. Multiple representations can be maximal.
The interesting question is not "is the freer arrow maximal?" (many things
are) but "what is the _minimal_ set of constructors needed to achieve
maximality?" — which is the Challenge #10 minimality result, a separate
and stronger theorem.

---

## Overall Verdict

### Does the maximality claim survive?

**NO — not as stated.** The claim is false in two ways:

1. **The formalized theorem is vacuous (Attack 2).** The theorem
   `sigma_maximal_ArrowApply` states `R.sigmaRep rc ⊆f allFacts`, which is
   trivially true for any `R`. It does not encode maximality. The `sorry`
   is unnecessary — the theorem is provable in one line — but it proves
   nothing.

2. **The claim fails for any open lattice (Attacks 1, 4, 5).** Provenance,
   finer-grained fanout types, and dynamic trace information are all
   structural facts that the freer arrow cannot recover but that other
   representations with full monadic power can. The claim is only true
   relative to a specific, fixed, closed, coarse lattice of six static
   facts — and even then, it is trivially true (the freer arrow hits the
   top of the lattice, so nothing can exceed it).

### What is the strongest true claim?

The strongest claim that survives all attacks is:

> **Theorem (Structural Boundary, Refined).** Let L be the fixed lattice
> of static structural facts L = {fanout_independence, branching,
> per_branch_effects, dependency_graph, feedback, effect_set}. Then:
>
> 1. σ(FreerArrow_with_Apply) = top(L) — the freer arrow with Apply
>    recovers all facts in L. **[Proved: `arrowapply_preserves_sigma`,
>    `sigmaFreerArrow_is_all`]**
>
> 2. σ(FreerArrow_with_Apply) = σ(FreerArrow) — adding monadic power
>    (Apply) does not reduce observability. **[Proved:
>    `arrowapply_preserves_sigma`]**
>
> 3. σ(FreerMonad) ⊊ σ(FreerArrow) — the standard freer monad (without
>    explicit Fanout/Choice constructors) loses `fanout_independence` and
>    `per_branch_effects`. **[Proved: `strict_fanout`,
>    `strict_per_branch_effects`]**
>
> 4. σ(OpaqueMonad) = ⊥ — the opaque monad recovers nothing. **[Proved:
>    `sigmaOpaqueMonad_subseteq_FreerMonad`]**
>
> **Corollary (Trivial Maximality for L):** Since
> σ(FreerArrow_with_Apply) = top(L), no representation can recover a fact
> in L that the freer arrow with Apply does not. This is a tautological
> consequence of hitting the top of a finite lattice, not a deep
> maximality result.
>
> **What is NOT claimed:**
>
> - The freer arrow with Apply is NOT maximal for any lattice beyond L.
>   Extending L with provenance, finer-grained fanout types, or dynamic
>   trace facts would break maximality (Attacks 1, 4, 5).
> - The freer arrow with Apply is NOT the unique maximal representation
>   for L. Any representation with explicit constructors for all
>   structural features in L (e.g., the freer monad with explicit
>   Fanout/Choice) is also maximal (Attack 6).
> - The maximality is NOT a model-theoretic theorem. It is a trivial
>   consequence of σ(FAA) = top(L) for a finite lattice L (Attack 2).

### What is genuinely non-trivial

The non-trivial results in the formalization are NOT the maximality
theorem. They are:

1. **The ordering theorem** (`sigma_ordering`): σ(FA) ⊇ σ(FM) ⊇ σ(OM).
   This is meaningful — it establishes a hierarchy of observability.

2. **The strict inequalities** (`strict_fanout`,
   `strict_per_branch_effects`): the freer monad LOSES specific facts.
   This is the formal version of the empirical "false dependency"
   phenomenon.

3. **The ArrowApply preservation** (`arrowapply_preserves_sigma`):
   adding monadic power does not reduce observability. This is the key
   insight: you can have full expressiveness AND full observability
   simultaneously.

These three results are the real contribution. The maximality theorem
adds nothing — it is either vacuous (as formalized) or false (for any
open lattice).

---

## The Refined Theorem

### What to remove

Remove or rename `sigma_maximal_ArrowApply`. As stated, it is vacuous. Do
not call it a "maximality theorem." The `sorry` should be replaced with
the trivial proof (`intro f _; trivial`), and the theorem should be
renamed to reflect what it actually says: "every fact set is a subset of
allFacts."

### What to add

Add an explicit statement of the **trivial maximality corollary**:

```lean
/-- Since σ(FreerArrow_with_Apply) = allFacts (the top of the StructFact
lattice), no representation can recover a fact in StructFact that the
freer arrow with Apply does not. This is a tautological consequence of
hitting the top of a finite lattice. -/
theorem trivial_maximality {Op V : Type}
    (R : MonadicRepresentation Op V)
    (c : FreerArrow Op V) (rc : R.Rep) :
    R.sigmaRep rc ⊆f sigmaFreerArrowApply c := by
  intro f _
  rw [sigmaFreerArrow_is_all]
  trivial
```

Note: no `sorry` needed. The proof is trivial. The theorem is trivial. The
name `trivial_maximality` is honest about this.

### What to state as the real boundary theorem

The real theorem is the combination of the ordering, strict inequalities,
and preservation — all of which are already proved:

```
For any computation C:
  (1) σ(FA(C)) = top(L)                    [sigmaFreerArrow_is_all]
  (2) σ(FAA(C)) = σ(FA(C)) = top(L)        [arrowapply_preserves_sigma]
  (3) σ(FM(C)) ⊊ σ(FA(C)) if C has fanout  [strict_fanout]
  (4) σ(FM(C)) ⊊ σ(FA(C)) if C has choice  [strict_per_branch_effects]
  (5) σ(OM(C)) = ⊥                          [by definition]
```

This is the structural boundary: the freer arrow with Apply sits at the
top of the lattice L, the freer monad sits strictly below it (for
computations with fanout/choice), and the opaque monad sits at the bottom.
Adding monadic power to the freer arrow does not move it down.

This is a genuine and interesting result. The maximality theorem is not.

---

## Summary Table

| Attack | Description                        | Falsifies?                            | Severity                                              |
| ------ | ---------------------------------- | ------------------------------------- | ----------------------------------------------------- |
| 1      | Provenance/metadata counterexample | **YES** (for open lattice)            | **Fatal** — claim is false for any extendable lattice |
| 2      | Theorem is vacuously true          | **YES** (formal theorem is vacuous)   | **Fatal** — the theorem proves nothing                |
| 3      | Same facts but cheaper             | No (but weakens significance)         | Minor — wrong metric                                  |
| 4      | Finer-grained facts                | **YES** (for refined lattice)         | **Serious** — claim is false for any refinement       |
| 5      | Dynamic information                | **YES** (if σ includes dynamic facts) | **Serious** — claim must restrict to static facts     |
| 6      | Non-uniqueness                     | No (but "the" → "a")                  | Minor — wording fix                                   |

### Attacks that succeed: 1, 2, 4, 5

The maximality claim is false as stated. The formalized theorem is
vacuous. The conceptual claim fails for any open, refined, or
dynamic-inclusive lattice.

### What survives

The **structural boundary** (ordering + strict inequalities + ArrowApply
preservation) survives all attacks and is the genuine contribution. It
establishes a meaningful hierarchy of observability and shows that monadic
power does not reduce structural observability. This is interesting and
non-trivial. The maximality theorem is not.

---

## Recommendation

1. **Remove the maximality theorem** or rename it to `trivial_maximality`
   with the trivial proof. Do not present it as a deep result.

2. **State the lattice explicitly** in all claims. The claim is relative to
   L = {fanout_independence, branching, per_branch_effects,
   dependency_graph, feedback, effect_set}. Do not imply it generalizes to
   other lattices.

3. **Add a "Limitations" section** to the results document acknowledging:
   - The claim is for a fixed, closed, coarse lattice only.
   - Provenance, finer-grained facts, and dynamic traces are out of scope.
   - The freer arrow is not the unique maximal representation.
   - The maximality is trivial (hitting the top of a finite lattice).

4. **Emphasize what is genuinely non-trivial**: the ordering, the strict
   inequalities, and the ArrowApply preservation. These are the real
   theorems. The "boundary" is the hierarchy σ(OM) ⊊ σ(FM) ⊊ σ(FA) =
   σ(FAA), not a vacuous maximality statement.

5. **Consider an alternative formulation** of maximality that is
   non-trivial. For example: "The freer arrow with Apply is the minimal
   representation (in terms of constructors) that achieves σ = top(L) while
   having full monadic power." This connects to the Challenge #10
   minimality result and is a genuinely interesting claim — but it is a
   different claim from the current maximality theorem, and it would need
   its own proof.
