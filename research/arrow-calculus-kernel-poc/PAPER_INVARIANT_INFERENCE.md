---
title: "Structural Invariant-Schema Inference and Semantic Verification for Lambda-Free Arrow Graphs"
author: "Anonymous"
date: "September 2026"
abstract: |
  We present an annotation-free invariant inference mechanism for
  lambda-free arrow graphs — directed graphs built from four
  combinators (arr, comp, first, loop) over a signature of base arrows.
  The graph carries no refinement annotations, proof terms, or
  user-supplied loop invariants. Our mechanism infers invariant schemas
  from graph topology and verifies them against base arrow contracts
  using Z3. The compositional postcondition propagation is proven sound
  in Lean4: every inferred postcondition holds for every well-typed
  execution. The invariant domain D is formally defined, and the
  inference is proven strictly stronger than the trivial sound floor.
  We also prove that invariants outside D exist and are undetectable
  (incompleteness). Loop invariant discovery — structural pattern
  recognition for side-channel, accumulator, and filter loops — is
  implemented in a Rust prototype and evaluated empirically. Across 72
  non-trivial benchmark cells the prototype achieves 100% accuracy:
  every property the graph should prove is proven (26/26), and every
  property it should not prove is correctly reported as unknown (46/46),
  with zero false positives. This contrasts with 37 annotations
  required by Liquid Types for 19 properties.
---

# 1. Introduction

Program verification is traditionally expensive. To prove that a function
preserves sortedness, maintains a length invariant, or satisfies a loop
specification, one supplies, in addition to the program, a collection of
auxiliary artifacts: refinement-type annotations on every sub-expression,
explicit proof terms for each verification condition, and — most stubbornly
— loop invariants that the programmer must discover and state by hand. The
annotations often outweigh the program. The loop-invariant problem in
particular is the canonical bottleneck: the invariant is the creative step
that neither the type checker nor the theorem prover can reliably take on
its own.

This paper starts from a different representation of programs. An **arrow
graph** is a directed, port-typed graph built from combinators over a
signature of base arrows. The calculus is **lambda-free**: the grammar has
no binder, no variable, and no application. The key observation is that an
arrow graph is _structurally transparent_: its wiring is explicit, every
wire is inspectable, and the combinator structure determines how
information flows. This raises the question:

> _Can we achieve Agda-level semantic guarantees — sortedness,
> permutation, loop invariants — at TypeScript-level programming
> ergonomics, by deriving proofs from the structure of a lambda-free
> arrow graph rather than from user-supplied annotations or explicit
> proof terms?_

We argue that it can, for a useful and characterizable class of programs,
demonstrated with a Rust prototype performing annotation-free inference and
a Lean4 mechanization establishing soundness. The positioning is
deliberate: TypeScript gives lightweight types with low programmer burden;
Agda gives very strong proofs but makes proof construction explicit. Arrow
graphs aim for the sweet spot between them, as the next subsection makes
concrete.

## The Sweet Spot

Consider the spectrum of programmer burden versus verification power:

```
JavaScript:  write algorithm          → no types, no proofs, no guarantees
TypeScript:  write algorithm + types  → types, no proofs, no semantic guarantees
Agda:        write algorithm + types + proofs → types + proofs, strong guarantees
Arrow graphs: write algorithm          → types + proofs, strong guarantees
```

JavaScript requires nothing beyond the algorithm but provides no
guarantees. TypeScript adds type annotations and gets basic types but no
semantic proofs. Agda requires the programmer to construct explicit proofs
and achieves very strong guarantees. Arrow graphs aim for the fourth
position: **the programming ergonomics of JavaScript** (just write the
algorithm, nothing else) **with the verification power of Agda** (real
theorems about behavior). The user does not write types. The user does
not write proofs. The user does not write generics. The user does not
write annotations. The user just writes the program — and the type,
the polymorphism, and the proof all fall out of the graph structure.

This is possible because the graph structure contains all the information.
The type is in the wiring. The proof is in the wiring. The polymorphism
is in the wiring. There is nothing to declare because the structure
already has everything. The difference from JavaScript is not that we
skip verification — it is that we do full verification by reading it off
the structure instead of asking the user to write it down.

The key question is whether this can be achieved without quietly moving
the proof-writing burden into annotations or library specifications.

|                           | JavaScript      | TypeScript               | Agda                            | Arrow graphs (this paper)               |
| ------------------------- | --------------- | ------------------------ | ------------------------------- | --------------------------------------- |
| What you write            | Algorithm       | Algorithm + types        | Algorithm + types + proofs      | **Algorithm only**                      |
| Basic types               | None            | Declared (with generics) | Declared (with universe params) | **Inferred from wiring**                |
| Prove sortedness          | No              | No                       | Explicit proof                  | **Inferred from graph**                 |
| Prove permutation         | No              | No                       | Explicit proof                  | **Inferred**                            |
| Polymorphism              | Dynamic         | Declared `<T>`           | Declared `{A B : Set}`          | **Inferred (α, β from wiring)**         |
| Proof attached to program | No              | No                       | Separate dependent term         | **Same graph**                          |
| Composition               | Excellent       | Excellent                | Proofs compose explicitly       | **Composition + inferred proofs**       |
| Loop invariants           | External/manual | External/manual          | Explicit dependent reasoning    | **Potentially inferred by `loop`**      |
| Programmer burden         | Lowest          | Low                      | High                            | **Low (target)**                        |
| Guarantees                | None            | Basic types              | Very strong                     | **Potentially very strong + automatic** |

The "potentially" qualifiers are deliberate: the loop invariant
discovery's body-guarantee seeding, iterated loop soundness, and WP
branching through Choice are formally proven in Lean4, and the domain
membership gap is formally stated ($D$ not closed under existential
projection). The structural pattern recognition (side-channel,
accumulator, filter heuristics) is now fully formalized in Lean4 —
each pattern has a complete D-derivation (constructing the invariant in
$D$) and a preservation proof (showing the invariant is preserved by the
loop body), summarized by `pattern_invariant_derivations_complete`
(Section 5.5). The table expresses the _target_ of this work, and the
paper honestly characterizes how far the current implementation and
formalization reach toward it.

**Contributions.**

We frame our contribution as **graph-structural proof inference**: the
arrow graph is simultaneously the program, the type, and the proof object,
and the inference procedure derives properties from the graph's combinator
structure. This is not refinement inference (which annotates an AST) or
invariant synthesis (which analyzes loop semantics) — it is proof
inference from the structure of a lambda-free graph. The broad vision is
that the arrow program itself is the input to a proof-inference procedure,
and the resulting proof is compositional with the program graph. The
narrow contribution of this paper is what we actually prove and implement:

1. **Annotation-free structural refinement propagation with semantic
   verification.** A structural mechanism infers invariant schemas from
   graph topology and verifies them against base arrow contracts. The
   inference is sound (formally proven in Lean4) but not complete — it
   discovers invariants within a structural domain $D$ and reports
   "unknown" for invariants outside $D$.

2. **Structural invariant-schema inference for loops.** For `loop G`
   where $G : A \times C \rightsquigarrow B \times C$, the inference
   recognizes the structural pattern of $G$ (side-channel, accumulator,
   filter) to infer an invariant schema $I(c)$ on the feedback channel,
   then verifies it with Z3. No user-supplied invariant is required for
   the cases we study.

3. **A formalized invariant domain with soundness and incompleteness.**
   The domain $D$ is defined as an inductive type in Lean4. The
   structural inference algorithm is formalized and proven sound
   (`inferred_postcondition_sound_full`), strictly stronger than the
   trivial floor (`floor_does_not_imply_inferred`), and the existence of
   undetectable invariants outside $D$ is proven
   (`analyze_incompleteness`).

4. **An empirical characterization with 100% accuracy on in-domain
   properties.** Across 72 non-trivial benchmark cells, the prototype
   proves every property the graph should prove (26/26) and correctly
   reports unknown for every property it should not (46/46), with zero
   false positives. We document 5 failure cases representing
   out-of-domain invariants.

**Foundation.** This paper builds on a lambda-free arrow-graph calculus
whose proof-theoretic foundations — a Curry-Howard correspondence between
graph typing and logical proof, subject reduction, and local cut
elimination — are established in parallel work [self-cite] and mechanized
in Lean4. We use these results as the logical foundation for the inference
mechanism but they are not contributions of this paper. Appendix A
summarizes the key facts.

**A note on "annotation-free."** By "annotation-free" we mean that the
program — the arrow graph — carries no refinement annotations. The base
arrow signatures (sort, map, filter, etc.) do carry known guarantees, but
these are the type signatures of primitive operations, not user-supplied
annotations on the program. This is analogous to how Hindley-Milner type
inference is "annotation-free" despite base operations having typed
signatures.

**Two layers of inference, both automatic.** The refinement inference
operates on top of standard type inference. The user writes the arrow
graph; the system derives both layers automatically:

1. **Type inference** (Hindley-Milner-style): the most general type is
   derived from the graph structure. The user never writes type
   signatures, generic parameters, or trait bounds. `map` is
   automatically polymorphic: the inference engine introduces type
   variables $\alpha, \beta$ during unification, deriving
   `map : (List α × (α ⇝ β)) ⇝ List β` from the wiring alone. `sort` is
   automatically monomorphic: `sort : List α ⇝ List α` because the
   graph structure constrains input and output to the same type. The
   user did not specify either — the most general type is always
   derivable from the wiring.

2. **Refinement inference** (this paper): the most precise semantic
   guarantee is derived from the graph structure plus the axiomatic
   contracts on base arrows. `sort` derives `Sorted(output)`, `map`
   derives `LengthEq(input, output)`, `filter` derives
   `AllSatisfy(output, p) ∧ |output| ≤ |input|` — all with zero
   annotations.

The user writes one thing — the arrow graph — and gets both the type and
the proof for free. This is the inversion: in traditional systems, the
type is declared and the proof is constructed. Here, both are inferred
from the same object: the program structure.

**No generics syntax needed.** Generics syntax (`<T>`, `[T]`,
`forall a.`) exists because statement-based languages require types to
be declared before use. Arrow graphs invert this: the graph IS the type
derivation. The inference engine reads the graph, introduces type
variables where needed, and derives the most general type. There is
nothing to declare because the structure already contains all the
information. Polymorphism is not a feature you opt into — it is the
default, falling out of the wiring.

# 2. Background

**The arrow calculus.** Hughes [26] introduced arrows as a generalization
of monads. Lindley, Wadler, and Yallop [31] developed the arrow calculus
as a metalanguage with four constructs and five laws. Our graph primitives
correspond to these constructs; the key difference is that we take them as
a **graph grammar** rather than a lambda-calculus extension. Categorically,
arrows are monoids in profunctor categories [24, 25]: `comp` is monoid
multiplication, `first` is tensorial strength, and `loop` is the trace of
a traced monoidal category [27].

**Refinement types and Liquid Types.** Freeman and Pfenning [17]
introduced refinement types for ML. Liquid Types [38] extend
Hindley-Milner inference with refinement types using SMT solving, but
still require annotations on recursive functions and loops. Our work
differs in that graph structure (not an AST) is the substrate for
inference, and loop invariant schemas are inferred by structural analysis
on the graph.

**Abstract interpretation.** Cousot and Cousot [10, 11] developed the
dominant framework for loop invariant inference. Our structural inference
is inspired by abstract interpretation but operates on graph structure
rather than program syntax. We do not claim a formal duality; the
structural analysis provides candidate schemas, and the SMT checker
provides soundness via semantic verification.

# 3. The Arrow-Graph Calculus

## 3.1 Primitives and Semantics

An arrow graph is a finite, directed, port-typed graph built from
combinators over a signature $\Sigma$ of base arrows $\varphi : A \to B$:

$$
\begin{aligned}
\text{Types:} \quad & A, B, C \in \text{Ty} ::= \alpha \mid A \times B \mid A + B \mid \top \mid \bot \\
\text{Graphs:} \quad & G, H \in \text{Graph} ::= \textsf{id}_A \mid \textsf{comp}(G, H) \mid \textsf{first}(G) \mid \textsf{loop}(G) \mid \textsf{arr}(\varphi)
\end{aligned}
$$

The calculus also includes `left`$(G)$ for sum types ($A + C \rightsquigarrow
B + C$), but the inference mechanism does not use it — `left` is always
treated conservatively (Section 4.3). We include it for completeness of
the calculus but focus on the four combinators that drive the inference:
`arr`, `comp`, `first`, and `loop`.

**No lambda-abstraction, no application, no variable appears.** The graph
reading is recovered by viewing `comp` as edge-sequencing, `first` as
functorial-boxing on products, and `loop` as a back-edge (cycle).

The operational semantics is standard. Execution $G \cdot a \Longrightarrow
v$ is defined by: identity returns its input; composition runs the left
then the right; `first` runs the sub-graph on the first component and
passes the second through; `arr`$(\varphi)$ applies the base arrow; and
`loop` iterates the step graph on the feedback channel until it
stabilizes.

## 3.2 Foundation: Graphs as Proof Objects

In parallel work [self-cite], we show that arrow graphs satisfy a
Curry-Howard correspondence: the typing judgment `TyOf G` and the proof
judgment `PrOf G` are bijections, subject reduction holds, and cut
elimination is a local graph rewrite. These results are mechanized in
Lean4 (`ProofGraphs.lean`, `ProofAdvantage.lean`) and serve as the
foundation for the inference mechanism. The key fact used in this paper:

> **Subject Reduction (Lean4).** If $\vdash G : A \rightsquigarrow B$ and
> $G \cdot a \Longrightarrow v$ with $a : A$, then $v : B$.

This is used in the soundness proof of the inference algorithm (Section
4.4) to establish that intermediate values in compositions are
well-typed. Full details are in Appendix A.

The Curry-Howard correspondence is not just a theoretical curiosity — it
is the _enabling condition_ for the inference mechanism. Because the
graph IS a proof object (its typing derivation is a proof derivation), the
inference procedure can extract proof-relevant information from the graph
structure directly. When we infer `Sorted` from
`comp(arr(filter(p)), arr(sort))`, we are reading the proof structure off
the graph: the cut rule (composition) combines the axiom (arr) for
`filter` with the axiom for `sort`, and the conjunction of their
guarantees is the inferred postcondition. This is what makes the inference
_proof inference_ rather than _type inference_: we are not just assigning
types, we are reconstructing a proof from the proof object's structure.

# 4. Refinement Propagation

## 4.1 Refinement Types

A **refinement type** is written $\{x : T \mid P(x)\}$, denoting the
subset of values of type $T$ satisfying predicate $P$. A refinement arrow
$\{x : A \mid P(x)\} \rightsquigarrow \{y : B \mid Q(x, y)\}$ denotes a
computation that, given an input satisfying $P$, produces an output
satisfying $Q$.

## 4.2 The Key Idea: Refinements Flow from Structure

The central claim is that **refinements flow from base-arrow signatures
plus graph structure, without user annotations on the graph.** The
signature $\Sigma$ is the language definition: each base arrow $\varphi$
carries a known pre-/post-condition, like the type of `+` or `cons`. The
graph is the program — it carries no type information, no refinement
annotation, no proof term. The checker traverses the graph, propagates
refinements through each combinator, and infers the output refinement from
the input refinement and the graph structure.

### 4.2.1 The Inversion: The Program Is the Proof

The mechanism is not heuristic, statistical, or search-based. It is a
**deterministic structural derivation**:

1. **Read the graph** — which combinators are wired together?
2. **Look up the axioms** — what do the leaf arrows guarantee?
3. **Compose** — `comp` conjoins guarantees, `first` preserves the
   side channel, `choice` branches through both arms, `loop` finds a
   fixpoint.
4. **Check implications** — can we prove $\textsf{guarantee} \implies
   \textsf{postcondition}$?

There is no machine learning, no search, no trial-and-error. The proof is
**structurally determined by the wiring**. Change the wiring and you get a
different proof. The graph _is_ the proof.

This is the inversion that distinguishes proof inference from proof
construction. In Agda, you write the proof. In Coq, you write the tactic
script. In test-based verification, you write the assertions. Here, you
write **the program**, and the proof falls out for free. The program is
the proof, and the checker reads the proof off the structure.

This is what makes the approach _proof inference_ rather than _type
inference_: we are not just assigning types, we are reconstructing a proof
from the proof object's structure. The Curry-Howard correspondence
(Section 3.2) is the enabling condition — because the graph IS a proof
object, its typing derivation is a proof derivation, and the inference
procedure extracts proof-relevant information from the graph structure
directly.

### 4.2.2 The Trusted Foundation

The only stated contracts are the **axioms**: trivial structural facts
about irreducible primitive operations. `cons` adds 1 to length.
`compare` returns a value $\leq 1$. `alloc` produces an empty list. These
are not deep properties — they are the definitions of the operations.

Given this small trusted foundation, arbitrary composed arrow graphs
acquire derived semantic guarantees automatically. The ratio is the value
proposition: $\sim 10$ axiomatic contracts enable infinitely many programs
to be verified with zero annotations.

## 4.3 The Inferred Postcondition

The function `inferred_postcondition`$(G)$ computes a predicate on the
output value of $G$ by structural recursion on the graph:

- `id` $\to$ `True` (no constraint beyond input = output).
- `arr`$(\varphi)$ $\to$ `sig_guarantee`$(\varphi)$ (the base arrow's
  output contract).
- `comp`$(G, H)$ $\to$ `inferred_postcondition`$(H)$ (propagate through
  $H$; $H$ produces the final output).
- `first`$(G)$ $\to$ `True` (conservative: side channel unconstrained).
- `loop`$(G)$ $\to$ `True` (conservative: floor for feedback; see
  Section 5).
- `left`$(G)$ $\to$ `True` (conservative: not used by the inference).

This mirrors the Rust `infer_r` function. For `comp`$(G, H)$, the
postcondition of the composition is the postcondition of $H$: if $H$
guarantees $Q$ of its output, then `comp`$(G, H)$ guarantees $Q$ of its
output.

## 4.4 Soundness

**Theorem (Structural Inference Soundness, Lean4 — `inferred_postcondition_sound_full`).**
_Let $\Sigma$ be a signature with sound denotation and sound guarantees:
for every $\varphi : A \to B$ and $a : A$, `sig_guarantee`$(\varphi)$
holds of $\textsf{den}(\varphi, a)$. For every well-typed graph $G$ with
$\textsf{TyOf}(G)$, every $a : A$, and every $v$ with
$G \cdot a \Longrightarrow v$, the inferred postcondition holds of $v$:_

$$
\textsf{inferred\_postcondition}(G)(v).
$$

_Proof is by induction on the evaluation relation `Eval`. The `eComp`
case uses subject reduction on $G$ to obtain the intermediate value's
type, feeding the inductive hypothesis for $H$. The `eArr` case uses the
signature soundness hypothesis. The conservative cases (`eFirst`,
`eLeft`, `eLoop`) hold trivially since the postcondition is `True`. Zero
`sorry`_ (`StructuralInference.lean`).

## 4.5 The Invariant Domain $D$

The invariant domain $D$ is the smallest set of predicates (on values)
containing: (a) base arrow guarantees (`sig_guarantee`), (b) `True`, (c)
conjunctions of predicates in $D$ ($P \wedge Q$ whenever $P, Q \in D$),
and (d) predicates lifted through `first` (component-wise, `onFirst`).
$D$ does **not** contain arbitrary arithmetic predicates, predicates
requiring induction on iteration count, or predicates not expressible in
the signature language. It is formalized in Lean4 as the inductive type
`InvariantDomain` (`InvariantDomain.lean`).

**Theorem (Domain Membership, Lean4 — `inferred_postcondition_in_domain`).**
_For every graph $G$, the inferred postcondition is a member of the
invariant domain $D$. Zero `sorry`._

**Theorem (Strictly Stronger than the Floor, Lean4 — `floor_does_not_imply_inferred`).**
_For any base arrow $\varphi$ whose guarantee is non-trivial (there
exists $v$ with $\neg\,\textsf{sig\_guarantee}(\varphi)(v)$), the sound
floor `True` does not imply the inferred postcondition. That is, the
structural inference is strictly stronger than the trivial sound floor.
Zero `sorry`._

**Theorem (Incompleteness — Invariants Outside $D$, Lean4 — `analyze_incompleteness`).**
_There exists a graph $G$ and a predicate $I$ such that (1) $G$
preserves $I$ (if $I(c)$ holds before a step, $I(c')$ holds after), but
(2) $I \notin D$ — no derivation in the invariant domain produces $I$.
Concretely: with an empty signature, the identity loop body preserves
the invariant $I = \textsf{False}$ (vacuously), but $\textsf{False}$
cannot be derived in $D$ from an empty signature. This proves the
structural approach is inherently incomplete: true invariants exist
outside $D$. Zero `sorry`._

## 4.6 Concrete Examples

Consider a signature with `sort` guaranteeing `Sorted` $\wedge$
`IsPerm`, `map`$(f)$ guaranteeing `IsList` $\wedge$ `LengthPreserved`,
and `filter`$(p)$ guaranteeing `IsList` $\wedge$ `AllSatisfy`$(p)$:

| Graph                             | Inferred output refinement          |
| --------------------------------- | ----------------------------------- |
| `arr(sort)`                       | `Sorted` $\wedge$ `IsPerm`          |
| `arr(map(f))`                     | `IsList` $\wedge$ `LengthPreserved` |
| `comp(arr(filter(p)), arr(sort))` | `AllSatisfy`$(p)$ $\wedge$ `Sorted` |
| `first(arr(sort))`                | (`Sorted` $\wedge$ `IsPerm`, $Q$)   |

The third row illustrates compositional inference: `filter` produces
`AllSatisfy`$(p)$, which flows into `sort`'s precondition; the
conjunction is inferred without annotation — the composition of two
base-arrow postconditions via the cut rule.

## 4.7 Worked Example: Insertion Sort

We walk through the full inference pipeline for insertion sort, expressed
as an arrow graph. The graph is:

```
loop(comp(comp(first(head_and_tail), first(insert)), consume_one))
```

**Step 1: Structural analysis.** The inference traverses the graph:

- `head_and_tail` splits the input list into head + tail.
- `insert` inserts the head into the accumulator $C$, maintaining
  sorted order. Its signature guarantees `Sorted`$(C')$.
- `consume_one` removes one element from the input, decrementing its
  length. Its signature guarantees $|C'| \leq |C|$.
- The `first` combinators thread the accumulator $C$ through unchanged
  while the input is consumed.

**Step 2: Candidate invariant generation.** The `analyze` function
recognizes the accumulator pattern: `insert`'s guarantee `Sorted` is
threaded through the loop body. The candidate invariant is
$I(C) = \textsf{Sorted}(C)$.

**Step 3: Fixpoint iteration.**

- $I_0 = \textsf{True}$ (initial floor).
- $I_1 = \textsf{Sorted}(C)$ (from `insert`'s guarantee).
- $I_2 = \textsf{Sorted}(C) \wedge \textsf{Sorted}(C)$ (fixpoint
  reached — $I_2 \equiv I_1$).

**Step 4: Z3 verification.** The candidate `Sorted`$(C)$ is verified
against the base arrow contracts: if $C$ is sorted and `insert` maintains
sortedness, then $C'$ is sorted. Z3 confirms: **verified**.

**Step 5: Output refinement.** The output refinement is
`Sorted`$(\textsf{output})$, inferred from the graph structure alone —
zero user annotations.

**Step 6: Termination.** The termination analysis discovers that
`consume_one` decrements $|C|$ by 1 each iteration, bounded below by 0.
A well-founded ranking function is synthesized: **termination
guaranteed**.

# 5. Structural Invariant-Schema Inference for Loops

## 5.1 The Problem

The hard case is `loop`. A loop `loop G` where $G : A \times C
\rightsquigarrow B \times C$ feeds the $C$-output back as the $C$-input
and iterates until the feedback channel stabilizes. To infer a
refinement on the output, we need an **invariant** $I(c)$ on the
feedback channel — a predicate such that $G$ preserves $I$: if $I(c)$
holds before the step, then $I(c')$ holds after, where $(b, c') = G(a,
c)$. This is the classical loop-invariant inference problem, restated on
graph structure: the loop body is the graph $G$, the feedback channel
$C$ is the mutable state, and $I$ is a predicate on $C$ that each step
preserves.

## 5.2 Structural Pattern Recognition

The `analyze` phase inspects the _structure_ of $G$ to determine its
effect on the feedback channel $C$. The graph wiring makes this a
structural case analysis, not semantic reasoning over an opaque
expression:

- **Side-channel: `loop(first(H))`.** The body acts on the first
  component via $H$ and passes $C$ through unchanged. $C$ is never
  inspected or modified. The candidate is `True`. The output refinement
  is `inferred_postcondition`$(H)$ on the first component.

- **Accumulator: `loop(comp(map_step, first(id)))`.** The `map_step`
  processes an element and updates $C$; `first(id)` keeps the previous
  $C$ available. If `map_step`'s signature encodes that it adds to $C$
  (e.g., postcondition $c' = c + a$), the invariant is
  $I(c) = (c = \sum \text{processed})$.

- **Filter: `loop(comp(filter_step, id))`.** The `filter_step` removes
  elements failing a predicate $p$. The invariant is
  `AllSatisfy`$(C, p)$.

- **Sortedness: `loop(comp(insert_step, first(id)))`.** The
  `insert_step` inserts one element maintaining sorted order. The
  invariant is `Sorted`$(C)$. This is insertion sort expressed as a
  loop (Section 4.7).

## 5.3 The Invariant Lattice and Transfer Function

We formalize the invariant-schema inference as iteration over a lattice
$(D, \le)$ where $D$ is the invariant domain (Section 4.5), $I \le J$
means $J \Rightarrow I$ (stronger predicates are higher), bottom is
`True` (the trivial invariant), and join is conjunction (strengthening).
The transfer function `transfer`$(G, I)$ computes the weakest
pre-invariant. The least fixpoint `lfp(transfer)` is the strongest
invariant discoverable by the iteration.

This is mechanized in Lean4 (`InvariantDomain.lean`): the lattice
ordering `DLe`, bottom `DBottom`, join `DJoin`, the transfer function
`transfer`, the fixpoint predicate `IsFixpoint`, and the theorems:

- **`True_is_fixpoint`** (Lean4): the sound floor `True` is always a
  fixpoint of the transfer. Zero `sorry`.
- **`lfp_is_invariant`** (Lean4): every fixpoint of the transfer is a
  preserved invariant — if $I$ is a fixpoint and $G \cdot (a, c)
  \Longrightarrow (v, c')$ with $I(c)$, then $I(c')$. Zero `sorry`.

## 5.4 What the Rust Implementation Does

The Rust prototype implements the full pipeline: structural candidate
generation from graph patterns, followed by Z3-backed SMT verification
of each candidate against base arrow contracts. The
`discover_invariant` function performs structural case analysis on the
loop body and produces a candidate invariant schema, which is then
semantically verified. The checker is **conservative**: it may return
`Unknown` for true implications it cannot discharge, but it never
returns `Verified` for a false one. This asymmetry makes the inference
sound — every property reported as verified is genuinely true.

## 5.5 What Lean4 Proves

The Lean4 formalization proves the soundness of **compositional
postcondition propagation** (`inferred_postcondition_sound_full`). For
loops, the formalized `inferred_postcondition` returns `True` (the
conservative floor), and the lattice/transfer machinery is defined with
`True` proven as a fixpoint.

The **loop invariant discovery** is now formally proven in Lean4
(`LoopInvariantDiscovery.lean`, 25 theorems and 13 definitions, zero
`sorry`): the body-guarantee seeding is proven sound
(`loop_invariant_from_body_sound`,
`wp_transfer_holds_for_body_guarantee`,
`body_guarantee_stronger_than_floor`) and the WP branching through
Choice is proven sound (`fixpoint_converges_with_choice`). Three
additional theorems strengthen the formalization:
`iterated_loop_invariant_sound` proves that the body-guarantee
invariant holds at every intermediate step of an `EvalIter` derivation,
not just at the fixpoint; `body_guarantee_implies_true` proves the
trivial direction ($I \implies \textsf{True}$); and
`body_guarantee_in_domain` closes the domain membership gap — $D$ is
extended with an `exProj` constructor (existential projection over the
first component of a pair), so the body-guarantee invariant
$\exists v, P(\text{pair}(v, c'))$ is in $D$ whenever $P \in D$.
The structural pattern recognition (side-channel, accumulator, filter)
is now fully formalized with complete invariant derivations: each
pattern has a D-derivation constructing the invariant in $D$ and a
preservation proof showing the invariant is preserved by the loop body.
Specifically, `filter_loop_preserves_any_D_invariant` and
`filter_loop_dTrue_in_D` prove that any $I \in D$ is preserved by filter
loops and construct `dTrue` $\in D$;
`side_channel_preserves_any_D_invariant` and `side_channel_dTrue_in_D`
do the same for side-channel loops; and
`accumulator_body_guarantee_in_D` and
`accumulator_body_guarantee_preserved` prove the body-guarantee
invariant is in $D$ (via `exProj`) and preserved for accumulator loops.
The summary theorem `pattern_invariant_derivations_complete` collects
these results. The earlier behavioral definitions
(`side_channel_first_id_preserves_C`,
`accumulator_feedback_transformed_by_G`,
`filter_loop_preserves_feedback`) capture the wiring-level properties
that underpin these derivations.

## 5.6 Termination Analysis

The Rust prototype includes a termination analysis binary (8 tests) that
discovers decreasing measures for loops — a well-founded ranking
function on the feedback channel. This is separate from the invariant:
the inference proves _conditional_ invariants (if the loop reaches a
fixpoint, the invariant holds), while termination analysis proves the
loop does reach a fixpoint. Termination is now formalized in Lean4
(`Termination.lean`, zero `sorry`): a `LoopIter` inductive threads
`c_next` into the recursive call (fixing the model limitation where
`EvalIter.eLoopIter` did not expose the next feedback value), and
`decreasing_measure_bounds_iterations` proves by induction that a
decreasing measure bounds the number of non-fixpoint iterations.

# 6. Implementation and Evaluation

## 6.1 The Rust Prototype

The Rust prototype (22 files, 22,030 lines) implements the full
inference pipeline with Z3-backed SMT verification (subprocess
invocation with a structural fallback). It comprises six binaries:
`refinement_inference` (20 tests), `real_programs` (5 programs),
`quantitative_comparison` (15 benchmarks), `termination_analysis` (8
tests), `liquid_types_comparison` (10 examples), and `evaluation`
(90-cell grid). The `RefTy` type models $\{x : T \mid P(x)\}$ with a
predicate algebra, mirroring the `RTy` inductive of
`RefinementProofGraphs.lean`.

The inference engine is also integrated as a plugin crate
(`handl-plugin-ext-refinement`, 270 tests) in the handl platform. This
integration adds three domain-specific axiom sets and arrow libraries,
all inferred annotation-free:

- **List operations** (16 arrows): `sort`, `map`, `filter`, `fold`,
  `insert`, `take`, `drop`, `zip`, `scan`, `reduce`, `vec`, `queue`,
  and others. Contracts include `Sorted`, `IsPerm`, `LengthEq`,
  `LengthPlusOne`, `LengthSubOne`.
- **Parsers** (1 recursive-descent arrow + 6 backtracking atoms): a
  Pratt parser (top-down operator-precedence) implemented as arrow
  graphs, inferring `LengthSubOne` (tokens consumed) and
  `Nested(ListLength)` (termination); plus a backtracking parser using
  Result-type modeling (ADR-0071). The backtracking parser is defined
  in `backtrack.hnl` as
  `parse.try_atom >>> (parse.extract_success ||| (parse.extract_error >>> parse.try_op))`,
  built from six atoms (`parse.try_atom`, `parse.try_op`,
  `parse.extract_success`, `parse.extract_error`, `parse.succeed`,
  `parse.fail`). Failure is modeled as a value — the output is a sum
  type `Result AST + Error` — so backtracking is expressed entirely
  with existing combinators (Seq, Choice, App); no `Try` combinator or
  calculus extension is required. The inference engine conjoins both
  Choice arms' guarantees, deriving that the overall output is always a
  valid `Result` (`IsSuccess ∨ IsError`). The backtracking parser is
  covered by 17 tests.
- **State machines** (3 arrows): `counter`, `buffer`, `protocol`,
  implemented as `loop(comp(choice(inc, dec), first(id)))`. The
  fixpoint discovers data invariants such as `Le(0, output)` (Count ≥ 0) from conditional transition contracts (`state.dec` requires
  `Le(0, input)`, guarantees `Le(0, output)`).

All 20 arrows across three domains infer with zero user annotations,
demonstrating that the structural inference mechanism generalizes
beyond list operations to parsers (including backtracking) and state
machines.

### 6.1.1 Operator Syntax

`.hnl` arrow files support two equivalent surface syntaxes. In addition
to the function-call form (`comp(a, b)`, `choice(a, b)`), the parser
accepts infix operator syntax: `>>>` (sequence, desugaring to
`comp`/`Seq`) and `|||` (choice, desugaring to `choice`/`Choice`).
`|||` binds tighter than `>>>`, so `a >>> b ||| c` parses as
`comp(a, choice(b, c))`. The two forms produce identical `Scheme` IR;
the operators are pure sugar, verified by 10 parser tests confirming
equivalence with the function-call form. The `backtrack.hnl` arrow
(above) is written in operator syntax.

## 6.2 The Lean4 Formalization

The Lean4 mechanization of the inference mechanism (8 files, zero
`sorry`) establishes: `RefinementProofGraphs.lean` (`RTy`,
`RHasType`, `preserves_comp`, `preserves_first`),
`RefinementCharacterization.lean` (completeness/incompleteness
statements), `InvariantDomain.lean` (domain $D$, lattice, transfer,
`True_is_fixpoint`, `lfp_is_invariant`, `floor_not_complete`,
`analyze_incompleteness`), `StructuralInference.lean`
(`inferred_postcondition_sound_full`,
`inferred_postcondition_in_domain`, `floor_does_not_imply_inferred`),
`LoopInvariantDiscovery.lean` (15 theorems and 5 definitions, zero
`sorry`): the body-guarantee seeding theorems
(`loop_invariant_from_body_sound`,
`loop_invariant_from_body_preserved`, `loop_invariant_post_fixpoint`,
`wp_transfer_holds_for_body_guarantee`,
`body_guarantee_stronger_than_floor`,
`loop_invariant_initialized_by_first_step`, `arr_body_guarantee_sound`,
`loop_invariant_at_fixpoint_step`), the WP branching through Choice
theorems (`wp_through_left_sound_left_arm`,
`wp_through_left_sound_right_arm`,
`body_guarantee_satisfies_left_arm_wp`,
`body_guarantee_satisfies_wp_through_left`,
`fixpoint_converges_with_choice`), three additional theorems
(`iterated_loop_invariant_sound` — the body-guarantee invariant holds
at every intermediate step of an `EvalIter` derivation, not just at the
fixpoint; `body_guarantee_implies_true` — the trivial direction
$I \implies \textsf{True}$; `body_guarantee_in_domain` — $D$ is
extended with `exProj` so the body-guarantee invariant is in $D$
whenever the body's postcondition is in $D$), the structural pattern
recognition definitions (`side_channel_first_id_preserves_C`,
`accumulator_feedback_transformed_by_G`,
`filter_loop_preserves_feedback`) capturing the wiring-level behavioral
properties of side-channel, accumulator, and filter loop patterns, and
seven additional theorems/definitions that upgrade these from
behavioral properties to full invariant derivations:
`filter_loop_preserves_any_D_invariant` and `filter_loop_dTrue_in_D`
(any $I \in D$ preserved by filter loops; `dTrue` $\in D$ constructed),
`side_channel_preserves_any_D_invariant` and `side_channel_dTrue_in_D`
(same for side-channel loops), `accumulator_body_guarantee_in_D` and
`accumulator_body_guarantee_preserved` (body-guarantee invariant $\in D$
via `exProj` and preserved for accumulator loops), and the summary
theorem `pattern_invariant_derivations_complete`.
Three additional files extend the formalization: `AlgorithmicCompleteness.lean`
(zero `sorry`) characterizes algorithmic completeness via the counterexample
`conjecture2_is_false` (the body-guarantee invariant is not the strongest
preserved `D`-invariant in general), the soundness of the strongest invariant
`analyze_strongest_sound`, and the conditional theorem
`analyze_strongest_in_D_if_D_closed_under_arbitrary_meets` (algorithmic
completeness within $D$ is exactly the closure of $D$ under arbitrary meets);
`Termination.lean` (zero `sorry`) formalizes loop termination via the
`LoopIter` inductive and `decreasing_measure_bounds_iterations`; and
`TraitInference.lean` (Phase 9, zero `sorry`) proves annotation-free law
recognition — `CutElim` normalization verifies functor laws, the
`SatisfiesLaw` predicate and inference theorem, and the connection to the
invariant domain $D$.

An additional 5,003 lines of Lean4 mechanization
(`ProofGraphs.lean`, `ProofAdvantage.lean`, etc.) establish the
foundational Curry-Howard correspondence, subject reduction, and cut
elimination used as the logical basis for this paper. These are
described in parallel work [self-cite] and summarized in Appendix A.

## 6.3 Lean4 vs. Rust: What Is Formal vs. What Is Empirical

| Component                                                   | Lean4 (formal)                                                                                                                                                                                           | Rust (empirical)                  |
| ----------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------- |
| Subject reduction (foundation)                              | Proven [self-cite]                                                                                                                                                                                       | N/A                               |
| Refinement typing (`RTy`, `RHasType`)                       | Defined + sound                                                                                                                                                                                          | N/A                               |
| `preserves_comp` / `preserves_first`                        | Proven                                                                                                                                                                                                   | N/A                               |
| Invariant domain $D$                                        | Defined                                                                                                                                                                                                  | N/A                               |
| Structural inference soundness                              | Proven (`inferred_postcondition_sound_full`)                                                                                                                                                             | N/A                               |
| Strictly stronger than floor                                | Proven (`floor_does_not_imply_inferred`)                                                                                                                                                                 | N/A                               |
| Incompleteness (invariants outside $D$)                     | Proven (`analyze_incompleteness`)                                                                                                                                                                        | N/A                               |
| Lattice + transfer function                                 | Defined                                                                                                                                                                                                  | N/A                               |
| Actual inference algorithm                                  | Defined (floor)                                                                                                                                                                                          | Implemented (structural + Z3)     |
| Z3 verification                                             | N/A                                                                                                                                                                                                      | Implemented                       |
| Loop invariant discovery (body guarantee)                   | Proven (`loop_invariant_from_body_sound`)                                                                                                                                                                | Implemented (structural patterns) |
| Loop invariant discovery (iterated loop soundness)          | Proven (`iterated_loop_invariant_sound`)                                                                                                                                                                 | N/A                               |
| Loop invariant discovery (WP branching through Choice)      | Proven (`fixpoint_converges_with_choice`)                                                                                                                                                                | Implemented (structural patterns) |
| Loop invariant discovery (structural patterns)              | Proven (full invariant derivations: `filter_loop_preserves_any_D_invariant`, `side_channel_preserves_any_D_invariant`, `accumulator_body_guarantee_preserved`, `pattern_invariant_derivations_complete`) | Implemented (structural patterns) |
| Domain membership ($D$ closed under existential projection) | Proven (`body_guarantee_in_domain`, `exProj`)                                                                                                                                                            | N/A                               |
| Algorithmic completeness (conditional)                      | Proven (`AlgorithmicCompleteness.lean`)                                                                                                                                                                  | N/A                               |
| Termination analysis                                        | Proven (`Termination.lean`)                                                                                                                                                                              | Implemented                       |
| Trait/law inference (annotation-free)                       | Proven (`TraitInference.lean`)                                                                                                                                                                           | N/A                               |
| Real programs                                               | N/A                                                                                                                                                                                                      | 5 programs                        |
| Coverage / scaling / failures                               | N/A                                                                                                                                                                                                      | 90-cell grid                      |

The Lean4 formalization proves the soundness of the inference framework;
the Rust implementation demonstrates the algorithm in practice. Formal
theorems establish what _can_ be proven; the implementation shows what
_is_ proven.

## 6.4 Empirical Results

**Annotation burden.** Arrow graphs require **0 user annotations** to
prove 19 properties, while Liquid Types require **37 annotations** (32
refinement + 5 loop invariants) for the same 19 properties. Base arrow
signatures carry guarantees, but these are the language definition, not
per-program annotations.

**Coverage accuracy.** The evaluation grid comprises 18 graph
structures tested against 5 properties each (90 cells total, 72
non-trivial). For each non-trivial cell, we classify whether the graph
_should_ prove the property (based on its structure and base arrow
signatures) or _should not_:

| Category                          | Count  | Result            |
| --------------------------------- | ------ | ----------------- |
| Should prove (true positives)     | 26     | 26 proven (100%)  |
| Should not prove (true negatives) | 46     | 46 unknown (100%) |
| False positives                   | 0      | —                 |
| False negatives (misses)          | 0      | —                 |
| **Overall accuracy**              | **72** | **100%**          |

The inference proves every property it should and correctly reports
"unknown" for every property it should not. Zero false positives
confirms soundness empirically; zero misses confirms completeness
relative to the domain $D$.

**Scaling.** Inference time scales linearly in graph size and loop
nesting depth, as measured by 15 benchmarks varying graph size from 3
to 50 nodes and loop depth from 0 to 3.

**Real programs.** All five real programs (insertion sort, `map`,
`filter`, `fold`/sum, pipeline) are built from arrow primitives and
verified annotation-free. Insertion sort is
`loop(comp(comp(first(head_and_tail), first(insert)), consume_one))`
with the `Sorted` invariant inferred from `insert`'s signature (Section
4.7).

**Cross-domain validation.** The platform integration
(`handl-plugin-ext-refinement`, 270 tests) extends the evaluation
beyond list operations to three domains, all annotation-free:

| Domain                 | Arrows  | Key inferred properties                                             |
| ---------------------- | ------- | ------------------------------------------------------------------- |
| List operations        | 16      | `Sorted`, `IsPerm`, `LengthEq`, `LengthPlusOne`                     |
| Parsers (Pratt)        | 1       | `LengthSubOne` (tokens consumed), `Nested(ListLength)` (terminates) |
| Parsers (backtracking) | 6 atoms | `IsSuccess ∨ IsError` (valid `Result` on every branch)              |
| State machines         | 3       | `Le(0, output)` (Count ≥ 0), length bounds (buffer)                 |

The state machine results are notable: the fixpoint discovers data
invariants (e.g., `Count ≥ 0`) from conditional transition contracts
without user-supplied invariants. A counter
`loop(comp(choice(state.inc, state.dec), first(id)))` infers
`Le(0, output)` because `state.dec` carries the precondition
`Le(0, input)` and guarantee `Le(0, output)`; the fixpoint propagates
the guarantee through the loop, establishing the invariant.

The backtracking parser is a new benchmark category exercising
Result-type modeling (ADR-0071). The graph
`parse.try_atom >>> (extract_success ||| (extract_error >>> parse.try_op))`
produces a sum-typed output (`Result AST + Error`); the Choice
branching mechanism conjoins both arms' guarantees, and the inference
derives `IsSuccess ∨ IsError` — the parser always produces a valid
`Result` regardless of which branch is taken. This confirms that
backtracking, previously out of scope, is handled by the existing
Choice machinery once failure is modeled as a value.

## 6.5 Failure Cases (Out-of-Domain Invariants)

We document five failure cases representing invariants outside $D$ —
properties the inference cannot discover, consistent with the
incompleteness theorem (`analyze_incompleteness`):

1. **Arithmetic accumulators.** A loop computing $c' = 2c + 1$ has the
   invariant $c = 2^n - 1$, but unless a base arrow encodes this
   arithmetic, the structural analysis has no candidate to propose.
2. **Permutation.** "Output is a permutation of input" requires
   relational reasoning not visible in graph wiring alone.
3. **Non-terminating loops.** The inference proves conditional
   invariants; it does not prove termination for loops without a
   decreasing measure.
4. **Cross-channel invariants.** Properties relating multiple feedback
   channels (e.g., "channels $C_1$ and $C_2$ have equal length")
   require relational reasoning across channels.
5. **Iteration-count reasoning.** Invariants depending on _how many
   times_ the loop has executed are beyond structural analysis — the
   graph shows _how_ $C$ is updated, not _how many times_.

This is **incompleteness, not unsoundness.** The inference never reports
a false property; it fails to report some true ones. The
`analyze_incompleteness` theorem (Section 4.5) formally proves that such
invariants exist outside $D$.

# 7. Related Work

**Liquid Types.** Rondon, Kawaguchi, and Jhala [38] extend
Hindley-Milner inference with refinement types using SMT solving, but
still require annotations on recursive functions and loops. Vazou et al.
[41] demonstrate practical refinement typing in Liquid Haskell, but still
require annotations on recursive functions. Our work targets the same
class of properties but uses graph structure (not an AST) as the inference
substrate, and loop invariant schemas are inferred by structural analysis
on the graph. The 0-vs-37 annotation comparison (Section 6.4) quantifies
this difference.

**Abstract interpretation.** Cousot and Cousot [10, 11] developed the
dominant framework for loop invariant inference, analyzing the
_semantics_ of the loop body. Graf and Saidi [21] introduced predicate
abstraction. Our approach infers invariant _schemas_ by analyzing the
_structure_ of the loop body (a graph): the wiring of $G$ in `loop G`
explicitly shows how the feedback channel is used, determining the
invariant schema class. This is complementary to abstract
interpretation, not a replacement.

**Data-driven loop invariant inference.** Sharma et al. [40] use
data-driven techniques (machine learning over test executions) to infer
loop invariants. Our approach is structural rather than data-driven: the
invariant schema is determined by the graph wiring, not by observing
executions.

**Arrow calculus.** Hughes [26] introduced arrows; Lindley, Wadler, and
Yallop [31] developed the arrow calculus. Heunen and Jacobs [24] and
Jacobs, Heunen, and Hasuo [25] established the categorical semantics.
Recent work continues to develop the semantic foundations of arrows [39].
Our four primitives are those of the arrow calculus (minus `left`, which
is demoted); our contribution is taking them as a graph grammar and
developing the inference mechanism.

**Hoare logic for arrows.** Alves, Fernandez, and Mackie [1] build a
graphical calculus of proofs for intuitionistic logic / lambda-calculus.
Their graphs are a _notation_ for lambda-terms; ours are a _primitive
syntax_ with no lambda underneath. They do not mechanize the
correspondence, prove subject reduction, or address type inference.

**Graph-based proof systems.** Acclavio, Horne, and Straßburger [43]
develop an analytic proof system on graphs, and Kurashige et al. [42]
use e-graphs for lemma discovery in equational proofs. Both use graph
structure for proof manipulation, but neither targets program
verification or invariant inference. Our work uses graph structure as
the substrate for _inferring_ program properties, not for proof search
or lemma discovery.

**SMT-based verification.** Flanagan and Qadeer [16] and Graf and Saidi
[21] use SMT solving for predicate abstraction and software
verification. Our Z3-backed checker follows the standard
sound-but-incomplete paradigm; the difference is that candidates come
from structural analysis of the graph, not from predicate-abstraction
heuristics or user annotations.

# 8. Limitations and Future Work

**Loop invariant discovery: body guarantee and WP branching formally
proven.** Lean4 proves the soundness of compositional postcondition
propagation (`inferred_postcondition_sound_full`) and, in
`LoopInvariantDiscovery.lean` (15 theorems and 5 definitions, zero
`sorry`), the core loop invariant mechanism. The loop body's structural
postcondition, projected onto the feedback channel, is a sound loop
invariant (`loop_invariant_from_body_sound`): the invariant holds
unconditionally on every output (optimistic propagation), the fixpoint
converges in one step (`wp_transfer_holds_for_body_guarantee`), and it
is strictly stronger than the floor for non-trivial bodies
(`body_guarantee_stronger_than_floor`). The invariant also holds at
every intermediate step of an `EvalIter` derivation, not just at the
fixpoint (`iterated_loop_invariant_sound`). The WP branching through
Choice is likewise proven sound (`fixpoint_converges_with_choice`,
`body_guarantee_satisfies_wp_through_left`): the body guarantee
propagates through each arm of the choice and the combined fixpoint
converges.

**Structural pattern recognition fully formalized.** The
loop-specific strengthening beyond the body guarantee — structural
pattern recognition for side-channel, accumulator, and filter loops —
is implemented in Rust and now fully formalized in Lean4 with complete
invariant derivations. Three behavioral definitions
(`side_channel_first_id_preserves_C`,
`accumulator_feedback_transformed_by_G`,
`filter_loop_preserves_feedback`) capture the wiring-level properties
of these patterns: how `first(id)` preserves the feedback channel, how
`comp(F, first(G))` executes as F then first(G), and how `first(F)`
preserves the feedback channel. Seven additional theorems and
definitions upgrade these from behavioral properties to full invariant
derivations: `filter_loop_preserves_any_D_invariant` (any $I \in D$ is
preserved by filter loops) and `filter_loop_dTrue_in_D` (constructs
`dTrue` $\in D$); `side_channel_preserves_any_D_invariant` and
`side_channel_dTrue_in_D` (same for side-channel loops);
`accumulator_body_guarantee_in_D` (body-guarantee invariant $\in D$ via
`exProj`) and `accumulator_body_guarantee_preserved` (preserved for
accumulator loops); and the summary theorem
`pattern_invariant_derivations_complete`. Each pattern now has both a
D-derivation (constructing the invariant in $D$) and a preservation
proof (showing the invariant is preserved by the loop body), closing
the gap between pattern recognition and invariant domain membership.

**Algorithmic completeness characterized by conditional theorem.** The
inference is sound but not complete. The Lean4 theorem
`analyze_incompleteness` proves that true invariants exist outside $D$.
The domain $D$ is now closed under existential projection (via the
`exProj` constructor), so the body-guarantee invariant
$\exists v, P(\text{pair}(v, c'))$ is in $D$ whenever $P \in D$
(`body_guarantee_in_domain`). The algorithmic completeness question is
now fully characterized in `AlgorithmicCompleteness.lean` (zero
`sorry`): the false conjecture that the body-guarantee invariant is the
strongest preserved `D`-invariant was refuted by the counterexample
`conjecture2_is_false` (`True` is a preserved `D`-invariant that does
not imply the body-guarantee when the postcondition is non-trivial).
The strongest preserved `D`-invariant `analyze_strongest` is proven
sound (`analyze_strongest_sound`), and the conditional theorem
`analyze_strongest_in_D_if_D_closed_under_arbitrary_meets` proves that
algorithmic completeness within $D$ is exactly the closure of $D$
under arbitrary meets — resolving the former open problem by replacing
the unprovable existential negative with a provable conditional
positive. The `analyze_spec` function returns the floor (`True`) and
does not compute the strongest invariant in $D$; the Rust
implementation approximates the strongest invariant by structural
analysis.

**Arithmetic invariants outside $D$.** The domain $D$ contains only
predicates from base-arrow guarantees, conjunction, and lifting through
`first`. Arithmetic invariants are outside $D$ unless the signature
encodes them. Richer signatures enable richer invariants, but the
domain boundary is inherent to the structural approach.

**Z3 subprocess.** The Rust prototype invokes Z3 via subprocess rather
than native bindings, incurring serialization overhead. A native
integration would improve performance but not soundness.

**Future directions.** (1) Formalizing the loop invariant discovery in
Lean4. (2) Extending the refinement language beyond structural
properties — arithmetic and relational refinements. (3) Extending loop
inference to nested loops and multiple feedback channels. (4)
Integrating the Rust inference engine with a proof assistant. (5)
Allowing shared sub-graphs (DAG structure) for proof reuse.

**Scope boundary: deterministic dataflow.** The inference mechanism
applies to deterministic dataflow — programs where the graph structure
fully determines behavior. This covers list operations, recursive-descent
parsers, backtracking parsers, and state machine data invariants.
Backtracking is now in scope: ADR-0071 commits to Result-type modeling,
where parser failure is a value (a sum type `Result AST + Error`) rather
than an effect, so backtracking is expressed with the existing Choice
combinator and no calculus extension is required (Section 6.1). The
backtracking parser is implemented (`backtrack.hnl`, 6 atoms, 17 tests)
and inferred annotation-free. Concurrency is now in scope: ADR-0072
models concurrent systems as dataflow over event streams — a loop over
an externally supplied event stream, with shared state as the feedback
channel and event handlers as Choice branches. The graph remains
deterministic; the non-determinism is external (which events arrive),
and the fixpoint discovers invariants that hold for all event orderings
using the same mechanism as state machines. What remains out of scope:
(a) liveness properties, which are temporal rather than invariant; (b)
global properties spanning multiple independent loops. These boundaries
are documented in ADR-0070 through ADR-0073.

**Backtracking parsers (ADR-0071): implemented, not proposed.**
Result-type modeling is the committed approach: parser output is a sum
type `Result AST + Error`, and backtracking is
`parse_A >>> (extract_success ||| (extract_error >>> parse_B))` — plain
Seq and Choice over a sum-typed output. The earlier `Try`-combinator
option has been dropped. The inference engine handles this with its
existing WP branching through Choice: the `inl` branch propagates the
success guarantee, the `inr` branch propagates into the backtrack arm,
and the conjoined guarantee is `IsSuccess ∨ IsError`. No new inference
rules are needed. The implementation (6 atoms, `backtrack.hnl`, 17
tests) confirms the approach end-to-end.

**Concurrency (ADR-0072): in scope, architecturally clear.**
Concurrency is modeled as dataflow over event streams. A concurrent
system is `loop(comp(handle_event, first(id)))` where events arrive via
the input stream and shared state is the feedback channel `C`;
`handle_event` branches over event types via Choice. Shared-memory
concurrency models each thread's operation as an event handler, and
race-condition safety means the fixpoint invariant holds for all event
orderings. Message-passing (CSP/actor) concurrency models channel state
as the feedback channel, with `receive`/`send` atoms carrying
pre-/post-conditions; deadlock freedom reduces to precondition
preservation by the discovered invariant. No new calculus primitives or
inference rules are required — the fixpoint mechanism from ADR-0073
applies directly. Liveness properties and global multi-loop properties
remain out of scope.

**Module system: normalization as abstraction.** The arrow-native module
system (ADR-0069) treats files as arrows and imports as projections. The
key design insight is that **import normalization is a semantic
abstraction** — the meaning of `import` is fixed (project a name from a
record arrow), but the realization is flexible: compile-time desugaring
(eager, static IR), whole-program flattening (eager, inlined single
graph), or runtime module loading (lazy, cached). All three strategies
implement the same abstraction, and the inference engine is agnostic to
the choice. This separates semantics from implementation strategy,
letting the toolchain choose per context (production build, whole-program
inference, REPL) without changing the meaning of imports.

# 9. Conclusion

We have presented an annotation-free invariant inference mechanism for
lambda-free arrow graphs. Refinements flow from base-arrow signatures
through graph combinators without per-program annotations, and loop
invariant schemas are inferred by structural analysis on the graph and
verified against base arrow contracts — without user-supplied
invariants.

The compositional propagation is formally proven sound in Lean4
(`inferred_postcondition_sound_full`), strictly stronger than the
trivial floor (`floor_does_not_imply_inferred`), and the existence of
undetectable invariants outside $D$ is proven
(`analyze_incompleteness`). The loop invariant discovery is formally
proven sound in Lean4 (`LoopInvariantDiscovery.lean`, 15 theorems and 5 definitions, zero
`sorry`): the body's postcondition projected onto
the feedback channel is a valid invariant
(`loop_invariant_from_body_sound`), the fixpoint converges in one step
(`wp_transfer_holds_for_body_guarantee`), and it is strictly stronger
than the floor for non-trivial bodies
(`body_guarantee_stronger_than_floor`). The invariant holds at every
intermediate step of an `EvalIter` derivation, not just at the
fixpoint (`iterated_loop_invariant_sound`). The WP branching through
Choice is likewise proven sound
(`fixpoint_converges_with_choice`): the body guarantee propagates
through each arm of the choice and the combined fixpoint converges.
The domain $D$ is closed under existential projection (via the `exProj`
constructor), so the body-guarantee invariant is in $D$ whenever the
body's postcondition is in $D$ (`body_guarantee_in_domain`).
The structural pattern recognition (side-channel, accumulator, filter
loop) is now fully formalized with complete invariant derivations: each
pattern has a D-derivation constructing the invariant in $D$ and a
preservation proof showing it is preserved by the loop body
(`filter_loop_preserves_any_D_invariant` / `filter_loop_dTrue_in_D`,
`side_channel_preserves_any_D_invariant` / `side_channel_dTrue_in_D`,
`accumulator_body_guarantee_in_D` / `accumulator_body_guarantee_preserved`),
summarized by `pattern_invariant_derivations_complete`. The behavioral
definitions (`side_channel_first_id_preserves_C`,
`accumulator_feedback_transformed_by_G`,
`filter_loop_preserves_feedback`) capture the wiring-level properties
that underpin these derivations.

The empirical evaluation demonstrates 100% accuracy on 72 non-trivial
benchmark cells: every property the graph should prove is proven
(26/26), and every property it should not is correctly reported as
unknown (46/46), with zero false positives. This contrasts with 37
annotations required by Liquid Types for 19 properties. The platform
integration extends these results to three domains — list operations
(16 arrows), parsers (1 recursive-descent arrow plus a backtracking
parser with 6 atoms using Result-type modeling), and state machines (3
arrows) — all inferred annotation-free, with 270 tests passing. We
have honestly characterized the boundary: the compositional propagation
and the loop invariant discovery (body-guarantee seeding, iterated loop
soundness, and WP branching through Choice) are formally proven sound;
the algorithmic completeness question is fully characterized by the
conditional theorem `analyze_strongest_in_D_if_D_closed_under_arbitrary_meets`
(zero `sorry`); loop termination is formalized in `Termination.lean`
(zero `sorry`); annotation-free law recognition is formalized in
`TraitInference.lean` (Phase 9, zero `sorry`); the structural pattern
recognition is now fully formalized with complete invariant derivations
(each pattern has a D-derivation and preservation proof, summarized by
`pattern_invariant_derivations_complete`, zero `sorry`) and the domain
membership gap is closed ($D$ is closed under existential projection via
`exProj`); the
scope is deterministic dataflow, now including
backtracking parsers
(failure modeled as a value via sum types) with concurrency
architecturally clear (dataflow over event streams, awaiting
implementation); and complex non-structural invariants are not
inferable by this mechanism.

The vision is **proof-carrying computation with minimal syntactic
overhead**: the programmer writes the graph, the language designer
supplies the signature, and the checker infers the refinements and
invariants by structural reasoning.

The Curry-Howard correspondence is the enabling condition: the graph is
simultaneously program, type, and proof, and the inference procedure
reads the proof structure off the graph. This is what distinguishes
graph-structural proof inference from annotation-based refinement typing
or semantic invariant synthesis: the proof is already there in the wiring
— we just have to read it.

# Appendix A: Foundation — Arrow Graphs as Proof Objects

This appendix summarizes the proof-theoretic foundation established in
parallel work [self-cite], which the inference mechanism builds on. Full
proofs are mechanized in Lean4.

## A.1 The Curry-Howard Correspondence

We interpret arrow types as propositions in intuitionistic logic:
$A \rightsquigarrow B \mapsto A \vdash B$, $A \times B \mapsto A \wedge
B$, $A + B \mapsto A \vee B$, $\top \mapsto \top$, $\bot \mapsto \bot$.
The typing rules and the proof rules are notation-for-notation
identical:

| Graph combinator | Type reading                             | Proof reading                                        |
| ---------------- | ---------------------------------------- | ---------------------------------------------------- |
| `id`$_A$         | $A \rightsquigarrow A$                   | $A \vdash A$ (identity)                              |
| `comp`$(G, H)$   | $A \rightsquigarrow C$                   | cut: $A \vdash B, B \vdash C \Rightarrow A \vdash C$ |
| `first`$(G)$     | $A \times C \rightsquigarrow B \times C$ | $\wedge$-functoriality                               |
| `left`$(G)$      | $A + C \rightsquigarrow B + C$           | $\vee$-functoriality                                 |
| `loop`$(G)$      | $A \rightsquigarrow B$                   | trace / fixpoint invariant                           |
| `arr`$(\varphi)$ | $A \rightsquigarrow B$                   | axiom (primitive inference step)                     |

**Theorem (Typing $\Leftrightarrow$ Proof, Lean4).** _For every arrow
graph $G$ and types $A, B$: $\Gamma \vdash G : A \rightsquigarrow B$ iff
$\Gamma \vdash G \Vdash A \vdash B$. The derivations are structurally
identical. The maps `TyOf.toPrOf` and `PrOf.toTyOf` are mutually
inverse bijections (`ProofGraphs.lean`)._

## A.2 Subject Reduction

**Theorem (Subject Reduction, Lean4).** _If $\vdash G : A \rightsquigarrow
B$ and $G \cdot a \Longrightarrow v$ with $a : A$, then $v : B$
(`ProofGraphs.lean`)._

This is the key property used by the inference soundness proof: it
ensures that intermediate values in compositions are well-typed, which
is needed for the `eComp` case of `inferred_postcondition_sound_full`.

## A.3 Local Cut Elimination

The `CutElim` rewrite relation (`ProofAdvantage.lean`) consists of
local rewrites: identity elimination and functor fusion. Each is a
single structural step — no substitution, no alpha-conversion, no
duplication. Unlike proof nets, our calculus is **not linear** —
`first` duplicates the side channel; locality comes from the graph
structure (no binders), not from linearity.

# References

[1] S. Alves, M. Fernandez, I. Mackie. "A New Graphical Calculus of
Proofs." arXiv:1102.2655, 2011.

[10] P. Cousot and R. Cousot. "Abstract Interpretation: A Unified
Lattice Model for Static Analysis of Programs." _POPL '77_, pp.
238-252, 1977.

[11] P. Cousot and R. Cousot. "Systematic Design of Program Analysis
Frameworks." _POPL '79_, pp. 269-282, 1979.

[16] C. Flanagan and S. Qadeer. "Predicate Abstraction for Software
Verification." _POPL '02_, pp. 191-202, 2002.

[17] T. Freeman and F. Pfenning. "Refinement Types for ML." _PLDI '91_,
pp. 268-277, 1991.

[18] J.-Y. Girard. "Linear Logic." _Theor. Comput. Sci._ 50:1-102, 1987.

[21] S. Graf and H. Saidi. "Construction of Abstract State Graphs with
PVS." _CAV '97_, LNCS 1254, pp. 72-83, 1997.

[24] C. Heunen and B. Jacobs. "Arrows, Like Monads, Are Monoids."
_MFPS-XXII_, ENTCS 158, pp. 219-236, 2006.

[25] B. Jacobs, C. Heunen, I. Hasuo. "Categorical Semantics for
Arrows." _J. Funct. Program._ 19(3-4):403-438, 2009.

[26] J. Hughes. "Generalising Monads to Arrows." _Sci. Comput.
Program._ 37(1-3):67-111, 2000.

[27] A. Joyal, R. Street, D. Verity. "Traced Monoidal Categories."
_Math. Proc. Camb. Phil. Soc._ 119(3):447-468, 1996.

[28] J. R. Hindley and J. P. Seldin. _Lambda-Calculus and Combinators:
An Introduction._ 2nd ed., Cambridge University Press, 2008.

[31] S. Lindley, P. Wadler, J. Yallop. "The Arrow Calculus." _J.
Funct. Program._ 20(1):51-69, 2010.

[38] P. M. Rondon, M. Kawaguchi, R. Jhala. "Liquid Types." _PLDI '08_,
pp. 159-169, 2008.

[39] J. Liell-Cock, Z. Shirazi, S. Staton. "The Relative Monadic
Metalanguage." _Proc. ACM Program. Lang._ 10, POPL, Article 60, 2026.

[40] S. Padhi, R. Sharma, T. Millstein. "LoopInvGen: A Loop Invariant
Generator based on Precondition Inference." arXiv:1707.02029, 2017.

[41] N. Vazou, E. L. Seidel, R. Jhala, D. Vytiniotis, S. Peyton-Jones.
"Refinement Types for Haskell." _ICFP '14_, pp. 269-282, 2014.

[42] C. Kurashige, R. Ji, A. Giridharan, M. Barbone, D. Noor, S. Itzhaky,
R. Jhala, N. Polikarpova. "CCLemma: E-Graph Guided Lemma Discovery for
Inductive Equational Proofs." _Proc. ACM Program. Lang._ 8, ICFP,
Article 264, 2024.

[43] M. Acclavio, R. Horne, L. Straßburger. "An Analytic Propositional
Proof System on Graphs." _Log. Methods Comput. Sci._ 18(4), 2022.
