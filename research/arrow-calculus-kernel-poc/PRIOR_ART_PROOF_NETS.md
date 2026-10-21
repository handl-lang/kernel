# Prior Art: Proof Nets, Interaction Nets, and Graphical Proof Objects

## Status: Positioning document for Phase 4

Date: 2026-09-02

This document surveys the prior art most directly relevant to the
Phase 4 result (arrow graphs as λ-free proof objects with a Curry-Howard
correspondence, local cut elimination, and annotation-free type
inference). It is intended to keep the novelty claims honest and to
identify the precise contribution of this work.

---

## 1. Proof Nets (Girard, 1987)

**Citation:**

- Jean-Yves Girard. "Linear Logic." _Theoretical Computer Science_ 50:1–102, 1987.
- Jean-Yves Girard. "Proof-Nets: The Parallel Syntax for Proof-Theory." In _Logic and Algebra_, 1995. [girard.perso.math.cnrs.fr/Proofnets.pdf]

**Key result:** Proof nets are a graph-based syntax for linear logic
proofs that eliminates the inessential orderings of sequent calculus.
Cut elimination on proof nets is **local** — each rewrite step touches
only the redex, not the surrounding proof — and does not require a
substitution lemma. This is because linear logic controls duplication:
each formula is used exactly once, so cut elimination cannot duplicate
sub-proofs.

**Relevance to our work:** Our `ProofAdvantage.lean` result (cut
elimination as local graph rewrite, no substitution lemma) is directly
analogous to the proof-net story. The key difference: proof nets are
for **linear logic**, where linearity guarantees no duplication. Our
graph calculus is for the **arrow calculus**, which is not linear
(`first` duplicates the side channel, `comp` can share sub-graphs).
The locality of our cut elimination comes from the graph structure
(no binders), not from linearity.

**What we do that they don't:** We connect the graphical proof object
to a **programming language** (effects, handlers, recursion — Phases
1-3). Proof nets are a proof-theoretic tool; they don't model
computational effects, handlers, or language protocols. Our work shows
that the arrow calculus — which already models these PL features —
inherits the proof-net advantage.

**Mechanization:** Proof nets for MLL have been mechanized in Rocq/Coq:

- Rémi Di Guardia and Olivier Laurent. "A Formalization of Multiplicative Proof-Nets in Rocq." 2025. [remidig.github.io/papers/rocqtlla2025.pdf]
- The `proofnet_mll` Coq library: [github.com/RemiDiG/proofnet_mll]
- The `ProofNet-IR` Lean4 library: [reservoir.lean-lang.org/@fushanbobfan/proofnet-ir]
- The `Metatheory` Lean4 library includes `ProofNets.lean`: [github.com/Arthur742Ramos/Metatheory]

Our Lean4 mechanization is independent of these (we mechanize arrow
graphs, not linear logic proof nets), but the existence of these
formalizations confirms that graph-based proof objects are a live
research area.

---

## 2. Interaction Nets (Lafont, 1990)

**Citation:**

- Yves Lafont. "Interaction Nets." In _Proc. 17th ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL '90)_, pp. 95–108, 1990. [doi.org/10.1145/96709.96718]

**Key result:** Interaction nets are a graphical model of computation
with local rewrite rules. They generalize proof nets and are Turing
complete. Key properties:

- **Locality:** only active pairs (connected principal ports) can be rewritten.
- **Linearity:** each interaction rule applies in constant time.
- **Strong confluence:** one-step diamond property (if c → c₁ and c → c₂, then c₁ → c' and c₂ → c' for some c').

**Relevance to our work:** Interaction nets are the computational
generalization of proof nets. Our arrow graph rewrites (`CutElim` in
`ProofAdvantage.lean`) are similar in spirit — local, graph-based,
no substitution — but our calculus is not symmetric in the
interaction-net sense (constructors and destructors are not dual). Our
`comp` is cut, our `first`/`left` are functorial strength, our `loop`
is trace — these are categorical, not interaction-combinator, primitives.

**What we do that they don't:** Interaction nets are a **computational
model**; they don't have a Curry-Howard correspondence to a logic (or
at least, not directly — the connection is via proof nets). Our work
establishes the Curry-Howard correspondence for arrow graphs
specifically: `TyOf ↔ PrOf`, subject reduction, proof realizability.
We also have **type inference** (the Rust prototype), which interaction
nets don't address.

---

## 3. Traced Monoidal Categories (Joyal, Street, Verity, 1996)

**Citation:**

- André Joyal, Ross Street, Dominic Verity. "Traced Monoidal Categories." _Mathematical Proceedings of the Cambridge Philosophical Society_ 119(3):447–468, 1996. [doi.org/10.1017/s0305004100074338]

**Key result:** Introduces the abstract notion of a **trace** in a
monoidal category — a uniform way to "feed back" outputs as inputs.
The trace operation captures feedback, contraction, and fixpoint
computation. The structure theorem shows every traced monoidal
category embeds into a tortile (ribbon) monoidal category.

**Relevance to our work:** Our `loop` primitive IS the trace operation.
`loop G : A ⇝ B` where `G : A×C ⇝ B×C` is exactly the trace of `G`
along the `C` channel. The `eLoop` rule in `Eval` is the trace
axiom. The `IteratedLoop.lean` extension (iterated trace = recursive
fixpoint) connects to Hasegawa's work (below).

**What we do that they don't:** Joyal-Street-Verity is pure category
theory. We mechanize the trace operation in Lean4 with subject
reduction (types preserved under trace), and we connect it to a
**programming language** (the arrow calculus with effects and
recursion). The categorical trace is the denotational semantics; our
`Eval`/`EvalIter` is the operational semantics, and subject reduction
connects them.

---

## 4. String Diagrams for Monoidal Categories (Selinger, 2010)

**Citation:**

- Peter Selinger. "A Survey of Graphical Languages for Monoidal Categories." In _New Structures for Physics_, Lecture Notes in Physics 813, pp. 289–355, Springer, 2010. [doi.org/10.1007/978-3-642-12821-9_4, arxiv:0908.3347]

**Key result:** A systematic survey of string diagram languages for
various monoidal category structures (braided, rigid, pivotal,
balanced, tortile, ribbon, traced, compact closed, *-autonomous).
Establishes the correspondence between categorical axioms and
graphical reasoning rules.

**Relevance to our work:** Our arrow graphs ARE string diagrams for a
traced monoidal category with products and coproducts. `comp` is
sequential composition (vertical wiring), `first` is tensorial strength
(horizontal wiring), `left` is coproduct functoriality, `loop` is
trace. The proof-theoretic reading (`PrOf`) is the string-diagram
reasoning system.

**What we do that they don't:** Selinger's survey is categorical and
graphical but not computational — it doesn't connect to type inference,
execution semantics, or programming language features. We provide:
(1) a Lean4 mechanization with subject reduction, (2) a Rust prototype
with annotation-free HM inference, (3) the connection to effects and
language protocols.

---

## 5. Recursion from Cyclic Sharing (Hasegawa, 1997)

**Citation:**

- Masahito Hasegawa. "Recursion from Cyclic Sharing: Traced Monoidal Categories and Models of Cyclic Lambda Calculi." In _Proc. TLCA '97_, LNCS 1210, pp. 196–213, 1997. [doi.org/10.1007/3-540-62688-3_37]
- Masahito Hasegawa. _Models of Sharing Graphs: A Categorical Semantics of Let and Letrec._ PhD thesis, University of Edinburgh, 1997. [lfcs.inf.ed.ac.uk/reports/97/ECS-LFCS-97-360]

**Key result:** Connects cyclic graph rewriting (sharing graphs) to
recursion via traced monoidal categories. Shows that `letrec` (cyclic
sharing) can be modeled by the trace operation, and that this gives a
semantic framework for recursion created from cyclic sharing —
generalizing traditional fixpoint recursion.

**Relevance to our work:** Our `loop` primitive and `IteratedLoop.lean`
extension are directly in this tradition. The iterated loop semantics
(`eLoopIter`) is recursion from cyclic sharing — the feedback channel
is the "shared" resource, and the fixpoint is the "stable sharing."
Hasegawa's categorical model is the denotational semantics; our
`EvalIter` is the operational semantics with proven subject reduction.

**What we do that they don't:** Hasegawa's work is categorical
semantics. We provide operational semantics (`EvalIter`), prove subject
reduction (types preserved across iterations), and mechanize it in
Lean4. We also connect it to the Curry-Howard correspondence (the
proof reading of `loop` is trace/fixpoint in the proof system).

---

## 6. Arrows as Monoids in Profunctor Categories (Heunen, Jacobs, Hasuo, 2006-2009)

**Citation:**

- Chris Heunen and Bart Jacobs. "Arrows, Like Monads, Are Monoids." In _Proc. MFPS-XXII_, ENTCS 158, pp. 219–236, 2006.
- Bart Jacobs and Ichiro Hasuo. "Freyd is Kleisli, for Arrows." In _Proc. MSFP 2006_.
- Bart Jacobs, Chris Heunen, Ichiro Hasuo. "Categorical Semantics for Arrows." _Journal of Functional Programming_ 19(3-4):403–438, 2009. [doi.org/10.1017/S0956796809007308]

**Key result:** Arrows are monoids in the category of bifunctors
`C^op × C → Set` (i.e., profunctors). The Kleisli construction for
arrows yields Freyd categories, formalizing "Arrows are Freyd
categories." This is the categorical foundation: a profunctor with
monoid structure (composition) + strength (first) + coproduct
functoriality (left) + trace (loop) = arrow.

**Relevance to our work:** This is the categorical semantics of our
`Graph` inductive. `comp` = monoid multiplication, `arr` = monoid unit
(or base arrow from the signature), `first` = tensorial strength,
`left` = coproduct functoriality, `loop` = trace. The "strong
cocartesian traced profunctor = Arrow" slogan (from our Challenge #12)
is exactly this result.

**What we do that they don't:** Jacobs-Heunen-Hasuo is categorical
semantics. We provide: (1) a **syntactic** proof system (`PrOf`) with
a Curry-Howard correspondence to typing (`TyOf`), (2) operational
semantics (`Eval`) with subject reduction, (3) a Lean4 mechanization,
(4) cut elimination as local graph rewrite. The categorical semantics
is the backdrop; our contribution is the proof-theoretic and
operational layer.

---

## 7. The Arrow Calculus (Lindley, Wadler, Yallop, 2010)

**Citation:**

- Sam Lindley, Philip Wadler, Jeremy Yallop. "The Arrow Calculus." _Journal of Functional Programming_ 20(1):51–69, 2010. [doi.org/10.1017/S095679680999027X]

**Key result:** Introduces a metalanguage for arrows that resembles
Moggi's monad metalanguage. Replaces the three constants + nine laws
of the classic arrow definition with four constructs + five laws. The
five laws are shown to be sound and complete.

**Relevance to our work:** This is the direct predecessor of our arrow
calculus. Our five primitives (`arr`, `comp`, `first`, `left`, `loop`)
correspond to Lindley-Wadler-Yallop's constructs. Our contribution is
showing that these primitives, taken as a **graph** (not as a λ-calculus
extension), form a proof system with a Curry-Howard correspondence.

**What we do that they don't:** Lindley-Wadler-Yallop work in a
λ-calculus setting (the arrow calculus extends STLC). We work in a
**λ-free** setting (the `Graph` inductive has no binder). The
Curry-Howard correspondence for the λ-based arrow calculus is just
the standard Curry-Howard for STLC. The Curry-Howard correspondence
for the λ-free graph calculus is the new result — the proof structure
is in the wiring, not in binders.

---

## 8. A Graphical Calculus of Proofs (Alves, Fernández, Mackie, 2011)

**Citation:**

- Sandra Alves, Maribel Fernández, Ian Mackie. "A New Graphical Calculus of Proofs." arXiv:1102.2655, 2011. [ar5iv.labs.arxiv.org/html/1102.2655]

**Key result:** A graphical representation for proofs of intuitionistic
logic, inspired by proof nets and interaction nets. By Curry-Howard,
this also gives a graphical notation for λ-calculus. The calculus
supports different levels of abstraction for proof simplification
(cut elimination).

**Relevance to our work:** This is the **closest prior work**. They
also build a graphical proof calculus inspired by proof nets, and they
also connect it to Curry-Howard. The key difference: their calculus is
for **intuitionistic logic / λ-calculus** (they represent λ-terms as
graphs). Our calculus is for the **arrow calculus** (we represent
arrow graphs as proofs). Their graphs are a _notation_ for λ-terms;
our graphs are a _primitive_ syntax with no λ underneath.

**What we do that they don't:** (1) We work with the arrow calculus
specifically, not λ-calculus — our graphs have no binder, not even a
hidden one. (2) We mechanize the correspondence in Lean4 (they don't
mechanize). (3) We prove subject reduction and cut elimination
preservation. (4) We have annotation-free HM type inference (Rust
prototype). (5) We connect to effects, handlers, and language
protocols (Phases 1-3).

---

## 9. Boisseau & Gibbons (2018) — Profunctor Optics

**Citation:**

- Guillaume Boisseau and Jeremy Gibbons. "What You Needa Know about Yoneda: Profunctor Optics and the Yoneda Lemma." _Proc. ACM Program. Lang._ 2(ICFP), Article 84, 2018. [doi.org/10.1145/3236779]

**Key result:** Derives the profunctor representation of optics (lenses,
prisms) from the concrete representation using the Yoneda Lemma. While
this paper is about optics, not arrows, it establishes the profunctor
machinery that underlies the categorical semantics of arrows.

**Relevance to our work:** The profunctor framework is the categorical
backdrop for arrows (per Jacobs-Heunen-Hasuo). Boisseau-Gibbons
demonstrate the practical power of the profunctor approach in
Haskell. Our work is orthogonal: we use the arrow primitives directly
(as a graph calculus), not the profunctor encoding.

---

## 10. Hughes (2000) — Arrows

**Citation:**

- John Hughes. "Generalising Monads to Arrows." _Science of Computer Programming_ 37(1-3):67–111, 2000. [doi.org/10.1016/S0167-6423(99)00034-6]

**Key result:** Introduces arrows as a generalization of monads for
structuring combinator libraries. Arrows make the dependence on input
explicit (unlike monads, which only model output).

**Relevance to our work:** This is the origin paper for the entire
project. Our five primitives are the arrow operations; our `Graph`
inductive is the arrow syntax; our `Eval` is the arrow semantics.

---

## 11. Graph-Based Type Inference (Erwig, McAdam, Clerici et al.)

**Citations:**

- Martin Erwig. "Visual Type Inference." _Journal of Visual Languages and Computing_ 17(2):161–186, 2006. [doi.org/10.1016/j.jvlc.2005.04.004]
- Bruce J. McAdam. "Graphs for Recording Type Information." Technical Report ECS-LFCS-99-415, University of Edinburgh, 1999.
- Silvia Clerici, Cristina Zoltan, Guillermo Prestigiacomo. "Graphical and Incremental Type Inference: A Graph Transformation Approach." In _Trends in Functional Programming (TFP)_, 2009/2010. [doi.org/10.1007/978-3-642-22941-1_5]

**Key result:** Erwig presents HM-style inference that works by
labeling nodes in a type-constraint graph and propagating types along
edges — no explicit type environment needed. McAdam shows how to record
HM type information as graphs. Clerici-Zoltan-Prestigiacomo's NiMo
language uses graph grammar and graph unification for incremental type
inference in a visual dataflow language.

**Relevance to our work:** These works show that HM inference is not
tied to ASTs — it can be performed on graphs. This supports the idea
of typing arrow proof graphs directly.

**What we do that they don't:** The existing graph-inference work
targets visual programming or alternative presentations of HM for
λ-calculus. We give a **logical proof-typing** for arrow combinators
and connect graph typing to proof normalization (the Curry-Howard
correspondence). Our `infer_type_poly` (Rust) performs HM unification
over arrow graph structures with fresh-variable instantiation of
polymorphic base arrows.

---

## 12. Combinatory Logic Curry-Howard (Curry, Hindley-Seldin, Howard)

**Citations:**

- Haskell B. Curry and Robert Feys. _Combinatory Logic, Vol. I._ North-Holland, 1958.
- J. Roger Hindley and Jonathan P. Seldin. _Lambda-Calculus and Combinators: An Introduction._ 2nd ed., Cambridge University Press, 2008.
- William A. Howard. "The Formulae-as-Types Notion of Construction." 1969 manuscript, published in _To H. B. Curry: Essays on Combinatory Logic_, Academic Press, 1980.

**Key result:** Typed combinatory logic (SK combinators) has a
Curry-Howard correspondence with Hilbert-style proofs — no λ-binders,
no α-equivalence. This is the original "variable-free proof object."

**Relevance to our work:** Combinatory logic is the precedent for
variable-free Curry-Howard. Our arrow graphs are variable-free in the
same sense (no binder), but they carry richer structure (products,
sums, trace) that combinatory logic doesn't model directly.

**What we do that they don't:** Combinatory logic is
implicational/functional but not effectful. Our arrow graphs model
effects, choice, and feedback — a strictly richer computational
vocabulary with a corresponding richer proof theory.

---

## Important Caveat: The "Strong Cocartesian Traced Profunctor = Arrow" Slogan

A focused prior-art search found that **no published paper states
precisely** "a strong cocartesian traced profunctor is exactly an
Arrow" as a single theorem. The ingredients are all known separately:

- **Strong profunctor = `first`** (Asada 2010: "Arrows are strong monads in Prof")
- **Cocartesian profunctor = `left`/`right`** (Boisseau-Gibbons 2018, via optics)
- **Traced profunctor = `loop`** (Hasegawa 1997, Joyal-Street-Verity 1996)

The combined equivalence appears to be **folklore**. If we need the
exact slogan, we should either (a) prove it as a new result or (b)
phrase it carefully as folklore and cite the three component papers.

**Additional citation for the profunctor characterization:**

- Kazuyuki Asada. "Arrows are Strong Monads." In _Proc. MSFP 2010_. [doi.org/10.1145/1863597.1863607]
- Robert Atkey. "What is a Categorical Model of Arrows?" _ENTCS_ 229:19–37, 2011. [doi.org/10.1016/j.entcs.2011.02.014]

---

## Summary: What Is and Isn't Novel

### NOT novel (established prior art):

- Graphical proof objects without binders (proof nets, Girard 1987)
- Local cut elimination on graphs (proof nets, interaction nets)
- Trace/feedback as a categorical operation (Joyal-Street-Verity 1996)
- Arrows as monoids in profunctor categories (Heunen-Jacobs-Hasuo 2009)
- Recursion from cyclic sharing (Hasegawa 1997)
- Graphical Curry-Howard for λ-calculus (Alves-Fernández-Mackie 2011)
- The arrow calculus (Lindley-Wadler-Yallop 2010)

### POTENTIALLY novel (our specific contribution):

1. **Arrow graphs as λ-free proof objects with a mechanized Curry-Howard
   correspondence.** The correspondence `TyOf ↔ PrOf` for arrow graphs
   (not λ-terms, not proof nets) is new. The Lean4 mechanization with
   round-trip bijections is new.

2. **Cut elimination as local graph rewrite for arrows, mechanized.**
   While cut elimination on proof nets is known, the specific rewrite
   system for arrow graphs (`CutElim` with `ceIdLeft`, `ceIdRight`,
   `ceFirstFusion`, `ceLeftFusion`) and its mechanized proof of
   proof/type preservation is new.

3. **Annotation-free HM type inference over graph structures.**
   Applying Hindley-Milner unification to arrow graphs (not syntax
   trees) with fresh-variable instantiation of polymorphic base arrows
   is a new practical demonstration.

4. **Iterated loop semantics with subject reduction.** The `EvalIter`
   relation with `eLoopZero`/`eLoopIter` and the proof that iterated
   subject reduction holds is new (Hasegawa studied the categorical
   semantics; we provide operational semantics + Lean4 mechanization).

5. **The connection to PL features.** Proof nets and interaction nets
   are proof-theoretic/computational tools. We show that the arrow
   calculus — which models effects, handlers, recursion, and language
   protocols — inherits the proof-net advantage. This bridges
   proof theory and programming language design.

### The honest one-sentence claim:

> We mechanize in Lean4 that the five independent arrow-calculus
> primitives form a λ-free proof system with a Curry-Howard
> correspondence, local cut elimination (no substitution lemma), and
> annotation-free polymorphic type inference — connecting the
> proof-net advantage (Girard 1987, Lafont 1990) to a programming
> language that models effects, handlers, and recursion.

---

## Recommended Positioning for Publication

**Frame as:** "Proof nets meet programming languages." The proof-net
community knows that graphs avoid the substitution tax; the PL
community knows that arrows model effects and recursion. We connect
the two: arrow graphs are proof objects, and they inherit the
proof-net advantage.

**Do NOT claim:** "We discovered that graphs can serve as proof
objects." (That's Girard 1987.)

**DO claim:** "We show that the arrow calculus — which already models
effects, handlers, and recursion — can serve as a λ-free proof object
with a mechanized Curry-Howard correspondence, and we demonstrate
annotation-free type inference over graph structures."

**Target venues:** ICFP (functional programming + types), POPL
(programming languages), CSL (computer science logic), or LICS (logic
in computer science). The work spans PL and proof theory, so ICFP or
POPL is the best fit if the PL connection is emphasized.
