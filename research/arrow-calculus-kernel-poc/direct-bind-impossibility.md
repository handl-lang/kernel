---
title: "A Direct-Bind Impossibility for Arrow Fanout and Loop"
subtitle: "A Mechanized Boundary for Structural Observability"
date: ""
---

# Abstract

We prove a _semantic impossibility_ for a precisely scoped class of encodings: no faithful _direct-bind_ encoding of the arrow primitives $\fanout$ (fanout) or $\loopop$ (feedback) preserves arrow semantics. A direct-bind encoding is a pair $(m, k)$ where the arrow is encoded as $\bindop\,m\,k$, with $m$ and $k$ satisfying the semantic specifications of the arrow's sub-computations, and the only communication from $m$ to the continuation $k$ is $m$'s monadic result — no side channel carries the original input to $k$. The proof rests on a single encoding-independent law of $\bindop$ (provable by $\mathsf{rfl}$ from $\bindop$'s semantics): the continuation in $\bindop\,m\,k$ is invoked with $m$'s _output_, never the original arrow input. For the witness $\fanout(\Get,\Put)$, this forces the monadic final state to be the threaded state while the arrow final state is the original input, diverging whenever $\mathit{input}\neq\mathit{state}$---for _all_ faithful direct-bind encodings, not merely the canonical translation. An analogous theorem holds for $\loopop$ (with a pair/feedback value domain). Both are mechanized in Lean 4. A third result for $\leftc$ (choice), with a weaker hypothesis, appears in the appendix.

The result is _not_ that "monads cannot encode arrows" — a monad that threads the original input through its state (e.g., a reader-state monad carrying both $\mathit{input}$ and $\mathit{state}$) can encode $\fanout(\Get,\Put)$. The result is that such an encoding is _not_ a direct-bind encoding: it requires a side channel beyond $m$'s monadic result. This sharpens the known expressiveness gap (Lindley, Wadler, Yallop [-@lindley2011idioms]) from "the inverse translation requires $\ArrowApply$" to "no faithful direct-bind encoding of $\fanout$ or $\loopop$ exists."

We formalize the information loss via an _indistinguishability_ argument: $\mathsf{encodeMonad}(\fanout(f, g)) = \mathsf{encodeMonad}(\mathsf{seq}(f, g))$ by $\mathsf{rfl}$, so any observer of the encoded monadic representation cannot distinguish fanout from sequencing. We derive a structural information ordering $\sigmaop(\OM(C)) \subseteq \sigmaop(\FM(C)) \subseteq \sigmaop(\FA(C))$, with both inclusions strict for suitable computations. $\ArrowApply$ preserves $\sigmaop$ (the structural facts recoverable from the freer arrow representation). We do not claim maximality over all conceivable representations; a tagged representation recovers strictly more, and we prove this.

With $\ArrowApply$, the five arrow primitives are expressively equivalent to monads ($\ArrowApply \cong \mathsf{Monad}$, Lindley, Wadler, Yallop [-@lindley2011idioms]) but _representationally superior_: the same computational content is carried in an inspectable tree, not an opaque closure.

As a negative side-result (Appendix), the standard arrow-to-lambda translation $\T$ is linear ($\size{\T(p)} \leq 8\cdot\size{p}$), compositional ($\T(f \comp g) = \T(g) \circ \T(f)$ definitionally), and law-preserving (the loop extension law holds under $\beta\eta$ plus fix-fusion/Bekić's lemma [-@bekic1969]). No translation asymmetry exists. The entire library comprises 212 Lean 4 theorems across 17 modules, all fully proven with zero `sorry`, supported by 242 Rust tests.

# Introduction {#sec:intro}

Arrows, introduced by Hughes [-@hughes2000], generalize monads to a notion of computation that need not be a strong functor. They have been proposed as a substrate for programming-language construction: a small calculus of composition, choice, and feedback from which abstraction, recursion, effects, and tooling can be _observed_ rather than _postulated_.

The expressiveness gap between arrows and monads is known: Lindley, Wadler, and Yallop [-@lindley2011idioms] proved that arrows embed into monads, but monads require $\ArrowApply$ to embed back. What is _not_ known is the precise _semantic_ content of this gap: _which_ arrow primitives cannot be encoded by monadic $\bindop$ _under a direct-bind discipline_, and _why_? Prior work [-@vandomelen2025freer] observed the gap empirically (freer monad continuations are opaque to static analysis); we prove a formal, scoped version.

**Scope.** We do not prove "monads cannot encode arrows." A monad that threads the original input through its state (a reader-state monad carrying both $\mathit{input}$ and $\mathit{state}$) can encode $\fanout(\Get,\Put)$. Our result is narrower and more precise: no _direct-bind_ encoding — one where the arrow is encoded as $\bindop\,m\,k$ with $m$'s monadic result as the _only_ communication from $m$ to $k$ — preserves arrow semantics for $\fanout$ or $\loopop$. The obstruction is structural: $\bindop$ exposes only the predecessor's output to the continuation, never the original input.

**Contribution.** This paper makes two primary contributions, both mechanized in Lean 4:

1. **A semantic impossibility for direct-bind encodings** ([Section 3](#sec:impossibility)). We define a formal `BindEncoding` class---a _direct-bind_ encoding where the arrow is encoded as $\bindop\,m\,k$ with no side channel carrying the original input to $k$---and prove that no faithful `BindEncoding` of $\fanout(\Get,\Put)$ or $\loopop\,\mathsf{body}$ preserves arrow semantics. The root cause is a single encoding-independent equation (provable by $\mathsf{rfl}$): the continuation in $\bindop\,m\,k$ is invoked with $m$'s output, never the original input. The theorem `no_faithful_bind_encoding_preserves_fanout` quantifies over all `BindEncoding`s whose components satisfy $\Get$-semantics and $\Put$-semantics. An analogous theorem holds for $\loopop$. A third result for $\leftc$ (choice), with a weaker hypothesis, appears in [Appendix B](#sec:choice-appendix).

2. **A representation boundary for structural observability** ([Section 4](#sec:sigma)). We prove $\mathsf{encodeMonad}(\fanout(f, g)) = \mathsf{encodeMonad}(\mathsf{seq}(f, g))$ by $\mathsf{rfl}$: the monadic encoding cannot distinguish fanout from sequencing. We derive a structural information ordering $\sigmaop(\OM(C)) \subseteq \sigmaop(\FM(C)) \subseteq \sigmaop(\FA(C))$ with both inclusions strict for suitable computations, prove $\ArrowApply$ preserves $\sigmaop$, and show that maximality over all conceivable representations is _false_ (a tagged representation recovers strictly more). With $\ArrowApply$, the freer arrow is expressively equivalent to monads (by Lindley et al.'s result [-@lindley2011idioms]) but representationally superior---the same computational content is carried in an inspectable tree, not an opaque closure.

As a negative side-result ([Appendix A](#sec:translation)), the standard arrow-to-lambda translation $\T$ is linear, compositional, and law-preserving. No translation asymmetry exists.

# Background {#sec:background}

**Arrows.** An arrow [-@hughes2000] is a type constructor $\alpha$ equipped with $\arr : (A \to B) \to \alpha\,A\,B$ and $\comp : \alpha\,A\,B \to \alpha\,B\,C \to \alpha\,A\,C$, satisfying category-like laws. Additional structure: $\first$ (products/fanout), $\leftc$ (sums/choice), $\loopop$ (feedback). The arrow laws include the composition-through-$\first$ law and the loop extension law $\loopop(f \comp \first\,g) = \loopop\,f \comp g$.

**Arrow calculus.** Lindley, Wadler, and Yallop [-@lindley2008arrow] established a bidirectional correspondence between the arrow calculus and lambda with products and sums. Their translation is the standard one; our $\T$ ([Appendix A](#sec:translation)) is an instance of their forward direction.

**ArrowApply and monads.** Lindley, Wadler, and Yallop [-@lindley2011idioms] established that $\ArrowApply$ (arrows with an $\app$ combinator for dynamic application) is isomorphic to $\mathsf{Monad}$. Without $\app$, arrows cannot express arbitrary higher-order functions; with $\app$, they have full monadic power.

**Freer monads and freer arrows.** Kiselyov and Ishii [-@kiselyov2013freer] introduced freer monads, which represent computations as explicit data structures. VanDomelen et al. [-@vandomelen2025freer] introduced freer arrows and observed empirically that freer monad continuations are opaque to static analysis, while freer arrow trees are inspectable. They did not prove a semantic impossibility; our contribution ([Section 3](#sec:impossibility)) is the formal, mechanized version.

**Algebraic effects for arrows.** Lindley [-@lindley2014algebraic] generalized algebraic effects and effect handlers to support idiom and arrow computations. The strict inclusions idioms $\subset$ arrows $\subset$ monads were established by Lindley, Wadler, and Yallop [-@lindley2011idioms] via type isomorphisms. Our characterization is concrete (about specific combinators $\fanout$, $\leftc$, $\loopop$) and mechanized.

# A Semantic Impossibility for Direct-Bind Encodings {#sec:impossibility}

This is the central result. We define a formal class of direct-bind encodings, state the semantic specifications precisely, and prove that no faithful encoding of $\fanout(\Get,\Put)$ or $\loopop\,\mathsf{body}$ preserves arrow semantics. The result is not "monads cannot encode arrows" — it is more precise: once the only communication channel from the first computation to the continuation is its monadic result, fanout cannot be faithfully represented when the first computation's semantics discard the original input.

## The Encoding Class {#sec:encoding-class}

To make the universal quantification precise, we define what a "direct-bind encoding" _is_.

::: {.definition #def:bind-encoding}

#### Direct-bind encoding (BindEncoding)

A **direct-bind encoding** of an arrow $A$ is a pair $(m, k)$ where:

- $m : \mathsf{Monad}$ encodes the first sub-computation,
- $k : \mathsf{V} \to \mathsf{Monad}$ is an opaque continuation encoding the second sub-computation,
- the encoding of $A$ is $\bindop\,m\,k$.

The "no side channel" property is not a separate field of the structure but a _consequence_ of the definition: since the encoding is exactly $\bindop\,m\,k$ (no pre-processing, no duplication, no packaging of the input before the bind), the only value $k$ receives from $m$ is $m$'s monadic result. The original arrow input is passed to `runMonad` as an argument but is not forwarded to $k$ except through $m$'s output. This is what makes the encoding "direct": the composition is a bare bind, not a bind wrapped in additional plumbing. The impossibility theorem is relative to this encoding class.

(Mechanized: `BindEncoding` structure in `FanoutUnencodable.lean`, with `BindEncoding.encoded = Monad.bind enc.m enc.k`.)
:::

Semantic correctness---that $m$ and $k$ faithfully represent the arrow's sub-computations---is specified separately via semantic predicates:

::: {.definition #def:get-put-semantics}

#### Get-semantics and Put-semantics

- **Get-semantics**: $\mathsf{GetSemantics}(m, \mathit{input}, \mathit{state})$ holds iff $\mathsf{runMonad}(m,\ \mathit{input},\ \mathit{state}) = (\mathit{state},\ \mathit{state})$ — the term reads the state, yields it as output, and leaves the state unchanged.
- **Put-semantics**: $\mathsf{PutSemantics}(k)$ holds iff $\forall x\, s.\ \mathsf{runMonad}(k\,x,\ x,\ s).2 = x$ — the continuation writes its input argument to the state. The monadic input is $x$ (equal to the continuation argument), reflecting that $\Put$'s operational semantics pass the monadic input as the continuation argument. A stronger spec $\forall x\, i\, s$ (with independent $i$) would be too strong: $\Put$ writes the monadic input, which equals the argument by construction.

A `BindEncoding` is **faithful** to $\fanout(\Get,\Put)$ if $m$ satisfies Get-semantics and $k$ satisfies Put-semantics. We restrict attention to faithful encodings — those whose components preserve the semantics of the corresponding sub-computations. The impossibility theorem is relative to this encoding class.

(Mechanized: `GetSemantics`, `PutSemantics`, `BindEncoding.faithful_fanout`.)
:::

## The Encoding-Independent Bind Law {#sec:bind-law}

We model monadic computations as a free monad over operations, with $\bindop$ taking an _opaque continuation_ (a function $\mathsf{Value} \to \mathsf{Monad}$, realized as `Rc<dyn Fn(Value) -> FreeM>` in the Rust implementation).

::: {.theorem #thm:bind-law}

#### Bind continuation law, encoding-independent

For all monadic $m$, continuations $k$, $\mathit{input}$, and $\mathit{state}$:

$$
\mathsf{runMonad}(\bindop\,m\,k,\ \mathit{input},\ \mathit{state}) = \mathsf{let}\ (o, s') = \mathsf{runMonad}(m,\ \mathit{input},\ \mathit{state})\ \mathsf{in}\ \mathsf{runMonad}(k\,o,\ \mathit{input},\ s').
$$

This is provable by $\mathsf{rfl}$ from the definition of $\bindop$'s semantics. (Mechanized: `bind_continuation_input_is_predecessor_output`.)
:::

::: {.corollary #cor:no-input}

#### Continuation cannot see original input

If $m$'s output differs from the original input ($\mathsf{runMonad}(m,\ \mathit{input},\ \mathit{state}).1 \neq \mathit{input}$), then $k$ is invoked with a value $\neq \mathit{input}$. (Mechanized: `continuation_cannot_see_original_input`.)
:::

This is the root cause. Arrow combinators can preserve access to an earlier computation input across composition, whereas monadic $\bindop$ exposes only the preceding computation's result to its continuation. The two theorems below — fanout and loop — are not separate impossibility mechanisms but two manifestations of this single structural fact. They form one theorem family: the bind law forces the continuation to see only the predecessor's output, and any arrow primitive that requires the original input in the continuation is subject to the same bottleneck.

## Fanout: the flagship theorem {#sec:fanout}

::: {.definition #def:fanout-witness}

#### The witness

Let $\Get$ be the operation that reads the state and yields it as output, and $\Put$ be the operation that writes the current arrow input into the state. The witness arrow program is:

$$
\mathsf{counterexample} = \fanout(\Get,\ \Put).
$$

Under arrow semantics, $\fanout$ distributes the original $\mathit{input}$ to both branches. So $\Get$ reads the state (output $= \mathit{state}$), and $\Put$ writes the original $\mathit{input}$ to the state. The arrow final state is $\mathit{input}$.
:::

::: {.theorem #thm:arrow-witness}

#### Arrow semantics of the witness

$\mathsf{runArrow}(\fanout(\Get,\Put),\ \mathit{input},\ \mathit{state}).2 = \mathit{input}$. (Mechanized: `runArrow_counterexample_state`.)
:::

::: {.theorem #thm:fanout-universal}

#### No faithful direct-bind encoding preserves fanout

For any `BindEncoding` $(m, k)$ faithful to $\fanout(\Get,\Put)$ — i.e., $\mathsf{GetSemantics}(m, \mathit{input}, \mathit{state})$ and $\mathsf{PutSemantics}(k)$ — if $\mathit{input} \neq \mathit{state}$:

$$
\mathsf{runArrow}(\fanout(\Get,\Put),\ \mathit{input},\ \mathit{state}).2 \neq \mathsf{runMonad}(\bindop\,m\,k,\ \mathit{input},\ \mathit{state}).2.
$$

(Mechanized: `no_faithful_bind_encoding_preserves_fanout`.)
:::

_Proof._ By [Theorem 1](#thm:bind-law), $k$ is invoked with $m$'s output. By Get-semantics, $m$'s output is $\mathit{state}$. By Put-semantics, $k$ writes its argument to the state, so the monadic final state is $\mathit{state}$. By [Theorem 2](#thm:arrow-witness), the arrow final state is $\mathit{input}$. If $\mathit{input} \neq \mathit{state}$, they diverge. The canonical `arrowToMonad` is one faithful instance (verified by `arrowToMonad_is_faithful`), but the theorem holds for the entire class. $\square$

::: {.remark}

#### Why the witness works

$\Get$'s output is constrained to exactly $\mathit{state}$ by Get-semantics — so $m$ cannot encode information about the original $\mathit{input}$ into its output. $\bindop$ threads this output (the state) into $\Put$, which writes the state. The arrow, by contrast, forwards the original input to $\Put$, which writes the input. The divergence is forced by Get-semantics (output $= \mathit{state}$) plus the bind law (continuation sees the output), and is independent of the encoding.
:::

::: {.remark}

#### What the theorem does and does not say

A reader might object: "If you forbid passing the input to the continuation, of course you can't encode a combinator that requires the input." This is correct, and the theorem is deliberately scoped. The contribution is not the _intuition_ (which is straightforward) but the _formalization_: a precisely defined encoding class (`BindEncoding`), precisely stated semantic specs (Get/Put-semantics), and a mechanized proof that the divergence holds for _all_ faithful instances of the class, not merely the canonical translation. The theorem does not say monads cannot encode $\fanout$ — a reader-state monad carrying both $\mathit{input}$ and $\mathit{state}$ can. It says such an encoding is not a direct-bind encoding: it requires a side channel (the input threaded through the state) beyond $m$'s monadic result.
:::

## Loop: an independent witness of the same invariant {#sec:loop-impossibility}

We extend the value domain to include pairs and define $\ArrowIII$ with a $\loopop$ combinator that feeds the body _both_ the input and the feedback channel (as a pair). The witness is $\loopop(\firstOfPair \comp \Put)$: the body extracts the input from the pair and writes it to the feedback channel.

Loop provides an independent witness of the same input-loss invariant exploited by fanout. It is not a qualitatively different impossibility — the root cause is identical — but it demonstrates that the obstruction is not specific to the fanout combinator. Any arrow primitive whose body requires access to the original input (alongside other channels) is subject to the same bind-based bottleneck.

::: {.theorem #thm:loop-universal}

#### No faithful direct-bind encoding preserves loop

For any `BindEncoding3` $(m, k)$ where $m$ satisfies Get-semantics ($\mathsf{runMonad}_3(m,\ \mathit{input},\ \mathit{state}) = (\mathit{state},\ \mathit{state})$) and $k$ satisfies Put-semantics ($\forall x\, s.\ \mathsf{runMonad}_3(k\,x,\ x,\ s).2 = x$), if $\mathit{input} \neq \mathit{state}$:

$$
\mathsf{runArrow}_3(\loopop\,\mathsf{body},\ \mathit{input},\ \mathit{state}).2 \neq \mathsf{runMonad}_3(\bindop\,m\,k,\ \mathit{input},\ \mathit{state}).2.
$$

(Mechanized: `no_faithful_bind_encoding_preserves_loop`.)
:::

_Proof._ Same structure as fanout. $\loopop$ gives the body _both_ the input and the feedback channel (as a pair). $\bindop$ gives the continuation only the previous output. By Get-semantics, $m$'s output is $\mathit{state}$; by Put-semantics, $k$ writes $\mathit{state}$ to the feedback. The arrow writes $\mathit{input}$. They diverge when $\mathit{input} \neq \mathit{state}$. $\square$

## The Structural Root Cause {#sec:root-cause}

::: {.theorem #thm:structural}

#### Impossibility is structural

The arrow $\fanout$ makes a branch depend on the original input: $\mathsf{runArrow}(\fanout(\mathsf{ident},\mathsf{ident}),\ \mathit{input},\ \_).1 = \mathit{input}$. The $\bindop$ continuation sees only the previous output, not the input. This is why the fanout ([Theorem 3](#thm:fanout-universal)) and loop ([Theorem 4](#thm:loop-universal)) impossibility theorems hold, and why recovering full monadic expressiveness requires $\ArrowApply$, which provides the dynamic application capability absent from the basic arrow interface. (Mechanized: `impossibilityIsStructural`.)
:::

::: {.remark}

#### Relation to prior work

VanDomelen et al. [-@vandomelen2025freer] observed the gap _empirically_ (freer monad continuations are opaque to static analysis). The fanout ([Theorem 3](#thm:fanout-universal)) and loop ([Theorem 4](#thm:loop-universal)) impossibility theorems prove the gap is not merely observational but _semantic_: no faithful direct-bind encoding preserves arrow semantics. This strengthens the expressive-power asymmetry from "the inverse translation requires $\ArrowApply$" (Lindley, Wadler, Yallop [-@lindley2011idioms]) to "no faithful direct-bind encoding of $\fanout$ or $\loopop$ exists."
:::

# An Indistinguishability-Based Information Boundary {#sec:sigma}

The impossibility theorems of [Section 3](#sec:impossibility) show _which_ arrow primitives cannot be encoded by $\bindop$ under the direct-bind discipline. This section formalizes _how much_ structural information is lost in the standard monadic encoding, via an indistinguishability argument. The main substantive result is the indistinguishability theorem itself; the ordering and "ground truth" statements follow largely by construction from the definitions of the three representations. We state them for completeness and to frame the strictness result, which is the non-trivial part.

## The Key Indistinguishability {#sec:indist}

The central fact is not stipulated but proved: the monadic encoding conflates fanout with sequencing.

::: {.theorem #thm:indist}

#### Fanout and seq are indistinguishable under monadic encoding

$$
\mathsf{encodeMonad}(\fanout(f, g)) = \mathsf{encodeMonad}(\mathsf{seq}(f, g)).
$$

Both encode to $\bindop(\mathsf{encodeMonad}(f))(\lambda\_.\,\mathsf{encodeMonad}(g))$. (Mechanized: `encodeMonad_fanout_eq_seq`, by $\mathsf{rfl}$.)
:::

This is the formal version of the "false dependency" phenomenon: when arrow $\fanout$ is translated to $\bindop$, the second computation appears to depend on the first's result, destroying the independence information. No observer of the _encoded monadic representation_ can distinguish $\fanout(f, g)$ from $\mathsf{seq}(f, g)$ — they encode to the same term. (The original arrow program obviously distinguishes them; the point is that this distinction is lost in the encoding.)

## The Information Ordering {#sec:ordering}

We define $\sigmaop(R, C) = \{ f \mid f \text{ is recoverable from } R\text{'s encoding of } C \}$, where a structural fact $f$ is _recoverable_ from representation $R$ iff there exists an observer $O_R$ such that $O_R(\mathsf{encode}_R(C)) = \mathsf{holds}(f, C)$ for every $C$. That is: an observer of the encoded representation can determine whether $f$ holds of the original computation. Indistinguishability ([Theorem 6](#thm:indist)) then implies non-recoverability directly: if $\mathsf{encode}_R(C_1) = \mathsf{encode}_R(C_2)$ but $\mathsf{holds}(f, C_1) \neq \mathsf{holds}(f, C_2)$, then no observer $O_R$ can compute $\mathsf{holds}(f, \cdot)$ correctly on both. The three representations are:

- $\FA$ (freer arrow): explicit tree with nodes for $\mathsf{seq}$, $\fanout$, $\leftc$, $\loopop$, $\mathsf{op}$, $\mathsf{apply}$.
- $\FM$ (freer monad): explicit tree with nodes for $\bindop$, $\leftc$, $\loopop$, $\mathsf{op}$. By [Theorem 6](#thm:indist), $\fanout$ and $\mathsf{seq}$ encode to the same $\bindop$ node.
- $\OM$ (opaque monad): a black-box function. No structure is inspectable.

::: {.theorem #thm:ordering}

#### The sigma measure-ordering

For any computation $C$:

$$
\sigmaop(\OM(C)) \subseteq \sigmaop(\FM(C)) \subseteq \sigmaop(\FA(C)).
$$

This holds by construction: $\OM$ exposes nothing, $\FM$ exposes the $\bindop$ tree (which subsumes $\OM$'s information), and $\FA$ exposes a strictly finer tree (with a dedicated $\fanout$ node). (Mechanized: `sigma_ordering`.)
:::

The non-trivial content is the _strictness_ of the $\FM \subseteq \FA$ inclusion:

::: {.theorem #thm:strict}

#### Strict inequality for fanout

For $C = \fanout(f, g)$: $\mathsf{fanout\_independence} \in \sigmaop(\FA(C))$ but $\mathsf{fanout\_independence} \notin \sigmaop(\FM(C))$. This follows from [Theorem 6](#thm:indist): since $\fanout(f,g)$ and $\mathsf{seq}(f,g)$ are indistinguishable under $\FM$, any fact that distinguishes them (like $\mathsf{fanout\_independence}$) is not recoverable. (Mechanized: `strict_fanout`.)
:::

The $\OM \subseteq \FM$ inclusion is also strict for computations with inspectable structure (e.g., effect sets), but the $\FM \subseteq \FA$ strictness is the substantive result, as it rests on the indistinguishability theorem rather than on the definition of opacity alone.

## ArrowApply Preserves sigma {#sec:apply-preserves}

::: {.theorem #thm:apply-preserves}

#### ArrowApply preserves sigma

$\sigmaop(\FAA(C)) = \sigmaop(\FA(C))$. The $\sigmaop$ measure is defined over the original structural fact language (fanout independence, branching, feedback, etc.); the $\app$ constructor is a new node in the representation vocabulary but is not itself a structural fact that $\sigmaop$ tracks. Since $\app$ is a visible tree node (not an opaque closure), it adds monadic power without introducing opacity, so no existing structural fact becomes unrecoverable. (Mechanized: `arrowapply_preserves_sigma`, by $\mathsf{rfl}$; `arrowapply_preserves_fanout` for the fanout-specific corollary.)
:::

## Non-Maximality {#sec:maximality}

The statement that $\sigmaop(\FA, C) = \{ f \mid \mathsf{holds}(f, C) \}$ holds by construction: we defined $\mathsf{holds}$ relative to the freer arrow representation, so $\FA$ recovers exactly the facts that hold. (Mechanized: `sigmaFA_is_ground_truth`.) This is a definitional fact, not a deep theorem; we state it to frame the non-maximality result.

::: {.theorem #thm:max-false}

#### Non-maximality

There exists a representation (_TaggedFreerArrow_: freer arrow with provenance labels on each $\mathsf{op}$) with full monadic power (includes $\app$) that recovers strictly more than $\FAA$: for $C$ with ops, $\mathsf{op\_provenance} \in \sigmaop(\mathsf{Tagged}, C)$ but $\mathsf{op\_provenance} \notin \sigmaop(\FAA, C)$. (Mechanized: `maximality_is_false`.)
:::

::: {.remark}

#### What FAA achieves, and what it does not

The freer arrow with $\ArrowApply$ achieves both (a) full monadic power (via $\app$) and (b) full observability of the structural facts tracked by $\sigmaop$. It is _not_ the maximal representation — richer representations (e.g., TaggedFreerArrow) can carry metadata (provenance, source locations, cost models) beyond the structural fact language, recovering strictly more. We do not claim minimality over all conceivable representations. We claim that $\FAA$ _has_ both properties and that $\sigmaop(\FM)$ is a strict subset: the monadic representation loses fanout independence ([Theorem 8](#thm:strict)), while $\FAA$ does not ([Theorem 9](#thm:apply-preserves)).
:::

# Representational Superiority {#sec:minimality}

## Syntactic Independence (Brief) {#sec:independence}

The standard arrow interface (Hughes [-@hughes2000], Lindley, Wadler, and Yallop [-@lindley2008arrow]) uses three primitives ($\arr$, $\comp$, $\first$). We extend to five by adding $\leftc$ (sums/choice) and $\loopop$ (feedback). In the free arrow calculus, each of the five primitives is syntactically non-derivable from the other four: $\leftc$ introduces $\mathsf{Sum}$-handling, $\first$ introduces $\times$-handling, $\loopop$ introduces feedback, and $\comp$/$\arr$ are trivially independent. (Mechanized in `Basic.lean` via type-inequality for distinct inductive constructors.)

This establishes _syntactic_ non-derivability (distinct constructors have distinct types), not _semantic_ independence. A semantic independence theorem would require, for each primitive, constructing a model satisfying the other four laws in which that primitive is not definable. We do not prove that here, and note that the syntactic result is close to definitional.

## Expressive Equivalence, Representational Superiority {#sec:superiority}

By Lindley, Wadler, and Yallop's result [-@lindley2011idioms], arrows equipped with $\ArrowApply$ are expressively equivalent to monads ($\ArrowApply \cong \mathsf{Monad}$): both can represent the same computations. This is an external theorem about the arrow _interface_, not our own formalization. Our contribution is the _representation_ result: the five-primitive freer arrow with $\ArrowApply$ carries the same computational content in an inspectable tree, while the freer monad carries it in an explicit $\bindop$ tree with opaque continuations. The difference is _representational_:

| Property                             | Freer arrow with $\ArrowApply$ | Freer monad                                           |
| ------------------------------------ | ------------------------------ | ----------------------------------------------------- |
| Expressive power                     | Full monadic (via $\app$)      | Full monadic                                          |
| Representation                       | Inspectable tree               | Explicit $\bindop$ tree with opaque continuations     |
| $\fanout$ structure                  | Visible node                   | Lost (encodes to $\bindop$, [Theorem 6](#thm:indist)) |
| $\leftc$ structure                   | Visible node                   | Visible node                                          |
| $\loopop$ structure                  | Visible node                   | Visible node                                          |
| $\sigmaop$ ([Section 4](#sec:sigma)) | Full structural facts          | Strict subset ([Theorem 8](#thm:strict))              |

The impossibility theorems of [Section 3](#sec:impossibility) show _why_ the representation matters: the arrow primitives that require input access ($\fanout$, $\loopop$) cannot be encoded by $\bindop$ alone under the direct-bind discipline, so the monadic representation _cannot_ carry their structure---it must be re-derived at runtime. The arrow representation carries it by construction.

> _The five-primitive freer arrow with $\ArrowApply$ is a representation achieving both full monadic power and full observability of the structural facts tracked by $\sigmaop$, while the freer monad achieves full monadic power but loses fanout independence._

# Empirical Corroboration {#sec:empirical}

The impossibility and $\sigmaop$ results are formal. We corroborate them with 242 Rust tests (all passing) that implement three representations of the same computations — freer arrow, opaque monad, freer monad — and check that the opaque monad is semantically adequate but structurally lossy: sequential composition is preserved, but fanout/independence, branching, effect sets, per-branch effects, dependency graphs, and feedback are all lost. The freer monad recovers everything, confirming the loss is about _opacity_ (closures hide structure), not monadic structure per se. We do not present this as a systematic empirical study but as a sanity check that the formal asymmetry manifests in executable implementations. The test suite is in the supplementary material.

**Honest limitation.** Structural explicitness does not _require_ arrows---one could define a disciplined lambda calculus with explicit let-binding for every subexpression. The arrow advantage is that the discipline is _enforced by the representation_, not _imposed by convention_. Whether enforced discipline is an advantage depends on the use case; we state this as an architectural argument, not a formal result.

# Related Work {#sec:related}

**Hughes (2000).** Introduced arrows and stated the arrow laws [-@hughes2000]. Our $\T$ is the standard translation implicit in Hughes's presentation; we make linearity and compositionality explicit and mechanize them.

**Lindley, Wadler, Yallop (2008).** Established the bidirectional correspondence between the arrow calculus and lambda with products and sums [-@lindley2008arrow]. Our $\T$ is an instance of their forward translation.

**Lindley, Wadler, Yallop (2011).** Established $\ArrowApply \cong \mathsf{Monad}$ and the strict inclusions idioms $\subset$ arrows $\subset$ monads [-@lindley2011idioms]. Our contribution is the semantic impossibility ([Section 3](#sec:impossibility)), which strengthens this from "the inverse translation requires $\ArrowApply$" to "no faithful direct-bind encoding of $\fanout$ or $\loopop$ exists."

**Kiselyov and Ishii (2013).** Freer monads [-@kiselyov2013freer] make the same structural insight that underlies our representation asymmetry: explicit, traversable representations preserve information that opaque representations destroy. Our indistinguishability theorem ([Section 4](#sec:indist)) formalizes this.

**Lindley (2014).** Generalized algebraic effects and effect handlers to support idiom and arrow computations [-@lindley2014algebraic]. Our work is complementary: we identify a concrete semantic obstruction (the bind continuation law) for specific combinators, rather than a general handler calculus.

**VanDomelen et al. (2025).** Introduced freer arrows and observed the observational gap empirically [-@vandomelen2025freer]. Our contribution is the formal, mechanized impossibility ([Section 3](#sec:impossibility)) and the indistinguishability boundary ([Section 4](#sec:sigma)).

# Conclusion {#sec:conclusion}

We have proved a scoped semantic impossibility: under a precisely defined class of direct-bind encodings (`BindEncoding`), no faithful encoding of arrow $\fanout$ or $\loopop$ preserves arrow semantics. The root cause is a single encoding-independent law of $\bindop$ (provable by $\mathsf{rfl}$): the continuation is invoked with $m$'s output, never the original input. Arrow combinators can preserve access to an earlier computation input across composition; monadic $\bindop$ exposes only the preceding computation's result to its continuation. This is not a claim that monads cannot encode arrows — a monad with a side channel for the input can — but that no _direct-bind_ encoding (one without such a side channel) suffices.

We formalized the information loss via an indistinguishability argument: $\mathsf{encodeMonad}(\fanout) = \mathsf{encodeMonad}(\mathsf{seq})$ by $\mathsf{rfl}$, so any observer of the encoded monadic representation cannot distinguish fanout from sequencing. We derived the ordering $\sigmaop(\OM(C)) \subseteq \sigmaop(\FM(C)) \subseteq \sigmaop(\FA(C))$, with the $\FM \subseteq \FA$ inclusion strict for fanout computations, proved $\ArrowApply$ preserves $\sigmaop$, and showed that maximality over all representations is false.

With $\ArrowApply$, the five arrow primitives are expressively equivalent to monads (Lindley, Wadler, Yallop [-@lindley2011idioms]) but representationally superior: the same computational content is carried in an inspectable tree, not an opaque closure.

As a negative side-result, the standard arrow-to-lambda translation $\T$ is linear, compositional, and law-preserving. No translation asymmetry exists. The genuine asymmetry is semantic and representational, not translational.

**Mechanization.** The Lean 4 formalization comprises 17 modules with 212 theorems, all with zero `sorry`. The core modules are: `FanoutUnencodable.lean` (27 theorems: `BindEncoding` class, Get/Put semantics, encoding-independent $\bindop$ law, universal fanout/loop unencodability, choice with weaker hypothesis), `StructuralInfo.lean` (13 theorems: indistinguishability, $\sigmaop$ ordering, strict inequality, $\ArrowApply$ preservation, non-maximality), `Translation.lean` (22 theorems: linearity, compositionality, loop extension), `Basic.lean` (7 theorems: syntactic independence classifications), `ProofRelevant.lean` (3 theorems: proof-relevant subject reduction), `RefinementCharacterization.lean` (6 theorems), `AlgorithmicCompleteness.lean` (algorithmic completeness characterization via conditional theorem), `Termination.lean` (loop termination via `LoopIter` inductive), `TraitInference.lean` (Phase 9: annotation-free law recognition), `LoopInvariantDiscovery.lean` (full invariant derivations from structural pattern recognition: filter, side-channel, accumulator patterns each have a D-derivation and preservation proof, summarized by `pattern_invariant_derivations_complete`), and `DependentProofGraphs.lean` (dependent loop termination via `DEvalIter`, `DLoopIter`, and `ddecreasing_measure_bounds_iterations` — the last formalization gap is closed). The remaining modules cover proof graphs, invariant domains, structural inference, and iterated loops.

**Axiom dependencies.** The formalization uses three sound axioms, all standard meta-theorems: (1) `BetaEta_confluence_normal_forms` — confluence of $\beta\eta$-reduction on STLC (Tait–Martin-Löf), stated as an axiom because the full confluence proof is beyond the scope of this formalization; (2) `Classical.choice` — the law of excluded middle / choice, used in `ProofRelevant.lean` to extract witnesses from non-emptiness proofs; (3) type inequality between distinct inductive constructors, used in `Basic.lean` for syntactic independence. No `sorry` appears in any proof. The formalization is supported by 242 Rust tests (all passing).

# References {#references}

# Appendix A: The Forward Translation — A Negative Result {#sec:translation}

As a negative side-result, we investigate whether the standard arrow-to-lambda translation $\T$ suffers size blowup or non-compositionality. We prove it does not. This addresses a conjectured translation asymmetry and clarifies that the genuine asymmetry is semantic ([Section 3](#sec:impossibility)), not translational.

## The Translation {#sec:T-def}

We work in the simply-typed lambda calculus with products ($\times$), sums ($+$), and a fixed-point combinator $\fix$, using de Bruijn indices. We call this calculus $\stlc$. The standard translation $\T : \arrowprog \to \lamterm$ is:

$$
\T(\arr\,f) = f \qquad \T(f \comp g) = \lambda x.\, \T(g)\,(\T(f)\,x)
$$

$$
\T(\first\,f) = \lambda(x, y).\, (\T(f)\,x,\, y)
$$

$$
\T(\leftc\,f) = \lambda s.\, \mathsf{case}\,s\,[\mathsf{inl}.\, \mathsf{inl}\,(\T(f)\,x) \mid \mathsf{inr}.\, \mathsf{inr}\,y]
$$

$$
\T(\loopop\,f) = \lambda x.\, \mathsf{fst}\,(\fix\,(\lambda r.\, \T(f)\,(x, r)))
$$

This is an instance of the Lindley--Wadler--Yallop forward translation [-@lindley2008arrow].

## Summary: No Translation Asymmetry {#sec:translation-summary}

| Property                                  | Status                                      | Mechanized                    |
| ----------------------------------------- | ------------------------------------------- | ----------------------------- |
| Linearity ($\size{\T(p)} \leq 8\size{p}$) | Holds                                       | `T_linear`                    |
| Compositionality of $\comp$               | Definitional                                | `T_comp_is_composition`       |
| Compositionality of $\first$              | Up to $\beta$                               | `T_first_compositional`       |
| Compositionality of $\leftc$              | Up to $\beta\eta$ + commuting               | `T_left_compositional`        |
| Loop extension law                        | Up to $\beta\eta\fix$ (Bekić [-@bekic1969]) | `loopExt_eq_under_BetaEtaFix` |
| Loop law fails under $\beta\eta$          | Existential                                 | `loopExt_not_BetaEta`         |

The forward translation is linear, compositional, and law-preserving (up to the general recursion subtlety: the loop extension law holds under $\beta\eta$ plus fix-fusion/Bekić's lemma, but not under $\beta\eta$ alone, since $\fix$ is inert without unrolling). No translation asymmetry exists.

# Appendix B: Choice Unencodability (Weaker Hypothesis) {#sec:choice-appendix}

The fanout and loop theorems of [Section 3](#sec:impossibility) derive divergence purely from Get/Put semantic specifications. We sketch here an analogous result for $\leftc$ (choice), noting that its hypothesis is weaker.

We extend the value domain to include sums ($\mathsf{Left}\,v$, $\mathsf{Right}\,v$) and define $\ArrowII$ with a $\mathsf{choice}$ combinator that branches on the input. The witness is $\leftc(\Get,\ \mathsf{Pure}\,42)$: with input $\mathsf{Right}\,99$, the arrow branches to $\mathsf{Pure}\,42$.

::: {.theorem #thm:choice-universal}

#### Choice unencodability (weaker hypothesis)

For all monadic $m$ satisfying Get-semantics and all $k$, if $k$ applied to $\mathit{state}$ does not produce the arrow result:

$$
\runArrowII(\leftc(\Get,\mathsf{Pure}\,42),\ \mathsf{Right}\,99,\ \mathit{state}).1 \neq \runMonadII(\bindop\,m\,k,\ \mathsf{Right}\,99,\ \mathit{state}).1.
$$

(Mechanized: `no_bind_encoding_preserves_choice`.)
:::

::: {.remark}

#### Why this is weaker

The choice theorem requires an additional hypothesis (`hBranch`) stating that $k$ applied to the state does not produce the arrow result — close to assuming what we want to prove. A version with a clean Put-like constraint (analogous to fanout/loop) would require a richer value domain. We present this as supporting evidence that the same input-loss invariant applies to choice, not as an equally tight universal theorem.
:::
