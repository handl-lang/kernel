# Why the Arrow Language Is Built This Way

## The short version

handl is **arrow-native**: the fundamental unit of computation is an
arrow `A ~> B`, not a function. The language is a human-facing notation
for the arrow calculus kernel, and the central design claim is that
**the graph is the derivation** — the wiring of an arrow graph is, at
once, the type derivation, the proof, the trait conformance, and the
execution schedule.

This is a deliberate departure from the lambda-calculus tradition. It
is not a stylistic choice; it is the move that makes the language
structurally inspectable in a way that closures cannot be.

## Why arrows, not functions

A closure bundles two things: a function body and the environment it
captured. Both halves are opaque to static analysis — you cannot walk
into a captured environment, and you cannot decompose a continuation
without losing the original input.

The arrow calculus has neither half:

- **No function body** — the kernel has no `λx. e` form. The six
  combinators (`arr` / `>>>` / `first` / `choice` / `loop` / `app`)
  do not bind variables.
- **No environment to capture** — with no binder, there are no free
  variables, so there is nothing to close over.

What you might call a "function" is an arrow `τ ~> σ`: a value that
takes a `τ` and produces a `σ`. It does not remember anything beyond
what is wired into it. The wiring _is_ the program.

This is the deliberate opposite of the monadic tradition, where `bind`
threads an opaque host-language continuation. The
[direct-bind impossibility result](../../direct-bind-impossibility.md)
shows this opacity is not cosmetic: a continuation that only sees the
predecessor's output _cannot_ faithfully encode `fanout` or `loop`.
Closures don't just hide structure — they destroy the ability to
represent certain arrow programs at all.

For the full argument, see
[Local Data Without Closures](local-data-without-closures.md).

## Why the graph is the derivation

In classical Curry–Howard, λ-terms _are_ proofs, and binders carry the
proof structure. handl's claim is that **graph wiring carries the proof
structure — no λ needed**. This is a λ-free Curry–Howard
correspondence.

The translation table:

| Arrow primitive        | Program     | Proof                |
| ---------------------- | ----------- | -------------------- |
| `id`                   | identity    | identity `A ⊢ A`     |
| `f >>> g`              | composition | **cut**              |
| `first(f)`             | act on 1st  | **∧-functoriality**  |
| `choice(f, g)`         | branch      | **∨-functoriality**  |
| `loop(f)`              | feedback    | **trace / fixpoint** |
| `arr(φ)`               | lift φ      | **axiom**            |
| `f &&& g` (derived)    | fanout      | **∧-introduction**   |
| `f \|\|\| g` (derived) | merge       | **∨-elimination**    |

The theorem (proven in Lean4): `TyOf G ⟺ PrOf G`. Typing derivation
and proof derivation are the _same inductive object_ — same indices,
same constructors, same side conditions, mutually inverse round-trips.
The proof judgment adds zero logical power over the typing judgment;
it's the same derivation read differently.

This is why one object — the graph — carries four readings at once:

| Reading           | Carried by                               |
| ----------------- | ---------------------------------------- |
| type              | wiring (HM + row polymorphism)           |
| proof             | wiring (cut, functoriality, trace)       |
| trait conformance | wiring (graph assignment to a signature) |
| schedule          | wiring (dependency graph)                |

An opaque monad cannot be a proof object because its structure is
hidden in closures. An arrow graph can, because it has none.

See [Arrows ↔ Logic](../ARROWS_AND_LOGIC.md) for the full
correspondence.

## Why Pratt parsing

The grammar is consumed by a **data-driven Pratt parser** (ADR-0053):
top-down operator precedence, table-driven from grammar rows keyed by
`(token_kind, position)`. Each row carries binding powers, a child
shape, a node kind, and an optional desugar rule.

The choice is architectural, not just ergonomic. The platform's
governing principle is **language as data, engines as interpreters**
(ADR-0044): every stage is a data fragment plus a generic engine that
names no concrete construct. A Pratt parser is the natural fit because
its dispatch is already table-driven — precedence and shape live in
data, not in handwritten recursive-descent branches. Adding a
Pratt-expressible construct requires only new grammar rows, no parser
source changes.

The one context-sensitive rule — the contextual `{}` disambiguation
between records and blocks (ID.11) — is accepted because distinct
delimiters were rejected as syntactic noise in an expression-oriented
language. It is a position-based rule, not a parser special case.

## Why Hindley–Milner with rows

Types are inferred from wiring; explicit annotations are optional.
The inference is **Hindley–Milner extended with row variables**
(OCaml-style row polymorphism) over arrow graphs.

Row polymorphism is chosen because the language is **structurally
typed by default**: records and positional structures are typed by
their shape, not by a nominal declaration. A record with extra fields
unifies with a narrower constraint. This is the natural typing for a
dataflow language where wires carry tuples and the graph shape is the
type.

The typechecker is a **normalisation-by-evaluation (NbE)** engine
(ADR-0054), not a monolithic `match term { … }`. Type rules are data;
the engine is generic. Types are represented as **tagged values**
(ADR-0055) — unforgeable, structurally equal within the host registry
— so the typechecker and runtime share one value space without
confusion.

## Why predicates as types

A type is an ordinary value (usually a function) that applied to a
value yields `type.bool`. `x: T = e` is sugar for `x = e; assert T(x)`.

This is a deliberate refusal to introduce a separate total/proof
sublanguage. Refinement types, type families, and dependent typing
fall out of ordinary function values. The consequence: there is no
"proof mode" distinct from "programming mode" — the same language
does both, and the graph carries both readings simultaneously.

Refinement inference is backed by Z3, but Z3 is an _engine_, not a
language feature. The predicates are handl values; Z3 just solves
them.

## Why traits are graph assignments

A trait is an arrow signature; an impl is a graph assignment. Trait
**inference** is the primary mode — the engine searches an open
catalog of known arrow signatures and recognises conformance from the
wiring. Explicit declarations are secondary sugar.

This follows from "the graph is the derivation": if the wiring is
already the type and the proof, it is also the trait conformance.
There is no separate interface sublanguage because there is no need
for one — the graph already carries the evidence.

Law checking uses **cut-elimination (CutElim)** over proof graphs,
reusing the same λ-free Curry–Howard structure that makes the graph a
proof object. The trait catalog is open and catalog-driven — zero
hardcoded refinement contracts.

## Why files are arrows

A file is an arrow, not a sequence of statements. Imports normalise to
projections.

This is forced by the kernel: if the fundamental unit is an arrow, the
module model cannot be statement-based. There are no statements to
evaluate into an environment, no sequential execution of bindings, no
first-class environment to produce. A file _is_ an arrow graph; import
is projection from that graph; the two caches are the graph itself
(for execution) and its inferred contracts (for verification).

## Why deterministic dataflow for concurrency

The arrow calculus is deterministic dataflow: given an input, the
graph produces a unique output. Concurrency does not break this —
parallelism is inferred from independent branches, and the dependency
graph _is_ the schedule.

No new primitives (`Parallel`, `Race`, `Channel`, `Lock`) are added.
Concurrency is expressed within the existing five combinators, because
independent branches of `&&&` are already structurally independent —
the graph says so. The inference mechanism reads the proof off the
graph structure, which requires that the structure fully determines
the behaviour; deterministic dataflow preserves this.

## The one-line thesis

The arrow calculus is the kernel, and the graph is the type
derivation, the proof, the trait conformance, and the schedule — all
at once. Every other choice (Pratt, HM+rows, predicates-as-types,
graph traits, arrow modules, dataflow concurrency) follows from
refusing to introduce a second object when the wiring already carries
the evidence.
