# Why the Trait Layer Is Three Features, Not a Keyword

## The short version

handl has no `trait` keyword and no `impl` keyword. The Rust/Haskell
trait pattern — a named bundle of operations with laws, a concrete
implementation, and a resolution mechanism that finds the right impl
for a type — is not a syntactic category in handl. It is an _emergent
shape_ produced by combining three independent features: **laws**,
**bundles**, and **handlers**.

This is not minimalism for its own sake. The reason for the split is
that the bundled `trait` construct (ADR-0075's approach) was doing
almost nothing that the kernel did not already do. Eight features were
bundled into one keyword; six already existed in handl, independent of
any trait mechanism. The bundle was load-bearing for exactly two
things: equational laws and law proof reuse. Everything else was sugar.

This is better than a `trait` keyword because each feature is
understandable in isolation, composes freely, and can be used without
the others. A user who needs only a verified arrow writes a law. A user
who needs a named record writes a bundle. A user who needs runtime
injection writes a handler. The full trait experience is the
combination of all three — but no user is forced to take all three to
get any one.

## The problem with bundled traits

ADR-0075 introduced a single bundled construct: `trait` (a named schema
of arrow operations plus equational laws), `impl` (a graph assignment
for each operation), and `law` (an equation declared inside a `trait`).
The trait layer bundled eight features:

1. Named bundles of arrows.
2. Passing arrows as parameters.
3. Resolution (finding the right arrows for a type).
4. Named equational laws with compositional proof reuse.
5. First-class arrows (already in the kernel).
6. Effect handlers (already in the kernel).
7. Dependent types / associated types (already in the kernel).
8. ArrowApply / blanket impls (already in the kernel).

Six of the eight are already present in handl, with no `trait` keyword
involved. Records of arrows are already named bundles — Phase 3's
`Language = { parse, eval, format, typecheck, lit }` is a bundle with
impls (Arithmetic, Boolean) and no trait machinery. First-class arrows,
effect handlers, dependent types, signature inclusion, and ArrowApply
are all kernel features that predate the trait layer.

The two features handl actually lacked were equational laws (the
ability to _require_ that an arrow satisfies an equation) and law proof
reuse (verify once, inherit by composition at every use site). The
`trait` keyword was bundling six things the language already had in
order to deliver two things it did not. That is a poor exchange: one
large, complex syntactic category to gate two genuinely new
capabilities.

The bundle is only load-bearing for **multi-operation laws** — laws
that span two or more arrows from the same impl. A roundtrip law needs
both `serialize` and `deserialize` bound together; that binding is what
the bundle provides. A single-operation law like the functor law
attaches to one arrow and needs no bundle at all. This is the common
case.

## The decoupled insight: three independent features

The decoupling rests on the observation that laws, bundles, and
handlers answer three _different_ questions, and that no question
requires the others:

- A **law** answers "does this arrow satisfy this equation?" It
  attaches to any arrow. No bundle required.
- A **bundle** answers "do these operations come from the same impl?"
  It is a named record of arrows with laws attached. Without laws, it
  is just a record — sugar, no semantic power.
- A **handler** answers "which impl do I use here?" It injects an arrow
  or bundle at a scope boundary. It is the resolution mechanism.

The "trait" pattern emerges when all three are present: a law over a
bundle's operations, injected by a handler, verified at the handler
site. But the pattern is a shape, not a keyword. There is no syntactic
marker that says "this is a trait." The combination is recognised by
its parts, consistent with handl's annotation-free philosophy.

This is better than a `trait` keyword because it composes. The seven
non-trivial combinations of the three features each produce something
useful (see the [composition
table](../reference/laws-bundles-handlers.md#composition-table) in the
reference). A user takes only what they need.

## Why handlers for resolution, not implicit search

Rust and Haskell solve the "which impl?" question with global
coherence: at most one impl per trait+type, worldwide, enforced by
orphan rules and specificity algorithms. This is the most complex and
most complained-about part of both languages' trait systems. The
coherence problem is not a minor implementation detail; it is a
structural consequence of implicit global resolution. If the compiler
must silently pick an impl, then there must be a rule that guarantees
exactly one impl is pickable, and that rule must hold across all
modules, including those not yet written.

handl does not solve the coherence problem. It eliminates it, by
design. Resolution is **lexical**: `handle ... with` names the impl at
a scope boundary, and nearest-wins, like exception handlers. An inner
handler shadows an outer one for the same arrow or bundle. There is no
global uniqueness check, no orphan rule, no specificity algorithm. The
compiler never silently picks an impl.

The reason this works is that the handler is explicit. The user has
already said which impl they mean. There is nothing to disambiguate.
The catalog (ADR-0075 §3) survives as a _fallback_ — when no handler is
installed, the compiler searches the open trait catalog. One match is
injected; multiple matches are an error that asks the user to name one
explicitly. The fallback is honest: it never guesses.

This is a deliberate departure from the Rust/Haskell mental model.
Users familiar with those languages will find handlers where they
expected instances. The trade-off is explicitness: the safe,
law-checked path requires writing `handle ... with`. There is no
implicit "the system finds the impl" by default. This is more verbose
for the common case, but it removes the hardest part of the trait
system entirely.

## Why `=` not `≡` in laws

ADR-0075 used `≡` inside `law` declarations, inherited from the Lean4
mechanization, where `≡` distinguishes graph equality from
definitional equality. At the surface syntax level, this is
unnecessary ceremony. A `law` declaration is a distinct syntactic
context: the parser knows it is inside a law, not inside an expression.
The context already disambiguates what `=` means.

Inside a `law` context, `=` means **extensional equality of arrows**:
both sides produce the same output for all inputs. This is unambiguous
because no other meaning of `=` is available in that context. Dropping
`≡` in favour of `=` makes laws easier to type without sacrificing
precision. The ceremony of a special symbol is not carrying its weight.

## The static/dynamic split

Handlers come in two flavours, and the split is load-bearing for law
guarantees:

- A **static handler** fixes the impl at compile time. Laws are
  verified at the `handle` site — CutElim for structural laws, semantic
  axioms for non-functor laws — and the proof travels to every inner
  use. This is the "trait" case.
- A **dynamic handler** chooses the impl at runtime. There is no
  compile-time law guarantee. This is the effect-handler case.

The bundle marks "this is static, law-checked." A bare operation handle
is "this is dynamic, no law claim." The distinction is not a type
annotation; it is a consequence of what the handler binds. A handler
that injects a bundle (a record with laws) is the static path. A
handler that injects a single bare arrow can be dynamic.

This split is honest about a limitation: there is no mechanism to
verify laws for runtime-chosen impls. Dynamic handlers are the
effect-handler case, and effect handlers make no law claim. Trying to
blur this boundary — to verify laws for impls that are not yet chosen —
would require solving a problem that is, in general, undecidable. The
design declines to pretend otherwise.

## Connection to the research

The decoupled surface syntax changes nothing about the verification
machinery underneath. The Lean4 mechanization and Rust prototype from
ADR-0075 remain the substrate, and they are honest about what is proven
and what is not.

**CutElim normalisation verifies structural laws.**
`TraitInference.lean` proves the functor laws (`first id ≡ id`,
`first (f >>> g) ≡ first f >>> first g`) by CutElim normalisation, with
zero `sorry`. The recognition is purely from wiring structure
(`UsesFirst` triggers the check). This is proven for the cases
attempted.

**Congruence and strong normalisation close the decidability gap.**
`CutElimCongruence.lean` adds congruence rules (rewriting inside
subgraphs) and proves strong normalisation — every rewrite sequence
terminates in at most `graphSize G - 1` steps. This means CutElim-based
law checking is decidable for the six-rewrite fragment. That fragment
is not all laws, but it is the structural core.

**Non-functor laws require semantic axioms.**
`EquationalLawInference.lean` proves that laws like the roundtrip law
(`serialize >>> deserialize ≡ id`) and semigroup associativity are
_not_ CutElim rewrites — they are semantic facts about specific base
arrows. The mechanization models this honestly: the law's `sound` field
is an explicit hypothesis (an axiom), not hidden behind a `sorry`.
Structural pattern recognition still triggers the check; the axiom
discharges it.

The split between "CutElim-proven" and "axiom-discharged" is not a
fudge. It is the honest representation of two genuinely different kinds
of law. Structural laws (functor, coproduct) are theorems of the wiring
itself — they hold because of the shape of the graph, independent of
what the base arrows do. Semantic laws (roundtrip, associativity) are
facts about particular base arrows — they hold because `serialize` and
`deserialize` are inverses, not because of any graph shape. Pretending
the second kind was the first kind would be dishonest, and the
mechanization refuses to.

## See also

- [ADR-0076 — Decoupled Trait Layer](../../../../project/adrs/0076-decoupled-trait-layer.md)
  — the design decision this explains.
- [ADR-0075 — Traits as Arrow Signatures](../../../../project/adrs/0075-traits-as-arrow-signatures.md)
  — the bundled approach this supersedes; the catalog, CutElim, and
  research foundation this preserves.
- [Laws, Bundles, and Handlers (reference)](../reference/laws-bundles-handlers.md)
  — exact syntax forms and the composition table.
- [Verify Arrow Laws (how-to)](../how-to/verify-arrow-laws.md) —
  practical steps for declaring, bundling, and injecting.
- [Why the Arrow Language Is Built This Way](./arrow-language-architecture.md)
  — the arrow-native foundation these features build on.
