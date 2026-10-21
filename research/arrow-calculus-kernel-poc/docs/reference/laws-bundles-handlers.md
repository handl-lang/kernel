# Laws, Bundles, and Handlers Reference

The three independent features of the decoupled trait layer (ADR-0076):
**laws**, **bundles**, and **handlers**. No `trait` keyword. No `impl`
keyword. The "trait" pattern is an emergent shape produced by combining
the three.

For design rationale, see
[ADR-0076](../../../../project/adrs/0076-decoupled-trait-layer.md). For
the catalog and CutElim research foundation, see
[ADR-0075](../../../../project/adrs/0075-traits-as-arrow-signatures.md).
For practical steps, see [Verify Arrow Laws
(how-to)](../how-to/verify-arrow-laws.md).

## Components

### Law

A `law` is a standalone declaration that an arrow satisfies an
equation. It attaches to any arrow. No bundle required.

```handl
map : (A ~> B) ~> (F<A> ~> F<B>)
law map_id:    map id        = id
law map_comp:  map (f >>> g) = map f >>> map g
```

A `law` inside a bundle attaches to the bundle's operations:

```handl
Serializer<F> = {
  serialize   : F ~> Text
  deserialize : Text ~> F
  law roundtrip: serialize >>> deserialize = id
}
```

### Bundle

A **bundle** is a named record of arrows plus laws over them. It is
syntactically a record — no keyword. A bundle is only needed when a law
spans multiple operations that must come from the same impl.

```handl
Serializer<F> = {
  serialize   : F ~> Text
  deserialize : Text ~> F
  law roundtrip: serialize >>> deserialize = id
}
```

Without laws, a bundle is a named record of arrows — sugar, no semantic
power:

```handl
Language = { parse, eval, format, typecheck, lit }
```

### Handler

A **handler** injects an arrow or bundle at a scope boundary. This is
dependency injection over effect handlers (ADR-0052). It is the single
resolution mechanism.

```handl
-- inject a single arrow
handle sort_by intCmp list with map = map_list

-- inject a bundle (the "trait" case)
handle migrate json with Serializer<JSON> = json_impl
```

Handlers are lexically scoped, nearest-wins. An inner handler shadows
an outer one for the same arrow or bundle.

## Composition table

The three features are independent. No combination is mandatory. The
"trait" pattern emerges when all three are present.

| Combo                  | What it produces                |
| ---------------------- | ------------------------------- |
| Law alone              | Verified arrow                  |
| Bundle alone           | Named record (sugar)            |
| Handler alone          | Effect injection (dynamic ok)   |
| Law + Bundle           | Verified multi-op contract      |
| Law + Handler          | Verified, injected arrow        |
| Bundle + Handler       | Injected contract               |
| Law + Bundle + Handler | The "trait" pattern (all three) |

## `=` in laws

Inside a `law` context, `=` means **extensional equality of arrows**:
both sides produce the same output for all inputs. This is unambiguous
because `law ...` is a distinct syntactic context. No special `≡`
symbol is used. ADR-0075 used `≡`; ADR-0076 drops it.

## Law verification methods

| Method                | Applies to                                  | Mechanism                                                                | Proven status                                                                                                                       |
| --------------------- | ------------------------------------------- | ------------------------------------------------------------------------ | ----------------------------------------------------------------------------------------------------------------------------------- |
| CutElim normalisation | Structural laws (functor, coproduct)        | Wiring-structure recognition (`UsesFirst`), CutElim rewrites, congruence | Proven for the six-rewrite fragment (`CutElimCongruence.lean`: strong normalisation, terminates in at most `graphSize G - 1` steps) |
| Semantic axiom        | Non-functor laws (roundtrip, associativity) | Structural recognition triggers the check; explicit axiom discharges it  | Honest hypothesis, not hidden behind `sorry` (`EquationalLawInference.lean`)                                                        |

### Which laws are which

- **Structural (CutElim-proven):** functor identity (`first id ≡ id`),
  functor composition (`first (f >>> g) ≡ first f >>> first g`),
  coproduct laws. These are theorems of wiring shape, independent of
  base arrows.
- **Semantic (axiom-required):** roundtrip (`serialize >>> deserialize
= id`), semigroup associativity. These are facts about specific base
  arrows, not about graph shape.

### Law proof reuse

If `migrate = deserialize >>> serialize` and both `serialize` and
`deserialize` have verified roundtrip laws, `migrate` inherits the
lossless proof by composition. Laws compose because laws are arrow
compositions. No separate proof step.

## Resolution methods

| Method                               | Role     | Behaviour                                                                     |
| ------------------------------------ | -------- | ----------------------------------------------------------------------------- |
| Explicit handler (`handle ... with`) | Primary  | Names the impl, lexically scoped, laws checked at installation. Safe default. |
| Catalog search                       | Fallback | When no handler is installed, search the open trait catalog (ADR-0075 §3).    |
| Global coherence                     | None     | Not present. Eliminated by lexical scoping, not solved by algorithm.          |

### Catalog search disambiguation

| Match count | Result                                                                                                                    |
| ----------- | ------------------------------------------------------------------------------------------------------------------------- |
| One         | Impl is injected automatically.                                                                                           |
| Multiple    | Compile error: "ambiguous — N impls match, name one explicitly via `handle ... with`." The compiler never silently picks. |
| Zero        | Unresolved; install a handler or register an impl in the catalog.                                                         |

The catalog is the ambient default handler set — handlers always
installed unless overridden by an explicit `handle ... with`. Catalog
storage (ADR-0075 §4) is unchanged (abstract interface, SQLite
default).

## Static vs dynamic handler semantics

| Handler kind | Impl fixed      | Law guarantee                                                        | Use case                |
| ------------ | --------------- | -------------------------------------------------------------------- | ----------------------- |
| Static       | At compile time | Laws verified at the `handle` site; proof travels to every inner use | The "trait" case        |
| Dynamic      | At runtime      | No compile-time law guarantee                                        | The effect-handler case |

A bundle marks "this is static, law-checked." A bare operation handle
is "this is dynamic, no law claim." Law checking runs once at the
`handle` site for static handlers. There is no mechanism to verify laws
for runtime-chosen impls.

## What this replaces from ADR-0075

| ADR-0075 construct                | ADR-0076 replacement                                       |
| --------------------------------- | ---------------------------------------------------------- |
| `trait` keyword                   | Optional bundle (a record with laws attached). No keyword. |
| `impl` keyword                    | `handle ... with` (handler installation). No keyword.      |
| `law` inside `trait`              | `law` is standalone, attachable to any arrow or bundle.    |
| Implicit catalog search (primary) | Explicit handlers (primary), catalog search (fallback).    |
| Coherence problem                 | Eliminated by lexical scoping of handlers.                 |
| `≡` in laws                       | `=` (unambiguous in `law` context).                        |

## What this preserves from ADR-0075

- The open trait catalog (§3) — ambient default handler set. Unchanged.
- Catalog storage (§4) — unchanged (abstract interface, SQLite default).
- CutElim law verification (§11) — unchanged, applied at the `handle` site.
- Catalog search (§12) — demoted to fallback for the one-impl case. Unchanged in mechanism.
- The research foundation — CutElim rewrites, congruence, strong normalisation, non-functor law axioms. Unchanged.

## Not yet specified

The following are deferred in ADR-0076 and not yet specified:

- **Bundled-operations effect representation.** How the effect system
  represents a bundle of operations as one handler is a design question
  for the effect-handler mechanism, not resolved here.
- **Dynamic handlers + laws.** Verifying laws for runtime-chosen impls
  is not supported. Confirming this boundary is deferred.
- **Specificity-by-verified-laws tiebreaker.** When catalog search
  returns multiple matches, the default is "multiple = error." A
  convenience tiebreaker (prefer the impl with more verified laws) is
  possible but deferred.
- **Law syntax for higher-order laws.** Laws that quantify over arrows
  (e.g. `forall f g. map (f >>> g) = map f >>> map g`) need explicit
  quantifier syntax. The examples use free variables implicitly scoped
  by the law; precise quantifier syntax is deferred.
- **Whether single-arrow laws should be inferable or always declared.**
  ADR-0075's primary mode was trait inference (recognition from wiring
  without declaration). ADR-0076 defaults to declared laws because
  inference is proven only for functor laws and is not complete in
  general. Whether inference becomes the default is deferred.

## See also

- [ADR-0076 — Decoupled Trait Layer](../../../../project/adrs/0076-decoupled-trait-layer.md)
  — design rationale and decision.
- [ADR-0075 — Traits as Arrow Signatures](../../../../project/adrs/0075-traits-as-arrow-signatures.md)
  — the catalog, CutElim, and research foundation this preserves.
- [ADR-0052 — Arrow Calculus Kernel](../../../../project/adrs/0052-arrow-calculus-kernel.md)
  — the `handle ... with` handler machinery.
- [Verify Arrow Laws (how-to)](../how-to/verify-arrow-laws.md) —
  practical steps for declaring, bundling, and injecting.
- [Why the Trait Layer Is Three Features, Not a Keyword](../explanations/laws-bundles-handlers.md)
  — why the layer is decoupled.
