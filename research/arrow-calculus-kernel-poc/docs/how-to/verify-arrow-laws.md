# How to Verify Arrow Laws

This guide covers declaring laws, bundling arrows that share a law,
injecting impls with handlers, and resolving without a handler. For
the design rationale behind the three-feature split, see [Why the
Trait Layer Is Three Features, Not a
Keyword](../explanations/laws-bundles-handlers.md). For exact syntax
forms, see the [reference](../reference/laws-bundles-handlers.md).

## How to declare a law on an arrow

Write a standalone `law` declaration attached to the arrow. No bundle
required.

```handl
map : (A ~> B) ~> (F<A> ~> F<B>)
law map_id:    map id        = id
law map_comp:  map (f >>> g) = map f >>> map g
```

`=` inside a `law` context means extensional equality of arrows: both
sides produce the same output for all inputs.

If your law is structural (functor, coproduct), CutElim normalisation
verifies it automatically. If your law is semantic (roundtrip,
associativity), you need an axiom — see [How to check if a law is
CutElim-proven or needs an axiom](#how-to-check-if-a-law-is-cutelim-proven-or-needs-an-axiom).

## How to bundle arrows with a shared law

Write a named record of arrows with the law attached inside. Use a
bundle only when a law spans multiple operations that must come from
the same impl.

```handl
Serializer<F> = {
  serialize   : F ~> Text
  deserialize : Text ~> F
  law roundtrip: serialize >>> deserialize = id
}
```

The bundle guarantees `serialize` and `deserialize` come from the same
impl (same handler). This binding is what makes the roundtrip law
meaningful.

If your operations do not share a law, do not write a bundle. A record
of arrows without laws is just a named record — write it as a plain
record.

```handl
Language = { parse, eval, format, typecheck, lit }
```

## How to inject an impl with a handler

Use `handle ... with` to inject an arrow or bundle at a scope boundary.
The handler is lexically scoped: nearest-wins, like exception handlers.

To inject a single arrow:

```handl
handle sort_by intCmp list with map = map_list
```

To inject a bundle (the "trait" case):

```handl
handle migrate json with Serializer<JSON> = json_impl
```

Law checking runs once at the `handle` site. If verification fails, the
`handle` form is a compile error. Every inner use inherits the proof;
you do not re-verify at each use site.

If the handler is static (impl fixed at compile time), laws are
verified and the proof travels. If the handler is dynamic (impl chosen
at runtime), there is no compile-time law guarantee — this is the
effect-handler case, not the trait case.

## How to resolve without a handler

If no `handle ... with` is installed, the compiler searches the open
trait catalog (ADR-0075 §3) as a fallback.

- **One match** — the impl is injected automatically.
- **Multiple matches** — compile error: "ambiguous — N impls match,
  name one explicitly via `handle ... with`." The compiler never
  silently picks.
- **No match** — unresolved; write a `handle ... with` or register an
  impl in the catalog.

To disambiguate the multiple-match case, write an explicit handler:

```handl
handle migrate json with Serializer<JSON> = json_impl
```

## How to check if a law is CutElim-proven or needs an axiom

The split is determined by the kind of law, not by a syntax flag.

If your law is **structural** — functor identity, functor composition,
coproduct laws — CutElim normalisation verifies it from wiring
structure alone. No axiom needed. This is proven for the six-rewrite
fragment (`CutElimCongruence.lean`: congruence plus strong
normalisation, every rewrite sequence terminates in at most
`graphSize G - 1` steps).

```handl
law map_id:    map id        = id
law map_comp:  map (f >>> g) = map f >>> map g
```

If your law is **semantic** — roundtrip, semigroup associativity, any
law that is a fact about specific base arrows rather than about graph
shape — CutElim cannot verify it. The law requires an explicit semantic
axiom. Structural pattern recognition still triggers the check; the
axiom discharges it.

```handl
Serializer<F> = {
  serialize   : F ~> Text
  deserialize : Text ~> F
  law roundtrip: serialize >>> deserialize = id
}
```

The axiom is an explicit hypothesis, not hidden behind a `sorry`. If
you cannot supply the axiom, the law is not verified.

## How to inherit a law proof by composition

If a composed arrow is built from arrows that have verified laws, the
composition inherits the proof. You do not write a separate law
declaration for the composed arrow.

```handl
-- serialize and deserialize both have verified roundtrip laws
migrate = deserialize >>> serialize
-- migrate inherits the lossless proof by composition
```

Laws compose because laws _are_ arrow compositions. No separate proof
step is needed.

## See also

- [Laws, Bundles, and Handlers (reference)](../reference/laws-bundles-handlers.md)
  — exact syntax forms, the composition table, resolution methods.
- [Why the Trait Layer Is Three Features, Not a Keyword](../explanations/laws-bundles-handlers.md)
  — why the layer is decoupled, why handlers not implicit search, the
  static/dynamic split.
- [ADR-0076 — Decoupled Trait Layer](../../../../project/adrs/0076-decoupled-trait-layer.md)
  — the design decision.
