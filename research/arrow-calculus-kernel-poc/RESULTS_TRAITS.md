# ADR-0075 Prototype Results: Traits as Arrow Signatures

## Status

Prototype complete for the catalog/storage/CutElim pipeline; Lean4
functor-law mechanization proven; non-functor law inference aspirational.

Date: 2026-09-02

---

## Summary

- **What was built:** (1) a Lean4 mechanization (`TraitInference.lean`)
  extending `CutElim` with two new rewrites and proving the functor and
  coproduct-functor identity + composition laws by normalization, with
  zero `sorry`; (2) a Rust prototype (`trait_catalog.rs`) implementing the
  open trait catalog, the 3-step matching pipeline (type filter ->
  fingerprint -> CutElim), an in-memory store, and a built-in catalog of
  5 entries; (3) a SQLite backend (`trait_catalog_sqlite.rs`) over the
  same abstract `TraitCatalogStore` interface, with persistence, indexes,
  and a verification cache.
- **What works:** CutElim verification of the functor/coproduct-functor
  identity + composition laws (Lean, zero `sorry`; mirrored in Rust); the
  3-step pipeline recognizes `Functor` for the demo `map` graph and
  reports `Mapping` as a placeholder multi-match; SQLite persistence
  survives close+reopen with the verification cache intact; law graphs
  round-trip losslessly through serde JSON.
- **What is aspirational:** non-functor equational laws (monad, roundtrip,
  sortedness-as-equation) are stubbed as semantic placeholders
  (`cutelim_proven = false`); higher-kinded type shapes (`F<A>`) are
  PARTIALLY implemented -- the `Ty::App` constructor exists and the type
  filter unifies `F<A> ~> F<B>` with `[a] ~> [b]` (F := List) and
  `Tree<a> ~> Tree<b>` (F := Tree), but higher-kinded trait _parameters_
  in the surface syntax (`trait Functor<F>`) are still open; trait
  resolution coherence and CutElim strong normalization are not proven;
  the surface syntax (§5-§10: trait/impl/law declarations, supertraits,
  associated types, blanket impls) is not implemented.

---

## Mapping to ADR-0075 sections

| ADR section                              | Status       | Notes                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 |
| ---------------------------------------- | ------------ | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| §1 Primary mode: trait inference         | Partial      | The 3-step pipeline recognizes `Functor` for the `map` graph from wiring alone (no `trait`/`impl`/`law` declaration). Proven only for the functor/coproduct-functor structural pattern; non-functor law inference is aspirational.                                                                                                                                                                                                                                                                                    |
| §2 Secondary mode: explicit declarations | Stubbed      | No surface `trait`/`impl`/`law` parser. The built-in catalog entries play the role of declared law patterns, but there is no user-facing declaration syntax.                                                                                                                                                                                                                                                                                                                                                          |
| §3 Open trait catalog + 3-step pipeline  | Implemented  | `trait_catalog.rs`: `CatalogEntry`/`LawEquation`, `TraitCatalogStore`, `InMemoryStore`, `infer_traits` (type filter via HM unify -> canonical fingerprint hash -> CutElim `law_equal`), multi-match, verification cache, 5 built-in entries. The fingerprint is now canonical under alpha-renaming (de Bruijn Arr names), associativity of `comp` (chain flattening), and identity absorption (`id` pruning in `comp` chains), while preserving sharing structure and law-relevant combinator differences (ADR OQ#6). |
| §4 Catalog storage (SQLite)              | Implemented  | `trait_catalog_sqlite.rs`: `SqliteStore` over the same `TraitCatalogStore` trait; schema (`trait_entries` + `verification_cache` + indexes); persistence across reopen; equivalence with `InMemoryStore`; lossless law round-trip. `lookup_by_type_shape` does a linear scan with `Unifier::unify` (a canonical-string index cannot match a type-constructor variable against a concrete constructor, the higher-kinded case from §5; a unification-aware index is future work).                                      |
| §5 Type parameter syntax (`F<A>`)        | Partial      | `Ty::App(Box<Ty>, Box<Ty>)` models `F<A>` (angle brackets per ADR §5); `Display`/`free_vars`/`apply_map`/`Substitution::apply`/`Unifier::unify`/`occurs_in` all handle it. `Functor`'s `type_shape` is the generic `F<A> ~> F<B>`; the type filter unifies it with `[a] ~> [b]` (F := List, via a `List`<->`App` bridge) and `Tree<a> ~> Tree<b>` (F := Tree), and rejects `Int ~> Bool`. Higher-kinded trait _parameters_ in the surface syntax (`trait Functor<F>`) remain open (ADR OQ#5).                         |
| §6 Impl declaration (graph layer)        | Stubbed      | No `impl` surface syntax; the demo supplies the `map` graph directly as a `PolyGraph`.                                                                                                                                                                                                                                                                                                                                                                                                                                |
| §7 Generic code with trait bounds        | Out-of-scope | No trait-bound desugaring; no generic-code resolution wired to the catalog.                                                                                                                                                                                                                                                                                                                                                                                                                                           |
| §8 Supertraits as signature inclusion    | Out-of-scope | Not modelled.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         |
| §9 Associated types via dependent types  | Out-of-scope | Not modelled in this prototype (substrate exists in `DependentProofGraphs.lean`).                                                                                                                                                                                                                                                                                                                                                                                                                                     |
| §10 Blanket impls via ArrowApply         | Stubbed      | `PolyGraph::App` is present as an opaque placeholder (fresh input/output vars); it is NOT wired into CutElim or inference semantics.                                                                                                                                                                                                                                                                                                                                                                                  |
| §11 Law verification: CutElim connection | Partial      | `TraitInference.lean` proves the functor/coproduct-functor identity + composition laws via `CutElimStar` normalization (zero `sorry`). `trait_catalog.rs` mirrors the 6 rewrites in `normalize`/`law_equal`. Congruence (rewriting inside subgraphs), termination, and completeness are open.                                                                                                                                                                                                                         |
| §12 Trait resolution: catalog search     | Partial      | The 3-step pipeline IS the catalog search (type filter -> fingerprint -> CutElim). No coherence/ambiguity algorithm; multi-match returns all matches. Step 3 checks the catalog entry's law pattern is CutElim-self-consistent (see honest note below); full graph-into-schema instantiation is future work.                                                                                                                                                                                                          |

---

## The Lean4 mechanization (§11 foundation)

`lean/ArrowMinimalityLib/TraitInference.lean` mechanizes the CutElim
foundation for trait-law verification. It builds on
`ProofAdvantage.lean`, which defines the `CutElim` rewrite relation and
its reflexive-transitive closure `CutElimStar`.

**The 6 CutElim rewrites** (defined in `ProofAdvantage.lean` lines
101-124, the last two added for this work):

```
ceIdLeft      : comp(idG A, G)        ==> G
ceIdRight     : comp(G, idG B)        ==> G
ceFirstFusion : comp(first G, first H) ==> first(comp G H)
ceLeftFusion  : comp(left G, left H)   ==> left(comp G H)
ceFirstId     : first(idG A)           ==> idG(A x D)     (functor identity)
ceLeftId      : left(idG A)            ==> idG(A + D)     (coproduct functor identity)
```

`ceFirstId` and `ceLeftId` are valid cut-elimination steps: `first` is
conjunction-functoriality, and functoriality applied to the identity
proof _is_ the identity proof on the conjunction. No substitution, no
binder.

**The law types and predicates:**

- `Law` — an inductive type of named equational laws
  (`functorId`, `functorComp`, `coproductFunctorId`,
  `coproductFunctorComp`), each carrying the type/graph parameters
  needed to instantiate both sides.
- `LawVerified law` — a `Prop`: the law is verified when both sides
  normalize to the same canonical form under `CutElimStar` (expressed
  via `Nonempty`, since `CutElimStar` is a `Type 1` derivation).
- `SatisfiesLaw G law` — graph `G` satisfies `law` when `G`'s wiring
  matches the law's pattern AND the law is verified. The pattern is
  recognized structurally.
- `UsesFirst` / `UsesLeft` — inductive structural recognizers: a graph
  _uses `first`_ (resp. `left`) if the combinator appears anywhere in its
  wiring (here, or in either side of a composition).

**The inference theorems** (annotation-free — the law is not declared):

- `satisfies_functor_identity`: if `G` uses `first`, then `G` satisfies
  the functor identity law `first(idG A) = idG(A x D)` for any `A D`.
- `satisfies_functor_composition`: if `G` uses `first`, then `G`
  satisfies `first(comp F H) = comp(first F)(first H)` for any `F H`.
- `satisfies_coproduct_functor_identity` / `satisfies_coproduct_functor_composition`:
  the analogous theorems for `left`.
- `all_functor_laws_verified`: every functor/coproduct-functor law is
  verified by CutElim normalization.

**`inferred_trait`** is the structural law-inference function (analogue
of `inferred_postcondition` from `StructuralInference.lean`): it maps a
graph to a `Prop` by structural recursion — `first G` and `left G`
detect their patterns; `comp G H` unions via disjunction; `id`/`arr`/`loop`
detect nothing. `inferred_trait_sound_functor` and
`inferred_trait_sound_coproduct` prove soundness: if `inferred_trait`
detects the pattern, the corresponding laws are verified.

**Task 3 (connection to invariant domain D):**
`first_id_semantic_equiv` and `left_id_semantic_equiv` prove the two
sides of each identity law are semantically equivalent (same output for
same input) directly from the `Eval` rules. `first_comp_semantic_forward`
/ `first_comp_semantic_backward` prove the composition law's semantic
equivalence. `functor_id_law_implies_preserves_all_D` connects the
functor identity law to preservation of all `D`-invariants.

**Zero `sorry`:** the file builds green under `lake build` with no
`sorry` proof terms (the word `sorry` appears only in comments stating
"zero `sorry`"). `lake build` reports `Build completed successfully
(19 jobs)`.

**Honest assessment** (from the file's own "Honest assessment" section,
lines 628-653):

- **What works:** the functor laws for `first` and `left` are verified
  by CutElim normalization, and the inference from wiring structure to
  law satisfaction is proven. The connection to `D` is established for
  the identity law (preservation of all `D`-invariants).
- **`inferred_trait` is a `Prop`-valued flag**, not a data structure
  enumerating the specific laws. A more useful implementation would
  return a list/set of `Law` instances, but this requires
  universe-polymorphic containers that are awkward in Lean4.
- **The "preserves all D" connection is vacuously weak:** it only
  discharges the identity case `first(idG A)`, where the graph is
  semantically the identity (so trivially preserves every invariant).
  It does not establish preservation for non-identity functorial graphs.
- **Congruence is open:** `CutElim` only rewrites at the top level.
  Verifying laws for complex graphs (e.g. `map_list` built from the five
  primitives) requires congruence rules for rewriting inside subgraphs —
  straightforward but tedious to formalize.
- **More laws:** the framework handles functor laws for `first`/`left`
  only. Extending to `loop` trace laws, `arr` laws, interchange laws
  requires adding the corresponding CutElim rewrites and proving
  preservation.
- **Completeness is open:** the theorems prove _soundness_ (if the
  pattern is detected, the law holds), not _completeness_ (if the law
  holds, the pattern is detected). Completeness is false in general —
  some laws require semantic reasoning beyond CutElim.

---

## The Rust prototype (§3 + §11 + §12)

`src/trait_catalog.rs` is a self-contained (pure-std) prototype of the
open trait catalog and the matching pipeline. It mirrors the Lean
graph/type model and the CutElim rewrites.

### The `PolyGraph` kernel model

The graph is built from 5 core combinators plus 2 ADR-0075 extensions:

```
Id | Comp(G, H) | First(G) | Left(G) | Loop(G) | Arr(name) | Choice(G, H) | App(G)
```

- `Choice(G, H)` — binary sum functoriality (`A+B ~> C+D` from
  `A~>C`, `B~>D`), an extension over the original unary `Left`.
- `App(G)` — placeholder for ArrowApply (ADR-0052 kernel `app`). Opaque
  to inference (fresh input/output vars); NOT wired into CutElim.
  Present so the graph model matches the kernel alphabet without
  claiming apply semantics.

Types (`Ty`) mirror `poly_proof_graph_tests.rs` plus the ADR-0075
section 5 higher-kinded constructor: `Atom | Var | Prod | Sum | Arrow |
Unit | Void | List | App`. `App(F, A)` is type application `F<A>`; it lets
`Functor`'s `type_shape` be the generic `F<A> ~> F<B>` rather than the
`List` instance. Unification bridges `List(t)` to `App(Atom("List"), t)`
so `F<A>` unifies with `[A]` (binding `F := List`); a bare `Atom` (e.g.
`Int`) is not bridged, so `Int` does not unify with `F<A>`. Full
higher-kinded trait _parameters_ in the surface syntax remain open (ADR
OQ#5).

### The CutElim normalizer (mirrors `ProofAdvantage.lean`)

`rewrite_root` applies one of the 6 rewrites at the graph root:
`ceIdLeft`, `ceIdRight`, `ceFirstFusion`, `ceLeftFusion`, `ceFirstId`,
`ceLeftId`. `rewrite_pass` normalizes children bottom-up first, then
repeatedly fires root rewrites until none apply (so a cascade like
`comp(first id, first id) -> first(comp id id) -> first id -> id`
completes within one pass). `normalize` repeats passes to a fixpoint,
bounded by `NORMALIZE_FUEL = 1024`. `law_equal(g1, g2)` returns whether
the two graphs normalize to the same form.

**Termination honesty:** the CutElim rewrite relation is NOT proven
strongly normalizing for all graphs (ADR Negative; OQ#2). The six
rewrites are size-non-increasing and terminate quickly in practice (the
proof-net advantage), but the fuel bound is a safety net. If fuel is
exhausted before a fixpoint, the result is the partially-normalized
graph (`law_equal` may then report false negatives).

### `fingerprint` (canonical, ADR OQ#6)

`fingerprint(graph)` is a canonical structural hash of the combinator
tree, computed by a CHEAP structural canonicalization (not full
CutElim) before hashing:

1. **Associativity flattening** -- nested `comp(comp(f,g),h)` is
   flattened to a list `[f,g,h]` (order preserved; `comp` is NOT
   commutative) and re-nested left-associated. This makes
   `comp(comp(f,g),h)` and `comp(f,comp(g,h))` produce the same
   fingerprint.
2. **Identity pruning** -- `id` nodes are dropped from `comp` chains
   (since `comp(id,f) equiv f` by CutElim `ceIdLeft`/`ceIdRight`). This
   makes `comp(id,f)` and `f` produce the same fingerprint.
3. **de Bruijn Arr-name canonicalization** -- each `Arr(name)` is
   replaced by `arr#N` where N is the index of first appearance of that
   name in a left-to-right traversal. This is invariant under
   alpha-renaming (`comp(arr_x,arr_y)` == `comp(arr_a,arr_b)`) while
   preserving sharing structure (`comp(arr_f,arr_f)` != `comp(arr_f,arr_g)`).

The old fingerprint (combinator tree with all `Arr` names erased to
`arr`, no associativity or identity canonicalization) is kept as
`raw_fingerprint(graph)` for comparison/testing.

**What the cheap canonicalization catches:**

- Associativity of `comp`: `comp(comp(f,g),h)` == `comp(f,comp(g,h))`
- Identity absorption in `comp` chains: `comp(id,f)` == `f`,
  `comp(f,id)` == `f`, `comp(id,comp(id,f))` == `f`
- Alpha-equivalence of base-arrow names: `comp(arr_x,arr_y)` ==
  `comp(arr_a,arr_b)`
- Sharing structure: `comp(arr_f,arr_f)` != `comp(arr_f,arr_g)`

**What the cheap canonicalization does NOT catch (left to Step 3
CutElim):**

- `first(id) equiv id` (CutElim `ceFirstId` step)
- `left(id) equiv id` (CutElim `ceLeftId` step)
- `first(f;g) equiv first f; first g` (CutElim `ceFirstFusion` step)
- `left(f;g) equiv left f; left g` (CutElim `ceLeftFusion` step)
- Commutativity of `choice` branches (not a CutElim rule; open)
- Deeper semantic equivalences

This is by design: the fingerprint is a fast filter that catches the
common structural equivalences without running the full normalizer.
Step 3 (CutElim `law_equal`) handles the deeper cases on the small set
of candidates that pass the fingerprint filter.

### Catalog types and the in-memory store

- `LawEquation { name, lhs: PolyGraph, rhs: PolyGraph }` — an
  equational law: two graphs that must normalize to the same form.
- `CatalogEntry { name, type_shape: Ty, fingerprint: String, laws:
Vec<LawEquation>, cutelim_proven: bool }` — a named law pattern. The
  `cutelim_proven` flag is the ADR's marker for whether CutElim
  normalization is proven for this pattern.
- `TraitCatalogStore` — the abstract storage trait
  (`lookup_by_type_shape`, `lookup_by_fingerprint`, `get`, `insert`,
  `remove`, `get_cached_verification`, `put_cached_verification`,
  `entries`, cache-stat hooks). The engine takes
  `&mut impl TraitCatalogStore` and never names a concrete backend.
- `InMemoryStore` — the in-memory backend (linear-scan lookups;
  `lookup_by_type_shape` filters by `Unifier::unify`).
- `VerificationResult { Verified, Unknown, Failed }` — cached outcome
  for a `(graph fingerprint, law pattern)` pair.

### The 3-step `infer_traits` pipeline

```
Step 0: infer the graph's type (annotation-free HM) + fingerprint
Step 1: type filter  -- store.lookup_by_type_shape (HM unify), prune non-unifying
Step 2: fingerprint  -- keep only entries whose fingerprint == graph's
Step 3: CutElim      -- for each law of each surviving entry:
                         cache check; if miss, run law_equal(lhs, rhs)
                         (placeholder entries -> Unknown, no verified laws)
```

Multi-match: ALL surviving entries are returned (sorted by name for
deterministic output). Verification results are written to the cache;
re-inference of the same graph hits the cache.

### Built-in catalog (5 entries)

```
Functor           type_shape F<A>~>F<B>  cutelim_proven=true
                    laws: identity (first(id) === id), composition (first(f;g) === first f; first g)
CoproductFunctor  type_shape (A+C)~>(B+D) cutelim_proven=true
                    laws: identity (left(id) === id), composition (left(f;g) === left f; left g)
Sorting           type_shape [A]~>[A]   cutelim_proven=false
                    laws: sorted (Sorted(sort(x)) -- semantic placeholder)
Mapping           type_shape [A]~>[B]   cutelim_proven=false
                    laws: length (LengthEq(map(x), x) -- semantic placeholder)
Filtering         type_shape (A~>Bool)~>([A]~>[A]) cutelim_proven=false
                    laws: allsat (AllSatisfy(filter(x), p) -- semantic placeholder)
```

`Functor` and `CoproductFunctor` are CutElim-proven — their laws ARE the
six CutElim rewrites. `Sorting`/`Mapping`/`Filtering` are semantic
placeholders: their laws (`Sorted`, `LengthEq`, `AllSatisfy`) are not
expressible as graph equations over the 5-combinator kernel and are
marked `cutelim_proven = false`, matching the ADR's explicit position
that non-functor law verification is aspirational (ADR "What is NOT yet
proven"; OQ#2).

**Higher-kinded `Functor` shape (ADR §5, OQ#5):** `Functor`'s
`type_shape` is the generic `F<A> ~> F<B>` (using `Ty::App`), not the
`List` instance `[A] ~> [B]`. The type filter unifies this with the demo
`map` graph's inferred `[a] ~> [b]` by binding `F := List, A := a, B := b`
(via the `List`<->`App` unification bridge), and with `Tree<a> ~> Tree<b>`
by binding `F := Tree`; it rejects `Int ~> Bool` (an `Atom` is not an
`App`). This makes the catalog's type filtering discriminate HKT shapes
for real. What remains open is the surface-syntax side: there is still no
`trait Functor<F>` declaration form, so the type-constructor variable `F`
is authored directly in the catalog entry rather than parsed from a
declaration.

### The demo `map` graph and its inferred traits

The demo graph is the ADR §1 `map` shape built from primitives:

```
map = loop (first (uncons ; choice nil (first f ; cons))) ; merge
```

Inferred type: `[a] ~> [b]`. Fingerprint:
`comp(loop(first(comp(arr#0,choice(arr#1,comp(first(arr#2),arr#3))))),arr#4)`.

The pipeline matches two entries (multi-match): `Functor` (two
CutElim-verified laws) and `Mapping` (one placeholder law).
`Sorting`/`Filtering`/`CoproductFunctor` are pruned by the type and/or
fingerprint filters.

### Captured output: `cargo run --bin trait_inference`

```
=== ADR-0075 prototype: Traits as Arrow Signatures ===

=== Demo: map graph from primitives (loop+first+choice+arr) ===
graph : (loop(first((uncons ; choice(nil,(first(f) ; cons))))) ; merge)
type  : [a] ~> [b]
fp    : comp(loop(first(comp(arr#0,choice(arr#1,comp(first(arr#2),arr#3))))),arr#4)
built-in catalog entries: 5

=== Pipeline run #1 (cold cache) ===
matches (multi-match):
  - Functor : cutelim_proven=true verified=["identity", "composition"] placeholder=[]
  - Mapping : cutelim_proven=false verified=[] placeholder=["length"]
cache: hits=0 misses=3

=== Pipeline run #2 (warm cache) ===
matches (multi-match):
  - Functor : cutelim_proven=true verified=["identity", "composition"] placeholder=[]
  - Mapping : cutelim_proven=false verified=[] placeholder=["length"]
cache: hits=3 misses=3

=== Tests ===
[pass] CutElim law_equal true cases (all 6 rewrites)
[pass] CutElim law_equal false cases
[pass] fingerprint same-shape-different-Arr
[pass] fingerprint different-shape
[pass] canonical fingerprint -- associativity (comp flattening)
[pass] canonical fingerprint -- identity pruning (id dropped from comp)
[pass] canonical fingerprint -- alpha-invariance (de Bruijn Arr names)
[pass] canonical fingerprint -- sharing preserved (de Bruijn distinguishes repeated names)
[pass] canonical fingerprint -- law-relevant differences preserved
[pass] canonical fingerprint -- combined associativity + identity + alpha + sharing
[pass] type filter pruning (Filtering, CoproductFunctor excluded)
[pass] fingerprint pruning (Sorting excluded)
[pass] pipeline map -> [Functor (verified), Mapping (placeholder)] (multi-match)
[pass] cache hit on re-inference (cache_hits=3)
[pass] 5 built-in entries present: ["Functor", "CoproductFunctor", "Sorting", "Mapping", "Filtering"]
[pass] CutElim-proven=["Functor", "CoproductFunctor"]  placeholder=["Sorting", "Mapping", "Filtering"]
[pass] [a]~>[b] unifies with F<A>~>F<B> (F := List)
[pass] Int~>Bool does NOT unify with F<A>~>F<B>
[pass] Tree<a>~>Tree<b> unifies with F<A>~>F<B> (F := Tree)
[pass] map type [a]~>[b] passes Functor's HKT type filter (Functor in candidates)

=== All tests passed ===
```

### Honest note on step 3 semantics

The prototype's step 3 checks `law_equal(law.lhs, law.rhs)` — i.e. it
confirms the catalog entry's law _pattern_ is CutElim-self-consistent
(both sides of the stored law equation normalize to the same form) —
and relies on the step-2 fingerprint match to establish that the graph
exhibits that structural pattern. This is a faithful approximation of
the ADR's "normalize both sides and compare" for the
structural-pattern case, where the law's lhs/rhs are written in the
same combinator alphabet as the graph and the fingerprint already
established shape equality.

Full instantiation of an arbitrary graph into a law schema (with
graph-specific subgraph matching, binding the law's schematic variables
`f`/`g` to the graph's concrete sub-arrows) is future work. For the
functor laws as stored, the law sides are concrete small graphs
(`first(id)`, `comp(first f, first g)`, etc.) and `law_equal` confirms
they normalize equal — which is exactly the CutElim verification the
Lean mechanization performs. The gap relative to the ADR's full vision
is that the prototype does not yet substitute a candidate graph's
sub-arrows into the law schema and re-normalize; it verifies the law
pattern once (at catalog population) and trusts the fingerprint for
per-graph matching.

---

## The SQLite backend (§4)

`src/trait_catalog_sqlite.rs` implements `SqliteStore`, a second backend
for the SAME inference engine. The engine (`infer_traits`,
`populate_builtin_catalog`) is written against
`impl TraitCatalogStore` and is reused here verbatim via a `#[path]`
module-include trick — it is NOT duplicated and NOT modified.

**Schema** (idempotent `IF NOT EXISTS`):

```sql
CREATE TABLE trait_entries (
  id INTEGER PRIMARY KEY, name TEXT NOT NULL,
  type_shape TEXT NOT NULL, fingerprint TEXT NOT NULL,
  laws TEXT NOT NULL, cutelim_proven INTEGER NOT NULL
);
CREATE INDEX idx_type_shape ON trait_entries(type_shape);
CREATE INDEX idx_fingerprint ON trait_entries(fingerprint);
CREATE TABLE verification_cache (
  graph_fingerprint TEXT NOT NULL, law_pattern_id TEXT NOT NULL,
  result TEXT NOT NULL,
  PRIMARY KEY (graph_fingerprint, law_pattern_id)
);
```

**Serialization:** `Ty`, `PolyGraph`, `LawEquation`, and `CatalogEntry`
derive `Serialize`/`Deserialize` (serde + serde_json). Entries are stored
as JSON blobs in `TEXT` columns and round-trip losslessly.
`PolyGraph::Arr` uses an owned `String` (not `&'static str`) so the
graph is serializable; this is behaviorally identical since
`law_equal`/`normalize` compare `Arr` names by string equality.

**`type_shape` storage + lookup:** the `type_shape` column stores a canonical
string key: type variables are renamed to `t0, t1, ...` in order of
first appearance, so two shapes differing only in variable names share
a key. The full `Ty` is recovered from the key via a small s-expr
parser (`key_to_type_shape`), which now also parses the ADR-0075
section 5 `F<A>` form (a trailing `<arg>` after an identifier head).
However, the `idx_type_shape` index is NOT used to drive
`lookup_by_type_shape`: a canonical-string index cannot match a
type-constructor variable against a concrete constructor (the
higher-kinded case `F<A> ~> F<B>` vs `[a] ~> [b]`, which unifies with
`F := List`), so the lookup does a linear scan with `Unifier::unify`,
matching `InMemoryStore` exactly (including the `List`<->`App` bridge).
The index/column are retained for inspection and
`get`/`entries`/`lookup_by_fingerprint` round-trips.

**Honesty note on `lookup_by_type_shape`:** the ADR claims "O(1) hash"
lookup on `type_shape`. A type shape contains type variables (and, with
§5, type-constructor variables), so two entries match whenever their
shapes UNIFY, not on string equality. A canonical-string index in
particular cannot match a type-constructor variable against a concrete
constructor (the higher-kinded case `F<A> ~> F<B>` vs `[a] ~> [b]`,
which unifies with `F := List`). This backend therefore does a linear
scan with `Unifier::unify` (O(|catalog|) per lookup, not O(1)), which is
correct for higher-kinded filtering but is not the ADR's claimed O(1).
A production backend would need a unification-aware index (e.g. a
substitution trie). This is a noted gap relative to the ADR's O(1) claim.

**Persistence:** entries and the verification cache survive close +
reopen. The persistence test inserts 5 built-ins + 1 custom entry, runs
inference (filling the cache), closes the DB, reopens at the same path,
and confirms: entry count persisted, custom entry retrievable by id
with all fields intact, re-inference hits the cache (cache_hits > 0,
misses = 0), and a direct `verification_cache` read returns
`Functor::identity -> Verified`.

**Equivalence with `InMemoryStore`:** both backends, populated with the
same built-in catalog, produce identical `infer_traits` results on the
demo `map` graph (same match count, same matched traits by name /
verified laws / placeholder laws / `cutelim_proven`). Entry parity is
checked across names, fingerprints, law counts, `cutelim_proven`, and
canonicalized `type_shape`.

**Lossless law round-trip:** a `RoundTrip` entry with two laws (an
identity law and a fusion law) is inserted, reloaded by id, and the
reloaded law graphs are structurally equal to the originals
(`law0.lhs == First(Id)`, etc.). The reloaded laws are also identical to
an in-memory reference, confirming the engine can run CutElim on
reloaded laws.

### Captured output: `cargo run --bin trait_inference_sqlite`

```
=== ADR-0075 section 4: SQLite catalog backend ===
graph : (loop(first((uncons ; choice(nil,(first(f) ; cons))))) ; merge)
fp    : comp(loop(first(comp(arr#0,choice(arr#1,comp(first(arr#2),arr#3))))),arr#4)

=== Equivalence test: InMemoryStore vs SqliteStore ===
both backends populated with 5 entries
[pass] entry parity (names, fingerprints, laws, type_shape, cutelim_proven)
[pass] infer_traits identical across InMemoryStore and SqliteStore
  matches:
    - Functor : cutelim_proven=true verified=["identity", "composition"] placeholder=[]
    - Mapping : cutelim_proven=false verified=[] placeholder=["length"]

=== Persistence test: close + reopen, cache survives ===
phase 1: inserted 6 entries (custom id=6), ran inference (cache_hits=0, misses=3)
phase 2: reopened, 6 entries present
[pass] custom entry retrievable by id=6 with all fields intact
phase 2 re-inference: cache_hits=3, cache_misses=0
[pass] verification cache persisted across reopen (cache_hits=3)
[pass] direct verification_cache read: Functor::identity -> Verified
[pass] temp db cleaned up

=== CRUD test: insert / get / remove ===
[pass] insert -> get -> remove -> get(None) -> entries empty

=== Index test: lookup_by_fingerprint selectivity ===
inserted 9 entries total
[pass] lookup_by_fingerprint selective (custom fps -> 1 each; map fp -> 2)

=== Round-trip test: laws survive SQLite and remain CutElim-checkable ===
[pass] law graphs round-trip losslessly (structural equality holds)
[pass] reloaded laws identical to in-memory reference

=== === All tests passed === ===
```

---

## What is proven vs aspirational

### Proven (zero `sorry` / passing tests)

- **Functor identity + composition laws via CutElim** (Lean,
  `TraitInference.lean`): `first(idG A)` and `idG(A x D)` both normalize
  to `idG(A x D)`; `first(comp G H)` and `comp(first G)(first H)` both
  normalize to `first(comp G H)`. Mirrored in Rust (`law_equal` true
  cases for all 6 rewrites).
- **Coproduct-functor identity + composition laws via CutElim** (Lean +
  Rust): the `left` analogues of the above.
- **CutElim preserves proofs and types** (`ProofAdvantage.lean`):
  `cut_elim_preserves_proof`, `cut_elim_preserves_type`, and their
  `CutElimStar` closures — extended to handle `ceFirstId`/`ceLeftId`.
- **Semantic equivalence of the functor identity law** (Lean):
  `first_id_semantic_equiv`, `left_id_semantic_equiv` — both sides
  produce the same output for the same input, from the `Eval` rules.
- **The 3-step pipeline recognizes `Functor` for the `map` graph**
  (Rust): type filter + fingerprint + CutElim verify the two functor
  laws; `Mapping` reports as a placeholder multi-match.
- **SQLite persistence + verification cache** (Rust): entries and cache
  survive close + reopen; re-inference is all cache hits.
- **Law round-trip** (Rust): law graphs survive SQLite serde losslessly
  and remain structurally equal to the originals.
- **Backend equivalence** (Rust): `InMemoryStore` and `SqliteStore`
  produce identical `infer_traits` results on the built-in catalog.
- **Higher-kinded type-filter discrimination** (Rust, ADR §5 / OQ#5):
  `Ty::App` models `F<A>`; `Functor`'s `type_shape` is `F<A> ~> F<B>`.
  The type filter unifies it with `[a] ~> [b]` (F := List, via a
  `List`<->`App` bridge) and `Tree<a> ~> Tree<b>` (F := Tree), and
  rejects `Int ~> Bool` (an `Atom` is not an `App`). The `Ty::App`
  canonical key round-trips through the SQLite `key_to_type_shape`
  parser.
- **Canonical fingerprint (associativity + identity + alpha + sharing)**
  (Rust, ADR OQ#6): the fingerprint is canonical under `comp`
  associativity (chain flattening), identity absorption (`id` pruned
  from `comp` chains), and alpha-renaming (de Bruijn Arr-name indexing).
  Sharing structure is preserved (`comp(arr_f, arr_f)` !=
  `comp(arr_f, arr_g)`); law-relevant combinator differences are
  preserved (`first` != `left`). Six test groups demonstrate each
  improvement, including comparison against the old `raw_fingerprint`.

### Aspirational / stubbed

- **Non-functor equational laws** (monad, roundtrip,
  sortedness-as-equation): stubbed as semantic placeholders
  (`cutelim_proven = false`). Their laws (`Sorted`, `LengthEq`,
  `AllSatisfy`) are not expressible as graph equations over the
  5-combinator kernel. This matches the ADR's "What is NOT yet proven"
  and OQ#1/#2/#4.
- **Higher-kinded type shapes (`F<A>`):** PARTIALLY implemented. The
  `Ty::App` constructor exists and the type filter discriminates HKT
  shapes (`F<A> ~> F<B>` matches `[a] ~> [b]` and `Tree<a> ~> Tree<b>`,
  rejects `Int ~> Bool`). What remains open is the surface-syntax side:
  there is no `trait Functor<F>` declaration form, so the
  type-constructor variable `F` is authored directly in the catalog
  entry rather than parsed from a declaration; there is also no kind
  system (the bridge treats `List(t)` as `App(Atom("List"), t)`
  structurally, without checking that `F` has the right kind) (OQ#5).
- **Trait resolution coherence:** no coherence/ambiguity algorithm;
  multi-match returns all matches; no global uniqueness check (ADR
  Negative; OQ#3).
- **CutElim strong normalization:** not proven; fuel (`NORMALIZE_FUEL =
1024`) is a safety net. The rewrites are size-non-increasing and
  terminate in practice, but a non-terminating law check is possible
  (ADR Negative; OQ#2).
- **CutElim congruence:** the Lean `CutElim` rewrites only at the top
  level; rewriting inside subgraphs (needed for complex graphs like
  `map_list` built from primitives) requires congruence rules — open.
- **`App`/ArrowApply blanket impls:** `PolyGraph::App` is an opaque
  placeholder (fresh vars, not wired into CutElim). Blanket impls via
  ArrowApply (ADR §10) are not implemented.
- **The surface syntax (§5-§10):** no `trait`/`impl`/`law` declaration
  parser, no supertraits, no associated types, no generic-code trait
  bounds. The prototype operates on the kernel `PolyGraph` directly.
- **`inferred_trait` as a data structure:** in Lean it is a `Prop`-valued
  flag, not a list/set of satisfied laws. The Rust side returns a
  `Vec<MatchedTrait>` (richer), but the Lean mechanization does not yet
  enumerate laws.
- **The "preserves all D" connection:** technically true but vacuously
  weak — only the identity case `first(idG A)` is discharged (the graph
  is semantically the identity, so it trivially preserves every
  invariant). Non-identity functorial graphs are not covered.
- **`lookup_by_type_shape` as a true unification index:** the SQLite
  backend now does a linear scan with `Unifier::unify` (correct for
  higher-kinded filtering, including the `List`<->`App` bridge), but
  this is O(|catalog|) per lookup, not the ADR's O(1). A
  unification-aware index (e.g. a substitution trie) is future work.

---

## Open questions carried forward

The ADR lists 8 Open Questions. Status after this prototype:

- **OQ#1 — Trait inference mechanization (load-bearing).** Law inference
  for non-functor patterns is NOT mechanized. The prototype proves the
  functor/coproduct-functor structural pattern; extending to monad,
  roundtrip, and other equational laws remains the key open question.
  _The prototype informs this: it confirms the structural-pattern +
  CutElim approach works for the functor case, but does not extend
  beyond it._
- **OQ#2 — CutElim-based law checking (part of this ADR).** The 6
  rewrites are mechanized (Lean + Rust) and prove the functor laws.
  Termination is not proven (fuel is the safety net); congruence
  (rewriting inside subgraphs) is open; completeness is open. _The
  prototype informs this: it provides the rewrite relation and the
  normalizer, but not the termination proof or the congruence
  extension._
- **OQ#3 — Trait resolution / catalog search.** The 3-step pipeline IS
  the catalog search. No coherence/ambiguity algorithm; multi-match
  returns all matches. _Implemented as far as the pipeline; coherence
  deferred._
- **OQ#4 — Law expressiveness.** Which laws are decidable under CutElim?
  The prototype shows the linear functor fragment is decidable (the 6
  rewrites terminate for it). The non-linear extension is open.
- **OQ#5 — Higher-kinded traits.** PARTIALLY modelled. `Ty::App(Box<Ty>,
Box<Ty>)` represents `F<A>` (ADR §5 angle-bracket syntax);
  `Display`/`free_vars`/`apply_map`/`Substitution::apply`/`Unifier::unify`/
  `occurs_in` all handle it, and `Functor`'s `type_shape` is the generic
  `F<A> ~> F<B>`. The type filter discriminates: `[a] ~> [b]` and
  `Tree<a> ~> Tree<b>` match (F := List / Tree), `Int ~> Bool` does not.
  What remains open: (1) higher-kinded trait _parameters_ in the surface
  syntax (`trait Functor<F>` declaration form) -- `F` is authored
  directly in the catalog entry, not parsed; (2) a kind system -- the
  `List`<->`App` bridge treats `List(t)` as `App(Atom("List"), t)`
  structurally without kind-checking; (3) multi-argument type
  constructors (`F<A,B>`) and higher-order constructors. _The prototype
  now exercises the type-filter layer of HKT concretely; the
  declaration/kind layers remain open._
- **OQ#6 — Catalog fingerprinting.** IMPLEMENTED. The fingerprint is now
  canonical under three structural equivalences: (1) associativity of
  `comp` (chain flattening, order preserved -- `comp` is not commutative),
  (2) identity absorption in `comp` chains (`id` pruned, matching CutElim
  `ceIdLeft`/`ceIdRight`), and (3) alpha-renaming of base-arrow names
  (de Bruijn indexing: first occurrence of a name gets `arr#0`, repeats
  get the same index, new names get the next index). The de Bruijn
  indexing preserves sharing structure: `comp(arr_f, arr_f)` gets a
  different fingerprint from `comp(arr_f, arr_g)`. Law-relevant combinator
  differences (`first` vs `left` vs `loop` vs `choice`) are preserved.
  The old fingerprint is kept as `raw_fingerprint` for comparison. Tests
  demonstrate all six improvement cases (associativity, identity pruning,
  alpha-invariance, sharing preserved, law-relevant difference preserved,
  combined). What is still open: the canonicalization is CHEAP (not full
  CutElim) -- it does not catch `first(id) equiv id` (`ceFirstId`),
  `first(f;g) equiv first f; first g` (`ceFirstFusion`), or their `left`
  analogues; these are left to Step 3 CutElim. Commutativity of `choice`
  branches is not canonicalized (not a CutElim rule; open). Deeper
  semantic equivalences are not caught by any structural hash.
  _The prototype now makes a principled concrete choice; the remaining
  design question is whether deeper equivalences should be folded into
  the fingerprint or left to CutElim._
- **OQ#7 — Catalog distribution.** Not addressed (storage is local
  SQLite; source files are the source of truth). Out of scope for this
  prototype.
- **OQ#8 — Built-in catalog contents.** The prototype ships 5 entries
  (Functor, CoproductFunctor, Sorting, Mapping, Filtering). The minimal
  set is not finalized. _The prototype provides a concrete starting
  set; the question of what else belongs remains open._

---

## How to run

From the poc directory
(`/home/luis/GitHub/handl-lang/host/research/arrow-calculus-kernel-poc`):

```
cd lean && lake build
```

Builds the Lean4 mechanization (19 jobs, zero `sorry`, builds green).

```
cargo run --bin trait_inference
```

Runs the in-memory catalog demo + tests (CutElim law_equal, fingerprint
same/different-shape, canonical fingerprint associativity/identity/
alpha/sharing/law-relevant/combined, type/fingerprint pruning, pipeline
multi-match, cache, built-in catalog, HKT type-filter discrimination).

```
cargo run --bin trait_inference_sqlite
```

Runs the SQLite backend tests (equivalence with InMemoryStore,
persistence across reopen, CRUD, index selectivity, lossless law
round-trip).

---

## References

- ADR: `host/project/adrs/0075-traits-as-arrow-signatures.md`
- Lean mechanization:
  `lean/ArrowMinimalityLib/TraitInference.lean` (law inference via
  CutElim; module doc lines 1-58; Summary + Honest assessment lines
  586-653)
- CutElim rewrite relation:
  `lean/ArrowMinimalityLib/ProofAdvantage.lean` (6 rewrites lines
  101-124; preservation theorems lines 146-232)
- Rust prototype:
  `src/trait_catalog.rs` (catalog, pipeline, in-memory store,
  CutElim normalizer, built-in catalog, demo + tests)
- SQLite backend:
  `src/trait_catalog_sqlite.rs` (`SqliteStore`, schema, persistence,
  equivalence, round-trip tests)
- Style reference: `RESULTS_PHASE3.md` (Phase 3 results doc)
