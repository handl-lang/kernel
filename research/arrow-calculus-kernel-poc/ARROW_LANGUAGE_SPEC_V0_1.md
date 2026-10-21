# Arrow Language Specification v0.1

## Status

Authoritative — v0.1 surface syntax per ADR-0074. This document is the
authoritative source for the v0.1 surface syntax; ADR-0074 is the decision of
record.

This specification defines the complete, self-contained v0.1 surface syntax of
the handl programming language. It is referenced by
[ADR-0074 — Arrow Surface Syntax v0.1 — Redesign](../../project/adrs/0074-arrow-syntax-v0_1-surface-redesign.md)
as "the authoritative source for the surface syntax." It encodes the two
corrections (destructuring renaming; `rec` as a recursive region), the
Addendum A.1–A.7 (while, for, do while, `??`, `?.`, spread, multi-way `if`), and
all seventeen Implementation Decisions (ID.1–ID.17) from that ADR.

The surface syntax denotes the six-combinator kernel from
[ADR-0052 — Arrow Calculus Kernel](../../project/adrs/0052-arrow-calculus-kernel.md)
(`arr` / `>>>` / `first` / `choice` / `loop` / `app`). The typing machinery is
delegated to
[ADR-0054 — Generic Typecheck Engine](../../project/adrs/0054-generic-typecheck-engine.md);
the trait system to
[ADR-0075 — Traits as Arrow Signatures](../../project/adrs/0075-traits-as-arrow-signatures.md);
the module model to
[ADR-0069 — Files Are Arrows](../../project/adrs/0069-arrow-native-modules.md).

---

## 1. Overview and Design Principles

The handl language is **arrow-native**: the fundamental unit of computation is
an _arrow_ `A ~> B`, not a function. The surface syntax is a human-facing
notation for the arrow calculus kernel (ADR-0052). The design principles,
accepted unchanged from the v0.1 draft (per ADR-0074), are:

1. **Arrow-native.** Everything is an arrow. There are no functions as a
   separate foundational category; functions are the degenerate pure case of
   arrows. The kernel is `arr` / `>>>` / `first` / `choice` / `loop` / `app`
   (ADR-0052).
2. **Statically typed.** Every arrow has a type `A ~> B`; the type system
   rejects ill-typed graphs at compile time.
3. **Type-inferred.** Types are inferred from wiring; explicit annotations are
   optional. Hindley–Milner-style inference over arrow graphs, extended with
   row variables (ADR-0054, ID.7).
4. **Expression-oriented.** Every construct produces a value (a wire). There
   are no statements; a file is an expression.
5. **Compositional.** Programs are built by composing arrows with `>>>`,
   `***`, `&&&`, `|||`. Composition is the primary structuring mechanism.
6. **Dataflow-oriented.** A program is a graph of named wires; dependencies
   between wires determine evaluation order.
7. **Structurally typed by default.** Records and positional structures are
   typed by their shape, not by a nominal declaration. Row polymorphism
   (OCaml-style) allows a record with extra fields to unify with a narrower
   constraint (ID.7, ADR-0054).
8. **Immutable values and wires.** Wires are bound once; "mutation" is
   re-construction (e.g. spread, §11). Shadowing inside `rec` regions creates a
   new wire per iteration, not an in-place update.
9. **Parallelism inferred from independent branches.** Independent wires in a
   graph block may run concurrently; the dependency graph is the schedule
   (ADR-0072).
10. **Explicit control-flow exits via `return`.** A `return` terminates a path
    early. Its scope is the innermost enclosing `~>` (ID.14).
11. **Minimal syntax.** Optional punctuation (semicolons, commas) keeps common
    code compact. The contextual `{}` rule (ID.11) disambiguates records from
    blocks without distinct delimiters.

> **The graph is the type derivation.** The wiring of an arrow graph _is_ the
> evidence for its type and (where applicable) its proofs. This is the central
> idea inherited from the arrow calculus (ADR-0052) and the trait system
> (ADR-0075): the user writes the graph; type, proof, and trait conformance
> fall out of the wiring.

### 1.1 The minimal surface core

The **minimal surface core** is six forms:

```text
~>      (arrow construction)
>>>     (sequential composition)
***     (product)
&&&     (fan-out)
|||     (choice)
rec     (recursive region)
```

Everything else in the surface — `while`, `do while`, `for`, `??`, `?.`,
multi-way `if`, spread, arithmetic and comparison operators, and the operations
on literals — is **sugar** that desugars to the core: `rec`, `match` (which is
`|||`), `|||`, structural construction, and `arr`. None of the sugar introduces
a new kernel combinator (ADR-0074 Addendum). The desugaring summary is in §17.

The kernel itself has six combinators (`arr` / `>>>` / `first` / `choice` /
`loop` / `app`, ADR-0052). The surface core's `***` / `&&&` / `|||` are
themselves expressible over `first` / `choice`, but they are retained in the
surface core for readability and because their arrow _kind_ signatures (input
and output arity at the type level) are not yet fixed (ADR-0074 Negative;
follow-up task #3).

---

## 2. Lexical Structure

### 2.1 Identifiers

```text
identifier ::= identifier_start identifier_continue*
identifier_start  ::= [a-zA-Z_]
identifier_continue ::= [a-zA-Z0-9_']
```

Identifiers are case-sensitive. By convention, wire and arrow names are
lowercase (`parse`, `greet`, `add`). Type names referenced via the `type.`
namespace use the library's casing (e.g. `type.Str`, `type.Int`). Sum tags are
lowercase (§14).

### 2.2 Literals

Literals are **language-level** (ID.8): the parser produces them directly.
Operations _on_ literals are library arrows, not language primitives.

```text
literal ::= 'true' | 'false'           -- booleans (lowercase)
          | number                      -- 1, 1.5, 42
          | string                      -- "..."
```

- **Booleans** are `true` and `false` (lowercase). There is no `True`/`False`.
- **Numbers** are integer or floating-point: `1`, `1.5`, `42`. The numeric
  type is inferred or annotated via the `type.` namespace (`type.Int`,
  `type.Float`).
- **Strings** are double-quoted: `"hello"`, `"anonymous"`.

### 2.3 Comments

Line comments begin with `--` and run to the end of the line, as used
throughout the ADR-0074 examples:

```text
-- this is a comment
```

Block comments are not specified in v0.1; line comments suffice.

### 2.4 Operator characters

The operator characters are the multi-character symbols used by the
combinators and sugar:

```text
~>  >>>  ***  &&&  |||  ??  ?.  :  .  [ ] { } ( ) ,  =  |
```

plus the library operator characters `+ - * / == != < > <= >= && || !` which
the parser recognizes and desugars to arrow application (ID.8, §14).

### 2.5 Keywords

The following identifiers are reserved as keywords and may not be used as wire
or arrow names:

```text
if  else  match  rec  while  do  for  in  return
import  from  export  as  infer  type  trait  impl  law
```

`true`, `false`, and `_` are also reserved (`_` is the wildcard/placeholder,
§13). `export` and `as` are reserved globally in v0.1, like `import` and
`from`. All other identifiers are available for binding.

### 2.6 Reserved vs identifier

A keyword is reserved in all positions. An identifier that coincides with a
keyword is a parse error. The contextual keywords (`type`, `trait`, `impl`,
`law`, `infer`) are reserved only in their declaration positions; elsewhere
they would be identifiers, but to avoid ambiguity they are reserved globally
in v0.1.

---

## 3. Program Structure

### 3.1 Bindings

A program is a sequence of bindings, each of the form:

```text
name = expression
```

Optional semicolons may terminate a binding. Bindings are separated by
newlines (or semicolons). A binding introduces a named wire whose value is
the expression's result.

```text
parse = x ~> parseUser x
greet = { name: userName } ~> userName
```

### 3.2 A file is an arrow (ADR-0069)

Per ADR-0069, a `.hnl` file is an arrow:

- A **single-expression file** is that expression's arrow. Its type is the
  expression's arrow type.
- A **multi-name file** is an arrow that produces a **record** of named arrows.
  The bindings desugar to a record literal:

```text
-- file: collection.hnl
cons = ...
head = ...
sort = ...
```

desugars to:

```text
{ cons: ..., head: ..., sort: ... }
```

The file's arrow is `Unit ~> { cons: ..., head: ..., sort: ... }`. A file's
record may be filtered by `export` declarations (§3.4): `export` is a
visibility sugar layer that selects which fields of the record are exposed to
importers. A file with no `export` declarations exposes all named bindings
(the arrow-native default, ADR-0069 §6).

### 3.3 Imports (ID.16)

Per ADR-0069 and ID.16, the surface syntax for imports is:

```text
import name from "path"
import name1, name2 from "path"
import name as local from "path"
import "path" as alias
```

- `import name from "path"` — project `name` from the module's record arrow,
  bind as `name`.
- `import name1, name2 from "path"` — multi-name projection: one module,
  several fields.
- `import name as local from "path"` — project `name`, bind as `local`
  (rename).
- `import "path" as alias` — bind the module's whole record arrow to `alias`
  (enables `alias.field` via the existing field-access syntax, §11.2).

Each form **normalizes to a projection** of the module's record arrow:

```text
import sort from "collection/sort"
-- normalizes to:
sort = Project { field: "sort", record: ModuleRef { path: "collection/sort" } }

import sort, head from "collection"
-- normalizes to:
sort = Project { field: "sort", record: ModuleRef { path: "collection" } }
head = Project { field: "head", record: ModuleRef { path: "collection" } }

import sort as s from "collection/sort"
-- normalizes to:
s = Project { field: "sort", record: ModuleRef { path: "collection/sort" } }

import "collection" as coll
-- normalizes to:
coll = ModuleRef { path: "collection" }
```

For a single-expression file (no record), the import binds the file's arrow
directly (the projection of a single-expression module yields the module's
arrow itself). `Project` is `first` + `arr` (field projection); `ModuleRef`
is an opaque reference to a module's arrow, resolved by a normalization
strategy (§3.6). `App` (already a kernel combinator, ADR-0052) is used when an
imported name is applied.

Imports are top-level only and conventionally appear before bindings. Imports
are idempotent: repeated imports of the same name normalize to the same
projection. The normalization strategy (compile-time desugar, whole-program
flattening, or runtime loading) is an implementation choice (§3.6); the
semantics — import = projection — is fixed (ADR-0069 §5).

### 3.4 Exports — opt-in visibility sugar (ADR-0069 §6)

`export` is a **visibility sugar** layer on top of the record-arrow model. It
does not introduce a new runtime concept — it filters which fields of the
file's record arrow are exposed to importers. The surface syntax:

```text
export name                      -- mark an existing binding as public
export name = expr               -- binding + export in one
export name1, name2              -- mark several existing bindings public
export *                         -- all bindings in the file are public
export name from "path"          -- re-export: sugar for import + export
export * from "path"             -- re-export all of a module's public names
```

- `export name` — add `name` to the export set. `name` must be a binding in
  the file.
- `export name = expr` — introduce the binding `name = expr` and add `name` to
  the export set.
- `export name1, name2` — add several existing bindings to the export set.
- `export *` — all named bindings in the file are public.
- `export name from "path"` — re-export: sugar for `import name from "path"`
  followed by `export name`.
- `export * from "path"` — re-export all public names of `"path"`: import each
  as a `Project` binding and add all to the export set.

**Default (ADR-0069 §6):** if a file has no `export` declarations, all named
bindings are public. This preserves the arrow-native default and is backward
compatible. If a file has any `export` declaration, only the exported names
are visible to importers; non-exported bindings are private helpers.

`export` declarations are top-level and may appear anywhere among bindings.
They are not sequential statements — they collect a set of public names that
filters the file's record arrow. ADR-0069 §6 originally specified no `export`
in v0.1; `export` is now added as opt-in visibility sugar, which the ADR
explicitly permits as a future sugar addition.

### 3.5 Module Resolvers (ADR-0069 §5, ADR-0046)

Module resolution is a **host capability boundary** (ADR-0046). A
`ModuleResolver` trait resolves a module path to its source:

```text
ModuleResolver {
  resolve(path) -> ResolvedModule { path, source, origin }
}
```

Built-in resolvers:

- **`FileResolver`** — resolves paths against a filesystem root. The default
  for compiled builds and file-based projects.
- **`MemoryResolver`** — resolves paths against an in-memory map of path to
  source. Used for REPL, tests, and virtual environments.
- **`ChainResolver`** — tries resolvers in order, returning the first match.
  Composes `FileResolver` with `MemoryResolver`, for example.
- **`CachingResolver`** — wraps another resolver and caches resolved modules
  by path.

The resolver set is a host capability: a host may allow filesystem-only
resolution, deny HTTP/git resolution, etc. (ADR-0046). This keeps module
loading within the host's security boundary.

A `ModuleLoader` maintains two caches keyed by module path (ADR-0069 §4):

- **Graph cache**: `path → Scheme` — the parsed arrow graph, used for
  execution.
- **Contract cache**: `path → Contract` — the inferred contract, used for
  verification.

Both caches are populated when a module is first imported. Subsequent imports
return the cached entries. This enables **compositional inference**: each
module is inferred once, and its contract is reused by importers. The
inference engine does not re-trace imported arrows — it looks up their cached
contracts (ADR-0052, ADR-0070).

### 3.6 Normalization Strategies (ADR-0069 §5)

The semantic abstraction is fixed: **import = projection**. The realization
of that projection is an implementation choice. Three strategies, all valid
implementations of the same abstraction:

- **Strategy A (compile-time desugar, eager/static):** imports become
  `Project` / `ModuleRef` nodes at parse/normalize time. The IR is
  self-contained — no import syntax remains, only projections and `App`
  references. The default for compiled builds.
- **Strategy B (whole-program flattening, eager/inlined):** all `Project` /
  `App` / `ModuleRef` nodes resolve to inlined subgraphs, producing one
  self-contained graph with no indirection. Useful for whole-program
  inference and minimal artifacts.
- **Strategy C (runtime module loading, lazy/cached):** the resolver + loader
  parse, infer, and cache on first access. `ModuleRef` is resolved at
  runtime. The default for REPL and development workflows.

The three strategies are not mutually exclusive — a toolchain may use
Strategy A for production builds, Strategy B for whole-program inference, and
Strategy C for REPL/development. Inference is compositional under all three
via the contract cache (§3.5). The inference engine is agnostic to the
strategy: it sees `Project` nodes (A, C) or inlined subgraphs (B), and `App`
nodes (A, C) or resolved arrows (B).

---

## 4. Arrows

### 4.1 Arrow construction

An arrow is constructed with `~>`:

```text
arrow ::= pattern ~> expression
        | pattern ~> block
```

The left-hand side is an input pattern (a variable, a destructuring pattern,
or a positional structure); the right-hand side is the arrow body.

```text
greet = x ~> "hello, " ++ x
greet = { name: userName } ~> userName
add = [x, y] ~> x + y
```

### 4.2 Juxtaposition as application

Application is **juxtaposition**: writing an arrow next to its argument
applies it. There is no parenthesized call syntax for arrow application.

```text
parseUser input
add [a, b]
```

### 4.3 Inline and point-free arrows

Arrows may be written inline (binding the input) or point-free (omitting the
input, relying on the prefix rule):

```text
x ~> x * 2       -- inline
* 2               -- point-free (prefix operator = point-free arrow)
+ 1
>>> parse User    -- point-free, composed
.name             -- point-free field access
```

Point-free arrows use explicit `~>` when the input must be named; the prefix
forms (`* 2`, `+ 1`, `.name`) are shorthand for `x ~> x * 2`, `x ~> x + 1`,
`x ~> x.name` respectively (ID.8).

### 4.4 Multi-arg arrows — explicit positional structure, no currying (ID.2)

Arrows take **exactly one input**. Multi-input arrows use a positional
structure on the left of `~>`:

```text
add = [x, y] ~> x + y
```

Application requires the explicit positional structure — there is **no
auto-currying**:

```text
add [a, b]     -- correct
add a b        -- syntax error (ID.2)
```

### 4.5 Arrow types (ID.12)

Arrow types use `~>` at the type level, matching the term-level syntax:

```text
parse: Str ~> User
add: [Int, Int] ~> Int
```

Input and output are both type expressions (§13).

---

## 5. Composition Operators

### 5.1 The four combinators

```text
>>>     sequential composition
***     product (parallel)
&&&     fan-out (split to both)
|||     choice (branch)
```

- `f >>> g` feeds the output of `f` into `g`.
- `f *** g` runs `f` and `g` in parallel over the two components of a product
  input.
- `f &&& g` fans the input out to both `f` and `g`, producing a pair of results.
- `f ||| g` branches: on a `Left` input run `f`, on a `Right` input run `g`.

### 5.2 Categorical / arrow laws

The combinators satisfy the standard arrow laws (FORMALISM.md §Arrow Laws;
ADR-0052):

```text
-- Identity
arr id >>> f  ≡  f
f >>> arr id  ≡  f

-- Composition associativity
(f >>> g) >>> h  ≡  f >>> (g >>> h)

-- First homomorphism
first (arr f)  ≡  arr (λ(x,y). (f x, y))

-- Composition through first
first (f >>> g)  ≡  (first f) >>> (first g)

-- Exchange
first f >>> arr swap >>> first g  ≡  arr swap >>> first (f >>> g)
```

`***`, `&&&`, and `|||` inherit the corresponding laws from `first` and
`choice` (ADR-0052).

### 5.3 Arrow kind signatures — open

The arrow _kind_ signatures for `***` / `&&&` / `|||` — i.e. carrying their
input/output arity in the type system rather than only in the term grammar —
are **not yet fixed** (ADR-0074 Negative). The combinators carry their arity
in the term grammar for v0.1; type-level arity is follow-up task #3.

---

## 6. Operator Precedence and Associativity (ID.1)

The full precedence table, from highest to lowest (per ID.1):

```text
field access / indexing          (highest, left-assoc)
application (juxtaposition)      (left-assoc)
* / +  (arithmetic, library)     (left-assoc)
?? / ?.  (option sugar)          (left-assoc)
*** / &&&  (product / fan-out)   (left-assoc)
>>>  (sequential composition)    (left-assoc)
|||  (choice)                    (left-assoc)
~>  (arrow construction)         (right-assoc, lowest)
```

Explanatory notes (ID.1):

- **Application binds tighter than `>>>`:** `f x >>> g` parses as `(f x) >>> g`.
- **Arithmetic binds tighter than composition:** `x + 1 >>> f` parses as
  `(x + 1) >>> f`.
- **`~>` is the lowest-precedence operator and is right-associative:** the
  body of an arrow extends as far right as possible.

---

## 7. Blocks and Returns

### 7.1 Graph blocks

A **graph block** is a brace-delimited sequence of bindings:

```text
block ::= '{' binding (newline | ';' binding)* '}'
```

Each binding introduces a named wire. Dependencies between wires determine
order; independent wires may be evaluated concurrently (§16).

### 7.2 Final-binding returns

A **final binding** in a block both introduces a wire and returns its value.
The last binding in a block is the block's result:

```text
x ~> {
  a = f x
  b = g a
  b           -- the block returns b
}
```

A bare expression as the final element of a block is also the block's result.

### 7.3 Explicit `return`

An explicit `return` terminates a path early:

```text
x ~> {
  if x <= 0
    return 0
  next = x - 1
  next
}
```

### 7.4 `return` scope — innermost arrow only (ID.14)

`return` exits the **innermost enclosing `~>` arrow**. A `return` inside a
nested arrow exits that inner arrow, not any outer one. To exit an outer arrow
from inside a nested one, propagate the value explicitly via `match` / `|||`.

### 7.5 Contextual `{}` parsing (ID.11)

`{}` is parsed as a **block** when it immediately follows one of:

```text
~>          if cond       else        match val
while cond  for ...        rec
```

Otherwise `{}` is a **record**. In `match val { ... }`, the outer `{}` is the
match body (block-like, holding pattern arms); any `{}` inside a _pattern
position_ is a record pattern (§9, §10).

This is a contextual (position-based) rule, not a context-free one. It is
accepted because the alternative — distinct delimiters for records and blocks
— was rejected as syntactic noise in an expression-oriented language
(ADR-0074 Negative).

---

## 8. Conditionals

### 8.1 `if` / `else`

```text
if cond expr else expr
if cond { block } else { block }
```

Both single-statement and braced forms are permitted. `if` is an expression:
it produces a value. It is also usable for control flow (with `return`).

```text
sign = x ~> if x > 0
  "positive"
else
  "non-positive"
```

### 8.2 Multi-way `if` — flat guard chains (Addendum A.7)

For three or more conditional branches, multi-way `if` provides a flat form:

```text
if
  x > 0: "positive"
  x < 0: "negative"
  x == 0: "zero"
  _: "unknown"
```

Each arm is a condition expression followed by `:` and a result expression.
The `_` arm is the catch-all (else). This mirrors `match` syntax — same `:`
separator, same `_` wildcard — but each arm is a _guard condition_ rather than
a pattern. The `if` keyword (vs `match`) signals the difference.

For two branches, the existing `if`/`else` form is cleaner and remains
preferred:

```text
if x > 0
  "positive"
else
  "non-positive"
```

Multi-way `if` **desugars to nested `if`/`else`**:

```text
if
  c1: e1
  c2: e2
  _: e3

-- desugars to:
if c1
  e1
else if c2
  e2
else
  e3
```

**Exhaustiveness is required** (ID.13): the compiler requires a catch-all `_`
or proof that the conditions cover all cases, exactly as for `match`.

---

## 9. Pattern Matching

### 9.1 `match`

```text
match value {
  pattern: expr
  pattern: expr
  ...
}
```

The outer `{}` is the match body (block-like, per ID.11). Arms are
`pattern : expr`. Commas between arms are optional.

```text
classify = n ~> match n {
  0: "zero"
  _: "nonzero"
}
```

### 9.2 Patterns

```text
pattern ::= literal
          | identifier
          | '_'
          | positional_pattern
          | record_pattern
          | nested_pattern

positional_pattern ::= '[' pattern_element (','? pattern_element)* ']'
record_pattern     ::= '{' record_pattern_element (','? record_pattern_element)* '}'
```

Pattern kinds:

- **Literal** — matches a specific value (`0`, `"zero"`, `true`).
- **Variable** — binds the matched value to a local wire.
- **`_` wildcard** — matches anything, binds nothing.
- **Positional** — `[a, b]` matches a positional structure by position.
- **Record** — `{ name, age }` matches a record by field.
- **Nested** — patterns compose: `{ user: { name: userName } }`.

### 9.3 Exhaustiveness (ID.13)

The compiler checks exhaustiveness. A non-exhaustive `match` is a compile
error. A `_` catch-all (or proof that the listed patterns cover all cases) is
required.

---

## 10. Destructuring

### 10.1 Positional and record destructuring

```text
[first, second] = value
{ name, age } = user
```

Rest destructuring captures the tail:

```text
[a, ...remaining]
{ name, ...remaining }
```

Nested patterns compose:

```text
{ user: { name, age } } = record
```

Simultaneous assignment swaps wires:

```text
a, b = b, c
```

### 10.2 Correction 1 — Destructuring renaming

A pattern element may use `source: local` to bind a source field/position to a
**different local wire name** (ADR-0074 Correction 1).

For records:

```text
{ name: userName, age: userAge } = user
```

means: take the `name` field, bind it locally as `userName`; take the `age`
field, bind it locally as `userAge`.

In **arrow input position**:

```text
greet = { name: userName } ~> userName
```

is the arrow that selects `.name` and outputs it under the local wire
`userName`.

**Nested patterns compose:**

```text
{
  user: {
    name: userName
    age: userAge
  }
} ~> {
  userName
  userAge
}
```

For **positional structures** there is no source name to rename — the pattern
variable _is_ the local name:

```text
[first, second] = value
```

**Rest destructuring** already names the tail naturally, so renaming is not
needed there:

```text
[a, ...remaining]
{ name, ...remaining }
```

### 10.3 The `pattern_element` grammar

The grammar for a single pattern element (ADR-0074 Correction 1):

```text
pattern_element ::= source ':' local
                  | identifier
                  | '...' identifier
                  | literal
                  | nested_pattern
```

- `source : local` — bind source field/position `source` to local wire `local`.
- `identifier` — the single-identifier form: the identifier serves as **both
  source and local name** (the common case, preserved for brevity).
- `... identifier` — rest: capture the tail under `identifier`.
- `literal` — match a literal value (in `match` contexts).
- `nested_pattern` — a nested positional/record pattern.

This makes destructuring a first-class pattern feature: the source structure
and the local wire namespace are independent, and the programmer chooses
whether they coincide. Nonsense such as `1: x` outside match contexts is
forbidden (ADR-0074 Negative).

---

## 11. Records, Indexing, and Spread

### 11.1 Records

```text
{ name: "Luis", age: 30 }
```

Commas between fields are optional. Computed keys use bracket notation:

```text
{ [val]: x }
```

### 11.2 Indexing and field access

```text
obj[val]      -- indexing (dynamic key)
obj.field     -- field access (static key)
```

Field access and indexing are the highest-precedence operators (§6).

### 11.3 Spread — construction dual of rest destructuring (Addendum A.5)

Rest destructuring captures `...rest` on the binding side. Spread re-inserts
it on the construction side. They are duals; the round-trip is the immutable
record update pattern.

**Object spread:**

```text
{ ...a, b: 2 }
```

means: take all fields of `a`, then add/override `b: 2`. **Later keys win**
(same as TypeScript):

```text
{ ...a, b: 2 }   -- b: 2 wins if a has b
{ b: 2, ...a }   -- a's b wins if a has b
```

**Multiple spreads (merge):**

```text
{ ...a, ...b, c: 3 }
```

Union of fields; later spreads override earlier on conflicts. This is record
merge:

```text
merged = { ...defaults, ...overrides }
```

**Positional spread:**

```text
[...a, b]              -- append
[head, ...middle, last]  -- destructuring from both ends (already supported)
```

**Computed keys + spread:**

```text
{ ...a, [key]: value }
```

Spread first, then computed key overrides.

**The round-trip (immutable record update):**

```text
{ b, ...rest } = a          -- extract b, capture the rest
newA = { ...rest, b: 2 }    -- re-insert with updated b
```

This is how a field is "mutated" without mutation. The `...rest` captured on
the left is spread back on the right.

**Spread in arrow position:**

```text
withDefaults = input ~> {
  { ...defaults, ...input }
}

parseAndMerge = x ~> {
  parsed = parse x
  { ...defaults, ...parsed }
}
```

### 11.4 Spread typing

Spread is structural, as with everything else:

- `{ ...a, b: 2 }` has type "all fields of `a`, plus `b: Int`". If `a` already
  has `b`, the type is narrowed to `Int` (the override wins).
- `{ ...a, ...b }` has type "union of `a`'s and `b`'s fields, with `b`'s types
  winning on conflicts".
- `[...a, b]` has type "positional structure of `a`'s element type, plus `b`'s
  type".

The solver derives these from the spread operands' structural types — no new
type machinery, just structural unification with override semantics. The
override rule is **"last wins, structurally"** (ADR-0074 Negative): on a field
type conflict, the later operand's type is taken. This is a structural
override rule, not a subtyping rule.

### 11.5 What spread is and is not

Spread is a **construction form**, not control-flow sugar. It does **not**
desugar to `match` or `rec`; it is the direct counterpart to rest
destructuring, which is also a primitive pattern form. The kernel sees it as
an `arr` node that merges two structural values (ADR-0074 Addendum A.5).

---

## 12. Control Flow

The core control-flow forms are `if`, `match`, and `rec`. The Addendum adds
`while`, `do while`, `for`, `??`, and `?.` as sugar over `rec`, `match`, and
`|||`. None introduce new kernel combinators.

### 12.1 `rec` — recursive region (Correction 2)

`rec` **does not define a recursive arrow**. It introduces a **recursive
computation region** inside an arrow graph (ADR-0074 Correction 2). Bindings
inside the region may depend on other bindings in the same region, including
bindings textually defined later. The compiler constructs the corresponding
feedback graph and checks that the recursive structure is well-typed.

**Syntax:**

```text
rec {
  binding
  binding
  ...
}
```

The region evaluates to its last binding (or to an explicit `return`), like a
graph block.

**Minimal example:**

```text
loop = x ~> {
  rec {
    a = f b
    b = g a
  }
  a
}
```

Here `a` and `b` form a cyclic graph:

```text
      ┌──── f ← b
      │
      a
      │
      ↓
      g
      │
      └────→ b
```

**A practical feedback loop:**

```text
iterate = x ~> {
  rec {
    next = step current
    current = if done next
      next
      else step next
  }
  current
}
```

**The earlier `countdown` and `retry` examples, rewritten as arrows that
_contain_ a `rec` region (not as `rec`-declared arrows):**

```text
countdown = x ~> {
  rec {
    result = if x <= 0
      0
      else countdown (x - 1)
  }
  result
}
```

or, with the feedback made explicit:

```text
countdown = x ~> {
  rec {
    next = x - 1
    result = if x <= 0
      0
      else countdown next
  }
  result
}
```

```text
retry = request ~> {
  rec {
    result = send request
    exit = if result.ok
      result
      else if result.attempts >= 3
        err "failed"
        else retry result.next
  }
  exit
}
```

**Defining property:** `rec` describes a **graph with cycles**, not a
recursive function. This keeps `rec` consistent with the language's central
idea (ADR-0052) and with Paterson's `loop` combinator at the kernel level.

**Typing (ID.3):** `rec` regions follow Paterson's `loop` model. The region has
a state wire and an exit wire; the fixpoint is over the state. **Termination
is NOT checked at the type level** — it is a runtime/effect concern. The type
is the fixpoint of the state transition. No guard/`return` is required for
well-typedness. A `rec` without a well-typed fixpoint is a **compile error**,
not a runtime divergence. This is the same discipline the kernel applies to
`loop`; `rec` is the surface syntax for the same idea.

The legal-recursive-binding grammar is formalized around the Paterson model:

- Every binding inside a `rec` region is a wire in a cyclic subgraph.
- The compiler must be able to assign a well-typed fixpoint to the region.
- A region that admits no well-typed fixpoint is a compile error.

### 12.2 `while` — sugar over `rec` (Addendum A.1)

```text
while cond {
  body
}
```

desugars to a `rec` region with an implicit feedback wire: each iteration's
bindings feed back into the next; the loop exits when `cond` is false. The
result is the **last expression in the body, evaluated on the final iteration**
(ID.5). If the body never runs (condition false on entry), the result is a
type-appropriate default inferred by the solver.

A `while` without a block is also permitted:

```text
while cond
  body
```

**Example:**

```text
countdown = n ~> {
  while n > 0 {
    n = n - 1
  }
  n
}
```

**Conceptual graph:**

```text
n ──→ cond ──→ if ──┬──→ n' = n - 1 ──→ feedback
                    │
                    └──→ exit ──→ output
```

The `n = n - 1` inside the body is a new wire per iteration (shadowing), with
the feedback edge connecting each iteration's `n` to the next. This is exactly
what `rec` already does; `while` is the common case where there is one
condition and one body, with the feedback made implicit.

### 12.3 `for x in xs` — sugar over `rec` + destructuring (Addendum A.2)

```text
for x in xs {
  body
}
```

desugars to a `rec` region that splits head/tail, binds `x` to the head, runs
the body, and recurses on the tail. The result is a **collection of body
results** — i.e. it is `map`.

A **fold form** is provided with an explicit accumulator:

```text
for x in xs, acc = init {
  body
}
```

This produces the final `acc` — i.e. it is `fold`.

**Example (map):**

```text
doubled = xs ~> {
  for x in xs {
    x * 2
  }
}
```

**Example (fold):**

```text
sum = xs ~> {
  for x in xs, acc = 0 {
    acc + x
  }
}
```

**Graph for `for x in xs { f x }`:**

```text
xs ──→ split ──┬──→ x ──→ f x ──→ collect
               │
               └──→ rest ──→ feedback
                                │
                          (exit when empty)
```

The `for` form is the surface counterpart to the `loop`-over-stream pattern
described in ADR-0072 and the state-machine loop in ADR-0073.

**Iterator trait (ID.6):** `for x in xs` requires the input to satisfy the
`Iterator` trait defined in ADR-0075. The `for` form desugars to a `rec` region
that calls `Iterator.next` and dispatches via `match` / `|||`.

**Map vs fold ambiguity:** The bare form produces a collection (map); the
`acc = init` form produces a scalar (fold). The parser distinguishes these by
the presence of the accumulator binding, and the type checker enforces that
the fold form's body produces a value of the accumulator's type (ADR-0074
Negative).

### 12.4 `do { ... } while` — sugar over `rec`, body-first (Addendum A.6)

```text
do {
  body
} while cond
```

The body executes **before** the first condition check — the loop runs at
least once. After each body execution, `cond` is evaluated; if true, the body
runs again; if false, the loop exits with the last body result.

This is the post-test loop, complementing `while` (pre-test). It desugars to
a `rec` region that runs the body first, then branches on the condition:

```text
-- desugar of: do { body } while cond
rec {
  result = body
  continue = cond result
  -- if continue, feedback to re-run body
  -- if !continue, exit with result
}
```

**Examples:**

```text
-- read until empty line (always reads at least once)
readUntilEmpty = input ~> {
  do {
    line = readLine input
  } while line != ""
  line
}

-- prompt at least once
prompt = input ~> {
  do {
    answer = askUser input
  } while answer != "yes"
  answer
}
```

The result is the last expression in the body, evaluated on the final
iteration (same semantics as `while`, ID.5).

### 12.5 `??` — nullish coalescing (Addendum A.3)

```text
a ?? b
```

desugars to a `match` over the option sum:

```text
match a {
  some: value
  none: b
  _: b
}
```

If `a` is `some value`, the result is `value`. If `a` is `none` (or any
non-`some`), the result is `b`. This is a choice operation — it is `|||` over
`some | none` with the right branch being a constant arrow.

**Example:**

```text
name = user.name ?? "anonymous"
```

The option variant names are lowercase (`some` / `none`), matching the spec's
pattern style. `Option` is a **library type** in `lib-option` (ID.9), not a
language primitive.

### 12.6 `?.` — optional chaining (Addendum A.4)

```text
user?.address?.city
```

Each `?.field` is an arrow:

```text
?.field = x ~> match x {
  some: v ~> v.field
  none: none
}
```

And the chain composes via `>>>`:

```text
user?.address?.city  =  user ~> (?.address >>> ?.city)
```

Once a `?.` hits `none`, every subsequent `?.` returns `none` — composition
short-circuits through `none`. This is clean because `>>>` already propagates
`none` through the chain.

**Example with coalescing:**

```text
city = user?.address?.city ?? "unknown"
```

### 12.7 `return` inside loop bodies

Per ADR-0074 Negative, a `return` inside a `while` / `do while` / `for` body
**exits the enclosing arrow, not just the loop**. Because these forms desugar
to `rec` regions, the `return` must be specified in the desugaring to escape
the enclosing `~>`, consistent with ID.14 (`return` scope is innermost enclosing
`~>` only). The precise feedback-wire naming rule for `while` / `do while` /
`for` — "last binding of a given name feeds back to the next iteration" — and
its interaction with parallel independent wires in the body is to be written
down in the desugaring specification (follow-up task #4).

---

## 13. Types

### 13.1 Explicit annotations

```text
name: Type
parse: Str ~> User
add: [Int, Int] ~> Int
```

### 13.2 The `type.` namespace

Built-in types are referenced via the `type.` namespace:

```text
type.Str
type.Int
type.Float
type.Bool
```

### 13.3 Structural inference

Types are inferred from wiring. The inference engine is Hindley–Milner-style
over arrow graphs, extended with row variables (ADR-0054).

### 13.4 `infer` and `_`

`infer x` names the inferred type of `x`. `infer (parse _)` names the inferred
type of an arrow expression with a placeholder input.

`_` is the inferred/wildcard placeholder. It is allowed in exactly two
contexts (ID.10):

1. `infer (parse _)` — to extract a type from an arrow expression.
2. As a **wildcard pattern** in `match` and destructuring.

`_` is **NOT** allowed as a function argument: `f _` is a syntax error.
Point-free arrows use explicit `~>` instead (ID.10).

### 13.5 User-defined types — structural, no `type` keyword (ID.15)

Types are structural and inferred. `infer x` names the inferred type of `x`;
`infer (parse _)` names the inferred type of an arrow expression. There is
**no `type` declaration keyword** in v0.1. Sum types are library-provided
(`lib-option`, `lib-result`) or inferred from constructor usage. Nominal
tagging uses branded types (ADR-0055).

### 13.6 Structural subsumption — row polymorphism (ID.7)

Row polymorphism is OCaml-style. `{ name } ~> name` has type
`{ name: Str | r } ~> Str` where `r` is a row variable. A record with
additional fields unifies with the row constraint. The solver tracks extra
fields through composition. This requires row variables in the type system
(ADR-0054).

### 13.7 Consistency with the formalism

The type system is consistent with the arrow calculus formalism
(FORMALALISM.md §Type System): judgments `Γ ⊢ e : τ`, with inference rules for
`arr`, composition (`>>>`), `first`, `choice`, `loop`, and `app`. The surface
type `A ~> B` corresponds to the formalism's arrow type `τ ~> σ`. Product
(`***`) corresponds to `first`; sum/choice (`|||`) corresponds to `choice`;
`rec` corresponds to `loop`. The full typing machinery (row variables,
fixpoint checks for `rec`) is delegated to ADR-0054 and ADR-0070/ADR-0073.

---

## 14. Sum and Option Construction (ID.4, ID.8, ID.9)

### 14.1 Tags are lowercase, prefix-position (ID.4)

```text
some value
none
Left value
Right value
ok value
err value
```

Tags are lowercase and in **prefix position**: the tag name precedes its
payload. **Nullary tags** (`none`, `err` when no payload) are bare
identifiers. These are **library constructors**, not language primitives
(ID.4, ID.8).

### 14.2 No built-in operators — all library arrows (ID.8)

There are **no built-in operators** in the language. `+`, `-`, `*`, `/`, `==`,
`!=`, `<`, `>`, `<=`, `>=`, `&&`, `||`, `!` are all **library arrows**. The
parser recognizes operator characters and desugars operator expressions to
arrow application:

```text
x + y    desugars to   add [x, y]
```

Point-free operators follow the general prefix rule: any binary operator in
prefix position is a point-free arrow:

```text
* 2  =  x ~> x * 2
```

**Literals are language-level** (ID.8): `true` / `false` (booleans, lowercase),
numeric (`1`, `1.5`), string (`"..."`). Operations on literals are library
arrows.

### 14.3 `Option` and `Result` are library types (ID.9)

- `Option` (`some` / `none`) is in `lib-option`, a handl library.
- `Result` (`ok` / `err`) is in `lib-result`, a handl library.

Neither is a language primitive. `??` and `?.` are surface sugar that desugar
to `match` over the library's `Option` type. The spec examples using
`return error "msg"` should be read as `return (err "msg")` using
`lib-result`'s constructor (ID.9).

---

## 15. Traits (ID.17, ID.6)

Per ADR-0075, the trait system is fully specified in that ADR; this section is
a brief summary for completeness.

- **Trait inference is the primary mode** (annotation-free, laws recognized
  from wiring). The user writes a graph; the system recognizes which equational
  laws it satisfies.
- **Explicit `trait` / `impl` / `law` declarations are optional sugar** — names
  for law patterns the system already detects, used for documentation and
  explicit intent.
- **No global coherence** in v1.
- **Traits are structural, not nominal.**

The `Iterator` trait (ADR-0075) is **required** for `for x in xs` (ID.6). The
`for` form desugars to a `rec` region that calls `Iterator.next` and
dispatches via `match` / `|||`.

The `trait` / `impl` / `law` keywords (§2.5) are reserved for these optional
declarations. The full trait surface and semantics — including the open trait
catalog, `CutElim`-based law checking, and catalog storage — are the authority
of ADR-0075.

---

## 16. Graph Semantics

- **Bindings are named wires.** Each `name = expression` introduces a wire
  carrying the expression's value.
- **Dependencies determine order.** A wire that references another wire
  depends on it; the dependency graph is the evaluation schedule.
- **Independent nodes may run concurrently.** Wires with no dependency between
  them may be evaluated in parallel; parallelism is inferred from the graph
  (ADR-0072).
- **Control flow is graph structure.** `if` / `match` / `|||` route values
  through branches; `rec` introduces feedback edges. There is no implicit
  sequential execution of bindings — order is dataflow order.
- **Errors are early-exit paths.** An error propagates as an early exit through
  the graph (the `|||` / `choice` routing), consistent with the handler model
  (ADR-0052, Sanada).

---

## 17. Minimal Core and Desugaring Summary

### 17.1 The minimal surface core

```text
~>      >>>     ***     &&&     |||     rec
```

Everything else desugars to this core (and beneath it, to the six kernel
combinators of ADR-0052).

### 17.2 Desugaring summary table

The table below summarizes how each surface form expands into the kernel. The
full desugaring specification — including feedback-wire naming for `while` /
`do while` / `for`, the nested `if`/`else` expansion for multi-way `if`, and
the structural override rule for spread — is a separate follow-up document
(follow-up task #4, ADR-0074 Implementation). This table is a summary.

| Surface form                       | Desugars to                                                             | Notes                                                                  |
| ---------------------------------- | ----------------------------------------------------------------------- | ---------------------------------------------------------------------- |
| `x ~> e`                           | `arr (λx. ⟦e⟧)`                                                         | arrow construction; body lifted into `arr`                             |
| `f >>> g`                          | `Seq f g`                                                               | sequential composition (kernel)                                        |
| `f *** g`                          | `first f` over product                                                  | product (over `first`)                                                 |
| `f &&& g`                          | fan-out to pair                                                         | fan-out (over `first` + `arr`)                                         |
| `f \|\|\| g`                       | `Choice f g`                                                            | choice (kernel)                                                        |
| `rec { ... }`                      | `Loop` region                                                           | feedback; Paterson `loop` (ID.3)                                       |
| `if c e1 else e2`                  | `arr c >>> choice ⟦e1⟧ ⟦e2⟧`                                            | conditional routing                                                    |
| multi-way `if`                     | nested `if`/`else`                                                      | A.7; exhaustiveness required (ID.13)                                   |
| `match v { p: e }`                 | `arr v >>> choice ...`                                                  | pattern dispatch via `                                                 |     |     | `             |
| `while c { body }`                 | `rec` with implicit feedback                                            | A.1; result = last body expr (ID.5)                                    |
| `do { body } while c`              | `rec`, body-first                                                       | A.6; runs at least once                                                |
| `for x in xs { body }`             | `rec` + `Iterator.next` + `match`                                       | A.2; map semantics; requires Iterator (ID.6)                           |
| `for x in xs, acc = init { body }` | `rec` fold                                                              | A.2; fold semantics                                                    |
| `a ?? b`                           | `match a { some: value, none: b }`                                      | A.3; `                                                                 |     |     | ` over Option |
| `user?.field`                      | `>>> (?.field)` arrow                                                   | A.4; composes via `>>>`, short-circuits on `none`                      |
| `{ ...a, b: 2 }`                   | `arr` merge node                                                        | A.5; construction form, NOT control-flow sugar; last-wins structurally |
| `[...a, b]`                        | `arr` merge node                                                        | A.5; positional spread                                                 |
| `x + y`                            | `add [x, y]`                                                            | ID.8; library arrow                                                    |
| `* 2`                              | `x ~> x * 2`                                                            | ID.8; prefix operator = point-free arrow                               |
| `obj.field`                        | `arr (λobj. obj.field)`                                                 | field access arrow                                                     |
| `obj[val]`                         | `arr (λobj. obj[val])`                                                  | indexing arrow                                                         |
| `some value` / `none`              | library constructor                                                     | ID.4, ID.9; `lib-option`                                               |
| `ok value` / `err value`           | library constructor                                                     | ID.9; `lib-result`                                                     |
| `import name from "path"`          | `name = Project { field: "name", record: ModuleRef { path: "path" } }`  | ID.16, ADR-0069; normalization to projection                           |
| `import name1, name2 from "path"`  | one `Project` binding per name                                          | ID.16, ADR-0069; multi-name projection                                 |
| `import name as local from "path"` | `local = Project { field: "name", record: ModuleRef { path: "path" } }` | ID.16, ADR-0069; project + rename                                      |
| `import "path" as alias`           | `alias = ModuleRef { path: "path" }`                                    | ID.16, ADR-0069; bind whole record arrow                               |
| `export name`                      | `name` added to export set                                              | ADR-0069 §6; visibility sugar; `name` must be a binding                |
| `export name = expr`               | binding `name = expr` AND `name` in export set                          | ADR-0069 §6; binding + export                                          |
| `export *`                         | all bindings added to export set                                        | ADR-0069 §6; all-public via explicit declaration                       |
| `export name from "path"`          | `name = Project { ... }` AND `name` in export set                       | ADR-0069 §6; re-export (import + export)                               |
| `export * from "path"`             | import all public names as `Project` bindings, all in export set        | ADR-0069 §6; re-export all                                             |

### 17.3 What is unspecified in v0.1

The following are deliberately left to follow-up tasks (ADR-0074
Implementation) and are **not** part of the v0.1 surface contract:

- Arrow kind signatures for `***` / `&&&` / `|||` at the type level
  (follow-up #3).
- The precise desugaring specification for the Addendum forms, including
  feedback-wire naming for `while` / `do while` / `for` (follow-up #4).
- The precise typing rule for `infer` (especially `infer (parse _)`)
  (ADR-0074 Risks).
- Row variable support details in the solver (follow-up #5, ADR-0054).

The import normalization strategy (compile-time desugar, whole-program
flattening, or runtime loading) is now specified — see §3.6 and ADR-0069 §5.
Export visibility (§3.4) and pluggable module resolvers (§3.5) are now
specified as well. These were previously unspecified; they are now part of the
v0.1 surface contract.

Where this specification is silent and the referenced ADRs are silent, the
behavior is unspecified for v0.1 and must be resolved by the follow-up tasks
above before implementation.

---

## Related ADRs

- [ADR-0052 — Arrow Calculus Kernel](../../project/adrs/0052-arrow-calculus-kernel.md)
  — defines the kernel (`arr` / `>>>` / `first` / `choice` / `loop` / `app`)
  that this surface syntax denotes.
- [ADR-0053 — Generic Pratt Parser](../../project/adrs/0053-generic-pratt-parser.md)
  — parser infrastructure the v0.1 surface will be implemented against.
- [ADR-0054 — Generic Typecheck Engine](../../project/adrs/0054-generic-typecheck-engine.md)
  — typechecking infrastructure for the structural inference, row
  polymorphism, and `rec` fixpoint checks.
- [ADR-0055 — Branded Values](../../project/adrs/0055-branded-values.md) —
  nominal tagging for structural types, used when nominal identity is needed.
- [ADR-0069 — Files Are Arrows](../../project/adrs/0069-arrow-native-modules.md)
  — the module model, `import` syntax, `export` visibility sugar, and
  normalization strategies this surface syntax programs against.
- [ADR-0046 — Capability Discipline at the Language Level](../../project/adrs/0046-capability-discipline-at-the-language-level.md)
  — the capability boundary that module resolvers (§3.5) operate within.
- [ADR-0070 — Refinement Inference Scope](../../project/adrs/0070-refinement-inference-scope.md)
  — the fixpoint discipline that `rec` regions will rely on for typing.
- [ADR-0072 — Concurrent Arrow Calculus](../../project/adrs/0072-concurrent-arrow-calculus.md)
  — the loop-over-event-stream pattern that `for x in xs` is the surface
  counterpart of for collection iteration.
- [ADR-0073 — State Machine Invariants](../../project/adrs/0073-state-machine-invariants.md)
  — `loop`-based fixpoint discovery; `rec` is the surface counterpart, and
  `while` / `for` desugar to it.
- [ADR-0074 — Arrow Surface Syntax v0.1 — Redesign](../../project/adrs/0074-arrow-syntax-v0_1-surface-redesign.md)
  — the decision of record that accepts this specification as authoritative.
- [ADR-0075 — Traits as Arrow Signatures](../../project/adrs/0075-traits-as-arrow-signatures.md)
  — the trait system (`trait` / `impl` / `law`, trait inference, catalog).
  Required for `for x in xs` (Iterator trait) and in scope for v0.1.
