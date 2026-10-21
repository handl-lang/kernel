# TypeScript → Arrow v0.1 Comparison

A side-by-side mapping of common TypeScript patterns to the arrow language
v0.1 surface syntax (per ADR-0074). Use this to orient yourself if you're
coming from TypeScript.

The biggest mental shift: **TypeScript composes by nesting calls and chaining
methods; the arrow language composes by wiring `>>>` / `***` / `&&&` / `|||`
and naming intermediate wires in graph blocks.** Where TS writes `f(g(h(x)))`,
the arrow language writes `(h >>> g >>> f) x` — and the order reads
left-to-right in dataflow direction.

## Core abstractions

| Concept      | TypeScript                            | Arrow v0.1                                   |
| ------------ | ------------------------------------- | -------------------------------------------- |
| Function     | `function add(x, y) { return x + y }` | `add = [x, y] ~> x + y`                      |
| Arrow fn     | `(x) => x * 2`                        | `x ~> x * 2`                                 |
| Point-free   | not really possible                   | `double = * 2`                               |
| Identity     | `const id = (x) => x`                 | `id = x ~> x`                                |
| Pipeline     | `f(g(h(x)))` or `pipe(x, h, g, f)`    | `h >>> g >>> f` applied: `(h >>> g >>> f) x` |
| Method chain | `xs.filter(f).map(g).reduce(h)`       | `filter f >>> map g >>> reduce h`            |

## Types

| Concept             | TypeScript                                  | Arrow v0.1                                    |
| ------------------- | ------------------------------------------- | --------------------------------------------- |
| Type alias          | `type User = { name: string; age: number }` | `User = infer user` (or structural, inferred) |
| Interface           | `interface User { name: string }`           | structural — no nominal interface needed      |
| Explicit annotation | `const x: number = 5`                       | `x: type.Int = 5`                             |
| Arrow input typed   | `(x: string) => ...`                        | `text: type.Str ~> ...`                       |
| Union               | `type R = Ok \| Err`                        | `Ok \| Err` (sum/choice structure)            |
| Generics            | `function id<T>(x: T): T`                   | inferred — `id = x ~> x` derives it           |

## Destructuring

| Concept         | TypeScript                                | Arrow v0.1                           |
| --------------- | ----------------------------------------- | ------------------------------------ |
| Object          | `const { name, age } = user`              | `{ name, age } = user`               |
| **Rename**      | `const { name: userName } = user`         | `{ name: userName } = user`          |
| Array           | `const [a, b] = pair`                     | `[a, b] = pair`                      |
| Rest (array)    | `const [head, ...tail] = xs`              | `[head, ...tail] = xs`               |
| Rest (object)   | `const { id, ...rest } = obj`             | `{ id, ...rest } = obj`              |
| Nested          | `const { u: { name } } = { u: { name } }` | `{ user: { name } } = input`         |
| Nested + rename | `const { u: { name: n } } = x`            | `{ user: { name: n } } = x`          |
| Swap            | `[a, b] = [b, a]`                         | `a, b = b, a` (or `[a, b] = [b, a]`) |

## Control flow

| Concept             | TypeScript                                 | Arrow v0.1                                        |
| ------------------- | ------------------------------------------ | ------------------------------------------------- |
| if/else (stmt)      | `if (ok) save(x); else reject(x)`          | `if ok\n  save x\nelse\n  reject x`               |
| if/else (expr)      | `const r = ok ? f(x) : g(x)`               | `r = if ok\n  f x\nelse\n  g x`                   |
| Multi-stmt          | `if (ok) { log(x); save(x) }`              | `if ok {\n  log x\n  save x\n}`                   |
| Early return        | `if (!ok) return err("x")`                 | `if !ok\n  return error "x"`                      |
| switch              | `switch (x) { case 0: ...; default: ... }` | `match x {\n  0: ...\n  _: ...\n}`                |
| Multi-way if        | `if (a) ... else if (b) ... else ...`      | `if {\n  a: ...\n  b: ...\n  _: ...\n}`           |
| Discriminated union | `switch (r.kind) { case "ok": ... }`       | `match r {\n  ok: ...\n  error: ...\n  _: ...\n}` |
| while               | `while (n > 0) { n = n - 1 }`              | `while n > 0 {\n  n = n - 1\n}`                   |
| do while            | `do { n = step(n) } while (!done)`         | `do {\n  n = step n\n} while !done`               |
| for...of (map)      | `xs.map(x => x * 2)`                       | `for x in xs {\n  x * 2\n}`                       |
| for...of (fold)     | `xs.reduce((acc, x) => acc + x, 0)`        | `for x in xs, acc = 0 {\n  acc + x\n}`            |

`while`, `do while`, and `for` desugar to `rec` regions — they are surface
sugar over the graph-feedback primitive, not new calculus combinators.

## Recursion & loops

| Concept      | TypeScript                                   | Arrow v0.1                                                                                                     |
| ------------ | -------------------------------------------- | -------------------------------------------------------------------------------------------------------------- |
| Recursive fn | `function f(n) { return n<=0 ? 0 : f(n-1) }` | `countdown = x ~> {\n  rec {\n    result = if x <= 0\n      0\n      else countdown (x - 1)\n  }\n  result\n}` |
| while loop   | `while (!done) x = step(x)`                  | `while !done {\n  x = step x\n}`                                                                               |
| do while     | `do { x = step(x) } while (!done)`           | `do {\n  x = step x\n} while !done`                                                                            |
| for...of     | `for (const x of xs) ...`                    | `for x in xs { ... }` (map) or `for x in xs, acc = init { ... }` (fold)                                        |
| reduce       | `xs.reduce((acc, x) => f(acc, x), init)`     | `for x in xs, acc = init {\n  f acc x\n}`                                                                      |

## Async / errors

| Concept           | TypeScript                                                | Arrow v0.1                                                                   |
| ----------------- | --------------------------------------------------------- | ---------------------------------------------------------------------------- |
| Promise chain     | `fetch().then(parse).then(validate)`                      | `fetch >>> parse >>> validate`                                               |
| async/await       | `async function p() { const a = await f(); return g(a) }` | `p = _ ~> {\n  a = f _\n  g a\n}` (async is a handler concern, per ADR-0052) |
| try/catch         | `try { f() } catch (e) { h(e) }`                          | `f \|\|\| h` (choice), or `if !valid\n  return error "..."` early-exit       |
| Optional chaining | `user?.address?.city`                                     | `user?.address?.city` (desugars to `?.address >>> ?.city`)                   |
| Nullish coalesce  | `x ?? fallback`                                           | `x ?? fallback` (desugars to `match x { some: value, none: fallback }`)      |
| Combined          | `user?.address?.city ?? "unknown"`                        | `user?.address?.city ?? "unknown"`                                           |

`??` and `?.` desugar to `match` over the `some` / `none` option sum. They are
surface sugar, not new primitives.

## Data structures

| Concept           | TypeScript                                           | Arrow v0.1                                 |
| ----------------- | ---------------------------------------------------- | ------------------------------------------ |
| Object literal    | `{ name: "L", age: 30 }`                             | `{ name: "L", age: 30 }` (commas optional) |
| Array literal     | `[1, 2, 3]`                                          | `[1, 2, 3]`                                |
| Object spread     | `{ ...a, b: 2 }`                                     | `{ ...a, b: 2 }`                           |
| Object merge      | `{ ...defaults, ...overrides }`                      | `{ ...defaults, ...overrides }`            |
| Array spread      | `[...a, b]`                                          | `[...a, b]`                                |
| Immutable update  | `const { b, ...rest } = a; return { ...rest, b: 2 }` | `{ b, ...rest } = a; { ...rest, b: 2 }`    |
| Computed key      | `{ [k]: v }`                                         | `{ [k]: v }`                               |
| Index             | `xs[i]`                                              | `xs[i]`                                    |
| Field access      | `user.name`                                          | `user.name`                                |
| Field accessor fn | `(o) => o.name`                                      | `.name` (point-free)                       |

Spread is the construction dual of rest destructuring — the round-trip
(`{ b, ...rest } = a` then `{ ...rest, b: 2 }`) is the immutable record update
pattern.

## Parallel / fan-out

| Concept               | TypeScript                                      | Arrow v0.1                                  |
| --------------------- | ----------------------------------------------- | ------------------------------------------- |
| Two independent calls | `const a = f(x); const b = g(x); return [a, b]` | `x ~> {\n  a = f x\n  b = g x\n  [a, b]\n}` |
| Same input, two fns   | `Promise.all([f(x), g(x)])`                     | `f &&& g`                                   |
| Pair of fns on pair   | `[f(a), g(b)]`                                  | `f *** g`                                   |
| Branch on sum         | `r.kind === "ok" ? f(r) : g(r)`                 | `f \|\|\| g`                                |

## Module / file

| Concept           | TypeScript                  | Arrow v0.1                                   |
| ----------------- | --------------------------- | -------------------------------------------- |
| Export            | `export const f = ...`      | `f = ...` (file is the arrow; per ADR-0069)  |
| Import            | `import { f } from "./mod"` | normalizes to projection of the module-arrow |
| Multi-export file | `export { f, g }`           | file is an arrow producing `{ f, g }`        |

## Notable gaps / differences

- **No `class`.** Records + arrows replace classes; methods become arrows over
  the record. No implementation inheritance — use composition (`>>>`) or
  traits (ADR-0075) for shared behavior. Nominal identity via branded types
  (ADR-0055). Encapsulation via module projection (ADR-0069).
- **No `let`/`const` distinction.** All bindings are wires (immutable).
  Mutation is an explicit effect/resource, not a keyword.
- **No `async`/`await` keywords.** Asynchrony is a handler interpretation of
  the arrow (ADR-0052), not surface syntax. A `>>>` chain _is_ the await
  chain.
- **No `try`/`catch`.** Errors are early-exit graph paths
  (`return error ...`) or `|||` choice over `Result`-like sums.
- **No `for` loops with index.** Iteration is `for x in xs` (map/fold),
  `while`, or `do while` for general feedback loops.
- **Generics are inferred, not declared.** No `<T>` syntax; the solver
  derives types from the graph. Pin a type with a wire annotation
  (`x: type.Int ~> ...`).
- **Traits are in v0.1 (per ADR-0075).** Trait inference is primary
  (annotation-free, laws recognized from wiring). Explicit `trait`/`impl`/
  `law` declarations are optional sugar. No global coherence in v1.
  `for x in xs` requires the `Iterator` trait.

## Reference

- [ADR-0074 — Arrow Surface Syntax v0.1](../../project/adrs/0074-arrow-syntax-v0_1-surface-redesign.md)
- [ADR-0075 — Traits as Arrow Signatures](../../project/adrs/0075-traits-as-arrow-signatures.md)
- [ADR-0052 — Arrow Calculus Kernel](../../project/adrs/0052-arrow-calculus-kernel.md)
- [ADR-0069 — Files Are Arrows](../../project/adrs/0069-arrow-native-modules.md)
- [ADR-0055 — Tagged Values](../../project/adrs/0055-branded-values.md)
