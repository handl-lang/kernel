# Phase 3 Experimental Results

## Status: ✅ Challenge #7 & #8 COMPLETED

Date: 2026-08-31
Current Phase: 3 (Language Protocol & Generic Tooling — Challenges #7 & #8) — **COMPLETE**
Focus: First-class `Language` protocol of arrows; generic language-agnostic
tooling (pretty-printer, error reporter, optimizer) that runs unchanged over
any language instance

---

## Experiments Completed

### ✅ Experiment 9: First-class Language Protocol (CHALLENGE #7)

**Goal:** Show that a programming language can be modelled as a protocol
whose every operation (parse, eval, format, typecheck) is an _arrow_, and
that — because arrows compose — generic tools can be built as arrow
pipelines working over ANY language instance.

**Model:** A `Language` is a record of arrows, reusing the freer-arrow +
handler machinery from Phase 2:

```rust
pub struct Language {
    pub name:      &'static str,
    pub parse:     Rc<dyn Fn(Value) -> Comp + 'static>,   // Text  ~> AST
    pub eval:      Rc<dyn Fn(Value) -> Comp + 'static>,   // (AST, Env) ~> Value
    pub format:    Rc<dyn Fn(Value) -> Comp + 'static>,   // AST   ~> Text
    pub typecheck: Rc<dyn Fn(Value) -> Comp + 'static>,   // AST   ~> Type
    pub lit:       Rc<dyn Fn(Value) -> Comp + 'static>,   // Value ~> AST
}
```

ASTs are tagged `Value`s (`Product(Str tag, List args)`), so they are
first-class data that arrows can inspect and rebuild. Errors (parse failure,
unbound variables, type mismatches) are raised with the `Throw` operation
and caught with `handle_exception` — no new effect primitive.

**Two language instances implemented:**

1. **Arithmetic** — `Int n | Var x | Add a b | Mul a b`
   - Surface syntax: `(+ 1 (* 2 x))`, `42`, `x`
   - Types: every well-formed expression has type `Int`
2. **Boolean / Logic** — `Bool b | Var x | And a b | Or a b | Not a`
   - Surface syntax: `(and true (not p))`, `true`, `p`
   - Types: every well-formed expression has type `Bool`

Each instance supplies its own `parse`/`eval`/`format`/`typecheck`/`lit`
arrows, sharing a common s-expression tokenizer.

### ✅ Experiment 10: Generic Language-Agnostic Tooling (CHALLENGE #8)

**Goal:** Build generic tools that work over ANY `Language` instance,
parameterized only by the `Language` record — not hardcoded to one language.

**Three generic tools implemented:**

1. **Generic pretty-printer** — `pretty_print : &Language -> AST -> Text`
   - Uses only the language's `format` arrow.
2. **Generic error reporter** — `report_error : &Language -> AST -> Env -> String`
   - Runs `typecheck` then `eval` under `handle_exception`, formatting a
     human-readable message. Catches both type and runtime errors.
3. **Generic optimizer (constant folding)** — `optimize : &Language -> AST -> AST`
   - Recursively optimizes children, then attempts `eval` with an empty
     environment; on success replaces the node with its literal (via `lit`),
     otherwise keeps the node with optimized children. Uses only the
     language's `eval` and `lit` arrows plus the generic tagged-AST shape.

**The crucial proof:** the SAME tool code runs unchanged against both
language instances. Only the `Language` parameter differs.

**Test Results:**

```
Language instance 1: Arithmetic (6 tests):
✅ parse "(+ 1 2)"                      = Add(Int 1, Int 2)
✅ eval Add(Int 2, Int 3)               = 5
✅ eval Add(Var x, Int 3) with x=7      = 10
✅ format Add(Int 1, Mul(Int 2, Var x)) = "(+ 1 (* 2 x))"
✅ typecheck Add(Int, Var)              = "Int"
✅ typecheck Add(Bool, Int)             = Left "type error: expected Int, got Bool"

Language instance 2: Boolean (6 tests):
✅ parse "(and true false)"             = And(Bool true, Bool false)
✅ eval And(Bool true, Bool false)      = false
✅ eval Not(Bool true)                  = false
✅ format Or(Var p, Not(Bool false))    = "(or p (not false))"
✅ typecheck And(Bool, Var)             = "Bool"
✅ typecheck And(Int, Bool)             = Left "type error: expected Bool, got Int"

Generic pretty-printer (2 tests):
✅ pretty_print on Arithmetic AST       = "(+ 1 2)"
✅ pretty_print on Boolean AST          = "(and true false)"

Generic error reporter (3 tests):
✅ report_error on unbound Arithmetic var  = "[Arithmetic] Runtime error: unbound variable"
✅ report_error on Arithmetic type error   = "[Arithmetic] Type error: ..."
✅ report_error on Boolean success         = "[Boolean] OK (Bool): true"

Generic optimizer / constant folding (3 tests):
✅ optimize Add(Int 2, Mul(Int 3, Int 4))      = Int 14
✅ optimize Add(Var x, Int 3)                  = unchanged (unbound x -> no fold)
✅ optimize And(Bool true, Not(Bool false))    = Bool true

Round-trip: parse >>> format >>> parse (2 tests):
✅ Arithmetic "(+ 1 (* 2 x))" round-trips to equivalent AST
✅ Boolean "(or true (not false))" round-trips to equivalent AST

Arrow composition (2 tests):
✅ parse >>> (pair env) >>> eval on "(+ 2 3)"  = 5
✅ parse >>> typecheck on "(+ 1 (* 2 3))"      = "Int"

Same tool, different languages (2 tests):
✅ pretty_print(arith, ...) = "(+ 1 2)"  ≠  pretty_print(bool, ...) = "(and true false)"
✅ optimize(arith, Add 4 5) = Int 9;     optimize(bool, Or false true) = Bool true

Total: 26/26 language protocol & tooling tests PASSED ✅
```

---

## Summary: Challenges #7 & #8 (Language Protocol & Generic Tooling)

### Claim Tested

> Can a language be a first-class protocol of arrows, such that generic
> tools compose over any language instance without hardcoding?

### What We've Shown

- ✅ A `Language` is a record of arrows (`parse`, `eval`, `format`,
  `typecheck`, `lit`); every operation is an arrow `Value ~> Comp`
- ✅ Two distinct language instances (Arithmetic, Boolean) implement the
  same protocol with their own arrows
- ✅ Three generic tools (pretty-printer, error reporter, optimizer) are
  written once and run unchanged over both instances — only the `Language`
  parameter differs
- ✅ Tools are arrow pipelines assembled from each language's own arrows
  (`parse >>> format >>> parse`, `parse >>> typecheck`, `arr (pair env)
  > > > eval`)
- ✅ Errors flow through the Phase 2 exception handler — no new effect
  primitive is needed for language tooling
- ✅ Round-trip `parse >>> format >>> parse` produces an equivalent AST,
  verifying that `format` and `parse` are inverses (an arrow identity)

### What This Means

**A compiler/tooling plugin interface is not a separate language feature.**
It emerges directly from arrow composition over a record of arrows. The
generic tools are _literally_ functions `&Language -> ...` that compose the
language's arrows with `>>>`; no type class, no reflection, no language
-specific branch is needed. This is the arrow-calculus counterpart of a
language server / IR toolkit, with composition as the only glue.

### Key Technical Achievements

- **First-class Language protocol:** a struct of `Rc<dyn Fn(Value) -> Comp>`
  arrows — languages are values that can be passed to tools
- **Tagged-Value ASTs:** ASTs are ordinary `Value`s, so generic tools can
  walk/rebuild them structurally without per-language code
- **`lit` arrow:** the inverse of `eval` on literals, enabling a fully
  generic constant-folding optimizer that re-embeds folded values
- **Composition as the tool interface:** `parse >>> format >>> parse`,
  `parse >>> typecheck`, `parse >>> (pair env) >>> eval` are all arrow
  pipelines — tools are pipelines, not special constructs

---

## Comparison: Generic Tooling With vs Without Arrows

| Aspect            | Without arrows (traditional)                                        | With arrows (this PoC)                                          |
| ----------------- | ------------------------------------------------------------------- | --------------------------------------------------------------- |
| Tool interface    | A type class / trait / interface per tool, implemented per language | A record of arrows; tools are `&Language -> ...` functions      |
| Tool composition  | Manual plumbing; each tool re-implements parse/eval glue            | `>>>` (`seq`) — tools are arrow pipelines                       |
| Adding a language | Implement every tool interface for the new language                 | Provide the 5 arrows; all tools work automatically              |
| Adding a tool     | New interface + per-language implementations                        | One `&Language -> ...` function; works on all languages         |
| Error handling    | Per-tool try/catch, language-specific error types                   | One `handle_exception` over the freer arrow; uniform `Either`   |
| Round-trip proof  | Ad-hoc per language                                                 | `parse >>> format >>> parse` is an arrow identity, checked once |
| Code reuse        | Shared via inheritance / generics + boilerplate                     | Shared via composition; zero per-language tool code             |

**Verdict:** Generic tooling without arrows requires a type class (or
equivalent) per tool, implemented afresh for each language, plus manual
plumbing to compose parse/eval/format. With arrows, the entire tooling
surface is _one composition operator_ over a record of arrows: the same
`pretty_print` / `report_error` / `optimize` source runs on every language,
and adding a language means supplying five arrows — nothing more.

---

## Cumulative Results (Phase 1 + Phase 2 + Phase 3)

| Challenge            | Question                                         | Result | Tests |
| -------------------- | ------------------------------------------------ | ------ | ----- |
| #1 Expressiveness    | Can arrows express basic functional patterns?    | ✅ YES | 3/3   |
| #2 Abstraction       | Higher-order patterns without lambda?            | ✅ YES | 10/10 |
| #3 Parametricity     | Generic programming without lambda?              | ✅ YES | 14/14 |
| #4 Typing            | Hindley-Milner inference on arrows?              | ✅ YES | 15/15 |
| #5 Recursion         | State machines replace recursive functions?      | ✅ YES | 2/2   |
| #6 Effects           | Handler-based effects replace monads?            | ✅ YES | 20/20 |
| #7 Language Protocol | First-class language as a protocol of arrows?    | ✅ YES | 12/12 |
| #8 Tooling           | Generic tools over any language via composition? | ✅ YES | 14/14 |

**Total: 90/90 tests passing** (44 Phase 1 + 20 Phase 2 + 26 Phase 3)

---

## Files Created/Updated

- `src/language_protocol_tests.rs` — 26-test language protocol + generic tooling suite
- `Cargo.toml` — added `language_protocol` binary
- `FORMALISM.md` — Language Protocol & Generic Tooling section
- `WORKING_NOTES.md` — Challenges #7 & #8 verdicts logged, decision section resolved
- `RESULTS_PHASE3.md` — this file

---

## Conclusion

**Phase 3 is complete.** A programming language is modelled as a first-class
record of arrows; generic tooling (pretty-printer, error reporter,
constant-folding optimizer) is just arrow composition over that record. The
same tool code runs unchanged on two distinct language instances, differing
only in the `Language` parameter. Errors flow through the Phase 2 exception
handler, and round-trip / parse-eval-typecheck pipelines are ordinary arrow
compositions. No monad, no type class, no language-specific branch — just
arrows and `>>>`.

**Cumulative thesis status:** Across all three phases, arrows (composition,
choice, feedback, operations + handlers) have proven sufficient for
expressiveness, abstraction, parametricity, Hindley–Milner typing, recursion,
effects & handlers, and now first-class language protocols with generic
tooling — 90/90 tests passing, zero warnings, no external dependencies.

---

**Date:** 2026-08-31
**Status:** Phase 3 COMPLETE ✅
**Next:** Optional deep dive into effect typing (row types / effect inference
for arrows) or larger language instances (statements, closures, a JSON data
language) to further stress the protocol.
