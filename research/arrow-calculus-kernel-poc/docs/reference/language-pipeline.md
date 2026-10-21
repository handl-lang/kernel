# Language Pipeline Reference

The end-to-end stages of the handl language, from source text to
execution. Each stage has a **data fragment** (what the programmer or
tool author provides) and an **engine** (the algorithm that interprets
it). This is the "language as data, engines as interpreters" split
(ADR-0044).

## Pipeline at a glance

| Stage       | Abstraction (data)            | Engine (algorithm)                | ADR           |
| ----------- | ----------------------------- | --------------------------------- | ------------- |
| lex         | tokens, lexer rules           | pattern-driven lexer              | ADR-0044      |
| parse       | grammar rows                  | data-driven Pratt parser          | ADR-0053      |
| desugar     | `DesugarRule` per grammar row | post-parse rewrite                | ADR-0074      |
| kernel IR   | arrow calculus                | — (the IR itself)                 | ADR-0052      |
| typecheck   | type rules                    | NbE typecheck engine              | ADR-0054      |
| refinement  | predicates                    | Z3 SMT inference                  | ADR-0068/0070 |
| traits      | arrow signatures + catalog    | graph matching + CutElim          | ADR-0075      |
| modules     | files as arrows               | projection normalisation          | ADR-0069      |
| eval        | eval scheme                   | tree-walk / bytecode / Cranelift  | ADR-0044      |
| concurrency | dependency graph              | deterministic dataflow scheduling | ADR-0072      |

## Lex — pattern-driven lexer

Token definitions and lexer rules are data; the engine is a generic
pattern matcher. No hardcoded token kinds.

**Token kinds:** literals (`Int`, `Float`, `Str`, `Ident`, `Wild`),
keywords (`if`, `else`, `match`, `rec`, `while`, `do`, `for`, `in`,
`return`, `import`, `export`, `from`, `as`, `infer`, `type`, `true`,
`false`), operators (`~>`, `>>>`, `***`, `&&&`, `|||`, `??`, `?.`, `=`,
`:`, `,`, `;`, `.`, `...`, `|`), delimiters, `Eof`.

Each token carries its own `lbp` (left-binding-power) for the Pratt
parser.

- PoC: `src/v0_1_surface.rs`, `lexer` module

## Parse — data-driven Pratt parser

Top-down operator precedence (Pratt's `nud`/`led`), table-driven from
`GrammarRow`s keyed by `(token_kind, position ∈ {Prefix, Infix})`.

Each row carries:

- binding-power pair `(lbp, rbp_right)` for infix rows; `prefix_rbp`
  for prefix rows
- `child_shape`: arity, optional `child_separators`, optional
  `DelimitedShape` for trailing delimited blocks
- `node_kind` (the AST node produced)
- optional `DesugarRule` (post-parse rewrite)

**One context-sensitive rule:** the contextual `{}` disambiguation
between record literals and blocks (ID.11). A `{` begins a block in
block-expecting contexts (after `~>`, `if` condition, `else`, `match`
scrutinee, `while`/`for`/`do` conditions); otherwise it begins a
record.

- ADR: ADR-0053
- Grammar: `ARROW_GRAMMAR_V0_1.md`
- PoC: `src/v0_1_surface.rs`, `parser` module

## Desugar — surface to kernel

The surface core is six forms:

```
~>      arrow construction
>>>     sequential composition
***     product
&&&     fan-out
|||     choice
rec     recursive region
```

Everything else — `while`, `for`, `do while`, `??`, `?.`, spread,
multi-way `if`, arithmetic/comparison operators — is sugar that
desugars to `rec`, `match` (which is `|||`), `|||`, structural
construction, and `arr`. No sugar introduces a new kernel combinator.

- Spec: `ARROW_LANGUAGE_SPEC_V0_1.md`
- Desugaring: `ARROW_DESUGARING_V0_1.md`

## Kernel IR — arrow calculus

Six combinators:

```
arr     first   >>>     choice   loop   app
```

| Combinator | Type                                   | Role                             |
| ---------- | -------------------------------------- | -------------------------------- |
| `arr`      | `(A → B) → (A ~> B)`                   | lift a pure function to an arrow |
| `>>>`      | `(A ~> B) → (B ~> C) → (A ~> C)`       | sequential composition           |
| `first`    | `(A ~> B) → ((A × C) ~> (B × C))`      | act on first component           |
| `choice`   | `(A ~> C) → (B ~> C) → ((A + B) ~> C)` | branch                           |
| `loop`     | `((A × C) ~> (B × C)) → (A ~> B)`      | feedback / recursion             |
| `app`      | `((A ~> B) × A) ~> B`                  | dynamic application              |

Functions are the degenerate pure case of arrows. There is no separate
`Function` category at the kernel.

The semantic foundation for effectful arrows is Sanada's _Algebraic
Effects and Handlers for Arrows_ — execution is one possible handler
interpretation, not a primitive property of arrows.

- ADR: ADR-0052
- PoC: `src/main.rs` (`Type::Arrow`, `ArrowValue`)

## Typecheck — NbE + Hindley–Milner + rows

The typechecker is a **normalisation-by-evaluation (NbE)** engine over
type-rule data. Inference is **Hindley–Milner extended with row
variables** (OCaml-style row polymorphism) over arrow graphs.

Types are represented as **tagged values** (ADR-0055) minted by the
host type registry — unforgeable, structural equality within the
registry.

Types are inferred from wiring; explicit annotations are optional.

- ADR: ADR-0054 (engine), ADR-0055 (tagged values)
- Rec typing: `ARROW_REC_TYPING_V0_1.md`

## Refinement — predicates as types

A type is an ordinary value (usually a function) that applied to a
value yields `type.bool`. `x: T = e` is sugar for `x = e; assert T(x)`.

Refinement types, type families, and dependent typing fall out without
a separate total/proof sublanguage. Refinement inference is backed by
Z3 (native Rust crate or pyz3 subprocess fallback).

- ADR: ADR-0068 (predicates), ADR-0070 (inference scope)
- PoC: `src/refinement_inference_tests.rs`

## Traits — graph-based interfaces

A trait is an arrow signature; an impl is a graph assignment. Trait
**inference** is the primary mode (the engine searches an open
catalog); explicit declarations are secondary sugar.

Law checking uses **cut-elimination (CutElim)** over proof graphs.
Storage is abstract with SQLite as the default local cache; the engine
is fully catalog-driven — zero hardcoded refinement contracts.

- ADR: ADR-0075
- PoC: `src/trait_catalog.rs`, `src/trait_catalog_sqlite.rs`

## Modules — files are arrows

A file is an arrow, not a sequence of statements. Imports normalise to
projections. No statement semantics, no first-class environment —
arrow graphs and inferred contracts are the two caches.

- ADR: ADR-0069

## Concurrency — deterministic dataflow

The calculus is deterministic dataflow: given an input, the graph
produces a unique output. Parallelism is inferred from independent
branches — the dependency graph _is_ the schedule. No new primitives
(`Parallel`, `Race`, `Channel`, `Lock`); concurrency is expressed
within the existing five combinators.

- ADR: ADR-0072

## Evaluation — dataflow graph reduction

The graph is the program; evaluation is dataflow-driven by the wiring,
not lambda-style reduction. Three backends:

| Backend   | What it does                              |
| --------- | ----------------------------------------- |
| tree-walk | interprets the arrow graph directly       |
| bytecode  | compiles schemes to bytecode, executes    |
| Cranelift | compiles schemes to native code, executes |

- PoC: `src/main.rs` (`Value`, reduction), `src/evaluation_tests.rs`

## The graph is the derivation

The central idea: the wiring of an arrow graph _is_ the evidence for
its type, its proof, its trait conformance, and its schedule. One
object carries all four readings.

| Reading           | Carried by                                                                                  |
| ----------------- | ------------------------------------------------------------------------------------------- |
| type              | wiring (HM + rows)                                                                          |
| proof             | wiring (`>>>` = cut, `first` = ∧-functoriality, `choice` = ∨-functoriality, `loop` = trace) |
| trait conformance | wiring (graph assignment to an arrow signature)                                             |
| schedule          | wiring (dependency graph)                                                                   |

See `docs/ARROWS_AND_LOGIC.md` for the Curry–Howard correspondence.
