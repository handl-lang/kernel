# kernel

The arrow-calculus substrate: language schema, tagged values, extension ABI.

## What it is

The kernel is the platform's smallest layer (ADR-0040): the `Language` data
schema and staged `lex`/`parse`/`eval` dispatch signatures (ADR-0044, language as
data), the tagged `Value` representation the engines share, and the dynamic extension
ABI (`hnl` extensions, ADR-0149). Libraries live in their own `lib-*` repos.

What is *not* kernel: engines, emitters, kits, plugins and hosts. They live in the
`engine-*`/`tool-*`/`exec-*`, `kit-*`, `ext-*` and `host`/`host-*` repos and
depend on the kernel, never the reverse.

## Modules
- `crates/handl-calculus` — the arrow-calculus IR (`Term`/`TermData`, `Model`/`ModelCtx`)
- `crates/handl-language` — the `Language` schema + staged lex/parse/eval dispatch signatures
- `crates/handl-value` — the tagged `Value` representation shared by engines
- `crates/handl-ops` — the op ABI (`Op`/`OpRegistry`/`OpContext`)
- `crates/handl-ext` — the shared ABI for dynamic `hnl` extensions (ADR-0149)
- `crates/defining-handl` — the self-hosting corpus (ADR-0044 phase 8)
- `crates/{ops,prim,prim-handl}` — the remaining `handl-lib-*` substrate packages


## Start here

- **Reference** — [public API](/kernel/reference/)
- **How-to** — [task recipes](/kernel/how-to/)
- **Explanation** — [design and rationale](/kernel/explanation/)

No tutorials: this repo is a building block used from Rust. End-to-end
walkthroughs live with the product that composes it — see the
[Handl platform](/handl/).
