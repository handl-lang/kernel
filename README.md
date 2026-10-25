# kernel

The arrow-calculus substrate of the Handl platform (ADR-0040): the
`Language` data schema, the tagged `Value` representation, the
extension ABI, and the `handl-lib-*` floor-lib packages. The
`Term`/`Model` foundation types live in `handl-lang/engine`
(`hnl-engine`); the `Plugin`/`Host`/`Operation`/`Behavior`/
`RuleAcceptor`/`Contribution` host primitives live in
`handl-lang/host`.

- `crates/handl-language` — the `Language` data schema and the staged
  `lex`/`parse`/`eval` dispatch signatures (ADR-0044 "language as data").
- `crates/handl-value` — the tagged `Value` representation shared by the
  eval engines.
- `crates/handl-ext` — the shared ABI for `hnl` dynamic extensions
  (ADR-0149).
- `crates/defining-handl` — the self-hosting infrastructure (ADR-0044
  Phase 8).
- `crates/{bytes,cmp,combinators,error,mood,obj,ops,prim,prim-handl,type}`
  — the `handl-lib-*` substrate packages.

Engines, emitters, kits, plugins, and hosts are **not** kernel — they live
in `handl-lang/host` and the target repos. The kernel deps on
`handl-lang/engine` (`hnl-engine`, git dep on `main`), so downstream
repos can pin the substrate without pulling the host repo.

It was extracted from the `handl-lang/host` workspace per the
ADR-0128 repo-split pattern: `git subtree split` preserves each crate's
history, grafted under `crates/`. Consumers take the crates as git deps
on `handl-lang/kernel` (`branch = "main"`, float-on-main); for local
development a sibling `../kernel` checkout is wired through the
consumer's `[patch]` table (`scripts/dev-link.sh` in host
regenerates it).

## Documentation

Published site (Diátaxis): <https://handl-lang.github.io/docs/kernel/>

- [Reference](https://handl-lang.github.io/docs/kernel/reference/) — public API surface
- [How-to](https://handl-lang.github.io/docs/kernel/how-to/) — task recipes
- [Explanation](https://handl-lang.github.io/docs/kernel/explanation/) — design and rationale

Decision records live on the `project` branch under `project/adrs/`.
