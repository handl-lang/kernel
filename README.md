# kernel

The arrow-calculus substrate of the Handl platform (ADR-0040): the
`Term`/`Model` calculus, the `Language` data schema, the tagged
`Value` representation, the op ABI, and the `hnl` extension ABI. The
`Plugin`/`Host`/`Operation`/`Behavior`/`RuleAcceptor`/`Contribution`
host primitives live in `handl-lang/host`.

- `crates/handl-calculus` — the arrow-calculus IR (`Term`/`TermData`,
  `Model`/`ModelCtx`) and the pluggable model seam.
- `crates/handl-language` — the `Language` data schema and the staged
  `lex`/`parse`/`eval` dispatch signatures (ADR-0044 "language as data").
- `crates/handl-value` — the tagged `Value` representation shared by the
  eval engines.
- `crates/handl-ops` — the op ABI: `Op`/`OpRegistry`/`OpContext`, the
  registration surface native Handl operations implement.
- `crates/handl-ext` — the shared ABI for `hnl` dynamic extensions
  (ADR-0149).
- `crates/defining-handl` — the self-hosting corpus (ADR-0044
  Phase 8).
- `crates/{ops,prim,prim-handl}` — the remaining `handl-lib-*`
  substrate packages (`handl-lib-ops`, `handl-lib-prim`,
  `handl-lib-prim-handl`); the rest of the floor libs live in their
  own `lib-*` repos.

Engines, emitters, kits, plugins, and hosts are **not** kernel — they live in
the sibling `engine-*`/`tool-*`/`exec-*`, `kit-*`, `ext-*` and `host-*`
repos. The workspace is self-contained: member crates resolve each
other through the root `[patch]` table, so downstream repos can pin the
substrate without pulling the host or engine repos.

Consumers take the crates as git deps on `handl-lang/kernel`
(`branch = "main"`, float-on-main); for local development a sibling
`../kernel` checkout is wired through the consumer's `[patch]` table.

## Documentation

Published site (Diátaxis): <https://handl-lang.github.io/docs/kernel/>

- [Reference](https://handl-lang.github.io/docs/kernel/reference/) — public API surface
- [How-to](https://handl-lang.github.io/docs/kernel/how-to/) — task recipes
- [Explanation](https://handl-lang.github.io/docs/kernel/explanation/) — design and rationale

Decision records live on the `project` branch under `project/adrs/`.
