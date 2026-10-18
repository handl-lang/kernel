# kernel

The arrow-calculus kernel of the Handl platform (ADR-0040): the calculus
vocabulary itself and nothing else — `Plugin`, `Host`, `Operation`,
`Behavior`, `RuleAcceptor`, `Contribution`, `Term`/`Value` shapes.

- `crates/hnl-engine` — the composition primitives every engine,
  emitter, and host builds on.
- `crates/handl-language` — the `Language` data schema and the staged
  `lex`/`parse`/`eval` dispatch signatures (ADR-0044 "language as data").
- `crates/handl-value` — the tagged `Value` representation shared by the
  eval engines.

Engines, emitters, kits, plugins, and hosts are **not** kernel — they live
in `handl-lang/platform` and the target repos. The kernel depends on
nothing in-repo but itself (crates.io deps only), so downstream repos can
pin the calculus without pulling the platform.

It was extracted from the `handl-lang/platform` workspace per the
ADR-0128 repo-split pattern: `git subtree split` preserves each crate's
history, grafted under `crates/`. Consumers take the crates as git deps
on `handl-lang/kernel` (`branch = "main"`, float-on-main); for local
development a sibling `../kernel` checkout is wired through the
consumer's `[patch]` table (`scripts/dev-link.sh` in platform
regenerates it).
