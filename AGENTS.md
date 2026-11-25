# kernel

The arrow-calculus substrate of the Handl platform (ADR-0040): the
`Term`/`Model` calculus, the `Language` data schema, the tagged
`Value` representation, the op ABI, and the `hnl` extension ABI. The
`Plugin`/`Host`/`Operation`/`Behavior`/`RuleAcceptor`/`Contribution`
host primitives live in `handl-lang/host` — engines, emitters, kits,
plugins, and hosts are **not** kernel.

## Layout

| path | role |
| --- | --- |
| `crates/handl-calculus` | the arrow-calculus IR (`Term`/`TermData`, `Model`/`ModelCtx`) and the pluggable model seam |
| `crates/handl-language` | the `Language` data schema + staged `lex`/`parse`/`eval` dispatch signatures (ADR-0044 "language as data") |
| `crates/handl-value` | the tagged `Value` representation shared by the eval engines |
| `crates/handl-ops` | the op ABI: `Op`/`OpRegistry`/`OpContext` |
| `crates/handl-ext` | the shared ABI for `hnl` dynamic extensions (ADR-0149) |
| `crates/defining-handl` | the self-hosting corpus (ADR-0044 Phase 8) |
| `crates/{ops,prim,prim-handl}` | `handl-lib-ops`, `handl-lib-prim`, `handl-lib-prim-handl` substrate packages |
| `vendor/` | vendored deps |
| `workflows/` | bupha gate wiring |

## Contract

- Cargo workspace; member crates resolve each other through the root
  `[patch]` table so downstream repos can pin the substrate without
  pulling host/engine repos.
- The rest of the floor libs live in their own `lib-*` repos.

## Verification

```bash
cargo test --workspace   # or per-crate cargo test
```

<!-- myco:agent-awareness -->

## Agent awareness

- Session start / any work discussion: run `myco status --prompt`
  before proposing next steps — know the board first.
- User describes new work → offer to capture it (`myco todo add`,
  `issue new`, `proposal new`). Don't wait to be asked.
- Picking up a task: `myco resume <ID>` is the briefing.
- Wrapping up: `myco handoff <ID>` anything resumable; keep statuses
  honest (claimed → in-progress → blocked/done).

<!-- /myco:agent-awareness -->
