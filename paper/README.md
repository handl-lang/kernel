# paper/

**Draft — proposed, not accepted.**  No human revision or external
review yet.

- `paper.qmd` — the quarto source
- `references.bib` — bibliography
- `paper.pdf` — the rendered draft

Rebuild: `quarto render paper.qmd --to pdf` (quarto + a LaTeX engine;
TinyTeX works).

## Convention

A repo that publishes a paper keeps it in a top-level `paper/`
directory: `paper.qmd` is the source of truth, `references.bib` and
any assets live beside it, and the committed `paper.pdf` is the
rendered output.  CI rebuilds the pdf from the qmd —
`handl-lang/docs/ci/paper-build.sh`, same command — and pushes the
result back to main when it changes, so a qmd edit never leaves a
stale pdf.

## This paper

This is the kernel paper: the canonical reference for the
arrow-calculus kernel — the closed six-combinator `Term` set, the
`Value`/`TaggedValue` shapes, the `Language` data schema
(language-as-data), and the Graded Modal Sanada Arrow Calculus.
It stays at the calculus level; the platform layer
(`handl-lang/host`) and the domain papers (`handl-lang/eqsat`,
`handl-lang/graphopt`) cite it rather than re-explaining it.  The
source material is [`../crates/`](../crates/) itself plus the
working draft and POC notes in
`handl-lang/host/research/`.
