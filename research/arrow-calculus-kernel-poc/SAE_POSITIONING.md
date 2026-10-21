# SAE Positioning: Staged Arrow Engine

## Status: Positioning document (not a verified result)

Date: 2026-08-31

This document captures the **Staged Arrow Engine (SAE)** framing — the
spatial-computing narrative that motivates lowering the arrow IR to
modern spatial hardware. It is a _positioning_ document, not a tested
result: the empirical evidence in this repo (Challenges #1–#11)
establishes the calculus and its structural properties; the SAE
framing describes the intended downstream target.

---

## The Problem SAE Addresses

Traditional programming models ground in the **λ-calculus**: variables
bind to lexical environments, function calls allocate dynamic stack
frames. This model is well-suited to single-threaded CPUs but creates
severe bottlenecks on **spatial hardware** (GPUs, NPUs, FPGAs):

- pointer chasing across heterogeneous memory,
- dynamic heap allocation incompatible with fixed on-device memory,
- dynamic stack management that spatial fabrics do not provide.

Alternative non-von-Neumann execution engines such as **Interaction
Nets (Inets)** enable stackless execution, but using them to run
dynamic λ-calculus terms causes severe memory bloat and runtime
overhead from dynamic node cloning (`dup` nodes).

---

## The SAE Proposal

SAE unifies three core ideas:

1. **Arrow Calculus (process algebra).** Replace implicit function
   application with explicit process composition and data routing.
2. **Multi-Stage Programming (staging).** Use a Stage 0 meta-evaluation
   phase to resolve dynamic control flow into statically route-optimized
   Arrow graphs _before_ execution.
3. **Explicit `ArrowApply` representation.** Express dynamic monadic
   power via an explicit `Apply` node rather than burying control flow
   inside opaque closures (`Rc<dyn Fn>`).

### Architectural advantages claimed

- **Monadic power without opacity.** `ArrowApply ≅ Monad` in expressive
  power, but the explicit `Apply` presentation preserves complete AST
  inspectability (choice recovery, effect inference, dependency graphs).
  This is exactly what Challenge #11 verified empirically.
- **Zero-allocation spatial execution.** Because Stage 0 resolves data
  routing and process topologies upfront, Stage 1 executes on
  contiguous memory buffers with **zero dynamic heap allocations, zero
  runtime node duplication, and zero call-stack overhead**.
- **Pre-compiled chunking.** Dynamic choices can be pre-rendered during
  Stage 0 into a static pool of execution chunks, turning runtime
  `ArrowApply` dispatch into a zero-allocation pointer switch rather
  than an expensive runtime compilation step. (See the "Speculative
  Compilation" section of `RESULTS_CHALLENGE11.md` and `WRITEUP.md` §6.)

---

## What is and is not established

| Claim                                            | Status                                     |
| ------------------------------------------------ | ------------------------------------------ |
| Arrow calculus is sufficient for PL construction | ✅ Challenges #1–#8, #11                   |
| Five primitives are independent (minimal)        | ✅ Challenge #10 (Lean4)                   |
| Explicit `ArrowApply` preserves inspectability   | ✅ Challenge #11 (19 tests)                |
| Opaque monadic encoding is structurally lossy    | ✅ Challenge #9 (33 tests)                 |
| Stage 0 staging eliminates dynamic allocation    | ⚠️ Proposed — not implemented in this repo |
| Lowering to Wasm memory slabs / WGSL dispatch    | ⚠️ Proposed — not implemented in this repo |
| Direct FPGA netlist synthesis                    | ⚠️ Speculative future direction            |
| Inets/dup-node overhead is avoided by SAE        | ⚠️ Argument only — no benchmark            |

The SAE framing is the **research direction**, not a completed result.
The completed results are the calculus and its structural properties;
the spatial lowering is the proposed next phase.

---

## Proposed Next Steps

1. **Targeting WebAssembly & WebGPU.** Lower the explicit Arrow IR
   graph into pre-allocated Wasm memory slabs and WGSL compute shaders
   for zero-allocation web execution.
2. **Visual tooling & hardware synthesis.** Develop visual graph
   inspection tools for spatial debugging; explore direct compilation
   to FPGA netlists.
3. **Benchmark against Inet-based λ execution.** Quantify the claimed
   avoidance of `dup`-node bloat on a representative dynamic workload.

---

## Relationship to the rest of the repo

The SAE narrative is the _application_ of the calculus results in this
repo. Challenges #9 and #11 are the load-bearing empirical results for
the SAE claim that explicit `ArrowApply` preserves the structure
required for ahead-of-time chunk pre-compilation. The minimality
result (Challenge #10) is what makes the calculus a credible
_foundation_ rather than an ad-hoc IR.

For the novelty status of the SAE framing relative to prior art, see
`PRIOR_ART.md`.
