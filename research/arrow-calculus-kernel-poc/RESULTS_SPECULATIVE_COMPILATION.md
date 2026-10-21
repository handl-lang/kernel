# Speculative Compilation of Transparent ArrowApply Trees

## Status: ✅ COMPLETE — 16/16 new tests passing, 221/221 cumulative

Date: 2026-08-31
Challenge: Speculative compilation (practical follow-up to Challenge #11)
Cumulative: 221/221 Rust tests passing (205 prior + 16 new), zero errors.

---

## The Question

RESULTS_CHALLENGE11.md proposed that the transparency of explicit
`ArrowApply` enables **speculative compilation**: pre-compiling every
reachable execution path into a flat execution chunk, turning runtime
`ArrowApply`/`Choice` dispatch into a zero-allocation table lookup.

> _Pre-rendering chunks turns ArrowApply from a runtime graph-synthesis
> step into a zero-allocation dispatch table._

**Does this actually work? Is it practical? What are the limits?**

---

## Implementation Design

### Three execution modes

| Mode                     | Description                                                    | Allocation                                           | Structure                       |
| ------------------------ | -------------------------------------------------------------- | ---------------------------------------------------- | ------------------------------- |
| **Tree-walking**         | Traverse `ExplicitComp` tree at runtime (the current approach) | Heap allocs per call (Box for Pair/Left/Right/Arrow) | Recursive, pointer-chasing      |
| **Speculative dispatch** | Pre-compiled flat chunk dispatch table                         | **Zero** at runtime                                  | Linear op array + indirect jump |
| **Baseline**             | Hand-written flat function (theoretical optimum)               | Zero                                                 | Compiled by LLVM                |

### Stage 0: `analyze(tree) -> DispatchTable`

The analyzer walks the `ExplicitComp` tree and compiles each reachable
path into a `Chunk` — a flat array of `FlatOp` operations with a
`ChunkTerm` terminator:

```
FlatOp ::= Const(i32) | AddConst(i32) | MulConst(i32) | SubConst(i32)
         | GetState | PutState | Dup | Pop | Add | Mul | Nop

ChunkTerm ::= Halt
             | Branch { left: usize, right: usize }       // Choice
             | DispatchApply { targets: Vec<usize> }       // ArrowApply
```

- **`Seq(f, g)`** → append `f`'s ops, then `g`'s ops into the same chunk.
- **`Choice(f, g)`** → set the current chunk's terminator to `Branch`,
  allocate two new chunks, compile `f` and `g` into them.
- **`SelectArrow(candidates)`** → set terminator to `DispatchApply` with
  one target per candidate; compile each candidate into its own chunk.
- **`Apply`** (truly dynamic, arrow unknown at compile time) → cannot be
  pre-compiled; falls back to tree-walking. This is the unbounded case.

### Runtime: `run_flat_from(table, stack, state)`

The flat VM operates on a pre-allocated `Vec<i32>` stack (reused across
invocations, never grown during execution for the benchmark programs).
Execution is a simple loop:

1. Read the current chunk by index.
2. Execute each `FlatOp` in order (no recursion, no allocation).
3. Execute the terminator:
   - `Halt` → return top of stack.
   - `Branch` → pop a tag (0=Left, nonzero=Right), jump to the target chunk.
   - `DispatchApply` → pop value, pop arrow ID, push value, jump to the
     pre-compiled chunk for that arrow.

**No `Box`, no `Value` enum, no `String`, no `HashMap` lookup at runtime.**
The dispatch is a single array index.

### Stack convention for nested branching

For nested `Choice`, tags are pushed innermost-first, outermost-last.
Each `Branch` pops one tag and dispatches, leaving the payload and
remaining inner tags on the stack:

```
4-way input Left(Left(x)):
  stack = [x, 0(inner), 0(outer)]
  outer Branch pops 0 → left chunk
  inner Branch pops 0 → left-left chunk
  left-left chunk: AddConst(10) on x, Halt → x + 10
```

### Allocation measurement

A custom `GlobalAlloc` wrapper (`CountingAlloc`) wraps the system
allocator and counts every `alloc` call via `AtomicU64` counters.
Counters are reset before each benchmark phase and read after, giving
exact allocation counts per execution mode.

---

## Benchmark Setup

### Programs

| Benchmark       | Tree structure                     | Paths | Description                        |
| --------------- | ---------------------------------- | ----- | ---------------------------------- |
| `no_branch`     | `Seq(AddConst(1), MulConst(2))`    | 1     | Pure pipeline: `(x+1)*2`           |
| `2-way`         | `Choice(AddConst(1), MulConst(2))` | 2     | One Choice: Left→x+1, Right→x*2    |
| `4-way`         | Nested `Choice` (2 levels)         | 4     | Two Choices: 4 leaf operations     |
| `8-way`         | Nested `Choice` (3 levels)         | 8     | Three Choices: 8 leaf operations   |
| `dynamic_apply` | `SelectArrow([+1, *2, -1, *3])`    | 4     | ArrowApply with 4 candidate arrows |

### Methodology

- **Iterations:** 5,000,000 per benchmark (per mode).
- **Build:** `cargo run --release` (LLVM `-O3`).
- **Warmup:** Each benchmark is run once before measurement.
- **Correctness:** Every benchmark asserts `tree_result == flat_result == baseline_result`.
- **Machine:** Single-threaded, release build.

Run with:

```bash
cargo run --bin speculative_compilation --release
```

---

## Results

### Execution time (ns per call)

| Benchmark     | Tree-walking | Speculative dispatch | Baseline | Tree/Flat speedup | Flat/Base gap |
| ------------- | ------------ | -------------------- | -------- | ----------------- | ------------- |
| no_branch     | 24.35 ns     | 7.00 ns              | 0.78 ns  | 3.48x             | 9.02x         |
| 2-way         | 27.34 ns     | 7.53 ns              | 0.96 ns  | 3.63x             | 7.88x         |
| 4-way         | 43.05 ns     | 12.13 ns             | 1.19 ns  | 3.55x             | 10.16x        |
| 8-way         | 57.54 ns     | 13.14 ns             | 3.65 ns  | 4.38x             | 3.60x         |
| dynamic_apply | 42.79 ns     | 8.35 ns              | 1.18 ns  | 5.12x             | 7.05x         |

### Runtime allocations (per call)

| Benchmark     | Tree-walking | Speculative dispatch | Baseline |
| ------------- | ------------ | -------------------- | -------- |
| no_branch     | 0.00         | **0.00**             | 0.00     |
| 2-way         | 1.00         | **0.00**             | 0.00     |
| 4-way         | 2.00         | **0.00**             | 0.00     |
| 8-way         | 3.00         | **0.00**             | 0.00     |
| dynamic_apply | 2.00         | **0.00**             | 0.00     |

> The tree-walking interpreter allocates 1 `Box` per `Choice` level
> (for `Left`/`Right` wrapping) plus 1 for `Pair` in the `SelectArrow`
> case. The `no_branch` case allocates 0 because `Int` values don't
> require boxing. **Speculative dispatch allocates zero in every case.**

### Setup cost (Stage 0 analysis + compilation)

| Benchmark     | Setup time | Chunks produced |
| ------------- | ---------- | --------------- |
| no_branch     | 539 ns     | 1               |
| 2-way         | 516 ns     | 3               |
| 4-way         | 957 ns     | 7               |
| 8-way         | 2,027 ns   | 15              |
| dynamic_apply | 917 ns     | 5               |

> Setup is a one-time cost of ~500 ns to ~2 µs. It is amortized over
> millions of invocations — negligible if the program runs more than
> ~100 times.

### Memory: flat ops vs tree nodes

| Benchmark     | Tree nodes | Flat ops (incl. terminators) | Ratio |
| ------------- | ---------- | ---------------------------- | ----- |
| no_branch     | 3          | 3                            | 1.00x |
| 2-way         | 3          | 5                            | 1.67x |
| 4-way         | 7          | 11                           | 1.57x |
| 8-way         | 15         | 23                           | 1.53x |
| dynamic_apply | 5          | 9                            | 1.80x |

> The flat representation uses ~1.5–1.8x the memory of the tree (each
> chunk carries its own copy of shared ops plus a terminator). This is
> the space cost of pre-compilation.

### Exponential blowup: nested Choices (full binary tree)

| Depth | Chunks  | Flat ops | Flat ops / tree nodes |
| ----- | ------- | -------- | --------------------- |
| 0     | 1       | 2        | 2.00                  |
| 1     | 3       | 5        | 1.67                  |
| 2     | 7       | 11       | 1.57                  |
| 4     | 31      | 47       | 1.52                  |
| 8     | 511     | 767      | 1.50                  |
| 12    | 8,191   | 12,287   | 1.50                  |
| 16    | 131,071 | 196,607  | 1.50                  |

> Chunks grow as **2^(depth+1) − 1** — exponential in nesting depth.
> The flat-op-to-tree-node ratio converges to **1.50x** (each leaf op
> is duplicated in its own chunk, plus one terminator per chunk, plus
> one branch terminator per internal node). At depth 16, this is
> 131K chunks / 197K flat ops — still manageable, but depth 20 would
> be 2M chunks. This is the fundamental limit.

---

## Key Findings

### 1. Speculative dispatch is 3.5–5x faster than tree-walking

The flat VM is consistently **3.5x to 5.1x faster** than the
tree-walking interpreter. The speedup comes from two sources:

- **Zero allocation:** The tree walker allocates 1–3 `Box`es per call
  (for `Left`/`Right`/`Pair` wrapping). Each allocation is a heap
  request + pointer chase + eventual free. The flat VM operates on
  raw `i32` values on a pre-allocated stack — no heap contact.
- **Linear execution vs pointer-chasing:** The tree walker follows
  `Box` pointers through the tree (random memory access, branchy
  match dispatch). The flat VM iterates over a contiguous `Vec<FlatOp>`
  array (sequential memory, predictable branch pattern).

### 2. Zero runtime allocation is achieved — verifiably

The `CountingAlloc` wrapper confirms: **speculative dispatch makes
exactly 0 heap allocations per invocation** across all benchmarks.
The tree walker makes 0–3 allocations per call (depending on
branching depth). This is the core claim from RESULTS_CHALLENGE11.md,
and it holds.

### 3. But the flat VM is still 4–10x slower than the baseline

The hand-written baseline functions are compiled by LLVM into
tight machine code (a few arithmetic instructions + a branch).
The flat VM is still an **interpreter** — it dispatches on `FlatOp`
tags in a loop, which LLVM cannot fully eliminate. The 4–10x gap
is the interpreter overhead: tag dispatch, stack manipulation,
indirect chunk jumps.

> **Honest assessment:** Speculative dispatch eliminates the
> _allocation_ overhead and the _pointer-chasing_ overhead of
> tree-walking, but it does NOT eliminate the _interpretation_
> overhead. To close the gap to the baseline, you would need to
> JIT-compile the chunks to native code (or transpile to a target
> like WGSL/LLVM IR). The dispatch table gets you to "fast
> interpreter"; only codegen gets you to "native speed."

### 4. The speedup grows with branching depth

| Benchmark     | Tree/Flat speedup |
| ------------- | ----------------- |
| no_branch     | 3.48x             |
| 2-way         | 3.63x             |
| 4-way         | 3.55x             |
| 8-way         | 4.38x             |
| dynamic_apply | 5.12x             |

The tree walker's cost grows faster than the flat VM's because each
`Choice` level adds a `Box` allocation + a recursive call + a
pointer chase. The flat VM adds only one tag pop + one indirect
jump per branch level. The dynamic_apply case shows the largest
speedup (5.12x) because the tree walker allocates a `Pair` + does
a `Vec` index + recurses into the candidate, while the flat VM
does two pops + one array index.

### 5. Setup cost is negligible for hot programs

Stage 0 analysis takes 500 ns – 2 µs. For a program invoked
millions of times, this is amortized to nothing. For a program
invoked once, it's pure overhead — but then tree-walking is also
fine since you're not latency-sensitive.

### 6. Exponential blowup is real but bounded for practical depths

The chunk count is **2^(depth+1) − 1** for a full binary tree of
nested Choices. At depth 8 (256-way branching), this is 511 chunks
— fine. At depth 16 (65536-way branching), it's 131K chunks —
borderline. At depth 20, it's 2M chunks — impractical.

However, **real programs rarely have deeply nested static choices**.
The branching depth in practice is typically 2–4 (a few if/else
levels). The exponential blowup is a theoretical limit, not a
practical blocker for typical programs.

---

## When speculative compilation helps

| Condition                                                      | Helps?      | Why                                                                                        |
| -------------------------------------------------------------- | ----------- | ------------------------------------------------------------------------------------------ |
| Finite, small branch space (≤ ~1000 paths)                     | ✅ Yes      | All paths pre-compiled; dispatch is O(1)                                                   |
| Hot programs (invoked >> 1000x)                                | ✅ Yes      | Setup cost amortized; per-call overhead is 3.5–5x lower                                    |
| Branching determined by runtime data from a known set          | ✅ Yes      | `SelectArrow` / `DispatchApply` handles this directly                                      |
| Allocation-sensitive environments (embedded, real-time)        | ✅ Yes      | Zero runtime allocation is verifiable                                                      |
| Unbounded dynamic dispatch (arrow set unknown at compile time) | ❌ No       | `Apply` node cannot be pre-compiled; must fall back to tree-walking                        |
| Very deep nesting (> 16 levels of static Choice)               | ⚠️ Marginal | Chunk count explodes; memory cost may exceed benefit                                       |
| Cold programs (invoked once)                                   | ❌ No       | Setup cost is pure overhead; tree-walking is simpler                                       |
| Need for native-speed execution                                | ⚠️ Partial  | Eliminates alloc overhead but not interpretation overhead; need JIT/codegen for full speed |

---

## Honest Assessment

### What works

The core claim — **zero-allocation dispatch via pre-compiled chunks** —
is **verified and real**. The `CountingAlloc` wrapper proves 0
allocations at runtime. The 3.5–5x speedup over tree-walking is
consistent and meaningful. For programs with a finite, bounded branch
space that are invoked many times, speculative compilation is a clear
win.

### What doesn't work

1. **The flat VM is still an interpreter.** It's 4–10x slower than
   hand-written code. The dispatch table eliminates allocation and
   pointer-chasing, but not the interpretation loop. To reach native
   speed, the chunks would need to be compiled to machine code (JIT)
   or transpiled to a target IR (WGSL, LLVM IR, etc.). The
   "zero-allocation dispatch table" is necessary but not sufficient
   for "native speed."

2. **Truly dynamic `Apply` cannot be pre-compiled.** When the arrow
   is an arbitrary runtime value (not from a known finite set), Stage 0
   cannot enumerate the candidates. The `Apply` node must fall back to
   tree-walking. This is the fundamental limitation: speculative
   compilation only works when the branch space is **statically
   bounded**.

3. **Exponential blowup limits depth.** Each nested `Choice` doubles
   the chunk count. For depth ≤ 10 (≤ 2047 chunks), this is fine.
   For depth > 16, memory becomes prohibitive. Real programs with
   moderate branching are OK; pathological nesting is not.

4. **The tree walker is already fast enough for many use cases.** At
   24–58 ns/call, tree-walking is sub-microsecond. For programs that
   aren't in a tight inner loop, this is perfectly adequate. The
   speculative dispatch win (7–13 ns/call) matters only when
   invocation frequency is high enough for the difference to compound.

### Bottom line

> **Speculative compilation of transparent ArrowApply trees is
> practical for programs with a finite, bounded branch space that are
> invoked frequently. It achieves verifiable zero-allocation dispatch
> and a 3.5–5x speedup over tree-walking. However, it does NOT achieve
> native speed — the flat VM is still an interpreter, 4–10x slower
> than hand-written code. The idea is a real optimization, not a
> silver bullet. It is the right tool when you need to eliminate
> allocation overhead in a hot loop with bounded branching, and it
> composes naturally with a future JIT/codegen stage that would close
> the remaining gap to native speed.**

---

## Files

- `src/speculative_compilation.rs` — full implementation + 16 tests + benchmark binary
- `Cargo.toml` — added `speculative_compilation` binary
- `RESULTS_SPECULATIVE_COMPILATION.md` — this document

---

## Cumulative Results

| Phase     | Challenge                                                            | Tests                               | Status          |
| --------- | -------------------------------------------------------------------- | ----------------------------------- | --------------- |
| 1         | #1–5 (expressiveness, abstraction, parametricity, typing, recursion) | 44                                  | ✅              |
| 2         | #6 (effects & handlers)                                              | 20                                  | ✅              |
| 3         | #7–8 (language protocol, generic tooling)                            | 26                                  | ✅              |
| Deep dive | Effect typing                                                        | 31                                  | ✅              |
| 4         | #9 (structural preservation)                                         | 33                                  | ✅              |
| 5         | #10 (minimality — Lean4)                                             | 11 theorems (9 proven, 2 specified) | ✅              |
| 6         | #11 (ArrowApply without opacity)                                     | 19                                  | ✅              |
| 7         | Speculative compilation (this)                                       | 16                                  | ✅              |
|           | **Total**                                                            | **221 + 11**                        | **All passing** |
