# AI-Generated Code Structure Experiment

## Status: COMPLETE — 28/28 tests passing

Date: 2026-09-01
Challenge: AI-generated code structure (PAPER.tex §8.3 evidence)
Cumulative: 205/205 tests passing (177 prior + 28 new), zero warnings.

---

## The Question

PAPER.tex §8.3 argues that arrow representations are more robust to
AI-generated code than lambda representations for structural analysis.
This argument was previously **speculation**. This experiment turns it
into **evidence**.

The thesis (THESIS.md, "What the structural advantage is NOT over")
already clarifies the precise claim:

> The structural advantage is over **opaque monadic representations**,
> not over lambda per se. Lambda terms, represented as syntax trees
> rather than compiled to closures, are also fully inspectable. The
> distinction: arrows make computational structure **explicit at the
> representation level** (fanout is `&&&`, feedback is `loop`,
> sequencing is `>>>`), while lambda makes it **implicit in the term
> structure**. Both representations _can_ yield the same structural
> information; arrows give it by construction, lambda requires
> recovery through analysis.

This is an argument about **enforcement vs. permission**: arrows make
it impossible to obscure computational structure, while lambda permits
obscuring it.

**The experiment tests this claim with three analysis levels on the
same computations, including obscured (AI-pattern) lambda code.**

---

## Experiment Design

### Three Analysis Levels

We test the same computations under three analysis regimes:

| Level                    | Approach        | How it works                                                           |
| ------------------------ | --------------- | ---------------------------------------------------------------------- |
| **Naive lambda**         | Syntactic       | `let x = e1 in e2` → e2 depends on e1 (no variable-usage check)        |
| **Sophisticated lambda** | Data-flow       | Checks whether `x` is actually used in `e2`; computes free variables   |
| **Arrow**                | By construction | Reads combinators directly (`Fanout` = independent, `Seq` = dependent) |

The **naive** analysis represents what a simple tool (or a human
skimming code) does: it sees sequential structure and assumes
dependency. The **sophisticated** analysis represents the best case
for lambda: proper data-flow analysis with free-variable computation
and use-def chains. The **arrow** analysis represents the arrow
advantage: structure is read directly from the representation.

### Eight Computations

Each computation is defined in both lambda and arrow form. The lambda
forms include "obscured" variants — the kind of code an LLM might
produce: correct but structurally undisciplined.

| #   | Name                         | True structure                  | Lambda obscuration                                                                               | Arrow form                      |
| --- | ---------------------------- | ------------------------------- | ------------------------------------------------------------------------------------------------ | ------------------------------- |
| C1  | Independent pair (obscured)  | f, g independent                | `let a = f(x) in let b = g(x) in (a,b)` — let-chain makes g appear dependent on f                | `f &&& g`                       |
| C2  | Independent state reads      | Two Gets independent            | `let a = Get in let b = Get in (a,b)` — let-chain makes second Get appear dependent on first     | `Get &&& Get`                   |
| C3  | Real sequential dependency   | g depends on f                  | `let a = f(x) in g(a)` — real dependency, no obscuration                                         | `f >>> g`                       |
| C4  | Mixed independent/dependent  | f→g dependent, h independent    | `let a = f(x) in let b = g(a) in let c = h(x) in (b,c)` — h's independence obscured by let-chain | `(f >>> g) &&& h`               |
| C5  | Feedback (recursion)         | Fixed-point structure           | `rec fact = λn. if n ≤ 1 then 1 else n * fact(n-1)` — feedback hidden in recursive call          | `loop step`                     |
| C6  | Branching with effects       | Two branches, different effects | `if b then (Get; Throw) else Put` — branching visible                                            | `choice (Get >>> Throw) Put`    |
| C7  | Nested branching             | Three-way branching             | `if b then (if c then Get else Put) else Throw` — nesting obscures structure                     | `choice (choice Get Put) Throw` |
| C8  | AI pattern: dead computation | f, g independent                | `let a = f(x) in g(x)` — a is never used; LLM computes unnecessary f(x)                          | `f &&& g`                       |

### Metrics

For each computation and analysis level, we measure:

- **Independence detection**: how many independent pairs are correctly identified?
- **False dependencies (missed independence)**: how many independent pairs does the analysis fail to detect?
- **Feedback detection**: can the analysis identify the feedback channel?
- **Per-branch effects**: can the analysis determine per-branch effect sets?
- **Analysis steps**: how many steps does the analysis require?

---

## Results

### Per-Computation Comparison

```
C1: Independent pair (obscured by let-chain)
  Ground truth: independent_pairs=1, feedback=false, per_branch=false

  Analysis       | steps | indep | false_deps | feedback | per_branch
  ---------------+-------+-------+------------+----------+----------
  Naive λ        |    34 |     0 |          1 |    false |     false
  Sophisticated  |    49 |     1 |          0 |    false |     false
  Arrow          |    13 |     1 |          0 |    false |     false

C2: Independent state reads (obscured by let-chain)
  Ground truth: independent_pairs=1, feedback=false, per_branch=false

  Analysis       | steps | indep | false_deps | feedback | per_branch
  ---------------+-------+-------+------------+----------+----------
  Naive λ        |    28 |     0 |          1 |    false |     false
  Sophisticated  |    41 |     1 |          0 |    false |     false
  Arrow          |    13 |     1 |          0 |    false |     false

C3: Real sequential dependency
  Ground truth: independent_pairs=0, feedback=false, per_branch=false

  Analysis       | steps | indep | false_deps | feedback | per_branch
  ---------------+-------+-------+------------+----------+----------
  Naive λ        |    21 |     0 |          0 |    false |     false
  Sophisticated  |    29 |     0 |          0 |    false |     false
  Arrow          |    13 |     0 |          0 |    false |     false

C4: Mixed independent and dependent parts
  Ground truth: independent_pairs=1, feedback=false, per_branch=false

  Analysis       | steps | indep | false_deps | feedback | per_branch
  ---------------+-------+-------+------------+----------+----------
  Naive λ        |    44 |     0 |          1 |    false |     false
  Sophisticated  |    64 |     1 |          0 |    false |     false
  Arrow          |    21 |     1 |          0 |    false |     false

C5: Feedback obscured by recursion (factorial)
  Ground truth: independent_pairs=0, feedback=true, per_branch=false

  Analysis       | steps | indep | false_deps | feedback | per_branch
  ---------------+-------+-------+------------+----------+----------
  Naive λ        |    16 |     0 |          0 |     true |     false
  Sophisticated  |    23 |     0 |          0 |     true |     false
  Arrow          |     8 |     0 |          0 |     true |     false

C6: Branching with per-branch effects
  Ground truth: independent_pairs=0, feedback=false, per_branch=true

  Analysis       | steps | indep | false_deps | feedback | per_branch
  ---------------+-------+-------+------------+----------+----------
  Naive λ        |    27 |     0 |          0 |    false |      true
  Sophisticated  |    34 |     0 |          0 |    false |      true
  Arrow          |    25 |     0 |          0 |    false |      true

C7: Branching obscured by nested conditionals
  Ground truth: independent_pairs=0, feedback=false, per_branch=true

  Analysis       | steps | indep | false_deps | feedback | per_branch
  ---------------+-------+-------+------------+----------+----------
  Naive λ        |    31 |     0 |          0 |    false |      true
  Sophisticated  |    39 |     0 |          0 |    false |      true
  Arrow          |    25 |     0 |          0 |    false |      true

C8: False dependency from unnecessary computation (AI pattern)
  Ground truth: independent_pairs=1, feedback=false, per_branch=false

  Analysis       | steps | indep | false_deps | feedback | per_branch
  ---------------+-------+-------+------------+----------+----------
  Naive λ        |    21 |     0 |          1 |    false |     false
  Sophisticated  |    29 |     1 |          0 |    false |     false
  Arrow          |    13 |     1 |          0 |    false |     false
```

### Aggregate Results

```
  Metric                    | Naive λ  | Sophisticated | Arrow
  ---------------------------+----------+---------------+-------
  Total analysis steps      |      222 |           308 |    131
  Total false dependencies  |        4 |             0 |      0
  Independence accuracy     |  4/8     |     8/8       |  8/8
```

---

## Key Findings

### 1. Naive lambda analysis fails on obscured code (4/8 correct)

The naive syntactic analysis — which treats every `let x = e1 in e2`
as creating a dependency from e1 to e2 — **misses all 4 independent
pairs** in the obscured computations (C1, C2, C4, C8). It produces
**4 false dependencies**: computations that are actually independent
but appear dependent due to the let-chain structure.

This is the "permission" problem: lambda permits the programmer (or
LLM) to write code where independence is obscured by sequential
structure. A naive analysis cannot recover it.

### 2. Sophisticated lambda analysis recovers all structure (8/8 correct)

With proper data-flow analysis — computing free variables, checking
whether bound variables are actually used — the sophisticated lambda
analysis **correctly detects all 4 independent pairs** and produces
**zero false dependencies**. It matches the arrow analysis in accuracy.

This confirms the thesis: **lambda CAN recover structure with
sufficient analysis**. The advantage is not about impossibility.

### 3. But sophisticated lambda requires 2.3x more analysis steps

The sophisticated lambda analysis requires **308 steps** across all 8
computations, compared to **131 steps** for the arrow analysis — a
**2.3x overhead**. This overhead comes from:

- Free-variable computation for every `let` binding
- Use-def chain construction
- Pair component variable-disjointness checking

The arrow analysis reads structure directly from combinators:
`Fanout` → independent, `Seq` → dependent, `Choice` → branching,
`Loop` → feedback. No data-flow analysis needed.

### 4. Arrow analysis is correct by construction (8/8, 0 false deps, 131 steps)

The arrow analysis:

- Detects all 4 independent pairs (via `Fanout` combinator)
- Produces zero false dependencies (structure is enforced)
- Requires the fewest analysis steps (131 vs 222 vs 308)
- Never fails on any structural fact

This is the "enforcement" advantage: arrows make it **impossible** to
obscure computational structure. You cannot write `f &&& g` in a way
that hides f and g's independence — the combinator IS the structural
fact.

### 5. Feedback and branching are detectable in all representations

Feedback (C5) and branching (C6, C7) are detectable by all three
analysis levels:

- **Feedback**: lambda's `rec` constructor is syntactically visible;
  arrow's `Loop` combinator is explicit. Both naive and sophisticated
  detect it.
- **Branching**: lambda's `if-then-else` is syntactically visible;
  arrow's `Choice` combinator is explicit. All three detect per-branch
  effects.

This is an **honest negative finding**: the arrow advantage is
**specific to independence detection**, not universal across all
structural properties. For feedback and branching, lambda's syntax
already makes the structure visible.

### 6. The AI-generated code pattern (C8) is the clearest case

Computation C8 simulates a common AI-generated code pattern: compute
something unnecessary, then do the real work. The lambda form
`let a = f(x) in g(x)` (where `a` is never used) makes g appear
dependent on f. The naive analysis gets this wrong; the sophisticated
analysis must do dead-variable detection to recover the independence.
The arrow form `f &&& g` makes independence inescapable.

---

## Honest Assessment

### What the evidence supports

The evidence supports the **enforcement vs. permission** argument:

1. **Naive analysis fails on obscured lambda code** (4 false dependencies,
   50% independence accuracy). This is what happens when structure is
   permitted to be implicit and the analysis is simple.

2. **Sophisticated analysis succeeds but costs more** (2.3x more steps
   than arrow). This is the cost of recovering structure that lambda
   permits to be obscured.

3. **Arrow analysis succeeds by construction** (zero false dependencies,
   fewest steps). This is the benefit of enforcing structural
   explicitness.

### What the evidence does NOT support

- **It does not show lambda analysis is impossible.** The sophisticated
  analysis recovers all structural facts. The gap is about analysis
  effort, not fundamental impossibility.

- **It does not show arrows are universally better.** For feedback and
  branching, lambda's syntax already exposes the structure. The arrow
  advantage is specific to **independence detection** (fanout).

- **It does not prove AI-generated code is always obscured.** The
  experiment simulates AI patterns (C8) but does not test on actual
  LLM output. The argument is architectural: in a setting where code
  generators cannot be trusted to write well-structured code, a
  representation that enforces structure is more robust.

### The precise claim (updated)

The evidence supports this refined version of the §8.3 argument:

> **For structural analysis of code where independence may be obscured
> (by let-chaining, dead computations, or undisciplined sequencing),
> arrow representations are more robust than lambda representations:
> they detect independence correctly by construction (zero false
> dependencies, minimal analysis steps), while lambda requires
> data-flow analysis to recover the same facts (2.3x more steps).
> For feedback and branching, both representations expose structure
> syntactically. The advantage is specific to independence detection
> and is about enforcement vs. permission, not impossibility.**

### Implications for the paper

PAPER.tex §8.3 can now cite this experiment as evidence rather than
speculation. The key points to update:

1. Replace "This is not a theorem" with "This is supported by
   experimental evidence (see RESULTS_AI_CODE_STRUCTURE.md): naive
   lambda analysis produces 4 false dependencies on 8 computations;
   sophisticated lambda recovers all structure but at 2.3x the
   analysis cost; arrow analysis is correct by construction."

2. Add the honest limitation: "The advantage is specific to
   independence detection. For feedback and branching, lambda syntax
   already exposes the structure."

3. Keep the architectural framing: "In a setting where code generators
   cannot be trusted to write well-structured code, a representation
   that makes structure inescapable is more valuable than one that
   makes structure optional."

---

## Test Summary

28 tests across 7 categories:

| Category                                             | Tests | Status |
| ---------------------------------------------------- | ----- | ------ |
| C1: Independent pair obscured                        | 4     | ✅     |
| C2: Independent state reads                          | 3     | ✅     |
| C3: Real dependency (control)                        | 1     | ✅     |
| C4: Mixed independent/dependent                      | 3     | ✅     |
| C5: Feedback (recursion)                             | 1     | ✅     |
| C6: Branching with effects                           | 2     | ✅     |
| C7: Nested branching                                 | 1     | ✅     |
| C8: AI pattern (dead computation)                    | 3     | ✅     |
| Aggregate: arrow never has false deps                | 1     | ✅     |
| Aggregate: naive misses independence                 | 1     | ✅     |
| Aggregate: sophisticated requires more steps         | 1     | ✅     |
| Aggregate: arrow independence = ground truth         | 1     | ✅     |
| Aggregate: sophisticated independence = ground truth | 1     | ✅     |
| Aggregate: naive independence ≠ ground truth         | 1     | ✅     |
| Aggregate: sophisticated recovers all structure      | 1     | ✅     |
| Aggregate: effect inference consistent               | 1     | ✅     |
| Free variable analysis                               | 2     | ✅     |

---

## Files

- `src/ai_code_structure_tests.rs` — 28-test suite + experiment binary
- `Cargo.toml` — added `ai_code_structure` binary
- `RESULTS_AI_CODE_STRUCTURE.md` — this document

---

## Cumulative Results

| Phase     | Challenge                                                            | Tests                                  | Status          |
| --------- | -------------------------------------------------------------------- | -------------------------------------- | --------------- |
| 1         | #1–5 (expressiveness, abstraction, parametricity, typing, recursion) | 48                                     | ✅              |
| 2         | #6 (effects & handlers)                                              | 20                                     | ✅              |
| 3         | #7–8 (language protocol, generic tooling)                            | 26                                     | ✅              |
| Deep dive | Effect typing                                                        | 31                                     | ✅              |
| 4         | #9 (structural preservation)                                         | 33                                     | ✅              |
| 5         | #10 (minimality — Lean4)                                             | 11 theorems                            | ✅              |
| 6         | #11 (ArrowApply without opacity)                                     | 19                                     | ✅              |
| 7         | Translation asymmetry — Lean4                                        | 8 theorems                             | ✅              |
| 8         | AI-generated code structure                                          | 28                                     | ✅              |
|           | **Total**                                                            | **205 Rust tests + 19 Lean4 theorems** | **All passing** |
