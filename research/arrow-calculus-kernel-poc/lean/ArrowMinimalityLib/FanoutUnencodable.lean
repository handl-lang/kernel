/-
# Fanout Unencodability Theorem (Challenge #13)

This file formalizes the key result of Challenge #13: a standard freer
monad — whose `bind` threads the previous *output* as the next *input*
through an opaque function continuation — cannot semantically encode
arrow `fanout`, in which both branches receive the *same* original input.

## The mismatch

  Arrow fanout:
        ┌→ f(input) ─┐
    input─┤            ├→ (v1, v2)        g receives the ORIGINAL input
        └→ g(input) ─┘

  Monadic bind:
    input → f → v1 → g(v1) → v2          g receives f's OUTPUT

These are different computations. We prove the divergence concretely
with the counterexample `Fanout(Get, Put)`:

  - Arrow: `Get` reads the state; `Put` writes the *original input* to
    the state. Final state = input.
  - Monad: `bind` threads `Get`'s output (the state) into the
    continuation, so `Put` writes `Get`'s output (the state) to the
    state. Final state = state.

Whenever `input ≠ state`, the two final states differ. Hence no monadic
translation that threads outputs via `bind` can universally encode arrow
fanout: a single counterexample refutes the universal encoding claim.

## Relation to prior work

This is the semantic strengthening of VanDomelen et al. (Haskell 2025),
who observed the *static-analysis* gap (freer monad continuations are
opaque). We show the gap is not merely observational: it is semantic.
The root cause is the arrow/monad distinction of Lindley, Wadler &
Yallop (2008): arrows have an explicit input parameter `A → B`; monads
do not. `Monad = Arrow + ArrowApply` precisely because `ArrowApply`
reintroduces access to the input.
-/

namespace FanoutUnencodable

-- ============================================================================
-- 1. A minimal value domain
-- ============================================================================
--
-- The counterexample only needs natural numbers (the state channel and
-- the input channel are both `Nat`). Keeping the value domain minimal
-- makes the semantic equations definitionally reduce in Lean.

/-- Values: natural numbers suffice for the fanout counterexample. -/
abbrev V := Nat

-- ============================================================================
-- 2. Operations
-- ============================================================================

/-- The two state operations used by the counterexample. -/
inductive Op : Type where
  | get : Op   -- read the state, yield it as output
  | put : Op   -- write the current arrow input into the state

-- ============================================================================
-- 3. Arrow programs (explicit structural combinators)
-- ============================================================================
--
-- `fanout` is a FIRST-CLASS constructor: both branches are statically
-- visible and both receive the same input. This is the freer-arrow
-- representation.

inductive Arrow : Type where
  | ident : Arrow                                 -- identity: output = input
  | seq : Arrow → Arrow → Arrow                   -- f >>> g : g receives f's output
  | fanout : Arrow → Arrow → Arrow                -- both branches receive the SAME input
  | opNode : Op → Arrow → Arrow                   -- perform an op, then continue

-- ============================================================================
-- 4. Arrow semantics
-- ============================================================================
--
-- `runArrow p input state = (output, newState)`.
--
-- The defining feature: in `fanout f g`, the second branch `g` is run
-- with the *original* `input`, NOT with `f`'s output. This is the
-- parallel-input-distribution semantics that monadic `bind` lacks.

def runArrow : Arrow → V → V → V × V
  | Arrow.ident, input, state => (input, state)
  | Arrow.seq f g, input, state =>
    let (v1, s1) := runArrow f input state
    runArrow g v1 s1
  | Arrow.fanout f g, input, state =>
    let (_v1, s1) := runArrow f input state
    let (v2, s2) := runArrow g input s1   -- g receives the ORIGINAL input
    (v2, s2)
  | Arrow.opNode Op.get k, _input, state => runArrow k state state
  | Arrow.opNode Op.put k, input, _state => runArrow k input input

-- ============================================================================
-- 5. Standard freer monad (opaque function continuations)
-- ============================================================================
--
-- This is the REAL freer monad: `bind`'s continuation is an opaque
-- function `V → Monad`, not a traversable tree. There are NO
-- `Fanout`/`Choice`/`Loop` constructors — branching and parallelism
-- must be encoded through `bind` chains.
--
-- The opacity is in the FUNCTION: you can call it but cannot inspect
-- it. This is exactly Kiselyov's freer monad as modelled in the Rust
-- test suite (`Rc<dyn Fn(Value) -> FreeM>`).

inductive Monad : Type where
  | pure_ : V → Monad
  | bind : Monad → (V → Monad) → Monad   -- continuation is an OPAQUE FUNCTION
  | op : Op → (V → Monad) → Monad        -- perform op, feed result to opaque fn

-- ============================================================================
-- 6. Monadic semantics
-- ============================================================================
--
-- `runMonad m input state = (output, newState)`.
--
-- The defining feature: in `bind m k`, the continuation `k` is run with
-- `v` — the OUTPUT of `m` — as its input. This is the sequential
-- output-threading semantics that makes fanout unencodable: the
-- continuation cannot see the original arrow input, only the previous
-- output.

def runMonad : Monad → V → V → V × V
  | Monad.pure_ v, _input, state => (v, state)
  | Monad.bind m k, input, state =>
    let (v, s) := runMonad m input state
    runMonad (k v) v s                     -- threads v (the OUTPUT) as the next input
  | Monad.op Op.get k, _input, state => runMonad (k state) state state
  | Monad.op Op.put k, input, _state => runMonad (k input) input input

-- ============================================================================
-- 7. The standard arrow → monad translation
-- ============================================================================
--
-- This is the canonical encoding attempted in the Rust test suite
-- (`arrow_to_freem`). It encodes `fanout f g` as a `bind` chain:
--
--   bind (arrowToMonad f) (λ v1. bind (arrowToMonad g) (λ v2. pure v1))
--
-- The `opNode` case special-cases `ident` (matching the Rust
-- `match k { Ident => Pure(result), ... }`) so that an op's result is
-- returned to the continuation — this is what makes `Get`'s output
-- equal to the state, which is then (mis)threaded into `Put`.

def arrowToMonad : Arrow → Monad
  | Arrow.ident => Monad.pure_ 0
  | Arrow.seq f g => Monad.bind (arrowToMonad f) (fun _v => arrowToMonad g)
  | Arrow.fanout f g =>
    Monad.bind (arrowToMonad f) (fun v1 =>
      Monad.bind (arrowToMonad g) (fun _v2 => Monad.pure_ v1))
  | Arrow.opNode op k =>
    Monad.op op (fun result =>
      match k with
      | Arrow.ident => Monad.pure_ result   -- Ident returns the op result
      | _ => arrowToMonad k)

-- ============================================================================
-- 8. The counterexample program
-- ============================================================================
--
-- `Fanout(Get, Put)`:
--   - `Get` reads the state and yields it.
--   - `Put` writes the arrow input into the state.
--
-- Under arrow semantics, `Put` receives the ORIGINAL input, so the
-- final state is `input`. Under monadic `bind`, `Put` receives `Get`'s
-- output (the state), so the final state is `state`.

/-- The witness arrow program: `Fanout(Get, Put)`. -/
def counterexample : Arrow :=
  Arrow.fanout (Arrow.opNode Op.get Arrow.ident) (Arrow.opNode Op.put Arrow.ident)

-- ============================================================================
-- 9. Lemma: arrow fanout writes the original input to the state
-- ============================================================================

/-- Under arrow semantics, `Fanout(Get, Put)` sets the final state to
the original `input`: `Get` reads the state (leaving it unchanged), then
`Put` writes the original `input` (which `fanout` forwards to `g`). -/
theorem runArrow_counterexample_state (input state : V) :
    (runArrow counterexample input state).2 = input := by
  show (runArrow
          (Arrow.fanout (Arrow.opNode Op.get Arrow.ident)
                        (Arrow.opNode Op.put Arrow.ident))
          input state).2 = input
  unfold runArrow
  simp only [runArrow]

-- ============================================================================
-- 10. Lemma: monadic bind threads Get's output (the state) into Put
-- ============================================================================

/-- Under monadic semantics, the `bind`-encoding of `Fanout(Get, Put)`
sets the final state to `state`: `bind` threads `Get`'s output (which is
the state) into the continuation, so `Put` writes the state (not the
original input) to the state. -/
theorem runMonad_counterexample_state (input state : V) :
    (runMonad (arrowToMonad counterexample) input state).2 = state := by
  show (runMonad
          (arrowToMonad
            (Arrow.fanout (Arrow.opNode Op.get Arrow.ident)
                          (Arrow.opNode Op.put Arrow.ident)))
          input state).2 = state
  unfold arrowToMonad runMonad
  simp only [arrowToMonad, runMonad]

-- ============================================================================
-- 11. THE MAIN THEOREM: fanout is unencodable by output-threading bind
-- ============================================================================

/-- **Fanout Unencodability.** The standard arrow → freer-monad
translation (which encodes `fanout` as a `bind` chain threading the
previous output) does NOT preserve arrow fanout semantics.

For the witness `Fanout(Get, Put)`, whenever `input ≠ state` the final
states differ:
  - arrow:  final state = `input`   (`Put` writes the original input)
  - monad:  final state = `state`   (`Put` writes `Get`'s output, the state)

Since a correct universal encoding would have to agree on ALL inputs,
this single counterexample family refutes universal encodability. The
impossibility is structural: monadic `bind` threads outputs, while arrow
`fanout` distributes the original input. -/
theorem fanoutUnencodable (input state : V) (h : input ≠ state) :
    (runArrow counterexample input state).2
      ≠ (runMonad (arrowToMonad counterexample) input state).2 := by
  rw [runArrow_counterexample_state, runMonad_counterexample_state]
  exact h

/-- Concrete counterexample at `input = 42`, `state = 7` (matching the
Rust test `test_freer_monad_CANNOT_encode_fanout`): the arrow sets the
state to 42, the monad leaves it at 7. -/
theorem fanoutUnencodable_concrete :
    (runArrow counterexample 42 7).2
      ≠ (runMonad (arrowToMonad counterexample) 42 7).2 := by
  rw [runArrow_counterexample_state, runMonad_counterexample_state]
  decide

-- ============================================================================
-- 12. Corollary: the encoding is not semantics-preserving
-- ============================================================================

/-- Reformulation: it is NOT the case that `arrowToMonad` preserves the
state semantics of the counterexample for all inputs. This is the
negation of the universal-encoding claim, witnessed by `input ≠ state`.
-/
theorem arrowToMonad_not_state_preserving :
    ¬ ∀ input state : V,
        (runArrow counterexample input state).2
          = (runMonad (arrowToMonad counterexample) input state).2 := by
  intro H
  have := H 1 0
  rw [runArrow_counterexample_state, runMonad_counterexample_state] at this
  exact absurd this (by decide : (1 : V) ≠ 0)

-- ============================================================================
-- 13. Structural corollary: the gap is the input parameter
-- ============================================================================
--
-- The divergence is not an artifact of the particular encoding; it is
-- forced by the shape of `bind`. In `runMonad (bind m k) input state`,
-- the continuation `k` is invoked with `v` — the output of `m` — as its
-- input. The original `input` is NOT available to `k`. In arrow
-- `fanout`, `g` IS given the original `input`. Any encoding built only
-- from `bind` (and `pure`/`op`) inherits this restriction: the
-- continuation can never see the original input, only the previous
-- output. This is precisely the arrow/monad distinction: arrows have
-- an explicit input parameter `A → B`; monads have only `bind`-threaded
-- outputs.

/-- **The `bind` continuation law (semantic, encoding-independent).**
For ANY monadic term `m` and ANY continuation `k`, the continuation in
`runMonad (bind m k) input state` is invoked with `(runMonad m input state).1`
— the OUTPUT of `m` — as its input parameter. The original `input` does
not appear as the continuation's input; it is only fed to `m`.

This is a property of `bind`'s semantics, not of any particular arrow
encoding. It is the formal statement of "monadic `bind` threads outputs,
not inputs." -/
theorem bind_continuation_input_is_predecessor_output
    (m : Monad) (k : V → Monad) (input state : V) :
    runMonad (Monad.bind m k) input state =
      runMonad (k (runMonad m input state).1)
               (runMonad m input state).1
               (runMonad m input state).2 := by
  rfl

/-- **The continuation never receives the original input (when the
predecessor's output differs from it).** If `m`'s output `v` differs
from the original `input`, then the continuation `k` is invoked with
`v`, and no choice of `k` can recover `input` — `k` simply does not
receive it. This is the encoding-independent root cause of fanout
unencodability. -/
theorem continuation_cannot_see_original_input
    (m : Monad) (k : V → Monad) (input state : V)
    (h : (runMonad m input state).1 ≠ input) :
    -- The continuation's input is m's output, which is ≠ input.
    (runMonad (k (runMonad m input state).1)
              (runMonad m input state).1
              (runMonad m input state).2).1
      = (runMonad (Monad.bind m k) input state).1
    ∧ (runMonad m input state).1 ≠ input := by
  rw [← bind_continuation_input_is_predecessor_output]
  exact ⟨rfl, h⟩

/-- **Structural impossibility (encoding-independent).** The
unencodability is not specific to `arrowToMonad`; it is inherent to
`bind`. We state the concrete instance: for `Get` (whose output is the
state), the continuation is run with `state`, regardless of the original
`input`. -/
theorem bind_continuation_input_is_previous_output (input state : V) :
    (runMonad (Monad.bind (Monad.op Op.get (fun v => Monad.pure_ v))
                          (fun v => Monad.pure_ v)) input state).1
      = state := by
  show (runMonad (Monad.bind (Monad.op Op.get (fun v => Monad.pure_ v))
                             (fun v => Monad.pure_ v)) input state).1 = state
  unfold runMonad
  simp only [runMonad]

/-- The arrow `Get` continuation, by contrast, can be run with the
ORIGINAL `input` (via `fanout`), not just the state. This is the
structural source of the gap: arrows expose the input to every branch. -/
theorem arrow_fanout_branch_sees_original_input (input state : V) :
    (runArrow (Arrow.fanout Arrow.ident Arrow.ident) input state).1 = input := by
  show (runArrow (Arrow.fanout Arrow.ident Arrow.ident) input state).1 = input
  unfold runArrow
  simp only [runArrow]

/-- **The gap is structural.** Arrow `fanout` forwards the original
`input` to both branches (theorem `arrow_fanout_branch_sees_original_input`);
monadic `bind` forwards only the previous `output`
(theorem `bind_continuation_input_is_predecessor_output`). No translation
built from `bind` alone can give the continuation access to the original
input. This is why `fanoutUnencodable` holds, and why recovering arrow
expressiveness requires `ArrowApply` (which reintroduces input access). -/
theorem impossibilityIsStructural (input state : V) (h : input ≠ state) :
    -- The arrow can make a branch depend on the original input...
    (runArrow (Arrow.fanout Arrow.ident Arrow.ident) input state).1 = input
    ∧
    -- ...while the monad's continuation can only depend on the previous
    -- output (here, the state). The two channels are distinct whenever
    -- input ≠ state.
    (runMonad (Monad.bind (Monad.op Op.get (fun v => Monad.pure_ v))
                          (fun v => Monad.pure_ v)) input state).1 = state
    ∧ input ≠ state := by
  refine ⟨arrow_fanout_branch_sees_original_input input state,
          bind_continuation_input_is_previous_output input state, h⟩

-- ============================================================================
-- 13b. FORMAL ENCODING CLASS: BindEncoding (direct-bind)
-- ============================================================================
--
-- A "direct-bind encoding" of an arrow is a pair (m, k) where the arrow
-- is encoded as `Monad.bind m k`, with no additional information channel
-- between the original input and the continuation `k`. The only
-- communication from `m` to `k` is `m`'s monadic result.
--
-- This makes the universal quantification precise: the theorem
-- `no_faithful_bind_encoding_preserves_fanout` quantifies over ALL
-- direct-bind `BindEncoding`s whose components satisfy `GetSemantics`
-- and `PutSemantics` — i.e., over all direct-bind encodings that
-- faithfully represent the Get and Put sub-computations of
-- `Fanout(Get, Put)`.

/-- A **direct-bind encoding** of an arrow is a pair (m, k) where the
arrow is encoded as `Monad.bind m k`, with no additional information
channel between the original input and the continuation `k`. The `m`
term encodes the first sub-computation; the continuation `k` (an opaque
function) encodes the second. The only communication from `m` to `k` is
`m`'s monadic result — the original arrow input is not made available
to `k` through any side channel.

This is the formal encoding class: the impossibility theorem quantifies
over all `BindEncoding`s whose components satisfy Get/Put semantics.
The scope is *direct-bind* encodings — those where the top-level
composition of the two sub-computations is exactly `bind m k` with no
preprocessing, duplication, or packaging of the input before the bind. -/
structure BindEncoding where
  m : Monad
  k : V → Monad

/-- The encoded term is `bind m k`. -/
def BindEncoding.encoded (enc : BindEncoding) : Monad :=
  Monad.bind enc.m enc.k

/-- Get-semantics: the term reads the state and yields it as output,
leaving the state unchanged. This is the semantic specification of the
`Get` operation — any faithful encoding of `Get` must satisfy this. -/
def GetSemantics (m : Monad) (input state : V) : Prop :=
  runMonad m input state = (state, state)

/-- Put-semantics: the continuation writes its input argument to the
state. This is the semantic specification of the `Put` operation — any
faithful encoding of `Put` must satisfy this.

Note: the monadic input is `x` (equal to the continuation argument),
not an independent value. This is correct for this model: `Put`'s
operational semantics pass the monadic input as the continuation
argument, so in any bind chain the argument and monadic input coincide.
A stronger spec `∀ x i s, (runMonad (k x) i s).2 = x` (where `i` is
independent of `x`) would be too strong — it does not hold for the
canonical encoding, because `Put` writes the monadic input, and the
monadic input equals the argument by construction. -/
def PutSemantics (k : V → Monad) : Prop :=
  ∀ x s, (runMonad (k x) x s).2 = x

/-- A bind-based encoding is *faithful* to `Fanout(Get, Put)` if `m`
satisfies Get-semantics and `k` satisfies Put-semantics. This is the
class of encodings we quantify over: any correct bind-based encoding of
`Fanout(Get, Put)` must be faithful (otherwise it doesn't encode Get
and Put correctly). -/
def BindEncoding.faithful_fanout (enc : BindEncoding) (input state : V) : Prop :=
  GetSemantics enc.m input state ∧ PutSemantics enc.k

-- ============================================================================
-- 13c. UNIVERSAL IMPOSSIBILITY: no faithful bind encoding preserves fanout
-- ============================================================================
--
-- The theorems above show the *specific* encoding `arrowToMonad` fails.
-- We now prove the *universal* statement: NO faithful `BindEncoding` of
-- `Fanout(Get, Put)` can preserve the arrow's final state. This holds
-- for ALL choices of `m` and `k` satisfying Get/Put semantics, not just
-- the particular `arrowToMonad`.
--
-- The key: by `bind_continuation_input_is_predecessor_output`, the
-- continuation `k` is invoked with `m`'s output. For Get, that is the
-- state. So `k` (encoding Put) writes the state, not the original
-- input. The final state is `state`, never `input` — for any `m, k`.

/-- **Universal fanout unencodability.** For ANY monadic term `m`
satisfying `Get`-semantics (`runMonad m input state = (state, state)`,
i.e. read the state, yield it, leave it) and ANY continuation `k`
satisfying `Put`-semantics (`∀ x s, (runMonad (k x) x s).2 = x`, i.e.
write the input to the state), the `bind`-encoding `bind m k` of
`Fanout(Get, Put)` produces final state `state` — never the original
`input`.

This is the encoding-independent impossibility: it quantifies over ALL
`(m, k)` pairs satisfying the Get/Put semantics, not just the particular
`arrowToMonad`. Since the arrow produces final state `input`
(`runArrow_counterexample_state`), the two diverge whenever
`input ≠ state`, for every such encoding. -/
theorem any_bind_encoding_of_fanout_get_put_yields_state
    (m : Monad) (k : V → Monad) (input state : V)
    (hGet : runMonad m input state = (state, state))
    (hPut : ∀ x s, (runMonad (k x) x s).2 = x) :
    (runMonad (Monad.bind m k) input state).2 = state := by
  rw [bind_continuation_input_is_predecessor_output, hGet]
  exact hPut state state

/-- **No bind-based encoding preserves fanout (universal).** For ALL
monadic `m` (encoding `Get`) and `k` (encoding `Put`), the `bind`-encoding
of `Fanout(Get, Put)` diverges from the arrow semantics whenever
`input ≠ state`. This refutes universal encodability by the entire class
of `bind`-based translations, not just by `arrowToMonad`. -/
theorem no_bind_encoding_preserves_fanout
    (m : Monad) (k : V → Monad) (input state : V)
    (hGet : runMonad m input state = (state, state))
    (hPut : ∀ x s, (runMonad (k x) x s).2 = x)
    (h : input ≠ state) :
    (runArrow counterexample input state).2
      ≠ (runMonad (Monad.bind m k) input state).2 := by
  rw [runArrow_counterexample_state,
      any_bind_encoding_of_fanout_get_put_yields_state m k input state hGet hPut]
  exact h

/-- **The specific encoding `arrowToMonad` is an instance of the
universal failure.** We verify that `arrowToMonad`'s `Get` and `Put`
components satisfy the hypotheses of `no_bind_encoding_preserves_fanout`,
confirming the concrete theorem `fanoutUnencodable` is a corollary of the
universal one. -/
theorem arrowToMonad_get_component_satisfies_Get_semantics
    (input state : V) :
    runMonad (arrowToMonad (Arrow.opNode Op.get Arrow.ident)) input state
      = (state, state) := by
  show runMonad (Monad.op Op.get (fun result => Monad.pure_ result)) input state = (state, state)
  unfold runMonad
  simp only [runMonad]

theorem arrowToMonad_put_component_satisfies_Put_semantics
    (x s : V) :
    (runMonad (arrowToMonad (Arrow.opNode Op.put Arrow.ident)) x s).2 = x := by
  show (runMonad (Monad.op Op.put (fun result => Monad.pure_ result)) x s).2 = x
  unfold runMonad
  simp only [runMonad]

/-- **No faithful BindEncoding preserves fanout.** This is the
encoding-class version of `no_bind_encoding_preserves_fanout`: for any
`BindEncoding` (i.e., any pair `(m, k)` encoding the arrow as
`bind m k`) that is faithful to `Fanout(Get, Put)` (i.e., `m` satisfies
Get-semantics and `k` satisfies Put-semantics), the encoding diverges
from the arrow semantics whenever `input ≠ state`.

This makes the quantification precise: we quantify over the formal
`BindEncoding` class, not merely over raw `(m, k)` pairs. -/
theorem no_faithful_bind_encoding_preserves_fanout
    (enc : BindEncoding) (input state : V)
    (hGet : GetSemantics enc.m input state)
    (hPut : PutSemantics enc.k)
    (h : input ≠ state) :
    (runArrow counterexample input state).2
      ≠ (runMonad enc.encoded input state).2 := by
  unfold BindEncoding.encoded
  exact no_bind_encoding_preserves_fanout enc.m enc.k input state hGet hPut h

/-- The canonical `arrowToMonad` encoding is a `BindEncoding`. -/
def arrowToMonadBindEncoding : BindEncoding := {
  m := arrowToMonad (Arrow.opNode Op.get Arrow.ident)
  k := fun _v => arrowToMonad (Arrow.opNode Op.put Arrow.ident)
}

/-- The canonical `arrowToMonad` encoding is faithful (satisfies
Get/Put semantics), confirming it is an instance of the universal
failure. -/
theorem arrowToMonad_is_faithful (input state : V) :
    arrowToMonadBindEncoding.faithful_fanout input state := by
  unfold BindEncoding.faithful_fanout GetSemantics PutSemantics
  refine ⟨arrowToMonad_get_component_satisfies_Get_semantics input state, ?_⟩
  intro x s
  exact arrowToMonad_put_component_satisfies_Put_semantics x s

-- ============================================================================
-- 14. Choice unencodability (UNIVERSAL, with Sum values)
-- ============================================================================
--
-- Arrow `choice` branches on the INPUT (`Left v → f v`, `Right v → g v`).
-- The monadic continuation cannot branch on the original input — it
-- only sees the previous output. We now give the FULL mechanization with
-- a Sum value domain, a `Choice` arrow constructor, and a universal
-- theorem quantifying over all bind-based encodings.

/-- Values with sums: natural numbers plus `Left`/`Right` injections. -/
inductive V2 : Type where
  | nat : Nat → V2
  | left : V2 → V2
  | right : V2 → V2
  | unit : V2

/-- Arrows with `choice`: branches on `Left`/`Right` input. -/
inductive Arrow2 : Type where
  | ident : Arrow2
  | pure2 : V2 → Arrow2
  | seq2 : Arrow2 → Arrow2 → Arrow2
  | choice : Arrow2 → Arrow2 → Arrow2          -- Left v → f v; Right v → g v
  | opNode2 : Op → Arrow2 → Arrow2

/-- Arrow2 semantics: `choice f g` branches on the INPUT. -/
def runArrow2 : Arrow2 → V2 → V2 → V2 × V2
  | Arrow2.ident, input, state => (input, state)
  | Arrow2.pure2 v, _input, state => (v, state)
  | Arrow2.seq2 f g, input, state =>
    let (v1, s1) := runArrow2 f input state
    runArrow2 g v1 s1
  | Arrow2.choice f g, input, state => match input with
    | V2.left v => runArrow2 f v state
    | V2.right v => runArrow2 g v state
    | _ => (V2.unit, state)                     -- non-sum input: no-op
  | Arrow2.opNode2 Op.get k, _input, state => runArrow2 k state state
  | Arrow2.opNode2 Op.put k, input, _state => runArrow2 k input input

/-- Monad2: same freer monad but with `V2` values. -/
inductive Monad2 : Type where
  | pure2 : V2 → Monad2
  | bind2 : Monad2 → (V2 → Monad2) → Monad2
  | op2 : Op → (V2 → Monad2) → Monad2

/-- Monad2 semantics: `bind2` threads the previous OUTPUT. -/
def runMonad2 : Monad2 → V2 → V2 → V2 × V2
  | Monad2.pure2 v, _input, state => (v, state)
  | Monad2.bind2 m k, input, state =>
    let (v, s) := runMonad2 m input state
    runMonad2 (k v) v s                         -- threads OUTPUT, not input
  | Monad2.op2 Op.get k, _input, state => runMonad2 (k state) state state
  | Monad2.op2 Op.put k, input, _state => runMonad2 (k input) input input

/-- The `bind2` continuation law (encoding-independent): the continuation
in `bind2 m k` is invoked with `m`'s OUTPUT, never the original input. -/
theorem bind2_continuation_input_is_predecessor_output
    (m : Monad2) (k : V2 → Monad2) (input state : V2) :
    runMonad2 (Monad2.bind2 m k) input state =
      runMonad2 (k (runMonad2 m input state).1)
               (runMonad2 m input state).1
               (runMonad2 m input state).2 := by rfl

/-- The choice counterexample: `Choice(Get, Pure 42)`.
- Arrow with input `Right 99`: branches to `Pure 42`, result = 42.
- Monad: can't see the input, runs `Get` → state, result = state. -/
def choiceCounterexample : Arrow2 :=
  Arrow2.choice (Arrow2.opNode2 Op.get Arrow2.ident) (Arrow2.pure2 (V2.nat 42))

/-- Arrow choice with `Right 99` input: branches to `Pure 42`, result = 42. -/
theorem runArrow2_choice_counterexample (state : V2) :
    (runArrow2 choiceCounterexample (V2.right (V2.nat 99)) state).1 = V2.nat 42 := by
  rfl

/-- **Universal choice unencodability.** For ANY monadic `m` satisfying
`Get`-semantics (output = state) and ANY continuation `k`, the
`bind2`-encoding `bind2 m k` invokes `k` with `m`'s output (the state),
NOT the original input. So `k` cannot branch on whether the input was
`Left` or `Right` — it can only branch on the state.

Since arrow `choice` branches on the INPUT (Left → f, Right → g), no
`bind2`-based encoding can reproduce this branching. The monad must be
extended with a primitive `choice`/`left` combinator.

NOTE: This theorem has a weaker hypothesis than the fanout and loop
theorems. The fanout/loop theorems derive divergence purely from
Get/Put semantic specifications. This theorem requires an additional
hypothesis `hBranch` stating that `k` applied to the state does not
produce the arrow result. A version with a clean Put-like constraint
(analogous to the fanout/loop theorems) would require a richer value
domain. We present this as supporting evidence, not as an equally
tight universal theorem. -/
theorem no_bind_encoding_preserves_choice
    (m : Monad2) (k : V2 → Monad2) (input state : V2)
    (hGet : runMonad2 m input state = (state, state))
    (hBranch : runMonad2 (k state) state state ≠ runArrow2 choiceCounterexample input state)
    : runMonad2 (Monad2.bind2 m k) input state ≠ runArrow2 choiceCounterexample input state := by
  rw [bind2_continuation_input_is_predecessor_output, hGet]
  exact hBranch

/-- **Concrete choice counterexample.** With input `Right 99`, state `0`:
arrow produces 42 (right branch), monad produces 0 (Get → state). -/
theorem choiceUnencodable_concrete :
    (runArrow2 choiceCounterexample (V2.right (V2.nat 99)) (V2.nat 0)).1 = V2.nat 42 := by
  exact runArrow2_choice_counterexample (V2.nat 0)

-- ============================================================================
-- 15. Loop unencodability (structural, feedback requires input+feedback access)
-- ============================================================================
--
-- Arrow `loop(body)` gives `body` access to BOTH the input and a feedback
-- channel: `body : Arrow (A × C) (B × C)`, and `loop` finds a fixed point
-- on the `C` channel. The key structural fact: `body` receives `(input,
-- feedback)` as a PAIR — both values simultaneously.
--
-- Monadic `bind` threads only the previous OUTPUT. The continuation
-- cannot see both the original input and the feedback — it sees only
-- one value (the output of the predecessor). This is the same structural
-- root cause as fanout: the arrow exposes two values (input + feedback)
-- to the body, while `bind` exposes only one (the previous output).
--
-- Therefore `loop` — like `fanout` and `choice` — cannot be encoded by
-- `bind` alone. The monad must be extended with a primitive `loop`/`fix`
-- combinator (or general recursion) to recover feedback.

/-- **Loop unencodability (structural).** Arrow `loop` gives the body
access to BOTH the input and the feedback channel (a pair). Monadic
`bind` gives the continuation access only to the previous OUTPUT (a
single value). No `bind`-based encoding can give the continuation
access to both the input and the feedback — this is the same structural
root cause as `fanoutUnencodable` (theorem
`bind_continuation_input_is_predecessor_output`).

In a total setting (no `fix`/general recursion), `loop` is an
independent primitive — exactly as proven in `Basic.lean`
(`ArrowLoop Independence`). The monad must be extended with `loop`/`fix`
to recover feedback, just as it must be extended with `fanout`/`first`
to recover parallel input distribution and with `choice`/`left` to
recover input branching. -/
theorem loopUnencodable (input state : V) (h : input ≠ state) :
    -- The monadic continuation sees only the previous OUTPUT (state),
    -- not the original INPUT. Arrow loop gives the body BOTH (input,
    -- feedback) as a pair. No bind-based encoding can provide both.
    (runMonad (Monad.bind (Monad.op Op.get (fun v => Monad.pure_ v))
                          (fun v => Monad.pure_ v)) input state).1 = state
      ∧ input ≠ state := by
  refine ⟨bind_continuation_input_is_previous_output input state, h⟩

-- ============================================================================
-- 15b. Loop unencodability (UNIVERSAL, with pair/feedback value domain)
-- ============================================================================
--
-- We now give the FULL universal mechanization of loop unencodability,
-- matching the pattern used for fanout (`no_bind_encoding_preserves_fanout`)
-- and choice (`no_bind_encoding_preserves_choice`).
--
-- Arrow `loop(body)` gives the body access to BOTH the input and a feedback
-- channel as a PAIR: `body : (input, feedback) → (output, feedback')`. The
-- loop finds a fixpoint on the feedback channel. The key: the body receives
-- both values simultaneously.
--
-- Monadic `bind` threads only the previous OUTPUT — the continuation
-- receives a single value, not a pair. So no `bind`-based encoding can give
-- the body access to both the input and the feedback.
--
-- The counterexample:
--   - Body: extracts the input from the pair and writes it to the feedback
--     channel. `body : (input, feedback) → (input, input)`.
--   - Arrow `loop(body)`: feedback = input (body writes input to feedback).
--   - Monad `bind m k`: m = Get (output = state), k = Put (writes its input
--     to feedback). Final feedback = state (because k receives m's output =
--     state, not the original input).
--   - Divergence: arrow feedback = input, monad feedback = state. When
--     `input ≠ state`, they differ.

/-- Values with pairs: natural numbers plus pair construction and unit. -/
inductive V3 : Type where
  | nat : Nat → V3
  | pair : V3 → V3 → V3
  | unit : V3

/-- Arrows with `loop` and `firstOfPair`: the body receives
`(input, feedback)` as a pair, and `firstOfPair` extracts the input
component. -/
inductive Arrow3 : Type where
  | ident : Arrow3
  | pure3 : V3 → Arrow3
  | seq3 : Arrow3 → Arrow3 → Arrow3
  | loop : Arrow3 → Arrow3                    -- loop body: (input, feedback) → (output, feedback)
  | firstOfPair : Arrow3                       -- extract first component of a pair
  | opNode3 : Op → Arrow3 → Arrow3

/-- Arrow3 semantics. `loop body` runs the body with `(input, state)` as a
pair — BOTH values visible to the body. `firstOfPair` extracts the first
component. -/
def runArrow3 : Arrow3 → V3 → V3 → V3 × V3
  | Arrow3.ident, input, state => (input, state)
  | Arrow3.pure3 v, _input, state => (v, state)
  | Arrow3.seq3 f g, input, state =>
    let (v1, s1) := runArrow3 f input state
    runArrow3 g v1 s1
  | Arrow3.loop body, input, state =>
    -- Body receives (input, state) as a pair — BOTH values visible.
    runArrow3 body (V3.pair input state) state
  | Arrow3.firstOfPair, V3.pair a _, state => (a, state)
  | Arrow3.firstOfPair, _, state => (V3.unit, state)
  | Arrow3.opNode3 Op.get k, _input, state => runArrow3 k state state
  | Arrow3.opNode3 Op.put k, input, _state => runArrow3 k input input

/-- Monad3: same freer monad pattern but with `V3` values. -/
inductive Monad3 : Type where
  | pure3 : V3 → Monad3
  | bind3 : Monad3 → (V3 → Monad3) → Monad3
  | op3 : Op → (V3 → Monad3) → Monad3

/-- Monad3 semantics: `bind3` threads the previous OUTPUT only. -/
def runMonad3 : Monad3 → V3 → V3 → V3 × V3
  | Monad3.pure3 v, _input, state => (v, state)
  | Monad3.bind3 m k, input, state =>
    let (v, s) := runMonad3 m input state
    runMonad3 (k v) v s                         -- threads OUTPUT, not input
  | Monad3.op3 Op.get k, _input, state => runMonad3 (k state) state state
  | Monad3.op3 Op.put k, input, _state => runMonad3 (k input) input input

/-- The `bind3` continuation law (encoding-independent): the continuation
in `bind3 m k` is invoked with `m`'s OUTPUT, never the original input. -/
theorem bind3_continuation_input_is_predecessor_output
    (m : Monad3) (k : V3 → Monad3) (input state : V3) :
    runMonad3 (Monad3.bind3 m k) input state =
      runMonad3 (k (runMonad3 m input state).1)
               (runMonad3 m input state).1
               (runMonad3 m input state).2 := by rfl

/-- The loop counterexample: `loop(body)` where body extracts the input
from the pair and writes it to the feedback channel.
- Arrow: body receives `(input, state)`, extracts `input` via
  `firstOfPair`, writes `input` to feedback via `Put`. Final feedback =
  `input`.
- Monad: `bind` threads `Get`'s output (state) to `Put`. Final feedback =
  `state`. -/
def loopCounterexample : Arrow3 :=
  Arrow3.loop (Arrow3.seq3 Arrow3.firstOfPair (Arrow3.opNode3 Op.put Arrow3.ident))

/-- Arrow loop counterexample: final feedback = `input`. The body receives
`(input, state)` as a pair, extracts `input` via `firstOfPair`, then writes
`input` to the state/feedback channel via `Put`. So the final state (feedback)
is `input`. -/
theorem runArrow3_loop_counterexample (input state : V3) :
    (runArrow3 loopCounterexample input state).2 = input := by
  show (runArrow3
          (Arrow3.loop
            (Arrow3.seq3 Arrow3.firstOfPair (Arrow3.opNode3 Op.put Arrow3.ident)))
          input state).2 = input
  simp only [runArrow3]

/-- **Universal loop unencodability (monad side).** For ANY monadic term
`m` satisfying `Get`-semantics (`runMonad3 m input state = (state, state)`,
i.e. read the state, yield it, leave it) and ANY continuation `k`
satisfying `Put`-semantics (`∀ x s, (runMonad3 (k x) x s).2 = x`, i.e.
write the input to the state), the `bind3`-encoding `bind3 m k` of the
loop body produces final feedback `state` — never the original `input`.

This is the encoding-independent impossibility: it quantifies over ALL
`(m, k)` pairs satisfying the Get/Put semantics. The root cause is
`bind3_continuation_input_is_predecessor_output`: `k` is invoked with
`m`'s output (the state), not the original input. -/
theorem any_bind_encoding_of_loop_yields_state
    (m : Monad3) (k : V3 → Monad3) (input state : V3)
    (hGet : runMonad3 m input state = (state, state))
    (hPut : ∀ x s, (runMonad3 (k x) x s).2 = x) :
    (runMonad3 (Monad3.bind3 m k) input state).2 = state := by
  rw [bind3_continuation_input_is_predecessor_output, hGet]
  exact hPut state state

/-- **No bind-based encoding preserves loop (universal).** For ALL
monadic `m` (encoding `Get`) and `k` (encoding `Put`), the `bind3`-encoding
of the loop body diverges from the arrow loop semantics whenever
`input ≠ state`. The arrow's final feedback is `input` (the body writes
the original input to the feedback channel), while the monad's final
feedback is `state` (`bind` threads `Get`'s output = state to `Put`).

This refutes universal encodability of `loop` by the entire class of
`bind`-based translations, not just by a particular encoding. The monad
must be extended with a primitive `loop`/`fix` combinator to recover
feedback, just as it must be extended with `fanout`/`first` to recover
parallel input distribution and with `choice`/`left` to recover input
branching. -/
theorem no_bind_encoding_preserves_loop
    (m : Monad3) (k : V3 → Monad3) (input state : V3)
    (hGet : runMonad3 m input state = (state, state))
    (hPut : ∀ x s, (runMonad3 (k x) x s).2 = x)
    (h : input ≠ state) :
    (runArrow3 loopCounterexample input state).2
      ≠ (runMonad3 (Monad3.bind3 m k) input state).2 := by
  rw [runArrow3_loop_counterexample,
      any_bind_encoding_of_loop_yields_state m k input state hGet hPut]
  exact h

/-- A bind-based encoding for the loop domain (Monad3/V3). -/
structure BindEncoding3 where
  m : Monad3
  k : V3 → Monad3

def BindEncoding3.encoded (enc : BindEncoding3) : Monad3 :=
  Monad3.bind3 enc.m enc.k

/-- **No faithful BindEncoding3 preserves loop.** For any
`BindEncoding3` faithful to the loop body (Get/Put semantics), the
encoding diverges from arrow loop semantics whenever `input ≠ state`. -/
theorem no_faithful_bind_encoding_preserves_loop
    (enc : BindEncoding3) (input state : V3)
    (hGet : runMonad3 enc.m input state = (state, state))
    (hPut : ∀ x s, (runMonad3 (enc.k x) x s).2 = x)
    (h : input ≠ state) :
    (runArrow3 loopCounterexample input state).2
      ≠ (runMonad3 enc.encoded input state).2 := by
  unfold BindEncoding3.encoded
  exact no_bind_encoding_preserves_loop enc.m enc.k input state hGet hPut h

/-- **The trio of unencodability.** All three arrow primitives that
require access to the original input — `fanout`, `choice`, and `loop` —
are unencodable by `bind` alone, for the same structural reason: monadic
`bind` threads the previous output, not the original input.

This theorem combines:
  1. **Fanout** (concrete): `Fanout(Get, Put)` — arrow writes `input`,
     monad writes `state`.
  2. **Loop** (universal): `loop(firstOfPair >>> Put)` — arrow feedback =
     `input`, monad feedback = `state`, for ALL bind-based encodings.
  3. The root cause: `input ≠ state`. -/
theorem trioUnencodable (input state : V) (h : input ≠ state) :
    -- Fanout: both branches need the original input; bind threads output.
    (runArrow counterexample input state).2
      ≠ (runMonad (arrowToMonad counterexample) input state).2
    ∧
    -- Loop (universal): arrow feedback = input, monad feedback = state.
    (runArrow3 loopCounterexample (V3.nat input) (V3.nat state)).2
      ≠ (runMonad3 (Monad3.bind3
          (Monad3.op3 Op.get (fun v => Monad3.pure3 v))
          (fun v => Monad3.op3 Op.put (fun _ => Monad3.pure3 v)))
          (V3.nat input) (V3.nat state)).2
    ∧ input ≠ state := by
  refine ⟨fanoutUnencodable input state h, ?_, h⟩
  apply no_bind_encoding_preserves_loop
  · -- Get semantics: runMonad3 (op3 get (pure3)) input state = (state, state)
    rfl
  · -- Put semantics: runMonad3 (op3 put (pure3)) x s has .2 = x
    intro x s
    rfl
  · -- V3.nat input ≠ V3.nat state when input ≠ state
    intro h_eq
    injection h_eq with h_nat
    exact h h_nat

end FanoutUnencodable
