# Arrow Calculus Prototype Implementation

This is a reference implementation of the arrow calculus formalism, suitable for testing the hypotheses.

---

## Data Structures (Pseudocode / Haskell-like)

### Types and Values

```haskell
-- Type representation
data Type
  = TVar String              -- type variable (a, b, ...)
  | TInt                     -- Int type
  | TString                  -- String type
  | TBool                    -- Bool type
  | TProduct Type Type       -- (τ × σ)
  | TSum Type Type           -- (τ + σ)
  | TList Type               -- [τ]
  | TFunction Type Type      -- τ → σ (pure function)
  | TArrow Type Type         -- τ ~> σ (arrow type)
  | TUnit                    -- () - unit type

-- Value representation
data Value
  = VInt Int
  | VString String
  | VBool Bool
  | VUnit
  | VProduct Value Value
  | VLeft Value
  | VRight Value
  | VList [Value]
  | VArrow ArrowValue        -- an arrow as a value (for higher-order)

-- Arrow value representation (abstract)
data ArrowValue
  = AArr (Value → Value)                 -- arr f: pure function lifted
  | AComp ArrowValue ArrowValue          -- f >>> g: composition
  | AFirst ArrowValue                    -- first f: operate on first component
  | AChoice ArrowValue ArrowValue        -- choice f g: route based on Left/Right
  | ALoop ArrowValue State               -- loop f: feedback with state
  | APrim String                         -- primitive: app, etc.

-- Program AST
data Expr
  = Var String
  | Lit Value
  | Arr Expr                             -- arr e
  | Comp Expr Expr                       -- e >>> e'
  | First Expr                           -- first e
  | Choice Expr Expr                     -- choice e e'
  | Loop Expr                            -- loop e
  | App Expr Expr                        -- function application (e e')
  | BinOp String Expr Expr               -- +, -, *, ==, <, etc.
  | If Expr Expr Expr                    -- if e then e1 else e2
  | Lambda String Expr                   -- λx. e (for reference; translate to arrows)
  | Let String Expr Expr                 -- let x = e in e'

-- Type environment (context)
type Context = [(String, Type)]

-- Evaluation environment (variable bindings)
type Env = [(String, Value)]
```

---

## Type Checking

```haskell
-- Type inference
infer :: Context → Expr → Either TypeError Type

-- Variable
infer ctx (Var x) =
  case lookup x ctx of
    Just t  → Right t
    Nothing → Left (UnboundVariable x)

-- Literal
infer ctx (Lit (VInt _))  = Right TInt
infer ctx (Lit (VBool _)) = Right TBool
infer ctx (Lit (VString _)) = Right TString
infer ctx (Lit VUnit) = Right TUnit

-- Arrow: arr e
-- Requires: e : τ → σ
-- Produces: τ ~> σ
infer ctx (Arr e) = do
  t ← infer ctx e
  case t of
    TFunction τ σ → Right (TArrow τ σ)
    _             → Left (ExpectedFunction t)

-- Composition: f >>> g
-- Requires: f : τ ~> σ, g : σ ~> ρ
-- Produces: τ ~> ρ
infer ctx (Comp f g) = do
  TArrow τ σ ← infer ctx f
  TArrow σ' ρ ← infer ctx g
  if σ == σ'
    then Right (TArrow τ ρ)
    else Left (TypeMismatch σ σ')

-- First: first e
-- Requires: e : τ ~> σ
-- Produces: (τ × ρ) ~> (σ × ρ)  [ρ is unconstrained]
infer ctx (First e) = do
  TArrow τ σ ← infer ctx e
  -- Note: ρ is a fresh type variable, left unconstrained
  let ρ = TVar ("ρ_" ++ fresh_id)
  Right (TArrow (TProduct τ ρ) (TProduct σ ρ))

-- Choice: choice f g
-- Requires: f : τ ~> ρ, g : σ ~> ρ
-- Produces: (τ + σ) ~> ρ
infer ctx (Choice f g) = do
  TArrow τ ρ ← infer ctx f
  TArrow σ ρ' ← infer ctx g
  if ρ == ρ'
    then Right (TArrow (TSum τ σ) ρ)
    else Left (TypeMismatch ρ ρ')

-- Loop: loop e
-- Requires: e : (τ × ρ) ~> (σ × ρ)
-- Produces: τ ~> σ
infer ctx (Loop e) = do
  TArrow (TProduct τ ρ) (TProduct σ ρ') ← infer ctx e
  if ρ == ρ'
    then Right (TArrow τ σ)
    else Left (StateTypeMismatch ρ ρ')

-- Lambda: λx. e
-- Produces: τ → σ where τ is parameter type, σ is body type
infer ctx (Lambda x e) = do
  -- τ is a fresh type variable
  let τ = TVar ("τ_" ++ fresh_id)
  σ ← infer ((x, τ) : ctx) e
  Right (TFunction τ σ)

-- Application: f e
-- Requires: f : τ → σ, e : τ
-- Produces: σ
infer ctx (App f e) = do
  TFunction τ σ ← infer ctx f
  τ' ← infer ctx e
  if τ == τ'
    then Right σ
    else Left (TypeMismatch τ τ')

-- Binary operations
infer ctx (BinOp "+" e1 e2) = do
  TInt ← infer ctx e1
  TInt ← infer ctx e2
  Right TInt

infer ctx (BinOp "==" e1 e2) = do
  τ ← infer ctx e1
  τ' ← infer ctx e2
  if τ == τ'
    then Right TBool
    else Left (TypeMismatch τ τ')

-- If-then-else
infer ctx (If cond e1 e2) = do
  TBool ← infer ctx cond
  σ ← infer ctx e1
  σ' ← infer ctx e2
  if σ == σ'
    then Right σ
    else Left (BranchTypeMismatch σ σ')

-- Let binding
infer ctx (Let x e body) = do
  τ ← infer ctx e
  infer ((x, τ) : ctx) body
```

---

## Evaluation

```haskell
-- Evaluate expression to value
eval :: Env → Expr → Either EvalError Value

eval env (Lit v) = Right v

eval env (Var x) =
  case lookup x env of
    Just v  → Right v
    Nothing → Left (UnboundVariable x)

-- Lift pure function to arrow
eval env (Arr e) = do
  f ← eval env e
  -- e should evaluate to a function
  Right (VArrow (AArr (λv. eval_function f v)))

-- Composition
eval env (Comp f g) = do
  VArrow af ← eval env f
  VArrow ag ← eval env g
  Right (VArrow (AComp af ag))

-- First
eval env (First e) = do
  VArrow ae ← eval env e
  Right (VArrow (AFirst ae))

-- Choice
eval env (Choice f g) = do
  VArrow af ← eval env f
  VArrow ag ← eval env g
  Right (VArrow (AChoice af ag))

-- Loop
eval env (Loop e) = do
  VArrow ae ← eval env e
  Right (VArrow (ALoop ae init_state))

-- Lambda: package as a function value
eval env (Lambda x e) = do
  -- Store closure: (parameter name, body, environment)
  Right (closure x e env)

-- Application: f e
eval env (App f arg) = do
  func ← eval env f
  value ← eval env arg
  case func of
    (Closure x body closure_env) →
      eval ((x, value) : closure_env) body
    _ → Left (NotAFunction func)

-- Binary operations
eval env (BinOp "+" e1 e2) = do
  VInt n1 ← eval env e1
  VInt n2 ← eval env e2
  Right (VInt (n1 + n2))

eval env (BinOp "-" e1 e2) = do
  VInt n1 ← eval env e1
  VInt n2 ← eval env e2
  Right (VInt (n1 - n2))

eval env (BinOp "*" e1 e2) = do
  VInt n1 ← eval env e1
  VInt n2 ← eval env e2
  Right (VInt (n1 * n2))

eval env (BinOp "==" e1 e2) = do
  v1 ← eval env e1
  v2 ← eval env e2
  Right (VBool (v1 == v2))

eval env (BinOp "<" e1 e2) = do
  VInt n1 ← eval env e1
  VInt n2 ← eval env e2
  Right (VBool (n1 < n2))

-- If-then-else
eval env (If cond e1 e2) = do
  VBool b ← eval env cond
  if b
    then eval env e1
    else eval env e2

-- Let binding
eval env (Let x e body) = do
  v ← eval env e
  eval ((x, v) : env) body
```

---

## Arrow Execution

```haskell
-- Execute an arrow with input value
run_arrow :: ArrowValue → Value → Either EvalError Value

-- Basic arrow: arr f
run_arrow (AArr f) v = f v

-- Composition: f >>> g
run_arrow (AComp af ag) v = do
  intermediate ← run_arrow af v
  run_arrow ag intermediate

-- First: operates on first component of pair
run_arrow (AFirst af) (VProduct a b) = do
  a' ← run_arrow af a
  Right (VProduct a' b)
run_arrow (AFirst af) v = Left (ExpectedProduct v)

-- Choice: route based on Left/Right
run_arrow (AChoice af ag) (VLeft a) = do
  run_arrow af a
run_arrow (AChoice af ag) (VRight b) = do
  run_arrow ag b
run_arrow (AChoice af ag) v = Left (ExpectedSum v)

-- Loop: feedback (state machine)
-- This is tricky: we need a termination condition
-- For now, use a fixed iteration limit
run_arrow (ALoop step state) v =
  loop_iterate step v state max_iterations
  where
    max_iterations = 100
    loop_iterate step v state 0 =
      Left (MaxIterationsExceeded)
    loop_iterate step v (VProduct v_current s) n =
      case run_arrow step (VProduct v s) of
        Left err → Left err
        Right (VProduct v_out s_out) →
          if s_out == s  -- state unchanged → termination
            then Right v_out
            else loop_iterate step v_out s_out (n-1)
```

---

## Lambda to Arrow Translation

```haskell
-- Translate lambda term to arrow term
translate_to_arrow :: Expr → Expr

-- Identity
translate_to_arrow (Lambda x (Var y)) | x == y =
  Arr (Lambda "_" (Var "_"))  -- λ_. _ (identity)

-- Constant
translate_to_arrow (Lambda x (Lit c)) =
  Arr (Lambda "_" (Lit c))

-- Abstraction over computation
translate_to_arrow (Lambda x e) =
  Arr (Lambda x (translate_to_arrow e))

-- Application: f e becomes (arr f) >>> app >>> (arr e)
-- This is more complex; we need to handle function composition
translate_to_arrow (App f e) =
  let f' = translate_to_arrow f
      e' = translate_to_arrow e
  in Comp f' e'

-- Already an arrow
translate_to_arrow (Comp f g) =
  Comp (translate_to_arrow f) (translate_to_arrow g)

-- Other expressions
translate_to_arrow e = e
```

---

## Example Programs (in Expr AST)

### Example 1: Identity

```haskell
-- Lambda version
id_lambda = Lambda "x" (Var "x")

-- Arrow version
id_arrow = Arr (Lambda "x" (Var "x"))

-- Type: a ~> a
-- Execution: id_arrow `run_arrow` (VInt 5) ⟹ VInt 5
```

### Example 2: Increment

```haskell
add1 = Arr (Lambda "x" (BinOp "+" (Var "x") (Lit (VInt 1))))

-- Type: Int ~> Int
-- Execution: add1 `run_arrow` (VInt 5) ⟹ VInt 6
```

### Example 3: Composition (add1 then mul2)

```haskell
add1 = Arr (Lambda "x" (BinOp "+" (Var "x") (Lit (VInt 1))))
mul2 = Arr (Lambda "x" (BinOp "*" (Var "x") (Lit (VInt 2))))

composed = Comp add1 mul2

-- Type: Int ~> Int
-- Execution: composed `run_arrow` (VInt 5) ⟹ VInt 12
--   Step 1: add1 · 5 ⟹ 6
--   Step 2: mul2 · 6 ⟹ 12
```

### Example 4: Higher-order (applyTwice)

```haskell
-- In arrow form: f ~> (a ~> a)
-- applyTwice f = f >>> f

applyTwice f = Comp f f

-- Executing:
-- applyTwice (arr (λx. x+1)) · 5
-- ⟹ (arr (λx. x+1)) >>> (arr (λx. x+1)) · 5
-- ⟹ ((λx. x+1) · 5) ; ((λx. x+1) · 6)
-- ⟹ 7
```

### Example 5: Feedback (Counter)

```haskell
-- counter : () ~> Int
-- counter = loop step
--   where step : (() × Int) ~> (Int × Int)
--         step = arr (λ((), s). (s, s+1))

step = Arr (Lambda "(unit, state)"
  (BinOp "pair"
    (Var "state")
    (BinOp "+" (Var "state") (Lit (VInt 1)))))

counter = Loop step

-- Execution: counter `run_arrow` VUnit
-- ⟹ step · ((), 0) ⟹ (0, 1)
-- ⟹ step · ((), 1) ⟹ (1, 2)
-- ... until termination (state unchanged)
```

### Example 6: Factorial via Feedback

```haskell
-- factorial : Int ~> Int
-- factorial = loop step
--   where step : (Int × (Int, Int)) ~> (Int × (Int, Int))
--         step = arr (λ(n, (acc, _)).
--           if n <= 1
--             then (acc, (n, acc))
--             else ((n-1)*acc, (n-1, (n-1)*acc)))

step_body =
  If (BinOp "<=" (Var "n") (Lit (VInt 1)))
    (BinOp "pair" (Var "acc") (BinOp "pair" (Var "n") (Var "acc")))
    (BinOp "pair"
      (BinOp "*" (Var "n") (Var "acc"))
      (BinOp "pair"
        (BinOp "-" (Var "n") (Lit (VInt 1)))
        (BinOp "*" (BinOp "-" (Var "n") (Lit (VInt 1))) (Var "acc"))))

step = Arr (Lambda "(n, (acc, _))" step_body)

factorial = Loop step

-- Execution: factorial `run_arrow` (VInt 5)
-- ⟹ repeatedly applies step with state
-- ⟹ VInt 120
```

---

## Testing Framework

```haskell
-- Test result
data TestResult = Pass String | Fail String String

-- Run a test
run_test :: String → (Either Error Value) → Value → TestResult
run_test name result expected =
  case result of
    Left err → Fail name (show err) (show expected)
    Right actual →
      if actual == expected
        then Pass name
        else Fail name (show actual) (show expected)

-- Test suite for Phase 1
test_phase_1 = [
  run_test "identity"
    (run_arrow id_arrow (VInt 5))
    (VInt 5),

  run_test "increment"
    (run_arrow add1 (VInt 5))
    (VInt 6),

  run_test "composition"
    (run_arrow composed (VInt 5))
    (VInt 12),

  run_test "higher-order (applyTwice)"
    (run_arrow (applyTwice add1) (VInt 5))
    (VInt 7),

  run_test "factorial(5)"
    (run_arrow factorial (VInt 5))
    (VInt 120),
]
```

---

## Key Implementation Decisions

1. **Arrow values as abstract data:** `ArrowValue` is an enumeration of arrow constructs, not raw functions. This allows inspection and composition.

2. **Big-step evaluation:** We use big-step semantics for simplicity; small-step is equivalent but more verbose.

3. **Loop termination:** We use a fixed iteration limit + state equality check. In a full implementation, this would be a handler concern (Sanada's model).

4. **Type inference:** Simplified; a real implementation would use constraint solving and unification.

5. **Lambda-to-arrow translation:** Wrapped in `arr`; more sophisticated translations (avoiding unnecessary lifting) are possible but would complicate the implementation.

---

## Next Steps

1. Implement this in a concrete language (Rust, Haskell, Python, etc.)
2. Run test suite to validate formalism
3. Extend with more examples (recursion patterns, effects)
4. Measure expressiveness against lambda calculus
