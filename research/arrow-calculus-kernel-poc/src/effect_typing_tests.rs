// Deep Dive: Effect Typing for Arrows
//
// Key questions:
// 1. Can we statically infer the *effect row* of an arrow computation — the
//    set of operations it may perform — without running it?
// 2. Are handlers *effect eliminators*: does `handle_state` remove {Get, Put}
//    from the effect row, leaving foreign ops through (pass-through)?
// 3. Can a handler stack be checked for completeness — is any effect left
//    unhandled — purely from the inferred effect rows?
//
// This is the arrow-calculus analogue of effect inference in algebraic-effect
// systems (Bauer & Pretnar, Frank, Koka). The freer-arrow `Comp` from Phase 2
// uses `Rc<dyn Fn>` continuations, which are not statically traversable. For
// inference we therefore use a *static computation tree* `IComp` that mirrors
// `Comp` but stores continuations as explicit sub-trees (`Box<IComp>`), so the
// whole computation can be walked and its operations collected.
//
//   IComp ::= Pure IValue
//           | Op IOp IValue Type IComp   -- op, arg, result type, continuation
//
// The effect of a tree is the set of operations appearing in it:
//
//   effect(Pure v)        = ∅
//   effect(Op op _ _ k)   = {op} ∪ effect(k)
//
// A handler *removes* its handled operations from the effect row (handler as
// effect eliminator), and pass-through leaves foreign operations in place:
//
//   effect(handle_state c)    = effect(c) \ {Get, Put}
//   effect(handle_io c)       = effect(c) \ {Read, Write}
//   effect(handle_exception c)= effect(c) \ {Throw}
//
// A computation is safe to run when its remaining effect row is empty after
// the handler stack has been applied.

use std::collections::HashSet;
use std::fmt;

// ============================================================================
// Types (adapted from the HM type system in type_inference_tests.rs)
// ============================================================================

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Int,
    Bool,
    String,
    Unit,
    Var(String),
    Arrow(Box<Type>, Box<Type>),       // a ~> b
    List(Box<Type>),                   // [a]
    Product(Box<Type>, Box<Type>),     // (a, b)
    Sum(Box<Type>, Box<Type>),         // (a + b)
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Int => write!(f, "Int"),
            Type::Bool => write!(f, "Bool"),
            Type::String => write!(f, "String"),
            Type::Unit => write!(f, "()"),
            Type::Var(name) => write!(f, "{}", name),
            Type::Arrow(a, b) => write!(f, "{} ~> {}", a, b),
            Type::List(t) => write!(f, "[{}]", t),
            Type::Product(a, b) => write!(f, "({} × {})", a, b),
            Type::Sum(a, b) => write!(f, "({} + {})", a, b),
        }
    }
}

// ============================================================================
// Effect Operations (mirrors the Phase 2 `Op` enum)
// ============================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IOp {
    Get,
    Put,
    Read,
    Write,
    Throw,
}

impl fmt::Display for IOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IOp::Get => write!(f, "Get"),
            IOp::Put => write!(f, "Put"),
            IOp::Read => write!(f, "Read"),
            IOp::Write => write!(f, "Write"),
            IOp::Throw => write!(f, "Throw"),
        }
    }
}

/// All operations, in canonical order for stable display.
const ALL_OPS: [IOp; 5] = [IOp::Get, IOp::Put, IOp::Read, IOp::Write, IOp::Throw];

// ============================================================================
// Effect Rows
// ============================================================================
//
// An effect row is the set of operations a computation may perform. This is
// the concrete (ground) form; polymorphic rows with a row-variable tail are
// modelled separately by `RowEffect` below.

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Effect {
    ops: HashSet<IOp>,
}

impl Effect {
    /// The empty effect row ∅ — a pure computation.
    pub fn empty() -> Self {
        Effect {
            ops: HashSet::new(),
        }
    }

    /// A singleton effect row {op}.
    pub fn singleton(op: IOp) -> Self {
        let mut ops = HashSet::new();
        ops.insert(op);
        Effect { ops }
    }

    /// Build an effect row from a collection of operations.
    pub fn from_ops<I: IntoIterator<Item = IOp>>(iter: I) -> Self {
        Effect {
            ops: iter.into_iter().collect(),
        }
    }

    /// Insert an operation into the row.
    pub fn insert(&mut self, op: IOp) {
        self.ops.insert(op);
    }

    /// Does the row contain this operation?
    pub fn contains(&self, op: IOp) -> bool {
        self.ops.contains(&op)
    }

    /// Union of two effect rows: ε₁ ∪ ε₂.
    pub fn union(&self, other: &Effect) -> Effect {
        Effect {
            ops: self.ops.union(&other.ops).copied().collect(),
        }
    }

    /// Difference of two effect rows: ε₁ \ ε₂.
    ///
    /// This is the handler-as-eliminator rule: subtracting a handler's owned
    /// operations from a computation's effect yields the remaining effect.
    pub fn difference(&self, other: &Effect) -> Effect {
        Effect {
            ops: self.ops.difference(&other.ops).copied().collect(),
        }
    }

    /// Is this effect row a subset of `other`?
    pub fn is_subset(&self, other: &Effect) -> bool {
        self.ops.is_subset(&other.ops)
    }

    /// Is the effect row empty (∅)?
    pub fn is_empty(&self) -> bool {
        self.ops.is_empty()
    }

    /// Iterate over the operations in canonical order.
    pub fn iter_sorted(&self) -> Vec<IOp> {
        ALL_OPS.iter().copied().filter(|op| self.ops.contains(op)).collect()
    }
}

impl fmt::Display for Effect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let ops = self.iter_sorted();
        if ops.is_empty() {
            return write!(f, "∅");
        }
        let names: Vec<String> = ops.iter().map(|op| op.to_string()).collect();
        write!(f, "{{{}}}", names.join(", "))
    }
}

// ============================================================================
// Effect-Typed Computations
// ============================================================================

/// A value type paired with an effect row: `τ / ε`.
#[derive(Debug, Clone, PartialEq)]
pub struct EffectType {
    pub ty: Type,
    pub effect: Effect,
}

impl fmt::Display for EffectType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} / {}", self.ty, self.effect)
    }
}

// ============================================================================
// Inference-Friendly Values
// ============================================================================
//
// `IValue` mirrors the Phase 2 `Value` but adds a `Received(Type)` variant
// representing the result handed to a continuation by an operation. This lets
// us reconstruct the type flowing through the tree without running it.

#[derive(Debug, Clone, PartialEq)]
pub enum IValue {
    Int(i32),
    Bool(bool),
    Str(String),
    Unit,
    Product(Box<IValue>, Box<IValue>),
    List(Vec<IValue>),
    Left(Box<IValue>),
    Right(Box<IValue>),
    /// A value received from an operation result, carrying its type.
    Received(Type),
}

/// Infer the `Type` of an `IValue`.
pub fn type_of_value(v: &IValue) -> Type {
    match v {
        IValue::Int(_) => Type::Int,
        IValue::Bool(_) => Type::Bool,
        IValue::Str(_) => Type::String,
        IValue::Unit => Type::Unit,
        IValue::Product(a, b) => Type::Product(
            Box::new(type_of_value(a)),
            Box::new(type_of_value(b)),
        ),
        IValue::List(vs) => match vs.first() {
            Some(e) => Type::List(Box::new(type_of_value(e))),
            None => Type::List(Box::new(Type::Var("a".to_string()))),
        },
        IValue::Left(a) => Type::Sum(
            Box::new(type_of_value(a)),
            Box::new(Type::Var("b".to_string())),
        ),
        IValue::Right(b) => Type::Sum(
            Box::new(Type::Var("a".to_string())),
            Box::new(type_of_value(b)),
        ),
        IValue::Received(t) => t.clone(),
    }
}

// ============================================================================
// Static Computation Tree (for inference)
// ============================================================================
//
//   IComp ::= Pure IValue
//           | Op IOp IValue Type IComp
//
// The `Op` node carries: the operation, its argument value, the *result type*
// (the type the continuation receives from the operation), and the
// continuation as an explicit sub-tree. This is the statically-traversable
// analogue of Phase 2's `Comp = Pure v | Op op arg (Rc<dyn Fn>)`.

#[derive(Debug, Clone, PartialEq)]
pub enum IComp {
    Pure(IValue),
    Op(IOp, IValue, Type, Box<IComp>),
}

// --- Builders ---------------------------------------------------------------
//
// Each builder mirrors a Phase 2 operation constructor but produces a static
// tree. The continuation is an explicit `IComp`, so the whole computation can
// be traversed for inference.

/// Lift a pure value into a computation: `pure v : τ ~> τ / ∅`.
pub fn ipure(v: IValue) -> IComp {
    IComp::Pure(v)
}

/// `get` — read the state. Arg `()`, result type `state_ty`, continuation
/// receives the state. `get : () ~> State / {Get}`.
pub fn iget(state_ty: Type, k: IComp) -> IComp {
    IComp::Op(IOp::Get, IValue::Unit, state_ty, Box::new(k))
}

/// `get` that simply returns the state it read.
pub fn iget_pure(state_ty: Type) -> IComp {
    iget(state_ty.clone(), ipure(IValue::Received(state_ty)))
}

/// `put s` — overwrite the state. Arg `s`, result type `()`. `put : State ~> () / {Put}`.
pub fn iput(arg: IValue, k: IComp) -> IComp {
    IComp::Op(IOp::Put, arg, Type::Unit, Box::new(k))
}

/// `put s` that returns Unit.
pub fn iput_pure(arg: IValue) -> IComp {
    iput(arg, ipure(IValue::Unit))
}

/// `read` — read one input. Arg `()`, result type `String`. `read : () ~> String / {Read}`.
pub fn iread(k: IComp) -> IComp {
    IComp::Op(IOp::Read, IValue::Unit, Type::String, Box::new(k))
}

/// `read` that returns the string it read.
pub fn iread_pure() -> IComp {
    iread(ipure(IValue::Received(Type::String)))
}

/// `write s` — emit one output. Arg `s`, result type `()`. `write : String ~> () / {Write}`.
pub fn iwrite(arg: IValue, k: IComp) -> IComp {
    IComp::Op(IOp::Write, arg, Type::Unit, Box::new(k))
}

/// `write s` that returns Unit.
pub fn iwrite_pure(arg: IValue) -> IComp {
    iwrite(arg, ipure(IValue::Unit))
}

/// `throw msg` — raise an exception. Result type is polymorphic (`α`) because
/// the continuation is never invoked. `throw : String ~> α / {Throw}`.
pub fn ithrow(msg: &str, result_ty: Type, k: IComp) -> IComp {
    IComp::Op(
        IOp::Throw,
        IValue::Str(msg.to_string()),
        result_ty,
        Box::new(k),
    )
}

/// `throw msg` that never returns (continuation is unreachable).
pub fn ithrow_pure(msg: &str) -> IComp {
    let a = Type::Var("a".to_string());
    ithrow(msg, a.clone(), ipure(IValue::Received(a)))
}

// ============================================================================
// Effect Inference
// ============================================================================
//
//   infer(Pure v)          = (type_of_value(v), ∅)
//   infer(Op op _ _ k)     = (ty(k), {op} ∪ effect(k))
//
// where (ty(k), effect(k)) = infer(k). The result type of an `Op` node is the
// type of its continuation; the operation's own result type is only the type
// handed *to* the continuation.

pub fn infer_effect(comp: &IComp) -> EffectType {
    match comp {
        IComp::Pure(v) => EffectType {
            ty: type_of_value(v),
            effect: Effect::empty(),
        },
        IComp::Op(op, _arg, _result_ty, k) => {
            let k_et = infer_effect(k);
            EffectType {
                ty: k_et.ty,
                effect: Effect::singleton(*op).union(&k_et.effect),
            }
        }
    }
}

// ============================================================================
// Handler Effect Elimination
// ============================================================================
//
// A handler removes its owned operations from the effect row; foreign
// operations remain (pass-through). This is exactly the typing counterpart of
// the Phase 2 pass-through semantics.
//
//   effect(handle_state c)     = effect(c) \ {Get, Put}
//   effect(handle_io c)        = effect(c) \ {Read, Write}
//   effect(handle_exception c) = effect(c) \ {Throw}

/// The set of operations a state handler owns.
pub fn state_handled() -> Effect {
    Effect::from_ops([IOp::Get, IOp::Put])
}

/// The set of operations an IO handler owns.
pub fn io_handled() -> Effect {
    Effect::from_ops([IOp::Read, IOp::Write])
}

/// The set of operations an exception handler owns.
pub fn exception_handled() -> Effect {
    Effect::from_ops([IOp::Throw])
}

/// Effect of a computation after one handler: `effect(c) \ handled`.
pub fn effect_after_handler(comp_effect: &Effect, handled_ops: &Effect) -> Effect {
    comp_effect.difference(handled_ops)
}

/// Effect of a computation after a whole handler stack (applied left to right,
/// i.e. innermost handler first).
pub fn effect_after_stack(comp_effect: &Effect, stack: &[Effect]) -> Effect {
    let mut e = comp_effect.clone();
    for handled in stack {
        e = e.difference(handled);
    }
    e
}

// ============================================================================
// Effect Safety (Unhandled-Effect Detection)
// ============================================================================

/// The outcome of checking a remaining effect row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Safety {
    /// The effect row is empty — the computation is safe to run.
    Safe,
    /// Operations remain unhandled — running would be a runtime error.
    Unhandled(Vec<IOp>),
}

impl fmt::Display for Safety {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Safety::Safe => write!(f, "safe (no unhandled effects)"),
            Safety::Unhandled(ops) => {
                let names: Vec<String> = ops.iter().map(|op| op.to_string()).collect();
                write!(f, "unhandled effects: {{{}}}", names.join(", "))
            }
        }
    }
}

/// Check whether a remaining effect row is safe (empty) or carries unhandled
/// operations. This is the static counterpart of Phase 2's `run` returning
/// `RunError::UnhandledOp`.
pub fn check_safety(remaining: &Effect) -> Safety {
    if remaining.is_empty() {
        Safety::Safe
    } else {
        Safety::Unhandled(remaining.iter_sorted())
    }
}

/// Full safety check: infer the effect of a computation, apply a handler
/// stack, and report whether anything remains unhandled.
pub fn check_computation(comp: &IComp, stack: &[Effect]) -> Safety {
    let et = infer_effect(comp);
    let remaining = effect_after_stack(&et.effect, stack);
    check_safety(&remaining)
}

// ============================================================================
// Polymorphic Effect Rows (Bonus)
// ============================================================================
//
// A ground `Effect` is a closed set of operations. For polymorphism we extend
// the row with an optional *row variable* `ρ` standing for an unknown tail of
// foreign operations. This mirrors row-polymorphic effect systems (Koka,
// Frank): a computation may have effect `{Get, Put, ρ}` — it performs Get and
// Put, plus whatever `ρ` turns out to be.
//
// A handler eliminates its own operations from the known part and *leaves the
// row variable intact* (the unknown tail may still contain foreign ops that
// pass through). Two rows unify when their known operations agree and their
// row variables can be reconciled.

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct RowEffect {
    ops: HashSet<IOp>,
    /// Optional row variable `ρ` — an unknown tail of operations.
    row_var: Option<String>,
}

impl RowEffect {
    /// A closed (ground) effect row with no row variable.
    pub fn closed(ops: &[IOp]) -> Self {
        RowEffect {
            ops: ops.iter().copied().collect(),
            row_var: None,
        }
    }

    /// An effect row with a row-variable tail.
    pub fn open(ops: &[IOp], row_var: &str) -> Self {
        RowEffect {
            ops: ops.iter().copied().collect(),
            row_var: Some(row_var.to_string()),
        }
    }

    /// A pure row: just the row variable `ρ` (no known ops).
    pub fn var(row_var: &str) -> Self {
        RowEffect {
            ops: HashSet::new(),
            row_var: Some(row_var.to_string()),
        }
    }

    /// Insert a known operation.
    pub fn insert(&mut self, op: IOp) {
        self.ops.insert(op);
    }

    /// Does the row contain this known operation?
    pub fn contains(&self, op: IOp) -> bool {
        self.ops.contains(&op)
    }

    /// Does the row have a row-variable tail?
    pub fn has_row_var(&self) -> bool {
        self.row_var.is_some()
    }

    /// The row variable name, if any.
    pub fn row_var_name(&self) -> Option<&str> {
        self.row_var.as_deref()
    }

    /// Handler elimination on a polymorphic row: remove the handler's owned
    /// operations from the *known* set; the row variable is preserved because
    /// foreign (unknown) ops pass through.
    pub fn eliminate(&self, handled: &Effect) -> RowEffect {
        RowEffect {
            ops: self.ops.difference(&handled.ops).copied().collect(),
            row_var: self.row_var.clone(),
        }
    }

    /// Unify two effect rows. Two rows unify if:
    ///   - their known operations are compatible (no conflicting ground ops),
    ///   - and at least one side has a row variable that can absorb the
    ///     other's extra operations, or both are ground and equal.
    ///
    /// Returns the unified row on success.
    pub fn unify(&self, other: &RowEffect) -> Option<RowEffect> {
        // Union of known operations.
        let mut ops: HashSet<IOp> = self.ops.union(&other.ops).copied().collect();

        // If both sides are ground, they must be equal.
        match (&self.row_var, &other.row_var) {
            (None, None) => {
                if self.ops == other.ops {
                    Some(RowEffect { ops, row_var: None })
                } else {
                    None
                }
            }
            // One side has a row variable: it absorbs the other's extra ops.
            (Some(rv), None) => {
                let _ = &mut ops;
                Some(RowEffect {
                    ops,
                    row_var: Some(rv.clone()),
                })
            }
            (None, Some(rv)) => Some(RowEffect {
                ops,
                row_var: Some(rv.clone()),
            }),
            // Both have row variables: unify the variables (keep one name).
            (Some(rv1), Some(rv2)) => Some(RowEffect {
                ops,
                row_var: Some(if rv1 == rv2 {
                    rv1.clone()
                } else {
                    format!("{}|{}", rv1, rv2)
                }),
            }),
        }
    }
}

impl fmt::Display for RowEffect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut parts: Vec<String> = ALL_OPS
            .iter()
            .filter(|op| self.ops.contains(op))
            .map(|op| op.to_string())
            .collect();
        if let Some(rv) = &self.row_var {
            parts.push(rv.clone());
        }
        if parts.is_empty() {
            write!(f, "∅")
        } else {
            write!(f, "{{{}}}", parts.join(", "))
        }
    }
}

// ============================================================================
// Example Programs (static trees)
// ============================================================================

/// `get >>> put` — read state then write it back. Effect {Get, Put}.
pub fn prog_get_put() -> IComp {
    let s = Type::Var("State".to_string());
    iget(s.clone(), iput_pure(IValue::Received(s)))
}

/// `read >>> write` — echo one input to output. Effect {Read, Write}.
pub fn prog_read_write() -> IComp {
    iread(iwrite_pure(IValue::Received(Type::String)))
}

/// `get >>> throw` — read state then raise. Effect {Get, Throw}.
pub fn prog_get_throw() -> IComp {
    let s = Type::Var("State".to_string());
    iget(s, ithrow_pure("boom"))
}

/// A computation using all five operations: get, put, read, write, throw.
/// Effect {Get, Put, Read, Write, Throw}.
pub fn prog_all_five() -> IComp {
    let s = Type::Var("State".to_string());
    iget(
        s.clone(),
        iput(
            IValue::Received(s),
            iread(iwrite(IValue::Received(Type::String), ithrow_pure("done"))),
        ),
    )
}

/// `read >>> get >>> put` — State + IO. Effect {Read, Get, Put}.
pub fn prog_state_io() -> IComp {
    let s = Type::Var("State".to_string());
    iread(iget(s.clone(), iput_pure(IValue::Received(s))))
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // --- Effect set operations ---------------------------------------------

    #[test]
    fn test_effect_empty_insert_contains() {
        let mut e = Effect::empty();
        assert!(e.is_empty());
        assert!(!e.contains(IOp::Get));
        e.insert(IOp::Get);
        assert!(e.contains(IOp::Get));
        assert!(!e.is_empty());
        // Display of empty is ∅.
        assert_eq!(Effect::empty().to_string(), "∅");
    }

    #[test]
    fn test_effect_union() {
        let a = Effect::from_ops([IOp::Get, IOp::Put]);
        let b = Effect::from_ops([IOp::Read, IOp::Write]);
        let u = a.union(&b);
        assert!(u.contains(IOp::Get));
        assert!(u.contains(IOp::Put));
        assert!(u.contains(IOp::Read));
        assert!(u.contains(IOp::Write));
        assert!(!u.contains(IOp::Throw));
    }

    #[test]
    fn test_effect_difference_handler_elimination() {
        // {Get, Put, Read} \ {Get, Put} = {Read}  (state handler eliminates
        // its own ops, leaves the foreign Read through).
        let comp = Effect::from_ops([IOp::Get, IOp::Put, IOp::Read]);
        let handled = state_handled();
        let remaining = comp.difference(&handled);
        assert!(remaining.contains(IOp::Read));
        assert!(!remaining.contains(IOp::Get));
        assert!(!remaining.contains(IOp::Put));
    }

    #[test]
    fn test_effect_subset() {
        let small = Effect::from_ops([IOp::Get]);
        let big = Effect::from_ops([IOp::Get, IOp::Put, IOp::Read]);
        assert!(small.is_subset(&big));
        assert!(!big.is_subset(&small));
        assert!(big.is_subset(&big));
    }

    // --- Effect inference on pure computations -----------------------------

    #[test]
    fn test_infer_pure_int() {
        let et = infer_effect(&ipure(IValue::Int(42)));
        assert_eq!(et.ty, Type::Int);
        assert!(et.effect.is_empty());
        assert_eq!(et.to_string(), "Int / ∅");
    }

    #[test]
    fn test_infer_pure_bool() {
        let et = infer_effect(&ipure(IValue::Bool(true)));
        assert_eq!(et.ty, Type::Bool);
        assert!(et.effect.is_empty());
    }

    #[test]
    fn test_infer_pure_product_and_list() {
        let prod = ipure(IValue::Product(
            Box::new(IValue::Int(1)),
            Box::new(IValue::Bool(false)),
        ));
        let et = infer_effect(&prod);
        assert_eq!(et.ty, Type::Product(Box::new(Type::Int), Box::new(Type::Bool)));
        assert!(et.effect.is_empty());

        let list = ipure(IValue::List(vec![IValue::Int(1), IValue::Int(2)]));
        let et2 = infer_effect(&list);
        assert_eq!(et2.ty, Type::List(Box::new(Type::Int)));
        assert!(et2.effect.is_empty());
    }

    // --- Effect inference on single-operation computations -----------------

    #[test]
    fn test_infer_get() {
        let s = Type::Var("State".to_string());
        let et = infer_effect(&iget_pure(s.clone()));
        assert_eq!(et.ty, s);
        assert_eq!(et.effect, Effect::singleton(IOp::Get));
        assert_eq!(et.effect.to_string(), "{Get}");
    }

    #[test]
    fn test_infer_put() {
        let et = infer_effect(&iput_pure(IValue::Int(5)));
        assert_eq!(et.ty, Type::Unit);
        assert_eq!(et.effect, Effect::singleton(IOp::Put));
    }

    #[test]
    fn test_infer_read() {
        let et = infer_effect(&iread_pure());
        assert_eq!(et.ty, Type::String);
        assert_eq!(et.effect, Effect::singleton(IOp::Read));
    }

    #[test]
    fn test_infer_throw_polymorphic() {
        let et = infer_effect(&ithrow_pure("err"));
        // Result type is polymorphic (a type variable) — throw never returns.
        assert_eq!(et.ty, Type::Var("a".to_string()));
        assert_eq!(et.effect, Effect::singleton(IOp::Throw));
    }

    // --- Effect inference on composed computations -------------------------

    #[test]
    fn test_infer_get_then_put() {
        let et = infer_effect(&prog_get_put());
        assert_eq!(et.ty, Type::Unit);
        assert_eq!(et.effect, Effect::from_ops([IOp::Get, IOp::Put]));
    }

    #[test]
    fn test_infer_read_then_write() {
        let et = infer_effect(&prog_read_write());
        assert_eq!(et.ty, Type::Unit);
        assert_eq!(et.effect, Effect::from_ops([IOp::Read, IOp::Write]));
    }

    #[test]
    fn test_infer_get_then_throw() {
        let et = infer_effect(&prog_get_throw());
        assert_eq!(et.ty, Type::Var("a".to_string()));
        assert_eq!(et.effect, Effect::from_ops([IOp::Get, IOp::Throw]));
    }

    #[test]
    fn test_infer_all_five_operations() {
        let et = infer_effect(&prog_all_five());
        assert_eq!(
            et.effect,
            Effect::from_ops([IOp::Get, IOp::Put, IOp::Read, IOp::Write, IOp::Throw])
        );
    }

    // --- Handler effect elimination ---------------------------------------

    #[test]
    fn test_handle_state_eliminates_get_put() {
        let et = infer_effect(&prog_get_put());
        let remaining = effect_after_handler(&et.effect, &state_handled());
        assert!(remaining.is_empty());
    }

    #[test]
    fn test_handle_state_passthrough_read() {
        // {Get, Put, Read} handled by state -> {Read} remains (pass-through).
        let et = infer_effect(&prog_state_io());
        assert_eq!(et.effect, Effect::from_ops([IOp::Read, IOp::Get, IOp::Put]));
        let remaining = effect_after_handler(&et.effect, &state_handled());
        assert_eq!(remaining, Effect::singleton(IOp::Read));
    }

    #[test]
    fn test_handle_io_eliminates_read_write() {
        let et = infer_effect(&prog_read_write());
        let remaining = effect_after_handler(&et.effect, &io_handled());
        assert!(remaining.is_empty());
    }

    #[test]
    fn test_handle_exception_eliminates_throw() {
        let et = infer_effect(&ithrow_pure("err"));
        let remaining = effect_after_handler(&et.effect, &exception_handled());
        assert!(remaining.is_empty());
    }

    #[test]
    fn test_handle_exception_passthrough_get() {
        // {Get, Throw} handled by exception -> {Get} remains (pass-through).
        let et = infer_effect(&prog_get_throw());
        let remaining = effect_after_handler(&et.effect, &exception_handled());
        assert_eq!(remaining, Effect::singleton(IOp::Get));
    }

    // --- Handler stacking --------------------------------------------------

    #[test]
    fn test_stack_state_io_eliminates_all() {
        let et = infer_effect(&prog_state_io());
        let remaining = effect_after_stack(&et.effect, &[state_handled(), io_handled()]);
        assert!(remaining.is_empty());
    }

    #[test]
    fn test_stack_state_exception_eliminates_all() {
        let et = infer_effect(&prog_get_throw());
        let remaining =
            effect_after_stack(&et.effect, &[state_handled(), exception_handled()]);
        assert!(remaining.is_empty());
    }

    #[test]
    fn test_full_stack_eliminates_all_five() {
        let et = infer_effect(&prog_all_five());
        let remaining = effect_after_stack(
            &et.effect,
            &[state_handled(), io_handled(), exception_handled()],
        );
        assert!(remaining.is_empty());
    }

    // --- Effect safety / unhandled detection ------------------------------

    #[test]
    fn test_unhandled_get_detected() {
        // A get with no state handler in the stack -> unhandled.
        let et = infer_effect(&iget_pure(Type::Var("State".to_string())));
        let safety = check_safety(&et.effect);
        assert_eq!(safety, Safety::Unhandled(vec![IOp::Get]));
    }

    #[test]
    fn test_partial_handler_leaves_unhandled() {
        // {Get, Read} handled by only state -> {Read} remains unhandled.
        let comp = iread(iget_pure(Type::Var("State".to_string())));
        let safety = check_computation(&comp, &[state_handled()]);
        assert_eq!(safety, Safety::Unhandled(vec![IOp::Read]));
    }

    #[test]
    fn test_fully_handled_is_safe() {
        // All five operations, full handler stack -> safe.
        let safety = check_computation(
            &prog_all_five(),
            &[state_handled(), io_handled(), exception_handled()],
        );
        assert_eq!(safety, Safety::Safe);
    }

    // --- Polymorphic effect rows (bonus) ----------------------------------

    #[test]
    fn test_row_effect_var_and_display() {
        let r = RowEffect::open(&[IOp::Get, IOp::Put], "ρ");
        assert!(r.contains(IOp::Get));
        assert!(r.has_row_var());
        assert_eq!(r.row_var_name(), Some("ρ"));
        assert_eq!(r.to_string(), "{Get, Put, ρ}");

        let pure = RowEffect::var("ρ");
        assert_eq!(pure.to_string(), "{ρ}");
    }

    #[test]
    fn test_row_effect_handler_preserves_row_var() {
        // {Get, Put, ρ} handled by state -> {ρ} (row var preserved; foreign
        // ops in ρ pass through).
        let r = RowEffect::open(&[IOp::Get, IOp::Put], "ρ");
        let remaining = r.eliminate(&state_handled());
        assert!(!remaining.contains(IOp::Get));
        assert!(!remaining.contains(IOp::Put));
        assert!(remaining.has_row_var());
        assert_eq!(remaining.to_string(), "{ρ}");
    }

    #[test]
    fn test_row_effect_unify_ground_equal() {
        let a = RowEffect::closed(&[IOp::Get, IOp::Put]);
        let b = RowEffect::closed(&[IOp::Get, IOp::Put]);
        assert_eq!(a.unify(&b), Some(RowEffect::closed(&[IOp::Get, IOp::Put])));
    }

    #[test]
    fn test_row_effect_unify_ground_unequal_fails() {
        let a = RowEffect::closed(&[IOp::Get]);
        let b = RowEffect::closed(&[IOp::Put]);
        assert_eq!(a.unify(&b), None);
    }

    #[test]
    fn test_row_effect_unify_open_absorbs() {
        // {Get, ρ} unifies with {Put} -> {Get, Put, ρ} (ρ absorbs Put).
        let a = RowEffect::open(&[IOp::Get], "ρ");
        let b = RowEffect::closed(&[IOp::Put]);
        let u = a.unify(&b).expect("open row unifies with ground");
        assert!(u.contains(IOp::Get));
        assert!(u.contains(IOp::Put));
        assert!(u.has_row_var());
    }
}

// ============================================================================
// Demo
// ============================================================================

fn main() {
    println!("Arrow Calculus: Deep Dive — Effect Typing for Arrows");
    println!("=====================================================\n");

    println!("Effect rows are inferred statically by traversing the");
    println!("computation tree; handlers act as effect eliminators.\n");

    // --- Pure ---
    println!("1. Pure computation: pure 42");
    let et = infer_effect(&ipure(IValue::Int(42)));
    println!("   inferred: {}\n", et);

    // --- Single ops ---
    println!("2. Single operations:");
    let s = Type::Var("State".to_string());
    println!("   get        : {}", infer_effect(&iget_pure(s.clone())));
    println!("   put 5      : {}", infer_effect(&iput_pure(IValue::Int(5))));
    println!("   read       : {}", infer_effect(&iread_pure()));
    println!("   throw \"err\": {}\n", infer_effect(&ithrow_pure("err")));

    // --- Composed ---
    println!("3. Composed computations:");
    println!("   get >>> put        : {}", infer_effect(&prog_get_put()));
    println!("   read >>> write     : {}", infer_effect(&prog_read_write()));
    println!("   get >>> throw      : {}", infer_effect(&prog_get_throw()));
    println!("   all five ops       : {}\n", infer_effect(&prog_all_five()));

    // --- Handler elimination ---
    println!("4. Handler effect elimination (handlers as effect eliminators):");
    let all = infer_effect(&prog_all_five());
    println!("   effect of all-five program: {}", all.effect);
    let after_state = effect_after_handler(&all.effect, &state_handled());
    println!("   after handle_state    : {}  (Get, Put removed)", after_state);
    let after_io = effect_after_handler(&after_state, &io_handled());
    println!("   after handle_io       : {}  (Read, Write removed)", after_io);
    let after_exc = effect_after_handler(&after_io, &exception_handled());
    println!("   after handle_exception: {}  (Throw removed)\n", after_exc);

    // --- Handler stacking ---
    println!("5. Handler stacking (full stack on all-five program):");
    let stack = [state_handled(), io_handled(), exception_handled()];
    let remaining = effect_after_stack(&all.effect, &stack);
    println!("   remaining effect: {}", remaining);
    println!("   safety check    : {}\n", check_safety(&remaining));

    // --- Safety: unhandled detection ---
    println!("6. Unhandled-effect detection (static counterpart of runtime error):");
    let unhandled = check_computation(&iget_pure(s), &[]);
    println!("   get with no handler   : {}", unhandled);
    let partial = check_computation(&prog_state_io(), &[state_handled()]);
    println!("   state+io, only state  : {}", partial);
    let safe = check_computation(&prog_all_five(), &stack);
    println!("   all-five, full stack  : {}\n", safe);

    // --- Polymorphic rows ---
    println!("7. Polymorphic effect rows (row variable ρ):");
    let r = RowEffect::open(&[IOp::Get, IOp::Put], "ρ");
    println!("   row {{Get, Put, ρ}}            : {}", r);
    println!("   after handle_state (ρ kept)    : {}", r.eliminate(&state_handled()));
    let a = RowEffect::open(&[IOp::Get], "ρ");
    let b = RowEffect::closed(&[IOp::Put]);
    println!("   unify {{Get, ρ}} with {{Put}}   : {}", a.unify(&b).unwrap());
}
