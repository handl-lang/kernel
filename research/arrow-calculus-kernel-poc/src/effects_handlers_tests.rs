// Challenge #6: Effects & Handlers for Arrows
//
// Key questions:
// 1. Can monadic effects (State, IO, Exceptions) be encoded as arrow
//    operations + handlers, without a monad primitive?
// 2. Do multiple effects compose as cleanly as monad transformers?
// 3. Is handler composition at least as expressive as monad transformers,
//    with better composability?
//
// Model: a "freer arrow". A computation is a tree of suspended operations,
// each carrying a continuation. A handler walks the tree, intercepting its
// own operations and *passing through* foreign ones by rebuilding the
// continuation with itself re-applied. This pass-through is what lets
// handlers stack independently, mirroring (and improving on) monad
// transformers.

use std::cell::RefCell;
use std::fmt;
use std::rc::Rc;

// ============================================================================
// Values
// ============================================================================

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Int(i32),
    Bool(bool),
    Str(String),
    Unit,
    Product(Box<Value>, Box<Value>),
    List(Vec<Value>),
    Left(Box<Value>),
    Right(Box<Value>),
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Int(n) => write!(f, "{}", n),
            Value::Bool(b) => write!(f, "{}", b),
            Value::Str(s) => write!(f, "\"{}\"", s),
            Value::Unit => write!(f, "()"),
            Value::Product(a, b) => write!(f, "({}, {})", a, b),
            Value::Left(v) => write!(f, "Left({})", v),
            Value::Right(v) => write!(f, "Right({})", v),
            Value::List(vs) => {
                write!(f, "[")?;
                for (i, v) in vs.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", v)?;
                }
                write!(f, "]")
            }
        }
    }
}

impl Value {
    fn as_int(&self) -> Option<i32> {
        match self {
            Value::Int(n) => Some(*n),
            _ => None,
        }
    }

    fn as_str(&self) -> Option<&str> {
        match self {
            Value::Str(s) => Some(s),
            _ => None,
        }
    }
}

// ============================================================================
// Effect Operations
// ============================================================================
//
// An operation is the unit of effectful behaviour. Programs mention operations
// without committing to an interpretation; handlers supply the interpretation.
//
//   operation Get  : ()       ~> State      -- read current state
//   operation Put  : State    ~> ()         -- overwrite state
//   operation Read : ()       ~> String     -- read one input
//   operation Write: String   ~> ()         -- emit one output
//   operation Throw: String   ~> _          -- raise an exception (aborting)

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Op {
    Get,
    Put,
    Read,
    Write,
    Throw,
}

impl fmt::Display for Op {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Op::Get => write!(f, "Get"),
            Op::Put => write!(f, "Put"),
            Op::Read => write!(f, "Read"),
            Op::Write => write!(f, "Write"),
            Op::Throw => write!(f, "Throw"),
        }
    }
}

// ============================================================================
// Effectful Computations (Freer Arrow)
// ============================================================================
//
//   Comp ::= Pure v
//          | Op op arg k        -- perform `op` with `arg`, continue with `k`
//
// `k : Value -> Comp` is the continuation: it receives the operation's result
// and produces the rest of the computation. Continuations are stored as
// `Rc<dyn Fn>` so they can be cheaply cloned into rebuilt continuations when
// a handler passes a foreign operation through.

pub enum Comp {
    Pure(Value),
    Op(
        Op,
        Value,
        Rc<dyn Fn(Value) -> Comp + 'static>,
    ),
}

// ============================================================================
// Builders
// ============================================================================

/// Lift a pure value into a computation.
pub fn pure(v: Value) -> Comp {
    Comp::Pure(v)
}

/// `arr f`: lift a pure function `f : Value -> Value` into an arrow
/// `Value ~> Value` (here: a function from input to a pure computation).
pub fn arr(f: fn(Value) -> Value) -> Rc<dyn Fn(Value) -> Comp + 'static> {
    Rc::new(move |x| pure(f(x)))
}

/// Monadic bind, which corresponds to arrow composition when the first
/// component feeds its output to the second:
///
///   bind(f, g)  ~  f >>> arr(\x. g x)   (sequencing)
///
/// Traverses `f`'s operations, threading `g` onto every continuation so that
/// once `f` produces a value, `g` is invoked on it.
pub fn bind(comp: Comp, g: Rc<dyn Fn(Value) -> Comp + 'static>) -> Comp {
    match comp {
        Comp::Pure(v) => g(v),
        Comp::Op(op, arg, k) => {
            let g2 = Rc::clone(&g);
            Comp::Op(op, arg, Rc::new(move |r| bind(k(r), Rc::clone(&g2))))
        }
    }
}

/// `f >>> g`: arrow composition. Both sides are arrows `Value ~> Comp`;
/// the output of `f` is fed as input to `g`.
pub fn seq(
    f: Rc<dyn Fn(Value) -> Comp + 'static>,
    g: Rc<dyn Fn(Value) -> Comp + 'static>,
) -> Rc<dyn Fn(Value) -> Comp + 'static> {
    Rc::new(move |x| bind(f(x), Rc::clone(&g)))
}

// --- Operation constructors -------------------------------------------------

/// `get ()` — perform Get, yield the current state as the result.
pub fn get() -> Comp {
    Comp::Op(Op::Get, Value::Unit, Rc::new(|s| Comp::Pure(s)))
}

/// `put s` — perform Put with new state `s`, yield Unit.
pub fn put(s: Value) -> Comp {
    Comp::Op(Op::Put, s, Rc::new(|_| Comp::Pure(Value::Unit)))
}

/// `read ()` — perform Read, yield the next input string.
pub fn read() -> Comp {
    Comp::Op(Op::Read, Value::Unit, Rc::new(|s| Comp::Pure(s)))
}

/// `write s` — perform Write with payload `s`, yield Unit.
pub fn write(s: Value) -> Comp {
    Comp::Op(Op::Write, s, Rc::new(|_| Comp::Pure(Value::Unit)))
}

/// `throw msg` — raise an exception. The continuation is never invoked.
pub fn throw(msg: &str) -> Comp {
    Comp::Op(
        Op::Throw,
        Value::Str(msg.to_string()),
        // Unreachable: handlers abort on Throw rather than resuming.
        Rc::new(|_| Comp::Pure(Value::Unit)),
    )
}

/// Convenience: modify the state with a pure function and return the new state.
///   modify f = bind get (\s. put (f s) >>> get)
pub fn modify(f: fn(Value) -> Value) -> Comp {
    bind(get(), Rc::new(move |s| {
        let new = f(s);
        bind(put(new.clone()), Rc::new(move |_| pure(new.clone())))
    }))
}

// ============================================================================
// Handlers
// ============================================================================
//
// A handler interprets a subset of operations. The defining trick is
// *pass-through*: when the handler meets an operation it does not own, it
// rebuilds the operation node with a continuation that re-applies the handler
// to the resumed computation. This is what lets handlers stack: an outer
// handler eventually sees the rebuilt foreign operation and interprets it.
//
//   handle_state (Op Get _ k)   s  =  handle_state (k s) s
//   handle_state (Op Put s' k) s  =  handle_state (k ()) s'
//   handle_state (Op op a k)   s  =  Op op a (\r. handle_state (k r) s)  -- pass-through
//   handle_state (Pure v)      s  =  Pure v

// --- State handler ----------------------------------------------------------
//
// Threads a piece of state through the computation. Removes Get/Put.

pub fn handle_state(comp: Comp, state: Value) -> Comp {
    match comp {
        Comp::Pure(v) => Comp::Pure(v),

        // Get: resume continuation with current state; state unchanged.
        Comp::Op(Op::Get, _, k) => handle_state(k(state.clone()), state),

        // Put: update state, resume continuation with Unit.
        Comp::Op(Op::Put, new_state, k) => {
            handle_state(k(Value::Unit), new_state)
        }

        // Foreign operation: rebuild, re-apply handler to the continuation
        // with the state current at this point.
        Comp::Op(op, arg, k) => {
            let s = state.clone();
            Comp::Op(op, arg, Rc::new(move |r| handle_state(k(r), s.clone())))
        }
    }
}

/// Like `handle_state`, but returns the final state *paired* with the result:
///   handle_state_pair p s  =  Pure (Product (result, final_state))
///
/// This makes handler *order* observable. With an exception handler stacked
/// outside, a throw discards the state (mirroring `StateT (Except)`); with
/// the state handler outside, pre-throw state changes survive in the pair
/// (mirroring `ExceptT (State)`). Same program, different semantics — purely
/// a function of handler order, with no change to the program text.
pub fn handle_state_pair(comp: Comp, state: Value) -> Comp {
    match comp {
        Comp::Pure(v) => Comp::Pure(Value::Product(Box::new(v), Box::new(state))),

        Comp::Op(Op::Get, _, k) => handle_state_pair(k(state.clone()), state),

        Comp::Op(Op::Put, new_state, k) => {
            handle_state_pair(k(Value::Unit), new_state)
        }

        // Foreign op: the continuation returns a Product(val, state) which
        // flows out through the op to the outer handler unchanged.
        Comp::Op(op, arg, k) => {
            let s = state.clone();
            Comp::Op(op, arg, Rc::new(move |r| handle_state_pair(k(r), s.clone())))
        }
    }
}

// --- IO handler -------------------------------------------------------------
//
// Simulates IO against a fixed list of inputs and a shared output buffer.
// Removes Read/Write. Uses Rc<RefCell<_>> so the output buffer can be shared
// across rebuilt continuations without borrowing against 'static.

pub fn handle_io(
    comp: Comp,
    inputs: Rc<Vec<String>>,
    input_idx: usize,
    outputs: Rc<RefCell<Vec<String>>>,
) -> Comp {
    match comp {
        Comp::Pure(v) => Comp::Pure(v),

        // Read: feed the next input to the continuation.
        Comp::Op(Op::Read, _, k) => {
            let input = inputs
                .get(input_idx)
                .cloned()
                .unwrap_or_default();
            handle_io(
                k(Value::Str(input)),
                inputs,
                input_idx + 1,
                outputs,
            )
        }

        // Write: append payload to the output buffer.
        Comp::Op(Op::Write, Value::Str(s), k) => {
            outputs.borrow_mut().push(s);
            handle_io(k(Value::Unit), inputs, input_idx, outputs)
        }

        // Foreign operation: pass through, preserving input position and
        // buffer identity.
        Comp::Op(op, arg, k) => {
            let inputs2 = Rc::clone(&inputs);
            let outputs2 = Rc::clone(&outputs);
            Comp::Op(
                op,
                arg,
                Rc::new(move |r| {
                    handle_io(k(r), Rc::clone(&inputs2), input_idx, Rc::clone(&outputs2))
                }),
            )
        }
    }
}

// --- Exception handler ------------------------------------------------------
//
// Catches Throw, producing `Right v` on success and `Left msg` on throw.
// Foreign operations pass through with the handler re-applied. Because Throw
// aborts, the continuation is discarded on a throw.

pub fn handle_exception(comp: Comp) -> Comp {
    match comp {
        Comp::Pure(v) => Comp::Pure(Value::Right(Box::new(v))),

        // Throw: discard continuation, surface the error as Left.
        Comp::Op(Op::Throw, Value::Str(msg), _k) => {
            Comp::Pure(Value::Left(Box::new(Value::Str(msg))))
        }

        // Foreign operation: pass through, keep catching in the continuation.
        Comp::Op(op, arg, k) => Comp::Op(op, arg, Rc::new(move |r| handle_exception(k(r)))),
    }
}

// ============================================================================
// Final Interpreter
// ============================================================================
//
// After all handlers have run, a well-formed program is `Pure`. Any remaining
// `Op` is an *unhandled* operation — a runtime error, exactly analogous to
// an unhandled effect in algebraic-effect systems.

#[derive(Debug, Clone, PartialEq)]
pub enum RunError {
    UnhandledOp(Op),
}

impl fmt::Display for RunError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RunError::UnhandledOp(op) => write!(f, "unhandled operation: {}", op),
        }
    }
}

pub fn run(comp: Comp) -> Result<Value, RunError> {
    match comp {
        Comp::Pure(v) => Ok(v),
        Comp::Op(op, _, _) => Err(RunError::UnhandledOp(op)),
    }
}

// ============================================================================
// Example Programs
// ============================================================================
//
// Each program is written once, in terms of operations only. Different
// handler stacks give it different semantics — the program text never
// mentions a monad, transformer, or state thread.

/// A stateful counter: read state, increment, write back, return new value.
///   counter = get >>> arr (+1) >>> (dup >>> put) >>> get
pub fn counter_program() -> Comp {
    bind(get(), Rc::new(|s| {
        let s = s.as_int().unwrap_or(0);
        let new = Value::Int(s + 1);
        bind(put(new.clone()), Rc::new(move |_| {
            pure(new.clone())
        }))
    }))
}

/// Increment state `n` times, returning the final state.
pub fn increment_n(n: u32) -> Comp {
    // Start from the identity arrow (zero increments), then compose `n`
    // counter steps onto it. Each counter step ignores its input and reads,
    // increments, and writes back the state.
    let mut step: Rc<dyn Fn(Value) -> Comp + 'static> = Rc::new(|x| pure(x));
    for _ in 0..n {
        step = seq(Rc::clone(&step), Rc::new(|_| counter_program()));
    }
    // Seed: ignore the input, run the chain.
    bind(pure(Value::Unit), step)
}

/// Safe division: throws "divide by zero" when the divisor is 0.
pub fn safe_div(num: i32, den: i32) -> Comp {
    if den == 0 {
        throw("divide by zero")
    } else {
        pure(Value::Int(num / den))
    }
}

/// Read a number, add it to the state, return the new state.
/// Uses State (get/put) and IO (read).
pub fn read_and_accumulate() -> Comp {
    bind(read(), Rc::new(|input| {
        let n: i32 = input.as_str().and_then(|s| s.parse().ok()).unwrap_or(0);
        bind(get(), Rc::new(move |s| {
            let acc = s.as_int().unwrap_or(0) + n;
            bind(put(Value::Int(acc)), Rc::new(move |_| {
                pure(Value::Int(acc))
            }))
        }))
    }))
}

/// Read a number, add to state, but throw if the running total exceeds a cap.
/// Uses State + IO + Exception together.
pub fn capped_accumulate(cap: i32) -> Comp {
    bind(read(), Rc::new(move |input| {
        let n: i32 = input.as_str().and_then(|s| s.parse().ok()).unwrap_or(0);
        bind(get(), Rc::new(move |s| {
            let acc = s.as_int().unwrap_or(0) + n;
            if acc > cap {
                throw("cap exceeded")
            } else {
                bind(put(Value::Int(acc)), Rc::new(move |_| {
                    pure(Value::Int(acc))
                }))
            }
        }))
    }))
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // --- State ----------------------------------------------------------------

    #[test]
    fn test_state_counter_single_increment() {
        // counter_program under handle_state with init 4 -> 5
        let handled = handle_state(counter_program(), Value::Int(4));
        let result = run(handled).unwrap();
        assert_eq!(result, Value::Int(5));
    }

    #[test]
    fn test_state_counter_chained() {
        // Three increments starting from 0 -> 3
        let prog = increment_n(3);
        let handled = handle_state(prog, Value::Int(0));
        let result = run(handled).unwrap();
        assert_eq!(result, Value::Int(3));
    }

    #[test]
    fn test_state_get_put_roundtrip() {
        // put 7 >>> get should yield 7
        let prog = bind(put(Value::Int(7)), Rc::new(|_| get()));
        let handled = handle_state(prog, Value::Int(0));
        let result = run(handled).unwrap();
        assert_eq!(result, Value::Int(7));
    }

    #[test]
    fn test_state_pure_passes_through() {
        // A pure computation under the state handler is unchanged.
        let handled = handle_state(pure(Value::Int(42)), Value::Int(0));
        assert_eq!(run(handled).unwrap(), Value::Int(42));
    }

    // --- Exceptions -----------------------------------------------------------

    #[test]
    fn test_exception_success_yields_right() {
        let handled = handle_exception(safe_div(10, 2));
        let result = run(handled).unwrap();
        assert_eq!(result, Value::Right(Box::new(Value::Int(5))));
    }

    #[test]
    fn test_exception_throw_yields_left() {
        let handled = handle_exception(safe_div(10, 0));
        let result = run(handled).unwrap();
        assert_eq!(
            result,
            Value::Left(Box::new(Value::Str("divide by zero".to_string())))
        );
    }

    #[test]
    fn test_exception_aborts_continuation() {
        // throw then pure(99): the 99 must never be reached.
        let prog = bind(throw("boom"), Rc::new(|_| pure(Value::Int(99))));
        let result = run(handle_exception(prog)).unwrap();
        assert_eq!(
            result,
            Value::Left(Box::new(Value::Str("boom".to_string())))
        );
    }

    #[test]
    fn test_mid_program_catch_recovers() {
        // Wrap a throwing sub-computation with handle_exception, then branch
        // on the resulting Either — a try/catch written in terms of handlers.
        let prog = bind(
            handle_exception(safe_div(10, 0)),
            Rc::new(|either| match either {
                Value::Right(v) => pure(*v),
                Value::Left(e) => pure(Value::Str(format!("caught: {}", e))),
                _ => pure(Value::Unit),
            }),
        );
        let result = run(handle_exception(prog)).unwrap();
        // Outer handler wraps the already-Right/Left value again.
        match result {
            Value::Right(inner) => {
                assert_eq!(*inner, Value::Str("caught: \"divide by zero\"".to_string()));
            }
            other => panic!("expected Right, got {:?}", other),
        }
    }

    // --- IO -------------------------------------------------------------------

    #[test]
    fn test_io_read_returns_input() {
        let inputs = Rc::new(vec!["hello".to_string()]);
        let outputs = Rc::new(RefCell::new(Vec::new()));
        let handled = handle_io(read(), inputs, 0, outputs);
        let result = run(handled).unwrap();
        assert_eq!(result, Value::Str("hello".to_string()));
    }

    #[test]
    fn test_io_write_collects_output() {
        let inputs = Rc::new(Vec::new());
        let outputs = Rc::new(RefCell::new(Vec::new()));
        let prog = bind(write(Value::Str("a".to_string())), Rc::new(|_| {
            write(Value::Str("b".to_string()))
        }));
        let handled = handle_io(prog, inputs, 0, Rc::clone(&outputs));
        run(handled).unwrap();
        assert_eq!(
            outputs.borrow().clone(),
            vec!["a".to_string(), "b".to_string()]
        );
    }

    #[test]
    fn test_io_echo() {
        // read >>> write: echo one input to the output buffer.
        let inputs = Rc::new(vec!["ping".to_string()]);
        let outputs = Rc::new(RefCell::new(Vec::new()));
        let prog = bind(read(), Rc::new(|s| write(s)));
        let handled = handle_io(prog, inputs, 0, Rc::clone(&outputs));
        run(handled).unwrap();
        assert_eq!(outputs.borrow().clone(), vec!["ping".to_string()]);
    }

    // --- Multi-effect composition --------------------------------------------

    #[test]
    fn test_state_plus_io_accumulate() {
        // read_and_accumulate twice, starting from state 0, with inputs 10, 20.
        let prog = bind(read_and_accumulate(), Rc::new(|_| read_and_accumulate()));
        let inputs = Rc::new(vec!["10".to_string(), "20".to_string()]);
        let outputs = Rc::new(RefCell::new(Vec::new()));

        // Stack: state innermost, io outermost. Both must cooperate.
        let state_handled = handle_state(prog, Value::Int(0));
        let io_handled = handle_io(state_handled, inputs, 0, outputs);
        let result = run(io_handled).unwrap();
        assert_eq!(result, Value::Int(30));
    }

    #[test]
    fn test_state_plus_exception_preserves_state_on_success() {
        // safe_div(20, 2) = 10; store in state; should succeed with state 10.
        let prog = bind(safe_div(20, 2), Rc::new(|v| {
            bind(put(v), Rc::new(|_| get()))
        }));
        let state_handled = handle_state(prog, Value::Int(0));
        let exc_handled = handle_exception(state_handled);
        let result = run(exc_handled).unwrap();
        assert_eq!(result, Value::Right(Box::new(Value::Int(10))));
    }

    #[test]
    fn test_state_plus_exception_aborts_before_state_update() {
        // safe_div(20, 0) throws; the put must never run.
        let prog = bind(safe_div(20, 0), Rc::new(|v| {
            bind(put(v), Rc::new(|_| get()))
        }));
        let state_handled = handle_state(prog, Value::Int(0));
        let exc_handled = handle_exception(state_handled);
        let result = run(exc_handled).unwrap();
        assert_eq!(
            result,
            Value::Left(Box::new(Value::Str("divide by zero".to_string())))
        );
    }

    #[test]
    fn test_state_io_exception_all_three_success() {
        // capped_accumulate(100) twice with inputs 30, 40 -> 70 (under cap).
        let prog = bind(capped_accumulate(100), Rc::new(|_| capped_accumulate(100)));
        let inputs = Rc::new(vec!["30".to_string(), "40".to_string()]);
        let outputs = Rc::new(RefCell::new(Vec::new()));

        let state_handled = handle_state(prog, Value::Int(0));
        let io_handled = handle_io(state_handled, inputs, 0, outputs);
        let exc_handled = handle_exception(io_handled);
        let result = run(exc_handled).unwrap();
        assert_eq!(result, Value::Right(Box::new(Value::Int(70))));
    }

    #[test]
    fn test_state_io_exception_all_three_throws() {
        // capped_accumulate(50) with inputs 30, 40 -> 30 ok, then 70 > 50 throws.
        let prog = bind(capped_accumulate(50), Rc::new(|_| capped_accumulate(50)));
        let inputs = Rc::new(vec!["30".to_string(), "40".to_string()]);
        let outputs = Rc::new(RefCell::new(Vec::new()));

        let state_handled = handle_state(prog, Value::Int(0));
        let io_handled = handle_io(state_handled, inputs, 0, outputs);
        let exc_handled = handle_exception(io_handled);
        let result = run(exc_handled).unwrap();
        assert_eq!(
            result,
            Value::Left(Box::new(Value::Str("cap exceeded".to_string())))
        );
    }

    // --- Handler ordering (vs monad transformers) ----------------------------

    #[test]
    fn test_handler_order_exception_outer_vs_inner() {
        // Same program: put 10, then throw, then (unreached) put 20.
        // The two handler orders give observably different results, exactly
        // mirroring the difference between monad-transformer stacks:
        //
        //   StateT (Except)  ==  exception OUTSIDE state
        //     -> throw discards state; result is Left, state is LOST.
        //   ExceptT (State)  ==  state OUTSIDE exception
        //     -> state changes before the throw survive; result is
        //        Product(Left, 10), state is PRESERVED.
        //
        // The program text is identical in both cases; only handler order
        // differs.
        let make_prog = || {
            bind(put(Value::Int(10)), Rc::new(|_| {
                bind(throw("stop"), Rc::new(|_| put(Value::Int(20))))
            }))
        };

        // Order A: exception outer (state inner). State lost on throw.
        let a = run(handle_exception(handle_state_pair(make_prog(), Value::Int(0)))).unwrap();
        assert_eq!(
            a,
            Value::Left(Box::new(Value::Str("stop".to_string())))
        );

        // Order B: state outer (exception inner). State preserved on throw.
        let b = run(handle_state_pair(handle_exception(make_prog()), Value::Int(0))).unwrap();
        assert_eq!(
            b,
            Value::Product(
                Box::new(Value::Left(Box::new(Value::Str("stop".to_string())))),
                Box::new(Value::Int(10)),
            )
        );
    }

    #[test]
    fn test_unhandled_operation_errors() {
        // A Get with no state handler in scope is a runtime error.
        let err = run(get()).unwrap_err();
        assert_eq!(err, RunError::UnhandledOp(Op::Get));
    }

    #[test]
    fn test_pass_through_preserves_foreign_ops_for_outer_handler() {
        // A state handler passing a Read through must leave it intact for an
        // outer IO handler to interpret. Verifies pass-through correctness.
        let prog = bind(get(), Rc::new(|s| {
            bind(read(), Rc::new(move |input| {
                pure(Value::Product(
                    Box::new(s.clone()),
                    Box::new(input),
                ))
            }))
        }));

        let inputs = Rc::new(vec!["hi".to_string()]);
        let outputs = Rc::new(RefCell::new(Vec::new()));

        let state_handled = handle_state(prog, Value::Int(7));
        let io_handled = handle_io(state_handled, inputs, 0, outputs);
        let result = run(io_handled).unwrap();
        assert_eq!(
            result,
            Value::Product(Box::new(Value::Int(7)), Box::new(Value::Str("hi".to_string())))
        );
    }

    #[test]
    fn test_arrow_composition_with_effects() {
        // arr (+1) >>> counter_program: lift a pure step, then a stateful one.
        let add_one: Rc<dyn Fn(Value) -> Comp + 'static> = arr(|v| {
            Value::Int(v.as_int().unwrap_or(0) + 1)
        });
        let composed = seq(add_one, Rc::new(|_| counter_program()));

        // Input 9 -> (+1) -> 10 (discarded by counter_program, which reads state)
        // state init 0 -> counter -> 1
        let handled = handle_state(composed(Value::Int(9)), Value::Int(0));
        assert_eq!(run(handled).unwrap(), Value::Int(1));
    }
}

// ============================================================================
// Demo
// ============================================================================

fn main() {
    println!("Arrow Calculus: Challenge #6 - Effects & Handlers");
    println!("=================================================\n");

    // Demo 1: State
    println!("Demo 1: Stateful counter (3 increments from 0)");
    let prog = increment_n(3);
    let handled = handle_state(prog, Value::Int(0));
    match run(handled) {
        Ok(v) => println!("  result: {} (expected 3)\n", v),
        Err(e) => println!("  error: {}\n", e),
    }

    // Demo 2: Exception
    println!("Demo 2: Safe division (10 / 0)");
    let handled = handle_exception(safe_div(10, 0));
    match run(handled) {
        Ok(v) => println!("  result: {} (expected Left \"divide by zero\")\n", v),
        Err(e) => println!("  error: {}\n", e),
    }

    // Demo 3: IO echo
    println!("Demo 3: IO echo (read then write)");
    let inputs = Rc::new(vec!["ping".to_string()]);
    let outputs = Rc::new(RefCell::new(Vec::new()));
    let prog = bind(read(), Rc::new(|s| write(s)));
    let handled = handle_io(prog, inputs, 0, Rc::clone(&outputs));
    run(handled).ok();
    println!("  outputs: {:?} (expected [\"ping\"])\n", outputs.borrow());

    // Demo 4: State + IO + Exception together
    println!("Demo 4: State + IO + Exception (capped accumulate, cap=50)");
    let prog = bind(capped_accumulate(50), Rc::new(|_| capped_accumulate(50)));
    let inputs = Rc::new(vec!["30".to_string(), "40".to_string()]);
    let outputs = Rc::new(RefCell::new(Vec::new()));
    let handled = handle_exception(handle_io(
        handle_state(prog, Value::Int(0)),
        inputs,
        0,
        outputs,
    ));
    match run(handled) {
        Ok(v) => println!("  result: {} (expected Left \"cap exceeded\")\n", v),
        Err(e) => println!("  error: {}\n", e),
    }

    // Demo 5: Mid-program catch
    println!("Demo 5: Mid-program catch (recover from divide-by-zero)");
    let prog = bind(handle_exception(safe_div(10, 0)), Rc::new(|either| match either {
        Value::Right(v) => pure(*v),
        Value::Left(e) => pure(Value::Str(format!("caught: {}", e))),
        _ => pure(Value::Unit),
    }));
    match run(handle_exception(prog)) {
        Ok(v) => println!("  result: {} (expected Right \"caught: ...\")\n", v),
        Err(e) => println!("  error: {}\n", e),
    }
}
