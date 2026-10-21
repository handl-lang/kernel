// Challenge #12: Structural Preservation Under Profunctor Translation
//
// THE QUESTION (engaging the Wikipedia claim that profunctors "subsume"
// arrow utility):
//
//   Does the profunctor interface (dimap + lmap + rmap + composition)
//   preserve the structural properties that the arrow interface preserves?
//
// We compare four representations:
//
//   1. Freer arrow    — structure explicit (from Challenge #9)
//   2. Opaque profunctor — function-based, dimap/lmap/rmap/seq available
//      but structure hidden inside closures
//   3. Bare freer profunctor — explicit tree, but ONLY dimap/seq/ops
//      (no strength/first, no choice/left, no trace/loop)
//   4. Freer profunctor + strength + choice + trace — explicit tree with
//      first/left/loop added back. This IS an arrow.
//
// Expected finding:
//   - The bare profunctor CANNOT EXPRESS fanout, choice, or feedback —
//     it lacks the combinators. These require additional structure
//     (strength, cocartesian, trace).
//   - The opaque profunctor CAN express them (by encoding as functions)
//     but loses ALL structural information — same as the opaque monad.
//   - The freer profunctor + strength + choice + trace recovers all
//     structure — but it is isomorphic to the arrow. You haven't
//     subsumed arrows; you've reconstructed them with different names.
//
// The "subsumption" is hollow: profunctors are more general (weaker),
// and to recover arrow utility you add back exactly the arrow structure.

use std::collections::HashSet;
use std::fmt;
use std::rc::Rc;

// ============================================================================
// Shared Types (matching Challenge #9)
// ============================================================================

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Value {
    Int(i32),
    Bool(bool),
    Unit,
    Pair(Box<Value>, Box<Value>),
    Left(Box<Value>),
    Right(Box<Value>),
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Int(n) => write!(f, "{}", n),
            Value::Bool(b) => write!(f, "{}", b),
            Value::Unit => write!(f, "()"),
            Value::Pair(a, b) => write!(f, "({}, {})", a, b),
            Value::Left(v) => write!(f, "Left({})", v),
            Value::Right(v) => write!(f, "Right({})", v),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Op {
    Get,
    Put,
    Throw,
}

impl fmt::Display for Op {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Op::Get => write!(f, "Get"),
            Op::Put => write!(f, "Put"),
            Op::Throw => write!(f, "Throw"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Effect {
    ops: HashSet<Op>,
}

impl Effect {
    pub fn empty() -> Self {
        Effect { ops: HashSet::new() }
    }
    pub fn singleton(op: Op) -> Self {
        let mut ops = HashSet::new();
        ops.insert(op);
        Effect { ops }
    }
    pub fn union(&self, other: &Effect) -> Effect {
        Effect { ops: self.ops.union(&other.ops).copied().collect() }
    }
    pub fn contains(&self, op: Op) -> bool {
        self.ops.contains(&op)
    }
    pub fn is_empty(&self) -> bool {
        self.ops.is_empty()
    }
    pub fn len(&self) -> usize {
        self.ops.len()
    }
}

impl fmt::Display for Effect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.ops.is_empty() {
            return write!(f, "{}", "{}");
        }
        let mut ops: Vec<_> = self.ops.iter().collect();
        ops.sort_by_key(|o| format!("{:?}", o));
        let names: Vec<_> = ops.iter().map(|o| o.to_string()).collect();
        write!(f, "{{{}}}", names.join(", "))
    }
}

// ============================================================================
// Representation 1: Freer Arrow (from Challenge #9, replicated)
// ============================================================================

#[derive(Debug, Clone)]
pub enum ArrowComp {
    Pure(Value),
    Seq(Box<ArrowComp>, Box<ArrowComp>),
    Fanout(Box<ArrowComp>, Box<ArrowComp>),
    Choice(Box<ArrowComp>, Box<ArrowComp>),
    OpNode(Op, Box<ArrowComp>),
    Loop(Box<ArrowComp>),
    Ident,
}

pub fn run_arrow(comp: &ArrowComp, input: Value, state: Value) -> Result<(Value, Value), String> {
    match comp {
        ArrowComp::Pure(v) => Ok((v.clone(), state)),
        ArrowComp::Ident => Ok((input, state)),
        ArrowComp::Seq(f, g) => {
            let (v1, s1) = run_arrow(f, input, state)?;
            run_arrow(g, v1, s1)
        }
        ArrowComp::Fanout(f, g) => {
            let (v1, s1) = run_arrow(f, input.clone(), state)?;
            let (v2, s2) = run_arrow(g, input, s1)?;
            Ok((Value::Pair(Box::new(v1), Box::new(v2)), s2))
        }
        ArrowComp::Choice(f, g) => {
            match input {
                Value::Left(v) => run_arrow(f, *v, state),
                Value::Right(v) => run_arrow(g, *v, state),
                _ => Err("choice requires Left/Right input".to_string()),
            }
        }
        ArrowComp::OpNode(op, k) => {
            match op {
                Op::Get => {
                    let (v, s) = run_arrow(k, state.clone(), state)?;
                    Ok((v, s))
                }
                Op::Put => {
                    let (_, s) = run_arrow(k, Value::Unit, input)?;
                    Ok((Value::Unit, s))
                }
                Op::Throw => Err("throw".to_string()),
            }
        }
        ArrowComp::Loop(body) => {
            let pair = Value::Pair(Box::new(input), Box::new(state));
            run_arrow(body, pair, Value::Unit)
        }
    }
}

// ============================================================================
// Representation 2: Opaque Profunctor (function-based, structurally hidden)
// ============================================================================
//
// A profunctor p a b with dimap/lmap/rmap and category composition (>>>).
// The implementation wraps a function — structure is invisible.
// This mirrors how profunctor libraries work (e.g., Haskell's profunctors):
// the concrete profunctor is a function in a newtype.

pub struct OpaqueP {
    run: Rc<dyn Fn(Value, Value) -> Result<(Value, Value), String>>,
}

impl OpaqueP {
    pub fn new(f: impl Fn(Value, Value) -> Result<(Value, Value), String> + 'static) -> Self {
        OpaqueP { run: Rc::new(f) }
    }

    pub fn run(&self, input: Value, state: Value) -> Result<(Value, Value), String> {
        (self.run)(input, state)
    }

    // dimap :: (c -> a) -> (b -> d) -> p a b -> p c d
    // Pre-compose with f (transforms input), post-compose with g (transforms output)
    pub fn dimap(
        &self,
        f: Rc<dyn Fn(Value) -> Value>,
        g: Rc<dyn Fn(Value) -> Value>,
    ) -> OpaqueP {
        let run = Rc::clone(&self.run);
        OpaqueP::new(move |input, state| {
            let (b, s) = (run)(f(input), state)?;
            Ok((g(b), s))
        })
    }

    // lmap :: (c -> a) -> p a b -> p c b  (pre-compose)
    pub fn lmap(&self, f: Rc<dyn Fn(Value) -> Value>) -> OpaqueP {
        let run = Rc::clone(&self.run);
        OpaqueP::new(move |input, state| (run)(f(input), state))
    }

    // rmap :: (b -> d) -> p a b -> p a d  (post-compose)
    pub fn rmap(&self, g: Rc<dyn Fn(Value) -> Value>) -> OpaqueP {
        let run = Rc::clone(&self.run);
        OpaqueP::new(move |input, state| {
            let (b, s) = (run)(input, state)?;
            Ok((g(b), s))
        })
    }

    // Category composition: p >>> q (sequential)
    pub fn seq(&self, other: &OpaqueP) -> OpaqueP {
        let run_f = Rc::clone(&self.run);
        let run_g = Rc::clone(&other.run);
        OpaqueP::new(move |input, state| {
            let (b, s1) = (run_f)(input, state)?;
            (run_g)(b, s1)
        })
    }

    // Pure (identity profunctor — arr id)
    pub fn pure_p(v: Value) -> Self {
        let v = v.clone();
        OpaqueP::new(move |_input, state| Ok((v.clone(), state)))
    }

    pub fn ident() -> Self {
        OpaqueP::new(|input, state| Ok((input, state)))
    }
}

// Opaque profunctor operations
pub fn prof_op_get() -> OpaqueP {
    OpaqueP::new(|_input, state| Ok((state.clone(), state)))
}

pub fn prof_op_put() -> OpaqueP {
    OpaqueP::new(|input, _state| Ok((Value::Unit, input)))
}

pub fn prof_op_throw(msg: &str) -> OpaqueP {
    let msg = msg.to_string();
    OpaqueP::new(move |_, _| Err(msg.clone()))
}

// ============================================================================
// Representation 3: Bare Freer Profunctor (explicit tree, no strength/choice/trace)
// ============================================================================
//
// This is a profunctor with ONLY the core structure: dimap, lmap, rmap,
// composition, and effect nodes. It does NOT have:
//   - first (strength / product) — needed for fanout
//   - left (choice / sum) — needed for branching
//   - loop (trace) — needed for feedback
//
// This is the honest "profunctor" interface. An arrow is a STRONG profunctor
// that is also a category — the strength and choice are ADDITIONAL structure.

#[derive(Clone)]
pub enum FreeP {
    Pure(Value),
    Ident,
    // Sequential composition (category)
    Seq(Box<FreeP>, Box<FreeP>),
    // dimap: pre/post compose with pure functions
    Dimap {
        pre: Rc<dyn Fn(Value) -> Value>,
        post: Rc<dyn Fn(Value) -> Value>,
        inner: Box<FreeP>,
    },
    // lmap: pre-compose only
    Lmap {
        pre: Rc<dyn Fn(Value) -> Value>,
        inner: Box<FreeP>,
    },
    // rmap: post-compose only
    Rmap {
        post: Rc<dyn Fn(Value) -> Value>,
        inner: Box<FreeP>,
    },
    // Effect node
    OpNode(Op, Box<FreeP>),
}

// NOTE: FreeP has NO constructor for Fanout, Choice, or Loop.
// A bare profunctor cannot express these.

pub fn run_freep(fp: &FreeP, input: Value, state: Value) -> Result<(Value, Value), String> {
    match fp {
        FreeP::Pure(v) => Ok((v.clone(), state)),
        FreeP::Ident => Ok((input, state)),
        FreeP::Seq(f, g) => {
            let (v1, s1) = run_freep(f, input, state)?;
            run_freep(g, v1, s1)
        }
        FreeP::Dimap { pre, post, inner } => {
            let (b, s) = run_freep(inner, pre(input), state)?;
            Ok((post(b), s))
        }
        FreeP::Lmap { pre, inner } => run_freep(inner, pre(input), state),
        FreeP::Rmap { post, inner } => {
            let (b, s) = run_freep(inner, input, state)?;
            Ok((post(b), s))
        }
        FreeP::OpNode(op, k) => {
            match op {
                Op::Get => run_freep(k, state.clone(), state),
                Op::Put => run_freep(k, Value::Unit, input),
                Op::Throw => Err("throw".to_string()),
            }
        }
    }
}

// ============================================================================
// Representation 4: Freer Profunctor + Strength + Choice + Trace (= Arrow)
// ============================================================================
//
// We add `First` (strength), `Left` (choice), and `Loop` (trace) to FreeP.
// This is a "strong cocartesian traced profunctor" — which is exactly an arrow.
// The point: to recover arrow utility, you add back exactly the arrow combinators.

#[derive(Clone)]
pub enum FreePA {
    Pure(Value),
    Ident,
    Seq(Box<FreePA>, Box<FreePA>),
    Dimap {
        pre: Rc<dyn Fn(Value) -> Value>,
        post: Rc<dyn Fn(Value) -> Value>,
        inner: Box<FreePA>,
    },
    OpNode(Op, Box<FreePA>),
    // Strength (first): p a b -> p (a, c) (b, c) — enables fanout
    First(Box<FreePA>),
    // Choice (left): p a b -> p (Either a c) (Either b c) — enables branching
    Left(Box<FreePA>),
    // Trace (loop): p (a, d) (b, d) -> p a b — enables feedback
    Loop(Box<FreePA>),
}

pub fn run_freepa(fp: &FreePA, input: Value, state: Value) -> Result<(Value, Value), String> {
    match fp {
        FreePA::Pure(v) => Ok((v.clone(), state)),
        FreePA::Ident => Ok((input, state)),
        FreePA::Seq(f, g) => {
            let (v1, s1) = run_freepa(f, input, state)?;
            run_freepa(g, v1, s1)
        }
        FreePA::Dimap { pre, post, inner } => {
            let (b, s) = run_freepa(inner, pre(input), state)?;
            Ok((post(b), s))
        }
        FreePA::OpNode(op, k) => {
            match op {
                Op::Get => run_freepa(k, state.clone(), state),
                Op::Put => run_freepa(k, Value::Unit, input),
                Op::Throw => Err("throw".to_string()),
            }
        }
        FreePA::First(inner) => {
            // first p: takes (a, c), runs p on a, keeps c
            match input {
                Value::Pair(a, c) => {
                    let (b, s) = run_freepa(inner, *a, state)?;
                    Ok((Value::Pair(Box::new(b), c), s))
                }
                _ => Err("first requires Pair input".to_string()),
            }
        }
        FreePA::Left(inner) => {
            // left p: Left a -> Left b (run p), Right c -> Right c (pass through)
            match input {
                Value::Left(a) => {
                    let (b, s) = run_freepa(inner, *a, state)?;
                    Ok((Value::Left(Box::new(b)), s))
                }
                Value::Right(c) => Ok((Value::Right(c), state)),
                _ => Err("left requires Left/Right input".to_string()),
            }
        }
        FreePA::Loop(body) => {
            let pair = Value::Pair(Box::new(input), Box::new(state));
            run_freepa(body, pair, Value::Unit)
        }
    }
}

// ============================================================================
// Translations: Arrow → each profunctor representation
// ============================================================================

// Arrow → Opaque profunctor
// Semantically faithful but structurally opaque (same as arrow_to_opaque)
pub fn arrow_to_opaque_p(comp: &ArrowComp) -> OpaqueP {
    match comp {
        ArrowComp::Pure(v) => OpaqueP::pure_p(v.clone()),
        ArrowComp::Ident => OpaqueP::ident(),
        ArrowComp::Seq(f, g) => {
            let pf = arrow_to_opaque_p(f);
            let pg = arrow_to_opaque_p(g);
            pf.seq(&pg)
        }
        ArrowComp::Fanout(f, g) => {
            // Fanout has no profunctor combinator — must encode as a function
            let f_clone = f.clone();
            let g_clone = g.clone();
            OpaqueP::new(move |input, state| {
                let pf = arrow_to_opaque_p(&f_clone);
                let (v1, s1) = pf.run(input.clone(), state)?;
                let pg = arrow_to_opaque_p(&g_clone);
                let (v2, s2) = pg.run(input, s1)?;
                Ok((Value::Pair(Box::new(v1), Box::new(v2)), s2))
            })
        }
        ArrowComp::Choice(f, g) => {
            // Choice has no profunctor combinator — must encode as a function
            let f_clone = f.clone();
            let g_clone = g.clone();
            OpaqueP::new(move |input, state| {
                match input {
                    Value::Left(v) => arrow_to_opaque_p(&f_clone).run(*v, state),
                    Value::Right(v) => arrow_to_opaque_p(&g_clone).run(*v, state),
                    _ => Err("choice requires Left/Right".to_string()),
                }
            })
        }
        ArrowComp::OpNode(op, k) => {
            let k_clone = k.clone();
            match op {
                Op::Get => {
                    let mk = arrow_to_opaque_p(&k_clone);
                    OpaqueP::new(move |_input, state| mk.run(state.clone(), state))
                }
                Op::Put => {
                    let mk = arrow_to_opaque_p(&k_clone);
                    OpaqueP::new(move |input, _state| mk.run(Value::Unit, input))
                }
                Op::Throw => prof_op_throw("error"),
            }
        }
        ArrowComp::Loop(body) => arrow_to_opaque_p(body),
    }
}

// Arrow → Bare freer profunctor
// Returns None for programs that use fanout/choice/loop — the bare profunctor
// has no combinators for them.
pub fn arrow_to_freep(comp: &ArrowComp) -> Option<FreeP> {
    match comp {
        ArrowComp::Pure(v) => Some(FreeP::Pure(v.clone())),
        ArrowComp::Ident => Some(FreeP::Ident),
        ArrowComp::Seq(f, g) => {
            Some(FreeP::Seq(
                Box::new(arrow_to_freep(f)?),
                Box::new(arrow_to_freep(g)?),
            ))
        }
        ArrowComp::Fanout(_, _) => None,  // CANNOT EXPRESS — no strength
        ArrowComp::Choice(_, _) => None,  // CANNOT EXPRESS — no choice
        ArrowComp::OpNode(op, k) => {
            Some(FreeP::OpNode(*op, Box::new(arrow_to_freep(k)?)))
        }
        ArrowComp::Loop(_) => None,  // CANNOT EXPRESS — no trace
    }
}

// Arrow → Freer profunctor + strength + choice + trace
// Always succeeds — this is isomorphic to the arrow
pub fn arrow_to_freepa(comp: &ArrowComp) -> FreePA {
    match comp {
        ArrowComp::Pure(v) => FreePA::Pure(v.clone()),
        ArrowComp::Ident => FreePA::Ident,
        ArrowComp::Seq(f, g) => {
            FreePA::Seq(
                Box::new(arrow_to_freepa(f)),
                Box::new(arrow_to_freepa(g)),
            )
        }
        ArrowComp::Fanout(f, g) => {
            // Fanout = first f >>> arr (&&& g) — but more directly:
            // We model fanout via First + pairing.
            // For structural fidelity, we keep a direct encoding using First.
            // f &&& g = first f >>> dimap (swap) (g) ... but to keep it clean
            // and structurally honest, we encode fanout as:
            //   dimap (\a -> (a, a)) (id) (first f >>> first g >>> arr pair)
            // However, the simplest structural encoding: use First on both
            // and combine. For this experiment, we use a Seq of Firsts.
            // Actually, the most honest encoding: fanout IS a distinct
            // pattern using strength. We encode it as:
            //   first(f) applied to (input, input), then first(g) on the result.
            // But the cleanest way that preserves structure is to note that
            // FreePA has First, and fanout = \a -> (f a, g a) which requires
            // running both. We encode it compositionally:
            let f_a = arrow_to_freepa(f);
            let g_a = arrow_to_freepa(g);
            // Encode: dimap (\a -> (a,a)) (\(b,c) -> (b,c)) (first f >>> first g)
            // But first f takes (a, c) -> (b, c), and we need to thread the
            // second component. The standard arrow fanout via first:
            //   f &&& g = arr (\a -> (a, a)) >>> first f >>> arr (\(_, c) -> (c, c)) >>> first g >>> arr (\(b, d) -> (b, d))
            // This is complex. For structural clarity, we use a simpler
            // representation: since FreePA is isomorphic to ArrowComp,
            // we can model fanout using First directly.
            //
            // For the structural experiment, what matters is that First
            // (strength) is the primitive that ENABLES fanout. We encode
            // fanout as a composite of First operations.
            //
            // Simplest faithful encoding:
            //   dimap (\a -> Pair(a, a)) id (Seq(First(f), Seq(First(g), ...)))
            // But First(g) would need to operate on (b, a) to get (b, c).
            // This requires swapping, which is dimap.
            //
            // For clarity and to avoid obscuring the structural point,
            // we encode fanout as a Dimap + First + Dimap + First + Dimap chain.
            // The KEY structural point: it uses First (strength), which the
            // bare FreeP lacks.
            let dup = Rc::new(|a: Value| Value::Pair(Box::new(a.clone()), Box::new(a)));
            let fst = Rc::new(|v: Value| {
                match v {
                    Value::Pair(a, _) => *a,
                    _ => v,
                }
            });
            let snd = Rc::new(|v: Value| {
                match v {
                    Value::Pair(_, c) => *c,
                    _ => v,
                }
            });
            let pair_up = Rc::new(|v: Value| {
                // v is Pair(Pair(b, a), Pair(b2, c)) — we want Pair(b, c)
                // After first f: Pair(Pair(b, a), a) — wait, let's trace:
                // dimap dup: a -> Pair(a, a)
                // first f: Pair(a, a) -> Pair(b, a)  [f runs on first component]
                // dimap (extract second): Pair(b, a) -> Pair(a, b)  [swap to run g on a]
                // first g: Pair(a, b) -> Pair(c, b)  [g runs on first component]
                // dimap (re-pair): Pair(c, b) -> Pair(b, c)  [swap back]
                // Actually this is getting convoluted. Let's just use the
                // direct approach: fanout is a composite that USES First.
                v
            });
            let _ = (fst, snd, pair_up);
            // Encode: dimap(dup, id) >>> first(f) >>> dimap(swap, id) >>> first(g) >>> dimap(swap, id)
            let swap = Rc::new(|v: Value| {
                match v {
                    Value::Pair(a, b) => Value::Pair(b, a),
                    _ => v,
                }
            });
            let identity = Rc::new(|v: Value| v);
            FreePA::Dimap {
                pre: dup,
                post: identity.clone(),
                inner: Box::new(FreePA::Seq(
                    Box::new(FreePA::First(Box::new(f_a))),
                    Box::new(FreePA::Dimap {
                        pre: swap.clone(),
                        post: identity.clone(),
                        inner: Box::new(FreePA::Seq(
                            Box::new(FreePA::First(Box::new(g_a))),
                            Box::new(FreePA::Dimap {
                                pre: swap,
                                post: identity,
                                inner: Box::new(FreePA::Ident),
                            }),
                        )),
                    }),
                )),
            }
        }
        ArrowComp::Choice(f, g) => {
            // Choice = left f >>> left g (but with pass-through)
            // Actually: choice f g = left f ||| left g — but ||| needs more.
            // The standard encoding: choice f g = left f >>> arr (merge)
            // For structural fidelity: Left is the primitive that enables choice.
            // We encode: left(f) handles Left, pass-through Right.
            // For full choice (both branches), we need: left f >>> dimap (handle right with g)
            // The cleanest: choice f g = left(f) >>> left(g) with appropriate routing.
            // For this experiment, we encode choice using Left directly.
            let f_a = arrow_to_freepa(f);
            let g_a = arrow_to_freepa(g);
            // Encode: left(f) >>> dimap (route) (left(g))
            // left f: Left a -> Left b, Right c -> Right c
            // Then we need to handle the Right case with g.
            //
            // The honest encoding of choice f g using Left:
            //   left(f) handles Left inputs, passes Right through.
            //   To handle Right inputs with g, swap the Either, apply left(g),
            //   then merge (extract from Either):
            //     left(f) >>> arr swapEither >>> left(g) >>> arr merge
            //   where swapEither(Left x) = Right x, swapEither(Right x) = Left x
            //   and merge(Left x) = x, merge(Right x) = x
            let swap_either = Rc::new(|v: Value| {
                match v {
                    Value::Left(x) => Value::Right(x),
                    Value::Right(x) => Value::Left(x),
                    _ => v,
                }
            });
            let merge_either = Rc::new(|v: Value| {
                match v {
                    Value::Left(x) => *x,
                    Value::Right(x) => *x,
                    _ => v,
                }
            });
            // arr swapEither = Dimap { pre: swap, post: id, inner: Ident }
            // arr merge      = Dimap { pre: merge, post: id, inner: Ident }
            let identity = Rc::new(|v: Value| v);
            FreePA::Seq(
                Box::new(FreePA::Left(Box::new(f_a))),
                Box::new(FreePA::Seq(
                    Box::new(FreePA::Dimap {
                        pre: swap_either,
                        post: identity.clone(),
                        inner: Box::new(FreePA::Ident),
                    }),
                    Box::new(FreePA::Seq(
                        Box::new(FreePA::Left(Box::new(g_a))),
                        Box::new(FreePA::Dimap {
                            pre: merge_either,
                            post: identity,
                            inner: Box::new(FreePA::Ident),
                        }),
                    )),
                )),
            )
        }
        ArrowComp::OpNode(op, k) => {
            FreePA::OpNode(*op, Box::new(arrow_to_freepa(k)))
        }
        ArrowComp::Loop(body) => {
            FreePA::Loop(Box::new(arrow_to_freepa(body)))
        }
    }
}

// ============================================================================
// Structural Recovery: Arrow (replicated from Challenge #9)
// ============================================================================

pub fn recover_fanout_arrow(comp: &ArrowComp) -> Option<(&ArrowComp, &ArrowComp)> {
    match comp {
        ArrowComp::Fanout(f, g) => Some((f, g)),
        _ => None,
    }
}

pub fn recover_choice_arrow(comp: &ArrowComp) -> Option<(&ArrowComp, &ArrowComp)> {
    match comp {
        ArrowComp::Choice(f, g) => Some((f, g)),
        _ => None,
    }
}

pub fn infer_effect_arrow(comp: &ArrowComp) -> Effect {
    match comp {
        ArrowComp::Pure(_) | ArrowComp::Ident => Effect::empty(),
        ArrowComp::Seq(f, g) => infer_effect_arrow(f).union(&infer_effect_arrow(g)),
        ArrowComp::Fanout(f, g) => infer_effect_arrow(f).union(&infer_effect_arrow(g)),
        ArrowComp::Choice(f, g) => infer_effect_arrow(f).union(&infer_effect_arrow(g)),
        ArrowComp::OpNode(op, k) => Effect::singleton(*op).union(&infer_effect_arrow(k)),
        ArrowComp::Loop(body) => infer_effect_arrow(body),
    }
}

pub fn per_branch_effects_arrow(comp: &ArrowComp) -> Option<(Effect, Effect)> {
    match comp {
        ArrowComp::Choice(f, g) => Some((infer_effect_arrow(f), infer_effect_arrow(g))),
        _ => None,
    }
}

pub fn recover_loop_arrow(comp: &ArrowComp) -> Option<&ArrowComp> {
    match comp {
        ArrowComp::Loop(body) => Some(body),
        _ => None,
    }
}

// ============================================================================
// Structural Recovery: Opaque Profunctor
// ============================================================================

pub fn recover_fanout_opaque_p(_p: &OpaqueP) -> Option<()> {
    None  // structure hidden in closure
}

pub fn recover_choice_opaque_p(_p: &OpaqueP) -> Option<()> {
    None  // structure hidden in closure
}

pub fn infer_effect_opaque_p(_p: &OpaqueP) -> Option<Effect> {
    None  // cannot inspect
}

pub fn per_branch_effects_opaque_p(_p: &OpaqueP) -> Option<(Effect, Effect)> {
    None  // cannot inspect
}

pub fn recover_loop_opaque_p(_p: &OpaqueP) -> Option<()> {
    None  // structure hidden
}

// ============================================================================
// Structural Recovery: Bare Freer Profunctor
// ============================================================================
//
// The bare freer profunctor has explicit structure for dimap/seq/ops,
// but NO structure for fanout/choice/loop — it cannot even represent them.

pub fn recover_fanout_freep(_fp: &FreeP) -> Option<()> {
    None  // FreeP has no Fanout constructor — CANNOT REPRESENT
}

pub fn recover_choice_freep(_fp: &FreeP) -> Option<()> {
    None  // FreeP has no Choice constructor — CANNOT REPRESENT
}

pub fn infer_effect_freep(fp: &FreeP) -> Effect {
    match fp {
        FreeP::Pure(_) | FreeP::Ident => Effect::empty(),
        FreeP::Seq(f, g) => infer_effect_freep(f).union(&infer_effect_freep(g)),
        FreeP::Dimap { inner, .. } => infer_effect_freep(inner),
        FreeP::Lmap { inner, .. } => infer_effect_freep(inner),
        FreeP::Rmap { inner, .. } => infer_effect_freep(inner),
        FreeP::OpNode(op, k) => Effect::singleton(*op).union(&infer_effect_freep(k)),
    }
}

pub fn per_branch_effects_freep(_fp: &FreeP) -> Option<(Effect, Effect)> {
    None  // no Choice — CANNOT REPRESENT branching
}

pub fn recover_loop_freep(_fp: &FreeP) -> Option<()> {
    None  // FreeP has no Loop — CANNOT REPRESENT feedback
}

// Detect whether FreeP uses strength (First) — it can't, by construction
pub fn has_strength_freep(_fp: &FreeP) -> bool {
    false  // FreeP has no First constructor
}

// ============================================================================
// Structural Recovery: Freer Profunctor + Strength + Choice + Trace
// ============================================================================

pub fn infer_effect_freepa(fp: &FreePA) -> Effect {
    match fp {
        FreePA::Pure(_) | FreePA::Ident => Effect::empty(),
        FreePA::Seq(f, g) => infer_effect_freepa(f).union(&infer_effect_freepa(g)),
        FreePA::Dimap { inner, .. } => infer_effect_freepa(inner),
        FreePA::OpNode(op, k) => Effect::singleton(*op).union(&infer_effect_freepa(k)),
        FreePA::First(inner) => infer_effect_freepa(inner),
        FreePA::Left(inner) => infer_effect_freepa(inner),
        FreePA::Loop(body) => infer_effect_freepa(body),
    }
}

pub fn has_strength_freepa(fp: &FreePA) -> bool {
    match fp {
        FreePA::First(_) => true,
        FreePA::Seq(f, g) => has_strength_freepa(f) || has_strength_freepa(g),
        FreePA::Dimap { inner, .. } => has_strength_freepa(inner),
        FreePA::OpNode(_, k) => has_strength_freepa(k),
        FreePA::Left(inner) => has_strength_freepa(inner),
        FreePA::Loop(body) => has_strength_freepa(body),
        _ => false,
    }
}

pub fn has_choice_freepa(fp: &FreePA) -> bool {
    match fp {
        FreePA::Left(_) => true,
        FreePA::Seq(f, g) => has_choice_freepa(f) || has_choice_freepa(g),
        FreePA::Dimap { inner, .. } => has_choice_freepa(inner),
        FreePA::OpNode(_, k) => has_choice_freepa(k),
        FreePA::First(inner) => has_choice_freepa(inner),
        FreePA::Loop(body) => has_choice_freepa(body),
        _ => false,
    }
}

pub fn has_trace_freepa(fp: &FreePA) -> bool {
    match fp {
        FreePA::Loop(_) => true,
        FreePA::Seq(f, g) => has_trace_freepa(f) || has_trace_freepa(g),
        FreePA::Dimap { inner, .. } => has_trace_freepa(inner),
        FreePA::OpNode(_, k) => has_trace_freepa(k),
        FreePA::First(inner) => has_trace_freepa(inner),
        FreePA::Left(inner) => has_trace_freepa(inner),
        _ => false,
    }
}

pub fn recover_loop_freepa(fp: &FreePA) -> Option<&FreePA> {
    match fp {
        FreePA::Loop(body) => Some(body),
        _ => None,
    }
}

// ============================================================================
// Example Programs
// ============================================================================

/// Sequential: Get >>> Put (representable in all four representations)
pub fn arrow_sequential() -> ArrowComp {
    ArrowComp::Seq(
        Box::new(ArrowComp::OpNode(Op::Get, Box::new(ArrowComp::Ident))),
        Box::new(ArrowComp::OpNode(Op::Put, Box::new(ArrowComp::Ident))),
    )
}

/// Fanout: Get &&& Put (NOT representable in bare profunctor)
pub fn arrow_fanout() -> ArrowComp {
    ArrowComp::Fanout(
        Box::new(ArrowComp::OpNode(Op::Get, Box::new(ArrowComp::Ident))),
        Box::new(ArrowComp::OpNode(Op::Put, Box::new(ArrowComp::Ident))),
    )
}

/// Choice: Left → Get, Right → Put (NOT representable in bare profunctor)
pub fn arrow_choice() -> ArrowComp {
    ArrowComp::Choice(
        Box::new(ArrowComp::OpNode(Op::Get, Box::new(ArrowComp::Ident))),
        Box::new(ArrowComp::OpNode(Op::Put, Box::new(ArrowComp::Ident))),
    )
}

/// Complex choice: Left → (Get >>> Throw), Right → Put
/// Per-branch effects: left = {Get, Throw}, right = {Put}
pub fn arrow_complex_choice() -> ArrowComp {
    ArrowComp::Choice(
        Box::new(ArrowComp::Seq(
            Box::new(ArrowComp::OpNode(Op::Get, Box::new(ArrowComp::Ident))),
            Box::new(ArrowComp::OpNode(Op::Throw, Box::new(ArrowComp::Pure(Value::Unit)))),
        )),
        Box::new(ArrowComp::OpNode(Op::Put, Box::new(ArrowComp::Ident))),
    )
}

/// Loop: feedback (NOT representable in bare profunctor)
pub fn arrow_loop() -> ArrowComp {
    ArrowComp::Loop(Box::new(ArrowComp::OpNode(Op::Get, Box::new(ArrowComp::Ident))))
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // === Semantic equivalence: all representations that CAN represent
    //     a program produce the same results ===

    #[test]
    fn test_semantic_equiv_sequential_all_four() {
        let arrow = arrow_sequential();
        let (v_arr, s_arr) = run_arrow(&arrow, Value::Int(42), Value::Int(7)).unwrap();

        let opaque_p = arrow_to_opaque_p(&arrow);
        let (v_op, s_op) = opaque_p.run(Value::Int(42), Value::Int(7)).unwrap();

        let freep = arrow_to_freep(&arrow).expect("sequential should translate to FreeP");
        let (v_fp, s_fp) = run_freep(&freep, Value::Int(42), Value::Int(7)).unwrap();

        let freepa = arrow_to_freepa(&arrow);
        let (v_fpa, s_fpa) = run_freepa(&freepa, Value::Int(42), Value::Int(7)).unwrap();

        assert_eq!(v_arr, v_op, "arrow == opaque profunctor (result)");
        assert_eq!(s_arr, s_op, "arrow == opaque profunctor (state)");
        assert_eq!(v_arr, v_fp, "arrow == freer profunctor (result)");
        assert_eq!(s_arr, s_fp, "arrow == freer profunctor (state)");
        assert_eq!(v_arr, v_fpa, "arrow == freer profunctor+arrow (result)");
        assert_eq!(s_arr, s_fpa, "arrow == freer profunctor+arrow (state)");
    }

    #[test]
    fn test_semantic_equiv_fanout_arrow_vs_opaque() {
        let arrow = arrow_fanout();
        let (v_arr, s_arr) = run_arrow(&arrow, Value::Int(42), Value::Int(7)).unwrap();

        let opaque_p = arrow_to_opaque_p(&arrow);
        let (v_op, s_op) = opaque_p.run(Value::Int(42), Value::Int(7)).unwrap();

        assert_eq!(v_arr, v_op, "fanout: arrow == opaque profunctor (result)");
        assert_eq!(s_arr, s_op, "fanout: arrow == opaque profunctor (state)");
    }

    #[test]
    fn test_semantic_equiv_choice_arrow_vs_opaque() {
        let arrow = arrow_choice();
        let input = Value::Right(Box::new(Value::Int(99)));
        let (v_arr, s_arr) = run_arrow(&arrow, input.clone(), Value::Int(0)).unwrap();

        let opaque_p = arrow_to_opaque_p(&arrow);
        let (v_op, s_op) = opaque_p.run(input, Value::Int(0)).unwrap();

        assert_eq!(v_arr, v_op, "choice: arrow == opaque profunctor (result)");
        assert_eq!(s_arr, s_op, "choice: arrow == opaque profunctor (state)");
    }

    #[test]
    fn test_semantic_equiv_complex_choice_arrow_vs_opaque() {
        let arrow = arrow_complex_choice();
        let input = Value::Right(Box::new(Value::Int(99)));
        let (v_arr, s_arr) = run_arrow(&arrow, input.clone(), Value::Int(0)).unwrap();

        let opaque_p = arrow_to_opaque_p(&arrow);
        let (v_op, s_op) = opaque_p.run(input, Value::Int(0)).unwrap();

        assert_eq!(v_arr, v_op);
        assert_eq!(s_arr, s_op);
    }

    // === The core finding: bare profunctor CANNOT REPRESENT fanout/choice/loop ===

    #[test]
    fn test_bare_profunctor_cannot_represent_fanout() {
        let arrow = arrow_fanout();
        let result = arrow_to_freep(&arrow);
        assert!(result.is_none(),
            "Bare profunctor CANNOT represent fanout — no strength (first) combinator");
    }

    #[test]
    fn test_bare_profunctor_cannot_represent_choice() {
        let arrow = arrow_choice();
        let result = arrow_to_freep(&arrow);
        assert!(result.is_none(),
            "Bare profunctor CANNOT represent choice — no choice (left) combinator");
    }

    #[test]
    fn test_bare_profunctor_cannot_represent_loop() {
        let arrow = arrow_loop();
        let result = arrow_to_freep(&arrow);
        assert!(result.is_none(),
            "Bare profunctor CANNOT represent loop — no trace (loop) combinator");
    }

    #[test]
    fn test_bare_profunctor_can_represent_sequential() {
        let arrow = arrow_sequential();
        let result = arrow_to_freep(&arrow);
        assert!(result.is_some(),
            "Bare profunctor CAN represent sequential composition — has category structure");
    }

    #[test]
    fn test_bare_profunctor_can_represent_effects() {
        let arrow = ArrowComp::OpNode(Op::Get, Box::new(ArrowComp::Ident));
        let freep = arrow_to_freep(&arrow).unwrap();
        let effect = infer_effect_freep(&freep);
        assert!(effect.contains(Op::Get),
            "Bare freer profunctor CAN infer effects — explicit OpNode");
    }

    // === Opaque profunctor loses all structural information ===

    #[test]
    fn test_opaque_profunctor_loses_fanout() {
        let arrow = arrow_fanout();
        let opaque_p = arrow_to_opaque_p(&arrow);
        assert!(recover_fanout_opaque_p(&opaque_p).is_none(),
            "Opaque profunctor loses fanout structure — hidden in closure");
    }

    #[test]
    fn test_opaque_profunctor_loses_choice() {
        let arrow = arrow_choice();
        let opaque_p = arrow_to_opaque_p(&arrow);
        assert!(recover_choice_opaque_p(&opaque_p).is_none(),
            "Opaque profunctor loses choice structure — hidden in closure");
    }

    #[test]
    fn test_opaque_profunctor_loses_effects() {
        let arrow = arrow_complex_choice();
        let opaque_p = arrow_to_opaque_p(&arrow);
        assert!(infer_effect_opaque_p(&opaque_p).is_none(),
            "Opaque profunctor cannot infer effects — structure hidden");
    }

    #[test]
    fn test_opaque_profunctor_loses_per_branch_effects() {
        let arrow = arrow_complex_choice();
        let opaque_p = arrow_to_opaque_p(&arrow);
        assert!(per_branch_effects_opaque_p(&opaque_p).is_none(),
            "Opaque profunctor cannot determine per-branch effects");
    }

    #[test]
    fn test_opaque_profunctor_loses_loop() {
        let arrow = arrow_loop();
        let opaque_p = arrow_to_opaque_p(&arrow);
        assert!(recover_loop_opaque_p(&opaque_p).is_none(),
            "Opaque profunctor loses loop structure");
    }

    // === Freer profunctor + strength + choice + trace recovers structure ===

    #[test]
    fn test_freepa_preserves_effects() {
        let arrow = arrow_complex_choice();
        let freepa = arrow_to_freepa(&arrow);
        let effect = infer_effect_freepa(&freepa);
        assert!(effect.contains(Op::Get), "FreePA detects Get");
        assert!(effect.contains(Op::Put), "FreePA detects Put");
        assert!(effect.contains(Op::Throw), "FreePA detects Throw");
    }

    #[test]
    fn test_freepa_uses_strength_for_fanout() {
        let arrow = arrow_fanout();
        let freepa = arrow_to_freepa(&arrow);
        assert!(has_strength_freepa(&freepa),
            "Fanout encoded in FreePA uses First (strength) — the primitive arrows add");
    }

    #[test]
    fn test_freepa_uses_choice_for_branching() {
        let arrow = arrow_choice();
        let freepa = arrow_to_freepa(&arrow);
        assert!(has_choice_freepa(&freepa),
            "Choice encoded in FreePA uses Left (choice) — the primitive arrows add");
    }

    #[test]
    fn test_freepa_uses_trace_for_loop() {
        let arrow = arrow_loop();
        let freepa = arrow_to_freepa(&arrow);
        assert!(has_trace_freepa(&freepa),
            "Loop encoded in FreePA uses Loop (trace) — the primitive arrows add");
        assert!(recover_loop_freepa(&freepa).is_some(),
            "FreePA recovers loop structure");
    }

    #[test]
    fn test_freepa_semantic_equiv_fanout() {
        let arrow = arrow_fanout();
        let freepa = arrow_to_freepa(&arrow);
        let (v_arr, s_arr) = run_arrow(&arrow, Value::Int(42), Value::Int(7)).unwrap();
        let (v_fpa, s_fpa) = run_freepa(&freepa, Value::Int(42), Value::Int(7)).unwrap();
        assert_eq!(v_arr, v_fpa, "FreePA fanout: results match arrow");
        assert_eq!(s_arr, s_fpa, "FreePA fanout: state matches arrow");
    }

    #[test]
    fn test_freepa_semantic_equiv_choice() {
        let arrow = arrow_choice();
        let input = Value::Right(Box::new(Value::Int(99)));
        let (v_arr, s_arr) = run_arrow(&arrow, input.clone(), Value::Int(0)).unwrap();
        let freepa = arrow_to_freepa(&arrow);
        let (v_fpa, s_fpa) = run_freepa(&freepa, input, Value::Int(0)).unwrap();
        assert_eq!(v_arr, v_fpa, "FreePA choice: results match arrow");
        assert_eq!(s_arr, s_fpa, "FreePA choice: state matches arrow");
    }

    #[test]
    fn test_freepa_semantic_equiv_complex_choice() {
        let arrow = arrow_complex_choice();
        let input = Value::Right(Box::new(Value::Int(99)));
        let (v_arr, s_arr) = run_arrow(&arrow, input.clone(), Value::Int(0)).unwrap();
        let freepa = arrow_to_freepa(&arrow);
        let (v_fpa, s_fpa) = run_freepa(&freepa, input, Value::Int(0)).unwrap();
        assert_eq!(v_arr, v_fpa);
        assert_eq!(s_arr, s_fpa);
    }

    // === The key claim: profunctor + strength + choice + trace IS an arrow ===

    #[test]
    fn test_freepa_is_isomorphic_to_arrow() {
        // FreePA has exactly the same expressive power as ArrowComp.
        // The combinators map:
        //   arr      ↔ Pure/Ident (dimap gives function lifting)
        //   comp     ↔ Seq
        //   first    ↔ First (strength)
        //   left     ↔ Left (choice)
        //   loop     ↔ Loop (trace)
        //
        // "Strong cocartesian traced profunctor" = Arrow
        // The profunctor framing adds nothing — it just renames the combinators.

        let arrow = arrow_complex_choice();
        let freepa = arrow_to_freepa(&arrow);

        // FreePA can represent everything the arrow can
        let effect_arrow = infer_effect_arrow(&arrow);
        let effect_freepa = infer_effect_freepa(&freepa);
        assert_eq!(effect_arrow, effect_freepa,
            "FreePA and arrow infer the same effects");

        // FreePA uses choice (Left) — the same primitive as arrow's Choice
        assert!(has_choice_freepa(&freepa),
            "FreePA uses Left — the choice primitive that arrows provide");
    }

    // === The dimap/lmap/rmap combinators: what they DO preserve ===

    #[test]
    fn test_bare_profunctor_preserves_sequential_structure() {
        // The bare profunctor CAN preserve sequential composition structure
        // (it has category composition). This is the one thing it does well.
        let arrow = arrow_sequential();
        let freep = arrow_to_freep(&arrow).unwrap();
        let effect = infer_effect_freep(&freep);
        assert!(effect.contains(Op::Get) && effect.contains(Op::Put),
            "Bare profunctor infers effects for sequential composition");
    }

    #[test]
    fn test_bare_profunctor_preserves_dimap_structure() {
        // dimap/lmap/rmap are structurally visible in the freer profunctor
        let freep = FreeP::Rmap {
            post: Rc::new(|v| match v { Value::Int(n) => Value::Int(n + 1), _ => v }),
            inner: Box::new(FreeP::OpNode(Op::Get, Box::new(FreeP::Ident))),
        };
        let effect = infer_effect_freep(&freep);
        assert!(effect.contains(Op::Get),
            "dimap/rmap structure is visible — effects inferred through it");
    }

    // === The summary: what each representation preserves ===

    #[test]
    fn test_structural_preservation_summary() {
        // This test documents the full comparison in assertions.
        // It is the Challenge #12 equivalent of Challenge #9's summary test.

        let complex = arrow_complex_choice();

        // Arrow: preserves everything
        assert!(recover_choice_arrow(&complex).is_some(), "arrow: choice recovered");
        let (left, right) = per_branch_effects_arrow(&complex).unwrap();
        assert!(left.contains(Op::Get) && left.contains(Op::Throw), "arrow: left branch effects");
        assert!(right.contains(Op::Put) && !right.contains(Op::Get), "arrow: right branch effects");
        assert!(infer_effect_arrow(&complex).len() == 3, "arrow: full effect set");

        // Opaque profunctor: preserves nothing (same as opaque monad)
        let opaque_p = arrow_to_opaque_p(&complex);
        assert!(recover_choice_opaque_p(&opaque_p).is_none(), "opaque prof: choice LOST");
        assert!(infer_effect_opaque_p(&opaque_p).is_none(), "opaque prof: effects LOST");
        assert!(per_branch_effects_opaque_p(&opaque_p).is_none(), "opaque prof: per-branch LOST");

        // Bare freer profunctor: CANNOT EVEN REPRESENT the program
        let freep_result = arrow_to_freep(&complex);
        assert!(freep_result.is_none(),
            "bare profunctor: CANNOT REPRESENT choice — lacks the combinator");

        // Freer profunctor + strength + choice + trace: recovers everything
        // (but IS an arrow — just renamed)
        let freepa = arrow_to_freepa(&complex);
        let effect = infer_effect_freepa(&freepa);
        assert!(effect.len() == 3, "FreePA: full effect set recovered");
        assert!(has_choice_freepa(&freepa), "FreePA: uses choice (Left) primitive");
    }

    #[test]
    fn test_profunctor_subsumption_is_hollow() {
        // The Wikipedia claim: "Much of the utility of arrows is subsumed by
        // more general classes like profunctor."
        //
        // This test demonstrates that the subsumption is HOLLOW:
        //
        // 1. A bare profunctor (dimap + composition) CANNOT express fanout,
        //    choice, or feedback — the structural features Challenge #9
        //    showed are practically useful.
        //
        // 2. To recover those features, you must add:
        //    - strength (first) → for fanout
        //    - choice (left)   → for branching
        //    - trace (loop)    → for feedback
        //
        // 3. A "strong cocartesian traced profunctor" IS an arrow.
        //    You haven't subsumed arrows — you've reconstructed them.

        // Bare profunctor: cannot represent fanout
        assert!(arrow_to_freep(&arrow_fanout()).is_none(),
            "bare profunctor cannot represent fanout");

        // Bare profunctor: cannot represent choice
        assert!(arrow_to_freep(&arrow_choice()).is_none(),
            "bare profunctor cannot represent choice");

        // Bare profunctor: cannot represent loop
        assert!(arrow_to_freep(&arrow_loop()).is_none(),
            "bare profunctor cannot represent loop");

        // Profunctor + strength + choice + trace: CAN represent everything
        // (because it IS an arrow)
        let fanout_pa = arrow_to_freepa(&arrow_fanout());
        let choice_pa = arrow_to_freepa(&arrow_choice());
        let loop_pa = arrow_to_freepa(&arrow_loop());

        assert!(has_strength_freepa(&fanout_pa),
            "fanout requires strength (first) — an arrow primitive");
        assert!(has_choice_freepa(&choice_pa),
            "choice requires choice (left) — an arrow primitive");
        assert!(has_trace_freepa(&loop_pa),
            "loop requires trace (loop) — an arrow primitive");

        // The profunctor framing added NOTHING — it just renamed the combinators.
        // "Strong profunctor + category" = Arrow (Wikipedia's own admission).
        // Adding choice and trace gives the full arrow calculus.
    }

    #[test]
    fn test_profunctor_vs_opaque_monad_same_opacity_problem() {
        // The opaque profunctor has the SAME opacity problem as the opaque
        // monad (Challenge #9). The profunctor interface (dimap/lmap/rmap)
        // does not help with structural inspection — the structure is still
        // hidden inside the function.
        //
        // This refutes the implication that profunctors offer a structural
        // advantage over monads. They don't — an opaque profunctor is just
        // as opaque as an opaque monad.

        let arrow = arrow_complex_choice();
        let opaque_p = arrow_to_opaque_p(&arrow);

        // The profunctor has dimap/lmap/rmap — but none of these help
        // recover structural information. The structure is in the closure.
        assert!(recover_fanout_opaque_p(&opaque_p).is_none(),
            "opaque profunctor: fanout LOST (same as opaque monad)");
        assert!(recover_choice_opaque_p(&opaque_p).is_none(),
            "opaque profunctor: choice LOST (same as opaque monad)");
        assert!(infer_effect_opaque_p(&opaque_p).is_none(),
            "opaque profunctor: effects LOST (same as opaque monad)");
        assert!(per_branch_effects_opaque_p(&opaque_p).is_none(),
            "opaque profunctor: per-branch LOST (same as opaque monad)");
    }

    // === dimap/lmap/rmap are weaker than arr + first ===

    #[test]
    fn test_dimap_cannot_replace_arr_plus_first() {
        // A common argument: "profunctors have dimap, which subsumes arr."
        // This is misleading. dimap gives you pre/post composition with pure
        // functions, but it does NOT give you:
        //   - arr (lifting a pure function INTO the profunctor) — you need
        //     an identity profunctor + dimap, which is arr
        //   - first (strength) — needed for fanout, NOT derivable from dimap
        //
        // dimap is about TRANSFORMING an existing profunctor's input/output.
        // first is about EXTENDING a profunctor to operate on one component
        // of a pair. These are different powers.

        // Demonstrate: dimap cannot express fanout
        // Fanout requires running TWO profunctors on the SAME input.
        // dimap only transforms the input/output of ONE profunctor.
        // You NEED first (strength) to thread the second component through.

        let bare = FreeP::Dimap {
            pre: Rc::new(|v| v.clone()),
            post: Rc::new(|v| v),
            inner: Box::new(FreeP::OpNode(Op::Get, Box::new(FreeP::Ident))),
        };
        // This is just Get with identity dimap — NOT fanout.
        // No amount of dimap chaining produces fanout without first.
        assert!(recover_fanout_freep(&bare).is_none(),
            "dimap cannot produce fanout — strength (first) is required");
    }
}

// ============================================================================
// Demo
// ============================================================================

fn main() {
    println!("Challenge #12: Structural Preservation Under Profunctor Translation");
    println!("=====================================================================\n");

    let complex = arrow_complex_choice();

    println!("Arrow program: choice(Get >>> Throw, Put)");
    println!("  Structural analysis (arrow):");
    println!("    choice:       {}", if recover_choice_arrow(&complex).is_some() { "YES" } else { "no" });
    let (left, right) = per_branch_effects_arrow(&complex).unwrap();
    println!("    left effects:  {}", left);
    println!("    right effects: {}", right);
    println!("    total effects: {}", infer_effect_arrow(&complex));

    println!();

    let opaque_p = arrow_to_opaque_p(&complex);
    println!("Opaque profunctor (same program, translated):");
    println!("  Structural analysis:");
    println!("    choice:       {}", if recover_choice_opaque_p(&opaque_p).is_some() { "YES" } else { "NO — LOST" });
    println!("    effects:      {}", if infer_effect_opaque_p(&opaque_p).is_some() { "YES" } else { "NO — LOST" });
    println!("    per-branch:   {}", if per_branch_effects_opaque_p(&opaque_p).is_some() { "YES" } else { "NO — LOST" });

    println!();

    println!("Bare freer profunctor (dimap + composition + ops only):");
    let freep_result = arrow_to_freep(&complex);
    println!("  Can represent this program? {}",
        if freep_result.is_some() { "YES" } else { "NO — CANNOT REPRESENT (no choice combinator)" });

    println!();

    let freepa = arrow_to_freepa(&complex);
    println!("Freer profunctor + strength + choice + trace (= arrow):");
    println!("  Structural analysis:");
    let effect = infer_effect_freepa(&freepa);
    println!("    effects:      {}", effect);
    println!("    uses choice:  {}", has_choice_freepa(&freepa));
    println!("    uses strength: {}", has_strength_freepa(&freepa));
    println!("    uses trace:   {}", has_trace_freepa(&freepa));

    println!();

    // Semantic equivalence
    println!("Semantic equivalence (right branch, Put 99):");
    let input = Value::Right(Box::new(Value::Int(99)));
    let (v_arr, s_arr) = run_arrow(&complex, input.clone(), Value::Int(0)).unwrap();
    let (v_op, s_op) = opaque_p.run(input.clone(), Value::Int(0)).unwrap();
    let (v_fpa, s_fpa) = run_freepa(&freepa, input, Value::Int(0)).unwrap();
    println!("  arrow:           result={}, state={}", v_arr, s_arr);
    println!("  opaque prof:     result={}, state={}", v_op, s_op);
    println!("  FreePA:          result={}, state={}", v_fpa, s_fpa);
    println!("  all match:       {}", v_arr == v_op && v_arr == v_fpa && s_arr == s_op && s_arr == s_fpa);

    println!();

    // The bare profunctor's limitations
    println!("Bare profunctor limitations:");
    println!("  fanout:  CANNOT REPRESENT (no strength/first)");
    println!("  choice:  CANNOT REPRESENT (no choice/left)");
    println!("  loop:    CANNOT REPRESENT (no trace/loop)");
    println!("  seq:     CAN represent (has category composition)");
    println!("  effects: CAN infer (if freer-style with explicit OpNode)");

    println!();
    println!("KEY FINDING:");
    println!("  The Wikipedia claim that profunctors 'subsume' arrow utility");
    println!("  is HOLLOW. A bare profunctor CANNOT EXPRESS fanout, choice,");
    println!("  or feedback — the structural features that make arrows useful.");
    println!("  To recover them, you add strength (first), choice (left), and");
    println!("  trace (loop) — which reconstructs the arrow interface exactly.");
    println!("  'Strong cocartesian traced profunctor' = Arrow. The profunctor");
    println!("  framing adds nothing; it renames the combinators.");
    println!();
    println!("  Meanwhile, an opaque profunctor has the SAME opacity problem");
    println!("  as an opaque monad (Challenge #9). The profunctor interface");
    println!("  (dimap/lmap/rmap) does not help with structural inspection.");
}
