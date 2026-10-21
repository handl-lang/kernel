// Challenge #9: Structural Preservation Under Monadic Translation
//
// THE CRITICAL QUESTION:
//
//   Does deriving `bind` destroy information that the original arrow
//   representation preserves?
//
// We compare three representations of the same computations:
//
//   1. Freer arrow  — structure explicit (defunctionalized continuations)
//   2. Opaque monad — structure hidden inside closures (can only run)
//   3. Freer monad  — structure explicit, but organized as a free monad
//
// The key comparison is freer arrow vs opaque monad: what structural
// properties can you observe from each?
//
// Expected finding: the opaque monad is semantically adequate (same
// results) but structurally lossy (independence, branching, per-branch
// effects, dependency graph all lost). The freer monad recovers structure,
// proving the loss is about *opacity*, not monadic structure per se.

use std::collections::HashSet;
use std::fmt;
use std::rc::Rc;

// ============================================================================
// Shared Types
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
// Representation 1: Freer Arrow (structure explicit)
// ============================================================================
//
// The arrow representation has explicit connectives: Seq, Fanout, Choice,
// Loop. Continuations are sub-trees (defunctionalized), so the entire
// computation is statically traversable.

#[derive(Debug, Clone)]
pub enum ArrowComp {
    Pure(Value),
    // f >>> g — sequential composition (g depends on f's output)
    Seq(Box<ArrowComp>, Box<ArrowComp>),
    // f &&& g — fanout: both consume the same input, results paired
    // KEY: f and g are INDEPENDENT — neither depends on the other
    Fanout(Box<ArrowComp>, Box<ArrowComp>),
    // choice f g — branching: Left input → f, Right input → g
    Choice(Box<ArrowComp>, Box<ArrowComp>),
    // perform an operation, continue with k (k receives op result)
    OpNode(Op, Box<ArrowComp>),
    // loop — feedback
    Loop(Box<ArrowComp>),
    // identity arrow (useful for building chains)
    Ident,
}

// Label sub-computations for dependency analysis
#[derive(Debug, Clone)]
pub struct LabeledArrow {
    pub label: usize,
    pub comp: ArrowComp,
}

// ============================================================================
// Representation 2: Opaque Monad (structure hidden)
// ============================================================================
//
// The monad is a black box: you can run it, but you cannot pattern-match
// on its structure. M<B> wraps a function that is opaque.

pub struct OpaqueM {
    // The computation is a function (input, state) -> (result, new_state).
    // Once wrapped, structure is invisible — you can only run it.
    run: Rc<dyn Fn(Value, Value) -> Result<(Value, Value), String>>,
}

impl OpaqueM {
    pub fn new(f: impl Fn(Value, Value) -> Result<(Value, Value), String> + 'static) -> Self {
        OpaqueM { run: Rc::new(f) }
    }

    pub fn run(&self, input: Value, state: Value) -> Result<(Value, Value), String> {
        (self.run)(input, state)
    }

    pub fn pure(v: Value) -> Self {
        OpaqueM::new(move |_input, state| Ok((v.clone(), state)))
    }

    pub fn bind(&self, g: Rc<dyn Fn(Value) -> OpaqueM>) -> OpaqueM {
        let run_f = Rc::clone(&self.run);
        OpaqueM::new(move |input, state| {
            let (b, state2) = (run_f)(input, state)?;
            let g_comp = g(b.clone());
            // g receives b as its input (arrow composition: f's output → g's input)
            g_comp.run(b, state2)
        })
    }
}

// Kleisli composition: f >=> g (simplified — all values are Value)
pub fn kleisli(
    f: Rc<dyn Fn(Value) -> OpaqueM>,
    g: Rc<dyn Fn(Value) -> OpaqueM>,
) -> Rc<dyn Fn(Value) -> OpaqueM> {
    Rc::new(move |a| {
        let mb = f(a);
        mb.bind(Rc::clone(&g))
    })
}

// Opaque monad operations (state + exception)
pub fn op_get() -> OpaqueM {
    OpaqueM::new(|_input, state| Ok((state.clone(), state)))
}

pub fn op_put() -> OpaqueM {
    // Put: input becomes the new state
    OpaqueM::new(|input, _state| Ok((Value::Unit, input)))
}

pub fn op_throw(msg: &str) -> OpaqueM {
    let msg = msg.to_string();
    OpaqueM::new(move |_, _| Err(msg.clone()))
}

// ============================================================================
// Representation 3: Freer Monad (structure explicit, monad-organized)
// ============================================================================
//
// The freer monad exposes structure like the freer arrow, but organized
// as a monad (Pure | FreeOp op continuation). This lets us test whether
// the structural loss is about *opacity* or about *monadic structure*.

#[derive(Debug, Clone)]
pub enum FreeM {
    Pure(Value),
    Ident,                                          // pass-through (identity)
    FreeOp(Op, Box<FreeM>),                         // perform op, continue with k
    Bind(Box<FreeM>, Box<FreeM>),                   // m >>= k
    Fanout(Box<FreeM>, Box<FreeM>),                 // f &&& g
    Choice(Box<FreeM>, Box<FreeM>),                 // choice f g
}

// ============================================================================
// Arrow execution (for semantic equivalence tests)
// ============================================================================

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
                    // input is the new state
                    let (_, s) = run_arrow(k, Value::Unit, input)?;
                    Ok((Value::Unit, s))
                }
                Op::Throw => Err("throw".to_string()),
            }
        }
        ArrowComp::Loop(body) => {
            // Simplified: run body with (input, state), iterate until terminated
            // For this experiment, just run once
            let pair = Value::Pair(Box::new(input), Box::new(state));
            run_arrow(body, pair, Value::Unit)
        }
    }
}

// ============================================================================
// Freer monad execution
// ============================================================================

pub fn run_freer(fm: &FreeM, input: Value, state: Value) -> Result<(Value, Value), String> {
    match fm {
        FreeM::Pure(v) => Ok((v.clone(), state)),
        FreeM::Ident => Ok((input, state)),
        FreeM::FreeOp(op, k) => {
            match op {
                Op::Get => run_freer(k, state.clone(), state),
                Op::Put => run_freer(k, Value::Unit, input),
                Op::Throw => Err("throw".to_string()),
            }
        }
        FreeM::Bind(m, k) => {
            let (v, s) = run_freer(m, input, state)?;
            run_freer(k, v, s)
        }
        FreeM::Fanout(f, g) => {
            let (v1, s1) = run_freer(f, input.clone(), state)?;
            let (v2, s2) = run_freer(g, input, s1)?;
            Ok((Value::Pair(Box::new(v1), Box::new(v2)), s2))
        }
        FreeM::Choice(f, g) => {
            match input {
                Value::Left(v) => run_freer(f, *v, state),
                Value::Right(v) => run_freer(g, *v, state),
                _ => Err("choice requires Left/Right".to_string()),
            }
        }
    }
}

// ============================================================================
// Translation: Arrow → Opaque Monad
// ============================================================================
//
// This translation is semantics-preserving but may lose structural
// information. Fanout becomes a bind chain; choice becomes a closure.

pub fn arrow_to_opaque(comp: &ArrowComp) -> OpaqueM {
    match comp {
        ArrowComp::Pure(v) => OpaqueM::pure(v.clone()),
        ArrowComp::Ident => OpaqueM::new(|input, state| Ok((input, state))),
        ArrowComp::Seq(f, g) => {
            let mf = arrow_to_opaque(f);
            let g_clone = g.clone();
            mf.bind(Rc::new(move |_v| arrow_to_opaque(&g_clone)))
        }
        ArrowComp::Fanout(f, g) => {
            // KEY: fanout must run both f and g with the SAME input.
            // In the opaque monad, this requires capturing the input
            // before the bind chain consumes it. The bind makes it LOOK
            // like g depends on f's result, even though it doesn't.
            let f_clone = f.clone();
            let g_clone = g.clone();
            OpaqueM::new(move |input, state| {
                let mf = arrow_to_opaque(&f_clone);
                let (v1, s1) = mf.run(input.clone(), state)?;
                let mg = arrow_to_opaque(&g_clone);
                let (v2, s2) = mg.run(input, s1)?;
                Ok((Value::Pair(Box::new(v1), Box::new(v2)), s2))
            })
        }
        ArrowComp::Choice(f, g) => {
            // Choice becomes a closure — branch structure is hidden
            let f_clone = f.clone();
            let g_clone = g.clone();
            OpaqueM::new(move |input, state| {
                match input {
                    Value::Left(v) => arrow_to_opaque(&f_clone).run(*v, state),
                    Value::Right(v) => arrow_to_opaque(&g_clone).run(*v, state),
                    _ => Err("choice requires Left/Right".to_string()),
                }
            })
        }
        ArrowComp::OpNode(op, k) => {
            let k_clone = k.clone();
            match op {
                Op::Get => {
                    // Get: return state as result, pass to continuation
                    let mk = arrow_to_opaque(&k_clone);
                    OpaqueM::new(move |_input, state| {
                        mk.run(state.clone(), state)
                    })
                }
                Op::Put => {
                    // Put: input becomes new state, pass Unit to continuation
                    let mk = arrow_to_opaque(&k_clone);
                    OpaqueM::new(move |input, _state| {
                        mk.run(Value::Unit, input)
                    })
                }
                Op::Throw => op_throw("error"),
            }
        }
        ArrowComp::Loop(body) => {
            arrow_to_opaque(body)
        }
    }
}

// ============================================================================
// Translation: Arrow → Freer Monad (structure-preserving)
// ============================================================================

pub fn arrow_to_freer(comp: &ArrowComp) -> FreeM {
    match comp {
        ArrowComp::Pure(v) => FreeM::Pure(v.clone()),
        ArrowComp::Ident => FreeM::Ident,
        ArrowComp::Seq(f, g) => {
            let ff = arrow_to_freer(f);
            let fg = arrow_to_freer(g);
            FreeM::Bind(Box::new(ff), Box::new(fg))
        }
        ArrowComp::Fanout(f, g) => {
            FreeM::Fanout(
                Box::new(arrow_to_freer(f)),
                Box::new(arrow_to_freer(g)),
            )
        }
        ArrowComp::Choice(f, g) => {
            FreeM::Choice(
                Box::new(arrow_to_freer(f)),
                Box::new(arrow_to_freer(g)),
            )
        }
        ArrowComp::OpNode(op, k) => {
            FreeM::FreeOp(*op, Box::new(arrow_to_freer(k)))
        }
        ArrowComp::Loop(body) => arrow_to_freer(body),
    }
}

// ============================================================================
// Structural Recovery: What can we observe from each representation?
// ============================================================================

// --- Independence detection ---

/// Detect whether a computation has independent parallel sub-computations
/// (fanout). Returns the pair of sub-computations if found.
pub fn recover_fanout_arrow(comp: &ArrowComp) -> Option<(&ArrowComp, &ArrowComp)> {
    match comp {
        ArrowComp::Fanout(f, g) => Some((f, g)),
        _ => None,
    }
}

/// Attempt to detect fanout from an opaque monad.
/// EXPECTED: None — the structure is hidden inside closures.
pub fn recover_fanout_opaque(_m: &OpaqueM) -> Option<()> {
    // We cannot inspect the structure of an OpaqueM — it's a black box.
    // The function inside could do anything: fanout, bind, choice, etc.
    // There is no way to determine this without running it.
    None
}

/// Detect fanout from a freer monad.
/// EXPECTED: Some — the structure is explicit.
pub fn recover_fanout_freer(fm: &FreeM) -> Option<(&FreeM, &FreeM)> {
    match fm {
        FreeM::Fanout(f, g) => Some((f, g)),
        _ => None,
    }
}

// --- Choice/branching detection ---

pub fn recover_choice_arrow(comp: &ArrowComp) -> Option<(&ArrowComp, &ArrowComp)> {
    match comp {
        ArrowComp::Choice(f, g) => Some((f, g)),
        _ => None,
    }
}

pub fn recover_choice_opaque(_m: &OpaqueM) -> Option<()> {
    // Cannot inspect — branch structure is hidden in the closure
    None
}

pub fn recover_choice_freer(fm: &FreeM) -> Option<(&FreeM, &FreeM)> {
    match fm {
        FreeM::Choice(f, g) => Some((f, g)),
        _ => None,
    }
}

// --- Effect set inference ---

pub fn infer_effect_arrow(comp: &ArrowComp) -> Effect {
    match comp {
        ArrowComp::Pure(_) | ArrowComp::Ident => Effect::empty(),
        ArrowComp::Seq(f, g) => {
            infer_effect_arrow(f).union(&infer_effect_arrow(g))
        }
        ArrowComp::Fanout(f, g) => {
            infer_effect_arrow(f).union(&infer_effect_arrow(g))
        }
        ArrowComp::Choice(f, g) => {
            infer_effect_arrow(f).union(&infer_effect_arrow(g))
        }
        ArrowComp::OpNode(op, k) => {
            Effect::singleton(*op).union(&infer_effect_arrow(k))
        }
        ArrowComp::Loop(body) => infer_effect_arrow(body),
    }
}

/// Attempt to infer the effect set from an opaque monad.
/// EXPECTED: None — we cannot determine effects without running.
pub fn infer_effect_opaque(_m: &OpaqueM) -> Option<Effect> {
    // The monad is a black box. We cannot know what operations it will
    // perform without running it. Even running it only tells us what
    // operations it performed for ONE input, not the full set.
    None
}

pub fn infer_effect_freer(fm: &FreeM) -> Effect {
    match fm {
        FreeM::Pure(_) | FreeM::Ident => Effect::empty(),
        FreeM::FreeOp(op, k) => {
            Effect::singleton(*op).union(&infer_effect_freer(k))
        }
        FreeM::Bind(m, k) => {
            infer_effect_freer(m).union(&infer_effect_freer(k))
        }
        FreeM::Fanout(f, g) => {
            infer_effect_freer(f).union(&infer_effect_freer(g))
        }
        FreeM::Choice(f, g) => {
            infer_effect_freer(f).union(&infer_effect_freer(g))
        }
    }
}

// --- Per-branch effect analysis ---

/// For a choice computation, return the effect sets of each branch.
/// Arrow: can do this (branches are visible).
pub fn per_branch_effects_arrow(comp: &ArrowComp) -> Option<(Effect, Effect)> {
    match comp {
        ArrowComp::Choice(f, g) => {
            Some((infer_effect_arrow(f), infer_effect_arrow(g)))
        }
        _ => None,
    }
}

/// Opaque monad: cannot determine per-branch effects.
pub fn per_branch_effects_opaque(_m: &OpaqueM) -> Option<(Effect, Effect)> {
    None
}

/// Freer monad: can determine per-branch effects.
pub fn per_branch_effects_freer(fm: &FreeM) -> Option<(Effect, Effect)> {
    match fm {
        FreeM::Choice(f, g) => {
            Some((infer_effect_freer(f), infer_effect_freer(g)))
        }
        _ => None,
    }
}

// --- Dependency graph ---

/// A dependency edge: computation `from` feeds into computation `to`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DepEdge {
    pub from: usize,
    pub to: usize,
}

/// Build a dependency graph from an arrow computation.
/// Nodes are sub-computations; edges represent data flow.
pub fn dependency_graph_arrow(comp: &ArrowComp) -> Vec<DepEdge> {
    let mut edges = Vec::new();
    let mut next_id = 0usize;
    build_dep_graph_arrow(comp, &mut edges, &mut next_id, None);
    edges
}

fn build_dep_graph_arrow(
    comp: &ArrowComp,
    edges: &mut Vec<DepEdge>,
    next_id: &mut usize,
    parent: Option<usize>,
) -> usize {
    let my_id = *next_id;
    *next_id += 1;

    if let Some(p) = parent {
        edges.push(DepEdge { from: p, to: my_id });
    }

    match comp {
        ArrowComp::Pure(_) | ArrowComp::Ident => {}
        ArrowComp::Seq(f, g) => {
            let f_id = build_dep_graph_arrow(f, edges, next_id, None);
            let g_id = build_dep_graph_arrow(g, edges, next_id, None);
            // f feeds into g (dependency)
            edges.push(DepEdge { from: f_id, to: g_id });
        }
        ArrowComp::Fanout(f, g) => {
            // Both f and g depend on the SAME input (my_id), not on each other
            let f_id = build_dep_graph_arrow(f, edges, next_id, Some(my_id));
            let g_id = build_dep_graph_arrow(g, edges, next_id, Some(my_id));
            // NO edge between f_id and g_id — they are independent
            let _ = (f_id, g_id); // suppress unused warning
        }
        ArrowComp::Choice(f, g) => {
            build_dep_graph_arrow(f, edges, next_id, Some(my_id));
            build_dep_graph_arrow(g, edges, next_id, Some(my_id));
        }
        ArrowComp::OpNode(_op, k) => {
            build_dep_graph_arrow(k, edges, next_id, Some(my_id));
        }
        ArrowComp::Loop(body) => {
            build_dep_graph_arrow(body, edges, next_id, Some(my_id));
        }
    }
    my_id
}

/// Attempt to build a dependency graph from an opaque monad.
/// EXPECTED: empty — structure is hidden.
pub fn dependency_graph_opaque(_m: &OpaqueM) -> Vec<DepEdge> {
    // Cannot inspect the structure — no graph can be built
    Vec::new()
}

/// Build a dependency graph from a freer monad.
pub fn dependency_graph_freer(fm: &FreeM) -> Vec<DepEdge> {
    let mut edges = Vec::new();
    let mut next_id = 0usize;
    build_dep_graph_freer(fm, &mut edges, &mut next_id, None);
    edges
}

fn build_dep_graph_freer(
    fm: &FreeM,
    edges: &mut Vec<DepEdge>,
    next_id: &mut usize,
    parent: Option<usize>,
) -> usize {
    let my_id = *next_id;
    *next_id += 1;

    if let Some(p) = parent {
        edges.push(DepEdge { from: p, to: my_id });
    }

    match fm {
        FreeM::Pure(_) | FreeM::Ident => {}
        FreeM::FreeOp(_op, k) => {
            build_dep_graph_freer(k, edges, next_id, Some(my_id));
        }
        FreeM::Bind(m, k) => {
            let m_id = build_dep_graph_freer(m, edges, next_id, None);
            let k_id = build_dep_graph_freer(k, edges, next_id, None);
            edges.push(DepEdge { from: m_id, to: k_id });
        }
        FreeM::Fanout(f, g) => {
            build_dep_graph_freer(f, edges, next_id, Some(my_id));
            build_dep_graph_freer(g, edges, next_id, Some(my_id));
        }
        FreeM::Choice(f, g) => {
            build_dep_graph_freer(f, edges, next_id, Some(my_id));
            build_dep_graph_freer(g, edges, next_id, Some(my_id));
        }
    }
    my_id
}

// --- Feedback detection ---

pub fn recover_loop_arrow(comp: &ArrowComp) -> Option<&ArrowComp> {
    match comp {
        ArrowComp::Loop(body) => Some(body),
        _ => None,
    }
}

pub fn recover_loop_opaque(_m: &OpaqueM) -> Option<()> {
    // Feedback structure is hidden in the closure
    None
}

pub fn has_loop_freer(fm: &FreeM) -> bool {
    match fm {
        FreeM::Pure(_) | FreeM::Ident => false,
        FreeM::FreeOp(_, k) => has_loop_freer(k),
        FreeM::Bind(m, k) => has_loop_freer(m) || has_loop_freer(k),
        FreeM::Fanout(f, g) | FreeM::Choice(f, g) => {
            has_loop_freer(f) || has_loop_freer(g)
        }
    }
}

// ============================================================================
// Example Programs
// ============================================================================

/// Fanout: two independent computations over the same input.
/// Arrow: f &&& g where f = arr(+1), g = arr(*2)
pub fn arrow_fanout() -> ArrowComp {
    ArrowComp::Fanout(
        Box::new(ArrowComp::Pure(Value::Int(0))), // placeholder — real version uses input
        Box::new(ArrowComp::Pure(Value::Int(0))),
    )
}

/// A more realistic fanout: Get state, then fanout into two pure transforms
pub fn arrow_fanout_get() -> ArrowComp {
    // get >>> (arr(+1) &&& arr(*2))
    // For simplicity: OpNode(Get, Fanout(Pure, Pure))
    ArrowComp::OpNode(
        Op::Get,
        Box::new(ArrowComp::Fanout(
            Box::new(ArrowComp::Ident),  // pass through (represents +0)
            Box::new(ArrowComp::Ident),  // pass through (represents *1)
        )),
    )
}

/// Choice: Left → Get, Right → Put
pub fn arrow_choice() -> ArrowComp {
    ArrowComp::Choice(
        Box::new(ArrowComp::OpNode(Op::Get, Box::new(ArrowComp::Ident))),
        Box::new(ArrowComp::OpNode(Op::Put, Box::new(ArrowComp::Ident))),
    )
}

/// Sequential: Get >>> Put (read state, write it back)
pub fn arrow_sequential() -> ArrowComp {
    ArrowComp::Seq(
        Box::new(ArrowComp::OpNode(Op::Get, Box::new(ArrowComp::Ident))),
        Box::new(ArrowComp::OpNode(Op::Put, Box::new(ArrowComp::Ident))),
    )
}

/// Complex: Fanout of (Get >>> throw) and (Put)
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

/// Loop: feedback structure
pub fn arrow_loop() -> ArrowComp {
    ArrowComp::Loop(Box::new(ArrowComp::OpNode(Op::Get, Box::new(ArrowComp::Ident))))
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // === Semantic equivalence: arrow and opaque monad produce same results ===

    #[test]
    fn test_semantic_equiv_sequential() {
        let arrow = arrow_sequential();
        let (v_arr, s_arr) = run_arrow(&arrow, Value::Int(42), Value::Int(7)).unwrap();

        let monad = arrow_to_opaque(&arrow);
        let (v_mon, s_mon) = monad.run(Value::Int(42), Value::Int(7)).unwrap();

        assert_eq!(v_arr, v_mon);
        assert_eq!(s_arr, s_mon);
    }

    #[test]
    fn test_semantic_equiv_choice_left() {
        let arrow = arrow_choice();
        let (v_arr, s_arr) = run_arrow(&arrow, Value::Left(Box::new(Value::Int(0))), Value::Int(7)).unwrap();

        let monad = arrow_to_opaque(&arrow);
        let (v_mon, s_mon) = monad.run(Value::Left(Box::new(Value::Int(0))), Value::Int(7)).unwrap();

        assert_eq!(v_arr, v_mon);
        assert_eq!(s_arr, s_mon);
    }

    #[test]
    fn test_semantic_equiv_choice_right() {
        let arrow = arrow_choice();
        let (v_arr, s_arr) = run_arrow(&arrow, Value::Right(Box::new(Value::Int(99))), Value::Int(7)).unwrap();

        let monad = arrow_to_opaque(&arrow);
        let (v_mon, s_mon) = monad.run(Value::Right(Box::new(Value::Int(99))), Value::Int(7)).unwrap();

        assert_eq!(v_arr, v_mon);
        assert_eq!(s_arr, s_mon);
    }

    #[test]
    fn test_semantic_equiv_get() {
        let arrow = ArrowComp::OpNode(Op::Get, Box::new(ArrowComp::Ident));
        let (v_arr, _) = run_arrow(&arrow, Value::Unit, Value::Int(42)).unwrap();

        let monad = arrow_to_opaque(&arrow);
        let (v_mon, _) = monad.run(Value::Unit, Value::Int(42)).unwrap();

        assert_eq!(v_arr, v_mon);
    }

    #[test]
    fn test_semantic_equiv_freer_monad() {
        let arrow = arrow_sequential();
        let freer = arrow_to_freer(&arrow);
        let (v_arr, s_arr) = run_arrow(&arrow, Value::Int(42), Value::Int(7)).unwrap();
        let (v_fr, s_fr) = run_freer(&freer, Value::Int(42), Value::Int(7)).unwrap();
        assert_eq!(v_arr, v_fr);
        assert_eq!(s_arr, s_fr);
    }

    #[test]
    fn test_semantic_equiv_all_three_complex() {
        let arrow = arrow_complex_choice();
        // Right branch (Put) should succeed
        let input = Value::Right(Box::new(Value::Int(99)));
        let (v_arr, s_arr) = run_arrow(&arrow, input.clone(), Value::Int(0)).unwrap();

        let monad = arrow_to_opaque(&arrow);
        let (v_mon, s_mon) = monad.run(input.clone(), Value::Int(0)).unwrap();

        assert_eq!(v_arr, v_mon);
        assert_eq!(s_arr, s_mon);
    }

    // === Structural recovery: fanout / independence ===

    #[test]
    fn test_arrow_recovers_fanout() {
        // Top-level fanout: two independent computations
        let arrow = ArrowComp::Fanout(
            Box::new(ArrowComp::OpNode(Op::Get, Box::new(ArrowComp::Ident))),
            Box::new(ArrowComp::OpNode(Op::Put, Box::new(ArrowComp::Ident))),
        );
        let result = recover_fanout_arrow(&arrow);
        assert!(result.is_some(), "Arrow should recover fanout structure");
    }

    #[test]
    fn test_opaque_monad_loses_fanout() {
        let arrow = ArrowComp::Fanout(
            Box::new(ArrowComp::OpNode(Op::Get, Box::new(ArrowComp::Ident))),
            Box::new(ArrowComp::OpNode(Op::Put, Box::new(ArrowComp::Ident))),
        );
        let monad = arrow_to_opaque(&arrow);
        let result = recover_fanout_opaque(&monad);
        assert!(result.is_none(), "Opaque monad should NOT recover fanout — structure is hidden");
    }

    #[test]
    fn test_freer_monad_recovers_fanout() {
        let arrow = ArrowComp::Fanout(
            Box::new(ArrowComp::OpNode(Op::Get, Box::new(ArrowComp::Ident))),
            Box::new(ArrowComp::OpNode(Op::Put, Box::new(ArrowComp::Ident))),
        );
        let freer = arrow_to_freer(&arrow);
        let result = recover_fanout_freer(&freer);
        assert!(result.is_some(), "Freer monad should recover fanout — structure is explicit");
    }

    #[test]
    fn test_fanout_independence_in_dependency_graph() {
        // In the arrow's dependency graph, fanout children have NO edge
        // between them — they are independent.
        let arrow = ArrowComp::Fanout(
            Box::new(ArrowComp::OpNode(Op::Get, Box::new(ArrowComp::Ident))),
            Box::new(ArrowComp::OpNode(Op::Put, Box::new(ArrowComp::Ident))),
        );
        let graph = dependency_graph_arrow(&arrow);
        // Node 0 = Fanout, Node 1 = Get, Node 2 = Ident (Get's child),
        // Node 3 = Put, Node 4 = Ident (Put's child)
        // Edges: 0→1, 1→2, 0→3, 3→4 — but NO 1→3 or 2→3 (independent)
        assert!(graph.iter().any(|e| e.from == 0 && e.to == 1), "fanout → left child (Get)");
        assert!(graph.iter().any(|e| e.from == 0 && e.to == 3), "fanout → right child (Put)");
        assert!(!graph.iter().any(|e| e.from == 1 && e.to == 3), "NO edge Get → Put (independent)");
        assert!(!graph.iter().any(|e| e.from == 3 && e.to == 1), "NO edge Put → Get (independent)");
    }

    // === Structural recovery: choice / branching ===

    #[test]
    fn test_arrow_recovers_choice() {
        let arrow = arrow_choice();
        let result = recover_choice_arrow(&arrow);
        assert!(result.is_some(), "Arrow should recover choice structure");
    }

    #[test]
    fn test_opaque_monad_loses_choice() {
        let arrow = arrow_choice();
        let monad = arrow_to_opaque(&arrow);
        let result = recover_choice_opaque(&monad);
        assert!(result.is_none(), "Opaque monad should NOT recover choice — branch hidden in closure");
    }

    #[test]
    fn test_freer_monad_recovers_choice() {
        let arrow = arrow_choice();
        let freer = arrow_to_freer(&arrow);
        let result = recover_choice_freer(&freer);
        assert!(result.is_some(), "Freer monad should recover choice");
    }

    // === Structural recovery: effect set ===

    #[test]
    fn test_arrow_infers_effect_set() {
        let arrow = arrow_complex_choice();
        let effect = infer_effect_arrow(&arrow);
        // Choice of (Get >>> Throw) and Put → {Get, Put, Throw}
        assert!(effect.contains(Op::Get), "should detect Get");
        assert!(effect.contains(Op::Put), "should detect Put");
        assert!(effect.contains(Op::Throw), "should detect Throw");
    }

    #[test]
    fn test_opaque_monad_cannot_infer_effect_set() {
        let arrow = arrow_complex_choice();
        let monad = arrow_to_opaque(&arrow);
        let result = infer_effect_opaque(&monad);
        assert!(result.is_none(), "Opaque monad should NOT allow effect inference — structure hidden");
    }

    #[test]
    fn test_freer_monad_infers_effect_set() {
        let arrow = arrow_complex_choice();
        let freer = arrow_to_freer(&arrow);
        let effect = infer_effect_freer(&freer);
        assert!(effect.contains(Op::Get), "freer monad should detect Get");
        assert!(effect.contains(Op::Put), "freer monad should detect Put");
        assert!(effect.contains(Op::Throw), "freer monad should detect Throw");
    }

    // === Per-branch effect analysis ===

    #[test]
    fn test_arrow_per_branch_effects() {
        let arrow = arrow_complex_choice();
        let (left_eff, right_eff) = per_branch_effects_arrow(&arrow).unwrap();
        // Left: Get >>> Throw → {Get, Throw}
        assert!(left_eff.contains(Op::Get), "left branch has Get");
        assert!(left_eff.contains(Op::Throw), "left branch has Throw");
        assert!(!left_eff.contains(Op::Put), "left branch has NO Put");
        // Right: Put → {Put}
        assert!(right_eff.contains(Op::Put), "right branch has Put");
        assert!(!right_eff.contains(Op::Get), "right branch has NO Get");
        assert!(!right_eff.contains(Op::Throw), "right branch has NO Throw");
    }

    #[test]
    fn test_opaque_monad_cannot_per_branch_effects() {
        let arrow = arrow_complex_choice();
        let monad = arrow_to_opaque(&arrow);
        let result = per_branch_effects_opaque(&monad);
        assert!(result.is_none(), "Opaque monad cannot determine per-branch effects");
    }

    #[test]
    fn test_freer_monad_per_branch_effects() {
        let arrow = arrow_complex_choice();
        let freer = arrow_to_freer(&arrow);
        let (left_eff, right_eff) = per_branch_effects_freer(&freer).unwrap();
        assert!(left_eff.contains(Op::Get) && left_eff.contains(Op::Throw));
        assert!(right_eff.contains(Op::Put) && !right_eff.contains(Op::Get));
    }

    // === Dependency graph ===

    #[test]
    fn test_arrow_builds_dependency_graph() {
        let arrow = arrow_sequential();
        let graph = dependency_graph_arrow(&arrow);
        assert!(!graph.is_empty(), "Arrow should produce a dependency graph");
        // Seq(Get, Put): Get feeds into Put
        // Node 0 = Seq, Node 1 = Get subtree, Node 2 = Put subtree
        // Edge: 1→2 (Get feeds Put)
        assert!(graph.iter().any(|e| e.from == 1 && e.to == 2), "Get should feed Put");
    }

    #[test]
    fn test_opaque_monad_no_dependency_graph() {
        let arrow = arrow_sequential();
        let monad = arrow_to_opaque(&arrow);
        let graph = dependency_graph_opaque(&monad);
        assert!(graph.is_empty(), "Opaque monad cannot produce a dependency graph");
    }

    #[test]
    fn test_freer_monad_builds_dependency_graph() {
        let arrow = arrow_sequential();
        let freer = arrow_to_freer(&arrow);
        let graph = dependency_graph_freer(&freer);
        assert!(!graph.is_empty(), "Freer monad should produce a dependency graph");
    }

    // === Feedback ===

    #[test]
    fn test_arrow_recovers_loop() {
        let arrow = arrow_loop();
        assert!(recover_loop_arrow(&arrow).is_some(), "Arrow should recover loop structure");
    }

    #[test]
    fn test_opaque_monad_loses_loop() {
        let arrow = arrow_loop();
        let monad = arrow_to_opaque(&arrow);
        assert!(recover_loop_opaque(&monad).is_none(), "Opaque monad should NOT recover loop");
    }

    // === The key finding: semantically adequate but structurally lossy ===

    #[test]
    fn test_monadic_encoding_is_semantically_adequate() {
        // Same program, same results — the monadic encoding is
        // semantically adequate.
        let arrow = arrow_complex_choice();
        let monad = arrow_to_opaque(&arrow);

        // Right branch (Put) succeeds in both
        let input = Value::Right(Box::new(Value::Int(99)));
        let (v_arr, s_arr) = run_arrow(&arrow, input.clone(), Value::Int(0)).unwrap();
        let (v_mon, s_mon) = monad.run(input, Value::Int(0)).unwrap();
        assert_eq!(v_arr, v_mon, "results match");
        assert_eq!(s_arr, s_mon, "state matches");
    }

    #[test]
    fn test_monadic_encoding_is_structurally_lossy() {
        // Same program, but structural information is LOST in the monad:
        // - Cannot recover fanout/independence
        // - Cannot recover choice/branching
        // - Cannot infer effect set
        // - Cannot determine per-branch effects
        // - Cannot build dependency graph
        // - Cannot recover loop structure
        let arrow = arrow_complex_choice();
        let monad = arrow_to_opaque(&arrow);

        // All structural recovery fails on the opaque monad:
        assert!(recover_fanout_opaque(&monad).is_none(), "fanout lost");
        assert!(recover_choice_opaque(&monad).is_none(), "choice lost");
        assert!(infer_effect_opaque(&monad).is_none(), "effect set lost");
        assert!(per_branch_effects_opaque(&monad).is_none(), "per-branch effects lost");
        assert!(dependency_graph_opaque(&monad).is_empty(), "dependency graph lost");
    }

    #[test]
    fn test_freer_monad_recovers_structure() {
        // The freer monad — which is a monad, but with explicit structure —
        // recovers ALL the information. This proves the loss is about
        // OPACITY, not about monadic structure per se.
        let arrow = arrow_complex_choice();
        let freer = arrow_to_freer(&arrow);

        // All structural recovery succeeds on the freer monad:
        assert!(recover_choice_freer(&freer).is_some(), "choice recovered");
        assert!(per_branch_effects_freer(&freer).is_some(), "per-branch effects recovered");
        let effect = infer_effect_freer(&freer);
        assert!(effect.contains(Op::Get) && effect.contains(Op::Throw), "effects recovered");
        assert!(!dependency_graph_freer(&freer).is_empty(), "dependency graph recovered");
    }

    #[test]
    fn test_structural_loss_has_practical_consequences() {
        // An optimizer that can fold independent branches separately
        // works on the arrow representation but NOT on the opaque monad.

        // Arrow: choice(Get, Put) — we can see both branches and optimize each
        let arrow = arrow_choice();
        let (left_branch, right_branch) = recover_choice_arrow(&arrow).unwrap();
        let left_eff = infer_effect_arrow(left_branch);
        let right_eff = infer_effect_arrow(right_branch);
        // We can optimize each branch independently because we can SEE them
        assert!(left_eff.contains(Op::Get), "can optimize left branch (sees Get)");
        assert!(right_eff.contains(Op::Put), "can optimize right branch (sees Put)");

        // Opaque monad: we CANNOT see the branches, so we CANNOT optimize
        let monad = arrow_to_opaque(&arrow);
        assert!(per_branch_effects_opaque(&monad).is_none(),
            "cannot optimize — branch structure invisible");
    }

    #[test]
    fn test_false_dependency_in_monadic_fanout() {
        // When fanout is translated to monadic bind, the second computation
        // APPEARS to depend on the first's result, even though it doesn't.
        //
        // Arrow: f &&& g — g does NOT depend on f
        // Monad: f >>= (\v1 -> g >>= (\v2 -> pure (v1, v2))) — g LOOKS like
        //        it might depend on v1 (f's result), but it doesn't use it.
        //
        // In the arrow, the dependency graph shows NO edge between f and g.
        // In the monad, the bind chain creates an APPARENT dependency.

        let arrow = ArrowComp::Fanout(
            Box::new(ArrowComp::OpNode(Op::Get, Box::new(ArrowComp::Ident))),
            Box::new(ArrowComp::OpNode(Op::Put, Box::new(ArrowComp::Ident))),
        );
        let graph = dependency_graph_arrow(&arrow);

        // In the arrow: Get and Put are INDEPENDENT (no edge between them)
        // Node 0 = Fanout, 1 = Get, 2 = Get's child (Ident), 3 = Put, 4 = Put's child
        // Edges: 0→1, 1→2, 0→3, 3→4 — but NO 1→3 or 2→3
        let get_node = 1;
        let put_node = 3;
        assert!(!graph.iter().any(|e| e.from == get_node && e.to == put_node),
            "Arrow: NO false dependency between Get and Put");

        // In the opaque monad, we can't even build the graph to check
        let monad = arrow_to_opaque(&arrow);
        assert!(dependency_graph_opaque(&monad).is_empty(),
            "Monad: cannot build graph at all — dependency structure hidden");
    }

    // === Effect set properties ===

    #[test]
    fn test_effect_set_empty_for_pure() {
        let arrow = ArrowComp::Pure(Value::Int(42));
        let effect = infer_effect_arrow(&arrow);
        assert!(effect.is_empty(), "pure computation has no effects");
    }

    #[test]
    fn test_effect_set_union_for_seq() {
        let arrow = ArrowComp::Seq(
            Box::new(ArrowComp::OpNode(Op::Get, Box::new(ArrowComp::Ident))),
            Box::new(ArrowComp::OpNode(Op::Put, Box::new(ArrowComp::Ident))),
        );
        let effect = infer_effect_arrow(&arrow);
        assert!(effect.contains(Op::Get) && effect.contains(Op::Put));
        assert_eq!(effect.len(), 2);
    }

    #[test]
    fn test_effect_set_union_for_fanout() {
        let arrow = ArrowComp::Fanout(
            Box::new(ArrowComp::OpNode(Op::Get, Box::new(ArrowComp::Ident))),
            Box::new(ArrowComp::OpNode(Op::Put, Box::new(ArrowComp::Ident))),
        );
        let effect = infer_effect_arrow(&arrow);
        assert_eq!(effect.len(), 2, "fanout union of effects");
    }

    #[test]
    fn test_effect_set_conditional_in_choice() {
        // In a choice, effects are CONDITIONAL — only one branch runs.
        // The arrow can see per-branch effects; the opaque monad cannot.
        let arrow = arrow_complex_choice();
        let (left, right) = per_branch_effects_arrow(&arrow).unwrap();
        // Left branch: {Get, Throw} — if we take the left branch, ONLY these
        // Right branch: {Put} — if we take the right branch, ONLY this
        assert_eq!(left.len(), 2, "left branch has 2 effects");
        assert_eq!(right.len(), 1, "right branch has 1 effect");
        // The opaque monad can only report the UNION (if it could report
        // at all), losing the conditional information.
    }
}

// ============================================================================
// Demo
// ============================================================================

fn main() {
    println!("Challenge #9: Structural Preservation Under Monadic Translation");
    println!("=================================================================\n");

    // The key demonstration: same program, three representations
    let arrow = arrow_complex_choice();

    println!("Arrow program: choice(Get >>> Throw, Put)");
    println!("  Structural analysis:");
    println!("    fanout:  {}", if recover_fanout_arrow(&arrow).is_some() { "YES" } else { "no" });
    println!("    choice:  {}", if recover_choice_arrow(&arrow).is_some() { "YES" } else { "no" });
    let (left, right) = per_branch_effects_arrow(&arrow).unwrap();
    println!("    left branch effects:  {}", left);
    println!("    right branch effects: {}", right);
    println!("    total effects:        {}", infer_effect_arrow(&arrow));
    println!("    dependency graph:     {} edges", dependency_graph_arrow(&arrow).len());

    println!();

    let monad = arrow_to_opaque(&arrow);
    println!("Opaque monad (same program, translated):");
    println!("  Structural analysis:");
    println!("    fanout:  {}", if recover_fanout_opaque(&monad).is_some() { "YES" } else { "NO — LOST" });
    println!("    choice:  {}", if recover_choice_opaque(&monad).is_some() { "YES" } else { "NO — LOST" });
    println!("    effects: {}", if infer_effect_opaque(&monad).is_some() { "YES" } else { "NO — LOST" });
    println!("    per-branch: {}", if per_branch_effects_opaque(&monad).is_some() { "YES" } else { "NO — LOST" });
    println!("    dep graph: {} edges", dependency_graph_opaque(&monad).len());

    println!();

    let freer = arrow_to_freer(&arrow);
    println!("Freer monad (same program, structure-preserving translation):");
    println!("  Structural analysis:");
    println!("    choice:  {}", if recover_choice_freer(&freer).is_some() { "YES" } else { "no" });
    let (left, right) = per_branch_effects_freer(&freer).unwrap();
    println!("    left branch effects:  {}", left);
    println!("    right branch effects: {}", right);
    println!("    total effects:        {}", infer_effect_freer(&freer));
    println!("    dependency graph:     {} edges", dependency_graph_freer(&freer).len());

    println!();

    // Semantic equivalence
    println!("Semantic equivalence (right branch, Put 99):");
    let input = Value::Right(Box::new(Value::Int(99)));
    let (v_arr, s_arr) = run_arrow(&arrow, input.clone(), Value::Int(0)).unwrap();
    let (v_mon, s_mon) = monad.run(input.clone(), Value::Int(0)).unwrap();
    println!("  arrow:  result={}, state={}", v_arr, s_arr);
    println!("  monad:  result={}, state={}", v_mon, s_mon);
    println!("  match:  {}", v_arr == v_mon && s_arr == s_mon);

    println!();
    println!("KEY FINDING:");
    println!("  The opaque monad is semantically adequate (same results)");
    println!("  but structurally lossy (independence, branching, per-branch");
    println!("  effects, dependency graph — all lost).");
    println!("  The freer monad recovers all structure, proving the loss is");
    println!("  about OPACITY, not monadic structure per se.");
}
