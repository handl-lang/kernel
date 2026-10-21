// AI-Generated Code Structure Experiment
//
// THE QUESTION (from PAPER.tex §8.3, currently speculation):
//
//   Is the arrow representation more robust to AI-generated code than the
//   lambda representation for structural analysis?
//
// The thesis (THESIS.md, "What the structural advantage is NOT over")
// already clarifies the precise claim:
//
//   - Lambda ASTs ARE inspectable (unlike opaque closures).
//   - The advantage is ENFORCEMENT vs. PERMISSION: arrows make
//     computational structure explicit by construction; lambda permits
//     it to be implicit (and therefore obscurable).
//   - Both representations CAN yield the same structural information;
//     arrows give it by construction, lambda requires recovery through
//     analysis.
//
// This experiment turns that architectural argument into EVIDENCE by
// testing three analysis levels on the same computations:
//
//   1. NAIVE lambda analysis  — syntactic: let-chain = dependency
//   2. SOPHISTICATED lambda analysis — data-flow: tracks variable usage
//   3. ARROW analysis — by construction: reads combinators directly
//
// We measure: false dependencies (false positives), analysis steps,
// structural facts recoverable, and robustness to obscuration.
//
// HONEST FRAMING: The thesis already says lambda CAN recover structure
// with analysis. So we expect:
//   - Naive lambda: FALSE DEPENDENCIES on obscured code
//   - Sophisticated lambda: CORRECT but more analysis work
//   - Arrow: CORRECT by construction, minimal work
//   - The gap is about ANALYSIS EFFORT and ROBUSTNESS, not impossibility

use std::collections::HashSet;
use std::fmt;

// ============================================================================
// Shared Types
// ============================================================================

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
            return write!(f, "{{}}");
        }
        let mut ops: Vec<_> = self.ops.iter().collect();
        ops.sort_by_key(|o| format!("{:?}", o));
        let names: Vec<_> = ops.iter().map(|o| o.to_string()).collect();
        write!(f, "{{{}}}", names.join(", "))
    }
}

// ============================================================================
// Lambda AST (inspectable syntax tree — NOT opaque closures)
// ============================================================================
//
// This is a proper syntax tree. It is fully traversable, unlike the
// OpaqueM from Challenge #9. The thesis explicitly acknowledges that
// lambda ASTs are inspectable. The question is not "can you inspect
// lambda?" but "how much analysis is needed to recover structure, and
// how robust is that analysis to obscuration?"

#[derive(Debug, Clone, PartialEq)]
pub enum Lam {
    // Variable reference
    Var(String),
    // Integer literal
    Int(i32),
    // Boolean literal
    Bool(bool),
    // Unit value
    Unit,
    // Pair
    Pair(Box<Lam>, Box<Lam>),
    // Lambda abstraction: λx. body
    Lam(String, Box<Lam>),
    // Function application: f arg
    App(Box<Lam>, Box<Lam>),
    // Let-binding: let x = e1 in e2
    // This is the key construct: it CREATES a sequential appearance.
    // Whether e2 actually DEPENDS on e1 depends on whether x is used.
    Let(String, Box<Lam>, Box<Lam>),
    // Conditional: if cond then t else f
    If(Box<Lam>, Box<Lam>, Box<Lam>),
    // Primitive function call (pure): e.g. f(x) where f is a named primitive
    Prim(String, Box<Lam>),
    // Effect operation: Get, Put, Throw
    OpCall(Op),
    // Recursive function: rec name = λparam. body
    // The recursion is the lambda way to express feedback.
    Rec(String, String, Box<Lam>),
    // Sequence: evaluate e1, then e2 (e1 result discarded)
    // This is an AI-code pattern: compute something, ignore it, do something else
    Seq(Box<Lam>, Box<Lam>),
}

impl fmt::Display for Lam {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Lam::Var(x) => write!(f, "{}", x),
            Lam::Int(n) => write!(f, "{}", n),
            Lam::Bool(b) => write!(f, "{}", b),
            Lam::Unit => write!(f, "()"),
            Lam::Pair(a, b) => write!(f, "({}, {})", a, b),
            Lam::Lam(x, body) => write!(f, "λ{}. {}", x, body),
            Lam::App(g, a) => write!(f, "({} {})", g, a),
            Lam::Let(x, e1, e2) => write!(f, "let {} = {} in {}", x, e1, e2),
            Lam::If(c, t, e) => write!(f, "if {} then {} else {}", c, t, e),
            Lam::Prim(name, arg) => write!(f, "{}({})", name, arg),
            Lam::OpCall(op) => write!(f, "{}", op),
            Lam::Rec(name, param, body) => {
                write!(f, "rec {} = λ{}. {}", name, param, body)
            }
            Lam::Seq(a, b) => write!(f, "{}; {}", a, b),
        }
    }
}

// ============================================================================
// Arrow AST (structure explicit by construction)
// ============================================================================
//
// The arrow representation has explicit connectives. Each combinator
// IS a structural fact:
//   Seq   = "g depends on f's output"
//   Fanout = "f and g are independent"
//   Choice = "branching: Left → f, Right → g"
//   Loop   = "feedback"

#[derive(Debug, Clone, PartialEq)]
pub enum Arrow {
    // Pure value (constant)
    Pure(Lam),
    // Identity: pass input through
    Ident,
    // Primitive function lifted to arrow: arr(f)
    ArrPrim(String),
    // f >>> g — sequential composition (g depends on f's output)
    Seq(Box<Arrow>, Box<Arrow>),
    // f &&& g — fanout: both consume same input, INDEPENDENT
    Fanout(Box<Arrow>, Box<Arrow>),
    // choice f g — branching: Left → f, Right → g
    Choice(Box<Arrow>, Box<Arrow>),
    // perform an operation
    OpNode(Op),
    // loop — feedback
    Loop(Box<Arrow>),
}

impl fmt::Display for Arrow {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Arrow::Pure(v) => write!(f, "pure({})", v),
            Arrow::Ident => write!(f, "id"),
            Arrow::ArrPrim(name) => write!(f, "arr({})", name),
            Arrow::Seq(a, b) => write!(f, "({} >>> {})", a, b),
            Arrow::Fanout(a, b) => write!(f, "({} &&& {})", a, b),
            Arrow::Choice(a, b) => write!(f, "choice({},{})", a, b),
            Arrow::OpNode(op) => write!(f, "{}", op),
            Arrow::Loop(body) => write!(f, "loop({})", body),
        }
    }
}

// ============================================================================
// Analysis Result Types
// ============================================================================

/// A labeled sub-computation for dependency analysis.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Node {
    pub id: usize,
    pub label: String,
}

/// A dependency edge: `from` feeds into `to`.
/// FALSE edges are marked as such for analysis.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DepEdge {
    pub from: usize,
    pub to: usize,
    pub is_false: bool, // true if this is a false dependency
}

/// The result of structural analysis on a computation.
#[derive(Debug, Clone)]
pub struct AnalysisResult {
    pub nodes: Vec<Node>,
    pub edges: Vec<DepEdge>,
    pub independent_pairs: Vec<(usize, usize)>, // pairs of independent sub-computations
    pub effects: Effect,
    pub per_branch_effects: Option<(Effect, Effect)>,
    pub has_feedback: bool,
    pub false_dependencies: usize,
    pub analysis_steps: usize,
    pub facts_recoverable: usize,
}

// ============================================================================
// Lambda Analysis: NAIVE (syntactic — let-chain = dependency)
// ============================================================================
//
// The naive analysis treats every let-binding as creating a dependency:
// `let x = e1 in e2` means e2 depends on e1. This is the simplest
// possible syntactic analysis — it does NOT check whether x is actually
// used in e2.
//
// This is the kind of analysis a simple tool (or a human skimming code)
// might do. It is FAST but WRONG on obscured code.

pub fn naive_lambda_analysis(term: &Lam) -> AnalysisResult {
    let mut nodes = Vec::new();
    let mut edges = Vec::new();
    let mut steps = 0usize;
    let mut next_id = 0usize;
    let effects = naive_lambda_effects(term, &mut steps);
    let has_feedback = naive_lambda_has_feedback(term, &mut steps);
    let _ = naive_lambda_dep_graph(term, &mut nodes, &mut edges, &mut next_id, &mut steps, None);

    // Naive analysis cannot determine per-branch effects (it doesn't
    // analyze branch structure properly)
    let per_branch = naive_lambda_per_branch_effects(term, &mut steps);

    // Count independent pairs: naive analysis finds NONE (every let-chain
    // looks like a dependency)
    let independent_pairs = Vec::new();

    // All edges are treated as real by the naive analysis (it doesn't
    // know they're false). We mark them as false AFTER the fact by
    // comparing with ground truth (done in the comparison, not here).
    let false_deps = 0; // naive analysis doesn't KNOW its deps are false

    let facts = count_facts(&nodes, &edges, &independent_pairs, per_branch.is_some(), has_feedback);

    AnalysisResult {
        nodes,
        edges,
        independent_pairs,
        effects,
        per_branch_effects: per_branch,
        has_feedback,
        false_dependencies: false_deps,
        analysis_steps: steps,
        facts_recoverable: facts,
    }
}

fn naive_lambda_dep_graph(
    term: &Lam,
    nodes: &mut Vec<Node>,
    edges: &mut Vec<DepEdge>,
    next_id: &mut usize,
    steps: &mut usize,
    parent: Option<usize>,
) -> usize {
    *steps += 1;
    let my_id = *next_id;
    *next_id += 1;
    let label = lam_label(term);
    nodes.push(Node { id: my_id, label });

    if let Some(p) = parent {
        edges.push(DepEdge { from: p, to: my_id, is_false: false });
    }

    match term {
        Lam::Var(_) | Lam::Int(_) | Lam::Bool(_) | Lam::Unit | Lam::OpCall(_) => {}
        Lam::Pair(a, b) => {
            naive_lambda_dep_graph(a, nodes, edges, next_id, steps, Some(my_id));
            naive_lambda_dep_graph(b, nodes, edges, next_id, steps, Some(my_id));
        }
        Lam::Lam(_, body) => {
            naive_lambda_dep_graph(body, nodes, edges, next_id, steps, Some(my_id));
        }
        Lam::App(g, a) => {
            naive_lambda_dep_graph(g, nodes, edges, next_id, steps, Some(my_id));
            naive_lambda_dep_graph(a, nodes, edges, next_id, steps, Some(my_id));
        }
        Lam::Let(_x, e1, e2) => {
            // NAIVE: let-chain creates a dependency from e1 to e2
            // This is the KEY: we assume e2 depends on e1 without checking
            let e1_id = naive_lambda_dep_graph(e1, nodes, edges, next_id, steps, None);
            let e2_id = naive_lambda_dep_graph(e2, nodes, edges, next_id, steps, None);
            // Create dependency edge e1 → e2 (may be FALSE)
            edges.push(DepEdge { from: e1_id, to: e2_id, is_false: false });
        }
        Lam::If(c, t, e) => {
            naive_lambda_dep_graph(c, nodes, edges, next_id, steps, Some(my_id));
            naive_lambda_dep_graph(t, nodes, edges, next_id, steps, Some(my_id));
            naive_lambda_dep_graph(e, nodes, edges, next_id, steps, Some(my_id));
        }
        Lam::Prim(_, arg) => {
            naive_lambda_dep_graph(arg, nodes, edges, next_id, steps, Some(my_id));
        }
        Lam::Rec(_, _, body) => {
            naive_lambda_dep_graph(body, nodes, edges, next_id, steps, Some(my_id));
        }
        Lam::Seq(a, b) => {
            // NAIVE: sequence creates a dependency from a to b
            let a_id = naive_lambda_dep_graph(a, nodes, edges, next_id, steps, None);
            let b_id = naive_lambda_dep_graph(b, nodes, edges, next_id, steps, None);
            edges.push(DepEdge { from: a_id, to: b_id, is_false: false });
        }
    }
    my_id
}

fn naive_lambda_effects(term: &Lam, steps: &mut usize) -> Effect {
    *steps += 1;
    match term {
        Lam::Var(_) | Lam::Int(_) | Lam::Bool(_) | Lam::Unit => Effect::empty(),
        Lam::OpCall(op) => Effect::singleton(*op),
        Lam::Pair(a, b) => {
            naive_lambda_effects(a, steps).union(&naive_lambda_effects(b, steps))
        }
        Lam::Lam(_, body) => naive_lambda_effects(body, steps),
        Lam::App(g, a) => {
            naive_lambda_effects(g, steps).union(&naive_lambda_effects(a, steps))
        }
        Lam::Let(_, e1, e2) => {
            naive_lambda_effects(e1, steps).union(&naive_lambda_effects(e2, steps))
        }
        Lam::If(c, t, e) => {
            naive_lambda_effects(c, steps)
                .union(&naive_lambda_effects(t, steps))
                .union(&naive_lambda_effects(e, steps))
        }
        Lam::Prim(_, arg) => naive_lambda_effects(arg, steps),
        Lam::Rec(_, _, body) => naive_lambda_effects(body, steps),
        Lam::Seq(a, b) => {
            naive_lambda_effects(a, steps).union(&naive_lambda_effects(b, steps))
        }
    }
}

fn naive_lambda_has_feedback(term: &Lam, steps: &mut usize) -> bool {
    *steps += 1;
    match term {
        Lam::Var(_) | Lam::Int(_) | Lam::Bool(_) | Lam::Unit | Lam::OpCall(_) => false,
        Lam::Pair(a, b) | Lam::App(a, b) | Lam::Let(_, a, b) | Lam::Seq(a, b) => {
            naive_lambda_has_feedback(a, steps) || naive_lambda_has_feedback(b, steps)
        }
        Lam::Lam(_, body) | Lam::Prim(_, body) => naive_lambda_has_feedback(body, steps),
        Lam::If(c, t, e) => {
            naive_lambda_has_feedback(c, steps)
                || naive_lambda_has_feedback(t, steps)
                || naive_lambda_has_feedback(e, steps)
        }
        // Rec is the lambda way to express feedback — naive analysis
        // CAN detect this (it sees the Rec constructor)
        Lam::Rec(_, _, _) => true,
    }
}

fn naive_lambda_per_branch_effects(term: &Lam, steps: &mut usize) -> Option<(Effect, Effect)> {
    *steps += 1;
    match term {
        Lam::If(_, t, e) => {
            // Naive analysis CAN see if-then-else and report per-branch effects
            // (this is one place where naive lambda analysis does OK)
            let t_eff = naive_lambda_effects(t, steps);
            let e_eff = naive_lambda_effects(e, steps);
            Some((t_eff, e_eff))
        }
        // Look inside lambdas, lets, and other wrappers to find if-then-else
        Lam::Lam(_, body) => naive_lambda_per_branch_effects(body, steps),
        Lam::Let(_, _, body) => naive_lambda_per_branch_effects(body, steps),
        _ => None,
    }
}

// ============================================================================
// Lambda Analysis: SOPHISTICATED (data-flow — tracks variable usage)
// ============================================================================
//
// The sophisticated analysis does proper data-flow analysis:
// - For `let x = e1 in e2`, it checks whether x is actually USED in e2.
//   If x is not used, there is NO dependency from e1 to e2.
// - This requires computing free variables of sub-terms.
//
// This analysis is CORRECT but requires more work (free-variable
// computation, use-def chains). It represents the best case for lambda.

/// Compute the set of free variables in a lambda term.
pub fn free_vars(term: &Lam) -> HashSet<String> {
    match term {
        Lam::Var(x) => {
            let mut s = HashSet::new();
            s.insert(x.clone());
            s
        }
        Lam::Int(_) | Lam::Bool(_) | Lam::Unit | Lam::OpCall(_) => HashSet::new(),
        Lam::Pair(a, b) => {
            let mut s = free_vars(a);
            s.extend(free_vars(b));
            s
        }
        Lam::Lam(x, body) => {
            let mut s = free_vars(body);
            s.remove(x);
            s
        }
        Lam::App(g, a) => {
            let mut s = free_vars(g);
            s.extend(free_vars(a));
            s
        }
        Lam::Let(x, e1, e2) => {
            // x is bound, so removed from e2's free vars
            let mut s = free_vars(e1);
            let mut e2_vars = free_vars(e2);
            e2_vars.remove(x);
            s.extend(e2_vars);
            s
        }
        Lam::If(c, t, e) => {
            let mut s = free_vars(c);
            s.extend(free_vars(t));
            s.extend(free_vars(e));
            s
        }
        Lam::Prim(_, arg) => free_vars(arg),
        Lam::Rec(name, param, body) => {
            let mut s = free_vars(body);
            s.remove(param);
            s.remove(name);
            s
        }
        Lam::Seq(a, b) => {
            let mut s = free_vars(a);
            s.extend(free_vars(b));
            s
        }
    }
}

/// Check whether a variable is used in a term.
pub fn uses_var(term: &Lam, var: &str) -> bool {
    free_vars(term).contains(var)
}

pub fn sophisticated_lambda_analysis(term: &Lam) -> AnalysisResult {
    let mut nodes = Vec::new();
    let mut edges = Vec::new();
    let mut steps = 0usize;
    let mut next_id = 0usize;
    let mut false_deps = 0usize;

    let effects = sophisticated_lambda_effects(term, &mut steps);
    let has_feedback = sophisticated_lambda_has_feedback(term, &mut steps);
    let _ = sophisticated_lambda_dep_graph(
        term,
        &mut nodes,
        &mut edges,
        &mut next_id,
        &mut steps,
        None,
        &mut false_deps,
    );

    let per_branch = sophisticated_lambda_per_branch_effects(term, &mut steps);

    // Sophisticated analysis CAN detect independence by checking variable usage
    let independent_pairs =
        sophisticated_lambda_find_independence(term, &mut steps);

    let facts = count_facts(
        &nodes,
        &edges,
        &independent_pairs,
        per_branch.is_some(),
        has_feedback,
    );

    AnalysisResult {
        nodes,
        edges,
        independent_pairs,
        effects,
        per_branch_effects: per_branch,
        has_feedback,
        false_dependencies: false_deps,
        analysis_steps: steps,
        facts_recoverable: facts,
    }
}

fn sophisticated_lambda_dep_graph(
    term: &Lam,
    nodes: &mut Vec<Node>,
    edges: &mut Vec<DepEdge>,
    next_id: &mut usize,
    steps: &mut usize,
    parent: Option<usize>,
    false_deps: &mut usize,
) -> usize {
    *steps += 1;
    let my_id = *next_id;
    *next_id += 1;
    let label = lam_label(term);
    nodes.push(Node { id: my_id, label });

    if let Some(p) = parent {
        edges.push(DepEdge { from: p, to: my_id, is_false: false });
    }

    match term {
        Lam::Var(_) | Lam::Int(_) | Lam::Bool(_) | Lam::Unit | Lam::OpCall(_) => {}
        Lam::Pair(a, b) => {
            sophisticated_lambda_dep_graph(a, nodes, edges, next_id, steps, Some(my_id), false_deps);
            sophisticated_lambda_dep_graph(b, nodes, edges, next_id, steps, Some(my_id), false_deps);
        }
        Lam::Lam(_, body) => {
            sophisticated_lambda_dep_graph(body, nodes, edges, next_id, steps, Some(my_id), false_deps);
        }
        Lam::App(g, a) => {
            sophisticated_lambda_dep_graph(g, nodes, edges, next_id, steps, Some(my_id), false_deps);
            sophisticated_lambda_dep_graph(a, nodes, edges, next_id, steps, Some(my_id), false_deps);
        }
        Lam::Let(x, e1, e2) => {
            let e1_id = sophisticated_lambda_dep_graph(e1, nodes, edges, next_id, steps, None, false_deps);
            let e2_id = sophisticated_lambda_dep_graph(e2, nodes, edges, next_id, steps, None, false_deps);

            // SOPHISTICATED: check whether x is actually used in e2
            *steps += 1; // cost of free-variable computation
            let e2_uses_x = uses_var(e2, x);

            if e2_uses_x {
                // Real dependency: e2 uses x which is bound by e1
                edges.push(DepEdge { from: e1_id, to: e2_id, is_false: false });
            } else {
                // FALSE dependency: x is not used in e2, so e2 does NOT
                // depend on e1. We do NOT create an edge.
                // But we record that a false dependency WOULD have been
                // created by the naive analysis.
                *false_deps += 1;
            }
        }
        Lam::If(c, t, e) => {
            sophisticated_lambda_dep_graph(c, nodes, edges, next_id, steps, Some(my_id), false_deps);
            sophisticated_lambda_dep_graph(t, nodes, edges, next_id, steps, Some(my_id), false_deps);
            sophisticated_lambda_dep_graph(e, nodes, edges, next_id, steps, Some(my_id), false_deps);
        }
        Lam::Prim(_, arg) => {
            sophisticated_lambda_dep_graph(arg, nodes, edges, next_id, steps, Some(my_id), false_deps);
        }
        Lam::Rec(_, _, body) => {
            sophisticated_lambda_dep_graph(body, nodes, edges, next_id, steps, Some(my_id), false_deps);
        }
        Lam::Seq(a, b) => {
            let _a_id = sophisticated_lambda_dep_graph(a, nodes, edges, next_id, steps, None, false_deps);
            let _b_id = sophisticated_lambda_dep_graph(b, nodes, edges, next_id, steps, None, false_deps);
            // SOPHISTICATED: Seq discards a's result, so b does NOT depend on a
            // (unless b references something from a, which it can't in Seq)
            *false_deps += 1; // a false dependency that naive analysis would create
        }
    }
    my_id
}

fn sophisticated_lambda_effects(term: &Lam, steps: &mut usize) -> Effect {
    // Same as naive for effects — effect inference is a traversal
    // and doesn't benefit from data-flow analysis (effects are not
    // about dependencies, they're about what operations appear)
    *steps += 1;
    match term {
        Lam::Var(_) | Lam::Int(_) | Lam::Bool(_) | Lam::Unit => Effect::empty(),
        Lam::OpCall(op) => Effect::singleton(*op),
        Lam::Pair(a, b) => {
            sophisticated_lambda_effects(a, steps).union(&sophisticated_lambda_effects(b, steps))
        }
        Lam::Lam(_, body) => sophisticated_lambda_effects(body, steps),
        Lam::App(g, a) => {
            sophisticated_lambda_effects(g, steps).union(&sophisticated_lambda_effects(a, steps))
        }
        Lam::Let(_, e1, e2) => {
            sophisticated_lambda_effects(e1, steps).union(&sophisticated_lambda_effects(e2, steps))
        }
        Lam::If(c, t, e) => {
            sophisticated_lambda_effects(c, steps)
                .union(&sophisticated_lambda_effects(t, steps))
                .union(&sophisticated_lambda_effects(e, steps))
        }
        Lam::Prim(_, arg) => sophisticated_lambda_effects(arg, steps),
        Lam::Rec(_, _, body) => sophisticated_lambda_effects(body, steps),
        Lam::Seq(a, b) => {
            sophisticated_lambda_effects(a, steps).union(&sophisticated_lambda_effects(b, steps))
        }
    }
}

fn sophisticated_lambda_has_feedback(term: &Lam, steps: &mut usize) -> bool {
    // Same as naive — Rec is detectable syntactically
    *steps += 1;
    match term {
        Lam::Var(_) | Lam::Int(_) | Lam::Bool(_) | Lam::Unit | Lam::OpCall(_) => false,
        Lam::Pair(a, b) | Lam::App(a, b) | Lam::Let(_, a, b) | Lam::Seq(a, b) => {
            sophisticated_lambda_has_feedback(a, steps)
                || sophisticated_lambda_has_feedback(b, steps)
        }
        Lam::Lam(_, body) | Lam::Prim(_, body) => {
            sophisticated_lambda_has_feedback(body, steps)
        }
        Lam::If(c, t, e) => {
            sophisticated_lambda_has_feedback(c, steps)
                || sophisticated_lambda_has_feedback(t, steps)
                || sophisticated_lambda_has_feedback(e, steps)
        }
        Lam::Rec(_, _, _) => true,
    }
}

fn sophisticated_lambda_per_branch_effects(term: &Lam, steps: &mut usize) -> Option<(Effect, Effect)> {
    // Same as naive — if-then-else is visible syntactically
    *steps += 1;
    match term {
        Lam::If(_, t, e) => {
            let t_eff = sophisticated_lambda_effects(t, steps);
            let e_eff = sophisticated_lambda_effects(e, steps);
            Some((t_eff, e_eff))
        }
        // Look inside lambdas, lets, and other wrappers to find if-then-else
        Lam::Lam(_, body) => sophisticated_lambda_per_branch_effects(body, steps),
        Lam::Let(_, _, body) => sophisticated_lambda_per_branch_effects(body, steps),
        _ => None,
    }
}

/// Detect independent sub-computations in a lambda term.
/// This requires data-flow analysis: two sub-computations are independent
/// if neither references the other's bound variables.
fn sophisticated_lambda_find_independence(term: &Lam, steps: &mut usize) -> Vec<(usize, usize)> {
    // For let x = e1 in e2 where x is NOT used in e2: e1 and e2 are independent.
    // We need to find these patterns and report the independence.
    // This requires the same free-variable analysis as the dep graph.
    let mut pairs = Vec::new();
    let mut counter = 0usize;
    sophisticated_find_independence_helper(term, steps, &mut pairs, &mut counter);
    pairs
}

fn sophisticated_find_independence_helper(
    term: &Lam,
    steps: &mut usize,
    pairs: &mut Vec<(usize, usize)>,
    counter: &mut usize,
) {
    *steps += 1;
    match term {
        Lam::Let(x, e1, e2) => {
            *steps += 1;
            if !uses_var(e2, x) {
                // e1 and e2 are independent!
                let a = *counter;
                *counter += 1;
                let b = *counter;
                *counter += 1;
                pairs.push((a, b));
            }
            sophisticated_find_independence_helper(e1, steps, pairs, counter);
            sophisticated_find_independence_helper(e2, steps, pairs, counter);
        }
        Lam::Seq(a, b) => {
            // Seq: temporal dependency (b happens after a, even if no data dep)
            // This is NOT independence — it's sequential ordering.
            // The arrow representation would use >>> (Seq), not &&& (Fanout).
            sophisticated_find_independence_helper(a, steps, pairs, counter);
            sophisticated_find_independence_helper(b, steps, pairs, counter);
        }
        Lam::Pair(a, b) => {
            // Pair components MIGHT be independent — need to check
            // if they share variables. This is harder.
            *steps += 1;
            let a_vars = free_vars(a);
            let b_vars = free_vars(b);
            if a_vars.is_disjoint(&b_vars) {
                let a_id = *counter;
                *counter += 1;
                let b_id = *counter;
                *counter += 1;
                pairs.push((a_id, b_id));
            }
            sophisticated_find_independence_helper(a, steps, pairs, counter);
            sophisticated_find_independence_helper(b, steps, pairs, counter);
        }
        Lam::Lam(_, body) | Lam::Prim(_, body) => {
            sophisticated_find_independence_helper(body, steps, pairs, counter);
        }
        Lam::App(g, a) => {
            sophisticated_find_independence_helper(g, steps, pairs, counter);
            sophisticated_find_independence_helper(a, steps, pairs, counter);
        }
        Lam::If(c, t, e) => {
            sophisticated_find_independence_helper(c, steps, pairs, counter);
            sophisticated_find_independence_helper(t, steps, pairs, counter);
            sophisticated_find_independence_helper(e, steps, pairs, counter);
        }
        Lam::Rec(_, _, body) => {
            sophisticated_find_independence_helper(body, steps, pairs, counter);
        }
        Lam::Var(_) | Lam::Int(_) | Lam::Bool(_) | Lam::Unit | Lam::OpCall(_) => {}
    }
}

// ============================================================================
// Arrow Analysis (by construction — reads combinators directly)
// ============================================================================
//
// The arrow analysis is trivial: each structural fact is a combinator.
// No data-flow analysis needed. No free-variable computation. No use-def
// chains. You just pattern-match on the AST.

pub fn arrow_analysis(comp: &Arrow) -> AnalysisResult {
    let mut nodes = Vec::new();
    let mut edges = Vec::new();
    let mut steps = 0usize;
    let mut next_id = 0usize;

    let effects = arrow_effects(comp, &mut steps);
    let has_feedback = arrow_has_feedback(comp, &mut steps);
    let _ = arrow_dep_graph(comp, &mut nodes, &mut edges, &mut next_id, &mut steps, None);

    let per_branch = arrow_per_branch_effects(comp, &mut steps);
    let independent_pairs = arrow_find_independence(comp, &mut steps);

    // Arrow analysis has ZERO false dependencies (structure is enforced)
    let facts = count_facts(
        &nodes,
        &edges,
        &independent_pairs,
        per_branch.is_some(),
        has_feedback,
    );

    AnalysisResult {
        nodes,
        edges,
        independent_pairs,
        effects,
        per_branch_effects: per_branch,
        has_feedback,
        false_dependencies: 0, // arrows enforce structure — no false deps
        analysis_steps: steps,
        facts_recoverable: facts,
    }
}

fn arrow_dep_graph(
    comp: &Arrow,
    nodes: &mut Vec<Node>,
    edges: &mut Vec<DepEdge>,
    next_id: &mut usize,
    steps: &mut usize,
    parent: Option<usize>,
) -> usize {
    *steps += 1;
    let my_id = *next_id;
    *next_id += 1;
    let label = arrow_label(comp);
    nodes.push(Node { id: my_id, label });

    if let Some(p) = parent {
        edges.push(DepEdge { from: p, to: my_id, is_false: false });
    }

    match comp {
        Arrow::Pure(_) | Arrow::Ident | Arrow::ArrPrim(_) | Arrow::OpNode(_) => {}
        Arrow::Seq(f, g) => {
            // Seq: f feeds into g — REAL dependency
            let f_id = arrow_dep_graph(f, nodes, edges, next_id, steps, None);
            let g_id = arrow_dep_graph(g, nodes, edges, next_id, steps, None);
            edges.push(DepEdge { from: f_id, to: g_id, is_false: false });
        }
        Arrow::Fanout(f, g) => {
            // Fanout: f and g are INDEPENDENT — no edge between them
            // Both depend on the same input (my_id), not on each other
            arrow_dep_graph(f, nodes, edges, next_id, steps, Some(my_id));
            arrow_dep_graph(g, nodes, edges, next_id, steps, Some(my_id));
            // NO edge between f and g — this is the key structural fact
        }
        Arrow::Choice(f, g) => {
            // Choice: branches are alternatives, not dependencies
            arrow_dep_graph(f, nodes, edges, next_id, steps, Some(my_id));
            arrow_dep_graph(g, nodes, edges, next_id, steps, Some(my_id));
        }
        Arrow::Loop(body) => {
            arrow_dep_graph(body, nodes, edges, next_id, steps, Some(my_id));
        }
    }
    my_id
}

fn arrow_effects(comp: &Arrow, steps: &mut usize) -> Effect {
    *steps += 1;
    match comp {
        Arrow::Pure(_) | Arrow::Ident | Arrow::ArrPrim(_) => Effect::empty(),
        Arrow::OpNode(op) => Effect::singleton(*op),
        Arrow::Seq(f, g) => arrow_effects(f, steps).union(&arrow_effects(g, steps)),
        Arrow::Fanout(f, g) => arrow_effects(f, steps).union(&arrow_effects(g, steps)),
        Arrow::Choice(f, g) => arrow_effects(f, steps).union(&arrow_effects(g, steps)),
        Arrow::Loop(body) => arrow_effects(body, steps),
    }
}

fn arrow_has_feedback(comp: &Arrow, steps: &mut usize) -> bool {
    *steps += 1;
    match comp {
        Arrow::Pure(_) | Arrow::Ident | Arrow::ArrPrim(_) | Arrow::OpNode(_) => false,
        Arrow::Loop(_) => true,
        Arrow::Seq(f, g) | Arrow::Fanout(f, g) | Arrow::Choice(f, g) => {
            arrow_has_feedback(f, steps) || arrow_has_feedback(g, steps)
        }
    }
}

fn arrow_per_branch_effects(comp: &Arrow, steps: &mut usize) -> Option<(Effect, Effect)> {
    *steps += 1;
    match comp {
        Arrow::Choice(f, g) => {
            Some((arrow_effects(f, steps), arrow_effects(g, steps)))
        }
        _ => None,
    }
}

fn arrow_find_independence(comp: &Arrow, steps: &mut usize) -> Vec<(usize, usize)> {
    let mut pairs = Vec::new();
    let mut counter = 0usize;
    arrow_find_independence_helper(comp, steps, &mut pairs, &mut counter);
    pairs
}

fn arrow_find_independence_helper(
    comp: &Arrow,
    steps: &mut usize,
    pairs: &mut Vec<(usize, usize)>,
    counter: &mut usize,
) {
    *steps += 1;
    match comp {
        Arrow::Fanout(f, g) => {
            // Fanout: f and g are independent BY CONSTRUCTION
            let a = *counter;
            *counter += 1;
            let b = *counter;
            *counter += 1;
            pairs.push((a, b));
            arrow_find_independence_helper(f, steps, pairs, counter);
            arrow_find_independence_helper(g, steps, pairs, counter);
        }
        Arrow::Seq(f, g) => {
            arrow_find_independence_helper(f, steps, pairs, counter);
            arrow_find_independence_helper(g, steps, pairs, counter);
        }
        Arrow::Choice(f, g) => {
            arrow_find_independence_helper(f, steps, pairs, counter);
            arrow_find_independence_helper(g, steps, pairs, counter);
        }
        Arrow::Loop(body) => {
            arrow_find_independence_helper(body, steps, pairs, counter);
        }
        Arrow::Pure(_) | Arrow::Ident | Arrow::ArrPrim(_) | Arrow::OpNode(_) => {}
    }
}

// ============================================================================
// Helper: labels and fact counting
// ============================================================================

fn lam_label(term: &Lam) -> String {
    match term {
        Lam::Var(x) => format!("var {}", x),
        Lam::Int(n) => format!("int {}", n),
        Lam::Bool(b) => format!("bool {}", b),
        Lam::Unit => "unit".to_string(),
        Lam::Pair(_, _) => "pair".to_string(),
        Lam::Lam(x, _) => format!("λ{}", x),
        Lam::App(_, _) => "app".to_string(),
        Lam::Let(x, _, _) => format!("let {}", x),
        Lam::If(_, _, _) => "if".to_string(),
        Lam::Prim(name, _) => format!("prim {}", name),
        Lam::OpCall(op) => format!("op {}", op),
        Lam::Rec(name, _, _) => format!("rec {}", name),
        Lam::Seq(_, _) => "seq".to_string(),
    }
}

fn arrow_label(comp: &Arrow) -> String {
    match comp {
        Arrow::Pure(_) => "pure".to_string(),
        Arrow::Ident => "id".to_string(),
        Arrow::ArrPrim(name) => format!("arr {}", name),
        Arrow::Seq(_, _) => ">>>".to_string(),
        Arrow::Fanout(_, _) => "&&&".to_string(),
        Arrow::Choice(_, _) => "choice".to_string(),
        Arrow::OpNode(op) => format!("op {}", op),
        Arrow::Loop(_) => "loop".to_string(),
    }
}

fn count_facts(
    nodes: &[Node],
    edges: &[DepEdge],
    independent_pairs: &[(usize, usize)],
    has_per_branch: bool,
    has_feedback: bool,
) -> usize {
    let mut facts = 0;
    // Dependency graph is a fact
    if !edges.is_empty() {
        facts += 1;
    }
    // Node count is a fact
    if !nodes.is_empty() {
        facts += 1;
    }
    // Independence is a fact
    facts += independent_pairs.len();
    // Per-branch effects is a fact
    if has_per_branch {
        facts += 1;
    }
    // Feedback detection is a fact
    if has_feedback {
        facts += 1;
    }
    facts
}

// ============================================================================
// The 8 Computations
// ============================================================================
//
// Each computation is defined in BOTH lambda form and arrow form.
// The lambda forms include "obscured" variants — the kind of code an
// LLM might produce: correct but structurally undisciplined.

/// A test computation with its lambda and arrow forms.
pub struct Computation {
    pub name: &'static str,
    pub description: &'static str,
    pub lambda: Lam,
    pub arrow: Arrow,
    /// The ground-truth number of independent pairs (for validation)
    pub true_independent_pairs: usize,
    /// The ground-truth: does this have feedback?
    pub true_has_feedback: bool,
    /// The ground-truth: does this have branching with per-branch effects?
    pub true_has_per_branch_effects: bool,
}

// --- Computation 1: Independent pair, obscured by let-chain ---
// True structure: f and g are independent (both consume x)
// Lambda obscured: let a = f(x) in let b = g(x) in (a, b)
//   - Naive: sees let-chain, thinks g depends on f (FALSE)
//   - Sophisticated: sees b doesn't reference a, concludes independent (TRUE)
// Arrow: f &&& g — independence explicit
pub fn comp1_independent_pair_obscured() -> Computation {
    Computation {
        name: "C1: Independent pair (obscured by let-chain)",
        description: "f(x) and g(x) are independent, but let-chain obscures it",
        lambda: Lam::Lam(
            "x".into(),
            Box::new(Lam::Let(
                "a".into(),
                Box::new(Lam::Prim("f".into(), Box::new(Lam::Var("x".into())))),
                Box::new(Lam::Let(
                    "b".into(),
                    Box::new(Lam::Prim("g".into(), Box::new(Lam::Var("x".into())))),
                    Box::new(Lam::Pair(
                        Box::new(Lam::Var("a".into())),
                        Box::new(Lam::Var("b".into())),
                    )),
                )),
            )),
        ),
        arrow: Arrow::Fanout(
            Box::new(Arrow::ArrPrim("f".into())),
            Box::new(Arrow::ArrPrim("g".into())),
        ),
        true_independent_pairs: 1,
        true_has_feedback: false,
        true_has_per_branch_effects: false,
    }
}

// --- Computation 2: Independent state reads, obscured by let-chain ---
// True structure: two Gets are independent
// Lambda obscured: let a = Get in let b = Get in (a, b)
//   - Naive: thinks second Get depends on first (FALSE)
//   - Sophisticated: sees b doesn't reference a, concludes independent (TRUE)
// Arrow: Get &&& Get — independence explicit
pub fn comp2_independent_reads_obscured() -> Computation {
    Computation {
        name: "C2: Independent state reads (obscured by let-chain)",
        description: "Two Get operations are independent, but let-chain obscures it",
        lambda: Lam::Lam(
            "_".into(),
            Box::new(Lam::Let(
                "a".into(),
                Box::new(Lam::OpCall(Op::Get)),
                Box::new(Lam::Let(
                    "b".into(),
                    Box::new(Lam::OpCall(Op::Get)),
                    Box::new(Lam::Pair(
                        Box::new(Lam::Var("a".into())),
                        Box::new(Lam::Var("b".into())),
                    )),
                )),
            )),
        ),
        arrow: Arrow::Fanout(
            Box::new(Arrow::OpNode(Op::Get)),
            Box::new(Arrow::OpNode(Op::Get)),
        ),
        true_independent_pairs: 1,
        true_has_feedback: false,
        true_has_per_branch_effects: false,
    }
}

// --- Computation 3: Real sequential dependency ---
// True structure: g depends on f's output
// Lambda: let a = f(x) in g(a) — REAL dependency
// Arrow: f >>> g — dependency explicit
// Both analyses should get this RIGHT
pub fn comp3_real_dependency() -> Computation {
    Computation {
        name: "C3: Real sequential dependency",
        description: "g genuinely depends on f's output — both should detect this",
        lambda: Lam::Lam(
            "x".into(),
            Box::new(Lam::Let(
                "a".into(),
                Box::new(Lam::Prim("f".into(), Box::new(Lam::Var("x".into())))),
                Box::new(Lam::Prim("g".into(), Box::new(Lam::Var("a".into())))),
            )),
        ),
        arrow: Arrow::Seq(
            Box::new(Arrow::ArrPrim("f".into())),
            Box::new(Arrow::ArrPrim("g".into())),
        ),
        true_independent_pairs: 0,
        true_has_feedback: false,
        true_has_per_branch_effects: false,
    }
}

// --- Computation 4: Mixed independent and dependent parts ---
// True structure: f→g is a dependency, h is independent of both
// Lambda obscured: let a = f(x) in let b = g(a) in let c = h(x) in (b, c)
//   - Naive: sees let-chain f→g→h, thinks h depends on g (FALSE)
//   - Sophisticated: sees c doesn't reference b, concludes h independent (TRUE)
// Arrow: (f >>> g) &&& h — structure explicit
pub fn comp4_mixed_independent_dependent() -> Computation {
    Computation {
        name: "C4: Mixed independent and dependent parts",
        description: "f→g is dependent, h is independent — let-chain obscures h's independence",
        lambda: Lam::Lam(
            "x".into(),
            Box::new(Lam::Let(
                "a".into(),
                Box::new(Lam::Prim("f".into(), Box::new(Lam::Var("x".into())))),
                Box::new(Lam::Let(
                    "b".into(),
                    Box::new(Lam::Prim("g".into(), Box::new(Lam::Var("a".into())))),
                    Box::new(Lam::Let(
                        "c".into(),
                        Box::new(Lam::Prim("h".into(), Box::new(Lam::Var("x".into())))),
                        Box::new(Lam::Pair(
                            Box::new(Lam::Var("b".into())),
                            Box::new(Lam::Var("c".into())),
                        )),
                    )),
                )),
            )),
        ),
        arrow: Arrow::Fanout(
            Box::new(Arrow::Seq(
                Box::new(Arrow::ArrPrim("f".into())),
                Box::new(Arrow::ArrPrim("g".into())),
            )),
            Box::new(Arrow::ArrPrim("h".into())),
        ),
        true_independent_pairs: 1,
        true_has_feedback: false,
        true_has_per_branch_effects: false,
    }
}

// --- Computation 5: Feedback obscured by recursion (factorial) ---
// True structure: feedback (fixed-point)
// Lambda: rec fact = λn. if n <= 1 then 1 else n * fact(n-1)
//   - Feedback is hidden in the recursive call
//   - Both naive and sophisticated CAN detect Rec syntactically
// Arrow: loop step — feedback explicit
pub fn comp5_feedback_recursion() -> Computation {
    Computation {
        name: "C5: Feedback obscured by recursion (factorial)",
        description: "Recursive factorial hides fixed-point structure; arrow loop makes it explicit",
        lambda: Lam::Rec(
            "fact".into(),
            "n".into(),
            Box::new(Lam::If(
                Box::new(Lam::Prim("<=".into(), Box::new(Lam::Var("n".into())))),
                Box::new(Lam::Int(1)),
                Box::new(Lam::Prim(
                    "*".into(),
                    Box::new(Lam::Var("n".into())),
                )),
            )),
        ),
        arrow: Arrow::Loop(Box::new(Arrow::ArrPrim("step".into()))),
        true_independent_pairs: 0,
        true_has_feedback: true,
        true_has_per_branch_effects: false,
    }
}

// --- Computation 6: Branching with per-branch effects ---
// True structure: two branches with different effects
// Lambda: if b then (Get; Throw) else Put(42)
//   - Both naive and sophisticated CAN see if-then-else
//   - Per-branch effects are recoverable (this is a case where lambda does OK)
// Arrow: choice (Get >>> Throw) Put — branching explicit
pub fn comp6_branching_effects() -> Computation {
    Computation {
        name: "C6: Branching with per-branch effects",
        description: "if-then-else with different effects per branch",
        lambda: Lam::Lam(
            "b".into(),
            Box::new(Lam::If(
                Box::new(Lam::Var("b".into())),
                Box::new(Lam::Seq(
                    Box::new(Lam::OpCall(Op::Get)),
                    Box::new(Lam::OpCall(Op::Throw)),
                )),
                Box::new(Lam::OpCall(Op::Put)),
            )),
        ),
        arrow: Arrow::Choice(
            Box::new(Arrow::Seq(
                Box::new(Arrow::OpNode(Op::Get)),
                Box::new(Arrow::OpNode(Op::Throw)),
            )),
            Box::new(Arrow::OpNode(Op::Put)),
        ),
        true_independent_pairs: 0,
        true_has_feedback: false,
        true_has_per_branch_effects: true,
    }
}

// --- Computation 7: Branching obscured by nested conditionals ---
// True structure: three-way branching
// Lambda: if b then (if c then Get else Put(1)) else Throw
//   - Nested if obscures the three-way structure
//   - Per-branch effects require recursive analysis
// Arrow: choice (choice Get Put) Throw — structure explicit
pub fn comp7_nested_branching() -> Computation {
    Computation {
        name: "C7: Branching obscured by nested conditionals",
        description: "Nested if-then-else obscures three-way branching structure",
        lambda: Lam::Lam(
            "b".into(),
            Box::new(Lam::If(
                Box::new(Lam::Var("b".into())),
                Box::new(Lam::If(
                    Box::new(Lam::Var("c".into())),
                    Box::new(Lam::OpCall(Op::Get)),
                    Box::new(Lam::OpCall(Op::Put)),
                )),
                Box::new(Lam::OpCall(Op::Throw)),
            )),
        ),
        arrow: Arrow::Choice(
            Box::new(Arrow::Choice(
                Box::new(Arrow::OpNode(Op::Get)),
                Box::new(Arrow::OpNode(Op::Put)),
            )),
            Box::new(Arrow::OpNode(Op::Throw)),
        ),
        true_independent_pairs: 0,
        true_has_feedback: false,
        true_has_per_branch_effects: true,
    }
}

// --- Computation 8: False dependency from unnecessary computation (AI pattern) ---
// True structure: a is computed but NEVER used; g is independent of f
// Lambda (AI pattern): let a = f(x) in g(x)  -- a is dead code
//   - Naive: thinks g depends on f (FALSE — let-chain creates apparent dependency)
//   - Sophisticated: sees a is unused, concludes independent (TRUE)
// Arrow: f &&& g — independence explicit (f's effect is kept, but no dependency)
pub fn comp8_false_dependency_ai_pattern() -> Computation {
    Computation {
        name: "C8: False dependency from unnecessary computation (AI pattern)",
        description: "LLM computes f(x), never uses it, then does g(x) — looks dependent, isn't",
        lambda: Lam::Lam(
            "x".into(),
            Box::new(Lam::Let(
                "a".into(),
                Box::new(Lam::Prim("f".into(), Box::new(Lam::Var("x".into())))),
                // a is NEVER referenced — dead code
                Box::new(Lam::Prim("g".into(), Box::new(Lam::Var("x".into())))),
            )),
        ),
        arrow: Arrow::Fanout(
            Box::new(Arrow::ArrPrim("f".into())),
            Box::new(Arrow::ArrPrim("g".into())),
        ),
        true_independent_pairs: 1,
        true_has_feedback: false,
        true_has_per_branch_effects: false,
    }
}

/// All 8 computations
pub fn all_computations() -> Vec<Computation> {
    vec![
        comp1_independent_pair_obscured(),
        comp2_independent_reads_obscured(),
        comp3_real_dependency(),
        comp4_mixed_independent_dependent(),
        comp5_feedback_recursion(),
        comp6_branching_effects(),
        comp7_nested_branching(),
        comp8_false_dependency_ai_pattern(),
    ]
}

// ============================================================================
// Comparison: run all three analyses on all computations
// ============================================================================

pub struct ComparisonRow {
    pub name: String,
    // Naive lambda
    pub naive_steps: usize,
    pub naive_independent_pairs: usize,
    pub naive_false_deps: usize, // deps that naive creates but are actually false
    pub naive_feedback: bool,
    pub naive_per_branch: bool,
    // Sophisticated lambda
    pub soph_steps: usize,
    pub soph_independent_pairs: usize,
    pub soph_false_deps: usize, // deps that soph correctly identifies as false
    pub soph_feedback: bool,
    pub soph_per_branch: bool,
    // Arrow
    pub arrow_steps: usize,
    pub arrow_independent_pairs: usize,
    pub arrow_false_deps: usize,
    pub arrow_feedback: bool,
    pub arrow_per_branch: bool,
    // Ground truth
    pub true_independent_pairs: usize,
    pub true_feedback: bool,
    pub true_per_branch: bool,
}

pub fn run_comparison() -> Vec<ComparisonRow> {
    all_computations()
        .iter()
        .map(|comp| {
            let naive = naive_lambda_analysis(&comp.lambda);
            let soph = sophisticated_lambda_analysis(&comp.lambda);
            let arr = arrow_analysis(&comp.arrow);

            // "false_deps" = missed independence: independent pairs the analysis
            // fails to detect. This is the key metric: how many independent
            // sub-computations does the analysis WRONGLY treat as dependent?
            let naive_missed = comp.true_independent_pairs.saturating_sub(naive.independent_pairs.len());
            let soph_missed = comp.true_independent_pairs.saturating_sub(soph.independent_pairs.len());
            let arrow_missed = comp.true_independent_pairs.saturating_sub(arr.independent_pairs.len());

            ComparisonRow {
                name: comp.name.to_string(),
                naive_steps: naive.analysis_steps,
                naive_independent_pairs: naive.independent_pairs.len(),
                naive_false_deps: naive_missed,
                naive_feedback: naive.has_feedback,
                naive_per_branch: naive.per_branch_effects.is_some(),
                soph_steps: soph.analysis_steps,
                soph_independent_pairs: soph.independent_pairs.len(),
                soph_false_deps: soph_missed,
                soph_feedback: soph.has_feedback,
                soph_per_branch: soph.per_branch_effects.is_some(),
                arrow_steps: arr.analysis_steps,
                arrow_independent_pairs: arr.independent_pairs.len(),
                arrow_false_deps: arrow_missed,
                arrow_feedback: arr.has_feedback,
                arrow_per_branch: arr.per_branch_effects.is_some(),
                true_independent_pairs: comp.true_independent_pairs,
                true_feedback: comp.true_has_feedback,
                true_per_branch: comp.true_has_per_branch_effects,
            }
        })
        .collect()
}

/// Count how many false dependencies the naive analysis creates
/// (let-bindings where the variable is not used in the body, plus seq nodes)
#[allow(dead_code)]
fn count_naive_false_deps(term: &Lam) -> usize {
    match term {
        Lam::Var(_) | Lam::Int(_) | Lam::Bool(_) | Lam::Unit | Lam::OpCall(_) => 0,
        Lam::Pair(a, b) => count_naive_false_deps(a) + count_naive_false_deps(b),
        Lam::Lam(_, body) => count_naive_false_deps(body),
        Lam::App(g, a) => count_naive_false_deps(g) + count_naive_false_deps(a),
        Lam::Let(x, e1, e2) => {
            let rest = count_naive_false_deps(e1) + count_naive_false_deps(e2);
            if !uses_var(e2, x) {
                1 + rest // this let creates a false dependency
            } else {
                rest
            }
        }
        Lam::If(c, t, e) => {
            count_naive_false_deps(c)
                + count_naive_false_deps(t)
                + count_naive_false_deps(e)
        }
        Lam::Prim(_, arg) => count_naive_false_deps(arg),
        Lam::Rec(_, _, body) => count_naive_false_deps(body),
        Lam::Seq(a, b) => {
            // Seq always creates a false dependency (naive thinks b depends on a)
            1 + count_naive_false_deps(a) + count_naive_false_deps(b)
        }
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // === Computation 1: Independent pair obscured by let-chain ===

    #[test]
    fn test_c1_naive_creates_false_dependency() {
        let comp = comp1_independent_pair_obscured();
        let naive = naive_lambda_analysis(&comp.lambda);
        // Naive analysis should find 0 independent pairs (it thinks everything
        // in a let-chain is dependent)
        assert_eq!(
            naive.independent_pairs.len(),
            0,
            "Naive: should NOT detect independence (let-chain obscures it)"
        );
        // The false dependency: naive MISSES 1 independent pair (f and g are
        // independent but the let-chain makes them appear dependent)
        let missed = comp.true_independent_pairs - naive.independent_pairs.len();
        assert_eq!(
            missed, 1,
            "Naive: should miss 1 independent pair (false dependency: g appears to depend on f)"
        );
    }

    #[test]
    fn test_c1_sophisticated_recovers_independence() {
        let comp = comp1_independent_pair_obscured();
        let soph = sophisticated_lambda_analysis(&comp.lambda);
        // Sophisticated analysis SHOULD detect independence
        // (via Pair analysis: free_vars(a) and free_vars(b) are disjoint)
        assert!(
            soph.independent_pairs.len() >= 1,
            "Sophisticated: should detect independence (data-flow shows a and b are independent)"
        );
        // And it should miss 0 independent pairs
        let missed = comp.true_independent_pairs - soph.independent_pairs.len();
        assert_eq!(
            missed, 0,
            "Sophisticated: should miss 0 independent pairs"
        );
    }

    #[test]
    fn test_c1_arrow_detects_independence_by_construction() {
        let comp = comp1_independent_pair_obscured();
        let arr = arrow_analysis(&comp.arrow);
        // Arrow: independence is a reading, not a computation
        assert_eq!(
            arr.independent_pairs.len(),
            1,
            "Arrow: should detect independence by construction (Fanout)"
        );
        assert_eq!(
            arr.false_dependencies, 0,
            "Arrow: no false dependencies (structure enforced)"
        );
    }

    #[test]
    fn test_c1_arrow_fewer_steps_than_sophisticated() {
        let comp = comp1_independent_pair_obscured();
        let soph = sophisticated_lambda_analysis(&comp.lambda);
        let arr = arrow_analysis(&comp.arrow);
        // Arrow should require fewer analysis steps (no free-var computation)
        assert!(
            arr.analysis_steps <= soph.analysis_steps,
            "Arrow: should require fewer steps ({}) than sophisticated lambda ({})",
            arr.analysis_steps,
            soph.analysis_steps
        );
    }

    // === Computation 2: Independent state reads ===

    #[test]
    fn test_c2_naive_false_dependency_on_reads() {
        let comp = comp2_independent_reads_obscured();
        let naive = naive_lambda_analysis(&comp.lambda);
        // Naive: misses independence of two Gets (let-chain obscures it)
        let missed = comp.true_independent_pairs - naive.independent_pairs.len();
        assert_eq!(
            missed, 1,
            "Naive: should miss 1 independent pair (false dependency between two Gets)"
        );
    }

    #[test]
    fn test_c2_sophisticated_recovers_read_independence() {
        let comp = comp2_independent_reads_obscured();
        let soph = sophisticated_lambda_analysis(&comp.lambda);
        assert!(
            soph.independent_pairs.len() >= 1,
            "Sophisticated: should detect two Gets are independent"
        );
    }

    #[test]
    fn test_c2_arrow_independence_by_construction() {
        let comp = comp2_independent_reads_obscured();
        let arr = arrow_analysis(&comp.arrow);
        assert_eq!(
            arr.independent_pairs.len(),
            1,
            "Arrow: Get &&& Get — independence explicit"
        );
    }

    // === Computation 3: Real dependency (both should get right) ===

    #[test]
    fn test_c3_both_detect_real_dependency() {
        let comp = comp3_real_dependency();
        let naive = naive_lambda_analysis(&comp.lambda);
        let soph = sophisticated_lambda_analysis(&comp.lambda);
        let arr = arrow_analysis(&comp.arrow);

        // All three should correctly detect NO independence
        assert_eq!(
            naive.independent_pairs.len(),
            0,
            "Naive: no independence (correct — real dependency)"
        );
        assert_eq!(
            soph.independent_pairs.len(),
            0,
            "Sophisticated: no independence (correct — real dependency)"
        );
        assert_eq!(
            arr.independent_pairs.len(),
            0,
            "Arrow: no independence (correct — Seq is real dependency)"
        );

        // No false dependencies
        assert_eq!(count_naive_false_deps(&comp.lambda), 0, "No false deps (real dependency)");
        assert_eq!(soph.false_dependencies, 0, "No false deps identified (none exist)");
        assert_eq!(arr.false_dependencies, 0, "Arrow: no false deps");
    }

    // === Computation 4: Mixed independent and dependent ===

    #[test]
    fn test_c4_naive_misses_h_independence() {
        let comp = comp4_mixed_independent_dependent();
        let naive = naive_lambda_analysis(&comp.lambda);
        // Naive: let-chain f→g→h, thinks h depends on g (FALSE)
        assert_eq!(
            naive.independent_pairs.len(),
            0,
            "Naive: should miss h's independence (obscured by let-chain)"
        );
        let missed = comp.true_independent_pairs - naive.independent_pairs.len();
        assert_eq!(
            missed, 1,
            "Naive: should miss 1 independent pair (h is independent of f→g)"
        );
    }

    #[test]
    fn test_c4_sophisticated_recovers_h_independence() {
        let comp = comp4_mixed_independent_dependent();
        let soph = sophisticated_lambda_analysis(&comp.lambda);
        // Sophisticated: sees c doesn't reference b, concludes h independent
        assert!(
            soph.independent_pairs.len() >= 1,
            "Sophisticated: should detect h is independent of f→g"
        );
    }

    #[test]
    fn test_c4_arrow_structure_explicit() {
        let comp = comp4_mixed_independent_dependent();
        let arr = arrow_analysis(&comp.arrow);
        // Arrow: (f >>> g) &&& h — h's independence is explicit
        assert_eq!(
            arr.independent_pairs.len(),
            1,
            "Arrow: (f>>>g) &&& h — h independence explicit"
        );
    }

    // === Computation 5: Feedback (recursion) ===

    #[test]
    fn test_c5_both_detect_feedback() {
        let comp = comp5_feedback_recursion();
        let naive = naive_lambda_analysis(&comp.lambda);
        let soph = sophisticated_lambda_analysis(&comp.lambda);
        let arr = arrow_analysis(&comp.arrow);

        // Both lambda analyses CAN detect Rec syntactically
        assert!(
            naive.has_feedback,
            "Naive: should detect feedback (Rec is visible)"
        );
        assert!(
            soph.has_feedback,
            "Sophisticated: should detect feedback (Rec is visible)"
        );
        // Arrow: loop is explicit
        assert!(
            arr.has_feedback,
            "Arrow: should detect feedback (Loop combinator)"
        );
    }

    // === Computation 6: Branching with per-branch effects ===

    #[test]
    fn test_c6_all_detect_per_branch_effects() {
        let comp = comp6_branching_effects();
        let naive = naive_lambda_analysis(&comp.lambda);
        let soph = sophisticated_lambda_analysis(&comp.lambda);
        let arr = arrow_analysis(&comp.arrow);

        // All three can see if-then-else / choice
        assert!(
            naive.per_branch_effects.is_some(),
            "Naive: should detect per-branch effects (if-then-else is visible)"
        );
        assert!(
            soph.per_branch_effects.is_some(),
            "Sophisticated: should detect per-branch effects"
        );
        assert!(
            arr.per_branch_effects.is_some(),
            "Arrow: should detect per-branch effects (Choice combinator)"
        );
    }

    #[test]
    fn test_c6_per_branch_effects_correct() {
        let comp = comp6_branching_effects();
        let arr = arrow_analysis(&comp.arrow);
        let (left, right) = arr.per_branch_effects.unwrap();
        // Left: Get >>> Throw → {Get, Throw}
        assert!(left.contains(Op::Get), "left branch has Get");
        assert!(left.contains(Op::Throw), "left branch has Throw");
        // Right: Put → {Put}
        assert!(right.contains(Op::Put), "right branch has Put");
        assert!(!right.contains(Op::Get), "right branch has NO Get");
    }

    // === Computation 7: Nested branching ===

    #[test]
    fn test_c7_nested_branching_detected() {
        let comp = comp7_nested_branching();
        let naive = naive_lambda_analysis(&comp.lambda);
        let arr = arrow_analysis(&comp.arrow);

        // Both can detect branching (if-then-else / choice is visible)
        assert!(
            naive.per_branch_effects.is_some(),
            "Naive: should detect top-level branching"
        );
        assert!(
            arr.per_branch_effects.is_some(),
            "Arrow: should detect branching (Choice)"
        );
    }

    // === Computation 8: False dependency (AI pattern) ===

    #[test]
    fn test_c8_naive_false_dependency_ai_pattern() {
        let comp = comp8_false_dependency_ai_pattern();
        let false_deps = count_naive_false_deps(&comp.lambda);
        assert!(
            false_deps > 0,
            "Naive: should create false dependency (AI pattern: compute, discard, continue)"
        );
    }

    #[test]
    fn test_c8_sophisticated_recovers_independence() {
        let comp = comp8_false_dependency_ai_pattern();
        let soph = sophisticated_lambda_analysis(&comp.lambda);
        // Sophisticated: sees a is unused in the continuation, concludes independent
        assert!(
            soph.false_dependencies >= 1,
            "Sophisticated: should identify false dependency"
        );
    }

    #[test]
    fn test_c8_arrow_no_false_dependency() {
        let comp = comp8_false_dependency_ai_pattern();
        let arr = arrow_analysis(&comp.arrow);
        assert_eq!(
            arr.false_dependencies, 0,
            "Arrow: no false deps (Fanout enforces independence)"
        );
        assert_eq!(
            arr.independent_pairs.len(),
            1,
            "Arrow: independence explicit"
        );
    }

    // === Aggregate: arrow never has false dependencies ===

    #[test]
    fn test_arrow_never_has_false_dependencies() {
        for comp in all_computations() {
            let arr = arrow_analysis(&comp.arrow);
            assert_eq!(
                arr.false_dependencies, 0,
                "Arrow {} should never have false dependencies",
                comp.name
            );
        }
    }

    // === Aggregate: naive misses independence on obscured computations ===

    #[test]
    fn test_naive_misses_independence_on_obscured() {
        let mut total_missed = 0;
        for comp in all_computations() {
            let naive = naive_lambda_analysis(&comp.lambda);
            let missed = comp.true_independent_pairs - naive.independent_pairs.len();
            total_missed += missed;
        }
        // At least 4 missed independent pairs across the obscured computations
        // (C1, C2, C4, C8 each have 1 independent pair that naive misses)
        assert!(
            total_missed >= 4,
            "Naive analysis should miss at least 4 independent pairs across computations, got {}",
            total_missed
        );
    }

    // === Aggregate: sophisticated requires more steps than arrow ===

    #[test]
    fn test_sophisticated_requires_more_steps_than_arrow() {
        let mut total_soph = 0;
        let mut total_arrow = 0;
        for comp in all_computations() {
            let soph = sophisticated_lambda_analysis(&comp.lambda);
            let arr = arrow_analysis(&comp.arrow);
            total_soph += soph.analysis_steps;
            total_arrow += arr.analysis_steps;
        }
        // Sophisticated lambda analysis should require at least as many steps
        // as arrow analysis (due to free-variable computation)
        assert!(
            total_soph >= total_arrow,
            "Sophisticated lambda ({}) should require >= steps than arrow ({})",
            total_soph,
            total_arrow
        );
    }

    // === Aggregate: arrow independence matches ground truth ===

    #[test]
    fn test_arrow_independence_matches_ground_truth() {
        for comp in all_computations() {
            let arr = arrow_analysis(&comp.arrow);
            assert_eq!(
                arr.independent_pairs.len(),
                comp.true_independent_pairs,
                "Arrow {}: independence count {} should match ground truth {}",
                comp.name,
                arr.independent_pairs.len(),
                comp.true_independent_pairs
            );
        }
    }

    // === Aggregate: sophisticated independence matches ground truth ===

    #[test]
    fn test_sophisticated_independence_matches_ground_truth() {
        for comp in all_computations() {
            let soph = sophisticated_lambda_analysis(&comp.lambda);
            assert_eq!(
                soph.independent_pairs.len(),
                comp.true_independent_pairs,
                "Sophisticated {}: independence count {} should match ground truth {}",
                comp.name,
                soph.independent_pairs.len(),
                comp.true_independent_pairs
            );
        }
    }

    // === Aggregate: naive independence does NOT match ground truth (the key finding) ===

    #[test]
    fn test_naive_independence_does_not_match_ground_truth() {
        let mut mismatches = 0;
        for comp in all_computations() {
            let naive = naive_lambda_analysis(&comp.lambda);
            if naive.independent_pairs.len() != comp.true_independent_pairs {
                mismatches += 1;
            }
        }
        // Naive analysis should mismatch on at least 3 computations
        // (the ones with obscured independence: C1, C2, C4, C8)
        assert!(
            mismatches >= 3,
            "Naive analysis should mismatch ground truth on at least 3 computations, got {}",
            mismatches
        );
    }

    // === Free variable analysis ===

    #[test]
    fn test_free_vars_basic() {
        let term = Lam::Var("x".into());
        let fv = free_vars(&term);
        assert!(fv.contains("x"));

        let term = Lam::Lam("x".into(), Box::new(Lam::Var("x".into())));
        let fv = free_vars(&term);
        assert!(!fv.contains("x"), "x is bound by lambda");

        let term = Lam::Let(
            "a".into(),
            Box::new(Lam::Var("x".into())),
            Box::new(Lam::Var("a".into())),
        );
        let fv = free_vars(&term);
        assert!(fv.contains("x"), "x is free in let");
        assert!(!fv.contains("a"), "a is bound by let");
    }

    #[test]
    fn test_uses_var() {
        let body = Lam::Pair(
            Box::new(Lam::Var("a".into())),
            Box::new(Lam::Var("b".into())),
        );
        assert!(uses_var(&body, "a"));
        assert!(uses_var(&body, "b"));
        assert!(!uses_var(&body, "c"));
    }

    // === The key honest finding: sophisticated lambda CAN recover structure ===

    #[test]
    fn test_sophisticated_lambda_recovers_structure_on_all_computations() {
        // This is the HONEST counter-finding: with data-flow analysis,
        // lambda CAN recover the same structural facts as arrows.
        // The gap is about ANALYSIS EFFORT, not impossibility.
        for comp in all_computations() {
            let soph = sophisticated_lambda_analysis(&comp.lambda);
            // Independence
            assert_eq!(
                soph.independent_pairs.len(),
                comp.true_independent_pairs,
                "Sophisticated {}: independence should match ground truth",
                comp.name
            );
            // Feedback
            assert_eq!(
                soph.has_feedback,
                comp.true_has_feedback,
                "Sophisticated {}: feedback should match ground truth",
                comp.name
            );
        }
    }

    // === Effect inference works on all representations ===

    #[test]
    fn test_effect_inference_all_representations() {
        for comp in all_computations() {
            let naive = naive_lambda_analysis(&comp.lambda);
            let soph = sophisticated_lambda_analysis(&comp.lambda);
            let arr = arrow_analysis(&comp.arrow);
            // All three should infer the same effect set
            assert_eq!(
                naive.effects, soph.effects,
                "{}: naive and sophisticated effects should match",
                comp.name
            );
            // Arrow effects should match too (for computations with effects)
            assert_eq!(
                naive.effects, arr.effects,
                "{}: naive and arrow effects should match",
                comp.name
            );
        }
    }
}

// ============================================================================
// Demo
// ============================================================================

fn main() {
    println!("============================================================");
    println!("AI-Generated Code Structure Experiment");
    println!("============================================================");
    println!();
    println!("Testing whether arrow representations are more robust to");
    println!("obscured (AI-generated) code than lambda representations");
    println!("for structural analysis.");
    println!();
    println!("Three analysis levels:");
    println!("  1. NAIVE lambda    — syntactic: let-chain = dependency");
    println!("  2. SOPHISTICATED   — data-flow: tracks variable usage");
    println!("  3. ARROW           — by construction: reads combinators");
    println!();

    let rows = run_comparison();

    // Print comparison table
    println!("--- Per-Computation Comparison ---");
    println!();
    for row in &rows {
        println!("{}", row.name);
        println!("  Ground truth: independent_pairs={}, feedback={}, per_branch={}",
            row.true_independent_pairs, row.true_feedback, row.true_per_branch);
        println!();
        println!("  {:<14} | steps | indep | false_deps | feedback | per_branch", "Analysis");
        println!("  {:-<14}-+-------+-------+------------+----------+----------", "");
        println!("  {:<14} | {:>5} | {:>5} | {:>10} | {:>8} | {:>9}",
            "Naive λ", row.naive_steps, row.naive_independent_pairs,
            row.naive_false_deps, row.naive_feedback, row.naive_per_branch);
        println!("  {:<14} | {:>5} | {:>5} | {:>10} | {:>8} | {:>9}",
            "Sophisticated", row.soph_steps, row.soph_independent_pairs,
            row.soph_false_deps, row.soph_feedback, row.soph_per_branch);
        println!("  {:<14} | {:>5} | {:>5} | {:>10} | {:>8} | {:>9}",
            "Arrow", row.arrow_steps, row.arrow_independent_pairs,
            row.arrow_false_deps, row.arrow_feedback, row.arrow_per_branch);
        println!();
    }

    // Aggregate
    let total_naive_steps: usize = rows.iter().map(|r| r.naive_steps).sum();
    let total_soph_steps: usize = rows.iter().map(|r| r.soph_steps).sum();
    let total_arrow_steps: usize = rows.iter().map(|r| r.arrow_steps).sum();
    let total_naive_false: usize = rows.iter().map(|r| r.naive_false_deps).sum();
    let total_soph_false: usize = rows.iter().map(|r| r.soph_false_deps).sum();
    let total_arrow_false: usize = rows.iter().map(|r| r.arrow_false_deps).sum();

    // Count independence detection accuracy
    let mut naive_indep_correct = 0;
    let mut soph_indep_correct = 0;
    let mut arrow_indep_correct = 0;
    for row in &rows {
        if row.naive_independent_pairs == row.true_independent_pairs {
            naive_indep_correct += 1;
        }
        if row.soph_independent_pairs == row.true_independent_pairs {
            soph_indep_correct += 1;
        }
        if row.arrow_independent_pairs == row.true_independent_pairs {
            arrow_indep_correct += 1;
        }
    }
    let total = rows.len();

    println!("--- Aggregate Results ---");
    println!();
    println!("  Metric                    | Naive λ  | Sophisticated | Arrow");
    println!("  {:-<26}-+----------+---------------+-------", "");
    println!("  Total analysis steps      | {:>8} | {:>13} | {:>6}", total_naive_steps, total_soph_steps, total_arrow_steps);
    println!("  Total false dependencies  | {:>8} | {:>13} | {:>6}", total_naive_false, total_soph_false, total_arrow_false);
    println!("  Independence accuracy     | {:>2}/{:<5} | {:>5}/{:<7} | {:>2}/{:<3}", naive_indep_correct, total, soph_indep_correct, total, arrow_indep_correct, total);
    println!();

    // Key findings
    println!("--- Key Findings ---");
    println!();
    println!("1. NAIVE lambda analysis creates {} false dependencies across", total_naive_false);
    println!("   {} computations. It detects independence correctly on only", total);
    println!("   {}/{} computations (misses obscured independence).", naive_indep_correct, total);
    println!();
    println!("2. SOPHISTICATED lambda analysis (with data-flow) recovers");
    println!("   independence correctly on {}/{} computations. It identifies", soph_indep_correct, total);
    println!("   {} false dependencies that naive analysis would create.", total_soph_false);
    println!("   But it requires {} analysis steps (vs {} for arrow).", total_soph_steps, total_arrow_steps);
    println!();
    println!("3. ARROW analysis detects independence correctly on {}/{}", arrow_indep_correct, total);
    println!("   computations, with ZERO false dependencies, in {} steps.", total_arrow_steps);
    println!();
    println!("4. The gap is about ANALYSIS EFFORT and ROBUSTNESS, not");
    println!("   impossibility. Sophisticated lambda CAN recover structure,");
    println!("   but requires data-flow analysis. Arrows give it by construction.");
    println!();
    println!("5. For AI-generated code (which tends to be obscured), the");
    println!("   naive analysis fails. The sophisticated analysis works but");
    println!("   requires more effort. The arrow analysis works trivially");
    println!("   because structure is enforced by the representation.");
    println!();

    // Honest assessment
    println!("--- Honest Assessment ---");
    println!();
    if soph_indep_correct == total && arrow_indep_correct == total {
        println!("  The sophisticated lambda analysis recovers ALL structural facts.");
        println!("  This confirms the thesis: the advantage is enforcement vs.");
        println!("  permission, not impossibility. Lambda CAN recover structure");
        println!("  with sufficient analysis. Arrows enforce it by construction.");
        println!();
        println!("  The practical gap: arrow analysis requires {} steps;", total_arrow_steps);
        println!("  sophisticated lambda requires {} steps ({}x more).", total_soph_steps, total_soph_steps / total_arrow_steps.max(1));
        println!("  Naive lambda requires {} steps but gets {} facts WRONG.", total_naive_steps, total - naive_indep_correct);
    }
    println!();
    println!("  This is an ARCHITECTURAL argument, not a theorem. The evidence");
    println!("  supports it: arrows enforce structural explicitness, making");
    println!("  analysis robust to obscured (AI-generated) code. Lambda permits");
    println!("  obscuration, requiring more analysis to recover the same facts.");
}
