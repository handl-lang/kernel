// Speculative Compilation of Transparent ArrowApply Trees
//
// Implements and benchmarks the "speculative compilation" idea proposed in
// RESULTS_CHALLENGE11.md: pre-compile every reachable execution path of an
// explicit (freer-style) ArrowApply computation tree into a flat execution
// chunk, then dispatch at runtime via a pre-allocated table — zero allocation,
// no graph traversal.
//
// Three execution modes are compared:
//   1. Tree-walking interpreter (traverses ExplicitComp at runtime)
//   2. Speculative dispatch (pre-compiled chunk dispatch table)
//   3. Baseline (hand-written flat function — the theoretical optimum)
//
// Run with:  cargo run --bin speculative_compilation --release

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Instant;

// ============================================================================
// Allocation counter (global allocator wrapper)
// ============================================================================

static ALLOC_COUNT: AtomicU64 = AtomicU64::new(0);
static ALLOC_BYTES: AtomicU64 = AtomicU64::new(0);

struct CountingAlloc;

unsafe impl GlobalAlloc for CountingAlloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        ALLOC_COUNT.fetch_add(1, Ordering::Relaxed);
        ALLOC_BYTES.fetch_add(layout.size() as u64, Ordering::Relaxed);
        System.alloc(layout)
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        System.dealloc(ptr, layout);
    }
}

#[global_allocator]
static GLOBAL: CountingAlloc = CountingAlloc;

fn alloc_count() -> u64 {
    ALLOC_COUNT.load(Ordering::Relaxed)
}
fn alloc_bytes() -> u64 {
    ALLOC_BYTES.load(Ordering::Relaxed)
}
fn reset_alloc_counters() {
    ALLOC_COUNT.store(0, Ordering::Relaxed);
    ALLOC_BYTES.store(0, Ordering::Relaxed);
}

// ============================================================================
// Boxed Value (used by the tree-walking interpreter)
// ============================================================================
//
// This mirrors the Value type from arrow_apply_tests.rs. The tree walker
// allocates Boxes for Pair/Left/Right/Arrow, which is the realistic overhead
// of the inspectable tree representation.

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Int(i32),
    Unit,
    Pair(Box<Value>, Box<Value>),
    Left(Box<Value>),
    Right(Box<Value>),
    Arrow(Box<ExplicitComp>),
}

// ============================================================================
// ExplicitComp — the inspectable computation tree
// ============================================================================
//
// Extended from the Challenge #11 representation with concrete pure-op leaves
// (AddConst, MulConst, SubConst) so we can build real benchmark programs
// without storing opaque closures. The structural nodes (Seq, Choice, OpNode,
// Apply, SelectArrow) are unchanged in spirit.
//
// SelectArrow is the ArrowApply case with a *finite, statically-known* set of
// candidate arrows. This is the case where speculative compilation applies:
// Stage 0 can see every possible arrow and pre-compile each one.

#[derive(Debug, Clone, PartialEq)]
pub enum ExplicitComp {
    /// Produce a constant value (arr (const v))
    Pure(Value),
    /// Identity arrow
    Ident,
    /// Sequential composition
    Seq(Box<ExplicitComp>, Box<ExplicitComp>),
    /// Choice: Left v -> f, Right v -> g
    Choice(Box<ExplicitComp>, Box<ExplicitComp>),
    /// Operation node (Get / Put) followed by continuation
    OpNode(Op, Box<ExplicitComp>),
    /// ArrowApply: input is (Arrow, value) — apply the embedded arrow.
    /// The arrow is only known at runtime (from the input value).
    Apply,
    /// ArrowApply with a finite, statically-known candidate set.
    /// Input is Pair(Int(id), value); run candidates[id] on value.
    /// This is the realistic speculative-compilation target.
    SelectArrow(Vec<ExplicitComp>),
    // Pure integer operations (leaf nodes — opaque at the leaf, like `arr`)
    AddConst(i32),
    MulConst(i32),
    SubConst(i32),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Op {
    Get,
    Put,
}

// ============================================================================
// Tree-walking interpreter (Mode 1)
// ============================================================================
//
// This is the "current approach": traverse the ExplicitComp tree at runtime.
// Every Seq/Choice is a recursive call; every Pair/Left/Right/Arrow value is
// a heap allocation.

pub fn run_tree(
    comp: &ExplicitComp,
    input: Value,
    state: &mut Value,
) -> Result<Value, String> {
    match comp {
        ExplicitComp::Pure(v) => Ok(v.clone()),
        ExplicitComp::Ident => Ok(input),
        ExplicitComp::Seq(f, g) => {
            let v1 = run_tree(f, input, state)?;
            run_tree(g, v1, state)
        }
        ExplicitComp::Choice(f, g) => match input {
            Value::Left(v) => run_tree(f, *v, state),
            Value::Right(v) => run_tree(g, *v, state),
            _ => Err("choice requires Left/Right".into()),
        },
        ExplicitComp::OpNode(op, k) => match op {
            Op::Get => {
                let s = state.clone();
                run_tree(k, s, state)
            }
            Op::Put => {
                *state = input.clone();
                run_tree(k, Value::Unit, state)
            }
        },
        ExplicitComp::Apply => match input {
            Value::Pair(arrow_box, value_box) => match arrow_box.as_ref() {
                Value::Arrow(comp_box) => run_tree(comp_box, value_box.as_ref().clone(), state),
                _ => Err("Apply: first component must be Arrow".into()),
            },
            _ => Err("Apply: input must be a pair".into()),
        },
        ExplicitComp::SelectArrow(candidates) => match input {
            Value::Pair(id_box, value_box) => match id_box.as_ref() {
                Value::Int(id) => {
                    let idx = *id as usize;
                    if idx >= candidates.len() {
                        return Err("SelectArrow: id out of range".into());
                    }
                    run_tree(&candidates[idx], value_box.as_ref().clone(), state)
                }
                _ => Err("SelectArrow: id must be Int".into()),
            },
            _ => Err("SelectArrow: input must be a pair".into()),
        },
        ExplicitComp::AddConst(c) => match input {
            Value::Int(n) => Ok(Value::Int(n + c)),
            _ => Err("AddConst: input must be Int".into()),
        },
        ExplicitComp::MulConst(c) => match input {
            Value::Int(n) => Ok(Value::Int(n * c)),
            _ => Err("MulConst: input must be Int".into()),
        },
        ExplicitComp::SubConst(c) => match input {
            Value::Int(n) => Ok(Value::Int(n - c)),
            _ => Err("SubConst: input must be Int".into()),
        },
    }
}

// ============================================================================
// Flat execution chunks (Mode 2: speculative dispatch)
// ============================================================================
//
// A flat chunk is a straight-line sequence of operations with NO branching.
// Branching is encoded in the chunk *terminator*, which either halts, branches
// on a tag (0 = Left, nonzero = Right), or dispatches an ArrowApply by arrow ID.
//
// The flat VM operates on raw i32 values on a pre-allocated stack. No Boxes,
// no Value enum, no heap allocation during execution.
//
// Stack convention for branching:
//   The payload is at the bottom. Tags are pushed on top, innermost-first,
//   outermost-last. A Branch terminator pops the top tag and dispatches,
//   leaving the payload (and any remaining inner tags) on the stack.
//
//   Example for 4-way (2 nested Choices), input Left(Left(x)):
//     stack = [x, 0, 0]   (payload x, inner tag 0=Left, outer tag 0=Left)
//     outer Branch pops 0 -> left chunk
//     inner Branch pops 0 -> left-left chunk
//     left-left chunk: AddConst(10) on x, Halt

#[derive(Debug, Clone, Copy)]
pub enum FlatOp {
    /// Push a constant i32 onto the stack
    Const(i32),
    /// top = top + c
    AddConst(i32),
    /// top = top * c
    MulConst(i32),
    /// top = top - c
    SubConst(i32),
    /// Push current state onto the stack
    GetState,
    /// Pop top -> state register
    PutState,
    /// Duplicate the top of stack
    Dup,
    /// Pop the top of stack
    Pop,
    /// Pop two values, push their sum
    Add,
    /// Pop two values, push their product
    Mul,
    /// No-op (pass through)
    Nop,
}

#[derive(Debug, Clone)]
pub enum ChunkTerm {
    /// End of this path — return top of stack
    Halt,
    /// Pop top (tag); if == 0 jump to `left` chunk, else jump to `right` chunk.
    /// (Encodes Choice: tag 0 = Left, tag 1 = Right.)
    Branch { left: usize, right: usize },
    /// ArrowApply dispatch: pop `value`, pop `id`, push `value`, jump to
    /// `targets[id]`. The candidate arrows are pre-compiled into chunks.
    DispatchApply { targets: Vec<usize> },
}

#[derive(Debug, Clone)]
pub struct Chunk {
    pub ops: Vec<FlatOp>,
    pub term: ChunkTerm,
}

#[derive(Debug, Clone)]
pub struct DispatchTable {
    pub chunks: Vec<Chunk>,
}

// ============================================================================
// Stage 0: analyze(tree) -> DispatchTable
// ============================================================================
//
// Walk the ExplicitComp tree, enumerate every reachable execution path, and
// compile each into a flat chunk. Choice nodes create branch terminators and
// spawn two new chunks. SelectArrow nodes create a DispatchApply terminator
// and spawn one chunk per candidate arrow.

pub struct Analyzer {
    chunks: Vec<Chunk>,
}

impl Analyzer {
    pub fn new() -> Self {
        Analyzer { chunks: Vec::new() }
    }

    /// Allocate a new empty chunk and return its index.
    fn new_chunk(&mut self) -> usize {
        let idx = self.chunks.len();
        self.chunks.push(Chunk {
            ops: Vec::new(),
            term: ChunkTerm::Halt,
        });
        idx
    }

    /// Compile `node` into chunk `chunk_idx`, appending ops and creating
    /// new chunks as needed for branches.
    fn compile_into(&mut self, node: &ExplicitComp, chunk_idx: usize) {
        let chunk = &mut self.chunks[chunk_idx];
        match node {
            ExplicitComp::Pure(Value::Int(n)) => chunk.ops.push(FlatOp::Const(*n)),
            ExplicitComp::Pure(Value::Unit) => chunk.ops.push(FlatOp::Const(0)),
            ExplicitComp::Pure(Value::Left(v)) => {
                if let Value::Int(n) = v.as_ref() {
                    chunk.ops.push(FlatOp::Const(-n.abs() - 1));
                }
            }
            ExplicitComp::Pure(Value::Right(v)) => {
                if let Value::Int(n) = v.as_ref() {
                    chunk.ops.push(FlatOp::Const(n.abs()));
                }
            }
            ExplicitComp::Pure(_) => chunk.ops.push(FlatOp::Const(0)),
            ExplicitComp::Ident => chunk.ops.push(FlatOp::Nop),
            ExplicitComp::AddConst(c) => chunk.ops.push(FlatOp::AddConst(*c)),
            ExplicitComp::MulConst(c) => chunk.ops.push(FlatOp::MulConst(*c)),
            ExplicitComp::SubConst(c) => chunk.ops.push(FlatOp::SubConst(*c)),
            ExplicitComp::OpNode(Op::Get, k) => {
                chunk.ops.push(FlatOp::GetState);
                self.compile_into(k, chunk_idx);
            }
            ExplicitComp::OpNode(Op::Put, k) => {
                chunk.ops.push(FlatOp::PutState);
                self.compile_into(k, chunk_idx);
            }
            ExplicitComp::Seq(f, g) => {
                self.compile_into(f, chunk_idx);
                self.compile_into(g, chunk_idx);
            }
            ExplicitComp::Choice(f, g) => {
                let left_idx = self.new_chunk();
                let right_idx = self.new_chunk();
                let chunk = &mut self.chunks[chunk_idx];
                chunk.term = ChunkTerm::Branch {
                    left: left_idx,
                    right: right_idx,
                };
                self.compile_into(f, left_idx);
                self.compile_into(g, right_idx);
            }
            ExplicitComp::SelectArrow(candidates) => {
                let targets: Vec<usize> = candidates
                    .iter()
                    .map(|_| self.new_chunk())
                    .collect();
                for (cand, &tgt) in candidates.iter().zip(targets.iter()) {
                    self.compile_into(cand, tgt);
                }
                let chunk = &mut self.chunks[chunk_idx];
                chunk.term = ChunkTerm::DispatchApply { targets };
            }
            ExplicitComp::Apply => {
                // Truly dynamic Apply (arrow not known at compile time).
                // We cannot pre-compile this — it's the unbounded case.
                // In a real system this would fall back to the tree walker.
                chunk.ops.push(FlatOp::Nop);
            }
        }
    }

    pub fn analyze(tree: &ExplicitComp) -> DispatchTable {
        let mut analyzer = Analyzer::new();
        let root = analyzer.new_chunk();
        analyzer.compile_into(tree, root);
        DispatchTable {
            chunks: analyzer.chunks,
        }
    }
}

// ============================================================================
// Runtime: flat VM execution (Mode 2)
// ============================================================================
//
// Executes a DispatchTable with zero heap allocation. The stack is a
// pre-allocated Vec<i32> that is reused across invocations.

/// Execute starting from chunk 0 with a pre-populated stack.
#[inline(never)]
pub fn run_flat_from(
    table: &DispatchTable,
    stack: &mut Vec<i32>,
    state: &mut i32,
) -> i32 {
    let mut chunk_idx: usize = 0;
    loop {
        let chunk = &table.chunks[chunk_idx];
        exec_ops(&chunk.ops, stack, state);
        match &chunk.term {
            ChunkTerm::Halt => return stack.pop().unwrap(),
            ChunkTerm::Branch { left, right } => {
                let tag = stack.pop().unwrap();
                chunk_idx = if tag == 0 { *left } else { *right };
            }
            ChunkTerm::DispatchApply { targets } => {
                let val = stack.pop().unwrap();
                let id = stack.pop().unwrap();
                stack.push(val);
                chunk_idx = targets[id as usize];
            }
        }
    }
}

/// Convenience wrapper: clear stack, push single input, execute.
#[inline(never)]
pub fn run_flat(
    table: &DispatchTable,
    input: i32,
    state: &mut i32,
    stack: &mut Vec<i32>,
) -> i32 {
    stack.clear();
    stack.push(input);
    run_flat_from(table, stack, state)
}

#[inline(always)]
fn exec_ops(ops: &[FlatOp], stack: &mut Vec<i32>, state: &mut i32) {
    for op in ops {
        match *op {
            FlatOp::Const(c) => stack.push(c),
            FlatOp::AddConst(c) => {
                let v = *stack.last().unwrap();
                *stack.last_mut().unwrap() = v + c;
            }
            FlatOp::MulConst(c) => {
                let v = *stack.last().unwrap();
                *stack.last_mut().unwrap() = v * c;
            }
            FlatOp::SubConst(c) => {
                let v = *stack.last().unwrap();
                *stack.last_mut().unwrap() = v - c;
            }
            FlatOp::GetState => stack.push(*state),
            FlatOp::PutState => {
                *state = stack.pop().unwrap();
            }
            FlatOp::Dup => {
                let v = *stack.last().unwrap();
                stack.push(v);
            }
            FlatOp::Pop => {
                stack.pop();
            }
            FlatOp::Add => {
                let b = stack.pop().unwrap();
                let a = stack.pop().unwrap();
                stack.push(a + b);
            }
            FlatOp::Mul => {
                let b = stack.pop().unwrap();
                let a = stack.pop().unwrap();
                stack.push(a * b);
            }
            FlatOp::Nop => {}
        }
    }
}

// ============================================================================
// Baseline functions (Mode 3: hand-written, theoretical optimum)
// ============================================================================

#[inline(never)]
pub fn baseline_no_branch(x: i32, _tag: i32, state: &mut i32) -> i32 {
    let _ = state;
    (x + 1) * 2
}

#[inline(never)]
pub fn baseline_2way(x: i32, tag: i32, state: &mut i32) -> i32 {
    let _ = state;
    if tag == 0 {
        x + 1
    } else {
        x * 2
    }
}

#[inline(never)]
pub fn baseline_4way(x: i32, tag_outer: i32, tag_inner: i32, state: &mut i32) -> i32 {
    let _ = state;
    if tag_outer == 0 {
        if tag_inner == 0 {
            x + 10
        } else {
            x + 1
        }
    } else {
        if tag_inner == 0 {
            x * 10
        } else {
            x * 2
        }
    }
}

#[inline(never)]
pub fn baseline_8way(
    x: i32,
    t1: i32,
    t2: i32,
    t3: i32,
    state: &mut i32,
) -> i32 {
    let _ = state;
    if t1 == 0 {
        if t2 == 0 {
            if t3 == 0 {
                x + 1000
            } else {
                x + 100
            }
        } else {
            if t3 == 0 {
                x + 10
            } else {
                x + 1
            }
        }
    } else {
        if t2 == 0 {
            if t3 == 0 {
                x * 1000
            } else {
                x * 100
            }
        } else {
            if t3 == 0 {
                x * 10
            } else {
                x * 2
            }
        }
    }
}

#[inline(never)]
pub fn baseline_dynamic_apply(id: i32, val: i32, state: &mut i32) -> i32 {
    let _ = state;
    match id {
        0 => val + 1,
        1 => val * 2,
        2 => val - 1,
        3 => val * 3,
        _ => val,
    }
}

// ============================================================================
// Benchmark program builders
// ============================================================================

fn prog_no_branch() -> ExplicitComp {
    ExplicitComp::Seq(
        Box::new(ExplicitComp::AddConst(1)),
        Box::new(ExplicitComp::MulConst(2)),
    )
}

fn prog_2way() -> ExplicitComp {
    ExplicitComp::Choice(
        Box::new(ExplicitComp::AddConst(1)),
        Box::new(ExplicitComp::MulConst(2)),
    )
}

fn prog_4way() -> ExplicitComp {
    ExplicitComp::Choice(
        Box::new(ExplicitComp::Choice(
            Box::new(ExplicitComp::AddConst(10)),
            Box::new(ExplicitComp::AddConst(1)),
        )),
        Box::new(ExplicitComp::Choice(
            Box::new(ExplicitComp::MulConst(10)),
            Box::new(ExplicitComp::MulConst(2)),
        )),
    )
}

fn prog_8way() -> ExplicitComp {
    ExplicitComp::Choice(
        Box::new(ExplicitComp::Choice(
            Box::new(ExplicitComp::Choice(
                Box::new(ExplicitComp::AddConst(1000)),
                Box::new(ExplicitComp::AddConst(100)),
            )),
            Box::new(ExplicitComp::Choice(
                Box::new(ExplicitComp::AddConst(10)),
                Box::new(ExplicitComp::AddConst(1)),
            )),
        )),
        Box::new(ExplicitComp::Choice(
            Box::new(ExplicitComp::Choice(
                Box::new(ExplicitComp::MulConst(1000)),
                Box::new(ExplicitComp::MulConst(100)),
            )),
            Box::new(ExplicitComp::Choice(
                Box::new(ExplicitComp::MulConst(10)),
                Box::new(ExplicitComp::MulConst(2)),
            )),
        )),
    )
}

fn prog_dynamic_apply() -> ExplicitComp {
    ExplicitComp::SelectArrow(vec![
        ExplicitComp::AddConst(1),
        ExplicitComp::MulConst(2),
        ExplicitComp::SubConst(1),
        ExplicitComp::MulConst(3),
    ])
}

// ============================================================================
// Utility: tree / chunk metrics
// ============================================================================

fn count_tree_nodes(comp: &ExplicitComp) -> usize {
    1 + match comp {
        ExplicitComp::Seq(f, g) | ExplicitComp::Choice(f, g) => {
            count_tree_nodes(f) + count_tree_nodes(g)
        }
        ExplicitComp::OpNode(_, k) => count_tree_nodes(k),
        ExplicitComp::SelectArrow(cands) => {
            cands.iter().map(count_tree_nodes).sum()
        }
        _ => 0,
    }
}

fn count_chunk_ops(table: &DispatchTable) -> usize {
    table.chunks.iter().map(|c| c.ops.len() + 1).sum()
}

// ============================================================================
// Input encoding helpers
// ============================================================================

/// Encode a 2-way choice input for the tree walker: tag 0 = Left, 1 = Right.
fn make_choice_input(payload: i32, tag: i32) -> Value {
    if tag == 0 {
        Value::Left(Box::new(Value::Int(payload)))
    } else {
        Value::Right(Box::new(Value::Int(payload)))
    }
}

/// Encode a 4-way choice input: Left(Left(x)) etc.
fn make_choice_input_4(payload: i32, t_outer: i32, t_inner: i32) -> Value {
    let inner = if t_inner == 0 {
        Value::Left(Box::new(Value::Int(payload)))
    } else {
        Value::Right(Box::new(Value::Int(payload)))
    };
    if t_outer == 0 {
        Value::Left(Box::new(inner))
    } else {
        Value::Right(Box::new(inner))
    }
}

/// Encode an 8-way choice input.
fn make_choice_input_8(payload: i32, t1: i32, t2: i32, t3: i32) -> Value {
    let inner2 = if t3 == 0 {
        Value::Left(Box::new(Value::Int(payload)))
    } else {
        Value::Right(Box::new(Value::Int(payload)))
    };
    let inner1 = if t2 == 0 {
        Value::Left(Box::new(inner2))
    } else {
        Value::Right(Box::new(inner2))
    };
    if t1 == 0 {
        Value::Left(Box::new(inner1))
    } else {
        Value::Right(Box::new(inner1))
    }
}

fn make_apply_input(id: i32, val: i32) -> Value {
    Value::Pair(Box::new(Value::Int(id)), Box::new(Value::Int(val)))
}

// ============================================================================
// Benchmark harness
// ============================================================================

const ITERS: u64 = 5_000_000;

struct DetailedResult {
    name: String,
    tree_ns_per_call: f64,
    flat_ns_per_call: f64,
    base_ns_per_call: f64,
    tree_allocs_per_call: f64,
    flat_allocs_per_call: f64,
    chunk_count: usize,
    tree_node_count: usize,
    setup_ns: u64,
}

fn run_detailed_benchmark(name: &str) -> DetailedResult {
    match name {
        "no_branch" => run_bench_no_branch(),
        "2way" => run_bench_2way(),
        "4way" => run_bench_4way(),
        "8way" => run_bench_8way(),
        "dynamic_apply" => run_bench_dynamic_apply(),
        _ => unreachable!(),
    }
}

fn run_bench_no_branch() -> DetailedResult {
    let tree = prog_no_branch();
    let tree_nodes = count_tree_nodes(&tree);

    let t0 = Instant::now();
    let table = Analyzer::analyze(&tree);
    let setup_ns = t0.elapsed().as_nanos() as u64;
    let chunk_count = table.chunks.len();

    let inputs: Vec<i32> = (0..ITERS as i32).map(|i| i % 1000).collect();

    // Tree-walking
    let mut state = Value::Int(0);
    let mut acc_tree: i64 = 0;
    let t0 = Instant::now();
    reset_alloc_counters();
    for &x in &inputs {
        let r = run_tree(&tree, Value::Int(x), &mut state).unwrap();
        acc_tree += if let Value::Int(n) = r { n as i64 } else { 0 };
    }
    let tree_exec_ns = t0.elapsed().as_nanos() as u64;
    let tree_allocs = alloc_count();

    // Flat dispatch
    let mut state_flat: i32 = 0;
    let mut stack: Vec<i32> = Vec::with_capacity(256);
    let mut acc_flat: i64 = 0;
    let t0 = Instant::now();
    reset_alloc_counters();
    for &x in &inputs {
        let r = run_flat(&table, x, &mut state_flat, &mut stack);
        acc_flat += r as i64;
    }
    let flat_exec_ns = t0.elapsed().as_nanos() as u64;
    let flat_allocs = alloc_count();

    // Baseline
    let mut state_base: i32 = 0;
    let mut acc_base: i64 = 0;
    let t0 = Instant::now();
    for &x in &inputs {
        let r = baseline_no_branch(x, 0, &mut state_base);
        acc_base += r as i64;
    }
    let base_exec_ns = t0.elapsed().as_nanos() as u64;

    assert_eq!(acc_tree, acc_flat, "no_branch: tree != flat");
    assert_eq!(acc_flat, acc_base, "no_branch: flat != baseline");

    DetailedResult {
        name: "no_branch (pipeline)".into(),
        tree_ns_per_call: tree_exec_ns as f64 / ITERS as f64,
        flat_ns_per_call: flat_exec_ns as f64 / ITERS as f64,
        base_ns_per_call: base_exec_ns as f64 / ITERS as f64,
        tree_allocs_per_call: tree_allocs as f64 / ITERS as f64,
        flat_allocs_per_call: flat_allocs as f64 / ITERS as f64,
        chunk_count,
        tree_node_count: tree_nodes,
        setup_ns,
    }
}

fn run_bench_2way() -> DetailedResult {
    let tree = prog_2way();
    let tree_nodes = count_tree_nodes(&tree);

    let t0 = Instant::now();
    let table = Analyzer::analyze(&tree);
    let setup_ns = t0.elapsed().as_nanos() as u64;
    let chunk_count = table.chunks.len();

    // Inputs: (payload, tag) — tag alternates 0/1
    let inputs: Vec<(i32, i32)> = (0..ITERS as i32)
        .map(|i| (i % 200 - 100, (i % 2) as i32))
        .collect();

    // Tree-walking
    let mut state = Value::Int(0);
    let mut acc_tree: i64 = 0;
    let t0 = Instant::now();
    reset_alloc_counters();
    for &(x, tag) in &inputs {
        let r = run_tree(&tree, make_choice_input(x, tag), &mut state).unwrap();
        acc_tree += if let Value::Int(n) = r { n as i64 } else { 0 };
    }
    let tree_exec_ns = t0.elapsed().as_nanos() as u64;
    let tree_allocs = alloc_count();

    // Flat dispatch: stack = [payload, tag]
    let mut state_flat: i32 = 0;
    let mut stack: Vec<i32> = Vec::with_capacity(256);
    let mut acc_flat: i64 = 0;
    let t0 = Instant::now();
    reset_alloc_counters();
    for &(x, tag) in &inputs {
        stack.clear();
        stack.push(x);
        stack.push(tag);
        let r = run_flat_from(&table, &mut stack, &mut state_flat);
        acc_flat += r as i64;
    }
    let flat_exec_ns = t0.elapsed().as_nanos() as u64;
    let flat_allocs = alloc_count();

    // Baseline
    let mut state_base: i32 = 0;
    let mut acc_base: i64 = 0;
    let t0 = Instant::now();
    for &(x, tag) in &inputs {
        let r = baseline_2way(x, tag, &mut state_base);
        acc_base += r as i64;
    }
    let base_exec_ns = t0.elapsed().as_nanos() as u64;

    assert_eq!(acc_tree, acc_flat, "2way: tree != flat");
    assert_eq!(acc_flat, acc_base, "2way: flat != baseline");

    DetailedResult {
        name: "2-way (1 Choice)".into(),
        tree_ns_per_call: tree_exec_ns as f64 / ITERS as f64,
        flat_ns_per_call: flat_exec_ns as f64 / ITERS as f64,
        base_ns_per_call: base_exec_ns as f64 / ITERS as f64,
        tree_allocs_per_call: tree_allocs as f64 / ITERS as f64,
        flat_allocs_per_call: flat_allocs as f64 / ITERS as f64,
        chunk_count,
        tree_node_count: tree_nodes,
        setup_ns,
    }
}

fn run_bench_4way() -> DetailedResult {
    let tree = prog_4way();
    let tree_nodes = count_tree_nodes(&tree);

    let t0 = Instant::now();
    let table = Analyzer::analyze(&tree);
    let setup_ns = t0.elapsed().as_nanos() as u64;
    let chunk_count = table.chunks.len();

    let inputs: Vec<(i32, i32, i32)> = (0..ITERS as i32)
        .map(|i| (i % 200 - 100, (i % 2) as i32, ((i / 2) % 2) as i32))
        .collect();

    // Tree-walking
    let mut state = Value::Int(0);
    let mut acc_tree: i64 = 0;
    let t0 = Instant::now();
    reset_alloc_counters();
    for &(x, to, ti) in &inputs {
        let r = run_tree(&tree, make_choice_input_4(x, to, ti), &mut state).unwrap();
        acc_tree += if let Value::Int(n) = r { n as i64 } else { 0 };
    }
    let tree_exec_ns = t0.elapsed().as_nanos() as u64;
    let tree_allocs = alloc_count();

    // Flat: stack = [payload, tag_inner, tag_outer]
    let mut state_flat: i32 = 0;
    let mut stack: Vec<i32> = Vec::with_capacity(256);
    let mut acc_flat: i64 = 0;
    let t0 = Instant::now();
    reset_alloc_counters();
    for &(x, to, ti) in &inputs {
        stack.clear();
        stack.push(x);
        stack.push(ti);
        stack.push(to);
        let r = run_flat_from(&table, &mut stack, &mut state_flat);
        acc_flat += r as i64;
    }
    let flat_exec_ns = t0.elapsed().as_nanos() as u64;
    let flat_allocs = alloc_count();

    // Baseline
    let mut state_base: i32 = 0;
    let mut acc_base: i64 = 0;
    let t0 = Instant::now();
    for &(x, to, ti) in &inputs {
        let r = baseline_4way(x, to, ti, &mut state_base);
        acc_base += r as i64;
    }
    let base_exec_ns = t0.elapsed().as_nanos() as u64;

    assert_eq!(acc_tree, acc_flat, "4way: tree != flat");
    assert_eq!(acc_flat, acc_base, "4way: flat != baseline");

    DetailedResult {
        name: "4-way (2 Choices)".into(),
        tree_ns_per_call: tree_exec_ns as f64 / ITERS as f64,
        flat_ns_per_call: flat_exec_ns as f64 / ITERS as f64,
        base_ns_per_call: base_exec_ns as f64 / ITERS as f64,
        tree_allocs_per_call: tree_allocs as f64 / ITERS as f64,
        flat_allocs_per_call: flat_allocs as f64 / ITERS as f64,
        chunk_count,
        tree_node_count: tree_nodes,
        setup_ns,
    }
}

fn run_bench_8way() -> DetailedResult {
    let tree = prog_8way();
    let tree_nodes = count_tree_nodes(&tree);

    let t0 = Instant::now();
    let table = Analyzer::analyze(&tree);
    let setup_ns = t0.elapsed().as_nanos() as u64;
    let chunk_count = table.chunks.len();

    let inputs: Vec<(i32, i32, i32, i32)> = (0..ITERS as i32)
        .map(|i| {
            (
                i % 200 - 100,
                (i % 2) as i32,
                ((i / 2) % 2) as i32,
                ((i / 4) % 2) as i32,
            )
        })
        .collect();

    // Tree-walking
    let mut state = Value::Int(0);
    let mut acc_tree: i64 = 0;
    let t0 = Instant::now();
    reset_alloc_counters();
    for &(x, t1, t2, t3) in &inputs {
        let r = run_tree(&tree, make_choice_input_8(x, t1, t2, t3), &mut state).unwrap();
        acc_tree += if let Value::Int(n) = r { n as i64 } else { 0 };
    }
    let tree_exec_ns = t0.elapsed().as_nanos() as u64;
    let tree_allocs = alloc_count();

    // Flat: stack = [payload, t3, t2, t1]  (t1 outermost on top)
    let mut state_flat: i32 = 0;
    let mut stack: Vec<i32> = Vec::with_capacity(256);
    let mut acc_flat: i64 = 0;
    let t0 = Instant::now();
    reset_alloc_counters();
    for &(x, t1, t2, t3) in &inputs {
        stack.clear();
        stack.push(x);
        stack.push(t3);
        stack.push(t2);
        stack.push(t1);
        let r = run_flat_from(&table, &mut stack, &mut state_flat);
        acc_flat += r as i64;
    }
    let flat_exec_ns = t0.elapsed().as_nanos() as u64;
    let flat_allocs = alloc_count();

    // Baseline
    let mut state_base: i32 = 0;
    let mut acc_base: i64 = 0;
    let t0 = Instant::now();
    for &(x, t1, t2, t3) in &inputs {
        let r = baseline_8way(x, t1, t2, t3, &mut state_base);
        acc_base += r as i64;
    }
    let base_exec_ns = t0.elapsed().as_nanos() as u64;

    assert_eq!(acc_tree, acc_flat, "8way: tree != flat");
    assert_eq!(acc_flat, acc_base, "8way: flat != baseline");

    DetailedResult {
        name: "8-way (3 Choices)".into(),
        tree_ns_per_call: tree_exec_ns as f64 / ITERS as f64,
        flat_ns_per_call: flat_exec_ns as f64 / ITERS as f64,
        base_ns_per_call: base_exec_ns as f64 / ITERS as f64,
        tree_allocs_per_call: tree_allocs as f64 / ITERS as f64,
        flat_allocs_per_call: flat_allocs as f64 / ITERS as f64,
        chunk_count,
        tree_node_count: tree_nodes,
        setup_ns,
    }
}

fn run_bench_dynamic_apply() -> DetailedResult {
    let tree = prog_dynamic_apply();
    let tree_nodes = count_tree_nodes(&tree);

    let t0 = Instant::now();
    let table = Analyzer::analyze(&tree);
    let setup_ns = t0.elapsed().as_nanos() as u64;
    let chunk_count = table.chunks.len();

    let inputs: Vec<(i32, i32)> = (0..ITERS as i32)
        .map(|i| ((i % 4) as i32, (i % 100) - 50))
        .collect();

    // Tree-walking
    let mut state = Value::Int(0);
    let mut acc_tree: i64 = 0;
    let t0 = Instant::now();
    reset_alloc_counters();
    for &(id, val) in &inputs {
        let r = run_tree(&tree, make_apply_input(id, val), &mut state).unwrap();
        acc_tree += if let Value::Int(n) = r { n as i64 } else { 0 };
    }
    let tree_exec_ns = t0.elapsed().as_nanos() as u64;
    let tree_allocs = alloc_count();

    // Flat dispatch: stack = [id, val]
    let mut state_flat: i32 = 0;
    let mut stack: Vec<i32> = Vec::with_capacity(256);
    let mut acc_flat: i64 = 0;
    let t0 = Instant::now();
    reset_alloc_counters();
    for &(id, val) in &inputs {
        stack.clear();
        stack.push(id);
        stack.push(val);
        let r = run_flat_from(&table, &mut stack, &mut state_flat);
        acc_flat += r as i64;
    }
    let flat_exec_ns = t0.elapsed().as_nanos() as u64;
    let flat_allocs = alloc_count();

    // Baseline
    let mut state_base: i32 = 0;
    let mut acc_base: i64 = 0;
    let t0 = Instant::now();
    for &(id, val) in &inputs {
        let r = baseline_dynamic_apply(id, val, &mut state_base);
        acc_base += r as i64;
    }
    let base_exec_ns = t0.elapsed().as_nanos() as u64;

    assert_eq!(acc_tree, acc_flat, "dynamic_apply: tree != flat");
    assert_eq!(acc_flat, acc_base, "dynamic_apply: flat != baseline");

    DetailedResult {
        name: "dynamic_apply (4 candidates)".into(),
        tree_ns_per_call: tree_exec_ns as f64 / ITERS as f64,
        flat_ns_per_call: flat_exec_ns as f64 / ITERS as f64,
        base_ns_per_call: base_exec_ns as f64 / ITERS as f64,
        tree_allocs_per_call: tree_allocs as f64 / ITERS as f64,
        flat_allocs_per_call: flat_allocs as f64 / ITERS as f64,
        chunk_count,
        tree_node_count: tree_nodes,
        setup_ns,
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tree_no_branch() {
        let tree = prog_no_branch();
        let mut state = Value::Int(0);
        let r = run_tree(&tree, Value::Int(5), &mut state).unwrap();
        assert_eq!(r, Value::Int(12));
    }

    #[test]
    fn test_flat_no_branch() {
        let tree = prog_no_branch();
        let table = Analyzer::analyze(&tree);
        let mut state = 0;
        let mut stack = Vec::with_capacity(256);
        let r = run_flat(&table, 5, &mut state, &mut stack);
        assert_eq!(r, 12);
    }

    #[test]
    fn test_tree_2way() {
        let tree = prog_2way();
        let mut state = Value::Int(0);
        let r_left = run_tree(&tree, make_choice_input(-5, 0), &mut state).unwrap();
        assert_eq!(r_left, Value::Int(-4));
        let r_right = run_tree(&tree, make_choice_input(5, 1), &mut state).unwrap();
        assert_eq!(r_right, Value::Int(10));
    }

    #[test]
    fn test_flat_2way() {
        let tree = prog_2way();
        let table = Analyzer::analyze(&tree);
        assert_eq!(table.chunks.len(), 3, "root + 2 branches");
        let mut state = 0;
        let mut stack = Vec::with_capacity(256);
        // Left: tag=0
        stack.clear();
        stack.push(-5);
        stack.push(0);
        assert_eq!(run_flat_from(&table, &mut stack, &mut state), -4);
        // Right: tag=1
        stack.clear();
        stack.push(5);
        stack.push(1);
        assert_eq!(run_flat_from(&table, &mut stack, &mut state), 10);
    }

    #[test]
    fn test_tree_4way() {
        let tree = prog_4way();
        let mut state = Value::Int(0);
        // Left(Left(x)) -> x + 10
        let r = run_tree(&tree, make_choice_input_4(5, 0, 0), &mut state).unwrap();
        assert_eq!(r, Value::Int(15));
        // Right(Right(x)) -> x * 2
        let r = run_tree(&tree, make_choice_input_4(5, 1, 1), &mut state).unwrap();
        assert_eq!(r, Value::Int(10));
        // Left(Right(x)) -> x + 1
        let r = run_tree(&tree, make_choice_input_4(5, 0, 1), &mut state).unwrap();
        assert_eq!(r, Value::Int(6));
        // Right(Left(x)) -> x * 10
        let r = run_tree(&tree, make_choice_input_4(5, 1, 0), &mut state).unwrap();
        assert_eq!(r, Value::Int(50));
    }

    #[test]
    fn test_flat_4way() {
        let tree = prog_4way();
        let table = Analyzer::analyze(&tree);
        assert_eq!(table.chunks.len(), 7, "root + 2 + 4 leaves");
        let mut state = 0;
        let mut stack = Vec::with_capacity(256);
        // Left(Left(x)): stack = [x, 0(inner), 0(outer)]
        stack.clear();
        stack.push(5);
        stack.push(0);
        stack.push(0);
        assert_eq!(run_flat_from(&table, &mut stack, &mut state), 15);
        // Right(Right(x)): stack = [x, 1, 1]
        stack.clear();
        stack.push(5);
        stack.push(1);
        stack.push(1);
        assert_eq!(run_flat_from(&table, &mut stack, &mut state), 10);
        // Left(Right(x)): stack = [x, 1, 0]
        stack.clear();
        stack.push(5);
        stack.push(1);
        stack.push(0);
        assert_eq!(run_flat_from(&table, &mut stack, &mut state), 6);
        // Right(Left(x)): stack = [x, 0, 1]
        stack.clear();
        stack.push(5);
        stack.push(0);
        stack.push(1);
        assert_eq!(run_flat_from(&table, &mut stack, &mut state), 50);
    }

    #[test]
    fn test_tree_8way() {
        let tree = prog_8way();
        let mut state = Value::Int(0);
        // Left(Left(Left(x))) -> x + 1000
        let r = run_tree(&tree, make_choice_input_8(5, 0, 0, 0), &mut state).unwrap();
        assert_eq!(r, Value::Int(1005));
        // Right(Right(Right(x))) -> x * 2
        let r = run_tree(&tree, make_choice_input_8(5, 1, 1, 1), &mut state).unwrap();
        assert_eq!(r, Value::Int(10));
    }

    #[test]
    fn test_flat_8way() {
        let tree = prog_8way();
        let table = Analyzer::analyze(&tree);
        assert_eq!(table.chunks.len(), 15, "root + 2 + 4 + 8 leaves");
        let mut state = 0;
        let mut stack = Vec::with_capacity(256);
        // Left(Left(Left(x))): stack = [x, 0, 0, 0]
        stack.clear();
        stack.push(5);
        stack.push(0);
        stack.push(0);
        stack.push(0);
        assert_eq!(run_flat_from(&table, &mut stack, &mut state), 1005);
        // Right(Right(Right(x))): stack = [x, 1, 1, 1]
        stack.clear();
        stack.push(5);
        stack.push(1);
        stack.push(1);
        stack.push(1);
        assert_eq!(run_flat_from(&table, &mut stack, &mut state), 10);
    }

    #[test]
    fn test_tree_dynamic_apply() {
        let tree = prog_dynamic_apply();
        let mut state = Value::Int(0);
        assert_eq!(
            run_tree(&tree, make_apply_input(0, 10), &mut state).unwrap(),
            Value::Int(11)
        );
        assert_eq!(
            run_tree(&tree, make_apply_input(1, 10), &mut state).unwrap(),
            Value::Int(20)
        );
        assert_eq!(
            run_tree(&tree, make_apply_input(2, 10), &mut state).unwrap(),
            Value::Int(9)
        );
        assert_eq!(
            run_tree(&tree, make_apply_input(3, 10), &mut state).unwrap(),
            Value::Int(30)
        );
    }

    #[test]
    fn test_flat_dynamic_apply() {
        let tree = prog_dynamic_apply();
        let table = Analyzer::analyze(&tree);
        assert_eq!(table.chunks.len(), 5, "root + 4 candidates");
        let mut state = 0;
        let mut stack = Vec::with_capacity(256);
        for (id, expected) in [(0, 11), (1, 20), (2, 9), (3, 30)] {
            stack.clear();
            stack.push(id);
            stack.push(10);
            assert_eq!(
                run_flat_from(&table, &mut stack, &mut state),
                expected,
                "id={}",
                id
            );
        }
    }

    #[test]
    fn test_tree_with_state_get() {
        // Get: returns current state
        let tree = ExplicitComp::OpNode(Op::Get, Box::new(ExplicitComp::Ident));
        let mut state = Value::Int(42);
        let r = run_tree(&tree, Value::Int(99), &mut state).unwrap();
        assert_eq!(r, Value::Int(42), "Get returns state");
        assert_eq!(state, Value::Int(42), "state unchanged by Get");
    }

    #[test]
    fn test_tree_with_state_put() {
        // Put: sets state to input, returns Unit
        let tree = ExplicitComp::OpNode(Op::Put, Box::new(ExplicitComp::Ident));
        let mut state = Value::Int(42);
        let r = run_tree(&tree, Value::Int(99), &mut state).unwrap();
        assert_eq!(r, Value::Unit, "Put returns Unit");
        assert_eq!(state, Value::Int(99), "Put sets state to input");
    }

    #[test]
    fn test_chunk_count_grows_with_branching() {
        assert_eq!(Analyzer::analyze(&prog_no_branch()).chunks.len(), 1);
        assert_eq!(Analyzer::analyze(&prog_2way()).chunks.len(), 3);
        assert_eq!(Analyzer::analyze(&prog_4way()).chunks.len(), 7);
        assert_eq!(Analyzer::analyze(&prog_8way()).chunks.len(), 15);
    }

    #[test]
    fn test_chunk_count_exponential() {
        // Full binary tree of nested Choices: n nested choices -> 2^(n+1) - 1 chunks
        fn full_choice_tree(depth: usize) -> ExplicitComp {
            if depth == 0 {
                return ExplicitComp::AddConst(1);
            }
            ExplicitComp::Choice(
                Box::new(full_choice_tree(depth - 1)),
                Box::new(full_choice_tree(depth - 1)),
            )
        }
        for depth in 0..10 {
            let tree = full_choice_tree(depth);
            let table = Analyzer::analyze(&tree);
            let expected = (1usize << (depth + 1)) - 1;
            assert_eq!(
                table.chunks.len(),
                expected,
                "depth {}: expected {} chunks, got {}",
                depth,
                expected,
                table.chunks.len()
            );
        }
    }

    #[test]
    fn test_apply_dynamic_fallback() {
        // The truly dynamic Apply node (arrow not known at compile time)
        // cannot be pre-compiled. The tree walker handles it at runtime.
        let prog = ExplicitComp::Apply;
        let input = Value::Pair(
            Box::new(Value::Arrow(Box::new(ExplicitComp::AddConst(1)))),
            Box::new(Value::Int(41)),
        );
        let mut state = Value::Int(0);
        let r = run_tree(&prog, input, &mut state).unwrap();
        assert_eq!(r, Value::Int(42), "dynamic Apply runs embedded arrow");
    }

    #[test]
    fn test_select_arrow_is_speculative() {
        // SelectArrow with a finite candidate set IS pre-compilable.
        let tree = prog_dynamic_apply();
        let table = Analyzer::analyze(&tree);
        // Root chunk has a DispatchApply terminator.
        match &table.chunks[0].term {
            ChunkTerm::DispatchApply { targets } => {
                assert_eq!(targets.len(), 4, "4 candidate arrows");
            }
            _ => panic!("root chunk should have DispatchApply terminator"),
        }
    }
}

// ============================================================================
// Main: run benchmarks and print results
// ============================================================================

fn main() {
    println!("============================================================");
    println!("  Speculative Compilation of Transparent ArrowApply Trees");
    println!("============================================================\n");

    println!("Iterations per benchmark: {}\n", ITERS);

    let bench_names = ["no_branch", "2way", "4way", "8way", "dynamic_apply"];

    // Warmup
    for name in &bench_names {
        let _ = run_detailed_benchmark(name);
    }

    // Full timing table
    println!("┌────────────────────────────┬──────────┬───────────┬───────────┬────────────┬────────────┬────────┬────────┐");
    println!("│ Benchmark                  │ Tree ns  │ Flat ns   │ Base ns   │ Tree alloc │ Flat alloc │ Chunks │ Nodes  │");
    println!("│                            │ /call    │ /call     │ /call     │ /call      │ /call      │        │        │");
    println!("├────────────────────────────┼──────────┼───────────┼───────────┼────────────┼────────────┼────────┼────────┤");

    let mut all_results = Vec::new();
    for name in &bench_names {
        let r = run_detailed_benchmark(name);
        println!(
            "│ {:<26} │ {:>8.2} │ {:>9.2} │ {:>9.2} │ {:>10.4} │ {:>10.4} │ {:>6} │ {:>6} │",
            r.name,
            r.tree_ns_per_call,
            r.flat_ns_per_call,
            r.base_ns_per_call,
            r.tree_allocs_per_call,
            r.flat_allocs_per_call,
            r.chunk_count,
            r.tree_node_count,
        );
        all_results.push(r);
    }
    println!("└────────────────────────────┴──────────┴───────────┴───────────┴────────────┴────────────┴────────┴────────┘");

    // Speedup summary
    println!("\n--- Speedup: tree-walking vs speculative dispatch ---\n");
    println!("┌────────────────────────────┬───────────┬───────────┐");
    println!("│ Benchmark                  │ Tree/Flat │ Flat/Base  │");
    println!("├────────────────────────────┼───────────┼───────────┤");
    for r in &all_results {
        let tree_over_flat = r.tree_ns_per_call / r.flat_ns_per_call;
        let flat_over_base = r.flat_ns_per_call / r.base_ns_per_call;
        println!(
            "│ {:<26} │ {:>9.2}x │ {:>10.2}x │",
            r.name, tree_over_flat, flat_over_base
        );
    }
    println!("└────────────────────────────┴───────────┴───────────┘");

    // Setup cost
    println!("\n--- Setup (Stage 0) cost ---\n");
    println!("┌────────────────────────────┬──────────────┐");
    println!("│ Benchmark                  │ Setup (ns)   │");
    println!("├────────────────────────────┼──────────────┤");
    for r in &all_results {
        println!("│ {:<26} │ {:>12} │", r.name, r.setup_ns);
    }
    println!("└────────────────────────────┴──────────────┘");

    // Memory: flat op count vs tree node count
    println!("\n--- Memory: flat op count vs tree node count ---\n");
    println!("┌────────────────────────────┬────────────┬────────────┬──────────┐");
    println!("│ Benchmark                  │ Tree nodes │ Flat ops   │ Ratio    │");
    println!("├────────────────────────────┼────────────┼────────────┼──────────┤");
    let trees: Vec<(&str, ExplicitComp)> = vec![
        ("no_branch", prog_no_branch()),
        ("2way", prog_2way()),
        ("4way", prog_4way()),
        ("8way", prog_8way()),
        ("dynamic_apply", prog_dynamic_apply()),
    ];
    for (name, tree) in &trees {
        let table = Analyzer::analyze(tree);
        let flat_ops = count_chunk_ops(&table);
        let tree_nodes = count_tree_nodes(tree);
        let ratio = flat_ops as f64 / tree_nodes as f64;
        println!("│ {:<26} │ {:>10} │ {:>10} │ {:>8.2} │", name, tree_nodes, flat_ops, ratio);
    }
    println!("└────────────────────────────┴────────────┴────────────┴──────────┘");

    // Exponential blowup
    println!("\n--- Exponential blowup: nested Choices (full binary tree) ---\n");
    println!("┌──────────┬──────────┬───────────┬────────────────┐");
    println!("│ Depth    │ Chunks   │ Flat ops  │ vs tree nodes  │");
    println!("├──────────┼──────────┼───────────┼────────────────┤");
    fn full_tree(depth: usize) -> ExplicitComp {
        if depth == 0 {
            return ExplicitComp::AddConst(1);
        }
        ExplicitComp::Choice(
            Box::new(full_tree(depth - 1)),
            Box::new(full_tree(depth - 1)),
        )
    }
    for depth in 0..=16 {
        let tree = full_tree(depth);
        let table = Analyzer::analyze(&tree);
        let tree_nodes = count_tree_nodes(&tree);
        let flat_ops = count_chunk_ops(&table);
        let ratio = flat_ops as f64 / tree_nodes as f64;
        println!(
            "│ {:<8} │ {:>8} │ {:>9} │ {:>14.2} │",
            depth,
            table.chunks.len(),
            flat_ops,
            ratio
        );
    }
    println!("└──────────┴──────────┴───────────┴────────────────┘");

    println!("\nDone. All correctness checks passed (assertions in benchmark functions).");
}
