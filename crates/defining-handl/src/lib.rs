//! # handl-defining-handl
//!
//! The **self-hosting infrastructure** for ADR-0044 Phase 8.
//!
//! ADR-0044 Phase 8 specifies: "`Language` carries an `eval` capability; a
//! `Language` value describes handl itself. Ship a `handl-defining-handl` data
//! file loaded as a `Language` value, evaluated under itself. The bootstrap
//! becomes `compile(handlLanguage, native)` via the cranelift engine."
//!
//! This crate produces a [`Language`] value that describes the **subset** of
//! handl the data-driven engines can evaluate — the constructs migrated to
//! the data-driven model in Phases 4–5 (value, var, the binary arithmetic /
//! comparison ops, unary not, block bindings (`do { x = v; ... }`), if,
//! ternary, function, call, pipe, paren, apply). It is the "handl defining
//! handl": the language spec as data.
//!
//! ## Scope (honest deliverable)
//!
//! Phases 4–5 migrated a **representative subset** of handl's ~50 constructs
//! to the data-driven model. **Full self-hosting of the entire handl language
//! is not achievable yet** — constructs whose eval schemes dispatch to
//! `Foreign` host functions (match, handle, flow, fanout, field-access,
//! import, export, module, template, resolve, json, hello.greet) are not
//! compilable by the bytecode/cranelift engines, and several `Prim` ops
//! (array, object, index, assign) are not yet implemented in any engine. The
//! `type-annot` construct uses a `Bind` with
//! `$payload` (reads `payload["name"]`) but a type annotation has no natural
//! bind name, so it is blocked until the payload convention is clarified.
//! This crate does **not** attempt to describe the full handl language as
//! data. Instead it:
//!
//! 1. Builds the **self-hosting infrastructure**: a [`Language`] value
//!    describing the subset, assembled from the canonical YAML data files
//!    via [`language`].
//! 2. Provides a **self-hosting corpus** ([`corpus`]) of subset programs used
//!    by the integration tests (`self_host.rs`, `bootstrap.rs`,
//!    `futamura.rs`) to prove the self-hosting *mechanism*. ADR-0052 Phase D
//!    adds an **arrow-authored corpus** ([`proc_corpus`]) demonstrating the
//!    arrow-calculus authoring surface (`x ~> body`).
//!
//! What is **proven**: a `Language` value can describe a language and be
//! evaluated under itself (across all three eval engines: tree-walk,
//! bytecode, cranelift), and compiled to native code via the cranelift engine
//! — the Futamura projection sanity check.
//!
//! What is **deferred**: full handl self-hosting (pending migration of the
//! remaining constructs — primarily `Foreign`-dispatched constructs and the
//! unimplemented `Prim` ops), and a standalone-binary bootstrap (writing an
//! executable to disk). Phase 8 proves the *mechanism*, not the
//! standalone-binary artifact.

#![warn(missing_docs)]

use handl_language::{Ast, AstNode, Language, Value};
use serde_json::json;

/// The self-describing `Language` assembled from the canonical YAML data
/// files.
///
/// This is the canonical data-driven language: the same `Language` produced by
/// [`handl_kit_data_canonical::assemble`] — the full language (tokens, grammar,
/// eval, AST shapes, capabilities) merged into one `Language` value from the
/// 7 YAML files in `handl-kit-data-canonical/data/`. It is "handl defining
/// handl" for the subset.
pub fn language() -> Language {
    // Delegate to the canonical data-driven kit assembly. This is the same
    // merged Language used by the data-driven runtime path — the single
    // source of truth for the subset.
    handl_kit_data_canonical::assemble()
        .expect("canonical data-driven kit must assemble")
        .lang()
        .clone()
}

// ---------------------------------------------------------------------------
// Self-hosting corpus
// ---------------------------------------------------------------------------

/// A single self-hosting corpus case: an [`Ast`] built from the subset
/// constructs and the expected evaluation result.
#[derive(Debug, Clone)]
pub struct CorpusCase {
    /// A human-readable name for the case.
    pub name: &'static str,
    /// A human-readable description of the source-level program this models.
    pub source: &'static str,
    /// The AST to evaluate (built from the subset's node kinds).
    pub ast: Ast,
    /// The expected result value.
    pub expected: Value,
    /// Whether this case is supported only under the tree-walk engine (not
    /// bytecode/cranelift). When `true`, the compiled-engine tests skip it;
    /// the tree-walk tests still run it. This flags constructs whose `Prim`
    /// op is implemented in the tree-walk engine but not yet in the bytecode
    /// or cranelift engines (an honest engine-coverage gap).
    pub tree_walk_only: bool,
}

/// Build the self-hosting corpus: a set of programs using the data-driven
/// subset constructs that all three eval engines (tree-walk, bytecode,
/// cranelift) can evaluate.
///
/// Each case's [`Ast`] is constructed manually using the canonical data-driven
/// node kinds and the payload conventions documented by the Phase 4
/// emitters. The Pratt grammar for delimited forms (call/if/function) is
/// a placeholder per Phase 4 deviations, so ASTs are hand-built rather than
/// parsed from source.
///
/// The corpus covers the following constructs. Cases marked **(tw-only)** use
/// a `Prim` op implemented in the tree-walk engine but not yet in the
/// bytecode or cranelift engines — they set [`CorpusCase::tree_walk_only`]
/// and are skipped by the compiled-engine tests. Currently no case is
/// tree-walk-only; the flag is retained for future engine-coverage gaps.
///
/// | Case                 | Source model                          | Constructs used                     |
/// |----------------------|---------------------------------------|-------------------------------------|
/// | `literal`            | `42`                                  | value                               |
/// | `arith_add`          | `1 + 2`                               | value, binary.add                   |
/// | `arith_sub`          | `10 - 4`                              | value, binary.sub                   |
/// | `arith_mul`          | `3 * 4`                               | value, binary.mul                   |
/// | `arith_div`          | `20 / 4`                              | value, binary.div                   |
/// | `arith_pow`          | `2 ^ 3`                               | value, binary.pow                   |
/// | `eq_true`            | `3 == 3`                              | value, binary.eq                    |
/// | `eq_false`           | `3 == 4`                              | value, binary.eq                    |
/// | `lt_true`            | `1 < 2`                               | value, binary.lt                    |
/// | `gt_true`            | `2 > 1`                               | value, binary.gt                    |
/// | `gte_true`           | `2 >= 2`                              | value, binary.gte                   |
/// | `gte_false`          | `1 >= 3`                              | value, binary.gte                   |
/// | `lte_true`           | `2 <= 2`                              | value, binary.lte                   |
/// | `lte_false`          | `3 <= 1`                              | value, binary.lte                   |
/// | `neq_true`           | `3 != 4`                              | value, binary.neq                   |
/// | `neq_false`          | `3 != 3`                              | value, binary.neq                   |
/// | `compare_less`       | `1 <=> 2`                             | value, binary.compare               |
/// | `compare_equal`      | `2 <=> 2`                             | value, binary.compare               |
/// | `compare_greater`    | `3 <=> 2`                             | value, binary.compare               |
/// | `typeof_number`      | `typeof 42`                           | value, typeof                       |
/// | `typeof_string`      | `typeof "hi"`                         | value, typeof                       |
/// | `typeof_bool`        | `typeof true`                         | value, typeof                       |
/// | `not_true`           | `!false`                              | value, unary.not                    |
/// | `not_false`          | `!true`                               | value, unary.not                    |
/// | `bind_var`           | `do { x = 5; x }`                     | value, assign, block, var           |
/// | `bind_stmt`          | `do { x :: 6; x }`                    | value, assign, block, var           |
/// | `if_true`            | `if (true) 1 else 2`                  | value, if                           |
/// | `if_false`           | `if (false) 1 else 2`                 | value, if                           |
/// | `ternary_true`       | `true ? 1 : 2`                        | value, ternary                      |
/// | `ternary_false`      | `false ? 1 : 2`                       | value, ternary                      |
/// | `paren`              | `(42)`                                | value, paren                        |
/// | `apply`              | `apply 42`                            | value, apply                        |
/// | `function_call`      | `do { f :: [x, y] ~> x + y; f(3, 4) }`  | function, call, block, assign, var, binary.add|
/// | `pipe_call`          | `do { f :: (x ~> x + 1); 5 | f }`       | function, pipe, block, assign, var, binary.add|
/// | `rest_params`        | `do { f :: [a, ...rest] ~> rest; f(1,2,3) }` | function(rest param), call, block, assign, var |
/// | `rest_params_empty`  | `do { f :: [a, ...rest] ~> rest; f(1) }` | function(rest param), call, block, assign, var |
/// | `nested_bind`        | `do { x = 3; y = 4; x + y }`            | block, assign, var, binary.add      |
/// | `if_with_bind`       | `if (true) (do { x = 1; x }) else 0`    | if, block, assign, var, value       |
/// | `array_literal`      | `[1, 2, 3]`                           | array                               |
/// | `array_index`        | `[10, 20, 30][1]`                     | index                               |
/// | `object_literal`     | `{"a": 1, "b": 2}`                    | object                              |
/// | `object_index`       | `{"x": 5}["x"]`                       | index                               |
/// | `assign_value`       | `x = 42`                              | assign                              |
///
/// Note: the `call` construct targets **2-argument calls** (the canonical
/// emitter's fixed arity), so the function-call case uses a 2-arg function
/// `f(x, y) -> x + y` applied as `f(3, 4)`. The `pipe` construct's scheme is
/// `App { callee: Child 1, args: [Child 0] }` — it applies the right child
/// (a function) to the left child (a value) — so the pipe case uses a 1-arg
/// function.
pub fn corpus() -> Vec<CorpusCase> {
    vec![
        // 1. Literal: 42
        CorpusCase {
            name: "literal",
            source: "42",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("value").with_payload(json!(42)));
                a
            },
            expected: json!(42),
            tree_walk_only: false,
        },
        // 2. Arithmetic: 1 + 2
        CorpusCase {
            name: "arith_add",
            source: "1 + 2",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("value").with_payload(json!(1)));
                a.push(AstNode::new("value").with_payload(json!(2)));
                a.push(AstNode::new("binary.add").with_payload(json!({"children": [0, 1]})));
                a
            },
            expected: json!(3),
            tree_walk_only: false,
        },
        // 3. Subtraction: 10 - 4
        CorpusCase {
            name: "arith_sub",
            source: "10 - 4",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("value").with_payload(json!(10)));
                a.push(AstNode::new("value").with_payload(json!(4)));
                a.push(AstNode::new("binary.sub").with_payload(json!({"children": [0, 1]})));
                a
            },
            expected: json!(6),
            tree_walk_only: false,
        },
        // 4. Multiplication: 3 * 4
        CorpusCase {
            name: "arith_mul",
            source: "3 * 4",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("value").with_payload(json!(3)));
                a.push(AstNode::new("value").with_payload(json!(4)));
                a.push(AstNode::new("binary.mul").with_payload(json!({"children": [0, 1]})));
                a
            },
            expected: json!(12),
            tree_walk_only: false,
        },
        // 5. Division: 20 / 4
        CorpusCase {
            name: "arith_div",
            source: "20 / 4",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("value").with_payload(json!(20)));
                a.push(AstNode::new("value").with_payload(json!(4)));
                a.push(AstNode::new("binary.div").with_payload(json!({"children": [0, 1]})));
                a
            },
            expected: json!(5),
            tree_walk_only: false,
        },
        // 6. Power: 2 ^ 3 (`pow` prim now in all engines)
        CorpusCase {
            name: "arith_pow",
            source: "2 ^ 3",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("value").with_payload(json!(2)));
                a.push(AstNode::new("value").with_payload(json!(3)));
                a.push(AstNode::new("binary.pow").with_payload(json!({"children": [0, 1]})));
                a
            },
            expected: json!(8.0),
            tree_walk_only: false,
        },
        // 7. Equality true: 3 == 3
        CorpusCase {
            name: "eq_true",
            source: "3 == 3",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("value").with_payload(json!(3)));
                a.push(AstNode::new("value").with_payload(json!(3)));
                a.push(AstNode::new("binary.eq").with_payload(json!({"children": [0, 1]})));
                a
            },
            expected: json!(true),
            tree_walk_only: false,
        },
        // 8. Equality false: 3 == 4
        CorpusCase {
            name: "eq_false",
            source: "3 == 4",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("value").with_payload(json!(3)));
                a.push(AstNode::new("value").with_payload(json!(4)));
                a.push(AstNode::new("binary.eq").with_payload(json!({"children": [0, 1]})));
                a
            },
            expected: json!(false),
            tree_walk_only: false,
        },
        // 9. Less-than true: 1 < 2
        CorpusCase {
            name: "lt_true",
            source: "1 < 2",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("value").with_payload(json!(1)));
                a.push(AstNode::new("value").with_payload(json!(2)));
                a.push(AstNode::new("binary.lt").with_payload(json!({"children": [0, 1]})));
                a
            },
            expected: json!(true),
            tree_walk_only: false,
        },
        // 10. Greater-than true: 2 > 1
        CorpusCase {
            name: "gt_true",
            source: "2 > 1",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("value").with_payload(json!(2)));
                a.push(AstNode::new("value").with_payload(json!(1)));
                a.push(AstNode::new("binary.gt").with_payload(json!({"children": [0, 1]})));
                a
            },
            expected: json!(true),
            tree_walk_only: false,
        },
        // 11. Unary not true: !false
        CorpusCase {
            name: "not_true",
            source: "!false",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("value").with_payload(json!(false)));
                a.push(AstNode::new("unary.not").with_payload(json!({"children": [0]})));
                a
            },
            expected: json!(true),
            tree_walk_only: false,
        },
        // 12. Unary not false: !true
        CorpusCase {
            name: "not_false",
            source: "!true",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("value").with_payload(json!(true)));
                a.push(AstNode::new("unary.not").with_payload(json!({"children": [0]})));
                a
            },
            expected: json!(false),
            tree_walk_only: false,
        },
        // 13. Block bind + var: do { x = 5; x }
        //     `eval_block` binds each `assign` child's target var, then
        //     returns the last child's value.
        CorpusCase {
            name: "bind_var",
            source: "do { x = 5; x }",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("value").with_payload(json!(5))); // 0
                a.push(AstNode::new("var").with_payload(json!("x"))); // 1
                a.push(
                    AstNode::new("assign") // 2: x = 5
                        .with_payload(json!({"children": [1, 0]})),
                );
                a.push(
                    AstNode::new("block") // 3: do { x = 5; x }
                        .with_payload(json!({"children": [2, 1]})),
                );
                a
            },
            expected: json!(5),
            // Block binding (update-or-define `assign`) is implemented in
            // all three engines.
            tree_walk_only: false,
        },
        // 14. Block bind via `::`: do { x :: 6; x }
        //     `=` and `::` both lex to `token.bind` → `assign` nodes.
        CorpusCase {
            name: "bind_stmt",
            source: "do { x :: 6; x }",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("value").with_payload(json!(6))); // 0
                a.push(AstNode::new("var").with_payload(json!("x"))); // 1
                a.push(
                    AstNode::new("assign") // 2: x :: 6
                        .with_payload(json!({"children": [1, 0]})),
                );
                a.push(
                    AstNode::new("block") // 3: do { x :: 6; x }
                        .with_payload(json!({"children": [2, 1]})),
                );
                a
            },
            expected: json!(6),
            tree_walk_only: false,
        },
        // 15. If true: if (true) 1 else 2
        CorpusCase {
            name: "if_true",
            source: "if (true) 1 else 2",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("value").with_payload(json!(true)));
                a.push(AstNode::new("value").with_payload(json!(1)));
                a.push(AstNode::new("value").with_payload(json!(2)));
                a.push(AstNode::new("if").with_payload(json!({"children": [0, 1, 2]})));
                a
            },
            expected: json!(1),
            tree_walk_only: false,
        },
        // 16. If false: if (false) 1 else 2
        CorpusCase {
            name: "if_false",
            source: "if (false) 1 else 2",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("value").with_payload(json!(false)));
                a.push(AstNode::new("value").with_payload(json!(1)));
                a.push(AstNode::new("value").with_payload(json!(2)));
                a.push(AstNode::new("if").with_payload(json!({"children": [0, 1, 2]})));
                a
            },
            expected: json!(2),
            tree_walk_only: false,
        },
        // 16b. If without else: `if (false) 1` — the `else` child is optional
        // (grammar `optional_children`); the arity-2 node evaluates to null.
        CorpusCase {
            name: "if_no_else",
            source: "if (false) 1",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("value").with_payload(json!(false)));
                a.push(AstNode::new("value").with_payload(json!(1)));
                a.push(AstNode::new("if").with_payload(json!({"children": [0, 1]})));
                a
            },
            expected: json!(null),
            tree_walk_only: false,
        },
        // 17. Ternary true: true ? 1 : 2  (ternary uses the same Branch scheme as if)
        CorpusCase {
            name: "ternary_true",
            source: "true ? 1 : 2",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("value").with_payload(json!(true)));
                a.push(AstNode::new("value").with_payload(json!(1)));
                a.push(AstNode::new("value").with_payload(json!(2)));
                a.push(AstNode::new("ternary").with_payload(json!({"children": [0, 1, 2]})));
                a
            },
            expected: json!(1),
            tree_walk_only: false,
        },
        // 18. Ternary false: false ? 1 : 2
        CorpusCase {
            name: "ternary_false",
            source: "false ? 1 : 2",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("value").with_payload(json!(false)));
                a.push(AstNode::new("value").with_payload(json!(1)));
                a.push(AstNode::new("value").with_payload(json!(2)));
                a.push(AstNode::new("ternary").with_payload(json!({"children": [0, 1, 2]})));
                a
            },
            expected: json!(2),
            tree_walk_only: false,
        },
        // 19. Paren: (42)  (paren is a Child 0 passthrough)
        CorpusCase {
            name: "paren",
            source: "(42)",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("value").with_payload(json!(42)));
                a.push(AstNode::new("paren").with_payload(json!({"children": [0]})));
                a
            },
            expected: json!(42),
            tree_walk_only: false,
        },
        // 20. Apply: apply 42  (apply is a Child 0 passthrough)
        CorpusCase {
            name: "apply",
            source: "apply 42",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("value").with_payload(json!(42)));
                a.push(AstNode::new("apply").with_payload(json!({"children": [0]})));
                a
            },
            expected: json!(42),
            tree_walk_only: false,
        },
        // 21. Mood (stale — removed in ADR-0026): the `42!` postfix mood
        // marker was replaced by infix keyword syntax (`is`, `must`, `may`,
        // `not`, `when`). The `mood` node kind no longer exists; only
        // `mood.int`, `mood.pot`, `mood.norm`, `mood.neg`, `mood.cnd` remain.
        // This case is intentionally omitted from the corpus.
        // 22. Function + call: do { f :: [x, y] ~> x + y; f(3, 4) }
        //     The canonical call emitter targets 2-arg calls, so the function
        //     takes two params.
        CorpusCase {
            name: "function_call",
            source: "do { f :: [x, y] ~> x + y; f(3, 4) }",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("var").with_payload(json!("x"))); // 0
                a.push(AstNode::new("var").with_payload(json!("y"))); // 1
                a.push(
                    AstNode::new("binary.add") // 2: body x + y
                        .with_payload(json!({"children": [0, 1]})),
                );
                a.push(
                    AstNode::new("function") // 3: (x, y) -> x + y
                        .with_payload(json!({"params": ["x", "y"], "body": 2})),
                );
                a.push(AstNode::new("value").with_payload(json!(3))); // 4
                a.push(AstNode::new("value").with_payload(json!(4))); // 5
                a.push(AstNode::new("var").with_payload(json!("f"))); // 6
                a.push(
                    AstNode::new("call") // 7: f(3, 4)
                        .with_payload(json!({"children": [6, 4, 5]})),
                );
                a.push(
                    AstNode::new("assign") // 8: f :: function
                        .with_payload(json!({"children": [6, 3]})),
                );
                a.push(
                    AstNode::new("block") // 9: do { f :: fn; f(3, 4) }
                        .with_payload(json!({"children": [8, 7]})),
                );
                a
            },
            expected: json!(7),
            tree_walk_only: false,
        },
        // 23. Pipe: do { f :: (x ~> x + 1); 5 | f }
        //     pipe scheme is App { callee: Child 1, args: [Child 0] } —
        //     applies the right child (function) to the left child (value).
        CorpusCase {
            name: "pipe_call",
            source: "do { f :: (x ~> x + 1); 5 | f }",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("var").with_payload(json!("x"))); // 0
                a.push(AstNode::new("value").with_payload(json!(1))); // 1
                a.push(
                    AstNode::new("binary.add") // 2: body x + 1
                        .with_payload(json!({"children": [0, 1]})),
                );
                a.push(
                    AstNode::new("function") // 3: (x) -> x + 1
                        .with_payload(json!({"params": ["x"], "body": 2})),
                );
                a.push(AstNode::new("value").with_payload(json!(5))); // 4: left of pipe
                a.push(AstNode::new("var").with_payload(json!("f"))); // 5: right of pipe
                a.push(
                    AstNode::new("pipe") // 6: 5 | f  → App(f, [5])
                        .with_payload(json!({"children": [4, 5]})),
                );
                a.push(
                    AstNode::new("assign") // 7: f :: function
                        .with_payload(json!({"children": [5, 3]})),
                );
                a.push(
                    AstNode::new("block") // 8: do { f :: fn; 5 | f }
                        .with_payload(json!({"children": [7, 6]})),
                );
                a
            },
            expected: json!(6),
            tree_walk_only: false,
        },
        // 23b. Rest params: do { f :: [a, ...rest] ~> rest; f(1, 2, 3) }.
        //     The `rest` payload field marks the variadic parameter; surplus
        //     args bind to it as an array.
        CorpusCase {
            name: "rest_params",
            source: "do { f :: [a, ...rest] ~> rest; f(1, 2, 3) }",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("var").with_payload(json!("rest"))); // 0
                a.push(
                    AstNode::new("function") // 1: [a, ...rest] ~> rest
                        .with_payload(json!({"params": ["a"], "rest": "rest", "body": 0})),
                );
                a.push(AstNode::new("value").with_payload(json!(1))); // 2
                a.push(AstNode::new("value").with_payload(json!(2))); // 3
                a.push(AstNode::new("value").with_payload(json!(3))); // 4
                a.push(AstNode::new("var").with_payload(json!("f"))); // 5
                a.push(
                    AstNode::new("call") // 6: f(1, 2, 3)
                        .with_payload(json!({"children": [5, 2, 3, 4]})),
                );
                a.push(
                    AstNode::new("assign") // 7: f :: function
                        .with_payload(json!({"children": [5, 1]})),
                );
                a.push(
                    AstNode::new("block") // 8: do { f :: fn; f(1, 2, 3) }
                        .with_payload(json!({"children": [7, 6]})),
                );
                a
            },
            expected: json!([2, 3]),
            tree_walk_only: false,
        },
        // 23c. Rest params, empty tail: do { f :: [a, ...rest] ~> rest; f(1) }.
        //     With no surplus args the rest binding is the empty array.
        CorpusCase {
            name: "rest_params_empty",
            source: "do { f :: [a, ...rest] ~> rest; f(1) }",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("var").with_payload(json!("rest"))); // 0
                a.push(
                    AstNode::new("function") // 1: [a, ...rest] ~> rest
                        .with_payload(json!({"params": ["a"], "rest": "rest", "body": 0})),
                );
                a.push(AstNode::new("value").with_payload(json!(1))); // 2
                a.push(AstNode::new("var").with_payload(json!("f"))); // 3
                a.push(
                    AstNode::new("call") // 4: f(1)
                        .with_payload(json!({"children": [3, 2]})),
                );
                a.push(
                    AstNode::new("assign") // 5: f :: function
                        .with_payload(json!({"children": [3, 1]})),
                );
                a.push(
                    AstNode::new("block") // 6: do { f :: fn; f(1) }
                        .with_payload(json!({"children": [5, 4]})),
                );
                a
            },
            expected: json!([]),
            tree_walk_only: false,
        },
        // 24. Nested block bindings + add: do { x = 3; y = 4; x + y }
        CorpusCase {
            name: "nested_bind",
            source: "do { x = 3; y = 4; x + y }",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("value").with_payload(json!(3))); // 0
                a.push(AstNode::new("value").with_payload(json!(4))); // 1
                a.push(AstNode::new("var").with_payload(json!("x"))); // 2
                a.push(AstNode::new("var").with_payload(json!("y"))); // 3
                a.push(
                    AstNode::new("binary.add") // 4: x + y
                        .with_payload(json!({"children": [2, 3]})),
                );
                a.push(
                    AstNode::new("assign") // 5: y = 4
                        .with_payload(json!({"children": [3, 1]})),
                );
                a.push(
                    AstNode::new("assign") // 6: x = 3
                        .with_payload(json!({"children": [2, 0]})),
                );
                a.push(
                    AstNode::new("block") // 7: do { x = 3; y = 4; x + y }
                        .with_payload(json!({"children": [6, 5, 4]})),
                );
                a
            },
            expected: json!(7),
            tree_walk_only: false,
        },
        // 25. If with block binding in branch:
        //     if (true) (do { x = 1; x }) else 0
        CorpusCase {
            name: "if_with_bind",
            source: "if (true) (do { x = 1; x }) else 0",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("value").with_payload(json!(true))); // 0: cond
                a.push(AstNode::new("value").with_payload(json!(1))); // 1
                a.push(AstNode::new("var").with_payload(json!("x"))); // 2
                a.push(
                    AstNode::new("assign") // 3: x = 1
                        .with_payload(json!({"children": [2, 1]})),
                );
                a.push(
                    AstNode::new("block") // 4: do { x = 1; x }
                        .with_payload(json!({"children": [3, 2]})),
                );
                a.push(AstNode::new("value").with_payload(json!(0))); // 5: else
                a.push(
                    AstNode::new("if") // 6
                        .with_payload(json!({"children": [0, 4, 5]})),
                );
                a
            },
            expected: json!(1),
            tree_walk_only: false,
        },
        // 26. Greater-than-or-equal true: 2 >= 2
        CorpusCase {
            name: "gte_true",
            source: "2 >= 2",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("value").with_payload(json!(2)));
                a.push(AstNode::new("value").with_payload(json!(2)));
                a.push(AstNode::new("binary.gte").with_payload(json!({"children": [0, 1]})));
                a
            },
            expected: json!(true),
            tree_walk_only: false,
        },
        // 27. Greater-than-or-equal false: 1 >= 3
        CorpusCase {
            name: "gte_false",
            source: "1 >= 3",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("value").with_payload(json!(1)));
                a.push(AstNode::new("value").with_payload(json!(3)));
                a.push(AstNode::new("binary.gte").with_payload(json!({"children": [0, 1]})));
                a
            },
            expected: json!(false),
            tree_walk_only: false,
        },
        // 28. Less-than-or-equal true: 2 <= 2
        CorpusCase {
            name: "lte_true",
            source: "2 <= 2",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("value").with_payload(json!(2)));
                a.push(AstNode::new("value").with_payload(json!(2)));
                a.push(AstNode::new("binary.lte").with_payload(json!({"children": [0, 1]})));
                a
            },
            expected: json!(true),
            tree_walk_only: false,
        },
        // 29. Less-than-or-equal false: 3 <= 1
        CorpusCase {
            name: "lte_false",
            source: "3 <= 1",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("value").with_payload(json!(3)));
                a.push(AstNode::new("value").with_payload(json!(1)));
                a.push(AstNode::new("binary.lte").with_payload(json!({"children": [0, 1]})));
                a
            },
            expected: json!(false),
            tree_walk_only: false,
        },
        // 30. Not-equal true: 3 != 4
        CorpusCase {
            name: "neq_true",
            source: "3 != 4",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("value").with_payload(json!(3)));
                a.push(AstNode::new("value").with_payload(json!(4)));
                a.push(AstNode::new("binary.neq").with_payload(json!({"children": [0, 1]})));
                a
            },
            expected: json!(true),
            tree_walk_only: false,
        },
        // 31. Not-equal false: 3 != 3
        CorpusCase {
            name: "neq_false",
            source: "3 != 3",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("value").with_payload(json!(3)));
                a.push(AstNode::new("value").with_payload(json!(3)));
                a.push(AstNode::new("binary.neq").with_payload(json!({"children": [0, 1]})));
                a
            },
            expected: json!(false),
            tree_walk_only: false,
        },
        // 32. Compare less: 1 <=> 2 → -1
        CorpusCase {
            name: "compare_less",
            source: "1 <=> 2",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("value").with_payload(json!(1)));
                a.push(AstNode::new("value").with_payload(json!(2)));
                a.push(AstNode::new("binary.compare").with_payload(json!({"children": [0, 1]})));
                a
            },
            expected: json!(-1),
            tree_walk_only: false,
        },
        // 33. Compare equal: 2 <=> 2 → 0
        CorpusCase {
            name: "compare_equal",
            source: "2 <=> 2",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("value").with_payload(json!(2)));
                a.push(AstNode::new("value").with_payload(json!(2)));
                a.push(AstNode::new("binary.compare").with_payload(json!({"children": [0, 1]})));
                a
            },
            expected: json!(0),
            tree_walk_only: false,
        },
        // 34. Compare greater: 3 <=> 2 → 1
        CorpusCase {
            name: "compare_greater",
            source: "3 <=> 2",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("value").with_payload(json!(3)));
                a.push(AstNode::new("value").with_payload(json!(2)));
                a.push(AstNode::new("binary.compare").with_payload(json!({"children": [0, 1]})));
                a
            },
            expected: json!(1),
            tree_walk_only: false,
        },
        // 35. typeof number: typeof 42 → "number"
        CorpusCase {
            name: "typeof_number",
            source: "typeof 42",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("value").with_payload(json!(42)));
                a.push(AstNode::new("typeof").with_payload(json!({"children": [0]})));
                a
            },
            expected: json!("number"),
            tree_walk_only: false,
        },
        // 36. typeof string: typeof "hi" → "string"
        CorpusCase {
            name: "typeof_string",
            source: "typeof \"hi\"",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("value").with_payload(json!("hi")));
                a.push(AstNode::new("typeof").with_payload(json!({"children": [0]})));
                a
            },
            expected: json!("string"),
            tree_walk_only: false,
        },
        // 37. typeof bool: typeof true → "bool"
        CorpusCase {
            name: "typeof_bool",
            source: "typeof true",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("value").with_payload(json!(true)));
                a.push(AstNode::new("typeof").with_payload(json!({"children": [0]})));
                a
            },
            expected: json!("bool"),
            tree_walk_only: false,
        },
        // 38. Array literal: [1, 2, 3] → [1, 2, 3]
        //     The `array` prim reads `elements` directly from the payload.
        CorpusCase {
            name: "array_literal",
            source: "[1, 2, 3]",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("array").with_payload(json!({"elements": [1, 2, 3]})));
                a
            },
            expected: json!([1, 2, 3]),
            tree_walk_only: false,
        },
        // 39. Array index: [10, 20, 30][1] → 20
        //     The `index` prim operates on the evaluated `children`:
        //     children[0] is the array node, children[1] is the index.
        CorpusCase {
            name: "array_index",
            source: "[10, 20, 30][1]",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("array").with_payload(json!({"elements": [10, 20, 30]})));
                a.push(AstNode::new("value").with_payload(json!(1)));
                a.push(AstNode::new("index").with_payload(json!({"children": [0, 1]})));
                a
            },
            expected: json!(20),
            tree_walk_only: false,
        },
        // 40. Object literal: {"a": 1, "b": 2} → {"a": 1, "b": 2}
        //     The `object` prim reads `entries` (array of {key, value}) from
        //     the payload and builds a JSON object.
        CorpusCase {
            name: "object_literal",
            source: "{\"a\": 1, \"b\": 2}",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("object").with_payload(json!({
                    "entries": [
                        {"key": "a", "value": 1},
                        {"key": "b", "value": 2}
                    ]
                })));
                a
            },
            expected: json!({"a": 1, "b": 2}),
            tree_walk_only: false,
        },
        // 41. Object index: {"x": 5}["x"] → 5
        //     The `index` prim with an object target and string key —
        //     children[0] is the object node, children[1] is the key.
        CorpusCase {
            name: "object_index",
            source: "{\"x\": 5}[\"x\"]",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("object").with_payload(json!({
                    "entries": [{"key": "x", "value": 5}]
                })));
                a.push(AstNode::new("value").with_payload(json!("x")));
                a.push(AstNode::new("index").with_payload(json!({"children": [0, 1]})));
                a
            },
            expected: json!(5),
            tree_walk_only: false,
        },
        // 42. Assign: x :: 42 → 42
        //     The `assign` prim reads `value` from the payload and returns it.
        CorpusCase {
            name: "assign_value",
            source: "x :: 42",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("assign").with_payload(json!({"target": "x", "value": 42})));
                a
            },
            expected: json!(42),
            tree_walk_only: false,
        },
    ]
}

// ---------------------------------------------------------------------------
// arrow-notation corpus (ADR-0052 Phase D)
// ---------------------------------------------------------------------------

/// Build the arrow-authored corpus: a set of programs authored using
/// arrow notation (`x ~> body`), the authoring surface introduced in
/// ADR-0052 Phase C.
///
/// `x ~> body` parses as `function(params, body)` — a `function` node
/// with params and body. The `function` eval scheme produces a closure.
///
/// Each case's [`Ast`] is constructed manually using the canonical
/// data-driven node kinds. The `function` node has payload `{"params":
/// [...], "body": idx}` (matching the existing corpus convention). Cases
/// that apply a function to a value use the `pipe` construct
/// (`App { callee: Child 1, args: [Child 0] }` — applies the right child
/// to the left child).
///
/// All cases produce **concrete values** (numbers), not closures, so they
/// can be run through every engine (v1 and v2, tree-walk and compiled) for
/// cross-engine conformance.
///
/// | Case               | Source model                                  | Expected |
/// |--------------------|-----------------------------------------------|----------|
/// | `proc_increment`   | `41 \| (x ~> x + 1)`                          | 42       |
/// | `proc_double`      | `21 \| (x ~> x * 2)`                          | 42       |
/// | `proc_const`       | `99 \| (x ~> 42)`                             | 42       |
/// | `proc_pipe_chain`  | `5 \| (x ~> x + 1) \| (y ~> y * 2)`          | 12       |
/// | `proc_bind_body`   | `3 \| (x ~> do { y = x + 1; y * 2 })`           | 8        |
pub fn proc_corpus() -> Vec<CorpusCase> {
    vec![
        // 1. proc_increment: 41 | (x ~> x + 1)  →  42
        //    The pipe applies the function (right) to 41 (left).
        CorpusCase {
            name: "proc_increment",
            source: "41 | (x ~> x + 1)",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("var").with_payload(json!("x"))); // 0: param x
                a.push(AstNode::new("value").with_payload(json!(1))); // 1: literal 1
                a.push(
                    AstNode::new("binary.add") // 2: body x + 1
                        .with_payload(json!({"children": [0, 1]})),
                );
                a.push(
                    AstNode::new("function") // 3: x ~> x + 1
                        .with_payload(json!({"params": ["x"], "body": 2})),
                );
                a.push(AstNode::new("value").with_payload(json!(41))); // 4: left of pipe
                a.push(
                    AstNode::new("pipe") // 5: 41 | fn  →  App(fn, [41])
                        .with_payload(json!({"children": [4, 3]})),
                );
                a
            },
            expected: json!(42),
            tree_walk_only: false,
        },
        // 2. proc_double: 21 | (x ~> x * 2)  →  42
        CorpusCase {
            name: "proc_double",
            source: "21 | (x ~> x * 2)",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("var").with_payload(json!("x"))); // 0: param x
                a.push(AstNode::new("value").with_payload(json!(2))); // 1: literal 2
                a.push(
                    AstNode::new("binary.mul") // 2: body x * 2
                        .with_payload(json!({"children": [0, 1]})),
                );
                a.push(
                    AstNode::new("function") // 3: x ~> x * 2
                        .with_payload(json!({"params": ["x"], "body": 2})),
                );
                a.push(AstNode::new("value").with_payload(json!(21))); // 4: left of pipe
                a.push(
                    AstNode::new("pipe") // 5: 21 | fn  →  42
                        .with_payload(json!({"children": [4, 3]})),
                );
                a
            },
            expected: json!(42),
            tree_walk_only: false,
        },
        // 3. proc_const: 99 | (x ~> 42)  →  42
        //    The function ignores its argument and returns 42.
        CorpusCase {
            name: "proc_const",
            source: "99 | (x ~> 42)",
            ast: {
                let mut a = Ast::new();
                a.push(AstNode::new("value").with_payload(json!(42))); // 0: body (constant)
                a.push(
                    AstNode::new("function") // 1: x ~> 42
                        .with_payload(json!({"params": ["x"], "body": 0})),
                );
                a.push(AstNode::new("value").with_payload(json!(99))); // 2: left of pipe
                a.push(
                    AstNode::new("pipe") // 3: 99 | fn  →  42
                        .with_payload(json!({"children": [2, 1]})),
                );
                a
            },
            expected: json!(42),
            tree_walk_only: false,
        },
        // 4. proc_pipe_chain: 5 | (x ~> x + 1) | (y ~> y * 2)  →  12
        //    Pipe is left-associative: (5 | (x ~> x + 1)) | (y ~> y * 2)
        //    Inner: 5 | (x ~> x + 1)  →  6.  Outer: 6 | (y ~> y * 2)  →  12.
        CorpusCase {
            name: "proc_pipe_chain",
            source: "5 | (x ~> x + 1) | (y ~> y * 2)",
            ast: {
                let mut a = Ast::new();
                // --- inner function: x ~> x + 1 ---
                a.push(AstNode::new("var").with_payload(json!("x"))); // 0: param x
                a.push(AstNode::new("value").with_payload(json!(1))); // 1: literal 1
                a.push(
                    AstNode::new("binary.add") // 2: body x + 1
                        .with_payload(json!({"children": [0, 1]})),
                );
                a.push(
                    AstNode::new("function") // 3: x ~> x + 1
                        .with_payload(json!({"params": ["x"], "body": 2})),
                );
                // --- outer function: y ~> y * 2 ---
                a.push(AstNode::new("var").with_payload(json!("y"))); // 4: param y
                a.push(AstNode::new("value").with_payload(json!(2))); // 5: literal 2
                a.push(
                    AstNode::new("binary.mul") // 6: body y * 2
                        .with_payload(json!({"children": [4, 5]})),
                );
                a.push(
                    AstNode::new("function") // 7: y ~> y * 2
                        .with_payload(json!({"params": ["y"], "body": 6})),
                );
                // --- pipe chain ---
                a.push(AstNode::new("value").with_payload(json!(5))); // 8: leftmost value
                a.push(
                    AstNode::new("pipe") // 9: inner pipe  5 | (x ~> x+1)  →  6
                        .with_payload(json!({"children": [8, 3]})),
                );
                a.push(
                    AstNode::new("pipe") // 10: outer pipe  6 | (y ~> y*2)  →  12
                        .with_payload(json!({"children": [9, 7]})),
                );
                a
            },
            expected: json!(12),
            tree_walk_only: false,
        },
        // 5. proc_bind_body: 3 | (x ~> do { y = x + 1; y * 2 })  →  8
        //    The function body is a block binding: y = x + 1 = 4, then y * 2 = 8.
        CorpusCase {
            name: "proc_bind_body",
            source: "3 | (x ~> do { y = x + 1; y * 2 })",
            ast: {
                let mut a = Ast::new();
                // --- function body: do { y = x + 1; y * 2 } ---
                a.push(AstNode::new("var").with_payload(json!("x"))); // 0: param x
                a.push(AstNode::new("value").with_payload(json!(1))); // 1: literal 1
                a.push(
                    AstNode::new("binary.add") // 2: x + 1
                        .with_payload(json!({"children": [0, 1]})),
                );
                a.push(AstNode::new("var").with_payload(json!("y"))); // 3: var y
                a.push(AstNode::new("value").with_payload(json!(2))); // 4: literal 2
                a.push(
                    AstNode::new("binary.mul") // 5: y * 2
                        .with_payload(json!({"children": [3, 4]})),
                );
                a.push(
                    AstNode::new("assign") // 6: y = x + 1
                        .with_payload(json!({"children": [3, 2]})),
                );
                a.push(
                    AstNode::new("block") // 7: do { y = x + 1; y * 2 }
                        .with_payload(json!({"children": [6, 5]})),
                );
                a.push(
                    AstNode::new("function") // 8: x ~> do { y = x + 1; y * 2 }
                        .with_payload(json!({"params": ["x"], "body": 7})),
                );
                a.push(AstNode::new("value").with_payload(json!(3))); // 9: left of pipe
                a.push(
                    AstNode::new("pipe") // 10: 3 | fn  →  8
                        .with_payload(json!({"children": [9, 8]})),
                );
                a
            },
            expected: json!(8),
            tree_walk_only: false,
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The corpus is non-empty and every case has a non-empty AST.
    #[test]
    fn corpus_is_nonempty() {
        let c = corpus();
        assert!(c.len() >= 38, "corpus should have at least 38 cases");
        for case in &c {
            assert!(!case.ast.is_empty(), "case '{}' has empty ast", case.name);
        }
    }

    /// The arrow corpus is non-empty and every case has a non-empty AST.
    #[test]
    fn proc_corpus_is_nonempty() {
        let c = proc_corpus();
        assert!(!c.is_empty(), "arrow corpus should have at least one case");
        for case in &c {
            assert!(
                !case.ast.is_empty(),
                "arrow case '{}' has empty ast",
                case.name
            );
        }
    }
}
