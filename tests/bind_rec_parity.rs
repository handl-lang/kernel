//! Block-binding / `rec` parity test (ADR-0074, ADR-0052).
//!
//! Runs real source programs that exercise block binding (`do { x = v; ... }`),
//! update-or-define `assign` semantics, and the `rec` fixpoint region that the
//! `while`/`do-while`/`for` desugars produce — through all three eval engines
//! (tree-walk, bytecode, cranelift) via the generic [`Runtime`]. The desugar
//! pass runs at parse time ([`Runtime::parse`]), so the compiled engines see
//! exactly the `rec` + `assign` structures the tree-walk engine sees.
//!
//! This is the compiled-engine coverage gate for the desugared language:
//! `x = y` inside a nested block must update the nearest enclosing binding
//! (the `while`/`for` desugars' `__continue`/`__xs` feedback wires depend on
//! it), and `rec` fixpoint convergence must observe those cross-scope writes
//! (`ScopeStack::enclosing_updated` + the end-of-pass env comparison).

use handl_defining_handl::language;
use handl_language::{Source, Value};
use handl_plugin_engine_exec::EvalEngine;
use handl_plugin_engine_exec_bytecode::BytecodeEngine;
use handl_plugin_engine_exec_cranelift::CraneliftEngine;
use handl_plugin_engine_exec_tree_walk::TreeWalkEngine;
use handl_plugin_engine_lex_pattern::DataLexerEngine;
use handl_plugin_engine_parse_pratt::PrattEngine;
use handl_runtime::Runtime;
use serde_json::json;

/// Build a `Runtime` bound to the given eval engine (shared canonical
/// language, data lexer, Pratt parser — so `desugar` runs at parse time).
fn runtime_with(eval: Box<dyn EvalEngine>) -> Runtime {
    Runtime::new(language())
        .with_lex_engine(Box::new(DataLexerEngine::new()))
        .with_parse_engine(PrattEngine::new())
        .with_eval_engine(eval)
}

/// Run `src` through all three engines and assert identical results equal
/// to `expected`.
fn assert_all_engines(src: &str, expected: Value) {
    let engines: Vec<(&'static str, Box<dyn EvalEngine>)> = vec![
        ("tree-walk", Box::new(TreeWalkEngine::new())),
        ("bytecode", Box::new(BytecodeEngine::new())),
        ("cranelift", Box::new(CraneliftEngine::new())),
    ];
    for (name, engine) in engines {
        let rt = runtime_with(engine);
        let got = rt
            .run(&Source::new(src))
            .unwrap_or_else(|e| panic!("{name}: `{src}` failed: {e}"));
        assert_eq!(got, expected, "{name}: `{src}` diverged");
    }
}

/// `do {}` block binding: define-then-read.
#[test]
fn block_bind_define() {
    assert_all_engines("do { x = 5; x }", json!(5));
}

/// Update-or-define: an `assign` inside a nested block updates the nearest
/// enclosing binding rather than shadowing it.
#[test]
fn block_bind_updates_enclosing() {
    assert_all_engines("do { x = 1; do { x = x + 1 }; x }", json!(2));
}

/// Same-scope rebinding inside one block.
#[test]
fn block_bind_rebind_same_scope() {
    assert_all_engines("do { x = 1; x = x + 1; x = x * 3; x }", json!(6));
}

/// `while cond { body }` desugars to a `rec` region whose `__continue`
/// feedback wire is written from inside the `if` branch block — requires
/// both cross-scope `assign` and `rec` fixpoint convergence.
#[test]
fn while_desugar_rec_parity() {
    assert_all_engines("do { x = 0; while x < 3 { x = x + 1 }; x }", json!(3));
}

/// `while` with a multi-statement body (`KeepRest` tail).
#[test]
fn while_desugar_multi_stmt_body() {
    assert_all_engines(
        "do { x = 0; y = 0; while x < 3 { x = x + 1; y = y + 2 }; x + y }",
        json!(9),
    );
}

/// `do { body } while cond` runs the body once before testing.
#[test]
fn do_while_desugar_rec_parity() {
    assert_all_engines("do { x = 0; do { x = x + 1 } while x < 3; x }", json!(3));
}

/// `for x in xs { body }` desugars to `block { __xs = xs; __result = [];
/// rec { … match __xs … } }` — the `__xs` cursor is written back from
/// inside the `match` arm's block, the deepest cross-scope `assign` case.
#[test]
fn for_desugar_rec_parity() {
    assert_all_engines(
        "do { t = 0; for x in [1, 2, 3] { t = t + x }; t }",
        json!(6),
    );
}
