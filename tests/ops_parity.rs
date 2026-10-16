//! Native op parity tests for newly-unified canonical eval schemes.
//!
//! Drives real handl source through tree-walk, bytecode, and cranelift and
//! asserts identical results, mirroring `flow_parity.rs` (ADR-0074 follow-up).

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
/// language, data lexer, Pratt parser).
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

/// `export` is a pass-through: the value of its child expression is returned.
#[test]
fn export_passes_through_child() {
    assert_all_engines("export 42", json!(42));
}
