//! `flow` (`>>>`) native-op parity test (ADR-0074 follow-up #3).
//!
//! `eval.flow` compiles `lhs >>> rhs` to `!Arr { op: flow, args: [lhs, rhs] }`.
//! The op is implemented per-engine (`prim_v2_flow` / the `flow` arm of each
//! engine's `apply_native`), so this file gates the semantics end-to-end:
//! the input is passed through as a *single* argument (arrays stay arrays),
//! and only a categorical `Pair` (`***`) is destructured into multiple
//! positional args. Runs identical source through tree-walk, bytecode, and
//! cranelift via the generic [`Runtime`] and asserts identical results.

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

/// Basic `>>>`: scalar input applied to a unary arrow callee.
#[test]
fn flow_scalar_to_arrow() {
    assert_all_engines("5 >>> (x ~> x + 1)", json!(6));
}

/// A list input is passed through as the callee's *single* argument —
/// unlike `call`/`App`, `flow` does not unpack arrays.
#[test]
fn flow_list_is_single_arg() {
    assert_all_engines("[1, 2, 3] >>> (xs ~> xs)", json!([1, 2, 3]));
}

/// A categorical `Pair` (`***`) input is destructured into positional args
/// for a multi-arity callee: `a *** b >>> f` → `f(a, b)`.
#[test]
fn flow_pair_destructures() {
    assert_all_engines("(1 *** 2) >>> ((a, b) ~> a + b)", json!(3));
}

/// Right-nested products flatten fully: `a *** b *** c >>> f` → `f(a, b, c)`.
#[test]
fn flow_nested_pair_flattens() {
    assert_all_engines("(1 *** 2 *** 3) >>> ((a, b, c) ~> a + b + c)", json!(6));
}

/// `>>>` composes left-to-right (precedence 25/26): `x >>> f >>> g` is
/// `(x >>> f) >>> g`.
#[test]
fn flow_chains() {
    assert_all_engines("3 >>> (x ~> x + 1) >>> (x ~> x * 2)", json!(8));
}
