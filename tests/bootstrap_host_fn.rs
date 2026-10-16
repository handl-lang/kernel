//! # bootstrap_host_fn.rs — end-to-end bootstrap via handl-level host fns
//!
//! ADR-0041 §5: "The bootstrap is a compilation step, not interpretation."
//! `compile(handl, "native")` should produce the self-hosting compiler.
//!
//! Unlike `bootstrap.rs` (which calls `CraneliftEngine::eval` directly via
//! the Rust engine API), this test drives the bootstrap through the
//! **handl-level** `compile` / `run_compiled` host functions exposed by the
//! `plugin-lib-lang-*` crates (`CompileModule` / `RunCompiledModule`). It:
//!
//! 1. Loads the self-describing `Language` value ([`language`]).
//! 2. Serializes a corpus case's [`Ast`] to a JSON value (the `ast` argument).
//! 3. Builds a handl AST that calls `compile(lang_value, ast_value, "native")`
//!    via a `foreign.compile` node, and evaluates it under a `Runtime` with
//!    the meta chain attached — obtaining a compiled-program handle.
//! 4. Builds a handl AST that calls `run_compiled(handle)` via a
//!    `foreign.run_compiled` node, and evaluates it — obtaining the result.
//! 5. Asserts the result matches `eval(lang, ast)` (the tree-walk reference).
//!
//! This proves the bootstrap works through the handl-level API, not just the
//! Rust engine API. The test runs for both `"native"` and `"bytecode"`
//! targets. Tree-walk-only corpus cases (e.g. `binary.pow`) are skipped —
//! their `Prim` op is not yet implemented in the compiled engines.

use handl_defining_handl::{corpus, language};
use handl_language::{Ast, AstNode, Language, Value, language_value};
use handl_platform::ModuleLookup;
use handl_plugin_engine_exec_bytecode::BytecodeCompileEngine;
use handl_plugin_engine_exec_cranelift::CraneliftCompileEngine;
use handl_plugin_engine_exec_tree_walk::TreeWalkEngine;
use handl_plugin_engine_lex_pattern::DataLexerEngine;
use handl_plugin_engine_parse_pratt::PrattEngine;
use handl_plugin_lib_lang_compile::CompileModule;
use handl_plugin_lib_lang_eval::EvalModule;
use handl_plugin_lib_lang_lex::LexModule;
use handl_plugin_lib_lang_parse::ParseModule;
use handl_plugin_lib_lang_run_compiled::RunCompiledModule;
use handl_runtime::{EngineRegistry, Runtime, RuntimeConfig, RuntimeFactoryImpl};
use serde_json::json;
use std::collections::HashMap;
use std::rc::Rc;

/// Build the default engine registry for tests: data lexer, pratt parser,
/// tree-walk eval, bytecode/cranelift compile engines.
fn test_registry() -> Rc<EngineRegistry> {
    let mut reg = EngineRegistry::new();
    reg.register_lex("data", Box::new(DataLexerEngine::new()));
    reg.register_parse("pratt", PrattEngine::new());
    reg.register_eval("tree-walk", Box::new(TreeWalkEngine::new()));
    reg.register_compile("bytecode", Box::new(BytecodeCompileEngine::new()));
    reg.register_compile("native", Box::new(CraneliftCompileEngine::new()));
    Rc::new(reg)
}

/// Build a `Runtime` for the self-describing `Language` with the meta chain
/// (the 5 `plugin-lib-lang-*` modules) attached and `self` injected as a
/// global.
fn make_runtime(lang: Language) -> Runtime {
    let config = RuntimeConfig::new()
        .with_lex("data")
        .with_parse("pratt")
        .with_eval("tree-walk");
    let registry = test_registry();
    let self_val = language_value(&lang);

    // Build the meta chain from the 5 plugin-lib-lang-* crates
    // (ADR-0047 §1). The factory's meta_chain is set after construction,
    // breaking the chicken-and-egg. Delegate is None (no user host fns).
    let factory = Rc::new(RuntimeFactoryImpl::new(
        Rc::clone(&registry),
        config.clone(),
    ));
    let factory_dyn: Rc<dyn handl_runtime::RuntimeFactory> =
        Rc::clone(&factory) as Rc<dyn handl_runtime::RuntimeFactory>;
    let run_compiled_mod = Rc::new(RunCompiledModule::new(Rc::clone(&factory_dyn), None));
    let compile_mod = Rc::new(CompileModule::new(
        Rc::clone(&factory_dyn),
        Some(Rc::clone(&run_compiled_mod) as Rc<dyn ModuleLookup>),
    ));
    let eval_mod = Rc::new(EvalModule::new(
        Rc::clone(&factory_dyn),
        Some(Rc::clone(&compile_mod) as Rc<dyn ModuleLookup>),
    ));
    let parse_mod = Rc::new(ParseModule::new(
        Rc::clone(&factory_dyn),
        Some(Rc::clone(&eval_mod) as Rc<dyn ModuleLookup>),
    ));
    let lex_mod = Rc::new(LexModule::new(
        Rc::clone(&factory_dyn),
        Some(Rc::clone(&parse_mod) as Rc<dyn ModuleLookup>),
    ));
    let meta_chain: Rc<dyn ModuleLookup> = lex_mod;
    factory.set_meta_chain(Rc::clone(&meta_chain));

    let mut globals = HashMap::new();
    globals.insert("self".to_string(), self_val);
    Runtime::from_registry_with_globals(lang, &registry, &config, Some(meta_chain), Some(&globals))
        .expect("runtime must build")
}

/// `compile(lang, ast, target)` via the `foreign.compile` host fn.
fn compile_via_host_fn(
    runtime: &Runtime,
    lang_val: &Value,
    ast_val: &Value,
    target: &str,
) -> Value {
    let mut ast = Ast::new();
    ast.push(AstNode::new("value").with_payload(lang_val.clone()));
    ast.push(AstNode::new("value").with_payload(ast_val.clone()));
    ast.push(AstNode::new("value").with_payload(json!(target)));
    ast.push(AstNode::new("foreign.compile").with_payload(json!({"children": [0, 1, 2]})));
    runtime.eval(&ast).expect("compile must succeed")
}

/// `run_compiled(handle)` via the `foreign.run_compiled` host fn.
fn run_compiled_via_host_fn(runtime: &Runtime, handle: &Value) -> Value {
    let mut ast = Ast::new();
    ast.push(AstNode::new("value").with_payload(handle.clone()));
    ast.push(AstNode::new("foreign.run_compiled").with_payload(json!({"children": [0]})));
    runtime.eval(&ast).expect("run_compiled must succeed")
}

/// `eval(lang, ast)` via the `foreign.eval` host fn (tree-walk reference).
fn eval_via_host_fn(runtime: &Runtime, lang_val: &Value, ast_val: &Value) -> Value {
    let mut ast = Ast::new();
    ast.push(AstNode::new("value").with_payload(lang_val.clone()));
    ast.push(AstNode::new("value").with_payload(ast_val.clone()));
    ast.push(AstNode::new("foreign.eval").with_payload(json!({"children": [0, 1]})));
    runtime.eval(&ast).expect("eval must succeed")
}

/// The end-to-end bootstrap via handl-level `compile` / `run_compiled` host
/// functions, targeting **native** (cranelift). For each non-tree-walk-only
/// corpus case: compile the case's AST under the self-describing language,
/// run the compiled program, and assert the result matches `eval(lang, ast)`.
#[test]
fn bootstrap_host_fn_native_matches_eval() {
    let lang = language();
    let lang_val = language_value(&lang);
    let runtime = make_runtime(lang.clone());

    for case in corpus() {
        if case.tree_walk_only {
            continue;
        }
        let ast_val = serde_json::to_value(&case.ast).expect("serialize ast");

        let handle = compile_via_host_fn(&runtime, &lang_val, &ast_val, "native");
        assert!(
            !handle.is_string(),
            "compile should return a handle, not a stub string, got: {}",
            handle
        );
        let compiled_result = run_compiled_via_host_fn(&runtime, &handle);
        let eval_result = eval_via_host_fn(&runtime, &lang_val, &ast_val);

        assert_eq!(
            compiled_result, eval_result,
            "bootstrap host-fn (native): case '{}' ({}) — run_compiled diverged from eval",
            case.name, case.source
        );
        assert_eq!(
            compiled_result, case.expected,
            "bootstrap host-fn (native): case '{}' ({}) — result does not match expected",
            case.name, case.source
        );
    }
}

/// The end-to-end bootstrap via handl-level `compile` / `run_compiled` host
/// functions, targeting **bytecode**. Same assertions as the native test.
#[test]
fn bootstrap_host_fn_bytecode_matches_eval() {
    let lang = language();
    let lang_val = language_value(&lang);
    let runtime = make_runtime(lang.clone());

    for case in corpus() {
        if case.tree_walk_only {
            continue;
        }
        let ast_val = serde_json::to_value(&case.ast).expect("serialize ast");

        let handle = compile_via_host_fn(&runtime, &lang_val, &ast_val, "bytecode");
        assert!(
            !handle.is_string(),
            "compile should return a handle, not a stub string, got: {}",
            handle
        );
        let compiled_result = run_compiled_via_host_fn(&runtime, &handle);
        let eval_result = eval_via_host_fn(&runtime, &lang_val, &ast_val);

        assert_eq!(
            compiled_result, eval_result,
            "bootstrap host-fn (bytecode): case '{}' ({}) — run_compiled diverged from eval",
            case.name, case.source
        );
        assert_eq!(
            compiled_result, case.expected,
            "bootstrap host-fn (bytecode): case '{}' ({}) — result does not match expected",
            case.name, case.source
        );
    }
}
