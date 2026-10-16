//! # self_host.rs — ADR-0044 Phase 8 self-hosting test
//!
//! Per ADR-0044 Phase 8 testing: "load `handl-defining-handl` as a `Language`
//! value, `eval(handlLanguage, ast)` produces the same result as the
//! host-built handl for a corpus of programs."
//!
//! This test loads the self-describing `Language` (via [`language`]) and
//! evaluates the self-hosting corpus under all three eval engines (tree-walk,
//! bytecode, cranelift). All engines must agree with the expected results —
//! proving the self-describing language can evaluate its own constructs.
//!
//! ## Scope
//!
//! The corpus covers the data-driven constructs that all three engines can
//! evaluate: value, var, the binary arithmetic / comparison ops (add, sub,
//! mul, div, pow, eq, neq, lt, gt, lte, gte, compare), typeof, unary not,
//! block bindings (`do { x = v; ... }`), if, ternary, function, call, pipe, paren,
//! apply, mood, type-annot, array, object, index, assign. Cases flagged via
//! [`CorpusCase::tree_walk_only`] (if any) use a `Prim` op implemented in
//! the tree-walk engine but not yet in the bytecode or cranelift engines;
//! they are run under tree-walk only and skipped by the compiled-engine
//! tests. Currently no corpus case is tree-walk-only.
//!
//! Constructs that dispatch to `Foreign` host functions (match, handle, flow,
//! fanout, field-access, import, export, module, template, resolve, json,
//! hello.greet) are **not** in the corpus — they remain blocked until the
//! engines gain support. This test proves the **mechanism** with honest
//! coverage: a `Language` value can describe a language and be evaluated
//! under itself across all three engines.

use handl_defining_handl::{corpus, language};
use handl_language::LangError;
use handl_plugin_engine_exec::{EvalEngine, EvalRequest};
use handl_plugin_engine_exec_bytecode::BytecodeEngine;
use handl_plugin_engine_exec_cranelift::CraneliftEngine;
use handl_plugin_engine_exec_tree_walk::TreeWalkEngine;
use handl_plugin_engine_parse_pratt::PrattEngine;
use handl_runtime::{EngineRegistry, Runtime, RuntimeConfig};
use std::rc::Rc;

/// Build a registry with the pratt parser + tree-walk eval engine (the
/// engines needed by the `Runtime`-based tests).
fn test_registry() -> Rc<EngineRegistry> {
    let mut reg = EngineRegistry::new();
    reg.register_parse("pratt", PrattEngine::new());
    reg.register_eval("tree-walk", Box::new(TreeWalkEngine::new()));
    Rc::new(reg)
}

/// Evaluate a corpus case under a `Runtime` (tree-walk or bytecode, selected
/// via `RuntimeConfig`) and return the result.
fn eval_with_runtime(
    lang: &handl_language::Language,
    config: &RuntimeConfig,
    ast: &handl_language::Ast,
) -> Result<handl_language::Value, LangError> {
    let registry = test_registry();
    let rt = Runtime::from_registry(lang.clone(), &registry, config)?;
    rt.eval(ast)
}

/// The emitter-assembled self-describing language evaluates the corpus
/// correctly under the tree-walk engine (the reference interpreter).
///
/// This runs **all** corpus cases, including the tree-walk-only ones.
#[test]
fn self_host_tree_walk_emitter_language() {
    let lang = language();
    let config = RuntimeConfig::new()
        .with_parse("pratt")
        .with_eval("tree-walk");
    for case in corpus() {
        let result = eval_with_runtime(&lang, &config, &case.ast);
        assert_eq!(
            result.unwrap(),
            case.expected,
            "tree-walk / emitter-lang: case '{}' ({}) failed",
            case.name,
            case.source
        );
    }
}

/// The self-describing language evaluates the corpus correctly under the
/// bytecode engine.
///
/// Tree-walk-only cases (if any) are skipped — their `Prim` op is not yet
/// implemented in the bytecode engine.
#[test]
fn self_host_bytecode_emitter_language() {
    let lang = language();
    let engine = BytecodeEngine::new();
    for case in corpus() {
        if case.tree_walk_only {
            continue;
        }
        let req = EvalRequest::new(case.ast.clone());
        let result = engine.eval(&lang, &req);
        assert_eq!(
            result.unwrap(),
            case.expected,
            "bytecode / emitter-lang: case '{}' ({}) failed",
            case.name,
            case.source
        );
    }
}

/// The self-describing language evaluates the corpus correctly under the
/// cranelift (native) engine.
///
/// Tree-walk-only cases (if any) are skipped — their `Prim` op is not yet
/// implemented in the cranelift engine.
#[test]
fn self_host_cranelift_emitter_language() {
    let lang = language();
    let engine = CraneliftEngine::new();
    for case in corpus() {
        if case.tree_walk_only {
            continue;
        }
        let req = EvalRequest::new(case.ast.clone());
        let result = engine.eval(&lang, &req);
        assert_eq!(
            result.unwrap(),
            case.expected,
            "cranelift / emitter-lang: case '{}' ({}) failed",
            case.name,
            case.source
        );
    }
}

/// All three eval engines agree on the self-hosted corpus (emitter language).
///
/// This is the cross-engine conformance gate scoped to the self-hosting
/// corpus: tree-walk, bytecode, and cranelift must produce identical results
/// for every non-tree-walk-only case.
#[test]
fn all_three_engines_agree_emitter_language() {
    let lang = language();
    let tw = TreeWalkEngine::new();
    let bc = BytecodeEngine::new();
    let cl = CraneliftEngine::new();
    for case in corpus() {
        if case.tree_walk_only {
            continue;
        }
        let req = EvalRequest::new(case.ast.clone());
        let tw_res = tw.eval(&lang, &req);
        let bc_res = bc.eval(&lang, &req);
        let cl_res = cl.eval(&lang, &req);
        assert_eq!(
            tw_res, bc_res,
            "case '{}': tree-walk and bytecode diverged",
            case.name
        );
        assert_eq!(
            tw_res, cl_res,
            "case '{}': tree-walk and cranelift diverged",
            case.name
        );
        assert_eq!(
            tw_res.unwrap(),
            case.expected,
            "case '{}': result does not match expected",
            case.name
        );
    }
}

/// The tree-walk-only corpus cases (if any) produce correct results under
/// the tree-walk engine. These cases use `Prim` ops not yet implemented in
/// the bytecode or cranelift engines; they are excluded from the
/// compiled-engine conformance gates above. When no tree-walk-only cases
/// remain (all `Prim` ops are implemented in every engine), this test is a
/// no-op.
#[test]
fn self_host_tree_walk_only_cases() {
    let lang = language();
    let tw = TreeWalkEngine::new();
    let mut ran = 0;
    for case in corpus() {
        if !case.tree_walk_only {
            continue;
        }
        let req = EvalRequest::new(case.ast.clone());
        let result = tw.eval(&lang, &req);
        assert_eq!(
            result.unwrap(),
            case.expected,
            "tree-walk-only: case '{}' ({}) failed",
            case.name,
            case.source
        );
        ran += 1;
    }
    // No assertion on `ran`: the corpus may legitimately have zero
    // tree-walk-only cases once every `Prim` op is implemented in all engines.
    let _ = ran;
}
