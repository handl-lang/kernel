//! # futamura_v2.rs — ADR-0052 Phase D v2 Futamura projection tests
//!
//! The 1st Futamura projection on the **v2 arrow kernel**: fix `lang`,
//! compile it once via `CraneliftEngineV2`, then evaluate multiple
//! different `ast`s against the same compiled module. Results must match
//! the v2 tree-walk reference (`V2Interpreter`) and the expected values.
//!
//! This mirrors the v1 `futamura.rs` tests but uses the v2 engines
//! (`CraneliftEngineV2`, `V2Interpreter`). The v2 tree-walk handler does
//! not implement `EvalEngine`; it is invoked via the same adapter pattern
//! used in `v2_parity.rs` (fresh `ScopeStack`, root = last arena node).
//!
//! ADR-0052 Phase D also adds the arrow-authored corpus
//! ([`proc_corpus`]): programs authored using `x ~> body` notation.
//! The `v2_futamura_proc_corpus` test runs these through
//! `CraneliftEngineV2`, proving the arrow-authored bootstrap works on the
//! v2 arrow kernel.

use handl_defining_handl::{corpus, language, proc_corpus};
use handl_language::{AstRef, LangError, Value};
use handl_plugin_engine_exec::{EvalEngine, EvalRequest};
use handl_plugin_engine_exec_cranelift::CraneliftEngineV2;
use handl_plugin_engine_exec_tree_walk::ScopeStack;
use handl_plugin_engine_exec_tree_walk::v2::V2Interpreter;

/// Evaluate a corpus case under the v2 tree-walk handler (`V2Interpreter`).
///
/// Mirrors the adapter in `v2_parity.rs`: a fresh `ScopeStack`, root =
/// last node in the arena (Pratt convention). `V2Interpreter` does not
/// implement `EvalEngine`, so this bridges it to the same
/// `Result<Value, LangError>` shape.
fn eval_v2_tree_walk(
    engine: &V2Interpreter,
    lang: &handl_language::Language,
    req: &EvalRequest,
) -> Result<Value, LangError> {
    let ast = &req.ast;
    if ast.is_empty() {
        return Ok(Value::Null);
    }
    let mut env = ScopeStack::new();
    let root_ref = AstRef::new(ast.len() - 1);
    engine.eval_node_v2(ast, root_ref, lang, &mut env)
}

/// The 1st Futamura projection on the v2 arrow kernel: fix `lang =
/// handlLanguage`, compile it once (build a `CraneliftEngineV2`), then
/// evaluate multiple different `ast`s (dynamic inputs) against the same
/// compiled module.
///
/// All results must match the v2 tree-walk reference and the expected
/// values. This demonstrates the v2 specialization: the `Language` is
/// compiled once, multiple programs run against it without re-reading the
/// `Language`.
#[test]
fn v2_futamura_first_projection_specializes_language_once() {
    let lang = language();
    // Specialize: compile the Language to native code once (v2 kernel).
    let cranelift = CraneliftEngineV2::new();
    // The v2 reference interpreter (unspecialized).
    let tree_walk = V2Interpreter::new();

    let cases = corpus();
    // Pick three distinct programs as the dynamic inputs.
    let dynamic_inputs: Vec<_> = cases
        .iter()
        .filter(|c| matches!(c.name, "literal" | "function_call" | "nested_bind"))
        .collect();
    assert_eq!(
        dynamic_inputs.len(),
        3,
        "sanity: expected 3 dynamic inputs for the projection",
    );

    for case in dynamic_inputs {
        let req = EvalRequest::new(case.ast.clone());
        // Dynamic input: a new ast evaluated against the same compiled module.
        let cl_result = cranelift.eval(&lang, &req);
        let tw_result = eval_v2_tree_walk(&tree_walk, &lang, &req);
        assert_eq!(
            cl_result, tw_result,
            "v2 futamura: case '{}' ({}) — specialized cranelift diverged from tree-walk",
            case.name, case.source,
        );
        assert_eq!(
            cl_result.unwrap(),
            case.expected,
            "v2 futamura: case '{}' ({}) — result does not match expected",
            case.name,
            case.source,
        );
    }
}

/// The v2 compiled module is reusable across many evaluations without
/// recompilation: evaluate the corpus in a loop, then again, against the
/// same `CraneliftEngineV2`. Results must be stable (the specialization
/// persists across calls).
///
/// Tree-walk-only cases are skipped — the cranelift engine cannot compile
/// them.
#[test]
fn v2_futamura_specialization_persists_across_calls() {
    let lang = language();
    let cranelift = CraneliftEngineV2::new();

    // First pass: evaluate every non-tree-walk-only corpus case.
    let mut pass1 = Vec::new();
    for case in corpus() {
        if case.tree_walk_only {
            continue;
        }
        let req = EvalRequest::new(case.ast.clone());
        pass1.push((
            case.name,
            case.source,
            case.expected.clone(),
            cranelift.eval(&lang, &req).unwrap(),
        ));
    }
    // Second pass: the same compiled module handles the same inputs again.
    let mut idx = 0;
    for case in corpus() {
        if case.tree_walk_only {
            continue;
        }
        let (name, source, expected, first) = &pass1[idx];
        idx += 1;
        let req = EvalRequest::new(case.ast.clone());
        let second = cranelift.eval(&lang, &req).unwrap();
        assert_eq!(
            &second, first,
            "v2 futamura: case '{}' ({}) — specialization was not stable across calls",
            name, source,
        );
        assert_eq!(
            second, *expected,
            "v2 futamura: case '{}' ({}) — second-pass result wrong",
            name, source,
        );
    }
}

/// The arrow-authored corpus runs through `CraneliftEngineV2` and
/// produces the expected results. This proves the arrow-authored bootstrap
/// (arrow-calculus authoring surface) works on the v2 arrow kernel.
///
/// Each arrow case uses a `function` node applied via `pipe`. The v2
/// cranelift engine must compile and evaluate these correctly.
#[test]
fn v2_futamura_proc_corpus() {
    let lang = language();
    let cranelift = CraneliftEngineV2::new();
    let tree_walk = V2Interpreter::new();

    let cases = proc_corpus();
    assert!(
        !cases.is_empty(),
        "arrow corpus should have at least one case",
    );

    for case in &cases {
        let req = EvalRequest::new(case.ast.clone());
        let cl_result = cranelift.eval(&lang, &req);
        let tw_result = eval_v2_tree_walk(&tree_walk, &lang, &req);
        assert_eq!(
            cl_result, tw_result,
            "v2 futamura arrow: case '{}' ({}) — cranelift diverged from tree-walk",
            case.name, case.source,
        );
        assert_eq!(
            cl_result.unwrap(),
            case.expected,
            "v2 futamura arrow: case '{}' ({}) — result does not match expected",
            case.name,
            case.source,
        );
    }
}
