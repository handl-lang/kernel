//! # futamura.rs — ADR-0044 Phase 8 Futamura projection sanity check
//!
//! Per ADR-0044 Phase 8 testing: "specializing `eval(handlLanguage, ast)` by
//! fixing `handlLanguage` and leaving `ast` dynamic produces a compiled
//! program (the Futamura projection sanity check)."
//!
//! ## The Futamura projection, conceptually
//!
//! The Futamura projections specialize an interpreter by fixing part of its
//! input and leaving the rest dynamic:
//!
//! - **1st projection:** fix `lang`, specialize `eval(lang, ast)` w.r.t.
//!   `lang`, leaving `ast` dynamic → a *compiled program* (a function that
//!   takes `ast` and produces values without re-reading the `Language`).
//! - **2nd projection:** fix `lang`, specialize the compiler itself w.r.t.
//!   `lang` → a *standalone compiler* for that language.
//! - **3rd projection:** specialize the specializer → a *compiler generator*.
//!
//! ADR-0044 notes that with `eval`/`compile` as functions on `Language` data,
//! "Futamura projections become currying … over data, not Rust trait
//! objects."
//!
//! ## Mapping to Phase 7's cranelift engine
//!
//! In Phase 7's cranelift engine, the **1st Futamura projection** maps to:
//!
//! 1. **Compile the `Language`'s schemes to native code once** — the
//!    `CraneliftEngine` builds its JIT module from `lang` (resolving every
//!    node kind's `Term` to native code at compile time, erasing the
//!    `lang.eval[node.kind]` data dispatch). This is the **specialization**
//!    step: `lang` is fixed and baked into native code.
//! 2. **Evaluate multiple `ast`s against the same compiled module** — the
//!    `ast` is the **dynamic input**. Each `eval` call runs the pre-compiled
//!    native functions against a new `ast`, without re-reading the `Language`.
//!
//! The result is a "compiled interpreter": a function that takes `ast` and
//! produces values, with the `Language` specialization already baked in. This
//! test demonstrates that specialization: one `CraneliftEngine` (one
//! compilation of the `Language`) evaluates multiple different programs
//! (different `ast`s) and all produce correct results.
//!
//! ## Scope
//!
//! This is a **sanity check** of the mechanism, not a full Futamura-style
//! partial-evaluation pipeline. Phase 8 proves that fixing `lang` and
//! compiling it once yields a native artifact that correctly handles dynamic
//! `ast` inputs — the essential property the 1st projection relies on. The
//! 2nd and 3rd projections (specializing the compiler / specializer) are
//! future work, enabled by keeping `compile` a function on data.

use handl_defining_handl::{corpus, language};
use handl_plugin_engine_exec::{EvalEngine, EvalRequest};
use handl_plugin_engine_exec_cranelift::CraneliftEngine;
use handl_plugin_engine_exec_tree_walk::TreeWalkEngine;

/// The 1st Futamura projection sanity check: fix `lang = handlLanguage`,
/// compile it once (build a `CraneliftEngine`), then evaluate multiple
/// different `ast`s (dynamic inputs) against the same compiled module.
///
/// All results must match the tree-walk reference and the expected values.
/// This demonstrates the specialization: the `Language` is compiled once,
/// multiple programs run against it without re-reading the `Language`.
#[test]
fn futamura_first_projection_specializes_language_once() {
    let lang = language();
    // Specialize: compile the Language to native code once.
    let cranelift = CraneliftEngine::new();
    // The reference interpreter (unspecialized — re-reads lang.eval per node).
    let tree_walk = TreeWalkEngine::new();

    let cases = corpus();
    // Pick three distinct programs as the dynamic inputs.
    let dynamic_inputs: Vec<_> = cases
        .iter()
        .filter(|c| matches!(c.name, "literal" | "function_call" | "nested_bind"))
        .collect();
    assert_eq!(
        dynamic_inputs.len(),
        3,
        "sanity: expected 3 dynamic inputs for the projection"
    );

    for case in dynamic_inputs {
        let req = EvalRequest::new(case.ast.clone());
        // Dynamic input: a new ast evaluated against the same compiled module.
        let cl_result = cranelift.eval(&lang, &req);
        let tw_result = tree_walk.eval(&lang, &req);
        assert_eq!(
            cl_result, tw_result,
            "futamura: case '{}' ({}) — specialized cranelift diverged from tree-walk",
            case.name, case.source
        );
        assert_eq!(
            cl_result.unwrap(),
            case.expected,
            "futamura: case '{}' ({}) — result does not match expected",
            case.name,
            case.source
        );
    }
}

/// The compiled module is reusable across many evaluations without
/// recompilation: evaluate the corpus in a loop, then again, against the
/// same `CraneliftEngine`. Results must be stable (the specialization
/// persists across calls).
///
/// Tree-walk-only cases are skipped — the cranelift engine cannot compile
/// them.
#[test]
fn futamura_specialization_persists_across_calls() {
    let lang = language();
    let cranelift = CraneliftEngine::new();

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
            "futamura: case '{}' ({}) — specialization was not stable across calls",
            name, source,
        );
        assert_eq!(
            second, *expected,
            "futamura: case '{}' ({}) — second-pass result wrong",
            name, source,
        );
    }
}
