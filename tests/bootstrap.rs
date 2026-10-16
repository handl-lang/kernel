//! # bootstrap.rs — ADR-0044 Phase 8 bootstrap test
//!
//! Per ADR-0044 Phase 8 testing: "`compile(handlLanguage, native)` produces a
//! binary that, when run on a corpus, produces the same results as the
//! host-built handl."
//!
//! In Phase 8, "compile" = build a [`CraneliftEngine`] with the
//! self-describing `Language`. The cranelift engine **is** the native
//! compilation (`compile(handlLanguage, native)` in the ADR's terms): it
//! compiles the `Language`'s `Term` data to native code via cranelift and
//! executes it via an in-memory JIT. The per-node scheme lookup
//! (`lang.eval[node.kind]`) is erased at compile time — baked into native
//! code (ADR §7).
//!
//! This test evaluates the self-hosting corpus via the cranelift engine and
//! asserts the results match the tree-walk reference (the host-built handl).
//! This proves the bootstrap path: the self-describing language, compiled to
//! native, produces correct results.
//!
//! ## What's proven vs. deferred
//!
//! **Proven:** the *mechanism* — native compilation of the self-describing
//! language produces correct results matching the reference interpreter, for
//! the migrated subset.
//!
//! **Deferred:** a true "produce a binary" bootstrap (writing a standalone
//! executable to disk that can be run independently of the host process).
//! Phase 8's cranelift engine is an in-memory JIT; emitting a relocatable
//! object file / standalone executable is a future step. The in-memory JIT
//! demonstrates the same compilation pipeline (`Term` → native code with
//! erased data dispatch) that a standalone-binary bootstrap would use.

use handl_defining_handl::{corpus, language};
use handl_plugin_engine_exec::{EvalEngine, EvalRequest};
use handl_plugin_engine_exec_cranelift::CraneliftEngine;
use handl_plugin_engine_exec_tree_walk::TreeWalkEngine;

/// `compile(handlLanguage, native)` (cranelift) produces results matching the
/// host-built handl (tree-walk) for the full corpus, using the
/// emitter-assembled language.
///
/// Tree-walk-only cases (e.g. `binary.pow`) are skipped — their `Prim` op is
/// not yet implemented in the cranelift engine.
#[test]
fn bootstrap_cranelift_matches_tree_walk_emitter_language() {
    let lang = language();
    let tree_walk = TreeWalkEngine::new();
    let cranelift = CraneliftEngine::new();
    for case in corpus() {
        if case.tree_walk_only {
            continue;
        }
        let req = EvalRequest::new(case.ast.clone());
        let tw_result = tree_walk.eval(&lang, &req);
        let cl_result = cranelift.eval(&lang, &req);
        // The native-compiled result matches the reference interpreter.
        assert_eq!(
            cl_result, tw_result,
            "bootstrap: case '{}' ({}) — cranelift diverged from tree-walk",
            case.name, case.source
        );
        // And both match the expected value.
        assert_eq!(
            cl_result.as_ref().unwrap(),
            &case.expected,
            "bootstrap: case '{}' ({}) — result does not match expected",
            case.name,
            case.source
        );
    }
}

/// The bootstrap path works via the `Runtime` abstraction (eval engine
/// selected by `RuntimeConfig { eval: "tree-walk" }` as the reference),
/// confirming the self-describing language binds correctly to a runtime.
///
/// Tree-walk-only cases are skipped — the cranelift engine cannot compile
/// them.
#[test]
fn bootstrap_self_describing_language_binds_to_runtime() {
    use handl_plugin_engine_exec_tree_walk::TreeWalkEngine;
    use handl_plugin_engine_parse_pratt::PrattEngine;
    use handl_runtime::{EngineRegistry, Runtime, RuntimeConfig};
    use std::rc::Rc;
    let lang = language();
    let config = RuntimeConfig::new()
        .with_parse("pratt")
        .with_eval("tree-walk");
    let mut reg = EngineRegistry::new();
    reg.register_parse("pratt", PrattEngine::new());
    reg.register_eval("tree-walk", Box::new(TreeWalkEngine::new()));
    let registry = Rc::new(reg);
    let rt = Runtime::from_registry(lang, &registry, &config).expect("runtime must bind");
    // The runtime-bound tree-walk is the reference; cranelift must match it.
    let cranelift = CraneliftEngine::new();
    // Re-create lang for cranelift (Runtime consumed it).
    let lang2 = language();
    for case in corpus() {
        if case.tree_walk_only {
            continue;
        }
        let rt_result = rt.eval(&case.ast);
        let req = EvalRequest::new(case.ast.clone());
        let cl_result = cranelift.eval(&lang2, &req);
        assert_eq!(
            cl_result, rt_result,
            "bootstrap (runtime): case '{}' ({}) — cranelift diverged from runtime tree-walk",
            case.name, case.source
        );
    }
}
