//! v1-vs-v2 parity test (ADR-0052).
//!
//! Runs the full self-hosting corpus through all six eval engines
//! (v1: tree-walk, bytecode, cranelift; v2: V2Interpreter, BytecodeEngineV2,
//! CraneliftEngineV2) and asserts they produce identical results for every
//! case. This is the parity gate for the v2 cutover.
//!
//! `V2Interpreter` (the v2 tree-walk handler) does not implement `EvalEngine`;
//! it exposes `eval_node_v2` directly. It is invoked via a small adapter that
//! mirrors `TreeWalkEngine::eval` (fresh `ScopeStack`, root = last arena node).
//! `BytecodeEngineV2` and `CraneliftEngineV2` both implement `EvalEngine` and
//! are driven through the trait like their v1 counterparts.

use handl_defining_handl::{corpus, language};
use handl_language::{AstRef, LangError, Value};
use handl_plugin_engine_exec::{EvalEngine, EvalRequest};
use handl_plugin_engine_exec_bytecode::{BytecodeEngine, BytecodeEngineV2};
use handl_plugin_engine_exec_cranelift::{CraneliftEngine, CraneliftEngineV2};
use handl_plugin_engine_exec_tree_walk::v2::V2Interpreter;
use handl_plugin_engine_exec_tree_walk::{ScopeStack, TreeWalkEngine};

/// Evaluate a corpus case under the v2 tree-walk handler (`V2Interpreter`).
///
/// Mirrors `TreeWalkEngine::eval`: a fresh `ScopeStack`, root = last node in
/// the arena (Pratt convention). `V2Interpreter` does not implement
/// `EvalEngine`, so this adapter bridges it to the same
/// `Result<Value, LangError>` shape used by the other engines.
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

/// A labelled engine result for parity comparison.
struct EngineResult {
    /// The engine name (e.g. `"v1-tree-walk"`).
    name: &'static str,
    /// The evaluation outcome.
    result: Result<Value, LangError>,
}

/// Run a single corpus case through the selected engines and collect the
/// labelled results.
fn run_case(
    case: &handl_defining_handl::CorpusCase,
    lang: &handl_language::Language,
    v1_tw: &TreeWalkEngine,
    v1_bc: &BytecodeEngine,
    v1_cl: &CraneliftEngine,
    v2_tw: &V2Interpreter,
    v2_bc: &BytecodeEngineV2,
    v2_cl: &CraneliftEngineV2,
    tree_walk_only: bool,
) -> Vec<EngineResult> {
    let req = EvalRequest::new(case.ast.clone());

    let v1_tw_res = v1_tw.eval(lang, &req);
    let v2_tw_res = eval_v2_tree_walk(v2_tw, lang, &req);

    let mut out = vec![
        EngineResult {
            name: "v1-tree-walk",
            result: v1_tw_res,
        },
        EngineResult {
            name: "v2-tree-walk",
            result: v2_tw_res,
        },
    ];

    if !tree_walk_only {
        out.push(EngineResult {
            name: "v1-bytecode",
            result: v1_bc.eval(lang, &req),
        });
        out.push(EngineResult {
            name: "v1-cranelift",
            result: v1_cl.eval(lang, &req),
        });
        out.push(EngineResult {
            name: "v2-bytecode",
            result: v2_bc.eval(lang, &req),
        });
        out.push(EngineResult {
            name: "v2-cranelift",
            result: v2_cl.eval(lang, &req),
        });
    }

    out
}

/// All six eval engines agree on the self-hosting corpus (ADR-0052 parity
/// gate).
///
/// For every corpus case:
/// - All engines that run the case (tree-walk engines always; compiled
///   engines only when `tree_walk_only` is false) must produce the same
///   result — either all `Ok` with equal values, or all `Err`.
/// - When the engines succeed, the result must match `case.expected`.
///
/// Any divergence is collected and reported at the end with the case name
/// and the per-engine results, so a failure pinpoints exactly which engines
/// diverged and how.
#[test]
fn v1_v2_parity_all_engines_agree() {
    let lang = language();
    let cases = corpus();

    let v1_tw = TreeWalkEngine::new();
    let v1_bc = BytecodeEngine::new();
    let v1_cl = CraneliftEngine::new();
    let v2_tw = V2Interpreter::new();
    let v2_bc = BytecodeEngineV2::new();
    let v2_cl = CraneliftEngineV2::new();

    let mut failures: Vec<String> = Vec::new();
    let mut cases_run = 0usize;

    for case in &cases {
        cases_run += 1;
        let results = run_case(
            case,
            &lang,
            &v1_tw,
            &v1_bc,
            &v1_cl,
            &v2_tw,
            &v2_bc,
            &v2_cl,
            case.tree_walk_only,
        );

        // Compare every engine against the first (the reference for this
        // case). Two results "agree" when both are Ok with equal values or
        // both are Err.
        let reference = &results[0];
        for r in &results {
            let agrees = match (&reference.result, &r.result) {
                (Ok(a), Ok(b)) => a == b,
                (Err(_), Err(_)) => true,
                _ => false,
            };
            if !agrees {
                failures.push(format!(
                    "case '{}' ({}): {} produced {:?}, {} produced {:?}",
                    case.name, case.source, reference.name, reference.result, r.name, r.result
                ));
            }
        }

        // When the reference engine succeeded, the value must match the
        // corpus expected value.
        if let Ok(v) = &reference.result {
            if v != &case.expected {
                failures.push(format!(
                    "case '{}' ({}): expected {}, got {}",
                    case.name, case.source, case.expected, v
                ));
            }
        }
    }

    assert!(
        failures.is_empty(),
        "v1-v2 parity failures ({} cases run):\n{}",
        cases_run,
        failures.join("\n")
    );
}

/// The tree-walk-only corpus cases (if any) produce matching results under
/// both the v1 and v2 tree-walk engines. Compiled engines are skipped for
/// these cases. When no tree-walk-only cases remain, this test is a no-op.
#[test]
fn v1_v2_parity_tree_walk_only_cases() {
    let lang = language();
    let cases = corpus();

    let v1_tw = TreeWalkEngine::new();
    let v2_tw = V2Interpreter::new();

    let mut failures: Vec<String> = Vec::new();
    let mut ran = 0usize;

    for case in &cases {
        if !case.tree_walk_only {
            continue;
        }
        ran += 1;
        let req = EvalRequest::new(case.ast.clone());
        let v1_res = v1_tw.eval(&lang, &req);
        let v2_res = eval_v2_tree_walk(&v2_tw, &lang, &req);

        let agrees = match (&v1_res, &v2_res) {
            (Ok(a), Ok(b)) => a == b,
            (Err(_), Err(_)) => true,
            _ => false,
        };
        if !agrees {
            failures.push(format!(
                "tree-walk-only case '{}' ({}): v1 produced {:?}, v2 produced {:?}",
                case.name, case.source, v1_res, v2_res
            ));
        }
        if let Ok(v) = &v1_res {
            if v != &case.expected {
                failures.push(format!(
                    "tree-walk-only case '{}' ({}): expected {}, got {}",
                    case.name, case.source, case.expected, v
                ));
            }
        }
    }

    // No assertion on `ran`: the corpus may legitimately have zero
    // tree-walk-only cases.
    let _ = ran;

    assert!(
        failures.is_empty(),
        "v1-v2 tree-walk-only parity failures:\n{}",
        failures.join("\n")
    );
}
