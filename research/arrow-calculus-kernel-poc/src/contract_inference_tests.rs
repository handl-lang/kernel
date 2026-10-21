// Contract Inference Tests — REAL refinement inference on kit-stdlib modules
// ADR-0070: replaces the placeholder stub with the real refinement engine.
//
// This is a standalone test binary in the PoC style (fn main() with PASS/FAIL
// assertions). It verifies that:
//   1. kernel_to_rgraph correctly translates Kernel graphs to RGraph
//   2. Real contracts are inferred for kit-stdlib data/sort (Sorted guarantee)
//   3. The ModuleLoader contract cache contains real refinements (not stubs)
//   4. Cascade contracts compose across atoms -> insert -> sort
//   5. The pipeline example infers refinements from map >>> filter >>> sort

#[path = "v0_1_surface.rs"]
#[allow(dead_code)]
mod v0_1_surface;

#[path = "modules.rs"]
#[allow(dead_code)]
mod modules;

use modules::Kernel;
use modules::{FileResolver, ModuleLoader, normalize_compile_time, kernel_to_rgraph,
              parse, desugar};
use modules::refinement_engine::{infer_refinement, standard_sig, RGraph, Pred, implies};
use std::path::PathBuf;

fn check(label: &str, ok: bool) {
    if ok {
        println!("  PASS  {}", label);
    } else {
        println!("  FAIL  {}", label);
        std::process::exit(1);
    }
}

/// Root directory for kit-stdlib modules.
fn kit_stdlib_root() -> PathBuf {
    PathBuf::from("kit-stdlib")
}

/// Root directory for examples.
fn examples_root() -> PathBuf {
    PathBuf::from("examples")
}

fn main() {
    println!("Contract Inference Tests — ADR-0070 Real Refinement Inference");
    println!("===============================================================\n");

    // === Section 1: Direct kernel_to_rgraph translation ===
    println!("Section 1: Direct kernel_to_rgraph translation");
    {
        // Kernel::Seq(Var("sort"), Var("sort")) should become
        // RGraph::Comp(Arr("sort"), Arr("sort")).
        let k = Kernel::seq(
            Kernel::Var("sort".to_string()),
            Kernel::Var("sort".to_string()),
        );
        let rgraph = kernel_to_rgraph(&k);
        println!("  Kernel: Seq(Var(sort), Var(sort))");
        println!("  RGraph: {}", rgraph);
        match &rgraph {
            RGraph::Comp(a, b) => {
                check("comp structure: left is Arr(sort)", **a == RGraph::Arr("sort".to_string()));
                check("comp structure: right is Arr(sort)", **b == RGraph::Arr("sort".to_string()));
            }
            other => {
                println!("  Expected Comp, got {:?}", other);
                check("comp structure: is Comp", false);
            }
        }

        // Kernel::Loop(Var("insert")) should become RGraph::Loop(Arr("insert")).
        let k2 = Kernel::Loop {
            body: Box::new(Kernel::Var("insert".to_string())),
        };
        let rgraph2 = kernel_to_rgraph(&k2);
        println!("  Kernel: Loop(Var(insert))");
        println!("  RGraph: {}", rgraph2);
        match &rgraph2 {
            RGraph::Loop(inner) => {
                check("loop structure: inner is Arr(insert)", **inner == RGraph::Arr("insert".to_string()));
            }
            other => {
                println!("  Expected Loop, got {:?}", other);
                check("loop structure: is Loop", false);
            }
        }

        // Kernel::First(Var("id")) should become RGraph::First(Arr("id")).
        let k3 = Kernel::First {
            inner: Box::new(Kernel::Var("id".to_string())),
        };
        let rgraph3 = kernel_to_rgraph(&k3);
        println!("  Kernel: First(Var(id))");
        println!("  RGraph: {}", rgraph3);
        match &rgraph3 {
            RGraph::First(inner) => {
                check("first structure: inner is Arr(id)", **inner == RGraph::Arr("id".to_string()));
            }
            other => {
                println!("  Expected First, got {:?}", other);
                check("first structure: is First", false);
            }
        }
    }
    println!();

    // === Section 2: Direct inference on kit-stdlib data/sort ===
    println!("Section 2: Direct inference on kit-stdlib data/sort");
    {
        // Chain resolver: kit-stdlib + examples (for any cross-references).
        let resolver = FileResolver::new(kit_stdlib_root());
        let loader = ModuleLoader::new(Box::new(resolver));

        // Normalize data/sort (Strategy A — compile-time inlining).
        let normalized = match normalize_compile_time("data/sort", &loader) {
            Ok(prog) => prog,
            Err(e) => {
                println!("  ERROR: {}", e);
                check("normalize_compile_time(data/sort)", false);
                return;
            }
        };
        check("normalize_compile_time(data/sort) succeeds", true);

        // Find the sort binding.
        let sort_kernel = normalized
            .bindings
            .iter()
            .find(|(n, _)| n == "sort")
            .map(|(_, k)| k.clone());

        let sort_kernel = match sort_kernel {
            Some(k) => k,
            None => {
                check("data/sort has a 'sort' binding", false);
                return;
            }
        };
        check("data/sort has a 'sort' binding", true);

        // Translate to RGraph and infer refinement.
        let rgraph = kernel_to_rgraph(&sort_kernel);
        println!("  sort RGraph: {}", rgraph);

        let sig = standard_sig();
        let result = match infer_refinement(&rgraph, &sig) {
            Ok(r) => r,
            Err(e) => {
                println!("  infer_refinement error: {}", e);
                check("infer_refinement(sort) succeeds", false);
                return;
            }
        };
        check("infer_refinement(sort) succeeds", true);

        let guarantee_str = result.guarantee.pretty();
        println!("  Guarantee: {}", guarantee_str);

        // The guarantee should contain Sorted (because sort = loop(insert >>> first(id)),
        // and insert has guarantee Sorted(output) in the sig table).
        check(
            "sort guarantee contains Sorted",
            guarantee_str.contains("Sorted"),
        );

        // Verify via the implication checker that the guarantee implies Sorted(output).
        let sorted = Pred::Sorted("output".to_string());
        let implies_sorted = implies(&result.guarantee, &sorted);
        println!("  implies({}, Sorted(output)) = {}", guarantee_str, implies_sorted);
        check(
            "sort guarantee implies Sorted(output)",
            implies_sorted,
        );

        // The loop should have discovered at least one invariant.
        println!("  Loop invariants: {}", result.loop_invariants.len());
        check(
            "sort has at least one loop invariant",
            result.loop_invariants.len() >= 1,
        );
    }
    println!();

    // === Section 3: Contract cache has real refinements ===
    println!("Section 3: Contract cache has real refinements");
    {
        let resolver = FileResolver::new(kit_stdlib_root());
        let loader = ModuleLoader::new(Box::new(resolver));

        let loaded = match loader.load("data/sort") {
            Ok(m) => m,
            Err(e) => {
                println!("  ERROR: {}", e);
                check("load data/sort via ModuleLoader", false);
                return;
            }
        };
        check("load data/sort via ModuleLoader", true);

        println!("  Contract signature: {}", loaded.contract.signature);
        println!("  Contract refinements: {:?}", loaded.contract.refinements);

        // The refinements should be non-empty and contain "Sorted".
        check(
            "data/sort contract refinements is non-empty",
            !loaded.contract.refinements.is_empty(),
        );
        let has_sorted = loaded
            .contract
            .refinements
            .iter()
            .any(|r| r.contains("Sorted"));
        check(
            "data/sort contract refinements contains 'Sorted'",
            has_sorted,
        );
    }
    println!();

    // === Section 4: Cascade contracts compose ===
    println!("Section 4: Cascade contracts compose (atoms -> insert -> sort)");
    {
        let resolver = FileResolver::new(kit_stdlib_root());
        let loader = ModuleLoader::new(Box::new(resolver));

        // data/atoms: id, compare, cons — all have guarantee True.
        let atoms = match loader.load("data/atoms") {
            Ok(m) => m,
            Err(e) => {
                println!("  ERROR loading data/atoms: {}", e);
                check("load data/atoms", false);
                return;
            }
        };
        check("load data/atoms", true);
        println!("  atoms refinements: {:?}", atoms.contract.refinements);
        check(
            "atoms: no refinements (all guarantee True)",
            atoms.contract.refinements.is_empty(),
        );

        // data/insert: loop(compare >>> choice(cons)) — compare and cons
        // both have guarantee True, so insert's guarantee is And(True, True).
        // It should NOT contain Sorted (the module defines insert as a loop
        // over compare/cons, not a reference to the "insert" base arrow).
        let insert = match loader.load("data/insert") {
            Ok(m) => m,
            Err(e) => {
                println!("  ERROR loading data/insert: {}", e);
                check("load data/insert", false);
                return;
            }
        };
        check("load data/insert", true);
        println!("  insert refinements: {:?}", insert.contract.refinements);
        let insert_has_sorted = insert
            .contract
            .refinements
            .iter()
            .any(|r| r.contains("Sorted"));
        check(
            "insert: no Sorted in refinements (graph is compare/cons, all True)",
            !insert_has_sorted,
        );

        // data/sort: loop(insert >>> first(id)) — the Var("insert") in the
        // sort binding maps to Arr("insert") in RGraph, and "insert" is in
        // the sig table with guarantee Sorted(output). So sort's guarantee
        // should contain Sorted.
        let sort = match loader.load("data/sort") {
            Ok(m) => m,
            Err(e) => {
                println!("  ERROR loading data/sort: {}", e);
                check("load data/sort", false);
                return;
            }
        };
        check("load data/sort", true);
        println!("  sort refinements: {:?}", sort.contract.refinements);
        let sort_has_sorted = sort
            .contract
            .refinements
            .iter()
            .any(|r| r.contains("Sorted"));
        check(
            "sort: contains Sorted (derived from loop(insert >>> first(id)))",
            sort_has_sorted,
        );
    }
    println!();

    // === Section 5: Pipeline example ===
    println!("Section 5: Pipeline example (map >>> filter >>> sort)");
    {
        // The pipeline example is in examples/pipeline/main.hnl.
        // It imports from fn/map, fn/filter, data/sort, fn/double, fn/is_even.
        // We need a resolver that can find both kit-stdlib and examples/pipeline.
        // Use a ChainResolver with kit-stdlib as root (the imports use paths
        // like "fn/map", "data/sort" which resolve under kit-stdlib).
        // The pipeline main.hnl is at examples/pipeline/main.hnl, but its
        // imports resolve relative to kit-stdlib. We load it via a resolver
        // rooted at examples/pipeline for the entry, but the imports need
        // kit-stdlib. A ChainResolver handles this: try examples/pipeline
        // first, then kit-stdlib.

        // Actually, the FileResolver resolves paths relative to its root.
        // The pipeline main.hnl imports "fn/map", "data/sort", etc. which
        // are under kit-stdlib. But the entry "pipeline/main" is under
        // examples/. We need a resolver that can find both.
        //
        // Strategy: use kit-stdlib as the root. The pipeline example's
        // imports (fn/map, fn/filter, data/sort, fn/double, fn/is_even)
        // all resolve under kit-stdlib. But "pipeline/main" doesn't exist
        // under kit-stdlib. We need to read the pipeline main.hnl directly.

        // Read the pipeline main.hnl source directly.
        let pipeline_path = examples_root().join("pipeline").join("main.hnl");
        let pipeline_source = match std::fs::read_to_string(&pipeline_path) {
            Ok(s) => s,
            Err(e) => {
                println!("  ERROR reading pipeline/main.hnl: {}", e);
                check("read pipeline/main.hnl", false);
                return;
            }
        };
        check("read pipeline/main.hnl", true);

        // Parse and desugar the pipeline source.
        let program = match parse(&pipeline_source) {
            Ok(p) => p,
            Err(e) => {
                println!("  ERROR parsing pipeline: {}", e);
                check("parse pipeline/main", false);
                return;
            }
        };
        check("parse pipeline/main", true);

        let desugared = desugar(&program);
        check("desugar pipeline/main", true);

        // Find the main binding.
        let main_kernel = desugared
            .bindings
            .iter()
            .find(|(n, _)| n == "main")
            .map(|(_, k)| k.clone());

        let main_kernel = match main_kernel {
            Some(k) => k,
            None => {
                check("pipeline has a 'main' binding", false);
                return;
            }
        };
        check("pipeline has a 'main' binding", true);

        // Translate to RGraph and infer refinement.
        let rgraph = kernel_to_rgraph(&main_kernel);
        println!("  main RGraph: {}", rgraph);

        let sig = standard_sig();
        let result = match infer_refinement(&rgraph, &sig) {
            Ok(r) => r,
            Err(e) => {
                println!("  infer_refinement error: {}", e);
                check("infer_refinement(pipeline main) succeeds", false);
                return;
            }
        };
        check("infer_refinement(pipeline main) succeeds", true);

        let guarantee_str = result.guarantee.pretty();
        println!("  Guarantee: {}", guarantee_str);

        // The pipeline is map(double) >>> filter(is_even) >>> sort.
        // sort's guarantee is Sorted(output), which should propagate through
        // the composition. The overall guarantee should contain Sorted.
        check(
            "pipeline guarantee contains Sorted (from sort)",
            guarantee_str.contains("Sorted"),
        );

        // It should also contain length preservation (from map).
        check(
            "pipeline guarantee contains length info (from map)",
            guarantee_str.contains("input") && guarantee_str.contains("output"),
        );
    }
    println!();

    // === Summary ===
    println!("===============================================================");
    println!("All contract inference tests passed.");
    println!("  - kernel_to_rgraph translates Kernel to RGraph correctly");
    println!("  - data/sort infers Sorted(output) from loop(insert >>> first(id))");
    println!("  - ModuleLoader contract cache has real refinements (not stubs)");
    println!("  - Cascade: atoms (no ref) -> insert (no Sorted) -> sort (Sorted)");
    println!("  - Pipeline: map >>> filter >>> sort infers Sorted + length");
    println!("===============================================================");
}
