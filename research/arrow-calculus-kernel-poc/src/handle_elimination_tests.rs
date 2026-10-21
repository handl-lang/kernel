// Compile-Time Handler Elimination Tests (ADR-0076)
//
// Verifies that `Kernel::Handle` nodes (from `handle ... with` surface syntax)
// are eliminated to concrete arrows at COMPILE TIME in the `kernel_to_rgraph`
// pipeline, using the `eliminate_handler_in_rgraph` tree walk. This is the
// compile-time analogue of the runtime `EffectGraph` machinery in
// `bundled_effects.rs` (`handle_eliminate` / `eliminate_all_handlers`).
//
// After lowering, the resulting `RGraph` has NO handler nodes and NO unhandled
// `Arr(target)` references -- every reference to the handled target has been
// rewritten to the concrete impl graph. The eliminated graph is a plain
// arrow graph that CutElim can normalize (verified via `PolyGraph`).
//
// Test layers:
//   1. Unit tests of `eliminate_handler_in_rgraph` on constructed RGraphs.
//   2. Integration tests of `kernel_to_rgraph` on constructed `Kernel::Handle`.
//   3. Full pipeline tests: parse -> desugar -> kernel_to_rgraph -> check.
//   4. Nested handlers (inner eliminated first, then outer).
//   5. Law checking after elimination (RGraph -> PolyGraph -> normalize).

#[path = "modules.rs"]
#[allow(dead_code)]
mod modules;

// Include the shared graph model / CutElim normalizer (ADR-0075 substrate) for
// law checking after elimination. This is the SAME `PolyGraph` type used by
// `bundled_effects.rs`. Its `fn main()` becomes dead code inside the module.
#[path = "trait_catalog.rs"]
#[allow(dead_code)]
mod trait_catalog;

use modules::Kernel;
use modules::{kernel_to_rgraph, eliminate_handler_in_rgraph, parse, desugar};
use modules::refinement_engine::RGraph;
use trait_catalog::{PolyGraph, normalize, law_equal};

/// Fuel budget for CutElim normalization (mirrors the module-private
/// `NORMALIZE_FUEL` constant in `trait_catalog.rs`).
const NORMALIZE_FUEL: usize = 1024;

fn check(label: &str, ok: bool) {
    if ok {
        println!("  PASS  {}", label);
    } else {
        println!("  FAIL  {}", label);
        std::process::exit(1);
    }
}

/// Convert an `RGraph` (refinement-engine IR) to a `PolyGraph` (concrete graph
/// for CutElim normalization). `RGraph` is a subset of `PolyGraph` (no
/// `Choice`/`App`), so the conversion is a structural homomorphism.
fn rgraph_to_poly(g: &RGraph) -> PolyGraph {
    match g {
        RGraph::Id => PolyGraph::Id,
        RGraph::Comp(a, b) => PolyGraph::Comp(
            Box::new(rgraph_to_poly(a)),
            Box::new(rgraph_to_poly(b)),
        ),
        RGraph::First(a) => PolyGraph::First(Box::new(rgraph_to_poly(a))),
        RGraph::Left(a) => PolyGraph::Left(Box::new(rgraph_to_poly(a))),
        RGraph::Loop(a) => PolyGraph::Loop(Box::new(rgraph_to_poly(a))),
        RGraph::Arr(name) => PolyGraph::Arr(name.clone()),
    }
}

/// Does an `RGraph` contain any `Arr(name)` where `name == target`?
fn contains_arr(graph: &RGraph, target: &str) -> bool {
    match graph {
        RGraph::Arr(name) => name == target,
        RGraph::Comp(a, b) => contains_arr(a, target) || contains_arr(b, target),
        RGraph::First(a) | RGraph::Left(a) | RGraph::Loop(a) => contains_arr(a, target),
        RGraph::Id => false,
    }
}

/// Desugar a single expression into a Kernel. Wraps the expression in a
/// one-binding program (`_t = <expr>`) and runs the full parse -> desugar
/// pipeline through `modules` so the `Kernel` type is the one consumed by
/// `kernel_to_rgraph`.
fn desugar_expr_to_kernel(src: &str) -> Result<Kernel, String> {
    let prog_src = format!("_t = {}", src);
    let program = parse(&prog_src).map_err(|e| e.to_string())?;
    let ds = desugar(&program);
    Ok(ds.bindings[0].1.clone())
}

fn main() {
    println!("Compile-Time Handler Elimination Tests (ADR-0076)");
    println!("==================================================\n");

    // ====================================================================
    // Section 1: Unit tests of eliminate_handler_in_rgraph on constructed
    // RGraphs. The elimination is a tree walk that replaces Arr(target)
    // with the impl graph.
    // ====================================================================
    println!("Section 1: eliminate_handler_in_rgraph (direct RGraph unit tests)");
    {
        // 1a. Single Arr(target) -> impl_graph.
        let body = RGraph::Arr("map".to_string());
        let impl_g = RGraph::Arr("map_list".to_string());
        let result = eliminate_handler_in_rgraph(&body, "map", &impl_g);
        println!("  body: {}  ->  eliminated: {}", body, result);
        check(
            "single Arr(map) replaced by Arr(map_list)",
            result == RGraph::Arr("map_list".to_string()),
        );
        check("no Arr(map) remains", !contains_arr(&result, "map"));

        // 1b. Comp(Arr("f"), Arr("map")) -> Comp(Arr("f"), Arr("map_list")).
        let body = RGraph::Comp(
            Box::new(RGraph::Arr("f".to_string())),
            Box::new(RGraph::Arr("map".to_string())),
        );
        let impl_g = RGraph::Arr("map_list".to_string());
        let result = eliminate_handler_in_rgraph(&body, "map", &impl_g);
        println!("  body: {}  ->  eliminated: {}", body, result);
        let expected = RGraph::Comp(
            Box::new(RGraph::Arr("f".to_string())),
            Box::new(RGraph::Arr("map_list".to_string())),
        );
        check("comp: Arr(map) replaced, Arr(f) preserved", result == expected);
        check("no Arr(map) remains in comp", !contains_arr(&result, "map"));

        // 1c. First(Comp(Arr("map"), Arr("g"))) -> First(Comp(impl, Arr("g"))).
        let body = RGraph::First(Box::new(RGraph::Comp(
            Box::new(RGraph::Arr("map".to_string())),
            Box::new(RGraph::Arr("g".to_string())),
        )));
        let impl_g = RGraph::Arr("map_list".to_string());
        let result = eliminate_handler_in_rgraph(&body, "map", &impl_g);
        println!("  body: {}  ->  eliminated: {}", body, result);
        check(
            "first: Arr(map) inside First replaced",
            !contains_arr(&result, "map"),
        );
        check(
            "first: Arr(g) preserved",
            contains_arr(&result, "g"),
        );

        // 1d. Loop(Arr("map")) -> Loop(impl).
        let body = RGraph::Loop(Box::new(RGraph::Arr("map".to_string())));
        let impl_g = RGraph::Arr("map_list".to_string());
        let result = eliminate_handler_in_rgraph(&body, "map", &impl_g);
        println!("  body: {}  ->  eliminated: {}", body, result);
        check("loop: Arr(map) inside Loop replaced", !contains_arr(&result, "map"));

        // 1e. Non-matching target is left alone.
        let body = RGraph::Arr("other".to_string());
        let impl_g = RGraph::Arr("map_list".to_string());
        let result = eliminate_handler_in_rgraph(&body, "map", &impl_g);
        check(
            "non-matching Arr(other) left as-is",
            result == RGraph::Arr("other".to_string()),
        );

        // 1f. Id is left alone.
        let body = RGraph::Id;
        let impl_g = RGraph::Arr("map_list".to_string());
        let result = eliminate_handler_in_rgraph(&body, "map", &impl_g);
        check("Id left as-is", result == RGraph::Id);

        // 1g. Impl graph is itself a composition (multi-node replacement).
        let body = RGraph::Comp(
            Box::new(RGraph::Arr("map".to_string())),
            Box::new(RGraph::Arr("h".to_string())),
        );
        let impl_g = RGraph::Comp(
            Box::new(RGraph::Arr("pre".to_string())),
            Box::new(RGraph::Arr("post".to_string())),
        );
        let result = eliminate_handler_in_rgraph(&body, "map", &impl_g);
        println!("  body: {}  ->  eliminated: {}", body, result);
        let expected = RGraph::Comp(
            Box::new(RGraph::Comp(
                Box::new(RGraph::Arr("pre".to_string())),
                Box::new(RGraph::Arr("post".to_string())),
            )),
            Box::new(RGraph::Arr("h".to_string())),
        );
        check("impl is a composition: spliced in place", result == expected);
        check("no Arr(map) remains after splice", !contains_arr(&result, "map"));
    }
    println!();

    // ====================================================================
    // Section 2: Integration tests of kernel_to_rgraph on constructed
    // Kernel::Handle nodes. This tests the full lowering: Kernel::Handle ->
    // lower impl -> lower body -> eliminate.
    // ====================================================================
    println!("Section 2: kernel_to_rgraph on Kernel::Handle (constructed)");
    {
        // 2a. handle (f >>> map) with map = map_list
        //     body = Seq(Var("f"), Var("map")), impl = Var("map_list")
        //     -> Comp(Arr("f"), Arr("map_list"))  [map eliminated]
        let k = Kernel::handle(
            Kernel::seq(
                Kernel::Var("f".to_string()),
                Kernel::Var("map".to_string()),
            ),
            "map",
            Kernel::Var("map_list".to_string()),
        );
        let rgraph = kernel_to_rgraph(&k);
        println!("  Kernel: handle (f >>> map) with map = map_list");
        println!("  RGraph: {}", rgraph);
        let expected = RGraph::Comp(
            Box::new(RGraph::Arr("f".to_string())),
            Box::new(RGraph::Arr("map_list".to_string())),
        );
        check("handle (f >>> map) with map = map_list -> Comp(f, map_list)", rgraph == expected);
        check("no Arr(map) remains after kernel_to_rgraph", !contains_arr(&rgraph, "map"));

        // 2b. handle (map >>> map) with map = impl  -- both references replaced.
        let k = Kernel::handle(
            Kernel::seq(
                Kernel::Var("map".to_string()),
                Kernel::Var("map".to_string()),
            ),
            "map",
            Kernel::Var("concrete".to_string()),
        );
        let rgraph = kernel_to_rgraph(&k);
        println!("  Kernel: handle (map >>> map) with map = concrete");
        println!("  RGraph: {}", rgraph);
        let expected = RGraph::Comp(
            Box::new(RGraph::Arr("concrete".to_string())),
            Box::new(RGraph::Arr("concrete".to_string())),
        );
        check("both Arr(map) references replaced", rgraph == expected);
        check("no Arr(map) remains", !contains_arr(&rgraph, "map"));

        // 2c. handle (first(map)) with map = impl -- First combinator.
        let k = Kernel::handle(
            Kernel::First {
                inner: Box::new(Kernel::Var("map".to_string())),
            },
            "map",
            Kernel::Var("map_impl".to_string()),
        );
        let rgraph = kernel_to_rgraph(&k);
        println!("  Kernel: handle (first(map)) with map = map_impl");
        println!("  RGraph: {}", rgraph);
        let expected = RGraph::First(Box::new(RGraph::Arr("map_impl".to_string())));
        check("first(map) -> first(map_impl)", rgraph == expected);
        check("no Arr(map) remains in first", !contains_arr(&rgraph, "map"));

        // 2d. handle (loop(map)) with map = impl -- Loop combinator.
        let k = Kernel::handle(
            Kernel::Loop {
                body: Box::new(Kernel::Var("map".to_string())),
            },
            "map",
            Kernel::Var("map_impl".to_string()),
        );
        let rgraph = kernel_to_rgraph(&k);
        println!("  Kernel: handle (loop(map)) with map = map_impl");
        println!("  RGraph: {}", rgraph);
        let expected = RGraph::Loop(Box::new(RGraph::Arr("map_impl".to_string())));
        check("loop(map) -> loop(map_impl)", rgraph == expected);
        check("no Arr(map) remains in loop", !contains_arr(&rgraph, "map"));

        // 2e. Impl is a composition (multi-node handler graph).
        let k = Kernel::handle(
            Kernel::seq(
                Kernel::Var("f".to_string()),
                Kernel::Var("Serializer".to_string()),
            ),
            "Serializer",
            Kernel::seq(
                Kernel::Var("json_serialize".to_string()),
                Kernel::Var("json_deserialize".to_string()),
            ),
        );
        let rgraph = kernel_to_rgraph(&k);
        println!("  Kernel: handle (f >>> Serializer) with Serializer = (json_serialize >>> json_deserialize)");
        println!("  RGraph: {}", rgraph);
        // body -> Comp(Arr("f"), Arr("Serializer"))
        // impl -> Comp(Arr("json_serialize"), Arr("json_deserialize"))
        // eliminated -> Comp(Arr("f"), Comp(Arr("json_serialize"), Arr("json_deserialize")))
        let expected = RGraph::Comp(
            Box::new(RGraph::Arr("f".to_string())),
            Box::new(RGraph::Comp(
                Box::new(RGraph::Arr("json_serialize".to_string())),
                Box::new(RGraph::Arr("json_deserialize".to_string())),
            )),
        );
        check("Serializer replaced by composition impl", rgraph == expected);
        check("no Arr(Serializer) remains", !contains_arr(&rgraph, "Serializer"));
    }
    println!();

    // ====================================================================
    // Section 3: Full pipeline tests -- parse -> desugar -> kernel_to_rgraph.
    // Uses the surface `handle ... with` syntax.
    // ====================================================================
    println!("Section 3: full pipeline (parse -> desugar -> kernel_to_rgraph)");
    {
        // 3a. handle (f >>> map) with map = map_list
        //     f, map, map_list are bare Vars -> Arr("f"), Arr("map"), Arr("map_list").
        //     After elimination: Comp(Arr("f"), Arr("map_list")).
        match desugar_expr_to_kernel("handle (f >>> map) with map = map_list") {
            Ok(k) => {
                println!("  source: handle (f >>> map) with map = map_list");
                println!("  desugared Kernel: {:?}", k);
                // Confirm it desugared to Kernel::Handle.
                check(
                    "desugar produces Kernel::Handle",
                    matches!(k, Kernel::Handle { ref target, .. } if target == "map"),
                );
                let rgraph = kernel_to_rgraph(&k);
                println!("  RGraph: {}", rgraph);
                // The body f >>> map lowers to Comp(Arr("f"), Arr("map"));
                // elimination replaces Arr("map") with Arr("map_list").
                check(
                    "pipeline: Arr(map) eliminated to Arr(map_list)",
                    !contains_arr(&rgraph, "map"),
                );
                check(
                    "pipeline: Arr(f) preserved",
                    contains_arr(&rgraph, "f"),
                );
                check(
                    "pipeline: Arr(map_list) present",
                    contains_arr(&rgraph, "map_list"),
                );
            }
            Err(e) => {
                println!("  FAIL [parse/desugar] handle (f >>> map) with map = map_list  =>  {}", e);
                std::process::exit(1);
            }
        }

        // 3b. handle (serialize >>> Serializer) with Serializer = json_impl
        //     target "Serializer" replaced by Arr("json_impl").
        match desugar_expr_to_kernel("handle (serialize >>> Serializer) with Serializer = json_impl") {
            Ok(k) => {
                println!("  source: handle (serialize >>> Serializer) with Serializer = json_impl");
                let rgraph = kernel_to_rgraph(&k);
                println!("  RGraph: {}", rgraph);
                check(
                    "pipeline: Arr(Serializer) eliminated",
                    !contains_arr(&rgraph, "Serializer"),
                );
                check(
                    "pipeline: Arr(json_impl) present",
                    contains_arr(&rgraph, "json_impl"),
                );
                check(
                    "pipeline: Arr(serialize) preserved",
                    contains_arr(&rgraph, "serialize"),
                );
            }
            Err(e) => {
                println!("  FAIL [parse/desugar] Serializer handle  =>  {}", e);
                std::process::exit(1);
            }
        }

        // 3c. handle body with map = map_list -- body has no map reference,
        //     so elimination is a no-op (body passes through unchanged).
        match desugar_expr_to_kernel("handle body with map = map_list") {
            Ok(k) => {
                println!("  source: handle body with map = map_list");
                let rgraph = kernel_to_rgraph(&k);
                println!("  RGraph: {}", rgraph);
                // body -> Arr("body"); no Arr("map") to replace.
                check(
                    "no-op handle: body preserved when target absent",
                    rgraph == RGraph::Arr("body".to_string()),
                );
            }
            Err(e) => {
                println!("  FAIL [parse/desugar] no-op handle  =>  {}", e);
                std::process::exit(1);
            }
        }
    }
    println!();

    // ====================================================================
    // Section 4: Nested handlers -- inner eliminated first, then outer.
    // handle (handle (a >>> b) with a = impl_a) with b = impl_b
    //   inner: Comp(Arr("a"), Arr("b")) -> Comp(Arr("impl_a"), Arr("b"))
    //   outer: Comp(Arr("impl_a"), Arr("b")) -> Comp(Arr("impl_a"), Arr("impl_b"))
    // ====================================================================
    println!("Section 4: nested handlers (inner first, then outer)");
    {
        // 4a. Constructed Kernel::Handle nested.
        let inner = Kernel::handle(
            Kernel::seq(
                Kernel::Var("a".to_string()),
                Kernel::Var("b".to_string()),
            ),
            "a",
            Kernel::Var("impl_a".to_string()),
        );
        let outer = Kernel::handle(inner, "b", Kernel::Var("impl_b".to_string()));
        let rgraph = kernel_to_rgraph(&outer);
        println!("  Kernel: handle (handle (a >>> b) with a = impl_a) with b = impl_b");
        println!("  RGraph: {}", rgraph);
        let expected = RGraph::Comp(
            Box::new(RGraph::Arr("impl_a".to_string())),
            Box::new(RGraph::Arr("impl_b".to_string())),
        );
        check("nested: inner a -> impl_a, outer b -> impl_b", rgraph == expected);
        check("nested: no Arr(a) remains", !contains_arr(&rgraph, "a"));
        check("nested: no Arr(b) remains", !contains_arr(&rgraph, "b"));
        check("nested: Arr(impl_a) present", contains_arr(&rgraph, "impl_a"));
        check("nested: Arr(impl_b) present", contains_arr(&rgraph, "impl_b"));

        // 4b. Nested via the parser.
        match desugar_expr_to_kernel(
            "handle (handle (a >>> b) with a = impl_a) with b = impl_b",
        ) {
            Ok(k) => {
                println!("  source: handle (handle (a >>> b) with a = impl_a) with b = impl_b");
                let rgraph = kernel_to_rgraph(&k);
                println!("  RGraph: {}", rgraph);
                check("nested pipeline: no Arr(a) remains", !contains_arr(&rgraph, "a"));
                check("nested pipeline: no Arr(b) remains", !contains_arr(&rgraph, "b"));
                check("nested pipeline: Arr(impl_a) present", contains_arr(&rgraph, "impl_a"));
                check("nested pipeline: Arr(impl_b) present", contains_arr(&rgraph, "impl_b"));
            }
            Err(e) => {
                println!("  FAIL [parse/desugar] nested handle  =>  {}", e);
                std::process::exit(1);
            }
        }

        // 4c. Three-deep nesting: handle (handle (handle x with a = ia) with b = ib) with c = ic
        //     where x = a >>> b >>> c.
        let innermost = Kernel::handle(
            Kernel::seq(
                Kernel::seq(Kernel::Var("a".to_string()), Kernel::Var("b".to_string())),
                Kernel::Var("c".to_string()),
            ),
            "a",
            Kernel::Var("ia".to_string()),
        );
        let middle = Kernel::handle(innermost, "b", Kernel::Var("ib".to_string()));
        let outermost = Kernel::handle(middle, "c", Kernel::Var("ic".to_string()));
        let rgraph = kernel_to_rgraph(&outermost);
        println!("  Kernel: handle (handle (handle ((a >>> b) >>> c) with a = ia) with b = ib) with c = ic");
        println!("  RGraph: {}", rgraph);
        // Expected: Comp(Comp(Arr("ia"), Arr("ib")), Arr("ic"))
        let expected = RGraph::Comp(
            Box::new(RGraph::Comp(
                Box::new(RGraph::Arr("ia".to_string())),
                Box::new(RGraph::Arr("ib".to_string())),
            )),
            Box::new(RGraph::Arr("ic".to_string())),
        );
        check("three-deep nesting: all targets eliminated", rgraph == expected);
        check("three-deep: no Arr(a/b/c) remains",
            !contains_arr(&rgraph, "a") && !contains_arr(&rgraph, "b") && !contains_arr(&rgraph, "c"));
    }
    println!();

    // ====================================================================
    // Section 5: Law checking after elimination. Convert the eliminated
    // RGraph to PolyGraph and run CutElim normalization. The eliminated
    // graph is a plain arrow graph (no handler nodes) and should normalize.
    // ====================================================================
    println!("Section 5: law checking after elimination (RGraph -> PolyGraph -> CutElim)");
    {
        // 5a. handle (f >>> map) with map = map_list -> Comp(Arr("f"), Arr("map_list"))
        //     Convert to PolyGraph and normalize. Comp(Arr, Arr) is already
        //     in normal form (no id/first rewrites apply).
        let k = Kernel::handle(
            Kernel::seq(
                Kernel::Var("f".to_string()),
                Kernel::Var("map".to_string()),
            ),
            "map",
            Kernel::Var("map_list".to_string()),
        );
        let rgraph = kernel_to_rgraph(&k);
        let poly = rgraph_to_poly(&rgraph);
        let norm = normalize(&poly, NORMALIZE_FUEL);
        println!("  eliminated RGraph: {}", rgraph);
        println!("  PolyGraph: {}", poly);
        println!("  normalized: {}", norm);
        check(
            "Comp(Arr, Arr) is already normal (no rewrites apply)",
            norm == poly,
        );

        // 5b. CutElim through rgraph_to_poly: comp(id, Arr("f")) -> Arr("f").
        //     (No Kernel variant produces RGraph::Id, so we construct the
        //     eliminated-shape RGraph directly to exercise the conversion +
        //     ceIdLeft rewrite. This is the shape an eliminated graph could
        //     have if the impl were the identity arrow.)
        let eliminated = RGraph::Comp(
            Box::new(RGraph::Id),
            Box::new(RGraph::Arr("f".to_string())),
        );
        let poly = rgraph_to_poly(&eliminated);
        let norm = normalize(&poly, NORMALIZE_FUEL);
        println!("  eliminated RGraph: {}", eliminated);
        println!("  PolyGraph: {}  ->  normalized: {}", poly, norm);
        check(
            "comp(id, f) normalizes to f via ceIdLeft",
            norm == PolyGraph::Arr("f".to_string()),
        );

        // 5c. law_equal: the eliminated graph is law_equal to the directly
        //     constructed concrete graph (no handler). This proves the
        //     elimination is semantically faithful: handle body with t = impl
        //     is equal to body[Arr(t) := impl].
        let handled = Kernel::handle(
            Kernel::seq(
                Kernel::Var("f".to_string()),
                Kernel::Var("map".to_string()),
            ),
            "map",
            Kernel::Var("map_list".to_string()),
        );
        let direct = Kernel::seq(
            Kernel::Var("f".to_string()),
            Kernel::Var("map_list".to_string()),
        );
        let handled_poly = rgraph_to_poly(&kernel_to_rgraph(&handled));
        let direct_poly = rgraph_to_poly(&kernel_to_rgraph(&direct));
        println!("  handled -> poly: {}", handled_poly);
        println!("  direct  -> poly: {}", direct_poly);
        check(
            "eliminated graph is law_equal to the direct concrete graph",
            law_equal(&handled_poly, &direct_poly),
        );

        // 5d. first(id) normalizes to id via ceFirstId (constructed RGraph).
        let eliminated = RGraph::First(Box::new(RGraph::Id));
        let poly = rgraph_to_poly(&eliminated);
        let norm = normalize(&poly, NORMALIZE_FUEL);
        println!("  first(id)  ->  PolyGraph: {}  ->  normalized: {}", poly, norm);
        check("first(id) normalizes to id via ceFirstId", norm == PolyGraph::Id);

        // 5e. A cascade: comp(first(id), first(id)) -> first(comp(id, id))
        //     -> first(id) -> id. Exercises the multi-step CutElim path
        //     through rgraph_to_poly.
        let eliminated = RGraph::Comp(
            Box::new(RGraph::First(Box::new(RGraph::Id))),
            Box::new(RGraph::First(Box::new(RGraph::Id))),
        );
        let poly = rgraph_to_poly(&eliminated);
        let norm = normalize(&poly, NORMALIZE_FUEL);
        println!("  comp(first(id), first(id))  ->  normalized: {}", norm);
        check(
            "comp(first(id), first(id)) normalizes to id via CutElim cascade",
            norm == PolyGraph::Id,
        );
    }
    println!();

    // ====================================================================
    // Summary
    // ====================================================================
    println!("==================================================");
    println!("All compile-time handler elimination tests passed.");
    println!("Kernel::Handle is eliminated to concrete arrows at compile time");
    println!("via eliminate_handler_in_rgraph (tree walk replacing Arr(target)).");
}
