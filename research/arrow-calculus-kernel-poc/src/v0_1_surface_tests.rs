// handl v0.1 Surface Syntax — Reference Parser Tests
// ADR-0074 follow-up #6.
//
// Test binary matching the PoC style (fn main() with assertions). Uses the
// v0_1_surface module via #[path].

#[path = "v0_1_surface.rs"]
mod v0_1_surface;

use v0_1_surface::{Kernel, parse, parse_expr, pretty, desugar};
use v0_1_surface::ast::*;
use v0_1_surface::desugar::{DesugaredProgram, ExportSet};

fn check_round_trip(label: &str, src: &str) {
    match parse_expr(src) {
        Ok(ast1) => {
            let printed = v0_1_surface::pretty::pretty_expr(&ast1, 0);
            match parse_expr(&printed) {
                Ok(ast2) => {
                    if ast1 == ast2 {
                        println!("  PASS [round-trip] {}  =>  {}", label, printed);
                    } else {
                        println!("  FAIL [round-trip] {}", label);
                        println!("       parsed:  {:?}", ast1);
                        println!("       printed: {}", printed);
                        println!("       re-parsed: {:?}", ast2);
                        std::process::exit(1);
                    }
                }
                Err(e) => {
                    println!("  FAIL [round-trip re-parse] {}  =>  {}", label, e);
                    println!("       printed: {}", printed);
                    std::process::exit(1);
                }
            }
        }
        Err(e) => {
            println!("  FAIL [parse] {}  =>  {}", label, e);
            std::process::exit(1);
        }
    }
}

fn check_parse_ok(label: &str, src: &str) {
    match parse_expr(src) {
        Ok(_) => println!("  PASS [parse]     {}", label),
        Err(e) => {
            println!("  FAIL [parse]     {}  =>  {}", label, e);
            std::process::exit(1);
        }
    }
}

fn check_desugar(label: &str, src: &str, pred: &dyn Fn(&Kernel) -> bool) {
    match parse_expr(src) {
        Ok(e) => {
            // Wrap in a single-binding program for desugar.
            let prog = Program {
                imports: vec![],
                exports: vec![],
                bindings: vec![Binding { name: "_t".to_string(), ty: None, value: e }],
            };
            let ds = desugar(&prog);
            let k = &ds.bindings[0].1;
            if pred(k) {
                println!("  PASS [desugar]   {}  =>  {:?}", label, k);
            } else {
                println!("  FAIL [desugar]   {}  =>  {:?}", label, k);
                std::process::exit(1);
            }
        }
        Err(e) => {
            println!("  FAIL [desugar parse] {}  =>  {}", label, e);
            std::process::exit(1);
        }
    }
}

fn main() {
    println!("handl v0.1 Surface — Reference Parser Tests");
    println!("=============================================\n");

    // ------------------------------------------------------------------
    // 1. Lexer smoke (implicit via parse)
    // ------------------------------------------------------------------
    println!("Section 1: Lexer (via parse)");
    check_parse_ok("int literal", "42");
    check_parse_ok("float literal", "1.5");
    check_parse_ok("string literal", "\"hello\"");
    check_parse_ok("bool true", "true");
    check_parse_ok("bool false", "false");

    // ------------------------------------------------------------------
    // 2. Parser + pretty-printer round-trip
    // ------------------------------------------------------------------
    println!("\nSection 2: Round-trip");
    check_round_trip("inline arrow", "x ~> x * 2");
    check_round_trip("point-free mul", "* 2");
    check_round_trip("point-free add", "+ 1");
    check_round_trip("seq compose", "f >>> g");
    check_round_trip("product", "f *** g");
    check_round_trip("fanout", "f &&& g");
    check_round_trip("choice", "f ||| g");
    check_round_trip("destructuring rename", "{ name: userName } ~> userName");
    check_round_trip("destructuring record", "{ name, age } = user");
    check_round_trip("spread merge", "{ ...defaults, ...overrides }");
    check_round_trip("spread positional", "[...a, b]");
    check_round_trip("nullish", "user.name ?? \"anonymous\"");
    check_round_trip("opt chain", "user?.address?.city");
    check_round_trip("opt chain + nullish", "user?.address?.city ?? \"unknown\"");
    check_round_trip("while", "while n > 0 { n = n - 1 }");
    check_round_trip("for map", "for x in xs { x * 2 }");
    check_round_trip("for fold", "for x in xs, acc = 0 { acc + x }");
    check_round_trip("do while", "do { line = readLine input } while line != \"\"");
    check_round_trip("multi-arg no-curry", "[x, y] ~> x + y");
    check_round_trip("match", "match v { some: x, none: 0, _: 0 }");
    check_round_trip("if two-branch", "if x > 0 { \"positive\" } else { \"non-positive\" }");
    check_round_trip("rec block", "rec { a = f b, b = g a }");
    check_round_trip("field access", "obj.field");
    check_round_trip("indexing", "obj[idx]");
    check_round_trip("paren", "(x + 1)");
    check_round_trip("infer name", "infer x");
    check_round_trip("infer arrow", "infer (parse _)");

    // ------------------------------------------------------------------
    // 3. Program-level (imports + bindings)
    // ------------------------------------------------------------------
    println!("\nSection 3: Program");
    let prog_src = "import sort from \"collection/sort\"\n\nadd = [x, y] ~> x + y\ngreet = { name: userName } ~> userName";
    match parse(prog_src) {
        Ok(p) => {
            let pp = pretty(&p);
            match parse(&pp) {
                Ok(p2) => {
                    if p == p2 {
                        println!("  PASS [program round-trip]");
                    } else {
                        println!("  FAIL [program round-trip]");
                        std::process::exit(1);
                    }
                }
                Err(e) => {
                    println!("  FAIL [program re-parse] {}", e);
                    std::process::exit(1);
                }
            }
        }
        Err(e) => {
            println!("  FAIL [program parse] {}", e);
            std::process::exit(1);
        }
    }

    // ------------------------------------------------------------------
    // 4. Desugar to kernel IR
    // ------------------------------------------------------------------
    println!("\nSection 4: Desugar");
    check_desugar("seq", "f >>> g", &|k| matches!(k, Kernel::Seq { .. }));
    check_desugar("choice", "f ||| g", &|k| matches!(k, Kernel::Choice { .. }));
    check_desugar(
        "if",
        "if c { a } else { b }",
        &|k| matches!(k, Kernel::Seq { snd, .. } if matches!(snd.as_ref(), Kernel::Choice { .. })),
    );
    check_desugar("rec", "rec { a = f b, b = g a }", &|k| matches!(k, Kernel::Loop { .. }));
    check_desugar(
        "arithmetic add",
        "x + y",
        &|k| matches!(k, Kernel::Seq { snd, .. } if matches!(snd.as_ref(), Kernel::Var(v) if v == "add")),
    );
    check_desugar("nullish", "a ?? b", &|k| matches!(k, Kernel::Choice { .. }));
    check_desugar("while", "while n > 0 { n = n - 1 }", &|k| matches!(k, Kernel::Loop { .. }));
    check_desugar(
        "arrow",
        "x ~> x",
        &|k| matches!(k, Kernel::Arr { op, .. } if op == "arrow"),
    );

    // ------------------------------------------------------------------
    // 5. Modules (imports / exports) — ADR-0069 + export visibility sugar
    // ------------------------------------------------------------------
    println!("\nSection 5: Modules");

    // Helper: program-level round-trip (parse → pretty → parse → compare).
    let check_prog_round_trip = |label: &str, src: &str| {
        match parse(src) {
            Ok(p) => {
                let pp = pretty(&p);
                match parse(&pp) {
                    Ok(p2) => {
                        if p == p2 {
                            println!("  PASS [prog round-trip] {}  =>  {}", label, pp.trim());
                        } else {
                            println!("  FAIL [prog round-trip] {}", label);
                            println!("       parsed:  {:?}", p);
                            println!("       printed: {}", pp);
                            println!("       re-parsed: {:?}", p2);
                            std::process::exit(1);
                        }
                    }
                    Err(e) => {
                        println!("  FAIL [prog re-parse] {}  =>  {}  (printed: {})", label, e, pp);
                        std::process::exit(1);
                    }
                }
            }
            Err(e) => {
                println!("  FAIL [prog parse] {}  =>  {}", label, e);
                std::process::exit(1);
            }
        }
    };

    // Imports.
    check_prog_round_trip("multi-name import", "import sort, head from \"collection\"");
    check_prog_round_trip("alias import", "import sort as s from \"collection/sort\"");
    check_prog_round_trip("whole import", "import \"collection\" as c");

    // Exports.
    check_prog_round_trip("export name", "export sort");
    check_prog_round_trip("export binding", "export sort = first(id) >>> insert");
    check_prog_round_trip("export all", "export *");
    check_prog_round_trip("re-export name", "export sort from \"collection/sort\"");
    check_prog_round_trip("re-export all", "export * from \"collection\"");

    // Full program with imports + bindings + exports round-trips.
    check_prog_round_trip(
        "full program",
        "import sort, head from \"collection\"\n\nadd = [x, y] ~> x + y\nexport sort, add",
    );

    // Desugar: import sort from "collection/sort" → Project/ModuleRef.
    match parse("import sort from \"collection/sort\"") {
        Ok(p) => {
            let ds = desugar(&p);
            let k = &ds.bindings[0].1;
            if matches!(k, Kernel::Project { field, record }
                if field == "sort"
                && matches!(record.as_ref(), Kernel::ModuleRef { path } if path == "collection/sort"))
            {
                println!("  PASS [desugar]    import sort  =>  {:?}", k);
            } else {
                println!("  FAIL [desugar]    import sort  =>  {:?}", k);
                std::process::exit(1);
            }
        }
        Err(e) => {
            println!("  FAIL [desugar parse] import sort  =>  {}", e);
            std::process::exit(1);
        }
    }

    // Desugar: import "collection" as c → ModuleRef.
    match parse("import \"collection\" as c") {
        Ok(p) => {
            let ds = desugar(&p);
            let k = &ds.bindings[0].1;
            if matches!(k, Kernel::ModuleRef { path } if path == "collection") {
                println!("  PASS [desugar]    import as c  =>  {:?}", k);
            } else {
                println!("  FAIL [desugar]    import as c  =>  {:?}", k);
                std::process::exit(1);
            }
        }
        Err(e) => {
            println!("  FAIL [desugar parse] import as c  =>  {}", e);
            std::process::exit(1);
        }
    }

    // Desugar: program with `export sort` has ExportSet::Names(["sort"]).
    match parse("sort = first(id)\nexport sort") {
        Ok(p) => {
            let ds = desugar(&p);
            match &ds.export_set {
                ExportSet::Names(ns) if ns == &vec!["sort".to_string()] => {
                    println!("  PASS [desugar]    export sort  =>  ExportSet::Names([\"sort\"])");
                }
                other => {
                    println!("  FAIL [desugar]    export sort  =>  {:?}", other);
                    std::process::exit(1);
                }
            }
        }
        Err(e) => {
            println!("  FAIL [desugar parse] export sort  =>  {}", e);
            std::process::exit(1);
        }
    }

    // Desugar: program with NO exports has ExportSet::All.
    match parse("sort = first(id)") {
        Ok(p) => {
            let ds = desugar(&p);
            if ds.export_set == ExportSet::All {
                println!("  PASS [desugar]    no exports  =>  ExportSet::All");
            } else {
                println!("  FAIL [desugar]    no exports  =>  {:?}", ds.export_set);
                std::process::exit(1);
            }
        }
        Err(e) => {
            println!("  FAIL [desugar parse] no exports  =>  {}", e);
            std::process::exit(1);
        }
    }

    // ------------------------------------------------------------------
    // 6. Law declarations (ADR-0076 `law ... forall ...` surface syntax)
    // ------------------------------------------------------------------
    println!("\nSection 6: Laws (law / forall)");

    // 6a. Simple law (no forall): law roundtrip: serialize >>> deserialize = id
    match parse_expr("law roundtrip: serialize >>> deserialize = id") {
        Ok(e) => match e {
            Expr::Law { name, vars, lhs, rhs } => {
                if name == "roundtrip"
                    && vars.is_empty()
                    && matches!(lhs.as_ref(), Expr::Compose { l, r }
                        if matches!(l.as_ref(), Expr::Var(ref n) if n == "serialize")
                        && matches!(r.as_ref(), Expr::Var(ref n) if n == "deserialize"))
                    && matches!(rhs.as_ref(), Expr::Var(ref n) if n == "id")
                {
                    println!("  PASS [ast] law roundtrip (no forall)");
                } else {
                    println!("  FAIL [ast] law roundtrip: name={:?} vars={:?} lhs={:?} rhs={:?}", name, vars, lhs, rhs);
                    std::process::exit(1);
                }
            }
            other => {
                println!("  FAIL [ast] expected Expr::Law, got {:?}", other);
                std::process::exit(1);
            }
        },
        Err(e) => {
            println!("  FAIL [parse] law roundtrip  =>  {}", e);
            std::process::exit(1);
        }
    }

    // 6b. Law with forall (two vars): law map_comp: forall f g. first(f >>> g) = first(f) >>> first(g)
    match parse_expr("law map_comp: forall f g. first(f >>> g) = first(f) >>> first(g)") {
        Ok(e) => match e {
            Expr::Law { name, vars, lhs, rhs } => {
                let vars_ok = vars == vec!["f".to_string(), "g".to_string()];
                // lhs: first(f >>> g)  ~>  App(Var("first"), Paren(Compose(Var f, Var g)))
                // (the parser wraps parenthesized args in Expr::Paren)
                let lhs_ok = matches!(lhs.as_ref(),
                    Expr::App { f, arg }
                        if matches!(f.as_ref(), Expr::Var(ref n) if n == "first")
                        && matches!(arg.as_ref(), Expr::Paren { inner }
                            if matches!(inner.as_ref(), Expr::Compose { l, r }
                                if matches!(l.as_ref(), Expr::Var(ref n) if n == "f")
                                && matches!(r.as_ref(), Expr::Var(ref n) if n == "g"))));
                // rhs: first(f) >>> first(g)  ~>  Compose(App(first, Paren(f)), App(first, Paren(g)))
                let rhs_ok = matches!(rhs.as_ref(),
                    Expr::Compose { l, r }
                        if matches!(l.as_ref(), Expr::App { f, arg }
                            if matches!(f.as_ref(), Expr::Var(ref n) if n == "first")
                            && matches!(arg.as_ref(), Expr::Paren { inner }
                                if matches!(inner.as_ref(), Expr::Var(ref n) if n == "f")))
                        && matches!(r.as_ref(), Expr::App { f, arg }
                            if matches!(f.as_ref(), Expr::Var(ref n) if n == "first")
                            && matches!(arg.as_ref(), Expr::Paren { inner }
                                if matches!(inner.as_ref(), Expr::Var(ref n) if n == "g"))));
                if name == "map_comp" && vars_ok && lhs_ok && rhs_ok {
                    println!("  PASS [ast] law map_comp (forall f g)");
                } else {
                    println!("  FAIL [ast] law map_comp: name={:?} vars={:?} lhs={:?} rhs={:?}", name, vars, lhs, rhs);
                    std::process::exit(1);
                }
            }
            other => {
                println!("  FAIL [ast] expected Expr::Law, got {:?}", other);
                std::process::exit(1);
            }
        },
        Err(e) => {
            println!("  FAIL [parse] law map_comp  =>  {}", e);
            std::process::exit(1);
        }
    }

    // 6c. Law with single-var forall: law map_id: forall f. first(id) = id
    match parse_expr("law map_id: forall f. first(id) = id") {
        Ok(e) => match e {
            Expr::Law { name, vars, lhs, rhs } => {
                let vars_ok = vars == vec!["f".to_string()];
                // lhs: first(id)  ~>  App(Var("first"), Paren(Var("id")))
                let lhs_ok = matches!(lhs.as_ref(),
                    Expr::App { f, arg }
                        if matches!(f.as_ref(), Expr::Var(ref n) if n == "first")
                        && matches!(arg.as_ref(), Expr::Paren { inner }
                            if matches!(inner.as_ref(), Expr::Var(ref n) if n == "id")));
                // rhs: id  ~>  Var("id")
                let rhs_ok = matches!(rhs.as_ref(), Expr::Var(ref n) if n == "id");
                if name == "map_id" && vars_ok && lhs_ok && rhs_ok {
                    println!("  PASS [ast] law map_id (forall f)");
                } else {
                    println!("  FAIL [ast] law map_id: name={:?} vars={:?} lhs={:?} rhs={:?}", name, vars, lhs, rhs);
                    std::process::exit(1);
                }
            }
            other => {
                println!("  FAIL [ast] expected Expr::Law, got {:?}", other);
                std::process::exit(1);
            }
        },
        Err(e) => {
            println!("  FAIL [parse] law map_id  =>  {}", e);
            std::process::exit(1);
        }
    }

    // 6d. Pretty-print round-trip for laws.
    check_round_trip("law no forall", "law roundtrip: serialize >>> deserialize = id");
    check_round_trip("law forall single", "law map_id: forall f. first(id) = id");
    check_round_trip("law forall two", "law map_comp: forall f g. first(f >>> g) = first(f) >>> first(g)");

    // 6e. Law as a binding value (a law can appear at the expression level).
    match parse("map_law = law roundtrip: serialize >>> deserialize = id") {
        Ok(p) => {
            if p.bindings.len() == 1 {
                match &p.bindings[0].value {
                    Expr::Law { name, vars, .. } if name == "roundtrip" && vars.is_empty() => {
                        println!("  PASS [binding] law as binding value");
                    }
                    other => {
                        println!("  FAIL [binding] expected Law value, got {:?}", other);
                        std::process::exit(1);
                    }
                }
            } else {
                println!("  FAIL [binding] expected 1 binding, got {}", p.bindings.len());
                std::process::exit(1);
            }
        }
        Err(e) => {
            println!("  FAIL [binding parse] law as binding  =>  {}", e);
            std::process::exit(1);
        }
    }

    // 6f. Program-level round-trip with a law as a binding value.
    check_prog_round_trip(
        "program with law binding",
        "roundtrip = law roundtrip: serialize >>> deserialize = id",
    );
    check_prog_round_trip(
        "program with quantified law binding",
        "mc = law map_comp: forall f g. first(f >>> g) = first(f) >>> first(g)",
    );

    // 6g. Desugar: a law lowers to a placeholder Kernel::Arr { op: "law", .. }.
    check_desugar(
        "law",
        "law roundtrip: serialize >>> deserialize = id",
        &|k| matches!(k, Kernel::Arr { op, .. } if op == "law"),
    );

    println!("\nAll tests passed.");
}
