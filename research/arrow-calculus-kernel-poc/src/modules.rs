// handl v0.1 — Pluggable Module Resolver and Normalization Strategies
// ADR-0069 §4 (two caches), §5 (three strategies), §7 (multi-file).
//
// This is a standalone test binary in the PoC style (fn main() with
// assertions). It is std-only (no external dependencies). It wires to the
// existing parser/desugar via #[path = "v0_1_surface.rs"] and implements:
//
//   - ResolvedModule + ResolveError
//   - ModuleResolver trait + FileResolver / MemoryResolver / ChainResolver / CachingResolver
//   - Contract (ADR-0070 real refinement inference via refinement_engine)
//   - ModuleLoader (two caches: graph + contract, Strategy C)
//   - normalize_compile_time  (Strategy A — eager, static IR)
//   - flatten_program         (Strategy B — whole-program flattening)
//
// See ADR-0069 §5 for the three strategies and §4 for the two caches.

// === Section 1: v0_1_surface module wiring ===

#[path = "v0_1_surface.rs"]
mod v0_1_surface;

use v0_1_surface::desugar::{DesugaredProgram, ExportSet};
use v0_1_surface::ast::Lit;

// Re-export Kernel, parse, desugar so downstream test binaries can
// construct values compatible with kernel_to_rgraph (ADR-0070) and
// parse source directly. Also used internally by this module.
pub use v0_1_surface::Kernel;
pub use v0_1_surface::parse;
pub use v0_1_surface::desugar;

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::path::PathBuf;
use std::rc::Rc;

// === Section 1b: refinement engine module (ADR-0070) ===

#[path = "refinement_engine.rs"]
pub mod refinement_engine;

use refinement_engine::{
    infer_refinement, standard_sig, BaseTy, Pred, RGraph, RefSigEntry, RefTy,
};

// === Section 2: ResolvedModule and errors ===

/// A resolved module: its logical path, source text, and origin label
/// (e.g. "file", "memory", "virtual"). Produced by a `ModuleResolver`.
/// (ADR-0069 §4 — the loader consumes resolved modules to populate caches.)
#[derive(Debug, Clone)]
pub struct ResolvedModule {
    pub path: String,
    pub source: String,
    pub origin: String,
}

/// Error kind for module resolution failures.
#[derive(Debug, Clone)]
pub enum ResolveErrorKind {
    /// The path was not found by any resolver in the chain.
    NotFound,
    /// An I/O error occurred while reading the module source.
    IoError(String),
    /// The host denied the capability required to resolve this path
    /// (ADR-0046 — capability discipline).
    Disallowed,
}

/// A resolution error: the path that failed plus a kind.
#[derive(Debug, Clone)]
pub struct ResolveError {
    pub path: String,
    pub kind: ResolveErrorKind,
}

impl std::fmt::Display for ResolveError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match &self.kind {
            ResolveErrorKind::NotFound => {
                write!(f, "module not found: {}", self.path)
            }
            ResolveErrorKind::IoError(msg) => {
                write!(f, "io error resolving {}: {}", self.path, msg)
            }
            ResolveErrorKind::Disallowed => {
                write!(
                    f,
                    "capability denied: cannot resolve {} (ADR-0046)",
                    self.path
                )
            }
        }
    }
}

// === Section 3: ModuleResolver trait + built-in resolvers ===

/// The module resolver trait. Resolution is a host capability boundary
/// (ADR-0046, ADR-0028, ADR-0035): the resolver set determines which paths
/// are importable. `resolve(&self)` is immutable; caches use interior
/// mutability (`RefCell`).
///
/// See ADR-0069 §4 and ARROW_DESUGARING_V0_1.md §12.6.
pub trait ModuleResolver {
    /// Resolve a module path to its source text.
    fn resolve(&self, path: &str) -> Result<ResolvedModule, ResolveError>;
    /// A short label for where this resolver finds modules ("file", "memory",
    /// "chain", "cache").
    fn origin(&self) -> &'static str;
}

/// `FileResolver` — resolves `path` to `<root>/<path>.hnl` (appending `.hnl`
/// if the path has no extension). Reads the file from disk. origin = "file".
/// This is the default resolver for compiled builds (ADR-0069 §7).
pub struct FileResolver {
    root: PathBuf,
}

impl FileResolver {
    pub fn new(root: PathBuf) -> Self {
        FileResolver { root }
    }
}

impl ModuleResolver for FileResolver {
    fn resolve(&self, path: &str) -> Result<ResolvedModule, ResolveError> {
        // Append .hnl if the path has no extension.
        let mut file_path = self.root.clone();
        file_path.push(path);
        if file_path.extension().is_none() {
            file_path.set_extension("hnl");
        }
        match std::fs::read_to_string(&file_path) {
            Ok(source) => Ok(ResolvedModule {
                path: path.to_string(),
                source,
                origin: "file".to_string(),
            }),
            Err(e) => {
                let kind = if e.kind() == std::io::ErrorKind::NotFound {
                    ResolveErrorKind::NotFound
                } else {
                    ResolveErrorKind::IoError(e.to_string())
                };
                Err(ResolveError {
                    path: path.to_string(),
                    kind,
                })
            }
        }
    }

    fn origin(&self) -> &'static str {
        "file"
    }
}

/// `MemoryResolver` — resolves paths against an in-memory map of path to
/// source. Used for REPL, tests, and virtual environments. origin = "memory".
pub struct MemoryResolver {
    modules: HashMap<String, String>,
}

impl MemoryResolver {
    pub fn new() -> Self {
        MemoryResolver {
            modules: HashMap::new(),
        }
    }

    pub fn insert(&mut self, path: &str, source: &str) {
        self.modules.insert(path.to_string(), source.to_string());
    }
}

impl ModuleResolver for MemoryResolver {
    fn resolve(&self, path: &str) -> Result<ResolvedModule, ResolveError> {
        match self.modules.get(path) {
            Some(source) => Ok(ResolvedModule {
                path: path.to_string(),
                source: source.clone(),
                origin: "memory".to_string(),
            }),
            None => Err(ResolveError {
                path: path.to_string(),
                kind: ResolveErrorKind::NotFound,
            }),
        }
    }

    fn origin(&self) -> &'static str {
        "memory"
    }
}

/// `ChainResolver` — tries each resolver in order, returning the first Ok.
/// If all fail, returns the last error (or NotFound if empty). origin = "chain".
pub struct ChainResolver {
    resolvers: Vec<Box<dyn ModuleResolver>>,
}

impl ChainResolver {
    pub fn new(resolvers: Vec<Box<dyn ModuleResolver>>) -> Self {
        ChainResolver { resolvers }
    }
}

impl ModuleResolver for ChainResolver {
    fn resolve(&self, path: &str) -> Result<ResolvedModule, ResolveError> {
        let mut last_err = ResolveError {
            path: path.to_string(),
            kind: ResolveErrorKind::NotFound,
        };
        for r in &self.resolvers {
            match r.resolve(path) {
                Ok(m) => return Ok(m),
                Err(e) => last_err = e,
            }
        }
        Err(last_err)
    }

    fn origin(&self) -> &'static str {
        "chain"
    }
}

/// `CachingResolver` — wraps another resolver and caches resolved modules by
/// path. Uses `RefCell` since `resolve(&self)` is immutable. origin delegates
/// to the inner resolver.
pub struct CachingResolver {
    inner: Box<dyn ModuleResolver>,
    cache: RefCell<HashMap<String, ResolvedModule>>,
}

impl CachingResolver {
    pub fn new(inner: Box<dyn ModuleResolver>) -> Self {
        CachingResolver {
            inner,
            cache: RefCell::new(HashMap::new()),
        }
    }
}

impl ModuleResolver for CachingResolver {
    fn resolve(&self, path: &str) -> Result<ResolvedModule, ResolveError> {
        if let Some(m) = self.cache.borrow().get(path) {
            return Ok(m.clone());
        }
        match self.inner.resolve(path) {
            Ok(m) => {
                self.cache.borrow_mut().insert(path.to_string(), m.clone());
                Ok(m)
            }
            Err(e) => Err(e),
        }
    }

    fn origin(&self) -> &'static str {
        self.inner.origin()
    }
}

// === Section 4: Contract (ADR-0069 §4 / ADR-0070 — real refinement inference) ===

/// A contract inferred by the refinement engine (ADR-0070). Captures a
/// best-effort arrow type signature and a list of refinement predicates
/// (guarantees + loop invariants). Both caches in `ModuleLoader` (§4) are
/// keyed by path; the contract cache stores these.
#[derive(Debug, Clone, PartialEq)]
pub struct Contract {
    /// A best-effort arrow type signature, e.g. "List α ~> { x : α | Sorted(x) }".
    pub signature: String,
    /// Refinement predicates, e.g. ["Sorted(output)"].
    pub refinements: Vec<String>,
}

/// Translate a Kernel graph to an RGraph for refinement inference.
/// ModuleRef and Project should be resolved BEFORE calling this (use
/// normalize_compile_time or flatten_program first). If they remain,
/// they are treated as unknown arrows (RGraph::Arr with the field/path name).
///
/// The surface syntax uses `loop(...)`, `first(...)`, `choice(...)` as
/// function-call syntax, which the desugar turns into `Seq(arg, Var(name))`.
/// This function detects those patterns and translates them to the
/// corresponding RGraph combinators (Loop, First, Left).
pub fn kernel_to_rgraph(k: &Kernel) -> RGraph {
    match k {
        Kernel::Var(name) => RGraph::Arr(name.clone()),
        Kernel::Const(_) => RGraph::Arr("const".to_string()),
        Kernel::Arr { op, args } => {
            // arr("arrow", [pat, body]) is a lambda — translate the body.
            // arr("loop", ...) — shouldn't appear, Loop is a separate variant.
            // arr(name, []) is a base arrow reference.
            // arr(name, [arg]) is a base arrow applied to one arg — treat as
            //   comp(arg, arr(name)) if arg is a graph, else just arr(name).
            if args.is_empty() {
                RGraph::Arr(op.clone())
            } else if op == "arrow" && args.len() == 2 {
                // Lambda: translate the body (args[1]).
                kernel_to_rgraph(&args[1])
            } else if args.len() == 1 {
                // Single-arg arr: comp(arg, arr(op))
                RGraph::Comp(
                    Box::new(kernel_to_rgraph(&args[0])),
                    Box::new(RGraph::Arr(op.clone())),
                )
            } else {
                // Multi-arg or unknown: treat as a named arrow.
                RGraph::Arr(op.clone())
            }
        }
        Kernel::Seq { fst, snd } => {
            // The desugar turns `f(x)` into `Seq(x, Var(f))`. When f is one
            // of the kernel combinators (loop, first, choice), translate to
            // the corresponding RGraph combinator instead of a composition.
            if let Kernel::Var(name) = snd.as_ref() {
                match name.as_str() {
                    "loop" => return RGraph::Loop(Box::new(kernel_to_rgraph(fst))),
                    "first" => return RGraph::First(Box::new(kernel_to_rgraph(fst))),
                    "choice" => {
                        // choice(arg) with one arg: treat as Left (conservative).
                        // choice(a, b) desugars to Seq(b, Seq(a, Var("choice"))).
                        // Detect the two-arg form and use the first arg.
                        if let Kernel::Seq { fst: inner_a, snd: inner_b } = fst.as_ref() {
                            if let Kernel::Var(inner_name) = inner_b.as_ref() {
                                if inner_name == "choice" {
                                    // Two-arg choice: choice(a, b) = Seq(b, Seq(a, Var("choice")))
                                    // Use the first arg (a) as the left branch.
                                    return RGraph::Left(Box::new(kernel_to_rgraph(inner_a)));
                                }
                            }
                        }
                        return RGraph::Left(Box::new(kernel_to_rgraph(fst)));
                    }
                    _ => {}
                }
            }
            RGraph::Comp(
                Box::new(kernel_to_rgraph(fst)),
                Box::new(kernel_to_rgraph(snd)),
            )
        }
        Kernel::First { inner } => RGraph::First(Box::new(kernel_to_rgraph(inner))),
        Kernel::Choice { l, r } => {
            // Choice ≈ Left in the refinement engine (both are sum routing).
            // Use the left branch's refinement (conservative).
            let _ = r;
            RGraph::Left(Box::new(kernel_to_rgraph(l)))
        }
        Kernel::Loop { body } => RGraph::Loop(Box::new(kernel_to_rgraph(body))),
        Kernel::App { callee, args } => {
            // App to a Var(name): treat as comp(args, arr(name)).
            if let Kernel::Var(name) = callee.as_ref() {
                if args.len() == 1 {
                    RGraph::Comp(
                        Box::new(kernel_to_rgraph(&args[0])),
                        Box::new(RGraph::Arr(name.clone())),
                    )
                } else {
                    RGraph::Arr(name.clone())
                }
            } else {
                // App to a non-Var callee: translate the callee.
                kernel_to_rgraph(callee)
            }
        }
        Kernel::ModuleRef { path } => {
            // Should be resolved before inference. Treat as unknown arrow.
            RGraph::Arr(path.clone())
        }
        Kernel::Project { field, .. } => {
            // Should be resolved before inference. Treat as unknown arrow.
            RGraph::Arr(field.clone())
        }
        // `handle body with target = impl_` (ADR-0076). Compile-time handler
        // elimination: lower the impl to a concrete RGraph, lower the body,
        // then rewrite every Arr(target) reference in the body to the impl
        // graph. After this, the graph has no handler nodes and no unhandled
        // target references -- the handler is eliminated at compile time, not
        // runtime. This is the compile-time analogue of
        // `bundled_effects::handle_eliminate` / `eliminate_all_handlers`, but
        // operates on `RGraph` (the refinement-engine IR) via a structural
        // tree walk rather than through the `EffectGraph` machinery. See
        // `eliminate_handler_in_rgraph` below.
        Kernel::Handle { body, target, impl_ } => {
            let impl_graph = kernel_to_rgraph(impl_);
            let body_graph = kernel_to_rgraph(body);
            eliminate_handler_in_rgraph(&body_graph, target, &impl_graph)
        }
    }
}

/// Compile-time handler elimination (ADR-0076). Walk an `RGraph` and replace
/// every `RGraph::Arr(name)` where `name == target` with `impl_graph` (cloned).
/// This is the compile-time analogue of `handle_eliminate` in
/// `bundled_effects.rs`: an unhandled operation reference (`Arr(target)`) is
/// rewritten to the concrete handler graph. After elimination the graph has no
/// `Arr(target)` nodes for the handled target -- the handler is gone, replaced
/// by concrete arrows.
///
/// Recursion is structural: composition and the unary combinators (first,
/// left, loop) recurse into their children; leaves that do not match `target`
/// are returned as-is. This mirrors the tree walk in
/// `bundled_effects::handle_eliminate` but operates on `RGraph` (the
/// refinement-engine IR) rather than `EffectGraph`.
///
/// Nested handlers are eliminated innermost-first naturally: `kernel_to_rgraph`
/// recurses into the body of a `Kernel::Handle` before applying THIS handler's
/// elimination, so an inner `handle ... with a = impl_a` is fully eliminated
/// (its `Arr(a)` nodes replaced) before the outer handler's `Arr(target)` walk
/// runs. This matches `eliminate_all_handlers` in `bundled_effects.rs`.
pub fn eliminate_handler_in_rgraph(graph: &RGraph, target: &str, impl_graph: &RGraph) -> RGraph {
    match graph {
        // The unhandled operation reference: replace with the concrete impl.
        RGraph::Arr(name) if name == target => impl_graph.clone(),
        // Binary combinator: recurse into both children.
        RGraph::Comp(a, b) => RGraph::Comp(
            Box::new(eliminate_handler_in_rgraph(a, target, impl_graph)),
            Box::new(eliminate_handler_in_rgraph(b, target, impl_graph)),
        ),
        // Unary combinators: recurse into the single child.
        RGraph::First(a) => RGraph::First(Box::new(eliminate_handler_in_rgraph(
            a,
            target,
            impl_graph,
        ))),
        RGraph::Left(a) => RGraph::Left(Box::new(eliminate_handler_in_rgraph(
            a,
            target,
            impl_graph,
        ))),
        RGraph::Loop(a) => RGraph::Loop(Box::new(eliminate_handler_in_rgraph(
            a,
            target,
            impl_graph,
        ))),
        // Leaves that do not match target (Id, Arr(other)): return as-is.
        _ => graph.clone(),
    }
}

/// Infer a REAL contract from a desugared program using the refinement engine
/// (ADR-0070). Each binding's Kernel is translated to RGraph, then
/// infer_refinement derives the guarantee and loop invariants.
///
/// For multi-binding programs (record modules), the contract is the record
/// of each binding's contract. For single-binding programs, it's that
/// binding's contract.
pub fn infer_contract(desugared: &DesugaredProgram) -> Contract {
    let sig = standard_sig();

    if desugared.bindings.is_empty() {
        return Contract { signature: "Unit ~> Unit".to_string(), refinements: vec![] };
    }

    let mut all_refinements: Vec<String> = Vec::new();
    let mut signatures: Vec<String> = Vec::new();

    for (name, kernel) in &desugared.bindings {
        let rgraph = kernel_to_rgraph(kernel);
        match infer_refinement(&rgraph, &sig) {
            Ok(result) => {
                // Format the signature.
                let sig_str = format!("{}: {:?}", name, result.output_type);
                signatures.push(sig_str);

                // Collect refinements.
                let guarantee_str = result.guarantee.pretty();
                if guarantee_str != "True" {
                    all_refinements.push(format!("{}: {}", name, guarantee_str));
                }
                for inv in &result.loop_invariants {
                    all_refinements.push(format!("{}: loop invariant: {} ({})",
                        name, inv.invariant.pretty(),
                        if inv.verified_by_smt { "SMT-verified" } else { "unverified" }));
                }
            }
            Err(_) => {
                signatures.push(format!("{}: unknown", name));
            }
        }
    }

    let signature = if signatures.len() == 1 {
        signatures[0].clone()
    } else {
        format!("Record({})", signatures.join(", "))
    };

    Contract {
        signature,
        refinements: all_refinements,
    }
}

/// Helper: does this kernel tree contain a `Loop` node?
#[allow(dead_code)]
fn contains_loop(k: &Kernel) -> bool {
    match k {
        Kernel::Loop { body } => true || contains_loop(body),
        Kernel::Seq { fst, snd } => contains_loop(fst) || contains_loop(snd),
        Kernel::First { inner } => contains_loop(inner),
        Kernel::Choice { l, r } => contains_loop(l) || contains_loop(r),
        Kernel::App { callee, args } => {
            contains_loop(callee) || args.iter().any(contains_loop)
        }
        Kernel::Arr { args, .. } => args.iter().any(contains_loop),
        Kernel::Project { record, .. } => contains_loop(record),
        Kernel::Handle { body, impl_, .. } => contains_loop(body) || contains_loop(impl_),
        Kernel::Var(_) | Kernel::Const(_) | Kernel::ModuleRef { .. } => false,
    }
}

// === Section 5: LoadError ===

/// Errors that can occur during module loading or normalization.
#[derive(Debug, Clone)]
pub enum LoadError {
    /// A resolution failure (path not found, io error, capability denied).
    Resolve(ResolveError),
    /// A parse error (the source resolved but did not parse).
    Parse(String),
    /// An import cycle was detected. The vector lists the cycle path.
    Cycle(Vec<String>),
}

impl std::fmt::Display for LoadError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            LoadError::Resolve(e) => write!(f, "resolve error: {}", e),
            LoadError::Parse(msg) => write!(f, "parse error: {}", msg),
            LoadError::Cycle(path) => {
                write!(f, "import cycle detected: {}", path.join(" -> "))
            }
        }
    }
}

// === Section 6: LoadedModule and ModuleLoader (ADR-0069 §4, Strategy C) ===

/// The result of loading a module: its desugared graph and inferred contract,
/// cloned from the loader's caches.
#[derive(Debug, Clone)]
pub struct LoadedModule {
    pub graph: DesugaredProgram,
    pub contract: Contract,
}

/// `ModuleLoader` maintains two caches keyed by module path (ADR-0069 §4):
/// - **Graph cache**: `path → DesugaredProgram` (the parsed arrow graph).
/// - **Contract cache**: `path → Contract` (the inferred contract).
///
/// On first load, the loader resolves the source, parses it, desugars it,
/// infers its contract, and stores both in the caches. Subsequent loads
/// return cached clones. This is Strategy C (runtime module loading, lazy +
/// cached) — see ADR-0069 §5.
pub struct ModuleLoader {
    resolver: Box<dyn ModuleResolver>,
    graph_cache: RefCell<HashMap<String, DesugaredProgram>>,
    contract_cache: RefCell<HashMap<String, Contract>>,
}

impl ModuleLoader {
    pub fn new(resolver: Box<dyn ModuleResolver>) -> Self {
        ModuleLoader {
            resolver,
            graph_cache: RefCell::new(HashMap::new()),
            contract_cache: RefCell::new(HashMap::new()),
        }
    }

    /// Load a module by path. On first access: resolve → parse → desugar →
    /// infer contract → cache both. On subsequent access: return cached
    /// clones. Returns `LoadedModule` (graph + contract).
    pub fn load(&self, path: &str) -> Result<LoadedModule, LoadError> {
        // Cache hit?
        if let Some(graph) = self.graph_cache.borrow().get(path) {
            let contract = self
                .contract_cache
                .borrow()
                .get(path)
                .cloned()
                .unwrap_or_else(|| Contract {
                    signature: "Unit ~> Unit".to_string(),
                    refinements: vec![],
                });
            return Ok(LoadedModule {
                graph: graph.clone(),
                contract,
            });
        }

        // Resolve the source.
        let resolved = self.resolver.resolve(path).map_err(LoadError::Resolve)?;

        // Parse.
        let program = parse(&resolved.source).map_err(LoadError::Parse)?;

        // Desugar.
        let desugared = desugar(&program);

        // Infer contract (ADR-0070 refinement engine).
        let contract = infer_contract(&desugared);

        // Cache both.
        self.graph_cache
            .borrow_mut()
            .insert(path.to_string(), desugared.clone());
        self.contract_cache
            .borrow_mut()
            .insert(path.to_string(), contract.clone());

        Ok(LoadedModule {
            graph: desugared,
            contract,
        })
    }

    /// Compute the public names of a module. `ExportSet::All` → all binding
    /// names (including import-projected bindings). `ExportSet::Names(ns)` →
    /// ns (plus expanded reexports — see `expand_reexports`).
    ///
    /// Per ADR-0069, imports become bindings via projection, and with no
    /// export declarations ALL bindings are public (including import bindings).
    /// So a module `import insert from "..." \n sort = ...` with no exports
    /// has public names `["insert", "sort"]`.
    pub fn public_names(&self, path: &str) -> Result<Vec<String>, LoadError> {
        let loaded = self.load(path)?;
        let mut names = match &loaded.graph.export_set {
            ExportSet::All => loaded
                .graph
                .bindings
                .iter()
                .map(|(n, _)| n.clone())
                .collect::<Vec<String>>(),
            ExportSet::Names(ns) => ns.clone(),
        };

        // Expand reexports: for each `export * from "path"`, query that
        // module's public names and add them.
        for reexport_path in &loaded.graph.reexports {
            let remote_names = self.public_names(reexport_path)?;
            for n in remote_names {
                if !names.contains(&n) {
                    names.push(n);
                }
            }
        }

        Ok(names)
    }

    /// Expand `export * from "path"` markers left by the desugar pass.
    /// For each path in `desugared.reexports`, query `public_names(path)`,
    /// and for each name add a binding
    /// `(name, Kernel::Project { field: name, record: ModuleRef { path } })`
    /// and add the name to the export set. Returns a new `DesugaredProgram`
    /// with reexports cleared and the export set updated.
    ///
    /// If the export set was `All`, it stays `All` (all bindings public,
    /// including the new reexport bindings). If it was `Names`, extend with
    /// the new names.
    pub fn expand_reexports(
        &self,
        desugared: &DesugaredProgram,
    ) -> Result<DesugaredProgram, LoadError> {
        let mut bindings = desugared.bindings.clone();
        let mut export_set = desugared.export_set.clone();
        let mut added_names: Vec<String> = Vec::new();

        for reexport_path in &desugared.reexports {
            let remote_names = self.public_names(reexport_path)?;
            for name in remote_names {
                // Avoid duplicate bindings.
                if bindings.iter().any(|(n, _)| n == &name) {
                    continue;
                }
                bindings.push((
                    name.clone(),
                    Kernel::Project {
                        field: name.clone(),
                        record: Box::new(Kernel::ModuleRef {
                            path: reexport_path.clone(),
                        }),
                    },
                ));
                added_names.push(name);
            }
        }

        // Update export set.
        match &mut export_set {
            ExportSet::All => {
                // All bindings are public; the new reexport bindings are
                // included automatically. Keep All.
            }
            ExportSet::Names(ns) => {
                for n in added_names {
                    if !ns.contains(&n) {
                        ns.push(n);
                    }
                }
            }
        }

        Ok(DesugaredProgram {
            bindings,
            export_set,
            reexports: Vec::new(), // cleared
        })
    }
}

// === Section 7: Kernel traversal helpers ===

/// Does this kernel tree contain any `Kernel::ModuleRef` node?
pub fn contains_module_ref(k: &Kernel) -> bool {
    match k {
        Kernel::ModuleRef { .. } => true,
        Kernel::Seq { fst, snd } => contains_module_ref(fst) || contains_module_ref(snd),
        Kernel::First { inner } => contains_module_ref(inner),
        Kernel::Choice { l, r } => contains_module_ref(l) || contains_module_ref(r),
        Kernel::Loop { body } => contains_module_ref(body),
        Kernel::App { callee, args } => {
            contains_module_ref(callee) || args.iter().any(contains_module_ref)
        }
        Kernel::Arr { args, .. } => args.iter().any(contains_module_ref),
        Kernel::Project { record, .. } => contains_module_ref(record),
        Kernel::Handle { body, impl_, .. } => {
            contains_module_ref(body) || contains_module_ref(impl_)
        }
        Kernel::Var(_) | Kernel::Const(_) => false,
    }
}

/// Does this kernel tree contain any `Kernel::Project` node?
pub fn contains_project(k: &Kernel) -> bool {
    match k {
        Kernel::Project { record, .. } => true || contains_project(record),
        Kernel::Seq { fst, snd } => contains_project(fst) || contains_project(snd),
        Kernel::First { inner } => contains_project(inner),
        Kernel::Choice { l, r } => contains_project(l) || contains_project(r),
        Kernel::Loop { body } => contains_project(body),
        Kernel::App { callee, args } => {
            contains_project(callee) || args.iter().any(contains_project)
        }
        Kernel::Arr { args, .. } => args.iter().any(contains_project),
        Kernel::Handle { body, impl_, .. } => contains_project(body) || contains_project(impl_),
        Kernel::Var(_) | Kernel::Const(_) | Kernel::ModuleRef { .. } => false,
    }
}

/// Recursively transform a kernel, applying a substitution function to each
/// node bottom-up.
fn transform_kernel<F>(k: &Kernel, f: &F) -> Kernel
where
    F: Fn(&Kernel) -> Kernel,
{
    // First recurse into children, then apply f to the result.
    let transformed = match k {
        Kernel::Arr { op, args } => Kernel::Arr {
            op: op.clone(),
            args: args.iter().map(|a| transform_kernel(a, f)).collect(),
        },
        Kernel::Seq { fst, snd } => Kernel::Seq {
            fst: Box::new(transform_kernel(fst, f)),
            snd: Box::new(transform_kernel(snd, f)),
        },
        Kernel::First { inner } => Kernel::First {
            inner: Box::new(transform_kernel(inner, f)),
        },
        Kernel::Choice { l, r } => Kernel::Choice {
            l: Box::new(transform_kernel(l, f)),
            r: Box::new(transform_kernel(r, f)),
        },
        Kernel::Loop { body } => Kernel::Loop {
            body: Box::new(transform_kernel(body, f)),
        },
        Kernel::App { callee, args } => Kernel::App {
            callee: Box::new(transform_kernel(callee, f)),
            args: args.iter().map(|a| transform_kernel(a, f)).collect(),
        },
        Kernel::Project { field, record } => Kernel::Project {
            field: field.clone(),
            record: Box::new(transform_kernel(record, f)),
        },
        other => other.clone(),
    };
    f(&transformed)
}

/// Collect all module paths referenced by `Kernel::ModuleRef` nodes in the
/// tree (deduplicated, preserving first-seen order).
fn collect_module_refs(k: &Kernel) -> Vec<String> {
    let mut paths: Vec<String> = Vec::new();
    collect_module_refs_into(k, &mut paths);
    paths
}

fn collect_module_refs_into(k: &Kernel, out: &mut Vec<String>) {
    match k {
        Kernel::ModuleRef { path } => {
            if !out.contains(path) {
                out.push(path.clone());
            }
        }
        Kernel::Seq { fst, snd } => {
            collect_module_refs_into(fst, out);
            collect_module_refs_into(snd, out);
        }
        Kernel::First { inner } => collect_module_refs_into(inner, out),
        Kernel::Choice { l, r } => {
            collect_module_refs_into(l, out);
            collect_module_refs_into(r, out);
        }
        Kernel::Loop { body } => collect_module_refs_into(body, out),
        Kernel::App { callee, args } => {
            collect_module_refs_into(callee, out);
            for a in args {
                collect_module_refs_into(a, out);
            }
        }
        // Recognize BOTH encodings of module_ref (ADR-0009 §1, §5): the
        // dedicated Kernel::ModuleRef variant (handled above) AND the
        // stringly-typed arr form `arr("module_ref", [Const(Str(path))])`.
        Kernel::Arr { op, args } => {
            if op == "module_ref" {
                if let Some(Kernel::Const(Lit::Str(path))) = args.get(0) {
                    if !out.contains(path) {
                        out.push(path.clone());
                    }
                }
            }
            for a in args {
                collect_module_refs_into(a, out);
            }
        }
        Kernel::Project { record, .. } => collect_module_refs_into(record, out),
        Kernel::Handle { body, impl_, .. } => {
            collect_module_refs_into(body, out);
            collect_module_refs_into(impl_, out);
        }
        Kernel::Var(_) | Kernel::Const(_) => {}
    }
}

/// Build a record literal kernel from a list of (name, kernel) pairs,
/// representing a module's public bindings. Each field is
/// `arr("field", [Const(Str(name)), kernel])`, wrapped in
/// `arr("record", [...])`, wrapped in `arr("module_record", [...])`.
fn build_module_record(public_bindings: &[(String, Kernel)]) -> Kernel {
    let fields: Vec<Kernel> = public_bindings
        .iter()
        .map(|(name, k)| {
            Kernel::arr(
                "field",
                vec![Kernel::Const(Lit::Str(name.clone())), k.clone()],
            )
        })
        .collect();
    let record = Kernel::arr("record", fields);
    Kernel::arr("module_record", vec![record])
}

// === Section 8: Strategy A — normalize_compile_time (eager, static IR) ===

/// Normalization Strategy A (ADR-0069 §5): compile-time desugar.
///
/// Resolves the entry module, parse+desugar it, then walks its bindings:
/// every `Kernel::ModuleRef { path }` is replaced by an inlined record literal
/// (`arr("module_record", [arr("record", [...])])`) containing the resolved
/// module's PUBLIC bindings. Recurses transitively with cycle detection.
///
/// The result is a self-contained `DesugaredProgram` where no `ModuleRef`
/// remains (all inlined as record literals). `Project` nodes remain — they
/// now project from an inlined record literal. This is correct for Strategy A.
pub fn normalize_compile_time(
    entry_path: &str,
    loader: &ModuleLoader,
) -> Result<DesugaredProgram, LoadError> {
    let mut visited: Vec<String> = Vec::new();
    normalize_compile_time_inner(entry_path, loader, &mut visited)
}

fn normalize_compile_time_inner(
    path: &str,
    loader: &ModuleLoader,
    visited: &mut Vec<String>,
) -> Result<DesugaredProgram, LoadError> {
    // Cycle detection.
    if visited.contains(&path.to_string()) {
        let mut cycle: Vec<String> = Vec::new();
        let start_idx = visited.iter().position(|p| p == path).unwrap_or(0);
        for p in &visited[start_idx..] {
            cycle.push(p.clone());
        }
        cycle.push(path.to_string());
        return Err(LoadError::Cycle(cycle));
    }
    visited.push(path.to_string());

    // Load the module.
    let loaded = loader.load(path)?;
    let desugared = loader.expand_reexports(&loaded.graph)?;

    // Collect all module paths referenced in this module's bindings.
    let ref_paths: Vec<String> = desugared
        .bindings
        .iter()
        .flat_map(|(_, k)| collect_module_refs(k))
        .collect::<Vec<String>>();

    // Recursively normalize each referenced module and build a replacement map:
    // path -> inlined module record kernel.
    let mut inline_map: HashMap<String, Kernel> = HashMap::new();
    for ref_path in &ref_paths {
        if inline_map.contains_key(ref_path) {
            continue;
        }
        let child = normalize_compile_time_inner(ref_path, loader, visited)?;
        let pub_binds = public_bindings_from(&child);
        inline_map.insert(ref_path.clone(), build_module_record(&pub_binds));
    }

    // Replace every ModuleRef { path } in every binding with the inlined record.
    let new_bindings: Vec<(String, Kernel)> = desugared
        .bindings
        .iter()
        .map(|(name, k)| {
            let new_k = replace_module_refs(k, &inline_map);
            (name.clone(), new_k)
        })
        .collect();

    // Pop this path from the visited stack (allow diamond dependencies).
    visited.pop();

    Ok(DesugaredProgram {
        bindings: new_bindings,
        export_set: desugared.export_set,
        reexports: Vec::new(),
    })
}

/// Extract public bindings from a DesugaredProgram (assumes reexports already
/// expanded).
fn public_bindings_from(desugared: &DesugaredProgram) -> Vec<(String, Kernel)> {
    let names = match &desugared.export_set {
        ExportSet::All => desugared
            .bindings
            .iter()
            .map(|(n, _)| n.clone())
            .collect::<Vec<String>>(),
        ExportSet::Names(ns) => ns.clone(),
    };
    desugared
        .bindings
        .iter()
        .filter(|(n, _)| names.contains(n))
        .cloned()
        .collect()
}

/// Replace every `Kernel::ModuleRef { path }` with `inline_map[path]` (cloned).
/// Paths not in the map are left as-is (should not happen if all refs were
/// collected).
fn replace_module_refs(k: &Kernel, map: &HashMap<String, Kernel>) -> Kernel {
    transform_kernel(k, &|node| match node {
        Kernel::ModuleRef { path } => match map.get(path) {
            Some(replacement) => replacement.clone(),
            None => Kernel::ModuleRef {
                path: path.clone(),
            },
        },
        other => other.clone(),
    })
}

// === Section 9: Strategy B — flatten_program (whole-program flattening) ===

/// Normalization Strategy B (ADR-0069 §5): whole-program flattening.
///
/// Like Strategy A but goes further: after inlining all module records, also
/// resolve every `Kernel::Project { field, record }` to the actual field
/// binding's kernel (look up `field` in the inlined record), and every
/// `Kernel::App { callee, args }` where callee is a `Var(name)` that resolves
/// to an inlined binding — substitute the callee's kernel. The result is a
/// SINGLE kernel graph with no `ModuleRef`, no `Project`, and no top-level
/// `App` to imported names.
///
/// The entry's "main arrow" is: if the entry has a single binding, that
/// binding's (flattened) kernel; if multiple bindings, the record of all
/// PUBLIC bindings (flattened). Returns that single `Kernel`.
pub fn flatten_program(entry_path: &str, loader: &ModuleLoader) -> Result<Kernel, LoadError> {
    let mut visited: Vec<String> = Vec::new();
    flatten_program_inner(entry_path, loader, &mut visited)
}

fn flatten_program_inner(
    path: &str,
    loader: &ModuleLoader,
    visited: &mut Vec<String>,
) -> Result<Kernel, LoadError> {
    // Cycle detection.
    if visited.contains(&path.to_string()) {
        let mut cycle: Vec<String> = Vec::new();
        let start_idx = visited.iter().position(|p| p == path).unwrap_or(0);
        for p in &visited[start_idx..] {
            cycle.push(p.clone());
        }
        cycle.push(path.to_string());
        return Err(LoadError::Cycle(cycle));
    }
    visited.push(path.to_string());

    // Load and expand reexports.
    let loaded = loader.load(path)?;
    let desugared = loader.expand_reexports(&loaded.graph)?;

    // Collect all module paths referenced.
    let ref_paths: Vec<String> = desugared
        .bindings
        .iter()
        .flat_map(|(_, k)| collect_module_refs(k))
        .collect::<Vec<String>>();

    // Recursively flatten each referenced module and build a map:
    // path -> (public bindings as (name, flattened kernel) pairs).
    let mut module_records: HashMap<String, Vec<(String, Kernel)>> = HashMap::new();
    for ref_path in &ref_paths {
        if module_records.contains_key(ref_path) {
            continue;
        }
        let _child_kernel = flatten_program_inner(ref_path, loader, visited)?;
        // The child kernel IS the module's main arrow. For a multi-binding
        // module, it's a record; for a single-binding module, it's that
        // binding's kernel. We need the public bindings as name->kernel pairs.
        // Re-load to get the bindings, then flatten each binding.
        let child_loaded = loader.load(ref_path)?;
        let child_expanded = loader.expand_reexports(&child_loaded.graph)?;
        let child_pub = public_bindings_from(&child_expanded);
        // Flatten each binding: replace ModuleRefs with inlined records, then
        // resolve Projects and App-to-Vars.
        let mut flattened_binds: Vec<(String, Kernel)> = Vec::new();
        for (bname, bk) in &child_pub {
            let inlined = inline_module_refs(bk, &module_records, ref_path, loader, visited)?;
            let resolved = resolve_projects_and_apps(&inlined, &child_pub);
            flattened_binds.push((bname.clone(), resolved));
        }
        module_records.insert(ref_path.clone(), flattened_binds);
    }

    // Now flatten this module's bindings.
    let pub_binds = public_bindings_from(&desugared);
    let mut flattened_bindings: Vec<(String, Kernel)> = Vec::new();
    for (name, k) in &pub_binds {
        let inlined = inline_module_refs(k, &module_records, path, loader, visited)?;
        let resolved = resolve_projects_and_apps(&inlined, &pub_binds);
        flattened_bindings.push((name.clone(), resolved));
    }

    visited.pop();

    // The entry's main arrow:
    if flattened_bindings.len() == 1 {
        Ok(flattened_bindings[0].1.clone())
    } else {
        // Build a record of all public bindings.
        let fields: Vec<Kernel> = flattened_bindings
            .iter()
            .map(|(name, k)| {
                Kernel::arr(
                    "field",
                    vec![Kernel::Const(Lit::Str(name.clone())), k.clone()],
                )
            })
            .collect();
        Ok(Kernel::arr("record", fields))
    }
}

/// Replace every `ModuleRef { path }` with an inlined record of the module's
/// public bindings (already flattened). Uses the `module_records` map; if a
/// path isn't in the map yet, recursively flatten it.
fn inline_module_refs(
    k: &Kernel,
    module_records: &HashMap<String, Vec<(String, Kernel)>>,
    _current_path: &str,
    loader: &ModuleLoader,
    visited: &mut Vec<String>,
) -> Result<Kernel, LoadError> {
    // Collect refs in this kernel.
    let refs = collect_module_refs(k);
    let mut inline_map: HashMap<String, Kernel> = HashMap::new();
    for ref_path in &refs {
        if inline_map.contains_key(ref_path) {
            continue;
        }
        if let Some(binds) = module_records.get(ref_path) {
            inline_map.insert(ref_path.clone(), build_module_record(binds));
        } else {
            // Need to flatten this child.
            let _child_kernel = flatten_program_inner(ref_path, loader, visited)?;
            // Re-load to get bindings and flatten them.
            let child_loaded = loader.load(ref_path)?;
            let child_expanded = loader.expand_reexports(&child_loaded.graph)?;
            let child_pub = public_bindings_from(&child_expanded);
            let mut flattened_binds: Vec<(String, Kernel)> = Vec::new();
            for (bname, bk) in &child_pub {
                let inlined = inline_module_refs(
                    bk,
                    module_records,
                    ref_path,
                    loader,
                    visited,
                )?;
                let resolved = resolve_projects_and_apps(&inlined, &child_pub);
                flattened_binds.push((bname.clone(), resolved));
            }
            inline_map.insert(ref_path.clone(), build_module_record(&flattened_binds));
        }
    }
    Ok(replace_module_refs(k, &inline_map))
}

/// Resolve `Project { field, record }` nodes: if `record` is an inlined
/// module record (`arr("module_record", [arr("record", [field_kernels])])`),
/// look up `field` in the field kernels and substitute. Also resolve
/// `App { callee: Var(name), args }` where `name` is a binding in `bindings`:
/// substitute the callee's kernel (keeping args as a Seq prefix).
///
/// This is the core of Strategy B: no Project, no ModuleRef, no App-to-import.
fn resolve_projects_and_apps(k: &Kernel, bindings: &[(String, Kernel)]) -> Kernel {
    transform_kernel(k, &|node| match node {
        Kernel::Project { field, record } => {
            // Try to resolve the project from an inlined record.
            if let Some(target) = lookup_field_in_record(record, field) {
                target
            } else {
                Kernel::Project {
                    field: field.clone(),
                    record: Box::new(record.as_ref().clone()),
                }
            }
        }
        Kernel::App { callee, args } => {
            // If callee is a Var(name) that matches a binding, substitute.
            if let Kernel::Var(name) = callee.as_ref() {
                if let Some((_, target_k)) = bindings.iter().find(|(n, _)| n == name) {
                    // App to a resolved arrow: Seq(args, target). For multiple
                    // args, Seq them together first.
                    let args_kernel = if args.len() == 1 {
                        args[0].clone()
                    } else if args.is_empty() {
                        Kernel::arr("unit", vec![])
                    } else {
                        Kernel::arr("tuple", args.clone())
                    };
                    return Kernel::seq(args_kernel, target_k.clone());
                }
            }
            Kernel::App {
                callee: callee.clone(),
                args: args.clone(),
            }
        }
        other => other.clone(),
    })
}

/// Look up a field by name in an inlined module record. The record is expected
/// to be `arr("module_record", [arr("record", [field_kernels])])` where each
/// field kernel is `arr("field", [Const(Str(name)), value])`. Returns the
/// value kernel if found.
fn lookup_field_in_record(record: &Kernel, field: &str) -> Option<Kernel> {
    // Unwrap module_record wrapper.
    let inner = match record {
        Kernel::Arr { op, args } if op == "module_record" && !args.is_empty() => &args[0],
        _ => return None,
    };
    // inner should be arr("record", [field_kernels])
    let fields = match inner {
        Kernel::Arr { op, args } if op == "record" => args,
        _ => return None,
    };
    for f in fields {
        if let Kernel::Arr { op, args } = f {
            if op == "field" && args.len() == 2 {
                if let Kernel::Const(Lit::Str(name)) = &args[0] {
                    if name == field {
                        return Some(args[1].clone());
                    }
                }
            }
        }
    }
    None
}

// === Section 10: CountingResolver (for cache-hit verification in tests) ===

/// A wrapper resolver that counts how many times `resolve` is called. Used in
/// tests to verify that `CachingResolver` and `ModuleLoader` caches prevent
/// redundant resolution. The count is shared via `Rc<Cell<usize>>` so it can
/// be read externally even after the resolver is boxed.
pub struct CountingResolver {
    inner: Box<dyn ModuleResolver>,
    count: Rc<Cell<usize>>,
}

impl CountingResolver {
    pub fn new(inner: Box<dyn ModuleResolver>) -> Self {
        CountingResolver {
            inner,
            count: Rc::new(Cell::new(0)),
        }
    }

    /// Create a CountingResolver and return a shared counter handle alongside
    /// it, so tests can read the call count after the resolver is boxed.
    pub fn new_with_counter(
        inner: Box<dyn ModuleResolver>,
    ) -> (Self, Rc<Cell<usize>>) {
        let count = Rc::new(Cell::new(0));
        let r = CountingResolver {
            inner,
            count: count.clone(),
        };
        (r, count)
    }

    pub fn call_count(&self) -> usize {
        self.count.get()
    }
}

impl ModuleResolver for CountingResolver {
    fn resolve(&self, path: &str) -> Result<ResolvedModule, ResolveError> {
        self.count.set(self.count.get() + 1);
        self.inner.resolve(path)
    }

    fn origin(&self) -> &'static str {
        self.inner.origin()
    }
}

// === Section 11: Static cycle detection (ADR-0009 §4) ===

/// Error from the static cycle-detection pass (ADR-0009 §4). Either an
/// import cycle (the vector lists the cycle as a sequence of paths) or a
/// load failure encountered while walking the import graph.
#[derive(Debug, Clone)]
pub enum CycleError {
    /// An import cycle was detected. The vector holds the cycle path, e.g.
    /// `["cycle_a", "cycle_b", "cycle_a"]`.
    Cycle(Vec<String>),
    /// A referenced module failed to load (resolve/parse) while building the
    /// import graph. Cycle detection is a static pass but uses the loader to
    /// read referenced modules' source (parsing is allowed; interpreting is
    /// not — see ADR-0009 §4).
    Load(LoadError),
}

impl std::fmt::Display for CycleError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            CycleError::Cycle(path) => {
                write!(f, "import cycle detected: {}", path.join(" -> "))
            }
            CycleError::Load(e) => write!(f, "load error during cycle detection: {}", e),
        }
    }
}

/// Collect all module paths referenced by `Kernel::ModuleRef` nodes AND by
/// the stringly-typed `arr("module_ref", [Const(Str(path))])` form
/// (ADR-0009 §1, §5), deduplicated, preserving first-seen order. Reuses the
/// generalized `collect_module_refs_into` recursive walk (Section 7) which
/// recognizes both encodings.
pub fn collect_module_refs_both(k: &Kernel) -> Vec<String> {
    let mut paths: Vec<String> = Vec::new();
    collect_module_refs_into(k, &mut paths);
    paths
}

/// Static cycle-detection pass (ADR-0009 §4). Walks `entry`'s bindings,
/// collects every `module_ref(path)` node (both the dedicated
/// `Kernel::ModuleRef` variant and the `arr("module_ref", [Const(Str(p))])`
/// form), and builds the import graph transitively via `loader`. Detects
/// cycles via DFS over the import graph. This is a STATIC pass: it only
/// walks Kernel structure and uses the loader to parse referenced modules'
/// source (no interpretation/execution — ADR-0009 §4 "no execution needed").
///
/// Returns `Ok(())` if the import graph is acyclic, or `Err(CycleError)`
/// listing the cycle path (or wrapping a load failure).
pub fn detect_cycles(entry: &DesugaredProgram, loader: &ModuleLoader) -> Result<(), CycleError> {
    // Build the import graph: path -> deduped list of paths it imports.
    let mut graph: HashMap<String, Vec<String>> = HashMap::new();
    let mut worklist: Vec<String> = Vec::new();

    // Seed the worklist from the entry program's module_ref nodes.
    for (_, k) in &entry.bindings {
        for p in collect_module_refs_both(k) {
            if !graph.contains_key(&p) && !worklist.contains(&p) {
                worklist.push(p);
            }
        }
    }

    // Transitively load each referenced module and record its imports.
    while let Some(path) = worklist.pop() {
        if graph.contains_key(&path) {
            continue;
        }
        let loaded = loader.load(&path).map_err(CycleError::Load)?;
        let expanded = loader.expand_reexports(&loaded.graph).map_err(CycleError::Load)?;
        let mut refs: Vec<String> = Vec::new();
        for (_, k) in &expanded.bindings {
            for p in collect_module_refs_both(k) {
                if !refs.contains(&p) {
                    refs.push(p);
                }
            }
        }
        for r in &refs {
            if !graph.contains_key(r) && !worklist.contains(r) {
                worklist.push(r.clone());
            }
        }
        graph.insert(path, refs);
    }

    // DFS cycle detection: track visited nodes and the current recursion
    // stack. A node already on the stack = back edge = cycle.
    let mut visited: Vec<String> = Vec::new();
    let mut stack: Vec<String> = Vec::new();
    let mut nodes: Vec<String> = graph.keys().cloned().collect();
    nodes.sort();
    for node in &nodes {
        if !visited.contains(node) {
            detect_cycles_dfs(node, &graph, &mut visited, &mut stack)?;
        }
    }
    Ok(())
}

/// DFS helper for `detect_cycles`. `visited` holds fully-explored nodes;
/// `stack` holds the current recursion path. A neighbor already on the
/// stack is a back edge → cycle.
fn detect_cycles_dfs(
    node: &str,
    graph: &HashMap<String, Vec<String>>,
    visited: &mut Vec<String>,
    stack: &mut Vec<String>,
) -> Result<(), CycleError> {
    // Already on the recursion stack → back edge → cycle.
    if let Some(start) = stack.iter().position(|n| n == node) {
        let mut cycle: Vec<String> = stack[start..].to_vec();
        cycle.push(node.to_string());
        return Err(CycleError::Cycle(cycle));
    }
    if visited.iter().any(|n| n == node) {
        return Ok(());
    }
    visited.push(node.to_string());
    stack.push(node.to_string());
    if let Some(neighbors) = graph.get(node) {
        for nb in neighbors {
            detect_cycles_dfs(nb, graph, visited, stack)?;
        }
    }
    stack.pop();
    Ok(())
}

// === Section 12: ContractRegistry (ADR-0009 §4 — permissive module ops) ===

/// A registry of op-name → `Contract`, used to give `module_ref`/`project`
/// (and any other op) a permissive contract so static contract inference can
/// proceed over a graph WITHOUT inlining the referenced modules' code
/// (ADR-0009 §4 "Contract inference").
///
/// The ADR's key point: registering `module_ref`/`project` with permissive
/// contracts (input: Any, output: Any) lets `infer_refinement` treat them as
/// KNOWN permissive arrows rather than unknown ones. You lose *precision*
/// (permissive vs. exact inlined contracts), not the *capability* of static
/// analysis. Precision is recoverable by registering tighter contracts loaded
/// from referenced modules' contract caches (see `register`).
pub struct ContractRegistry {
    contracts: HashMap<String, Contract>,
}

impl ContractRegistry {
    /// Create an empty registry.
    pub fn new() -> Self {
        ContractRegistry {
            contracts: HashMap::new(),
        }
    }

    /// Register (or override) the contract for an op. Pre-registering
    /// `module_ref`/`project` with permissive `Any ~> Any` contracts is the
    /// ADR-0009 §4 baseline.
    ///
    /// **Tighter contracts extension point:** to recover precision without
    /// inlining code, load each referenced module's contract (via
    /// `ModuleLoader`'s contract cache) and `register` it under the op name.
    /// `infer_contract_with_registry` will then resolve the op to the tighter
    /// contract. (Translating a tight `Contract`'s refinements into the
    /// refinement engine's structured `Pred`/`RefTy` is a future extension;
    /// today the op is at least KNOWN, so inference proceeds soundly.)
    pub fn register(&mut self, op: &str, contract: Contract) {
        self.contracts.insert(op.to_string(), contract);
    }

    /// Look up the registered contract for an op.
    pub fn get(&self, op: &str) -> Option<&Contract> {
        self.contracts.get(op)
    }

    /// Is an op registered?
    pub fn contains(&self, op: &str) -> bool {
        self.contracts.contains_key(op)
    }

    /// The standard registry the ADR-0009 §4 risk/mitigation and "Contract
    /// inference" section describe: `module_ref` and `project` pre-registered
    /// with the most permissive contract (`Any ~> Any`, no refinements).
    pub fn with_module_ops() -> Self {
        let mut r = Self::new();
        let permissive = Contract {
            signature: "Any ~> Any".to_string(),
            refinements: vec![],
        };
        r.register("module_ref", permissive.clone());
        r.register("project", permissive);
        r
    }
}

/// Translate a registered `Contract` into a permissive `RefSigEntry` for the
/// refinement engine's signature table. The op becomes a KNOWN base arrow
/// (input/output `Any`, guarantee `True`), so `infer_refinement` resolves it
/// instead of erroring with "Unknown base arrow".
///
/// A future extension can parse `contract.signature`/`contract.refinements`
/// into structured `RefTy`/`Pred` to honor tighter contracts; today every
/// registered op is treated as permissive, which is sound (ADR-0009 §4).
fn contract_to_sig_entry(op: &str, _contract: &Contract) -> RefSigEntry {
    RefSigEntry {
        name: op.to_string(),
        input: RefTy::Plain(BaseTy::Var("α".to_string())),
        output: RefTy::Plain(BaseTy::Var("α".to_string())),
        guarantee: Pred::True,
    }
}

/// Like `kernel_to_rgraph` (Section 4) but, when an op is registered in
/// `registry`, translates `module_ref`/`project` nodes (BOTH the dedicated
/// `Kernel::ModuleRef`/`Kernel::Project` variants AND the stringly-typed
/// `Kernel::Arr { op: "module_ref"/"project", .. }` form — ADR-0009 §1, §5)
/// to `RGraph::Arr("<op>")` so the extended signature table resolves them as
/// known permissive arrows. Unregistered ops keep the existing `kernel_to_rgraph`
/// behavior (treated as unknown arrows).
pub fn kernel_to_rgraph_with_registry(k: &Kernel, registry: &ContractRegistry) -> RGraph {
    match k {
        Kernel::ModuleRef { path } => {
            if registry.contains("module_ref") {
                RGraph::Arr("module_ref".to_string())
            } else {
                RGraph::Arr(path.clone())
            }
        }
        Kernel::Project { field, .. } => {
            if registry.contains("project") {
                RGraph::Arr("project".to_string())
            } else {
                RGraph::Arr(field.clone())
            }
        }
        Kernel::Arr { op, .. } => {
            // ADR-0009 §4: module_ref/project are registered ops. Their args
            // are literal paths/fields (not inferable sub-graphs), so when
            // registered, collapse the arr node to the known op arrow.
            if (op == "module_ref" || op == "project") && registry.contains(op) {
                return RGraph::Arr(op.clone());
            }
            kernel_to_rgraph(k)
        }
        _ => kernel_to_rgraph(k),
    }
}

/// Infer a contract for a desugared program, consulting a `ContractRegistry`
/// (ADR-0009 §4). Mirrors `infer_contract` (Section 4) but:
///   - extends `standard_sig()` with a permissive `RefSigEntry` for every
///     registered op, so `infer_refinement` resolves `module_ref`/`project`
///     as known permissive arrows instead of "Unknown base arrow";
///   - uses `kernel_to_rgraph_with_registry` so both encodings of
///     `module_ref`/`project` map to the registered op name.
///
/// `infer_refinement` itself is unmodified (ADR-0009 §4: "infer_refinement
/// works on the whole graph without modification").
pub fn infer_contract_with_registry(
    desugared: &DesugaredProgram,
    registry: &ContractRegistry,
) -> Contract {
    // Build the extended signature table: standard arrows + permissive entries
    // for every registered op (ADR-0009 §4).
    let mut sig = standard_sig();
    for (op, contract) in &registry.contracts {
        if !sig.iter().any(|e| e.name == *op) {
            sig.push(contract_to_sig_entry(op, contract));
        }
    }

    if desugared.bindings.is_empty() {
        return Contract { signature: "Unit ~> Unit".to_string(), refinements: vec![] };
    }

    let mut all_refinements: Vec<String> = Vec::new();
    let mut signatures: Vec<String> = Vec::new();

    for (name, kernel) in &desugared.bindings {
        let rgraph = kernel_to_rgraph_with_registry(kernel, registry);
        match infer_refinement(&rgraph, &sig) {
            Ok(result) => {
                let sig_str = format!("{}: {:?}", name, result.output_type);
                signatures.push(sig_str);

                let guarantee_str = result.guarantee.pretty();
                if guarantee_str != "True" {
                    all_refinements.push(format!("{}: {}", name, guarantee_str));
                }
                for inv in &result.loop_invariants {
                    all_refinements.push(format!("{}: loop invariant: {} ({})",
                        name, inv.invariant.pretty(),
                        if inv.verified_by_smt { "SMT-verified" } else { "unverified" }));
                }
            }
            Err(_) => {
                signatures.push(format!("{}: unknown", name));
            }
        }
    }

    let signature = if signatures.len() == 1 {
        signatures[0].clone()
    } else {
        format!("Record({})", signatures.join(", "))
    };

    Contract {
        signature,
        refinements: all_refinements,
    }
}

// === Section 13: Runtime module-loading handler clauses + governance ===
//                    (ADR-0009 §1 — the ops are the mechanism, §3 — governance
//                     is handler configuration)
//
// This section implements the STANDARD stdlib `module_ref`/`project` handler
// clause logic that ADR-0009's Risk/mitigation calls for: "provide a standard
// `module_ref` clause implementation in the stdlib that handles governance, so
// handler authors don't write it from scratch."
//
// Per ADR-0009 §1, a handler that has operation clauses for `module_ref` and
// `project` interprets them at runtime — loading the file, evaluating it,
// returning the arrow record, extracting the field. A handler WITHOUT these
// clauses either normalises them away first (Strategy A/B) or refuses with
// "unknown op: module_ref" (see `interpret_module_op` / `ModuleHandlerError`).
// "The handler's operation table is the opt-in." (ADR-0009 §1)
//
// Per ADR-0009 §3, governance lives in the `module_ref` clause as handler
// configuration: a path allowlist, a depth limit, runtime cycle detection,
// and resolver wiring (which `ModuleResolver` the `ModuleLoader` is built
// with — `FileResolver` only by default; `NetworkResolver` only if explicitly
// configured). No workspace-level policy file, no program-level directive.
//
// This is a PoC: "evaluate" / "interpret the graph" are simulated at the
// value/kernel level (the codebase has no full Kernel interpreter wired to
// handlers). The functions below operate on the existing `ModuleLoader` /
// `Kernel` / `LoadedModule` machinery to demonstrate the ADR's semantics.

/// Errors raised by the standard `module_ref`/`project` handler clauses
/// (ADR-0009 §1, §3). Each variant references the ADR section it enforces.
#[derive(Debug, Clone)]
pub enum ModuleHandlerError {
    /// ADR-0009 §3 "Path allowlist": `path` is outside `allowed_roots`.
    Denied(String),
    /// ADR-0009 §3 "Cycle detection at runtime": `path` is already on the
    /// active load stack. The vector lists the stack at the point of
    /// detection (the cycle is `stack[..]` + `path`).
    Cycle(Vec<String>),
    /// ADR-0009 §3 "Depth limit": the active load stack depth would exceed
    /// `max_depth`.
    DepthExceeded { path: String, depth: usize, max: usize },
    /// A downstream `ModuleLoader::load` failure (resolve/parse/cycle).
    Load(LoadError),
    /// ADR-0009 §1 `project` clause: the requested `field` was not found in
    /// the materialized module record.
    UnknownField(String),
    /// ADR-0009 §1: the handler's operation table does not include `op` —
    /// "the handler refuses with 'unknown op: module_ref'".
    UnknownOp(String),
}

impl std::fmt::Display for ModuleHandlerError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            ModuleHandlerError::Denied(path) => write!(
                f,
                "module_ref denied: path '{}' outside allowed_roots (ADR-0009 §3)",
                path
            ),
            ModuleHandlerError::Cycle(stack) => {
                write!(
                    f,
                    "runtime import cycle detected: {} (ADR-0009 §3)",
                    stack.join(" -> ")
                )
            }
            ModuleHandlerError::DepthExceeded { path, depth, max } => write!(
                f,
                "module_ref depth limit exceeded for '{}': depth {} >= max {} (ADR-0009 §3)",
                path, depth, max
            ),
            ModuleHandlerError::Load(e) => write!(f, "module load failed: {}", e),
            ModuleHandlerError::UnknownField(field) => write!(
                f,
                "project: unknown field '{}' (ADR-0009 §1)",
                field
            ),
            ModuleHandlerError::UnknownOp(op) => write!(
                f,
                "unknown op: '{}' — handler refuses (ADR-0009 §1)",
                op
            ),
        }
    }
}

// --- (a) Governance config (ADR-0009 §3, item 4) ---------------------------

/// Handler configuration that governs the standard `module_ref` clause
/// (ADR-0009 §3). This is the "handler config — the same place every other
/// capability is governed" the ADR describes.
///
/// Fields:
///   - `allowed_roots`: path allowlist. `is_path_allowed` returns true iff
///     `path` equals or is prefixed by (component-wise) one of the roots.
///     An EMPTY allowlist DENIES ALL paths — the safe default (ADR-0009 §3
///     "No network by default"; a handler that loads nothing is safe).
///   - `max_depth`: maximum depth of the active load stack. A `module_ref`
///     that would push the stack past this depth is refused.
///
/// Resolver wiring (ADR-0009 §3 "No network by default") is expressed by
/// which `ModuleResolver` the `ModuleLoader` is constructed with — that is
/// already handler config via the loader. `FileResolver` only by default;
/// a `NetworkResolver` is wired in only if the handler author explicitly
/// constructs the loader with one. This is NOT duplicated here.
#[derive(Debug, Clone)]
pub struct ModuleHandlerConfig {
    allowed_roots: Vec<String>,
    max_depth: usize,
}

impl ModuleHandlerConfig {
    /// A safe default: EMPTY allowlist (denies all paths) and a conservative
    /// `max_depth` of 8. A handler using the default config loads nothing
    /// until `allowed_roots` is populated — matching ADR-0009 §3 "No network
    /// by default" / deny-by-default governance.
    pub fn default() -> Self {
        ModuleHandlerConfig {
            allowed_roots: Vec::new(),
            max_depth: 8,
        }
    }

    /// Create a config with a given allowlist and depth limit.
    pub fn new(allowed_roots: Vec<String>, max_depth: usize) -> Self {
        ModuleHandlerConfig { allowed_roots, max_depth }
    }

    /// Add a path root to the allowlist (builder-style).
    pub fn allow_root(&mut self, root: &str) -> &mut Self {
        self.allowed_roots.push(root.to_string());
        self
    }

    /// Set the maximum load-stack depth (builder-style).
    pub fn with_max_depth(&mut self, max_depth: usize) -> &mut Self {
        self.max_depth = max_depth;
        self
    }

    /// ADR-0009 §3 "Path allowlist": returns true iff `path` equals, or is
    /// prefixed by (with a `/` boundary), one of `allowed_roots`. This is a
    /// component-wise prefix match so `"collection"` allows
    /// `"collection/sort"` but NOT `"collectionX"`. An empty allowlist
    /// denies all paths.
    pub fn is_path_allowed(&self, path: &str) -> bool {
        for root in &self.allowed_roots {
            if path == root {
                return true;
            }
            if path.starts_with(&format!("{}/", root)) {
                return true;
            }
        }
        false
    }

    /// The configured max load-stack depth.
    pub fn max_depth(&self) -> usize {
        self.max_depth
    }

    /// The configured allowed roots (read access for tests/inspection).
    pub fn allowed_roots(&self) -> &[String] {
        &self.allowed_roots
    }
}

// --- (b) Runtime load stack + cycle detection (ADR-0009 §3) ----------------

/// The active load stack tracked by the `module_ref` clause at runtime
/// (ADR-0009 §3 "Cycle detection at runtime"). The existing `ModuleLoader`
/// does NOT track a runtime stack (its cycle detection is in the
/// normalize/flatten passes), so the handler clause layer adds this. A path
/// already on the stack = cycle → `ModuleHandlerError::Cycle`, not an
/// infinite loop. This is the safety-critical property.
#[derive(Debug, Clone, Default)]
pub struct LoadStack {
    paths: Vec<String>,
}

impl LoadStack {
    pub fn new() -> Self {
        LoadStack { paths: Vec::new() }
    }

    /// Push `path` onto the active load stack.
    pub fn push(&mut self, path: &str) {
        self.paths.push(path.to_string());
    }

    /// Pop the top of the active load stack (no-op if empty).
    pub fn pop(&mut self) {
        self.paths.pop();
    }

    /// Is `path` already on the active load stack? (cycle check)
    pub fn contains(&self, path: &str) -> bool {
        self.paths.iter().any(|p| p == path)
    }

    /// Current depth of the active load stack.
    pub fn len(&self) -> usize {
        self.paths.len()
    }

    /// A snapshot of the active load stack (for error reporting).
    pub fn snapshot(&self) -> Vec<String> {
        self.paths.clone()
    }
}

// --- (c) The standard `module_ref` clause (ADR-0009 §1, item 1) ------------

/// The standard stdlib `module_ref` clause implementation (ADR-0009 §1 +
/// Risk/mitigation). Implements the governance the ADR requires so handler
/// authors don't write it from scratch:
///
///   1. ADR-0009 §3 "Path allowlist": check `config.is_path_allowed(path)`.
///   2. ADR-0009 §3 "Cycle detection at runtime": if `path` is already on
///      `stack`, return `Cycle` (NOT an infinite loop).
///   3. ADR-0009 §3 "Depth limit": if `stack.len() >= config.max_depth`,
///      return `DepthExceeded`.
///   4. Push `path`, `loader.load(path)`, build the record of public arrows
///      from the loaded module's public bindings via `build_module_record`,
///      pop `path`, return the record `Kernel`.
///   5. On `loader.load` error, pop and propagate as `Load`.
///
/// The returned `Kernel` is `arr("module_record", [arr("record", [...])])`
/// (see `build_module_record`, Section 7) — the "record of public arrows"
/// the ADR's `module_ref` clause returns.
pub fn handle_module_ref(
    path: &str,
    loader: &ModuleLoader,
    config: &ModuleHandlerConfig,
    stack: &mut LoadStack,
) -> Result<Kernel, ModuleHandlerError> {
    // (1) Path allowlist (ADR-0009 §3).
    if !config.is_path_allowed(path) {
        return Err(ModuleHandlerError::Denied(path.to_string()));
    }
    // (2) Runtime cycle detection (ADR-0009 §3).
    if stack.contains(path) {
        let mut snap = stack.snapshot();
        snap.push(path.to_string());
        return Err(ModuleHandlerError::Cycle(snap));
    }
    // (3) Depth limit (ADR-0009 §3).
    if stack.len() >= config.max_depth() {
        return Err(ModuleHandlerError::DepthExceeded {
            path: path.to_string(),
            depth: stack.len(),
            max: config.max_depth(),
        });
    }
    // (4) Load + build the record of public arrows. Push/pop around the
    // load so the runtime stack reflects the active load (and so a
    // transitive cycle is detected at step 2 of the recursive call).
    stack.push(path);
    let result = loader.load(path).map_err(|e| {
        // (5) On load error, pop before propagating.
        stack.pop();
        ModuleHandlerError::Load(e)
    });
    let loaded = match result {
        Ok(l) => l,
        Err(e) => return Err(e),
    };
    // Expand reexports so the public bindings are complete, then collect the
    // public (name, kernel) pairs and build the module record.
    let pub_binds = match loader.expand_reexports(&loaded.graph) {
        Ok(expanded) => public_bindings_from(&expanded),
        Err(e) => {
            stack.pop();
            return Err(ModuleHandlerError::Load(e));
        }
    };
    stack.pop();
    Ok(build_module_record(&pub_binds))
}

// --- (d) The standard `project` clause (ADR-0009 §1, item 1) ---------------

/// The standard stdlib `project` clause implementation (ADR-0009 §1).
/// Extracts `field` from `record`. The record is expected to be the
/// `arr("module_record", [arr("record", [...arr("field",
/// [Const(Str(name)), kernel])...])])` produced by `handle_module_ref` /
/// `build_module_record`. Walks the record kernel to find the field with a
/// matching name and returns its kernel.
///
/// If `record` is an UNMATERIALIZED `module_ref` (dedicated `Kernel::ModuleRef`
/// variant or the `arr("module_ref", [Const(Str(p))])` form — ADR-0009 §1, §5),
/// it is loaded first via `handle_module_ref` (using the same governance) and
/// then the field is projected from the materialized record. This mirrors the
/// ADR's semantics: `project(module_ref(path), field)`.
///
/// If the field is not found → `UnknownField`.
pub fn handle_project(
    record: &Kernel,
    field: &str,
    loader: &ModuleLoader,
    config: &ModuleHandlerConfig,
    stack: &mut LoadStack,
) -> Result<Kernel, ModuleHandlerError> {
    // If the record is an unmateralized module_ref, load it first.
    let materialized = match record {
        Kernel::ModuleRef { path } => {
            handle_module_ref(path, loader, config, stack)?
        }
        Kernel::Arr { op, args } if op == "module_ref" && args.len() == 1 => {
            if let Kernel::Const(Lit::Str(path)) = &args[0] {
                handle_module_ref(path, loader, config, stack)?
            } else {
                // Malformed module_ref arr; treat the record as-is.
                record.clone()
            }
        }
        other => other.clone(),
    };
    // Look up the field in the (now materialized) module record.
    match lookup_field_in_record(&materialized, field) {
        Some(k) => Ok(k),
        None => Err(ModuleHandlerError::UnknownField(field.to_string())),
    }
}

// --- (e) Combined op-table dispatch (ADR-0009 §1 "operation table") ---------

/// The handler's operation table dispatch (ADR-0009 §1: "the handler's
/// operation table is the opt-in"). A handler WITH this dispatch handles
/// module ops (runtime loading); a handler WITHOUT it refuses (see
/// `ModuleHandlerError::UnknownOp`).
///
/// Dispatches on `op`:
///   - `"module_ref"`: `args[0]` is `Const(Lit::Str(path))` → `handle_module_ref`.
///   - `"project"`: `args[0]` is the record kernel, `args[1]` is
///     `Const(Lit::Str(field))` → `handle_project`.
///   - any other `op` → `UnknownOp(op)` ("handler refuses with 'unknown op'").
///
/// This handles the stringly-typed `arr("module_ref", ...)` /
/// `arr("project", ...)` form (ADR-0009 §1, §5). For the DEDICATED
/// `Kernel::ModuleRef` / `Kernel::Project` variants, use
/// `interpret_module_kernel` (below), which converts them to the op-dispatch
/// form first.
pub fn interpret_module_op(
    op: &str,
    args: &[Kernel],
    loader: &ModuleLoader,
    config: &ModuleHandlerConfig,
    stack: &mut LoadStack,
) -> Result<Kernel, ModuleHandlerError> {
    match op {
        "module_ref" => {
            let path = match args.get(0) {
                Some(Kernel::Const(Lit::Str(p))) => p.clone(),
                _ => return Err(ModuleHandlerError::UnknownOp(
                    "module_ref (malformed args)".to_string(),
                )),
            };
            handle_module_ref(&path, loader, config, stack)
        }
        "project" => {
            if args.len() < 2 {
                return Err(ModuleHandlerError::UnknownOp(
                    "project (malformed args)".to_string(),
                ));
            }
            let record = &args[0];
            let field = match &args[1] {
                Kernel::Const(Lit::Str(f)) => f.clone(),
                _ => return Err(ModuleHandlerError::UnknownOp(
                    "project (malformed field)".to_string(),
                )),
            };
            handle_project(record, &field, loader, config, stack)
        }
        other => Err(ModuleHandlerError::UnknownOp(other.to_string())),
    }
}

/// Dispatch a `Kernel` node that may be a dedicated `Kernel::ModuleRef` /
/// `Kernel::Project` variant OR the stringly-typed `arr(...)` form
/// (ADR-0009 §1, §5) through the handler's operation table. This is the
/// single entry point that handles BOTH encodings, so a handler author can
/// feed any module-op kernel node to one function.
///
/// - `Kernel::ModuleRef { path }` → op `"module_ref"` with `[Const(Str(path))]`.
/// - `Kernel::Project { field, record }` → op `"project"` with
///   `[record, Const(Str(field))]`.
/// - `Kernel::Arr { op: "module_ref"/"project", .. }` → forwarded to
///   `interpret_module_op` directly.
/// - any other kernel → `UnknownOp("<non-module kernel>")` (a handler that
///   only has module-op clauses does not interpret other kernels).
pub fn interpret_module_kernel(
    k: &Kernel,
    loader: &ModuleLoader,
    config: &ModuleHandlerConfig,
    stack: &mut LoadStack,
) -> Result<Kernel, ModuleHandlerError> {
    match k {
        Kernel::ModuleRef { path } => interpret_module_op(
            "module_ref",
            &[Kernel::Const(Lit::Str(path.clone()))],
            loader,
            config,
            stack,
        ),
        Kernel::Project { field, record } => interpret_module_op(
            "project",
            &[record.as_ref().clone(), Kernel::Const(Lit::Str(field.clone()))],
            loader,
            config,
            stack,
        ),
        Kernel::Arr { op, args } if op == "module_ref" || op == "project" => {
            interpret_module_op(op, args, loader, config, stack)
        }
        other => Err(ModuleHandlerError::UnknownOp(format!(
            "<non-module kernel: {:?}>",
            other
        ))),
    }
}

// === Section 14: fn main() — test suite (PoC style) ===

fn check(label: &str, ok: bool) {
    if ok {
        println!("  PASS  {}", label);
    } else {
        println!("  FAIL  {}", label);
        std::process::exit(1);
    }
}

fn build_test_memory_resolver() -> MemoryResolver {
    let mut m = MemoryResolver::new();
    // collection/insert — a single binding (a loop arrow).
    m.insert(
        "collection/insert",
        "insert = rec { compare >>> (cons ||| cons) }",
    );
    // collection/sort — imports insert, defines sort.
    m.insert(
        "collection/sort",
        "import insert from \"collection/insert\"\nsort = rec { insert >>> id }",
    );
    // collection — multi-name file (record arrow).
    m.insert(
        "collection",
        "cons = compare\nhead = id\nsort = rec { compare >>> id }",
    );
    // main — imports sort, uses it.
    m.insert(
        "main",
        "import sort from \"collection/sort\"\nmain = sort([3, 1, 2])",
    );
    // reexport — export * from "collection".
    m.insert("reexport", "export * from \"collection\"");
    // cycle modules.
    m.insert("cycle_a", "import b from \"cycle_b\"\nx = b");
    m.insert("cycle_b", "import a from \"cycle_a\"\ny = a");
    m
}

fn main() {
    println!("handl v0.1 — Module System Tests (ADR-0069 §4–§5)");
    println!("==================================================\n");

    // --- Section 1: Resolvers ---
    println!("Section 1: Resolvers");
    {
        let mem = build_test_memory_resolver();

        // MemoryResolver: Ok with correct source.
        let r = mem.resolve("collection/sort");
        match r {
            Ok(m) => {
                check(
                    "MemoryResolver resolves collection/sort",
                    m.source.contains("import insert"),
                );
                check(
                    "MemoryResolver origin is 'memory'",
                    mem.origin() == "memory",
                );
            }
            Err(_) => check("MemoryResolver resolves collection/sort", false),
        }

        // MemoryResolver: NotFound for missing.
        match mem.resolve("missing") {
            Ok(_) => check("MemoryResolver NotFound for missing", false),
            Err(e) => check(
                "MemoryResolver NotFound for missing",
                matches!(e.kind, ResolveErrorKind::NotFound),
            ),
        }

        // ChainResolver: memory + FileResolver (temp dir).
        let mut chain_resolvers: Vec<Box<dyn ModuleResolver>> = Vec::new();
        let mut mem2 = MemoryResolver::new();
        mem2.insert("collection/sort", "sort = id");
        chain_resolvers.push(Box::new(mem2));
        chain_resolvers.push(Box::new(FileResolver::new(PathBuf::from("/tmp/handl_test_nonexistent"))));
        let chain = ChainResolver::new(chain_resolvers);

        match chain.resolve("collection/sort") {
            Ok(m) => check(
                "ChainResolver finds memory module",
                m.source == "sort = id",
            ),
            Err(_) => check("ChainResolver finds memory module", false),
        }
        match chain.resolve("totally/missing") {
            Ok(_) => check("ChainResolver NotFound for missing", false),
            Err(e) => check(
                "ChainResolver NotFound for missing",
                matches!(e.kind, ResolveErrorKind::NotFound),
            ),
        }
        check("ChainResolver origin is 'chain'", chain.origin() == "chain");

        // CachingResolver: returns Ok twice (cache hit on second).
        let mut mem3 = MemoryResolver::new();
        mem3.insert("collection/sort", "sort = id");
        let cache = CachingResolver::new(Box::new(mem3));
        let r1 = cache.resolve("collection/sort");
        let r2 = cache.resolve("collection/sort");
        check(
            "CachingResolver returns Ok twice",
            r1.is_ok() && r2.is_ok(),
        );
        check(
            "CachingResolver returns same content",
            r1.unwrap().source == r2.unwrap().source,
        );
    }

    // --- Section 2: ModuleLoader (Strategy C — two caches) ---
    println!("\nSection 2: ModuleLoader (Strategy C — two caches)");
    {
        let mem = build_test_memory_resolver();
        let (counting, counter) = CountingResolver::new_with_counter(Box::new(mem));
        let loader = ModuleLoader::new(Box::new(counting));

        // load("collection/sort") -> Ok; verify bindings contain "insert" as
        // a Project from ModuleRef.
        match loader.load("collection/sort") {
            Ok(loaded) => {
                let insert_binding = loaded
                    .graph
                    .bindings
                    .iter()
                    .find(|(n, _)| n == "insert");
                match insert_binding {
                    Some((_, k)) => {
                        check(
                            "load(collection/sort) has insert as Project from ModuleRef",
                            matches!(
                                k,
                                Kernel::Project { field, record }
                                    if field == "insert"
                                        && matches!(record.as_ref(), Kernel::ModuleRef { path } if path == "collection/insert")
                            ),
                        );
                    }
                    None => check("load(collection/sort) has insert binding", false),
                }
            }
            Err(e) => {
                check("load(collection/sort) succeeds", false);
                eprintln!("  error: {}", e);
            }
        }

        // Cache hit: loading the same path twice calls resolve only once.
        // We already loaded "collection/sort" once above. Load again.
        let count_before = counter.get();
        let _ = loader.load("collection/sort");
        let count_after = counter.get();
        check(
            "cache hit: second load does not call resolve",
            count_before == count_after,
        );

        // public_names("collection") -> ["cons", "head", "sort"] (All).
        match loader.public_names("collection") {
            Ok(names) => {
                check(
                    "public_names(collection) = [cons, head, sort]",
                    names.len() == 3
                        && names.contains(&"cons".to_string())
                        && names.contains(&"head".to_string())
                        && names.contains(&"sort".to_string()),
                );
            }
            Err(_) => check("public_names(collection) succeeds", false),
        }

        // public_names("collection/sort") -> ["insert", "sort"] (All, includes
        // the import-projected binding "insert").
        match loader.public_names("collection/sort") {
            Ok(names) => {
                check(
                    "public_names(collection/sort) = [insert, sort]",
                    names.len() == 2
                        && names.contains(&"insert".to_string())
                        && names.contains(&"sort".to_string()),
                );
            }
            Err(_) => check("public_names(collection/sort) succeeds", false),
        }

        // public_names("main") -> ["sort", "main"] (All, includes import).
        match loader.public_names("main") {
            Ok(names) => {
                check(
                    "public_names(main) = [sort, main]",
                    names.len() == 2
                        && names.contains(&"sort".to_string())
                        && names.contains(&"main".to_string()),
                );
            }
            Err(_) => check("public_names(main) succeeds", false),
        }
    }

    // --- Section 3: expand_reexports ---
    println!("\nSection 3: expand_reexports");
    {
        let mem = build_test_memory_resolver();
        let loader = ModuleLoader::new(Box::new(mem));

        match loader.load("reexport") {
            Ok(loaded) => {
                // Before expansion: export_set = Names([]), reexports = ["collection"].
                check(
                    "reexport before expansion: Names([])",
                    matches!(&loaded.graph.export_set, ExportSet::Names(ns) if ns.is_empty()),
                );
                check(
                    "reexport before expansion: reexports = [collection]",
                    loaded.graph.reexports == vec!["collection".to_string()],
                );

                match loader.expand_reexports(&loaded.graph) {
                    Ok(expanded) => {
                        // Should have bindings for cons, head, sort (each a
                        // Project from "collection").
                        let has_cons = expanded.bindings.iter().any(|(n, k)| {
                            n == "cons"
                                && matches!(
                                    k,
                                    Kernel::Project { field, record }
                                        if field == "cons"
                                            && matches!(record.as_ref(), Kernel::ModuleRef { path } if path == "collection")
                                )
                        });
                        let has_head = expanded.bindings.iter().any(|(n, k)| {
                            n == "head"
                                && matches!(
                                    k,
                                    Kernel::Project { field, record }
                                        if field == "head"
                                            && matches!(record.as_ref(), Kernel::ModuleRef { path } if path == "collection")
                                )
                        });
                        let has_sort = expanded.bindings.iter().any(|(n, k)| {
                            n == "sort"
                                && matches!(
                                    k,
                                    Kernel::Project { field, record }
                                        if field == "sort"
                                            && matches!(record.as_ref(), Kernel::ModuleRef { path } if path == "collection")
                                )
                        });
                        check("expand_reexports adds cons binding", has_cons);
                        check("expand_reexports adds head binding", has_head);
                        check("expand_reexports adds sort binding", has_sort);

                        // export_set should be Names(["cons","head","sort"]).
                        match &expanded.export_set {
                            ExportSet::Names(ns) => {
                                check(
                                    "expand_reexports export_set = Names([cons,head,sort])",
                                    ns.len() == 3
                                        && ns.contains(&"cons".to_string())
                                        && ns.contains(&"head".to_string())
                                        && ns.contains(&"sort".to_string()),
                                );
                            }
                            _ => check("expand_reexports export_set is Names", false),
                        }
                        // reexports cleared.
                        check(
                            "expand_reexports clears reexports",
                            expanded.reexports.is_empty(),
                        );
                    }
                    Err(e) => {
                        check("expand_reexports succeeds", false);
                        eprintln!("  error: {}", e);
                    }
                }
            }
            Err(e) => {
                check("load(reexport) succeeds", false);
                eprintln!("  error: {}", e);
            }
        }
    }

    // --- Section 4: Strategy A — normalize_compile_time ---
    println!("\nSection 4: Strategy A — normalize_compile_time");
    {
        let mem = build_test_memory_resolver();
        let loader = ModuleLoader::new(Box::new(mem));

        match normalize_compile_time("main", &loader) {
            Ok(normalized) => {
                // No ModuleRef anywhere.
                let any_ref = normalized
                    .bindings
                    .iter()
                    .any(|(_, k)| contains_module_ref(k));
                check("Strategy A: no ModuleRef remains", !any_ref);

                // Project nodes DO remain (Strategy A keeps projections).
                let any_project = normalized
                    .bindings
                    .iter()
                    .any(|(_, k)| contains_project(k));
                check("Strategy A: Project nodes remain", any_project);

                // The "sort" binding's Project now has a record that is an
                // inlined arr("module_record", ...) rather than a ModuleRef.
                let sort_binding = normalized.bindings.iter().find(|(n, _)| n == "sort");
                match sort_binding {
                    Some((_, k)) => {
                        let is_inlined = match k {
                            Kernel::Project { record, .. } => {
                                matches!(
                                    record.as_ref(),
                                    Kernel::Arr { op, .. } if op == "module_record"
                                )
                            }
                            _ => false,
                        };
                        check(
                            "Strategy A: sort binding Project has inlined module_record",
                            is_inlined,
                        );
                    }
                    None => check("Strategy A: sort binding exists", false),
                }

                // Print the normalized bindings for visibility.
                println!("  Normalized main bindings:");
                for (name, k) in &normalized.bindings {
                    println!("    {} = {:?}", name, k);
                }
            }
            Err(e) => {
                check("normalize_compile_time(main) succeeds", false);
                eprintln!("  error: {}", e);
            }
        }
    }

    // --- Section 5: Strategy B — flatten_program ---
    println!("\nSection 5: Strategy B — flatten_program");
    {
        let mem = build_test_memory_resolver();
        let loader = ModuleLoader::new(Box::new(mem));

        match flatten_program("main", &loader) {
            Ok(flat) => {
                check("Strategy B: no ModuleRef", !contains_module_ref(&flat));
                check("Strategy B: no Project", !contains_project(&flat));

                // Print the flattened kernel.
                println!("  Flattened main kernel:");
                println!("    {:?}", flat);
            }
            Err(e) => {
                check("flatten_program(main) succeeds", false);
                eprintln!("  error: {}", e);
            }
        }
    }

    // --- Section 6: Cycle detection ---
    println!("\nSection 6: Cycle detection");
    {
        let mem = build_test_memory_resolver();
        let loader = ModuleLoader::new(Box::new(mem));

        match normalize_compile_time("cycle_a", &loader) {
            Ok(_) => check("cycle_a normalization returns Cycle error", false),
            Err(e) => {
                check(
                    "cycle_a normalization returns Cycle error",
                    matches!(e, LoadError::Cycle(_)),
                );
                println!("  Cycle error: {}", e);
            }
        }

        // Also test cycle detection in flatten_program.
        let mem2 = build_test_memory_resolver();
        let loader2 = ModuleLoader::new(Box::new(mem2));
        match flatten_program("cycle_a", &loader2) {
            Ok(_) => check("cycle_a flatten returns Cycle error", false),
            Err(e) => {
                check(
                    "cycle_a flatten returns Cycle error",
                    matches!(e, LoadError::Cycle(_)),
                );
            }
        }
    }

    // --- Section 7: Capability boundary (ADR-0046) ---
    println!("\nSection 7: Capability boundary (ADR-0046)");
    {
        // A ChainResolver with ONLY a MemoryResolver (no file resolver).
        // Paths in memory succeed; paths needing a file resolver return
        // NotFound. This models a host denying the file capability.
        let mut mem = MemoryResolver::new();
        mem.insert("allowed", "x = id");
        let chain = ChainResolver::new(vec![Box::new(mem)]);

        match chain.resolve("allowed") {
            Ok(_) => check("capability: allowed path resolves", true),
            Err(_) => check("capability: allowed path resolves", false),
        }
        match chain.resolve("needs/file") {
            Ok(_) => check("capability: denied path returns NotFound", false),
            Err(e) => check(
                "capability: denied path returns NotFound",
                matches!(e.kind, ResolveErrorKind::NotFound),
            ),
        }
        println!("  Note: resolver set = [MemoryResolver only]; file capability denied.");
    }

    // --- Section 8: Static cycle detection (ADR-0009 §4) ---
    println!("\nSection 8: Static cycle detection (ADR-0009 §4)");
    {
        // Reuse the existing test memory resolver (has cycle_a/cycle_b) and
        // extend it with acyclic, self-cycle, and diamond fixtures.
        let mut mem = build_test_memory_resolver();
        mem.insert("acyclic_a", "import b from \"acyclic_b\"\nx = b");
        mem.insert("acyclic_b", "import c from \"acyclic_c\"\ny = c");
        mem.insert("acyclic_c", "z = id");
        mem.insert("self_a", "import a from \"self_a\"\nw = a");
        mem.insert("dia", "import b from \"dia_b\"\nimport c from \"dia_c\"\nmain = b");
        mem.insert("dia_b", "import d from \"dia_d\"\nb = d");
        mem.insert("dia_c", "import d from \"dia_d\"\nc = d");
        mem.insert("dia_d", "d = id");
        let loader = ModuleLoader::new(Box::new(mem));

        // Helper to build an entry program with a single module_ref binding
        // (dedicated Kernel::ModuleRef variant).
        let entry_dedicated = |path: &str| DesugaredProgram {
            bindings: vec![(
                "main".to_string(),
                Kernel::ModuleRef { path: path.to_string() },
            )],
            export_set: ExportSet::All,
            reexports: Vec::new(),
        };
        // Helper to build an entry program using the stringly-typed arr form
        // arr("module_ref", [Const(Str(path))]) (ADR-0009 §1, §5).
        let entry_arr_form = |path: &str| DesugaredProgram {
            bindings: vec![(
                "main".to_string(),
                Kernel::Arr {
                    op: "module_ref".to_string(),
                    args: vec![Kernel::Const(Lit::Str(path.to_string()))],
                },
            )],
            export_set: ExportSet::All,
            reexports: Vec::new(),
        };

        // Acyclic chain: acyclic_a -> acyclic_b -> acyclic_c (no cycle).
        match detect_cycles(&entry_dedicated("acyclic_a"), &loader) {
            Ok(()) => check("acyclic chain (a -> b -> c) -> Ok", true),
            Err(e) => {
                check("acyclic chain (a -> b -> c) -> Ok", false);
                eprintln!("  error: {}", e);
            }
        }

        // Cyclic graph: cycle_a -> cycle_b -> cycle_a (reuse existing fixtures).
        match detect_cycles(&entry_dedicated("cycle_a"), &loader) {
            Ok(()) => check("cycle (cycle_a <-> cycle_b) -> Err", false),
            Err(CycleError::Cycle(c)) => {
                check(
                    "cycle (cycle_a <-> cycle_b) -> Err with cycle path",
                    c.contains(&"cycle_a".to_string())
                        && c.contains(&"cycle_b".to_string()),
                );
                println!("  Cycle: {}", c.join(" -> "));
            }
            Err(e) => {
                check("cycle (cycle_a <-> cycle_b) -> Err with cycle path", false);
                eprintln!("  error: {}", e);
            }
        }

        // Self-cycle: self_a imports self_a.
        match detect_cycles(&entry_dedicated("self_a"), &loader) {
            Ok(()) => check("self-cycle (self_a -> self_a) -> Err", false),
            Err(CycleError::Cycle(c)) => check(
                "self-cycle (self_a -> self_a) -> Err",
                c.len() >= 2 && c[0] == "self_a" && c[1] == "self_a",
            ),
            Err(e) => {
                check("self-cycle (self_a -> self_a) -> Err", false);
                eprintln!("  error: {}", e);
            }
        }

        // Diamond: dia -> {dia_b, dia_c} -> dia_d (not a cycle).
        match detect_cycles(&entry_dedicated("dia"), &loader) {
            Ok(()) => check("diamond (dia -> b,c -> d) -> Ok", true),
            Err(e) => {
                check("diamond (dia -> b,c -> d) -> Ok", false);
                eprintln!("  error: {}", e);
            }
        }

        // arr-form encoding: arr("module_ref", [Const(Str("cycle_a"))]) must
        // also be recognized (ADR-0009 §1, §5) and detect the cycle.
        match detect_cycles(&entry_arr_form("cycle_a"), &loader) {
            Ok(()) => check("arr-form module_ref cycle detection -> Err", false),
            Err(CycleError::Cycle(c)) => {
                check(
                    "arr-form module_ref cycle detection -> Err with cycle",
                    c.contains(&"cycle_a".to_string()),
                );
                println!("  Cycle (arr-form): {}", c.join(" -> "));
            }
            Err(e) => {
                check("arr-form module_ref cycle detection -> Err with cycle", false);
                eprintln!("  error: {}", e);
            }
        }

        // arr-form acyclic: arr("module_ref", [Const(Str("acyclic_a"))]) -> Ok.
        match detect_cycles(&entry_arr_form("acyclic_a"), &loader) {
            Ok(()) => check("arr-form module_ref acyclic -> Ok", true),
            Err(e) => {
                check("arr-form module_ref acyclic -> Ok", false);
                eprintln!("  error: {}", e);
            }
        }

        // Load failure: a module_ref to a missing path propagates as
        // CycleError::Load (wrapped LoadError).
        match detect_cycles(&entry_dedicated("does/not/exist"), &loader) {
            Ok(()) => check("missing module ref -> Load error", false),
            Err(CycleError::Load(_)) => check("missing module ref -> Load error", true),
            Err(e) => {
                check("missing module ref -> Load error", false);
                eprintln!("  error: {}", e);
            }
        }
    }

    // --- Section 9: ContractRegistry (ADR-0009 §4) ---
    println!("\nSection 9: ContractRegistry (ADR-0009 §4)");
    {
        // with_module_ops() pre-registers permissive contracts for module_ref
        // and project (input: Any, output: Any — ADR-0009 §4).
        let reg = ContractRegistry::with_module_ops();
        check(
            "with_module_ops registers module_ref and project",
            reg.contains("module_ref") && reg.contains("project"),
        );
        let mr = reg.get("module_ref").unwrap();
        check(
            "module_ref contract is permissive Any ~> Any",
            mr.signature == "Any ~> Any" && mr.refinements.is_empty(),
        );
        let pr = reg.get("project").unwrap();
        check(
            "project contract is permissive Any ~> Any",
            pr.signature == "Any ~> Any" && pr.refinements.is_empty(),
        );
        // An empty registry contains neither op.
        let empty = ContractRegistry::new();
        check(
            "empty registry contains neither op",
            !empty.contains("module_ref") && !empty.contains("project"),
        );

        // A small program mirroring how desugar emits imports: a binding whose
        // kernel is Project { field, record: ModuleRef { path } }. The field
        // name ("myfunc") and path ("mymod") are NOT in standard_sig, so
        // without the registry they are treated as unknown arrows.
        let prog_project = DesugaredProgram {
            bindings: vec![(
                "main".to_string(),
                Kernel::Project {
                    field: "myfunc".to_string(),
                    record: Box::new(Kernel::ModuleRef {
                        path: "mymod".to_string(),
                    }),
                },
            )],
            export_set: ExportSet::All,
            reexports: Vec::new(),
        };

        // Without the registry: plain infer_contract treats the project field
        // as an unknown base arrow → binding marked "unknown".
        let plain_contract = infer_contract(&prog_project);
        check(
            "without registry: project op inferred as unknown",
            plain_contract.signature.contains("unknown"),
        );

        // With the registry: the permissive contract lets inference proceed —
        // the binding gets a real (permissive) type, NOT "unknown".
        let reg_contract = infer_contract_with_registry(&prog_project, &reg);
        check(
            "with registry: project op inferred (not unknown)",
            !reg_contract.signature.contains("unknown"),
        );
        println!("  registry contract signature: {}", reg_contract.signature);

        // Same contrast for a bare ModuleRef binding (dedicated variant).
        let prog_ref = DesugaredProgram {
            bindings: vec![(
                "main".to_string(),
                Kernel::ModuleRef {
                    path: "mymod".to_string(),
                },
            )],
            export_set: ExportSet::All,
            reexports: Vec::new(),
        };
        let plain_ref = infer_contract(&prog_ref);
        check(
            "without registry: module_ref op inferred as unknown",
            plain_ref.signature.contains("unknown"),
        );
        let reg_ref = infer_contract_with_registry(&prog_ref, &reg);
        check(
            "with registry: module_ref op inferred (not unknown)",
            !reg_ref.signature.contains("unknown"),
        );

        // The stringly-typed arr form (ADR-0009 §1, §5) is also recognized.
        // arr("module_ref", [Const(Str("mymod"))]) — without the registry the
        // Const arg becomes an unknown "const" arrow; with the registry the
        // node collapses to the known "module_ref" op arrow.
        let prog_arr = DesugaredProgram {
            bindings: vec![(
                "main".to_string(),
                Kernel::Arr {
                    op: "module_ref".to_string(),
                    args: vec![Kernel::Const(Lit::Str("mymod".to_string()))],
                },
            )],
            export_set: ExportSet::All,
            reexports: Vec::new(),
        };
        let plain_arr = infer_contract(&prog_arr);
        check(
            "without registry: arr-form module_ref inferred as unknown",
            plain_arr.signature.contains("unknown"),
        );
        let reg_arr = infer_contract_with_registry(&prog_arr, &reg);
        check(
            "with registry: arr-form module_ref inferred (not unknown)",
            !reg_arr.signature.contains("unknown"),
        );

        // Registering a tighter contract for an op OVERRIDES the permissive one
        // (ADR-0009 §4 "tighter contracts" extension point).
        let mut reg2 = ContractRegistry::with_module_ops();
        let tighter = Contract {
            signature: "List α ~> { x : α | Sorted(x) }".to_string(),
            refinements: vec!["Sorted(output)".to_string()],
        };
        reg2.register("module_ref", tighter.clone());
        let overridden = reg2.get("module_ref").unwrap();
        check(
            "tighter contract overrides permissive module_ref",
            overridden.signature == tighter.signature
                && overridden.refinements.len() == 1,
        );
        // project stays permissive (only module_ref was overridden).
        check(
            "project stays permissive after module_ref override",
            reg2.get("project").unwrap().signature == "Any ~> Any",
        );
    }

    // --- Section 10: Runtime module-loading handler clauses + governance
    //                  (ADR-0009 §1, §3) ---
    println!("\nSection 10: Runtime module-loading handler clauses + governance (ADR-0009 §1, §3)");
    {
        // A config that allows the "collection" root (covers
        // "collection/sort", "collection/insert", "collection") and the
        // cycle fixtures, with a generous depth limit.
        let make_config = || {
            let mut c = ModuleHandlerConfig::default();
            c.allow_root("collection").with_max_depth(16);
            c.allow_root("cycle_a");
            c.allow_root("cycle_b");
            c
        };

        // (1) handle_module_ref on an allowed path returns a record kernel
        // with the module's public bindings (arr("module_record", ...)).
        {
            let mem = build_test_memory_resolver();
            let loader = ModuleLoader::new(Box::new(mem));
            let config = make_config();
            let mut stack = LoadStack::new();
            match handle_module_ref("collection/sort", &loader, &config, &mut stack) {
                Ok(k) => {
                    let is_record = matches!(
                        &k,
                        Kernel::Arr { op, .. } if op == "module_record"
                    );
                    check(
                        "handle_module_ref(collection/sort) returns arr(module_record, ...)",
                        is_record,
                    );
                    // The record should contain the "sort" field (a public
                    // binding of collection/sort).
                    let has_sort = lookup_field_in_record(&k, "sort").is_some();
                    check(
                        "handle_module_ref record contains 'sort' field",
                        has_sort,
                    );
                    // Stack is balanced after a successful load.
                    check(
                        "load stack balanced after successful module_ref",
                        stack.len() == 0,
                    );
                }
                Err(e) => {
                    check("handle_module_ref(collection/sort) succeeds", false);
                    eprintln!("  error: {}", e);
                }
            }
        }

        // (2) Path outside the allowlist -> Denied.
        {
            let mem = build_test_memory_resolver();
            let loader = ModuleLoader::new(Box::new(mem));
            let config = make_config();
            let mut stack = LoadStack::new();
            match handle_module_ref("main", &loader, &config, &mut stack) {
                Ok(_) => check("path outside allowlist -> Denied", false),
                Err(ModuleHandlerError::Denied(p)) => check(
                    "path outside allowlist -> Denied",
                    p == "main",
                ),
                Err(e) => {
                    check("path outside allowlist -> Denied", false);
                    eprintln!("  error: {}", e);
                }
            }
        }

        // (3) Depth exceeded (set max_depth low) -> DepthExceeded.
        {
            let mem = build_test_memory_resolver();
            let loader = ModuleLoader::new(Box::new(mem));
            let mut config = make_config();
            config.with_max_depth(0); // any load exceeds depth 0
            let mut stack = LoadStack::new();
            match handle_module_ref("collection/sort", &loader, &config, &mut stack) {
                Ok(_) => check("max_depth=0 -> DepthExceeded", false),
                Err(ModuleHandlerError::DepthExceeded { path, depth, max }) => check(
                    "max_depth=0 -> DepthExceeded",
                    path == "collection/sort" && depth == 0 && max == 0,
                ),
                Err(e) => {
                    check("max_depth=0 -> DepthExceeded", false);
                    eprintln!("  error: {}", e);
                }
            }
        }

        // (4) Runtime cycle (cycle_a -> cycle_b -> cycle_a) -> Cycle, NOT an
        //     infinite loop. This is the safety-critical property.
        //
        // In a real interpreter, the `module_ref` clause evaluates the
        // module's bindings WHILE the module is on the load stack (between
        // push and pop). A binding that does `module_ref("cycle_a")` while
        // cycle_a is already on the stack triggers the cycle check. We
        // simulate that here: push cycle_a (evaluating its bindings), push
        // cycle_b (evaluating the binding cycle_a imports from cycle_b),
        // then try to load cycle_a again — it's on the stack -> Cycle.
        {
            let mem = build_test_memory_resolver();
            let loader = ModuleLoader::new(Box::new(mem));
            let config = make_config();
            let mut stack = LoadStack::new();

            // (a) Load cycle_a normally (verifies it loads and the stack
            // balances after).
            let record_a = handle_module_ref("cycle_a", &loader, &config, &mut stack);
            check("handle_module_ref(cycle_a) succeeds", record_a.is_ok());
            check(
                "stack balanced after successful cycle_a load",
                stack.len() == 0,
            );
            // cycle_a's record has a "b" field (the import from cycle_b).
            let rec_a = record_a.unwrap();
            check(
                "cycle_a record has 'b' field",
                lookup_field_in_record(&rec_a, "b").is_some(),
            );

            // (b) Simulate the transitive evaluation that triggers the
            // cycle. Push cycle_a (we're inside its evaluation), push
            // cycle_b (we're inside evaluating the binding it imports from
            // cycle_b), then try to load cycle_a — it's on the stack.
            stack.push("cycle_a");
            stack.push("cycle_b");
            check(
                "stack depth 2 before cycle attempt",
                stack.len() == 2,
            );
            let cycle_result = handle_module_ref("cycle_a", &loader, &config, &mut stack);
            match cycle_result {
                Ok(_) => check(
                    "runtime cycle (cycle_a -> cycle_b -> cycle_a) -> Cycle",
                    false,
                ),
                Err(ModuleHandlerError::Cycle(snap)) => check(
                    "runtime cycle (cycle_a -> cycle_b -> cycle_a) -> Cycle",
                    snap.contains(&"cycle_a".to_string())
                        && snap.contains(&"cycle_b".to_string()),
                ),
                Err(e) => {
                    check(
                        "runtime cycle (cycle_a -> cycle_b -> cycle_a) -> Cycle",
                        false,
                    );
                    eprintln!("  error: {}", e);
                }
            }
            // The cycle attempt must NOT have pushed cycle_a (it was
            // refused before push). Stack still has [cycle_a, cycle_b].
            check(
                "cycle attempt did not push (stack still [cycle_a, cycle_b])",
                stack.len() == 2
                    && stack.contains("cycle_a")
                    && stack.contains("cycle_b"),
            );
            // Clean up the simulated stack.
            stack.pop();
            stack.pop();
            check("stack empty after cleanup", stack.len() == 0);
        }

        // (5) handle_project extracts a known field from a materialized
        //     record -> the field's kernel.
        {
            let mem = build_test_memory_resolver();
            let loader = ModuleLoader::new(Box::new(mem));
            let config = make_config();
            let mut stack = LoadStack::new();
            // Materialize collection/sort, then project "sort".
            let record = handle_module_ref("collection/sort", &loader, &config, &mut stack)
                .expect("load collection/sort");
            match handle_project(&record, "sort", &loader, &config, &mut stack) {
                Ok(k) => {
                    // The "sort" binding's kernel is a Loop (rec { ... }).
                    let is_loop = matches!(k, Kernel::Loop { .. });
                    check(
                        "handle_project extracts 'sort' field kernel",
                        is_loop,
                    );
                }
                Err(e) => {
                    check("handle_project extracts 'sort' field kernel", false);
                    eprintln!("  error: {}", e);
                }
            }
        }

        // (6) handle_project on unknown field -> UnknownField.
        {
            let mem = build_test_memory_resolver();
            let loader = ModuleLoader::new(Box::new(mem));
            let config = make_config();
            let mut stack = LoadStack::new();
            let record = handle_module_ref("collection/sort", &loader, &config, &mut stack)
                .expect("load collection/sort");
            match handle_project(&record, "nonexistent", &loader, &config, &mut stack) {
                Ok(_) => check("project unknown field -> UnknownField", false),
                Err(ModuleHandlerError::UnknownField(f)) => check(
                    "project unknown field -> UnknownField",
                    f == "nonexistent",
                ),
                Err(e) => {
                    check("project unknown field -> UnknownField", false);
                    eprintln!("  error: {}", e);
                }
            }
        }

        // (7) interpret_module_op dispatches module_ref and project
        //     correctly; unknown op -> UnknownOp.
        {
            let mem = build_test_memory_resolver();
            let loader = ModuleLoader::new(Box::new(mem));
            let config = make_config();
            let mut stack = LoadStack::new();

            // module_ref via op dispatch (stringly-typed form).
            let mr_args = vec![Kernel::Const(Lit::Str("collection/sort".to_string()))];
            match interpret_module_op("module_ref", &mr_args, &loader, &config, &mut stack) {
                Ok(k) => check(
                    "interpret_module_op(module_ref) returns module_record",
                    matches!(
                        &k,
                        Kernel::Arr { op, .. } if op == "module_record"
                    ),
                ),
                Err(e) => {
                    check("interpret_module_op(module_ref) returns module_record", false);
                    eprintln!("  error: {}", e);
                }
            }

            // project via op dispatch (stringly-typed form): first
            // materialize a record, then project from it.
            let record = handle_module_ref("collection/sort", &loader, &config, &mut stack)
                .expect("load collection/sort");
            let proj_args = vec![
                record,
                Kernel::Const(Lit::Str("sort".to_string())),
            ];
            match interpret_module_op("project", &proj_args, &loader, &config, &mut stack) {
                Ok(k) => check(
                    "interpret_module_op(project) extracts field kernel",
                    matches!(k, Kernel::Loop { .. }),
                ),
                Err(e) => {
                    check("interpret_module_op(project) extracts field kernel", false);
                    eprintln!("  error: {}", e);
                }
            }

            // Unknown op -> UnknownOp ("handler refuses").
            match interpret_module_op("frobnicate", &[], &loader, &config, &mut stack) {
                Ok(_) => check("unknown op -> UnknownOp", false),
                Err(ModuleHandlerError::UnknownOp(op)) => check(
                    "unknown op -> UnknownOp",
                    op == "frobnicate",
                ),
                Err(e) => {
                    check("unknown op -> UnknownOp", false);
                    eprintln!("  error: {}", e);
                }
            }
        }

        // (8) Default config is safe: empty allowlist denies all paths.
        {
            let mem = build_test_memory_resolver();
            let loader = ModuleLoader::new(Box::new(mem));
            let config = ModuleHandlerConfig::default();
            let mut stack = LoadStack::new();
            check(
                "default config: empty allowlist denies all paths",
                !config.is_path_allowed("collection/sort")
                    && !config.is_path_allowed("anything"),
            );
            match handle_module_ref("collection/sort", &loader, &config, &mut stack) {
                Ok(_) => check("default config denies module_ref", false),
                Err(ModuleHandlerError::Denied(_)) => {
                    check("default config denies module_ref", true)
                }
                Err(e) => {
                    check("default config denies module_ref", false);
                    eprintln!("  error: {}", e);
                }
            }
        }

        // (9) Both encodings: interpret_module_kernel handles the dedicated
        //     Kernel::ModuleRef variant AND the arr("module_ref", ...) form.
        {
            let mem = build_test_memory_resolver();
            let loader = ModuleLoader::new(Box::new(mem));
            let config = make_config();
            let mut stack = LoadStack::new();

            // Dedicated Kernel::ModuleRef variant.
            let dedicated = Kernel::ModuleRef {
                path: "collection/sort".to_string(),
            };
            match interpret_module_kernel(&dedicated, &loader, &config, &mut stack) {
                Ok(k) => check(
                    "interpret_module_kernel handles Kernel::ModuleRef variant",
                    matches!(
                        &k,
                        Kernel::Arr { op, .. } if op == "module_record"
                    ),
                ),
                Err(e) => {
                    check("interpret_module_kernel handles Kernel::ModuleRef variant", false);
                    eprintln!("  error: {}", e);
                }
            }

            // Stringly-typed arr("module_ref", [Const(Str(p))]) form.
            let arr_form = Kernel::Arr {
                op: "module_ref".to_string(),
                args: vec![Kernel::Const(Lit::Str("collection/sort".to_string()))],
            };
            match interpret_module_kernel(&arr_form, &loader, &config, &mut stack) {
                Ok(k) => check(
                    "interpret_module_kernel handles arr(module_ref, ...) form",
                    matches!(
                        &k,
                        Kernel::Arr { op, .. } if op == "module_record"
                    ),
                ),
                Err(e) => {
                    check("interpret_module_kernel handles arr(module_ref, ...) form", false);
                    eprintln!("  error: {}", e);
                }
            }

            // Dedicated Kernel::Project variant: project "sort" from a
            // materialized record (use the dedicated variant directly).
            let record = handle_module_ref("collection/sort", &loader, &config, &mut stack)
                .expect("load collection/sort");
            let dedicated_proj = Kernel::Project {
                field: "sort".to_string(),
                record: Box::new(record),
            };
            match interpret_module_kernel(&dedicated_proj, &loader, &config, &mut stack) {
                Ok(k) => check(
                    "interpret_module_kernel handles Kernel::Project variant",
                    matches!(k, Kernel::Loop { .. }),
                ),
                Err(e) => {
                    check("interpret_module_kernel handles Kernel::Project variant", false);
                    eprintln!("  error: {}", e);
                }
            }

            // A non-module kernel -> UnknownOp (handler only has module-op
            // clauses).
            let non_module = Kernel::Var("x".to_string());
            match interpret_module_kernel(&non_module, &loader, &config, &mut stack) {
                Ok(_) => check("non-module kernel -> UnknownOp", false),
                Err(ModuleHandlerError::UnknownOp(_)) => {
                    check("non-module kernel -> UnknownOp", true)
                }
                Err(e) => {
                    check("non-module kernel -> UnknownOp", false);
                    eprintln!("  error: {}", e);
                }
            }
        }
    }

    println!("\nAll module-system tests passed.");
}
