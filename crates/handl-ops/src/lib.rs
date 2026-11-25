//! # handl-ops
//!
//! The **op ABI** — the registration surface for native Handl operations.
//!
//! An *op* is a Rust implementation of an operation declared in Handl source
//! (`op "cmp.eq" : ...`). Op libraries (`handl-lib-*`, `lib-*` repos) implement
//! [`Op`] and register implementations in an [`OpRegistry`] under their op
//! names. The host adapts [`OpContext`] to its evaluation context, so op
//! crates never depend on `handl-platform`.
//!
//! This is the single open extension point of the kernel substrate: the
//! calculus ([`handl-calculus`]), value ([`handl-value`]), and language
//! schema ([`handl-language`]) are closed; ops extend the platform by
//! registration, not by kernel edits.
//!
//! [`handl-calculus`]: https://github.com/handl-lang/kernel
//! [`handl-value`]: https://github.com/handl-lang/kernel
//! [`handl-language`]: https://github.com/handl-lang/kernel

#![warn(missing_docs)]

mod providers;

pub use providers::{kernel_atom_providers, KernelAtomImpl, KernelAtomProvider, KernelImplTable};

use std::collections::HashMap;
use std::sync::Arc;

use serde_json::Value;
use thiserror::Error;

// ---------------------------------------------------------------------------
// OpError
// ---------------------------------------------------------------------------

/// Errors produced by op implementations.
///
/// Mirrors the host's `EvalError` variants that ops can observe or raise,
/// minus the `Yield` payload — a yielded evaluation's continuation context is
/// host state and never crosses this boundary. The host converts
/// `EvalError::Yield { .. }` to [`OpError::Yield`] when an op observes it.
#[derive(Error, Debug, Clone, PartialEq)]
pub enum OpError {
    /// A value did not match the expected type.
    #[error("type mismatch: {0}")]
    TypeMismatch(String),
    /// A function was called that is not registered in any module.
    #[error("unknown function: {0}")]
    UnknownFunction(String),
    /// A variable was referenced that is not bound in any scope.
    #[error("unknown variable: {0}")]
    UnknownVariable(String),
    /// A resource limit (depth, calls, etc.) was exceeded.
    #[error("resource limit exceeded: {0}")]
    ResourceLimit(String),
    /// Evaluation yielded — the host suspended mid-flight. Ops only observe
    /// this (e.g. `error.try` reporting it); they cannot resume.
    #[error("evaluation yielded")]
    Yield,
    /// A generic op error.
    #[error("op error: {0}")]
    Other(String),
}

// ---------------------------------------------------------------------------
// OpContext — the capability surface ops may use
// ---------------------------------------------------------------------------

/// Evaluation capabilities available to an [`Op`] during its call.
///
/// The kernel defines the surface; the host implements it for its eval
/// context. Pure ops ignore the parameter entirely; higher-order ops use it
/// to evaluate function values or expression strings.
pub trait OpContext {
    /// Evaluate an expression string with the given variable bindings.
    ///
    /// Returns [`OpError::Other`] if the host has no expression evaluator.
    fn eval_expr(&mut self, expr: &str, vars: &[(String, Value)]) -> Result<Value, OpError>;

    /// Call a callable value (e.g. an arrow-value) with the given arguments.
    ///
    /// Returns `None` if the value is not callable through this context;
    /// otherwise the inner `Result` is the call's outcome.
    fn try_call_value(
        &mut self,
        callee: &Value,
        args: &[Value],
    ) -> Option<Result<Value, OpError>>;
}

// ---------------------------------------------------------------------------
// Op — a native operation implementation
// ---------------------------------------------------------------------------

/// A native implementation of a declared Handl op (a "handl" in ADR-0077
/// terms).
///
/// `args` are the already-evaluated argument values. `ctx` exposes the eval
/// capabilities the op may use; pure ops ignore it.
pub trait Op: Send + Sync + 'static {
    /// Invoke the op.
    fn call(&self, args: &[Value], ctx: &mut dyn OpContext) -> Result<Value, OpError>;
}

// ---------------------------------------------------------------------------
// RuntimePredicateChecker — op axiom checks (ADR-0077 Phase 3)
// ---------------------------------------------------------------------------

/// A runtime checker for op axiom predicates.
///
/// Op authors can optionally provide a checker when registering an op. If
/// provided, the checker is called at eval time by the host's dispatch:
/// - [`RuntimePredicateChecker::check_requires`] runs **before** the op
///   executes, with the call args. `Err` rejects the call.
/// - [`RuntimePredicateChecker::check_guarantee`] runs **after** the op
///   executes, with the return value. `Err` rejects the result.
///
/// If no checker is registered, the op's axioms are trusted.
pub trait RuntimePredicateChecker: Send + Sync {
    /// Check the `requires` predicate against call arguments.
    ///
    /// `Ok(())` if satisfied, `Err(message)` describing the violation.
    fn check_requires(&self, args: &[Value]) -> Result<(), String>;

    /// Check the `guarantee` predicate against the return value.
    ///
    /// `Ok(())` if satisfied, `Err(message)` describing the violation.
    fn check_guarantee(&self, output: &Value) -> Result<(), String>;
}

// ---------------------------------------------------------------------------
// OpRegistry — op name → Op impl
// ---------------------------------------------------------------------------

/// A registry mapping op names (e.g. `"cmp.eq"`) to [`Op`] impls.
///
/// Built at construction time via `&mut self` methods, then shared immutably
/// via [`Arc`]. The host imports kernel registries into its own dispatch; op
/// crates never see the host registry type.
#[derive(Default)]
pub struct OpRegistry {
    ops: HashMap<String, Arc<dyn Op>>,
    checkers: HashMap<String, Arc<dyn RuntimePredicateChecker>>,
}

impl OpRegistry {
    /// Create a new, empty `OpRegistry`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Register an [`Op`] under an op name, replacing any previous entry
    /// (and removing its checker — axioms become trusted).
    pub fn register(&mut self, op_name: &str, func: Arc<dyn Op>) {
        self.ops.insert(op_name.to_string(), func);
        self.checkers.remove(op_name);
    }

    /// Register an [`Op`] with an optional runtime axiom checker.
    pub fn register_with_checker(
        &mut self,
        op_name: &str,
        func: Arc<dyn Op>,
        checker: Option<Arc<dyn RuntimePredicateChecker>>,
    ) {
        self.ops.insert(op_name.to_string(), func);
        match checker {
            Some(c) => {
                self.checkers.insert(op_name.to_string(), c);
            }
            None => {
                self.checkers.remove(op_name);
            }
        }
    }

    /// Look up the [`Op`] registered under `op_name`.
    pub fn get(&self, op_name: &str) -> Option<Arc<dyn Op>> {
        self.ops.get(op_name).cloned()
    }

    /// Look up the [`RuntimePredicateChecker`] for `op_name`, if any.
    pub fn get_checker(&self, op_name: &str) -> Option<Arc<dyn RuntimePredicateChecker>> {
        self.checkers.get(op_name).cloned()
    }

    /// Iterate registered ops as `(name, op, checker)` triples.
    pub fn iter(
        &self,
    ) -> impl Iterator<Item = (&str, Arc<dyn Op>, Option<Arc<dyn RuntimePredicateChecker>>)> + '_ {
        self.ops.iter().map(|(name, op)| {
            (
                name.as_str(),
                Arc::clone(op),
                self.checkers.get(name).map(Arc::clone),
            )
        })
    }

    /// Whether an op is registered under `op_name`.
    pub fn contains(&self, op_name: &str) -> bool {
        self.ops.contains_key(op_name)
    }

    /// Number of registered ops.
    pub fn len(&self) -> usize {
        self.ops.len()
    }

    /// Whether the registry is empty.
    pub fn is_empty(&self) -> bool {
        self.ops.is_empty()
    }
}
