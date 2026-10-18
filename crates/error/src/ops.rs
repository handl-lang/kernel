//! `error` ops — the error-raising primitive (ADR-0092 gap (a)).
//!
//! `error.raise(v)` aborts the current evaluation with `v` as the error
//! payload: it never returns a value. The [`OpRegistry`] maps the op name
//! declared in `handl-packages/error/error.hnl` to the Rust handl below.
//!
//! This is the raise half of the ADR-0092 error story. There is still no
//! error-*capture* primitive (`assert.throws`/`test.run` need a
//! handl-reachable `EvalContext::try_call_value`), so a raised error
//! always propagates out of `eval` as a normal eval failure.
//!
//! Payload convention: a `String` payload is the message verbatim; any
//! other value is embedded as its JSON serialization. Errors surface as
//! [`EvalError::Other`], matching how `collections`' `collection is
//! empty` and other contract violations report today.

use std::sync::Arc;

use handl_platform::{EvalContext, EvalError, Function};
use handl_plugin_lib_handl::OpRegistry;
use serde_json::{Map, Value};

/// The op names declared in `error.hnl`.
pub const ERROR_OPS: &[&str] = &["error.raise", "error.try"];

/// The Rust handl for `op "error.raise" : Value -> a`.
///
/// Fails loudly: always returns `Err`, never `Ok`. A missing payload
/// defaults to a generic message so `error.raise()` still aborts.
#[derive(Debug, Clone, Copy)]
pub struct Raise;

impl Function for Raise {
    fn call(&self, args: &[Value], _ctx: &mut EvalContext) -> Result<Value, EvalError> {
        let message = match args.first() {
            None => "error raised".to_string(),
            Some(Value::String(s)) => s.clone(),
            Some(v) => serde_json::to_string(v).unwrap_or_else(|_| v.to_string()),
        };
        Err(EvalError::Other(message))
    }
}

/// `error.try(thunk: Fn) -> result`
///
/// Calls the provided arrow with `null` for each of its parameters and
/// captures any raised `EvalError`. Returns a `result`-shaped tag value:
/// `{"__tag__": "ok", "value": v}` on success or
/// `{"__tag__": "err", "value": <message>}` on failure.
#[derive(Debug, Clone, Copy)]
pub struct Try;

fn eval_error_message(e: EvalError) -> String {
    match e {
        EvalError::Other(s)
        | EvalError::TypeMismatch(s)
        | EvalError::UnknownFunction(s)
        | EvalError::UnknownVariable(s)
        | EvalError::ResourceLimit(s) => s,
        EvalError::Yield { .. } => "evaluation yielded".to_string(),
    }
}

impl Function for Try {
    fn call(&self, args: &[Value], ctx: &mut EvalContext) -> Result<Value, EvalError> {
        let f = args.first().ok_or_else(|| {
            EvalError::TypeMismatch(format!("expected {} args, got {}", 1, args.len()))
        })?;

        // Thunks are typically nullary, but callers may write `_ ~> ...`
        // or `x ~> ...`; supply `null` for every declared parameter so the
        // body runs regardless of whether the parameter is used.
        let params_len = f
            .as_object()
            .and_then(|o| o.get("params"))
            .and_then(|p| p.as_array())
            .map(|a| a.len())
            .unwrap_or(0);
        let call_args: Vec<Value> = (0..params_len).map(|_| Value::Null).collect();

        match ctx.try_call_value(f, &call_args) {
            Some(Ok(v)) => {
                let mut ok = Map::new();
                ok.insert("__tag__".to_string(), Value::String("ok".to_string()));
                ok.insert("value".to_string(), v);
                Ok(Value::Object(ok))
            }
            Some(Err(e)) => {
                let mut err = Map::new();
                err.insert("__tag__".to_string(), Value::String("err".to_string()));
                err.insert("value".to_string(), Value::String(eval_error_message(e)));
                Ok(Value::Object(err))
            }
            None => Err(EvalError::Other(
                "error.try: no value callable in context".to_string(),
            )),
        }
    }
}

/// Build the [`OpRegistry`] for the `error` module.
pub fn error_op_registry() -> OpRegistry {
    let mut registry = OpRegistry::new();
    registry.register("error.raise", Arc::new(Raise));
    registry.register("error.try", Arc::new(Try));
    registry
}
