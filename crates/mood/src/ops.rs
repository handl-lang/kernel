//! Rust `Function` impls for the `mood` module — the handls (handlers)
//! for the `op`/`handl` declarations in `mood.hnl`.
//!
//! All 6 functions are FFI atoms: they use `as_kind`, `project`,
//! `complement`, `matches`, `ok_result`, and `err_result` from
//! `crate::shared` and cannot be expressed as pure handl arrows without
//! losing the exact error messages the tests rely on. The `op`/`handl`
//! declaration form (ADR-0077 Phase 2) declares the interface in
//! `mood.hnl`; these impls provide the logic and are registered in an
//! [`OpRegistry`](handl_plugin_lib_handl::OpRegistry).

use handl_platform::{EvalContext, EvalError, Function};
use serde_json::Value as JsonValue;

use handl_lib_ops::shared::{
    as_kind, complement, err_result, matches, ok_result, project, require_arg_count, type_name,
};

#[derive(Clone, Copy)]
pub struct MoodInd;
impl Function for MoodInd {
    fn call(
        &self,
        args: &[serde_json::Value],
        _ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        require_arg_count(args, 2)?;
        let value = &args[0];
        let kind = as_kind(&args[1])?;
        match project(value, kind) {
            Some(v) => Ok(v),
            None => Err(EvalError::Other(format!(
                "mood.ind: expected {kind}, got {}",
                type_name(value)
            ))),
        }
    }
}

#[derive(Clone, Copy)]
pub struct MoodInt;
impl Function for MoodInt {
    fn call(
        &self,
        args: &[serde_json::Value],
        _ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        require_arg_count(args, 2)?;
        let value = &args[0];
        let kind = as_kind(&args[1])?;
        Ok(serde_json::Value::from(matches(value, kind)))
    }
}

#[derive(Clone, Copy)]
pub struct MoodNorm;
impl Function for MoodNorm {
    fn call(
        &self,
        args: &[serde_json::Value],
        _ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        require_arg_count(args, 2)?;
        let value = &args[0];
        let kind = as_kind(&args[1])?;
        match project(value, kind) {
            Some(v) => Ok(ok_result(v)),
            None => Ok(err_result(&format!("mood.norm: expected {kind}"))),
        }
    }
}

#[derive(Clone, Copy)]
pub struct MoodPot;
impl Function for MoodPot {
    fn call(
        &self,
        args: &[serde_json::Value],
        _ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        require_arg_count(args, 2)?;
        let value = &args[0];
        let kind = as_kind(&args[1])?;
        Ok(project(value, kind).unwrap_or_else(|| serde_json::Value::from(JsonValue::Null)))
    }
}

#[derive(Clone, Copy)]
pub struct MoodNeg;
impl Function for MoodNeg {
    fn call(
        &self,
        args: &[serde_json::Value],
        _ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        require_arg_count(args, 2)?;
        let value = &args[0];
        let kind = as_kind(&args[1])?;
        Ok(complement(value, kind).unwrap_or_else(|| serde_json::Value::from(JsonValue::Null)))
    }
}

#[derive(Clone, Copy)]
pub struct MoodCnd;
impl Function for MoodCnd {
    fn call(
        &self,
        args: &[serde_json::Value],
        _ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        require_arg_count(args, 3)?;
        let value = &args[0];
        let kind = as_kind(&args[1])?;
        let default = &args[2];
        Ok(project(value, kind).unwrap_or_else(|| serde_json::Value::from(default.clone())))
    }
}

use handl_plugin_lib_handl::OpRegistry;
use std::sync::Arc;

pub const MOOD_OPS: &[&str] = &[
    "mood.ind",
    "mood.int",
    "mood.norm",
    "mood.pot",
    "mood.neg",
    "mood.cnd",
];

pub fn mood_op_registry() -> OpRegistry {
    let mut registry = OpRegistry::new();
    registry.register("mood.ind", Arc::new(MoodInd));
    registry.register("mood.int", Arc::new(MoodInt));
    registry.register("mood.norm", Arc::new(MoodNorm));
    registry.register("mood.pot", Arc::new(MoodPot));
    registry.register("mood.neg", Arc::new(MoodNeg));
    registry.register("mood.cnd", Arc::new(MoodCnd));
    registry
}
