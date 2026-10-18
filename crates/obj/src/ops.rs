//! `obj` ops — record introspection primitives (gap #3).
//!
//! `obj.keys`/`obj.values`/`obj.entries` enumerate the fields of a Handl
//! object, preserving the iteration order of the underlying
//! `serde_json::Map`. They are the surface `hash_map` (and other record
//! ops) will build on now that arrow/record values cross the
//! `HandlFunction` boundary.

use std::sync::Arc;

use handl_platform::{EvalContext, EvalError, Function};
use handl_plugin_lib_handl::OpRegistry;
use serde_json::{Map, Value};

/// The op names declared in `obj.hnl`.
pub const OBJ_OPS: &[&str] = &["obj.keys", "obj.values", "obj.entries"];

fn require_one_object(args: &[Value]) -> Result<&Map<String, Value>, EvalError> {
    let arg = args.first().ok_or_else(|| {
        EvalError::TypeMismatch(format!("expected {} args, got {}", 1, args.len()))
    })?;
    arg.as_object().ok_or_else(|| {
        EvalError::TypeMismatch(format!(
            "expected {}, got {}",
            "object",
            json_type_name(arg)
        ))
    })
}

fn json_type_name(v: &Value) -> &'static str {
    match v {
        Value::Null => "null",
        Value::Bool(_) => "bool",
        Value::Number(_) => "number",
        Value::String(_) => "string",
        Value::Array(_) => "array",
        Value::Object(_) => "object",
    }
}

/// `obj.keys(v: object) -> array<string>`
#[derive(Debug, Clone, Copy)]
pub struct Keys;

impl Function for Keys {
    fn call(&self, args: &[Value], _ctx: &mut EvalContext) -> Result<Value, EvalError> {
        let input = require_one_object(args)?;
        Ok(Value::Array(
            input.keys().map(|k| Value::String(k.clone())).collect(),
        ))
    }
}

/// `obj.values(v: object) -> array`
#[derive(Debug, Clone, Copy)]
pub struct Values;

impl Function for Values {
    fn call(&self, args: &[Value], _ctx: &mut EvalContext) -> Result<Value, EvalError> {
        let input = require_one_object(args)?;
        Ok(Value::Array(input.values().cloned().collect()))
    }
}

/// `obj.entries(v: object) -> array<[string, value]>`
#[derive(Debug, Clone, Copy)]
pub struct Entries;

impl Function for Entries {
    fn call(&self, args: &[Value], _ctx: &mut EvalContext) -> Result<Value, EvalError> {
        let input = require_one_object(args)?;
        Ok(Value::Array(
            input
                .iter()
                .map(|(k, v)| Value::Array(vec![Value::String(k.clone()), v.clone()]))
                .collect(),
        ))
    }
}

/// Build the [`OpRegistry`] for the `obj` module.
pub fn obj_op_registry() -> OpRegistry {
    let mut registry = OpRegistry::new();
    registry.register("obj.keys", Arc::new(Keys));
    registry.register("obj.values", Arc::new(Values));
    registry.register("obj.entries", Arc::new(Entries));
    registry
}
