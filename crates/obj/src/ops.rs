//! `obj` ops — record introspection primitives (gap #3).
//!
//! `obj.keys`/`obj.values`/`obj.entries` enumerate the fields of a Handl
//! object, preserving the iteration order of the underlying
//! `serde_json::Map`. They are the surface `hash_map` (and other record
//! ops) will build on now that arrow/record values cross the
//! `HandlFunction` boundary.

use std::sync::Arc;

use handl_ops::{Op, OpContext, OpError};
use handl_ops::OpRegistry;
use serde_json::{Map, Value};

/// The op names declared in `obj.hnl`.
pub const OBJ_OPS: &[&str] = &["obj.keys", "obj.values", "obj.entries", "obj.set", "obj.from_entries"];

fn require_one_object(args: &[Value]) -> Result<&Map<String, Value>, OpError> {
    let arg = args.first().ok_or_else(|| {
        OpError::TypeMismatch(format!("expected {} args, got {}", 1, args.len()))
    })?;
    arg.as_object().ok_or_else(|| {
        OpError::TypeMismatch(format!(
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

impl Op for Keys {
    fn call(&self, args: &[Value], _ctx: &mut dyn OpContext) -> Result<Value, OpError> {
        let input = require_one_object(args)?;
        Ok(Value::Array(
            input.keys().map(|k| Value::String(k.clone())).collect(),
        ))
    }
}

/// `obj.values(v: object) -> array`
#[derive(Debug, Clone, Copy)]
pub struct Values;

impl Op for Values {
    fn call(&self, args: &[Value], _ctx: &mut dyn OpContext) -> Result<Value, OpError> {
        let input = require_one_object(args)?;
        Ok(Value::Array(input.values().cloned().collect()))
    }
}

/// `obj.entries(v: object) -> array<[string, value]>`
#[derive(Debug, Clone, Copy)]
pub struct Entries;

impl Op for Entries {
    fn call(&self, args: &[Value], _ctx: &mut dyn OpContext) -> Result<Value, OpError> {
        let input = require_one_object(args)?;
        Ok(Value::Array(
            input
                .iter()
                .map(|(k, v)| Value::Array(vec![Value::String(k.clone()), v.clone()]))
                .collect(),
        ))
    }
}

/// `obj.set(obj: object, key: string, value: value) -> object`
#[derive(Debug, Clone, Copy)]
pub struct Set;

impl Op for Set {
    fn call(&self, args: &[Value], _ctx: &mut dyn OpContext) -> Result<Value, OpError> {
        let input = require_one_object(&args[..1])?;
        let key = args
            .get(1)
            .and_then(|v| v.as_str())
            .ok_or_else(|| OpError::TypeMismatch("obj.set key must be a string".to_string()))?;
        let val = args
            .get(2)
            .cloned()
            .ok_or_else(|| OpError::TypeMismatch("obj.set expects 3 args".to_string()))?;
        let mut obj = input.clone();
        obj.insert(key.to_string(), val);
        Ok(Value::Object(obj))
    }
}

/// `obj.from_entries(entries: array<[string, value]>) -> object`
#[derive(Debug, Clone, Copy)]
pub struct FromEntries;

impl Op for FromEntries {
    fn call(&self, args: &[Value], _ctx: &mut dyn OpContext) -> Result<Value, OpError> {
        let entries = args
            .first()
            .and_then(|v| v.as_array())
            .ok_or_else(|| OpError::TypeMismatch("obj.from_entries expects an array".to_string()))?;
        let mut obj = serde_json::Map::new();
        for e in entries {
            let pair = e
                .as_array()
                .ok_or_else(|| OpError::TypeMismatch("entry must be [key, value]".to_string()))?;
            let key = pair
                .first()
                .and_then(|v| v.as_str())
                .ok_or_else(|| OpError::TypeMismatch("entry key must be a string".to_string()))?;
            let val = pair.get(1).cloned().unwrap_or(Value::Null);
            obj.insert(key.to_string(), val);
        }
        Ok(Value::Object(obj))
    }
}

/// Build the [`OpRegistry`] for the `obj` module.
pub fn obj_op_registry() -> OpRegistry {
    let mut registry = OpRegistry::new();
    registry.register("obj.keys", Arc::new(Keys));
    registry.register("obj.values", Arc::new(Values));
    registry.register("obj.entries", Arc::new(Entries));
    registry.register("obj.set", Arc::new(Set));
    registry.register("obj.from_entries", Arc::new(FromEntries));
    registry
}
