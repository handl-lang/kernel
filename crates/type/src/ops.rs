//! Rust `Function` impls for the `typeof` module — the handls (handlers)
//! for the `op`/`handl` declarations in `type.hnl`.
//!
//! All 13 functions and 12 type-tag constants are FFI atoms: they call
//! Rust type-checking and coercion logic that cannot be expressed as pure
//! handl arrows without losing the exact error messages the tests rely
//! on. The `op`/`handl` declaration form (ADR-0077 Phase 2) declares the
//! interface in `type.hnl`; these impls provide the logic and are
//! registered in an
//! [`OpRegistry`](handl_plugin_lib_handl::OpRegistry).

use handl_platform::{EvalContext, EvalError, Function};

use handl_lib_ops::shared::{
    as_kind, complement, err_result, matches, ok_result, project, require_arg_count,
    require_one_arg,
};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn require_one_arg_local(args: &[serde_json::Value]) -> Result<&serde_json::Value, EvalError> {
    args.first().ok_or(EvalError::TypeMismatch(format!(
        "expected {} args, got {}",
        1, 0,
    )))
}

fn require_two_args(
    args: &[serde_json::Value],
) -> Result<(&serde_json::Value, &serde_json::Value), EvalError> {
    if args.len() < 2 {
        return Err(EvalError::TypeMismatch(format!(
            "expected {} args, got {}",
            2,
            args.len(),
        )));
    }
    Ok((&args[0], &args[1]))
}

fn number_to_string(n: f64) -> String {
    format!("{}", n)
}

// ---------------------------------------------------------------------------
// Coercion
// ---------------------------------------------------------------------------

#[derive(Clone, Copy)]
pub struct ToString;
impl Function for ToString {
    fn call(
        &self,
        args: &[serde_json::Value],
        _ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        let arg = require_one_arg_local(args)?;
        let result = if let Some(s) = arg.as_str() {
            s.to_string()
        } else if let Some(n) = arg.as_f64() {
            number_to_string(n)
        } else if let Some(b) = arg.as_bool() {
            b.to_string()
        } else if arg.is_null() {
            "null".to_string()
        } else {
            arg.to_string()
        };
        Ok(serde_json::Value::from(result))
    }
}

#[derive(Clone, Copy)]
pub struct ToNumber;
impl Function for ToNumber {
    fn call(
        &self,
        args: &[serde_json::Value],
        _ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        let arg = require_one_arg_local(args)?;
        let result = if let Some(n) = arg.as_f64() {
            n
        } else if let Some(b) = arg.as_bool() {
            if b { 1.0 } else { 0.0 }
        } else if let Some(s) = arg.as_str() {
            let trimmed = s.trim();
            match trimmed.parse::<f64>() {
                Ok(parsed) if parsed.is_finite() => parsed,
                _ => 0.0,
            }
        } else if arg.is_null() {
            0.0
        } else {
            0.0
        };
        Ok(serde_json::Value::from(serde_json::json!(result)))
    }
}

#[derive(Clone, Copy)]
pub struct ToBool;
impl Function for ToBool {
    fn call(
        &self,
        args: &[serde_json::Value],
        _ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        let arg = require_one_arg_local(args)?;
        let result = if let Some(b) = arg.as_bool() {
            b
        } else if let Some(n) = arg.as_f64() {
            n != 0.0
        } else if let Some(s) = arg.as_str() {
            !s.is_empty()
        } else if arg.is_null() {
            false
        } else if let Some(arr) = arg.as_array() {
            !arr.is_empty()
        } else if let Some(obj) = arg.as_object() {
            !obj.is_empty()
        } else {
            false
        };
        Ok(serde_json::Value::from(result))
    }
}

// ---------------------------------------------------------------------------
// Predicates
// ---------------------------------------------------------------------------

#[derive(Clone, Copy)]
pub struct TypeOf;
impl Function for TypeOf {
    fn call(
        &self,
        args: &[serde_json::Value],
        _ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        let arg = require_one_arg(args)?;
        let type_name = if arg.is_null() {
            "null"
        } else if arg.is_boolean() {
            "bool"
        } else if arg.is_number() {
            "num"
        } else if arg.is_string() {
            "str"
        } else if arg.is_array() {
            "arr"
        } else if arg.is_object() {
            "obj"
        } else {
            "unknown"
        };
        Ok(serde_json::Value::from(type_name.to_string()))
    }
}

#[derive(Clone, Copy)]
pub struct TypeIs;
impl Function for TypeIs {
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
pub struct TypeMust;
impl Function for TypeMust {
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
            None => Ok(err_result(&format!("type.must: expected {kind}"))),
        }
    }
}

#[derive(Clone, Copy)]
pub struct TypeMay;
impl Function for TypeMay {
    fn call(
        &self,
        args: &[serde_json::Value],
        _ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        require_arg_count(args, 2)?;
        let value = &args[0];
        let kind = as_kind(&args[1])?;
        Ok(
            project(value, kind)
                .unwrap_or_else(|| serde_json::Value::from(serde_json::Value::Null)),
        )
    }
}

#[derive(Clone, Copy)]
pub struct TypeNot;
impl Function for TypeNot {
    fn call(
        &self,
        args: &[serde_json::Value],
        _ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        require_arg_count(args, 2)?;
        let value = &args[0];
        let kind = as_kind(&args[1])?;
        Ok(complement(value, kind)
            .unwrap_or_else(|| serde_json::Value::from(serde_json::Value::Null)))
    }
}

#[derive(Clone, Copy)]
pub struct TypeWhen;
impl Function for TypeWhen {
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

// ---------------------------------------------------------------------------
// Type-tag constants
// ---------------------------------------------------------------------------

#[derive(Clone, Copy)]
pub struct StringTag(&'static str);
impl Function for StringTag {
    fn call(
        &self,
        args: &[serde_json::Value],
        _ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        require_arg_count(args, 0)?;
        Ok(serde_json::Value::from(self.0.to_string()))
    }
}

pub static STRING_TAG: StringTag = StringTag("type.string");
pub static STR_TAG: StringTag = StringTag("type.str");
pub static NUMBER_TAG: StringTag = StringTag("type.number");
pub static NUM_TAG: StringTag = StringTag("type.num");
pub static INT_TAG: StringTag = StringTag("type.int");
pub static FLOAT_TAG: StringTag = StringTag("type.float");
pub static BOOL_TAG: StringTag = StringTag("type.bool");
pub static NULL_TAG: StringTag = StringTag("type.null");
pub static ARRAY_TAG: StringTag = StringTag("type.array");
pub static ARR_TAG: StringTag = StringTag("type.arr");
pub static OBJECT_TAG: StringTag = StringTag("type.object");
pub static OBJ_TAG: StringTag = StringTag("type.obj");
pub static ANY_TAG: StringTag = StringTag("type.any");
pub static UNKNOWN_TAG: StringTag = StringTag("type.unknown");

// ---------------------------------------------------------------------------
// Utilities
// ---------------------------------------------------------------------------

#[derive(Clone, Copy)]
pub struct Identity;
impl Function for Identity {
    fn call(
        &self,
        args: &[serde_json::Value],
        _ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        let arg = require_one_arg_local(args)?;
        Ok(arg.clone())
    }
}

#[derive(Clone, Copy)]
pub struct Default;
impl Function for Default {
    fn call(
        &self,
        args: &[serde_json::Value],
        _ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        let (value, fallback) = require_two_args(args)?;
        if value.is_null() {
            Ok(fallback.clone())
        } else {
            Ok(value.clone())
        }
    }
}

#[derive(Clone, Copy)]
pub struct Coalesce;
impl Function for Coalesce {
    fn call(
        &self,
        args: &[serde_json::Value],
        _ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        for arg in args {
            if !arg.is_null() {
                return Ok(arg.clone());
            }
        }
        Ok(serde_json::Value::from(serde_json::Value::Null))
    }
}

use handl_plugin_lib_handl::OpRegistry;
use std::sync::Arc;

pub const TYPE_OPS: &[&str] = &[
    "typeof.string",
    "typeof.str",
    "typeof.number",
    "typeof.num",
    "typeof.bool",
    "typeof.null",
    "typeof.array",
    "typeof.arr",
    "typeof.object",
    "typeof.obj",
    "typeof.any",
    "typeof.unknown",
    "typeof.is",
    "typeof.must",
    "typeof.may",
    "typeof.not",
    "typeof.when",
    "typeof.to_string",
    "typeof.to_number",
    "typeof.to_bool",
    "typeof.type_of",
    "typeof.typeof",
    "typeof.identity",
    "typeof.default",
    "typeof.coalesce",
];

pub fn type_op_registry() -> OpRegistry {
    let mut registry = OpRegistry::new();
    // Type-tag constants
    registry.register("typeof.string", Arc::new(STRING_TAG));
    registry.register("typeof.str", Arc::new(STR_TAG));
    registry.register("typeof.number", Arc::new(NUMBER_TAG));
    registry.register("typeof.num", Arc::new(NUM_TAG));
    registry.register("typeof.bool", Arc::new(BOOL_TAG));
    registry.register("typeof.null", Arc::new(NULL_TAG));
    registry.register("typeof.array", Arc::new(ARRAY_TAG));
    registry.register("typeof.arr", Arc::new(ARR_TAG));
    registry.register("typeof.object", Arc::new(OBJECT_TAG));
    registry.register("typeof.obj", Arc::new(OBJ_TAG));
    registry.register("typeof.any", Arc::new(ANY_TAG));
    registry.register("typeof.unknown", Arc::new(UNKNOWN_TAG));
    // Predicates
    registry.register("typeof.is", Arc::new(TypeIs));
    registry.register("typeof.must", Arc::new(TypeMust));
    registry.register("typeof.may", Arc::new(TypeMay));
    registry.register("typeof.not", Arc::new(TypeNot));
    registry.register("typeof.when", Arc::new(TypeWhen));
    // Coercion
    registry.register("typeof.to_string", Arc::new(ToString));
    registry.register("typeof.to_number", Arc::new(ToNumber));
    registry.register("typeof.to_bool", Arc::new(ToBool));
    // Type-of
    registry.register("typeof.type_of", Arc::new(TypeOf));
    registry.register("typeof.typeof", Arc::new(TypeOf));
    // Utilities
    registry.register("typeof.identity", Arc::new(Identity));
    registry.register("typeof.default", Arc::new(Default));
    registry.register("typeof.coalesce", Arc::new(Coalesce));
    registry
}
