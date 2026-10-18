//! Shared helpers for handl library crates.
//!
//! These primitives (argument requirements, value constructors, function
//! application, extremum selection) are used by the modules in this crate and
//! are also re-exported for sibling library crates such as
//! `handl-plugin-lib-cmp` so they can compose without duplicating the
//! function-value machinery.

use serde_json::{Map, Value as JsonValue};

use crate::function_value::FunctionValue;
use handl_platform::{EvalContext, EvalError};

// ════════════════════════════════════════════════════════════════════
// Tier 0: Shared helpers (replaces duplicated copies across modules)
// ════════════════════════════════════════════════════════════════════

// ── type requirements ──────────────────────────────────────────────

pub fn require_array(arg: &serde_json::Value) -> Result<&[serde_json::Value], EvalError> {
    arg.as_array()
        .map(Vec::as_slice)
        .ok_or(EvalError::TypeMismatch(format!(
            "expected {}, got {}",
            "array", "non-array",
        )))
}

pub fn require_function_value(arg: &serde_json::Value) -> Result<FunctionValue, EvalError> {
    FunctionValue::from_json(arg).ok_or(EvalError::TypeMismatch(format!(
        "expected {}, got {}",
        "function value", "non-function",
    )))
}

// ── argument count requirements ────────────────────────────────────

pub fn require_one_arg(args: &[serde_json::Value]) -> Result<&serde_json::Value, EvalError> {
    args.first().ok_or(EvalError::TypeMismatch(format!(
        "expected {} args, got {}",
        1, 0,
    )))
}

#[allow(dead_code)]
pub fn require_one_array(
    args: &[serde_json::Value],
) -> Result<&[serde_json::Value], EvalError> {
    let arg = args.first().ok_or(EvalError::TypeMismatch(format!(
        "expected {} args, got {}",
        1, 0,
    )))?;
    require_array(arg)
}

#[allow(dead_code)]
pub fn require_two_arrays(
    args: &[serde_json::Value],
) -> Result<(&[serde_json::Value], &[serde_json::Value]), EvalError> {
    if args.len() < 2 {
        return Err(EvalError::TypeMismatch(format!(
            "expected {} args, got {}",
            2,
            args.len(),
        )));
    }
    let a = require_array(&args[0])?;
    let b = require_array(&args[1])?;
    Ok((a, b))
}

pub fn require_function_and_array(
    args: &[serde_json::Value],
) -> Result<(FunctionValue, &[serde_json::Value]), EvalError> {
    if args.len() < 2 {
        return Err(EvalError::TypeMismatch(format!(
            "expected {} args, got {}",
            2,
            args.len(),
        )));
    }
    let fn_val = require_function_value(&args[0])?;
    let array = require_array(&args[1])?;
    Ok((fn_val, array))
}

pub fn require_functions(
    args: &[serde_json::Value],
) -> Result<Vec<FunctionValue>, EvalError> {
    if args.is_empty() {
        return Err(EvalError::TypeMismatch(format!(
            "expected {} args, got {}",
            1, 0,
        )));
    }
    args.iter().map(require_function_value).collect()
}

// ── param binding ──────────────────────────────────────────────────

pub fn bind_param(
    fn_val: &FunctionValue,
    value: &serde_json::Value,
) -> Vec<(String, serde_json::Value)> {
    fn_val
        .params
        .first()
        .map(|(name, _)| vec![(name.clone(), serde_json::Value::from(value.clone()))])
        .unwrap_or_default()
}

pub fn bind_two_params(
    fn_val: &FunctionValue,
    acc: &serde_json::Value,
    item: &serde_json::Value,
) -> Vec<(String, serde_json::Value)> {
    let param_names: Vec<&String> = fn_val.params.iter().map(|(name, _)| name).collect();
    let acc_name = param_names.first().map(|s| s.as_str()).unwrap_or("acc");
    let item_name = param_names.get(1).map(|s| s.as_str()).unwrap_or("x");
    vec![
        (acc_name.to_string(), serde_json::Value::from(acc.clone())),
        (item_name.to_string(), serde_json::Value::from(item.clone())),
    ]
}

fn pattern_binding_name(pattern: &JsonValue) -> Option<&str> {
    pattern.get("type").and_then(|v| v.as_str())?;
    pattern.get("name").and_then(|v| v.as_str())
}

fn destructure_pattern(
    pattern: &JsonValue,
    value: &JsonValue,
    out: &mut Vec<(String, JsonValue)>,
) -> Result<(), EvalError> {
    match pattern.get("type").and_then(|v| v.as_str()) {
        Some("identifier") => {
            if let Some(name) = pattern_binding_name(pattern) {
                out.push((name.to_string(), value.clone()));
            }
        }
        Some("array") => {
            let patterns = pattern
                .get("patterns")
                .and_then(|v| v.as_array())
                .ok_or(EvalError::Other("invalid array pattern".to_string()))?;
            let arr = value.as_array().ok_or(EvalError::TypeMismatch(format!(
                "expected {}, got {}",
                "array", "non-array",
            )))?;
            for (i, child_pattern) in patterns.iter().enumerate() {
                let child = arr.get(i).unwrap_or(&JsonValue::Null);
                destructure_pattern(child_pattern, child, out)?;
            }
        }
        Some("object") => {
            let obj = value.as_object().ok_or(EvalError::TypeMismatch(format!(
                "expected {}, got {}",
                "object", "non-object",
            )))?;
            let entries = pattern
                .get("entries")
                .and_then(|v| v.as_array())
                .ok_or(EvalError::Other("invalid object pattern".to_string()))?;
            for entry in entries {
                let arr = entry
                    .as_array()
                    .ok_or(EvalError::Other("invalid object pattern entry".to_string()))?;
                let key = arr
                    .get(0)
                    .and_then(|v| v.as_str())
                    .ok_or(EvalError::Other("invalid object pattern key".to_string()))?;
                let child_pattern = arr
                    .get(1)
                    .ok_or(EvalError::Other("invalid object pattern entry".to_string()))?;
                let child = obj.get(key).unwrap_or(&JsonValue::Null);
                destructure_pattern(child_pattern, child, out)?;
            }
        }
        _ => {}
    }
    Ok(())
}

pub fn bind_function_params(
    fn_val: &FunctionValue,
    args: &[JsonValue],
) -> Result<Vec<(String, serde_json::Value)>, EvalError> {
    let mut bindings = Vec::new();

    for (i, (name, _)) in fn_val.params.iter().enumerate() {
        let arg = args.get(i).unwrap_or(&JsonValue::Null);

        if let Some(pattern) = fn_val.patterns.get(i) {
            if pattern.get("type").is_some() {
                let mut raw = Vec::new();
                destructure_pattern(pattern, arg, &mut raw)?;
                bindings.extend(
                    raw.into_iter()
                        .map(|(n, v)| (n, serde_json::Value::from(v))),
                );
                continue;
            }
        }

        bindings.push((name.clone(), serde_json::Value::from(arg.clone())));
    }

    Ok(bindings)
}

// ── truthiness ─────────────────────────────────────────────────────

pub fn is_truthy_value(value: &serde_json::Value) -> bool {
    if let Some(b) = value.as_bool() {
        b
    } else if let Some(n) = value.as_f64() {
        n != 0.0
    } else if let Some(s) = value.as_str() {
        !s.is_empty()
    } else if value.is_null() {
        false
    } else if let Some(arr) = value.as_array() {
        !arr.is_empty()
    } else if let Some(obj) = value.as_object() {
        !obj.is_empty()
    } else {
        true
    }
}

// ── constructors ───────────────────────────────────────────────────

pub fn arr(items: &[serde_json::Value]) -> serde_json::Value {
    serde_json::Value::from(serde_json::Value::Array(items.to_vec()))
}

pub fn b(value: bool) -> serde_json::Value {
    serde_json::Value::from(value)
}

pub fn num(value: f64) -> serde_json::Value {
    serde_json::Value::from(serde_json::json!(value))
}

// ── string conversion ──────────────────────────────────────────────

pub fn key_to_string(value: &serde_json::Value) -> String {
    if let Some(s) = value.as_str() {
        s.to_string()
    } else if let Some(n) = value.as_f64() {
        if n == n.trunc() {
            format!("{n:.0}")
        } else {
            n.to_string()
        }
    } else if let Some(b) = value.as_bool() {
        b.to_string()
    } else if value.is_null() {
        "null".to_string()
    } else {
        serde_json::to_string(&value.clone()).unwrap_or_else(|_| "unknown".to_string())
    }
}

#[allow(dead_code)]
pub fn value_to_string(value: &serde_json::Value) -> String {
    match value {
        serde_json::Value::String(s) => s.clone(),
        serde_json::Value::Number(n) => {
            if let Some(f) = n.as_f64() {
                if f == f.trunc() {
                    format!("{f:.0}")
                } else {
                    f.to_string()
                }
            } else {
                n.to_string()
            }
        }
        serde_json::Value::Bool(b) => b.to_string(),
        serde_json::Value::Null => "null".to_string(),
        _ => serde_json::to_string(value).unwrap_or_else(|_| "unknown".to_string()),
    }
}

// ── extremum selection ─────────────────────────────────────────────

/// Returns a reference to the element selected by `better` over all items.
/// `better(candidate, best)` should be true when `candidate` should replace `best`.
pub fn find_extremum_by<'a, T>(
    items: &'a [T],
    mut better: impl FnMut(&T, &T) -> bool,
) -> Option<&'a T> {
    items
        .iter()
        .reduce(|best, x| if better(x, best) { x } else { best })
}

// ── type predicates (mood / type.*) ─────────────────────────────────

pub fn require_arg_count(
    args: &[serde_json::Value],
    expected: usize,
) -> Result<(), EvalError> {
    if args.len() != expected {
        return Err(EvalError::TypeMismatch(format!(
            "expected {} args, got {}",
            expected,
            args.len()
        )));
    }
    Ok(())
}

pub fn as_kind(value: &serde_json::Value) -> Result<&str, EvalError> {
    value
        .as_str()
        .ok_or_else(|| EvalError::Other("type kind must be a string".to_string()))
}

pub fn type_name(value: &serde_json::Value) -> &'static str {
    if value.is_null() {
        "null"
    } else if value.is_boolean() {
        "bool"
    } else if value.is_number() {
        "num"
    } else if value.is_string() {
        "str"
    } else if value.is_array() {
        "arr"
    } else if value.is_object() {
        "obj"
    } else {
        "unknown"
    }
}

pub fn matches(value: &serde_json::Value, kind: &str) -> bool {
    if let Some(rest) = kind.strip_prefix("type.") {
        match rest {
            "any" | "unknown" => true,
            "never" => false,
            "null" => value.is_null(),
            "bool" | "boolean" | "bin" => value.is_boolean(),
            "num" | "number" => value.is_number(),
            "str" | "string" => value.is_string(),
            "arr" | "array" => value.is_array(),
            "obj" | "object" => value.is_object(),
            _ => false,
        }
    } else if let Some(rest) = kind.strip_prefix("field.") {
        value.as_object().is_some_and(|o| o.get(rest).is_some())
    } else {
        value.as_object().is_some_and(|o| o.get(kind).is_some())
    }
}

pub fn project(value: &serde_json::Value, kind: &str) -> Option<serde_json::Value> {
    if kind.starts_with("type.") {
        if matches(value, kind) {
            Some(serde_json::Value::from(value.clone()))
        } else {
            None
        }
    } else if let Some(rest) = kind.strip_prefix("field.") {
        value
            .as_object()
            .and_then(|o| o.get(rest))
            .map(|v| serde_json::Value::from(v.clone()))
    } else {
        value
            .as_object()
            .and_then(|o| o.get(kind))
            .map(|v| serde_json::Value::from(v.clone()))
    }
}

pub fn complement(value: &serde_json::Value, kind: &str) -> Option<serde_json::Value> {
    if matches(value, kind) {
        return None;
    }

    if kind.starts_with("type.") || kind.starts_with("field.") {
        return Some(serde_json::Value::from(value.clone()));
    }

    // Variant tag: the complement is another key in the same object,
    // or the value itself if it is not a tagged object.
    if let Some(obj) = value.as_object() {
        obj.iter()
            .find(|(k, _)| k.as_str() != kind)
            .map(|(_, v)| serde_json::Value::from(v.clone()))
    } else {
        Some(serde_json::Value::from(value.clone()))
    }
}

pub fn ok_result(value: serde_json::Value) -> serde_json::Value {
    serde_json::Value::from(JsonValue::Object(Map::from_iter([(
        "ok".to_string(),
        value,
    )])))
}

pub fn err_result(message: &str) -> serde_json::Value {
    serde_json::Value::from(JsonValue::Object(Map::from_iter([(
        "err".to_string(),
        JsonValue::String(message.to_string()),
    )])))
}

// ════════════════════════════════════════════════════════════════════
// Tier 1: Composable primitives
// ════════════════════════════════════════════════════════════════════

/// Apply a single-param function to a value: bind_param + eval_expr.
pub fn apply_fn(
    ctx: &mut EvalContext,
    fn_val: &FunctionValue,
    value: &serde_json::Value,
) -> Result<serde_json::Value, EvalError> {
    let vars = bind_param(fn_val, value);
    ctx.eval_expr(&fn_val.body, &vars)
}

/// Apply a two-param function to two values: bind_two_params + eval_expr.
pub fn apply_fn2(
    ctx: &mut EvalContext,
    fn_val: &FunctionValue,
    a: &serde_json::Value,
    b: &serde_json::Value,
) -> Result<serde_json::Value, EvalError> {
    let vars = bind_two_params(fn_val, a, b);
    ctx.eval_expr(&fn_val.body, &vars)
}

/// Check if a value is an arrow-value (first-class function from the
/// tree-walk engine).
pub fn is_arrow_value(value: &serde_json::Value) -> bool {
    value
        .as_object()
        .and_then(|obj| obj.get("__arrow__"))
        .and_then(|v| v.as_bool())
        .unwrap_or(false)
}

/// Apply a callable value (arrow-value or FunctionValue) to a single arg.
/// If the value is an arrow-value, uses `ctx.try_call_value`. Otherwise,
/// falls back to `FunctionValue` + `eval_expr`.
pub fn apply_callable(
    ctx: &mut EvalContext,
    fn_arg: &serde_json::Value,
    value: &serde_json::Value,
) -> Result<serde_json::Value, EvalError> {
    if is_arrow_value(fn_arg) {
        ctx.try_call_value(fn_arg, std::slice::from_ref(value))
            .unwrap_or_else(|| {
                Err(EvalError::TypeMismatch(
                    "call_value: no value callable set in context".to_string(),
                ))
            })
    } else {
        let fn_val = require_function_value(fn_arg)?;
        apply_fn(ctx, &fn_val, value)
    }
}

/// Apply a callable value to two args (for reduce-like combinators).
pub fn apply_callable2(
    ctx: &mut EvalContext,
    fn_arg: &serde_json::Value,
    a: &serde_json::Value,
    b: &serde_json::Value,
) -> Result<serde_json::Value, EvalError> {
    if is_arrow_value(fn_arg) {
        ctx.try_call_value(fn_arg, &[a.clone(), b.clone()])
            .unwrap_or_else(|| {
                Err(EvalError::TypeMismatch(
                    "call_value: no value callable set in context".to_string(),
                ))
            })
    } else {
        let fn_val = require_function_value(fn_arg)?;
        apply_fn2(ctx, &fn_val, a, b)
    }
}

/// Check if a callable value's result is truthy (for filter-like combinators).
pub fn is_truthy_callable(
    ctx: &mut EvalContext,
    fn_arg: &serde_json::Value,
    value: &serde_json::Value,
) -> Result<bool, EvalError> {
    let result = apply_callable(ctx, fn_arg, value)?;
    Ok(is_truthy_value(&result))
}

/// Apply a predicate function and check if the result is truthy.
pub fn is_truthy_fn(
    ctx: &mut EvalContext,
    fn_val: &FunctionValue,
    value: &serde_json::Value,
) -> Result<bool, EvalError> {
    let result = apply_fn(ctx, fn_val, value)?;
    Ok(is_truthy_value(&result))
}

/// Map a function over an iterator, collecting results.
/// Works with any iterator yielding `&serde_json::Value`.
pub fn map_iter<'a, I>(
    ctx: &mut EvalContext,
    fn_val: &FunctionValue,
    iter: I,
) -> Result<Vec<serde_json::Value>, EvalError>
where
    I: Iterator<Item = &'a serde_json::Value>,
{
    let mut results = Vec::new();
    for item in iter {
        let mapped = apply_fn(ctx, fn_val, item)?;
        results.push(mapped);
    }
    Ok(results)
}

/// Map a callable (arrow-value or FunctionValue) over an iterator.
pub fn map_callable_iter<'a, I>(
    ctx: &mut EvalContext,
    fn_arg: &serde_json::Value,
    iter: I,
) -> Result<Vec<serde_json::Value>, EvalError>
where
    I: Iterator<Item = &'a serde_json::Value>,
{
    let mut results = Vec::new();
    for item in iter {
        let mapped = apply_callable(ctx, fn_arg, item)?;
        results.push(mapped);
    }
    Ok(results)
}

/// Filter an iterator by a callable predicate (arrow-value or FunctionValue).
pub fn filter_callable_iter<'a, I>(
    ctx: &mut EvalContext,
    fn_arg: &serde_json::Value,
    iter: I,
) -> Result<Vec<serde_json::Value>, EvalError>
where
    I: Iterator<Item = &'a serde_json::Value>,
{
    let mut results = Vec::new();
    for item in iter {
        if is_truthy_callable(ctx, fn_arg, item)? {
            results.push(item.clone());
        }
    }
    Ok(results)
}

/// Fold an iterator with a two-param callable (arrow-value or FunctionValue).
pub fn fold_callable_iter<'a, I>(
    ctx: &mut EvalContext,
    fn_arg: &serde_json::Value,
    iter: I,
    init: serde_json::Value,
) -> Result<serde_json::Value, EvalError>
where
    I: Iterator<Item = &'a serde_json::Value>,
{
    let mut acc = init;
    for item in iter {
        let result = apply_callable2(ctx, fn_arg, &acc, item)?;
        acc = result;
    }
    Ok(acc)
}

/// Find the first element matching a predicate.
/// Returns `None` if no match.
pub fn find_first<'a, I>(
    ctx: &mut EvalContext,
    fn_val: &FunctionValue,
    iter: I,
) -> Result<Option<serde_json::Value>, EvalError>
where
    I: Iterator<Item = &'a serde_json::Value>,
{
    for item in iter {
        if is_truthy_fn(ctx, fn_val, item)? {
            return Ok(Some(item.clone()));
        }
    }
    Ok(None)
}

/// Find the index of the first element matching a predicate.
/// Returns `None` if no match.
#[allow(dead_code)]
pub fn find_index<'a, I>(
    ctx: &mut EvalContext,
    fn_val: &FunctionValue,
    iter: I,
) -> Result<Option<usize>, EvalError>
where
    I: Iterator<Item = &'a serde_json::Value>,
{
    for (i, item) in iter.enumerate() {
        if is_truthy_fn(ctx, fn_val, item)? {
            return Ok(Some(i));
        }
    }
    Ok(None)
}
