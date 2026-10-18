//! Rust `Function` impls for the `combinators` and `transform` modules —
//! the handls (handlers) for the `op`/`handl` declarations in
//! `combinators.hnl` / `transform.hnl`.
//!
//! All functions are FFI atoms: they manipulate `serde_json::Value`
//! callables via `apply_fn` from `crate::shared` and cannot be expressed
//! as pure handl arrows without losing the exact `TypeMismatch` error
//! messages the tests rely on. The `op`/`handl` declaration form
//! (ADR-0077 Phase 2) declares the interface in `combinators.hnl`; these
//! impls provide the logic and are registered in an
//! [`OpRegistry`](handl_plugin_lib_handl::OpRegistry).

use handl_platform::{EvalContext, EvalError, Function};

use handl_lib_ops::function_value::FunctionValue;
use serde_json::Value as JsonValue;

use handl_lib_ops::shared::{
    apply_fn, apply_fn2, arr, b, bind_function_params, filter_callable_iter, find_first,
    fold_callable_iter, is_truthy_fn, key_to_string, map_callable_iter, map_iter, require_array,
    require_function_and_array, require_function_value, require_functions,
};

// ===========================================================================
// Helpers
// ===========================================================================

fn substitute_param(body: &str, param: &str, replacement: &str) -> String {
    let wrapped = format!("({replacement})");
    let mut result = String::new();
    let bytes = body.as_bytes();
    let mut i = 0;
    let mut in_string = false;
    while i < body.len() {
        let ch = bytes[i];
        if in_string {
            if ch == b'\\' && i + 1 < body.len() {
                result.push_str(&body[i..i + 2]);
                i += 2;
                continue;
            }
            if ch == b'"' {
                in_string = false;
                result.push('"');
                i += 1;
                continue;
            }
            let end = next_char_boundary(body, i);
            result.push_str(&body[i..end]);
            i = end;
            continue;
        }
        if ch == b'"' {
            in_string = true;
            result.push('"');
            i += 1;
            continue;
        }
        if body[i..].starts_with(param) {
            let before_ok = i == 0 || !is_ident_char(bytes[i - 1]);
            let after = i + param.len();
            let after_ok = after >= body.len() || !is_ident_char(bytes[after]);
            if before_ok && after_ok {
                result.push_str(&wrapped);
                i = after;
                continue;
            }
        }
        let end = next_char_boundary(body, i);
        result.push_str(&body[i..end]);
        i = end;
    }
    result
}

fn next_char_boundary(s: &str, i: usize) -> usize {
    let mut j = i + 1;
    while j < s.len() && !s.is_char_boundary(j) {
        j += 1;
    }
    j
}

fn is_ident_char(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

fn inline_chain(fns: &[FunctionValue]) -> Result<FunctionValue, EvalError> {
    if fns.is_empty() {
        return Err(EvalError::TypeMismatch(format!(
            "expected {} args, got {}",
            1, 0,
        )));
    }
    let first_fn = &fns[0];
    let input_param = first_fn
        .params
        .first()
        .map(|(name, _)| name.as_str())
        .unwrap_or("x");

    let mut body = first_fn.body.clone();
    for fn_val in &fns[1..] {
        let param = fn_val
            .params
            .first()
            .map(|(name, _)| name.as_str())
            .unwrap_or("x");
        body = substitute_param(&fn_val.body, param, &body);
    }

    Ok(FunctionValue {
        params: vec![(input_param.to_string(), serde_json::Value::Null)],
        return_schema: None,
        body,
        patterns: Vec::new(),
        captured: Vec::new(),
    })
}

// ===========================================================================
// Composition combinators
// ===========================================================================

// ── pipe ───────────────────────────────────────────────────────────

#[derive(Clone, Copy)]
pub struct Pipe;
impl Function for Pipe {
    fn call(
        &self,
        args: &[serde_json::Value],
        ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        if args.len() < 2 {
            return Err(EvalError::TypeMismatch(format!(
                "expected {} args, got {}",
                2,
                args.len(),
            )));
        }
        let mut value = args[0].clone();
        for fn_arg in &args[1..] {
            let fn_val = require_function_value(fn_arg)?;
            value = apply_fn(ctx, &fn_val, &value)?;
        }
        Ok(value)
    }
}

// ── flow / compose ─────────────────────────────────────────────────

#[derive(Clone, Copy)]
pub struct Flow;
impl Function for Flow {
    fn call(
        &self,
        args: &[serde_json::Value],
        _ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        let fns = require_functions(args)?;
        let composed = inline_chain(&fns)?;
        Ok(serde_json::Value::from(composed))
    }
}

#[derive(Clone, Copy)]
pub struct Compose;
impl Function for Compose {
    fn call(
        &self,
        args: &[serde_json::Value],
        _ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        let fns = require_functions(args)?;
        let reversed: Vec<FunctionValue> = fns.into_iter().rev().collect();
        let composed = inline_chain(&reversed)?;
        Ok(serde_json::Value::from(composed))
    }
}

// ── fanout ─────────────────────────────────────────────────────────

#[derive(Clone, Copy)]
pub struct Fanout;
impl Function for Fanout {
    fn call(
        &self,
        args: &[serde_json::Value],
        ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        if args.len() < 2 {
            return Err(EvalError::TypeMismatch(format!(
                "expected {} args, got {}",
                2,
                args.len(),
            )));
        }
        let value = args[0].clone();
        let inner = value;
        let mut results = Vec::with_capacity(args.len() - 1);
        for fn_arg in &args[1..] {
            let fn_val = require_function_value(fn_arg)?;
            let result = apply_fn(ctx, &fn_val, &inner)?;
            results.push(result);
        }
        Ok(arr(&results))
    }
}

// ── fanout_fn ──────────────────────────────────────────────────────

/// Lazy fanout: `fn.fanout_fn(f, g)` returns a function `x => fn.fanout(x, f, g)`,
/// i.e. an arrow that splits its input across `f` and `g` and yields
/// `[f(x), g(x)]`. This is the curried/combinator form of [`Fanout`] and the
/// desugar target of the `&&&` arrow-calculus sugar.
#[derive(Clone, Copy)]
pub struct FanoutFn;
impl Function for FanoutFn {
    fn call(
        &self,
        args: &[serde_json::Value],
        _ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        let fns = require_functions(args)?;
        // Bake the branch functions into the body as object-literal JSON so the
        // returned arrow, when applied, calls `fn.fanout(x, f, g, ...)`. Object
        // literals accept quoted keys, so `serde_json::to_string` output parses.
        let branches: Vec<String> = fns
            .iter()
            .map(|fv| serde_json::to_string(&fv.clone().to_json()))
            .collect::<Result<_, _>>()
            .map_err(|e| EvalError::Other(format!("fanout_fn: serialize branch: {e}")))?;
        let branch_list = branches.join(", ");
        let body = format!("fn.fanout(x, {branch_list})");
        let fn_val = FunctionValue {
            params: vec![("x".to_string(), serde_json::Value::Null)],
            return_schema: None,
            body,
            patterns: Vec::new(),
            captured: Vec::new(),
        };
        Ok(serde_json::Value::from(fn_val))
    }
}

// ── converge ───────────────────────────────────────────────────────

#[derive(Clone, Copy)]
pub struct Converge;
impl Function for Converge {
    fn call(
        &self,
        args: &[serde_json::Value],
        ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        if args.len() < 3 {
            return Err(EvalError::TypeMismatch(format!(
                "expected {} args, got {}",
                3,
                args.len(),
            )));
        }
        let value = &args[0];
        let combiner = require_function_value(&args[1])?;
        let branch_count = args.len() - 2;
        let mut results = Vec::with_capacity(branch_count);
        let inner = value.clone();
        for branch_arg in &args[2..] {
            let branch_fn = require_function_value(branch_arg)?;
            let result = apply_fn(ctx, &branch_fn, &inner)?;
            results.push(result);
        }
        let combined = if results.len() == 1 {
            results.into_iter().next().unwrap()
        } else {
            let mut acc = results[0].clone();
            for item in &results[1..] {
                acc = apply_fn2(ctx, &combiner, &acc, item)?;
            }
            acc
        };
        Ok(serde_json::Value::from(combined))
    }
}

// ===========================================================================
// Control flow
// ===========================================================================

// ── choice ─────────────────────────────────────────────────────────

#[derive(Clone, Copy)]
pub struct Choice;
impl Function for Choice {
    fn call(
        &self,
        args: &[serde_json::Value],
        ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        if args.len() < 4 {
            return Err(EvalError::TypeMismatch(format!(
                "expected {} args, got {}",
                4,
                args.len(),
            )));
        }
        let value = &args[0];
        let predicate = require_function_value(&args[1])?;
        let on_true = require_function_value(&args[2])?;
        let on_false = require_function_value(&args[3])?;

        let inner = value.clone();
        let is_true = is_truthy_fn(ctx, &predicate, &inner)?;
        let branch = if is_true { &on_true } else { &on_false };
        Ok(apply_fn(ctx, branch, &inner)?)
    }
}

// ── when / unless ──────────────────────────────────────────────────

#[derive(Clone, Copy)]
pub struct When;
impl Function for When {
    fn call(
        &self,
        args: &[serde_json::Value],
        ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        if args.len() < 3 {
            return Err(EvalError::TypeMismatch(format!(
                "expected {} args, got {}",
                3,
                args.len(),
            )));
        }
        let value = &args[0];
        let predicate = require_function_value(&args[1])?;
        let transform = require_function_value(&args[2])?;
        let inner = value.clone();
        if is_truthy_fn(ctx, &predicate, &inner)? {
            Ok(apply_fn(ctx, &transform, &inner)?)
        } else {
            Ok(value.clone())
        }
    }
}

#[derive(Clone, Copy)]
pub struct Unless;
impl Function for Unless {
    fn call(
        &self,
        args: &[serde_json::Value],
        ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        if args.len() < 3 {
            return Err(EvalError::TypeMismatch(format!(
                "expected {} args, got {}",
                3,
                args.len(),
            )));
        }
        let value = &args[0];
        let predicate = require_function_value(&args[1])?;
        let transform = require_function_value(&args[2])?;
        let inner = value.clone();
        if is_truthy_fn(ctx, &predicate, &inner)? {
            Ok(value.clone())
        } else {
            Ok(apply_fn(ctx, &transform, &inner)?)
        }
    }
}

// ===========================================================================
// Pattern matching
// ===========================================================================

fn match_pattern(
    pattern: &JsonValue,
    value: &JsonValue,
    out: &mut Vec<(String, JsonValue)>,
) -> Result<bool, EvalError> {
    if let Some(obj) = pattern.as_object() {
        if let Some(type_name) = obj.get("type").and_then(|v| v.as_str()) {
            match type_name {
                "wildcard" => return Ok(true),
                "literal" => {
                    let expected = pattern.get("value").ok_or_else(|| {
                        EvalError::Other("literal pattern missing `value`".into())
                    })?;
                    return Ok(expected == value);
                }
                "identifier" => {
                    let name = pattern
                        .get("name")
                        .and_then(|v| v.as_str())
                        .ok_or_else(|| {
                            EvalError::Other("identifier pattern missing `name`".into())
                        })?;
                    out.push((name.to_string(), value.clone()));
                    return Ok(true);
                }
                "array" => {
                    let patterns = pattern
                        .get("patterns")
                        .and_then(|v| v.as_array())
                        .ok_or_else(|| {
                            EvalError::Other("array pattern missing `patterns`".into())
                        })?;
                    let arr = match value.as_array() {
                        Some(a) => a,
                        None => return Ok(false),
                    };
                    for (i, child_pattern) in patterns.iter().enumerate() {
                        let child = arr.get(i).unwrap_or(&JsonValue::Null);
                        if !match_pattern(child_pattern, child, out)? {
                            return Ok(false);
                        }
                    }
                    return Ok(true);
                }
                "object" => {
                    let entries = pattern
                        .get("entries")
                        .and_then(|v| v.as_array())
                        .ok_or_else(|| {
                            EvalError::Other("object pattern missing `entries`".into())
                        })?;
                    let obj = match value.as_object() {
                        Some(o) => o,
                        None => return Ok(false),
                    };
                    for entry in entries {
                        let arr = entry.as_array().ok_or_else(|| {
                            EvalError::Other("invalid object pattern entry".into())
                        })?;
                        let key = arr
                            .get(0)
                            .and_then(|v| v.as_str())
                            .ok_or_else(|| EvalError::Other("invalid object pattern key".into()))?;
                        let child_pattern = arr.get(1).ok_or_else(|| {
                            EvalError::Other("invalid object pattern entry".into())
                        })?;
                        let child = obj.get(key).unwrap_or(&JsonValue::Null);
                        if !match_pattern(child_pattern, child, out)? {
                            return Ok(false);
                        }
                    }
                    return Ok(true);
                }
                _ => {
                    return Err(EvalError::Other(format!(
                        "unknown pattern type: {type_name}"
                    )));
                }
            }
        }
    }
    Ok(pattern == value)
}

// ── match ───────────────────────────────────────────────────────────

#[derive(Clone, Copy)]
pub struct Match;
impl Function for Match {
    fn call(
        &self,
        args: &[serde_json::Value],
        ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        if args.len() < 2 {
            return Err(EvalError::TypeMismatch(format!(
                "expected {} args, got {}",
                2,
                args.len(),
            )));
        }
        let value = &args[0];
        for branch_arg in &args[1..] {
            let branch = branch_arg
                .as_array()
                .ok_or(EvalError::TypeMismatch(format!(
                    "expected {}, got {}",
                    "array [pattern, handler]", "non-array branch",
                )))?;
            if branch.len() < 2 {
                return Err(EvalError::TypeMismatch(format!(
                    "expected {} args, got {}",
                    2,
                    branch.len(),
                )));
            }
            let pattern = &branch[0];
            let handler = &branch[1];
            let mut bindings = Vec::new();
            if match_pattern(pattern, value, &mut bindings)? {
                let fn_val =
                    FunctionValue::from_json(handler).ok_or(EvalError::TypeMismatch(format!(
                        "expected {}, got {}",
                        "function value", "non-function branch handler",
                    )))?;
                let vars: Vec<(String, serde_json::Value)> = bindings
                    .into_iter()
                    .map(|(name, val)| (name, serde_json::Value::from(val)))
                    .collect();
                return ctx.eval_expr(&fn_val.body, &vars);
            }
        }
        Err(EvalError::Other("no matching branch".into()))
    }
}

// NOTE: ADR 0040 gap — lazy if/then/else is not yet supported by the new
// non-generic Function trait. The eager If equivalent can be added when
// lazy evaluation support is available.

// ===========================================================================
// Application
// ===========================================================================

// ── apply ──────────────────────────────────────────────────────────

#[derive(Clone, Copy)]
pub struct Apply;
impl Function for Apply {
    fn call(
        &self,
        args: &[serde_json::Value],
        ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        if args.len() < 2 {
            return Err(EvalError::TypeMismatch(format!(
                "expected {} args, got {}",
                2,
                args.len(),
            )));
        }
        let fn_val = require_function_value(&args[0])?;
        let call_args = require_array(&args[1])?;
        let vars = bind_function_params(&fn_val, call_args)?;
        Ok(ctx.eval_expr(&fn_val.body, &vars)?)
    }
}

// ── tap ────────────────────────────────────────────────────────────

#[derive(Clone, Copy)]
pub struct Tap;
impl Function for Tap {
    fn call(
        &self,
        args: &[serde_json::Value],
        ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        if args.len() < 2 {
            return Err(EvalError::TypeMismatch(format!(
                "expected {} args, got {}",
                2,
                args.len(),
            )));
        }
        let fn_val = require_function_value(&args[0])?;
        let value = &args[1];
        let inner = value.clone();
        let _ = apply_fn(ctx, &fn_val, &inner)?;
        Ok(value.clone())
    }
}

// ===========================================================================
// Collection iteration
// ===========================================================================

// ── map ────────────────────────────────────────────────────────────

#[derive(Clone, Copy)]
pub struct Map;
impl Function for Map {
    fn call(
        &self,
        args: &[serde_json::Value],
        ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        if args.len() < 2 {
            return Err(EvalError::TypeMismatch(format!(
                "expected {} args, got {}",
                2,
                args.len(),
            )));
        }
        let array = require_array(&args[1])?;
        let results = map_callable_iter(ctx, &args[0], array.iter())?;
        Ok(arr(&results))
    }
}

// ── filter ─────────────────────────────────────────────────────────

#[derive(Clone, Copy)]
pub struct Filter;
impl Function for Filter {
    fn call(
        &self,
        args: &[serde_json::Value],
        ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        if args.len() < 2 {
            return Err(EvalError::TypeMismatch(format!(
                "expected {} args, got {}",
                2,
                args.len(),
            )));
        }
        let array = require_array(&args[1])?;
        let results = filter_callable_iter(ctx, &args[0], array.iter())?;
        Ok(arr(&results))
    }
}

// ── reduce ─────────────────────────────────────────────────────────

#[derive(Clone, Copy)]
pub struct Reduce;
impl Function for Reduce {
    fn call(
        &self,
        args: &[serde_json::Value],
        ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        if args.len() < 3 {
            return Err(EvalError::TypeMismatch(format!(
                "expected {} args, got {}",
                3,
                args.len(),
            )));
        }
        let array = require_array(&args[1])?;
        let init = args[2].clone();
        let result = fold_callable_iter(ctx, &args[0], array.iter(), init)?;
        Ok(serde_json::Value::from(result))
    }
}

// ── flat_map ───────────────────────────────────────────────────────

#[derive(Clone, Copy)]
pub struct FlatMap;
impl Function for FlatMap {
    fn call(
        &self,
        args: &[serde_json::Value],
        ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        let (fn_val, array) = require_function_and_array(args)?;
        let mapped = map_iter(ctx, &fn_val, array.iter())?;
        let mut results = Vec::new();
        for item in mapped {
            if let Some(sub) = item.as_array() {
                results.extend(sub.iter().cloned());
            } else {
                results.push(item);
            }
        }
        Ok(arr(&results))
    }
}

// ── find ───────────────────────────────────────────────────────────

#[derive(Clone, Copy)]
pub struct Find;
impl Function for Find {
    fn call(
        &self,
        args: &[serde_json::Value],
        ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        let (fn_val, array) = require_function_and_array(args)?;
        let result = find_first(ctx, &fn_val, array.iter())?;
        match result {
            Some(v) => Ok(serde_json::Value::from(v)),
            None => Ok(serde_json::Value::from(serde_json::Value::Null)),
        }
    }
}

// ── some / every ───────────────────────────────────────────────────

#[derive(Clone, Copy)]
pub struct SomeFn;
impl Function for SomeFn {
    fn call(
        &self,
        args: &[serde_json::Value],
        ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        let (fn_val, array) = require_function_and_array(args)?;
        for item in array {
            if is_truthy_fn(ctx, &fn_val, item)? {
                return Ok(b(true));
            }
        }
        Ok(b(false))
    }
}

#[derive(Clone, Copy)]
pub struct Every;
impl Function for Every {
    fn call(
        &self,
        args: &[serde_json::Value],
        ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        let (fn_val, array) = require_function_and_array(args)?;
        for item in array {
            if !is_truthy_fn(ctx, &fn_val, item)? {
                return Ok(b(false));
            }
        }
        Ok(b(true))
    }
}

// ── group_by ───────────────────────────────────────────────────────

#[derive(Clone, Copy)]
pub struct GroupBy;
impl Function for GroupBy {
    fn call(
        &self,
        args: &[serde_json::Value],
        ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        let (fn_val, array) = require_function_and_array(args)?;
        let mut groups: std::collections::BTreeMap<String, Vec<serde_json::Value>> =
            std::collections::BTreeMap::new();
        for item in array {
            let key = apply_fn(ctx, &fn_val, item)?;
            let key_str = key_to_string(&key);
            groups.entry(key_str).or_default().push(item.clone());
        }
        let mut result = serde_json::Map::new();
        for (k, v) in groups {
            result.insert(k, serde_json::Value::Array(v));
        }
        Ok(serde_json::Value::from(serde_json::Value::Object(result)))
    }
}

// ── partition ──────────────────────────────────────────────────────

#[derive(Clone, Copy)]
pub struct Partition;
impl Function for Partition {
    fn call(
        &self,
        args: &[serde_json::Value],
        ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        let (fn_val, array) = require_function_and_array(args)?;
        let mut matching = Vec::new();
        let mut rest = Vec::new();
        for item in array {
            if is_truthy_fn(ctx, &fn_val, item)? {
                matching.push(item.clone());
            } else {
                rest.push(item.clone());
            }
        }
        Ok(arr(&[
            serde_json::Value::Array(matching),
            serde_json::Value::Array(rest),
        ]))
    }
}

// ── count_by ───────────────────────────────────────────────────────

#[derive(Clone, Copy)]
pub struct CountBy;
impl Function for CountBy {
    fn call(
        &self,
        args: &[serde_json::Value],
        ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        let (fn_val, array) = require_function_and_array(args)?;
        let mut counts: std::collections::BTreeMap<String, f64> = std::collections::BTreeMap::new();
        for item in array {
            let key = apply_fn(ctx, &fn_val, item)?;
            let key_str = key_to_string(&key);
            *counts.entry(key_str).or_insert(0.0) += 1.0;
        }
        let mut result = serde_json::Map::new();
        for (k, v) in counts {
            result.insert(k, serde_json::json!(v));
        }
        Ok(serde_json::Value::from(serde_json::Value::Object(result)))
    }
}

// ===========================================================================
// Function manipulation
// ===========================================================================

// ── constantly ─────────────────────────────────────────────────────

#[derive(Clone, Copy)]
pub struct Constantly;
impl Function for Constantly {
    fn call(
        &self,
        args: &[serde_json::Value],
        _ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        let value = args.first().ok_or(EvalError::TypeMismatch(format!(
            "expected {} args, got {}",
            1, 0,
        )))?;
        let captured = value.clone();
        let fn_val = FunctionValue {
            params: vec![("_".to_string(), serde_json::Value::Null)],
            return_schema: None,
            body: serde_json::to_string(&captured).unwrap_or_else(|_| "null".to_string()),
            patterns: Vec::new(),
            captured: Vec::new(),
        };
        Ok(serde_json::Value::from(fn_val))
    }
}

// ── flip ───────────────────────────────────────────────────────────

#[derive(Clone, Copy)]
pub struct Flip;
impl Function for Flip {
    fn call(
        &self,
        args: &[serde_json::Value],
        _ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        let fn_val = require_function_value(args.first().ok_or(EvalError::TypeMismatch(
            format!("expected {} args, got {}", 1, 0,),
        ))?)?;
        if fn_val.params.len() < 2 {
            return Err(EvalError::TypeMismatch(format!(
                "expected {}, got {}",
                "function with at least 2 parameters", "function with fewer than 2 parameters",
            )));
        }
        let mut swapped_params = fn_val.params.clone();
        swapped_params.swap(0, 1);
        let flipped = FunctionValue {
            params: swapped_params,
            return_schema: None,
            body: fn_val.body.clone(),
            patterns: Vec::new(),
            captured: Vec::new(),
        };
        Ok(serde_json::Value::from(flipped))
    }
}

// ── partial ────────────────────────────────────────────────────────

#[derive(Clone, Copy)]
pub struct Partial;
impl Function for Partial {
    fn call(
        &self,
        args: &[serde_json::Value],
        _ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        if args.len() < 2 {
            return Err(EvalError::TypeMismatch(format!(
                "expected {} args, got {}",
                2,
                args.len(),
            )));
        }
        let fn_val = require_function_value(&args[0])?;
        let bound_args = require_array(&args[1])?;
        let bound_count = bound_args.len().min(fn_val.params.len());
        if bound_count == 0 {
            return Ok(serde_json::Value::from(fn_val));
        }
        let remaining_params: Vec<(String, serde_json::Value)> = fn_val.params[bound_count..]
            .iter()
            .map(|(name, schema)| (name.clone(), schema.clone()))
            .collect();
        let mut body = fn_val.body.clone();
        for i in 0..bound_count {
            let param_name = &fn_val.params[i].0;
            let replacement =
                serde_json::to_string(&bound_args[i]).unwrap_or_else(|_| "null".to_string());
            body = substitute_param(&body, param_name, &replacement);
        }
        let partial_fn = FunctionValue {
            params: remaining_params,
            return_schema: None,
            body,
            patterns: Vec::new(),
            captured: Vec::new(),
        };
        Ok(serde_json::Value::from(partial_fn))
    }
}

use handl_plugin_lib_handl::OpRegistry;
use std::sync::Arc;

pub const COMBINATORS_OPS: &[&str] = &[
    "combinators.pipe",
    "combinators.flow",
    "combinators.compose",
    "combinators.fanout",
    "combinators.fanout_fn",
    "combinators.choice",
    "combinators.apply",
    "combinators.flat_map",
    "combinators.find",
    "combinators.some",
    "combinators.every",
    "combinators.group_by",
    "combinators.partition",
    "combinators.count_by",
    "combinators.tap",
    "combinators.match",
    "combinators.constantly",
    "combinators.flip",
    "combinators.partial",
    "combinators.when",
    "combinators.unless",
    "combinators.converge",
];

pub fn combinators_op_registry() -> OpRegistry {
    let mut registry = OpRegistry::new();
    registry.register("combinators.pipe", Arc::new(Pipe));
    registry.register("combinators.flow", Arc::new(Flow));
    registry.register("combinators.compose", Arc::new(Compose));
    registry.register("combinators.fanout", Arc::new(Fanout));
    registry.register("combinators.fanout_fn", Arc::new(FanoutFn));
    registry.register("combinators.choice", Arc::new(Choice));
    registry.register("combinators.apply", Arc::new(Apply));
    registry.register("combinators.flat_map", Arc::new(FlatMap));
    registry.register("combinators.find", Arc::new(Find));
    registry.register("combinators.some", Arc::new(SomeFn));
    registry.register("combinators.every", Arc::new(Every));
    registry.register("combinators.group_by", Arc::new(GroupBy));
    registry.register("combinators.partition", Arc::new(Partition));
    registry.register("combinators.count_by", Arc::new(CountBy));
    registry.register("combinators.tap", Arc::new(Tap));
    registry.register("combinators.match", Arc::new(Match));
    registry.register("combinators.constantly", Arc::new(Constantly));
    registry.register("combinators.flip", Arc::new(Flip));
    registry.register("combinators.partial", Arc::new(Partial));
    registry.register("combinators.when", Arc::new(When));
    registry.register("combinators.unless", Arc::new(Unless));
    registry.register("combinators.converge", Arc::new(Converge));
    registry
}

pub const TRANSFORM_OPS: &[&str] = &["transform.map", "transform.filter", "transform.reduce"];

pub fn transform_op_registry() -> OpRegistry {
    let mut registry = OpRegistry::new();
    registry.register("transform.map", Arc::new(Map));
    registry.register("transform.filter", Arc::new(Filter));
    registry.register("transform.reduce", Arc::new(Reduce));
    registry
}
