//! Pure-data interpreter for the arrow-calculus `Term` kernel.
//!
//! This is a proof-of-concept evaluator for lowered `Term` graphs. It returns
//! `Err` for any construct it does not (yet) handle, which lets callers fall
//! back to the existing AST eval engine.

use std::collections::HashMap;

use handl_value::{TaggedValue, tagged_to_value};
use serde_json::{Map, Number, Value, from_value};

use crate::{ArrSource, Term};

/// Interpret a `Term` as an arrow from `input` to a result value.
///
/// Returns `Err` for unsupported `Term` variants or operator names, which is
/// the signal to fall back to another evaluator.
pub fn interpret(term: &Term, input: Value) -> Result<Value, String> {
    interpret_with_handlers(term, input, &HashMap::new())
}

/// Interpret a `Term` with an active handler map.
///
/// `handlers` maps capability/grade names to handler record values. It is used
/// by `Term::Handle` to install handlers and by `Term::Op` to dispatch graded
/// operations.
pub fn interpret_with_handlers(
    term: &Term,
    input: Value,
    handlers: &HashMap<String, Value>,
) -> Result<Value, String> {
    match term {
        Term::Arr { dim: _, value } | Term::Const { value } => Ok(value.clone()),

        Term::Seq { axis, fst, snd } => {
            // ADR-0120 Phase 5: `Seq{axis: k}` is `∘ₖ` — composition
            // along the k-th globular axis. Axis 0 on 1-cells (`dim ≤ 1`)
            // is sequential composition; `k < dim` pastes n-cells along
            // the k-boundary at the value level (∘₀ horizontal, ∘₁
            // vertical, …) — both operands see the same input.
            let k = seq_axis_index(axis, &input, handlers)?;
            let d = term_dim(fst);
            if k == 0 && d <= 1 {
                let v = interpret_with_handlers(fst, input, handlers)?;
                interpret_with_handlers(snd, v, handlers)
            } else {
                // Globular pasting: both operands evaluate against the
                // same input, and the *effective* dimension is the
                // greater of the declared term dimension and the
                // evaluated values' cell dimensions — a `Cell`/`__dim__`
                // record pastes at its own height, so `>>>[2]` runs on
                // 3-cell values through the dimension-2 surface scheme.
                let a = interpret_with_handlers(fst, input.clone(), handlers)?;
                let b = interpret_with_handlers(snd, input, handlers)?;
                cell_comp_axis(k, d, &a, &b)
            }
        }

        Term::First { inner } => {
            let (a, b) = pair_components(&input)?;
            let v = interpret_with_handlers(inner, a, handlers)?;
            Ok(mk_pair(v, b))
        }

        Term::Choice { l, r } => {
            let (side, value) = either_side(input)?;
            if side == "left" {
                interpret_with_handlers(l, value, handlers)
            } else {
                interpret_with_handlers(r, value, handlers)
            }
        }

        Term::Loop { body } => {
            let mut state = Value::Null;
            for _ in 0..10_000 {
                let pair = mk_pair(input.clone(), state);
                let out = interpret_with_handlers(body, pair, handlers)?;

                if let Some(v) = either_left_value(&out) {
                    return Ok(v);
                }

                if let Some(v) = either_right_value(&out) {
                    state = v;
                    continue;
                }

                // A plain pair is treated as (result, next-state) and terminates.
                if let Ok((fst, _snd)) = pair_components(&out) {
                    return Ok(fst);
                }

                // Anything else is treated as the final result for a simple
                // non-nested loop; this is a conservative fallback.
                return Ok(out);
            }
            Err("Loop: exceeded max iterations".to_string())
        }

        Term::App { callee, args } => {
            let arg_vals: Vec<Value> = args
                .iter()
                .map(|a| interpret_with_handlers(a, input.clone(), handlers))
                .collect::<Result<_, _>>()?;
            let arg_input = if arg_vals.len() == 1 {
                arg_vals.into_iter().next().unwrap()
            } else {
                Value::Array(arg_vals)
            };

            let callee_val = interpret_with_handlers(callee, input, handlers)?;

            // Bound-arrow record `{"__term__": <Term>, "__bound__": [v..]}`:
            // a frozen partial application — `__term__` runs on the
            // concatenation of `__bound__` and this call's arguments.
            if let Some(obj) = callee_val.as_object() {
                if let (Some(term_val), Some(Value::Array(bound))) =
                    (obj.get("__term__"), obj.get("__bound__"))
                {
                    if let Ok(scheme) = from_value::<Term>(term_val.clone()) {
                        let mut full_input = bound.clone();
                        match arg_input {
                            Value::Array(vals) => full_input.extend(vals),
                            v => full_input.push(v),
                        }
                        return interpret_with_handlers(
                            &scheme,
                            Value::Array(full_input),
                            handlers,
                        );
                    }
                }
            }

            // If the callee evaluates to a `Term` value, run it.
            if let Ok(scheme) = from_value::<Term>(callee_val.clone()) {
                return interpret_with_handlers(&scheme, arg_input, handlers);
            }

            // String callees are host-function names; the small interpreter
            // has no registry, so report it clearly.
            if callee_val.as_str().is_some() {
                return Err("App: host-function callees are not supported".to_string());
            }

            Err(format!("App: callee is not an arrow value: {callee_val}"))
        }

        Term::Handle {
            body,
            target,
            impl_,
        } => {
            let handler_val = interpret_with_handlers(impl_, Value::Null, handlers)?;
            let mut handlers = handlers.clone();
            handlers.insert(target.clone(), handler_val);
            interpret_with_handlers(body, input, &handlers)
        }

        Term::Op {
            dim,
            name,
            args,
            source,
            lit,
        } => eval_op(name, dim, args, source, lit.as_ref(), input, handlers),

        other => Err(format!("unsupported Term: {other:?}")),
    }
}

/// Resolve a `Seq` axis slot to its concrete axis index.
///
/// Literal axes (`Const n`/`Arr n`) resolve directly; compound axis terms
/// are evaluated as expressions against the incoming value. A non-numeric
/// result is a structural error — the axis is a natural-number position.
fn seq_axis_index(
    axis: &Term,
    input: &Value,
    handlers: &HashMap<String, Value>,
) -> Result<u64, String> {
    if let Some(k) = axis.nat_literal() {
        return Ok(k);
    }
    let v = interpret_with_handlers(axis, input.clone(), handlers)?;
    v.as_u64()
        .ok_or_else(|| format!("Seq: axis expression evaluated to a non-natural value: {v}"))
}

/// The globular dimension of a term (ADR-0120 Phase 5) — delegates to
/// [`Term::globular_dim`], the shared implementation. `Seq{axis: k}`
/// pastes along axis `k` only when `k < term_dim(fst)`.
fn term_dim(t: &Term) -> u64 {
    t.globular_dim()
}

/// Axis-`k` composition of n-cells at the JSON value level (ADR-0120).
/// Delegates to [`handl_value::cell_comp_axis`] — the single
/// implementation of the globular pasting law — via the `TaggedValue`
/// bridge. `declared_dim` is the operands' declared (term-level)
/// dimension; the effective dimension also lifts to the values' own
/// `cell_dim`, so `Cell`/`__dim__` records paste at their own height.
fn cell_comp_axis(axis: u64, declared_dim: u64, a: &Value, b: &Value) -> Result<Value, String> {
    let av = TaggedValue::from(a.clone());
    let bv = TaggedValue::from(b.clone());
    handl_value::cell_comp_axis(axis, declared_dim, &av, &bv).map(|v| tagged_to_value(&v))
}

/// `compose(diagram)` — generalized pasting/Kan filling (ADR-0120) at
/// the JSON value level; delegates to [`handl_value::cell_compose`].
fn cell_compose(diagram: &Value) -> Result<Value, String> {
    handl_value::cell_compose(&TaggedValue::from(diagram.clone())).map(|v| tagged_to_value(&v))
}

/// The declared operand dimension baked into a compiled
/// `cell_comp_axis[:N]` op name (the legacy `cell2_comp_axis[:N]`
/// spelling is accepted too). Bare `cell_comp_axis`/`cell2_comp_axis`
/// declare dimension 2 — the `>>>[k]` surface lift.
fn cell_axis_op_dim(name: &str) -> Option<u64> {
    for prefix in ["cell_comp_axis", "cell2_comp_axis"] {
        if name == prefix {
            return Some(2);
        }
        if let Some(suffix) = name.strip_prefix(prefix).and_then(|s| s.strip_prefix(':')) {
            return suffix.parse::<u64>().ok().map(|d| d.max(1));
        }
    }
    None
}

fn eval_op(
    name: &str,
    dim: &Term,
    args: &[Term],
    source: &ArrSource,
    lit: Option<&Value>,
    input: Value,
    handlers: &HashMap<String, Value>,
) -> Result<Value, String> {
    match name {
        "id" => Ok(input),

        "elem" => {
            let idx =
                lit.and_then(Value::as_u64)
                    .ok_or_else(|| "elem: missing integer literal")? as usize;
            input
                .as_array()
                .and_then(|a| a.get(idx).cloned())
                .ok_or_else(|| "elem: index out of bounds".into())
        }

        "eq" => {
            if args.len() != 2 {
                return Err("eq: expected two arguments".into());
            }
            let l = interpret_with_handlers(&args[0], input.clone(), handlers)?;
            let r = interpret_with_handlers(&args[1], input.clone(), handlers)?;
            // `handl_value::eq` — the same equality the exec engines'
            // `eq` op applies: cross-numeric (`Int(1) == Float(1.0)`),
            // unordered objects, and tagged-variant markers decoded.
            // Raw `serde_json` equality would split `1` from `1.0`.
            Ok(Value::Bool(handl_value::eq(
                &TaggedValue::from(l),
                &TaggedValue::from(r),
            )))
        }

        "gt" | "gte" | "lt" | "lte" => {
            if args.len() != 2 {
                return Err(format!("{name}: expected two arguments"));
            }
            let l = interpret_with_handlers(&args[0], input.clone(), handlers)?;
            let r = interpret_with_handlers(&args[1], input.clone(), handlers)?;
            let l = l
                .as_f64()
                .ok_or_else(|| format!("{name}: non-numeric argument"))?;
            let r = r
                .as_f64()
                .ok_or_else(|| format!("{name}: non-numeric argument"))?;
            let result = match name {
                "gt" => l > r,
                "gte" => l >= r,
                "lt" => l < r,
                "lte" => l <= r,
                _ => unreachable!(),
            };
            Ok(Value::Bool(result))
        }

        "and" | "or" => {
            if args.is_empty() {
                return Err(format!("{name}: expected at least one argument"));
            }
            let mut iter = args.iter();
            let first = interpret_with_handlers(iter.next().unwrap(), input.clone(), handlers)?;
            let mut acc = is_truthy(&first);
            for arg in iter {
                let v = interpret_with_handlers(arg, input.clone(), handlers)?;
                match name {
                    "and" => acc = acc && is_truthy(&v),
                    "or" => acc = acc || is_truthy(&v),
                    _ => unreachable!(),
                }
            }
            Ok(Value::Bool(acc))
        }

        "add" | "mul" | "sub" | "div" => {
            if args.is_empty() {
                return Err("math op: no arguments".into());
            }
            let mut values = Vec::with_capacity(args.len());
            for arg in args {
                values.push(interpret_with_handlers(arg, input.clone(), handlers)?);
            }
            // Mirror the exec engines' `Num` arithmetic
            // (`plugin-engine-exec`'s `Num::{Add,Sub,Mul,Div}` and the
            // `div` op's zero-divisor error): all-integer operands stay
            // in i64 — including *integer division* — while any Float
            // operand promotes the whole fold to f64, and a float result
            // keeps its Float repr even when whole. The previous
            // f64-fold-then-truncate disagreed with the engines on both
            // counts (`7 / 2` → `3.5` vs `3`; `2.5 + 0.5` → `3` vs `3.0`).
            if values.iter().all(|v| v.as_i64().is_some()) {
                let mut iter = values.into_iter();
                let mut result = iter.next().unwrap().as_i64().unwrap();
                for v in iter {
                    let n = v.as_i64().unwrap();
                    match name {
                        "add" => result += n,
                        "mul" => result *= n,
                        "sub" => result -= n,
                        "div" => {
                            if n == 0 {
                                return Err("div: division by zero".into());
                            }
                            result /= n;
                        }
                        _ => unreachable!(),
                    }
                }
                return Ok(Value::Number(Number::from(result)));
            }
            let mut iter = values.into_iter();
            let first = iter.next().unwrap();
            let mut result = first
                .as_f64()
                .ok_or_else(|| format!("{name}: non-numeric argument"))?;
            for v in iter {
                let n = v
                    .as_f64()
                    .ok_or_else(|| format!("{name}: non-numeric argument"))?;
                match name {
                    "add" => result += n,
                    "mul" => result *= n,
                    "sub" => result -= n,
                    "div" => {
                        if n == 0.0 {
                            return Err("div: division by zero".into());
                        }
                        result /= n;
                    }
                    _ => unreachable!(),
                }
            }
            Number::from_f64(result)
                .map(Value::Number)
                .ok_or_else(|| format!("{name}: invalid numeric result"))
        }

        "json" => {
            // ADR-0060 template substitution: args evaluate to values that
            // replace `$i` holes in the template literal, then the result
            // string parses as JSON.
            let template = lit
                .and_then(Value::as_str)
                .ok_or_else(|| "json: missing template literal".to_string())?;
            let mut s = template.to_string();
            for (i, arg) in args.iter().enumerate() {
                let v = interpret_with_handlers(arg, input.clone(), handlers)?;
                let replacement =
                    serde_json::to_string(&v).map_err(|e| format!("json: serialize arg: {e}"))?;
                s = s.replace(&format!("${i}"), &replacement);
            }
            serde_json::from_str::<Value>(&s).map_err(|e| format!("json: parse error: {e}"))
        }

        // `product`/`fanout`/`array` all produce plain arrays here —
        // internal dispatch pairs (`product`) are consumed by `elem`
        // indexing, which requires the `[a, b]` shape. NOTE: this makes
        // a lowered `***` serialize as `[a, b]` while the exec engines'
        // `product` op yields `TaggedValue::Pair` → `{"__pair__": [a, b]}`
        // — a known interpreter↔engine representation gap, pinned in
        // `handl-runtime/tests/engine_parity.rs`.
        "product" | "fn.fanout_fn" | "fanout" | "array" => {
            let mut out = Vec::with_capacity(args.len());
            for arg in args {
                out.push(interpret_with_handlers(arg, input.clone(), handlers)?);
            }
            Ok(Value::Array(out))
        }

        // `concat` — array concatenation, the lowering of spread elements:
        // `[a, ...xs, b]` folds to `concat(concat([a], xs), [b])`. Operands
        // evaluate against the incoming value like `array`'s; a non-array
        // operand is pushed as-is, mirroring the AST `array` op's
        // `...expr` rule (`pattern_match`'s rest-role flattening).
        "concat" => {
            let mut out = Vec::new();
            for arg in args {
                match interpret_with_handlers(arg, input.clone(), handlers)? {
                    Value::Array(xs) => out.extend(xs),
                    other => out.push(other),
                }
            }
            Ok(Value::Array(out))
        }

        // `record_merge` — object concatenation, the lowering of spread
        // entries: `{a: 1, ...o, b: 2}` folds to
        // `record_merge(record_merge({a: 1}, o), {b: 2})`. Later keys win
        // and a non-object operand is ignored, mirroring the AST
        // `object` op's `...expr` rule.
        "record_merge" => {
            let mut out = Map::new();
            for arg in args {
                if let Value::Object(m) = interpret_with_handlers(arg, input.clone(), handlers)? {
                    for (k, v) in m {
                        out.insert(k, v);
                    }
                }
            }
            Ok(Value::Object(out))
        }

        "record" => {
            let mut obj = Map::new();
            if let Some(keys) = lit.and_then(Value::as_array) {
                // Compiled form: `lit` carries the key list and `args`
                // the values (same length).
                if keys.len() != args.len() {
                    return Err("record: key/value count mismatch".into());
                }
                for (i, arg) in args.iter().enumerate() {
                    let key = keys[i]
                        .as_str()
                        .ok_or_else(|| "record: key is not a string")?;
                    obj.insert(
                        key.to_string(),
                        interpret_with_handlers(arg, input.clone(), handlers)?,
                    );
                }
            } else {
                // Scheme form (the tree-walk native op's shape): `args`
                // alternate key-expr, value-expr pairs.
                if args.len() % 2 != 0 {
                    return Err(format!(
                        "record: expected even number of arguments, got {}",
                        args.len()
                    ));
                }
                for i in (0..args.len()).step_by(2) {
                    let key = interpret_with_handlers(&args[i], input.clone(), handlers)?
                        .as_str()
                        .map(str::to_string)
                        .ok_or_else(|| format!("record: key at index {i} must be a string"))?;
                    obj.insert(
                        key,
                        interpret_with_handlers(&args[i + 1], input.clone(), handlers)?,
                    );
                }
            }
            Ok(Value::Object(obj))
        }

        "tag.construct" => {
            // `tag.construct(tag, record)` stamps `__tag__` onto a record —
            // the `Arrow`/`Cell2`/law record constructors share this op.
            if args.len() != 2 {
                return Err(format!(
                    "tag.construct: expected 2 arguments, got {}",
                    args.len()
                ));
            }
            let tag = interpret_with_handlers(&args[0], input.clone(), handlers)?
                .as_str()
                .map(str::to_string)
                .ok_or_else(|| "tag.construct: tag must be a string".to_string())?;
            let mut obj = match interpret_with_handlers(&args[1], input, handlers)? {
                Value::Object(m) => m,
                _ => Map::new(),
            };
            obj.insert("__tag__".into(), Value::from(tag));
            Ok(Value::Object(obj))
        }

        "field_access" => {
            let target = args.first().ok_or_else(|| "field_access: missing target")?;
            let v = interpret_with_handlers(target, input.clone(), handlers)?;
            match lit {
                Some(Value::Number(n)) if n.is_u64() => {
                    let idx = n.as_u64().unwrap() as usize;
                    v.as_array()
                        .and_then(|a| a.get(idx).cloned())
                        .ok_or_else(|| "field_access: index out of bounds".into())
                }
                Some(Value::String(s)) => v
                    .get(s)
                    .cloned()
                    .ok_or_else(|| format!("field_access: no field {s}")),
                // Computed index — `a[expr]` lowers to a second arg
                // evaluated on the input (the `lower_field_access`
                // dynamic-key form).
                None if args.len() >= 2 => {
                    let key = interpret_with_handlers(&args[1], input, handlers)?;
                    match &key {
                        Value::Number(n) if n.is_u64() => v
                            .as_array()
                            .and_then(|a| a.get(n.as_u64().unwrap() as usize).cloned())
                            .ok_or_else(|| "field_access: index out of bounds".into()),
                        Value::String(s) => v
                            .get(s.as_str())
                            .cloned()
                            .ok_or_else(|| format!("field_access: no field {s}")),
                        _ => Err("field_access: computed key is not a string/number".into()),
                    }
                }
                _ => Err("field_access: missing/unsupported field literal".into()),
            }
        }

        "tag" => {
            let side = if is_truthy(&input) { "left" } else { "right" };
            let mut obj = Map::new();
            obj.insert("__either__".to_string(), Value::String(side.to_string()));
            obj.insert("value".to_string(), input);
            Ok(Value::Object(obj))
        }

        // `pair_tag` — `if` lowering: the input is a pair `[cond, v]`; the
        // output is `left(v)` when `cond` is truthy, `right(v)` otherwise,
        // so `Choice(then, else)` branches see the original input `v`,
        // not the condition result.
        "pair_tag" => {
            let (cond, v) = pair_components(&input)?;
            let side = if is_truthy(&cond) { "left" } else { "right" };
            let mut obj = Map::new();
            obj.insert("__either__".to_string(), Value::String(side.to_string()));
            obj.insert("value".to_string(), v);
            Ok(Value::Object(obj))
        }

        // `loop_outcome` — the `while` fold's result mapping (the arrow-
        // lowering counterpart of `loop_step_outcome` in
        // `plugin-engine-exec`): `{state: v}` → `right(v)` (continue),
        // `{out: v}` → `left(v)` (terminate), anything else → `left(v)`.
        "loop_outcome" => {
            if let Some(obj) = input.as_object() {
                if let Some(st) = obj.get("state") {
                    let mut e = Map::new();
                    e.insert("__either__".to_string(), Value::from("right"));
                    e.insert("value".to_string(), st.clone());
                    return Ok(Value::Object(e));
                }
            }
            let v = input
                .as_object()
                .and_then(|o| o.get("out").cloned())
                .unwrap_or(input);
            let mut e = Map::new();
            e.insert("__either__".to_string(), Value::from("left"));
            e.insert("value".to_string(), v);
            Ok(Value::Object(e))
        }

        // `arr_len` — array length; `-1` on non-arrays so `match` pattern
        // discriminants fall through to the next arm instead of erroring.
        "arr_len" => Ok(match input.as_array() {
            Some(a) => Value::from(a.len() as i64),
            None => Value::from(-1),
        }),

        // `arr_drop` — `sv[lit..]` (the `[h, …t]` rest binder's tail).
        "arr_drop" => {
            let n = lit.and_then(Value::as_u64).unwrap_or(0) as usize;
            match input.as_array() {
                Some(a) => Ok(Value::Array(a.iter().skip(n).cloned().collect())),
                None => Err("arr_drop: input is not an array".into()),
            }
        }

        // --- `match` pattern predicates (arrow-lowered `try_pattern`) ----
        // These mirror `pattern_match::try_pattern`'s shape tests. They
        // are *total* (a non-object input reports false, never an error)
        // so a non-matching scrutinee falls through to the next arm —
        // the `arr_len` → `-1` convention, extended to objects.
        "is_obj" => Ok(Value::Bool(input.is_object())),

        // `has_field[:k]` — the input is an object *and* carries key `k`.
        "has_field" => {
            let key = lit
                .and_then(Value::as_str)
                .ok_or_else(|| "has_field: missing key literal")?;
            Ok(Value::Bool(
                input.as_object().map(|o| o.contains_key(key)) == Some(true),
            ))
        }

        // `tag_fields` — the tag-pattern binders' payload source
        // (ADR-0077): the input object's non-`__tag__` values, sorted by
        // key — positional binding mirrors `try_tag_pattern`'s
        // `payload_fields`. Only consulted by binder paths behind a
        // `has_field "__tag__"` guard, so a non-object input errors.
        "tag_fields" => {
            let obj = input
                .as_object()
                .ok_or_else(|| "tag_fields: input is not an object")?;
            let mut fields: Vec<(&String, &Value)> = obj
                .iter()
                .filter(|(k, _)| k.as_str() != "__tag__")
                .collect();
            fields.sort_by(|a, b| a.0.cmp(b.0));
            Ok(Value::Array(
                fields.into_iter().map(|(_, v)| v.clone()).collect(),
            ))
        }

        // `obj_except[:keys]` — the object-pattern `...rest` binder's
        // payload: the input object minus the listed (matched) keys.
        // Evaluated lazily from an arm body, so a non-object input errors.
        "obj_except" => {
            let keys = lit
                .and_then(Value::as_array)
                .ok_or_else(|| "obj_except: missing keys literal")?;
            let obj = input
                .as_object()
                .ok_or_else(|| "obj_except: input is not an object")?;
            let mut out = Map::new();
            for (k, v) in obj {
                if !keys.iter().any(|k2| k2.as_str() == Some(k.as_str())) {
                    out.insert(k.clone(), v.clone());
                }
            }
            Ok(Value::Object(out))
        }

        // `match_fail` — the `match` lowering's exhaust fallthrough;
        // mirrors `match_shell`'s "no arm matched".
        "match_fail" => Err("match: no arm matched".into()),

        // `truthy` — coerce the incoming value to a strict `Bool` (the
        // `&&`/`||` schemes' RHS arm; mirrors the `native_ops` op).
        "truthy" => Ok(Value::Bool(is_truthy(&input))),

        "assert" => {
            Err("assert: keyword assertions are not supported by the arrow interpreter".into())
        }

        other => {
            // Dimension-typed handler dispatch (ADR-0120 Phase 3): the
            // routing boundary is the op's *evaluated* `dim` — a named
            // dimension `Const "S"` IS a grade. Fallback order keeps
            // legacy shapes working: the host boundary `Foreign(name)`
            // is a boundary key too (module-registry name), and a bare
            // op name is its own dimension-1 label.
            let foreign_name = match source {
                ArrSource::Foreign(n) => Some(n.as_str()),
                _ => None,
            };
            let dim_label = dim.dim_label();
            let labels = [dim_label.as_deref(), foreign_name, Some(other)];
            for label in labels.into_iter().flatten() {
                if let Some(handler) = handlers.get(label) {
                    let impl_entry = handler
                        .get("impls")
                        .and_then(|impls| impls.get(other))
                        .or_else(|| handler.get(other));
                    if let Some(op) = impl_entry {
                        let scheme: Term = from_value(op.clone())
                            .map_err(|_| format!("op {other}: invalid handler arrow"))?;
                        return interpret_with_handlers(&scheme, input, handlers);
                    }
                }
            }
            // Calculus ops (ADR-0120) — the same ops `native_ops` shares
            // with the exec backends, consulted *after* handler dispatch
            // so a pushed handler may still override the name.
            //
            // `compose(diagram)`: generalized pasting/Kan filling — the
            // n-ary `Seq{axis}`. The diagram is an array of
            // `{axis, cell}` steps (a bare cell is axis 0); with no args
            // the incoming value is the diagram.
            if other == "compose" {
                let diagram = match args.len() {
                    0 => input,
                    1 => interpret_with_handlers(&args[0], input, handlers)?,
                    _ => {
                        let mut steps = Vec::with_capacity(args.len());
                        for arg in args {
                            steps.push(interpret_with_handlers(arg, input.clone(), handlers)?);
                        }
                        Value::Array(steps)
                    }
                };
                return cell_compose(&diagram);
            }
            // `cell_comp_axis[:N]` (legacy `cell2_comp_axis[:N]`) — the
            // compiled backends' lowering of `Seq{axis}` pasting:
            // `[axis, fst, snd]` on the same input, `N` the declared dim.
            if let Some(declared) = cell_axis_op_dim(other) {
                if args.len() != 3 {
                    return Err(format!(
                        "{other}: expected 3 arguments (axis, fst, snd), got {}",
                        args.len()
                    ));
                }
                let axis_val = interpret_with_handlers(&args[0], input.clone(), handlers)?;
                let k = axis_val
                    .as_u64()
                    .ok_or_else(|| format!("{other}: axis evaluated to a non-natural value"))?;
                let a = interpret_with_handlers(&args[1], input.clone(), handlers)?;
                let b = interpret_with_handlers(&args[2], input, handlers)?;
                return cell_comp_axis(k, declared, &a, &b);
            }
            // No handler: the `Err` doubles as the caller's fall-back
            // signal, so it carries the diagnostic text itself.
            match (dim_label, foreign_name) {
                (Some(d), _) => Err(format!("no handler for op {other} at dimension {d}")),
                (None, Some(n)) => Err(format!("no handler for op {other} at boundary {n}")),
                (None, None) => Err(format!("unsupported op: {other}")),
            }
        }
    }
}

fn pair_components(value: &Value) -> Result<(Value, Value), String> {
    if let Some(arr) = value.as_array() {
        if arr.len() == 2 {
            return Ok((arr[0].clone(), arr[1].clone()));
        }
    }
    if let Some(obj) = value.as_object() {
        if let Some(pair) = obj.get("__pair__").and_then(Value::as_array) {
            if pair.len() == 2 {
                return Ok((pair[0].clone(), pair[1].clone()));
            }
        }
    }
    Err("expected a pair (array of length 2 or __pair__)".to_string())
}

fn mk_pair(a: Value, b: Value) -> Value {
    Value::Array(vec![a, b])
}

fn either_side(value: Value) -> Result<(&'static str, Value), String> {
    if let Some(obj) = value.as_object() {
        if let Some(side) = obj.get("__either__").and_then(Value::as_str) {
            let inner = obj
                .get("value")
                .cloned()
                .ok_or_else(|| "Either: missing value")?;
            return match side {
                "left" => Ok(("left", inner)),
                "right" => Ok(("right", inner)),
                _ => Err(format!("Either: unknown side {side}")),
            };
        }
        if let Some(side) = obj.get("__tag__").and_then(Value::as_str) {
            let inner = obj.get("value").cloned().unwrap_or(Value::Null);
            return match side {
                "Left" => Ok(("left", inner)),
                "Right" => Ok(("right", inner)),
                _ => Err(format!("Choice: unknown tag {side}")),
            };
        }
    }
    Err("Choice: input is not an Either".to_string())
}

fn either_left_value(value: &Value) -> Option<Value> {
    if let Some(obj) = value.as_object() {
        if obj.get("__either__").and_then(Value::as_str) == Some("left") {
            return obj.get("value").cloned();
        }
        if obj.get("__tag__").and_then(Value::as_str) == Some("Left") {
            return obj.get("value").cloned();
        }
    }
    None
}

fn is_truthy(value: &Value) -> bool {
    match value {
        Value::Null | Value::Bool(false) => false,
        Value::Number(n) => n.as_f64().map_or(false, |f| f != 0.0),
        Value::String(s) => !s.is_empty(),
        _ => true,
    }
}

fn either_right_value(value: &Value) -> Option<Value> {
    if let Some(obj) = value.as_object() {
        if obj.get("__either__").and_then(Value::as_str) == Some("right") {
            return obj.get("value").cloned();
        }
        if obj.get("__tag__").and_then(Value::as_str) == Some("Right") {
            return obj.get("value").cloned();
        }
    }
    None
}
