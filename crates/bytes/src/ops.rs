//! Rust `Function` impls for the `bytes` module — the handls (handlers)
//! for the `op`/`handl` declarations in `bytes.hnl`.
//!
//! All 8 functions are FFI atoms: `Bytes` is a scalar value type
//! (`value_types.yaml`, ADR-0083 §2.1) with no literal syntax and no
//! eval-vocabulary constructor, so construction, indexing, slicing, and
//! UTF-8 coding cannot be expressed as pure handl arrows. The
//! `op`/`handl` declaration form (ADR-0077 Phase 2) declares the
//! interface in `bytes.hnl`; these impls provide the logic and are
//! registered in an [`OpRegistry`](handl_plugin_lib_handl::OpRegistry).
//!
//! `Bytes` values cross the `Function` boundary as
//! `{"__bytes__": [n, ...]}` — the canonical JSON encoding produced by
//! [`handl_value::tagged_to_value`] and decoded by
//! `TaggedValue::from(serde_json::Value)`; both are reused here rather
//! than hand-rolling the tag.

use std::rc::Rc;
use std::sync::Arc;

use handl_platform::{EvalContext, EvalError, Function};
use handl_plugin_lib_handl::OpRegistry;
use handl_value::{TaggedValue, tagged_to_value};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Decode a `Bytes` argument through the canonical tagged-value decoder
/// (`{"__bytes__": [n, ...]}` → `TaggedValue::Bytes`). A malformed or
/// non-`Bytes` payload is a `TypeMismatch`.
fn require_bytes(arg: &serde_json::Value) -> Result<Rc<Vec<u8>>, EvalError> {
    match TaggedValue::from(arg.clone()) {
        TaggedValue::Bytes(b) => Ok(b),
        _ => Err(EvalError::TypeMismatch(format!(
            "expected {}, got {}",
            "Bytes", "non-Bytes",
        ))),
    }
}

/// Encode a byte buffer as the canonical `{"__bytes__": [n, ...]}` JSON
/// value, via `TaggedValue::Bytes` and the shared tagged-value encoder.
fn encode_bytes(buf: Vec<u8>) -> serde_json::Value {
    tagged_to_value(&handl_value::bytes(buf))
}

fn require_integer(arg: &serde_json::Value) -> Result<i64, EvalError> {
    // Integral floats count: upstream ops (e.g. `char.code_point_at`)
    // produce `f64` values, so an integer-valued `127.0` must satisfy the
    // `List Int` contract just like a literal `127` does — matching the
    // `require_int` convention in `plugin-lib-char-native`.
    arg.as_i64()
        .or_else(|| {
            arg.as_f64()
                .filter(|n| n.fract() == 0.0 && n.is_finite())
                .map(|n| n as i64)
        })
        .ok_or(EvalError::TypeMismatch(format!(
            "expected {}, got {}",
            "integer", "non-integer",
        )))
}

fn require_string(arg: &serde_json::Value) -> Result<&str, EvalError> {
    arg.as_str().ok_or(EvalError::TypeMismatch(format!(
        "expected {}, got {}",
        "string", "non-string",
    )))
}

fn require_non_negative(arg: &serde_json::Value) -> Result<usize, EvalError> {
    let n = require_integer(arg)?;
    usize::try_from(n).map_err(|_| {
        EvalError::TypeMismatch(format!(
            "expected {}, got {}",
            "non-negative number", "negative number",
        ))
    })
}

// ---------------------------------------------------------------------------
// Construction / projection
// ---------------------------------------------------------------------------

/// The Rust handl for `op "bytes.from_list" : (List Int) -> Bytes`.
///
/// Each element must be an integer in `0..=255`; out-of-range or
/// non-integer elements are a `TypeMismatch` rather than a silent
/// truncation (matching the FFI marshal boundary's byte-range rule).
#[derive(Clone, Copy)]
pub struct FromList;
impl Function for FromList {
    fn call(
        &self,
        args: &[serde_json::Value],
        _ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        let arg = args.first().ok_or(EvalError::TypeMismatch(format!(
            "expected {} args, got {}",
            1, 0,
        )))?;
        let arr = handl_lib_ops::shared::require_array(arg)?;
        let mut buf = Vec::with_capacity(arr.len());
        for el in arr {
            let n = require_integer(el)?;
            let byte = u8::try_from(n)
                .map_err(|_| EvalError::TypeMismatch(format!("byte out of range 0..=255: {n}")))?;
            buf.push(byte);
        }
        Ok(encode_bytes(buf))
    }
}

/// The Rust handl for `op "bytes.to_list" : Bytes -> (List Int)`.
#[derive(Clone, Copy)]
pub struct ToList;
impl Function for ToList {
    fn call(
        &self,
        args: &[serde_json::Value],
        _ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        let arg = args.first().ok_or(EvalError::TypeMismatch(format!(
            "expected {} args, got {}",
            1, 0,
        )))?;
        let buf = require_bytes(arg)?;
        let items: Vec<serde_json::Value> = buf
            .iter()
            .map(|&byte| serde_json::Value::from(byte as i64))
            .collect();
        Ok(serde_json::Value::Array(items))
    }
}

// ---------------------------------------------------------------------------
// Buffer ops
// ---------------------------------------------------------------------------

/// The Rust handl for `op "bytes.concat" : (Bytes * Bytes) -> Bytes`.
#[derive(Clone, Copy)]
pub struct Concat;
impl Function for Concat {
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
        let a = require_bytes(&args[0])?;
        let b = require_bytes(&args[1])?;
        let mut buf = Vec::with_capacity(a.len() + b.len());
        buf.extend_from_slice(&a);
        buf.extend_from_slice(&b);
        Ok(encode_bytes(buf))
    }
}

/// The Rust handl for `op "bytes.slice" : (Bytes * Int * Int) -> Bytes`.
///
/// The window `[offset, offset + len)` is clamped to the buffer (the same
/// clamping semantics as `str.slice`); a negative `offset` or `len` is a
/// `TypeMismatch`.
#[derive(Clone, Copy)]
pub struct Slice;
impl Function for Slice {
    fn call(
        &self,
        args: &[serde_json::Value],
        _ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        if args.len() < 3 {
            return Err(EvalError::TypeMismatch(format!(
                "expected {} args, got {}",
                3,
                args.len(),
            )));
        }
        let buf = require_bytes(&args[0])?;
        let offset = require_non_negative(&args[1])?;
        let len = require_non_negative(&args[2])?;
        let start = offset.min(buf.len());
        let end = start.saturating_add(len).min(buf.len());
        Ok(encode_bytes(buf[start..end].to_vec()))
    }
}

/// The Rust handl for `op "bytes.len" : Bytes -> Int`.
#[derive(Clone, Copy)]
pub struct Len;
impl Function for Len {
    fn call(
        &self,
        args: &[serde_json::Value],
        _ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        let arg = args.first().ok_or(EvalError::TypeMismatch(format!(
            "expected {} args, got {}",
            1, 0,
        )))?;
        let buf = require_bytes(arg)?;
        Ok(serde_json::Value::from(buf.len() as i64))
    }
}

/// The Rust handl for `op "bytes.at" : (Bytes * Int) -> Int`.
///
/// A negative index is a `TypeMismatch`; an index at or past the end is an
/// out-of-bounds error (the same convention as `str.char_at`).
#[derive(Clone, Copy)]
pub struct At;
impl Function for At {
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
        let buf = require_bytes(&args[0])?;
        let index = require_integer(&args[1])?;
        if index < 0 {
            return Err(EvalError::TypeMismatch(format!(
                "expected {}, got {}",
                "non-negative number", "negative number",
            )));
        }
        let byte = buf.get(index as usize).ok_or_else(|| {
            EvalError::Other(format!(
                "index {index} out of bounds (byte count: {})",
                buf.len()
            ))
        })?;
        Ok(serde_json::Value::from(*byte as i64))
    }
}

// ---------------------------------------------------------------------------
// UTF-8 coding
// ---------------------------------------------------------------------------

/// The Rust handl for `op "bytes.utf8_encode" : String -> Bytes`.
#[derive(Clone, Copy)]
pub struct Utf8Encode;
impl Function for Utf8Encode {
    fn call(
        &self,
        args: &[serde_json::Value],
        _ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        let arg = args.first().ok_or(EvalError::TypeMismatch(format!(
            "expected {} args, got {}",
            1, 0,
        )))?;
        let s = require_string(arg)?;
        Ok(encode_bytes(s.as_bytes().to_vec()))
    }
}

/// The Rust handl for `op "bytes.utf8_decode" : Bytes -> String`.
///
/// Invalid UTF-8 is an error (matching the `base64.decode` utf-8 check).
#[derive(Clone, Copy)]
pub struct Utf8Decode;
impl Function for Utf8Decode {
    fn call(
        &self,
        args: &[serde_json::Value],
        _ctx: &mut EvalContext,
    ) -> Result<serde_json::Value, EvalError> {
        let arg = args.first().ok_or(EvalError::TypeMismatch(format!(
            "expected {} args, got {}",
            1, 0,
        )))?;
        let buf = require_bytes(arg)?;
        let s = String::from_utf8((*buf).clone())
            .map_err(|e| EvalError::Other(format!("bytes.utf8_decode is not valid utf-8: {e}")))?;
        Ok(serde_json::Value::from(s))
    }
}

// ---------------------------------------------------------------------------
// Op Registry
// ---------------------------------------------------------------------------

/// The op names declared in `bytes.hnl`.
pub const BYTES_OPS: &[&str] = &[
    "bytes.from_list",
    "bytes.to_list",
    "bytes.concat",
    "bytes.slice",
    "bytes.len",
    "bytes.at",
    "bytes.utf8_encode",
    "bytes.utf8_decode",
];

/// Build the [`OpRegistry`] for bytes, registering the Rust handls under
/// their op names (no runtime checkers; axioms trusted).
pub fn bytes_op_registry() -> OpRegistry {
    let mut registry = OpRegistry::new();
    registry.register("bytes.from_list", Arc::new(FromList));
    registry.register("bytes.to_list", Arc::new(ToList));
    registry.register("bytes.concat", Arc::new(Concat));
    registry.register("bytes.slice", Arc::new(Slice));
    registry.register("bytes.len", Arc::new(Len));
    registry.register("bytes.at", Arc::new(At));
    registry.register("bytes.utf8_encode", Arc::new(Utf8Encode));
    registry.register("bytes.utf8_decode", Arc::new(Utf8Decode));
    registry
}
