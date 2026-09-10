//! Fast tagged value representation for eval engines.
//!
//! This crate provides [`TaggedValue`], a tagged-enum value representation
//! intended to replace [`serde_json::Value`] on hot eval paths. The rest of
//! the handl platform (AST, Language data, LSP, plugins, serialization)
//! continues to use `serde_json::Value`; conversion happens at the eval
//! boundary via [`From`]/[`Into`].
//!
//! Key differences from `serde_json::Value`:
//!
//! - [`TaggedValue::Int`] is a native `i64`, not a heap-allocated `f64`-backed
//!   JSON [`serde_json::Number`].
//! - [`TaggedValue::Pair`] / [`TaggedValue::EitherLeft`] /
//!   [`TaggedValue::EitherRight`] are dedicated variants, not JSON objects
//!   with string keys (`{"__pair__": [a, b]}`, `{"__either__": "left",
//!   "value": v}`).
//! - Strings are [`Rc<str>`] and arrays/objects are [`Rc`]-backed for cheap
//!   cloning.
//! - [`TaggedValue::Arrow`] is a dedicated closure variant matching the
//!   `{"__arrow__": true, "params": [...], "body": <idx>, "env": {...}}`
//!   shape used by the arrow-calculus `App` combinator.

use std::ffi::c_void;
use std::fmt;
use std::rc::Rc;
use std::sync::atomic::{AtomicBool, Ordering};

use rustc_hash::FxHashMap;
use serde_json::{Map, Number, Value};

// ---------------------------------------------------------------------------
// ForeignResource — RAII wrapper for opaque C handles (ADR-0083 §2.2)
// ---------------------------------------------------------------------------

/// An opaque foreign resource tracked by RAII (ADR-0083 §2.2 — finalizable
/// values, a Phase 4 prerequisite).
///
/// Wraps a raw C pointer (`ptr`) and an optional `finalizer` cleanup
/// function. When the last [`Rc`] reference to a `ForeignResource` drops,
/// [`Drop`] runs the finalizer exactly once (guarded by the `dropped` flag
/// to prevent double-free). This is the mechanism that lets opaque
/// `handle`-typed FFI pointers (file descriptors, mmap regions, socket
/// handles) get cleaned up automatically when the handl value holding them
/// goes out of scope — no GC, no manual `close`.
///
/// # Safety invariants
///
/// - `ptr` must be a valid opaque handle obtained from a C function (e.g. a
///   file descriptor cast to a pointer, an `mmap` region, a socket handle).
///   This type never dereferences `ptr` — it only passes it to `finalizer`.
/// - `finalizer`, when `Some`, must be safe to call with `ptr` exactly once
///   and must release the underlying resource (e.g. `libc::close`).
/// - This type is held inside an [`Rc`] (single-threaded), so it is **not**
///   `Send` or `Sync`. The `dropped` flag uses [`AtomicBool`] to prepare for
///   a future `Arc` migration that would make resources thread-safe; the
///   atomic is harmless in the single-threaded case.
pub struct ForeignResource {
    /// The opaque C handle (file descriptor, mmap region, socket, …).
    /// Never dereferenced by this type — only passed to `finalizer`.
    pub ptr: *mut c_void,
    /// Optional cleanup function called with `ptr` on drop. When `None`,
    /// the resource is dropped without any cleanup (the caller is
    /// responsible for explicit release, matching ADR-0083's short-term
    /// "explicit close in handl" approach).
    pub finalizer: Option<unsafe fn(*mut c_void)>,
    /// Guard preventing double-free. Set to `true` atomically before the
    /// finalizer runs; a second drop path sees `true` and skips.
    dropped: AtomicBool,
}

impl ForeignResource {
    /// Create a new foreign resource wrapping `ptr` with an optional
    /// `finalizer`.
    ///
    /// # Safety
    ///
    /// The caller must uphold the safety invariants documented on
    /// [`ForeignResource`]: `ptr` is a valid opaque handle and `finalizer`
    /// (if `Some`) releases it when called with `ptr`.
    pub unsafe fn new(ptr: *mut c_void, finalizer: Option<unsafe fn(*mut c_void)>) -> Self {
        ForeignResource {
            ptr,
            finalizer,
            dropped: AtomicBool::new(false),
        }
    }

    /// Returns the raw opaque pointer without consuming the resource.
    pub fn ptr(&self) -> *mut c_void {
        self.ptr
    }

    /// Returns `true` if the finalizer has already run.
    pub fn is_dropped(&self) -> bool {
        self.dropped.load(Ordering::SeqCst)
    }
}

impl Drop for ForeignResource {
    fn drop(&mut self) {
        // Atomically claim the drop: only the first caller to observe
        // `false` runs the finalizer, preventing double-free even if the
        // `Drop` impl is re-entered.
        if self
            .dropped
            .compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst)
            .is_ok()
        {
            if let Some(fin) = self.finalizer {
                // SAFETY: the constructor's caller guaranteed that `fin` is
                // safe to call with `ptr` exactly once and releases the
                // underlying resource.
                unsafe { fin(self.ptr) };
            }
        }
    }
}

impl PartialEq for ForeignResource {
    fn eq(&self, other: &Self) -> bool {
        // Resource identity is the opaque pointer address; the finalizer
        // and dropped flag are not part of identity.
        self.ptr == other.ptr
    }
}

impl fmt::Debug for ForeignResource {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ForeignResource")
            .field("ptr", &self.ptr)
            .field("has_finalizer", &self.finalizer.is_some())
            .field("dropped", &self.dropped.load(Ordering::SeqCst))
            .finish()
    }
}

/// Fast tagged value representation for eval engines.
///
/// Replaces `serde_json::Value` in hot eval paths. Key differences:
/// - `Int(i64)` is a native integer, not a heap-allocated f64 wrapper
/// - `Pair`/`Either` are dedicated variants, not JSON objects with string keys
/// - Strings are `Rc<str>` for cheap cloning
/// - Arrays/Objects are `Rc`-backed for cheap cloning
#[derive(Clone, Debug, PartialEq)]
pub enum TaggedValue {
    Null,
    Bool(bool),
    Int(i64),
    Float(f64),
    Str(Rc<str>),
    /// Contiguous byte buffer (`Rc<Vec<u8>>`). Declared as the `Bytes`
    /// scalar type in `value_types.yaml` (ADR-0078 Phase 2 / ADR-0083
    /// §2.1). The JSON encoding is `{"__bytes__": [n, ...]}` — an array
    /// of numbers in `0..=255` — so it round-trips through
    /// `serde_json::Value` unambiguously (a plain JSON array would be
    /// indistinguishable from `Arr`).
    Bytes(Rc<Vec<u8>>),
    Arr(Rc<[TaggedValue]>),
    Obj(Rc<FxHashMap<Rc<str>, TaggedValue>>),
    /// Arrow-calculus pair: `(a, b)` — used by `First`/`Loop`.
    Pair(Rc<(TaggedValue, TaggedValue)>),
    /// Arrow-calculus `Either`: `left v` — used by `Choice`/`Loop`.
    EitherLeft(Rc<TaggedValue>),
    /// Arrow-calculus `Either`: `right v` — used by `Choice`/`Loop`.
    EitherRight(Rc<TaggedValue>),
    /// Arrow-value (closure): `{"__arrow__": true, "params": [...], "body":
    /// <idx>, "env": {...}}`.
    ///
    /// `home` is the provenance of the closure: the id of the eval frame
    /// (AST + Language + module chain) that minted it, registered in the
    /// producing engine's home-frame table. `body` is only meaningful
    /// against that frame's AST. `None` means the arrow belongs to the
    /// ambient evaluation — `body` is interpreted against the AST currently
    /// being evaluated (the overwhelmingly common case: arrows are created
    /// and applied within one `eval`). A `Some(id)` home is stamped when an
    /// arrow crosses a runtime boundary (e.g. a `.hnl` module function
    /// receiving or returning a closure), so the receiving engine can route
    /// application back to the frame that owns the body. On the JSON side
    /// the key is `"__home__"` inside the `__arrow__` object.
    ///
    /// `array_pattern` is `true` when the params node is an array-destructuring
    /// pattern (e.g. `[x, y] ~> body`). In that case the arrow expects a single
    /// array argument whose elements bind to the pattern's variables. On the
    /// JSON side the key is `"array_pattern"` inside the `__arrow__` object.
    Arrow {
        params: Rc<[String]>,
        /// Rest/variadic parameter name (`[a, ...rest] ~> body`): when
        /// `Some`, surplus call arguments are bound to this name as an
        /// array (`TaggedValue::Arr`) instead of being curried. On the
        /// JSON side the key is `"rest"` inside the `__arrow__` object.
        rest: Option<Rc<str>>,
        body: usize, // AstRef index
        env: Rc<FxHashMap<Rc<str>, TaggedValue>>,
        home: Option<u64>,
        /// Whether the arrow's params are an array-destructuring pattern.
        array_pattern: bool,
    },
    /// Opaque foreign resource (RAII handle). Wraps a raw C pointer + an
    /// optional finalizer that runs when the last `Rc` reference drops
    /// (ADR-0083 §2.2 — finalizable values, Phase 4 prerequisite). The
    /// JSON encoding is `{"__resource__": {"ptr": <address>}}` — a debug
    /// representation only, since the finalizer (a function pointer)
    /// cannot be serialized. Decoding from JSON produces a `Resource`
    /// with `finalizer = None`.
    Resource(Rc<ForeignResource>),
}

impl Default for TaggedValue {
    fn default() -> Self {
        TaggedValue::Null
    }
}

// ---------------------------------------------------------------------------
// Conversions: serde_json::Value <-> TaggedValue
// ---------------------------------------------------------------------------

impl From<Value> for TaggedValue {
    fn from(v: Value) -> TaggedValue {
        match v {
            Value::Null => TaggedValue::Null,
            Value::Bool(b) => TaggedValue::Bool(b),
            Value::Number(n) => number_to_tagged(n),
            Value::String(s) => TaggedValue::Str(Rc::from(s)),
            Value::Array(a) => {
                let els: Vec<TaggedValue> = a.into_iter().map(TaggedValue::from).collect();
                TaggedValue::Arr(Rc::from(els))
            }
            Value::Object(o) => object_to_tagged(o),
        }
    }
}

fn number_to_tagged(n: Number) -> TaggedValue {
    if n.is_i64() {
        TaggedValue::Int(n.as_i64().unwrap())
    } else {
        TaggedValue::Float(n.as_f64().unwrap_or(0.0))
    }
}

/// Decode a JSON array of numbers (each in `0..=255`) into a `Vec<u8>`.
///
/// Returns `None` if any element is missing, non-integer, or out of byte
/// range, so that a malformed `{"__bytes__": ...}` payload falls back to
/// being treated as a plain object rather than silently truncating.
fn json_array_to_bytes(arr: &[Value]) -> Option<Vec<u8>> {
    let mut out = Vec::with_capacity(arr.len());
    for el in arr {
        let n = el.as_i64()?;
        let b = u8::try_from(n).ok()?;
        out.push(b);
    }
    Some(out)
}

fn object_to_tagged(o: Map<String, Value>) -> TaggedValue {
    // Bytes: {"__bytes__": [n, ...]} — a byte buffer (ADR-0083 §2.1).
    if let Some(bytes_val) = o.get("__bytes__") {
        if let Some(arr) = bytes_val.as_array() {
            if let Some(buf) = json_array_to_bytes(arr) {
                return TaggedValue::Bytes(Rc::new(buf));
            }
        }
    }
    // Pair: {"__pair__": [a, b]}
    if let Some(pair_val) = o.get("__pair__") {
        if let Some(arr) = pair_val.as_array() {
            if arr.len() == 2 {
                let a = TaggedValue::from(arr[0].clone());
                let b = TaggedValue::from(arr[1].clone());
                return TaggedValue::Pair(Rc::new((a, b)));
            }
        }
    }
    // Either: {"__either__": "left"|"right", "value": v}
    if let Some(side) = o.get("__either__").and_then(|v| v.as_str()) {
        let value = o.get("value").cloned().unwrap_or(Value::Null);
        let inner = TaggedValue::from(value);
        return match side {
            "left" => TaggedValue::EitherLeft(Rc::new(inner)),
            "right" => TaggedValue::EitherRight(Rc::new(inner)),
            _ => {
                // Unknown side: fall back to a plain object.
                map_to_obj(o)
            }
        };
    }
    // Arrow-value: {"__arrow__": true, "params": [...], "body": <idx>,
    // "env": {...}, "array_pattern": <bool>}
    if o.get("__arrow__").and_then(|v| v.as_bool()) == Some(true) {
        let params: Rc<[String]> = match o.get("params") {
            Some(Value::Array(a)) => {
                let v: Vec<String> = a
                    .iter()
                    .filter_map(|p| p.as_str().map(|s| s.to_string()))
                    .collect();
                Rc::from(v)
            }
            _ => Rc::from(Vec::<String>::new()),
        };
        let body = o
            .get("body")
            .and_then(|v| v.as_u64())
            .map(|u| u as usize)
            .unwrap_or(0);
        let env = match o.get("env") {
            Some(Value::Object(env_map)) => Rc::from(obj_map_to_hashmap(env_map.clone())),
            _ => Rc::new(FxHashMap::default()),
        };
        let rest = o.get("rest").and_then(|v| v.as_str()).map(Rc::from);
        let home = o.get("__home__").and_then(|v| v.as_u64());
        let array_pattern = o
            .get("array_pattern")
            .and_then(|v| v.as_bool())
            .unwrap_or(false);
        return TaggedValue::Arrow {
            params,
            rest,
            body,
            env,
            home,
            array_pattern,
        };
    }
    // Resource: {"__resource__": {"ptr": <address>}} — a debug-only JSON
    // encoding (ADR-0083 §2.2). The finalizer cannot be serialized, so the
    // decoded Resource has `finalizer = None`.
    if let Some(res_val) = o.get("__resource__") {
        if let Some(ptr_n) = res_val.get("ptr").and_then(|v| v.as_i64()) {
            let fr = ForeignResource {
                ptr: ptr_n as *mut c_void,
                finalizer: None,
                dropped: AtomicBool::new(false),
            };
            return TaggedValue::Resource(Rc::new(fr));
        }
    }
    map_to_obj(o)
}

fn map_to_obj(o: Map<String, Value>) -> TaggedValue {
    TaggedValue::Obj(Rc::new(obj_map_to_hashmap(o)))
}

fn obj_map_to_hashmap(o: Map<String, Value>) -> FxHashMap<Rc<str>, TaggedValue> {
    o.into_iter()
        .map(|(k, v)| (Rc::from(k), TaggedValue::from(v)))
        .collect()
}

/// Encode a byte buffer as `{"__bytes__": [n, ...]}` — the JSON form of
/// `TaggedValue::Bytes` (ADR-0083 §2.1).
fn bytes_to_value(b: &[u8]) -> Value {
    let arr: Vec<Value> = b.iter().map(|&byte| Value::from(byte as i64)).collect();
    serde_json::json!({ "__bytes__": arr })
}

impl From<TaggedValue> for Value {
    fn from(v: TaggedValue) -> Value {
        tagged_to_value(&v)
    }
}

/// Convert a [`TaggedValue`] into a [`serde_json::Value`].
///
/// This borrows the value (cloning the inner data as needed) so it can be
/// used for both `From<TaggedValue>` and reference-based conversions.
pub fn tagged_to_value(v: &TaggedValue) -> Value {
    match v {
        TaggedValue::Null => Value::Null,
        TaggedValue::Bool(b) => Value::Bool(*b),
        TaggedValue::Int(i) => Value::from(*i),
        TaggedValue::Float(f) => serde_json::Number::from_f64(*f)
            .map(Value::Number)
            .unwrap_or(Value::Null),
        TaggedValue::Str(s) => Value::String((*s).to_string()),
        TaggedValue::Bytes(b) => bytes_to_value(b),
        TaggedValue::Arr(a) => Value::Array(a.iter().map(tagged_to_value).collect()),
        TaggedValue::Obj(o) => {
            let mut map = Map::new();
            for (k, val) in o.iter() {
                map.insert(k.to_string(), tagged_to_value(val));
            }
            Value::Object(map)
        }
        TaggedValue::Pair(p) => {
            serde_json::json!({"__pair__": [tagged_to_value(&p.0), tagged_to_value(&p.1)]})
        }
        TaggedValue::EitherLeft(inner) => {
            serde_json::json!({"__either__": "left", "value": tagged_to_value(inner)})
        }
        TaggedValue::EitherRight(inner) => {
            serde_json::json!({"__either__": "right", "value": tagged_to_value(inner)})
        }
        TaggedValue::Arrow {
            params,
            rest,
            body,
            env,
            home,
            array_pattern,
        } => {
            let mut env_map = Map::new();
            for (k, val) in env.iter() {
                env_map.insert(k.to_string(), tagged_to_value(val));
            }
            let mut v = serde_json::json!({
                "__arrow__": true,
                "params": params.iter().collect::<Vec<_>>(),
                "body": body,
                "env": Value::Object(env_map),
            });
            if let Some(r) = rest {
                v["rest"] = Value::String(r.to_string());
            }
            if let Some(h) = home {
                v["__home__"] = Value::from(*h);
            }
            if *array_pattern {
                v["array_pattern"] = Value::Bool(true);
            }
            v
        }
        TaggedValue::Resource(r) => {
            // Debug-only encoding: the finalizer (a function pointer)
            // cannot be serialized, so only the pointer address is emitted.
            serde_json::json!({
                "__resource__": { "ptr": r.ptr as i64 }
            })
        }
    }
}

// ---------------------------------------------------------------------------
// Accessors (mirror common serde_json patterns)
// ---------------------------------------------------------------------------

impl TaggedValue {
    /// Returns the value as `i64` if it is an integer.
    pub fn as_i64(&self) -> Option<i64> {
        match self {
            TaggedValue::Int(i) => Some(*i),
            _ => None,
        }
    }

    /// Returns the value as `f64` if it is a float or an integer.
    pub fn as_f64(&self) -> Option<f64> {
        match self {
            TaggedValue::Float(f) => Some(*f),
            TaggedValue::Int(i) => Some(*i as f64),
            _ => None,
        }
    }

    /// Returns the value as `&str` if it is a string.
    pub fn as_str(&self) -> Option<&str> {
        match self {
            TaggedValue::Str(s) => Some(s),
            _ => None,
        }
    }

    /// Returns the value as a byte slice if it is a `Bytes` value.
    pub fn as_bytes(&self) -> Option<&[u8]> {
        match self {
            TaggedValue::Bytes(b) => Some(b),
            _ => None,
        }
    }

    /// Returns the value as `bool` if it is a boolean.
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            TaggedValue::Bool(b) => Some(*b),
            _ => None,
        }
    }

    /// Returns the value as a slice of [`TaggedValue`] if it is an array.
    pub fn as_array(&self) -> Option<&[TaggedValue]> {
        match self {
            TaggedValue::Arr(a) => Some(a),
            _ => None,
        }
    }

    /// Returns the value as a `&FxHashMap` if it is an object.
    pub fn as_object(&self) -> Option<&FxHashMap<Rc<str>, TaggedValue>> {
        match self {
            TaggedValue::Obj(o) => Some(o),
            _ => None,
        }
    }

    /// Returns the value as a [`ForeignResource`] reference if it is a
    /// `Resource` (opaque foreign handle, ADR-0083 §2.2).
    pub fn as_resource(&self) -> Option<&ForeignResource> {
        match self {
            TaggedValue::Resource(r) => Some(r),
            _ => None,
        }
    }

    /// Indexes an object value by key, mirroring `serde_json::Value::get`
    /// for string keys. Returns `None` for non-objects or missing keys.
    pub fn get(&self, key: &str) -> Option<&TaggedValue> {
        match self {
            TaggedValue::Obj(o) => o.get(key),
            _ => None,
        }
    }

    /// Returns `true` if the value is `Null`.
    pub fn is_null(&self) -> bool {
        matches!(self, TaggedValue::Null)
    }

    /// Returns `true` if the value is an array.
    pub fn is_array(&self) -> bool {
        matches!(self, TaggedValue::Arr(_))
    }
}

// ---------------------------------------------------------------------------
// Helpers (mirror eval engine patterns)
// ---------------------------------------------------------------------------

/// Construct a pair value `(a, b)`.
pub fn pair(a: TaggedValue, b: TaggedValue) -> TaggedValue {
    TaggedValue::Pair(Rc::new((a, b)))
}

/// Construct a `Bytes` value from a byte buffer.
pub fn bytes(b: impl Into<Vec<u8>>) -> TaggedValue {
    TaggedValue::Bytes(Rc::new(b.into()))
}

/// Construct a `Resource` value wrapping an opaque C pointer with an
/// optional finalizer (ADR-0083 §2.2 — finalizable values).
///
/// When the last reference to the returned `Resource` drops, `finalizer`
/// (if `Some`) is called with `ptr` exactly once, releasing the underlying
/// resource.
///
/// # Safety
///
/// The caller must uphold the safety invariants of [`ForeignResource`]:
/// `ptr` is a valid opaque handle and `finalizer` (if `Some`) releases it
/// when called with `ptr`.
pub unsafe fn resource(ptr: *mut c_void, finalizer: Option<unsafe fn(*mut c_void)>) -> TaggedValue {
    TaggedValue::Resource(Rc::new(ForeignResource::new(ptr, finalizer)))
}

/// Extract the first component of a pair value, or `None` if not a pair.
pub fn pair_fst(v: &TaggedValue) -> Option<&TaggedValue> {
    match v {
        TaggedValue::Pair(p) => Some(&p.0),
        _ => None,
    }
}

/// Extract the second component of a pair value, or `None` if not a pair.
pub fn pair_snd(v: &TaggedValue) -> Option<&TaggedValue> {
    match v {
        TaggedValue::Pair(p) => Some(&p.1),
        _ => None,
    }
}

/// Construct a `left` Either value.
pub fn either_left(v: TaggedValue) -> TaggedValue {
    TaggedValue::EitherLeft(Rc::new(v))
}

/// Construct a `right` Either value.
pub fn either_right(v: TaggedValue) -> TaggedValue {
    TaggedValue::EitherRight(Rc::new(v))
}

/// Whether an Either value is a `left`.
pub fn is_either_left(v: &TaggedValue) -> bool {
    matches!(v, TaggedValue::EitherLeft(_))
}

/// Whether an Either value is a `right`.
pub fn is_either_right(v: &TaggedValue) -> bool {
    matches!(v, TaggedValue::EitherRight(_))
}

/// Extract the carried value from an Either (left or right).
pub fn either_value(v: &TaggedValue) -> Option<&TaggedValue> {
    match v {
        TaggedValue::EitherLeft(inner) | TaggedValue::EitherRight(inner) => Some(inner),
        _ => None,
    }
}

/// Whether a [`TaggedValue`] is truthy.
///
/// Mirrors handl's truthiness rules: `false`, `null`, `0`, and `""` are
/// falsy; everything else is truthy.
pub fn truthy(v: &TaggedValue) -> bool {
    match v {
        TaggedValue::Bool(b) => *b,
        TaggedValue::Null => false,
        TaggedValue::Int(i) => *i != 0,
        TaggedValue::Float(f) => *f != 0.0,
        TaggedValue::Str(s) => !s.is_empty(),
        TaggedValue::Bytes(b) => !b.is_empty(),
        // Resources are always truthy (an opaque handle exists).
        TaggedValue::Resource(_) => true,
        _ => true,
    }
}

// ---------------------------------------------------------------------------
// Arithmetic helpers
// ---------------------------------------------------------------------------

/// Coerce a [`TaggedValue`] to an `f64` if it is numeric.
fn as_f64(v: &TaggedValue) -> Option<f64> {
    v.as_f64()
}

/// Addition: `Int+Int=Int`, any `Float` involvement yields `Float`; error
/// otherwise.
pub fn add(a: &TaggedValue, b: &TaggedValue) -> Result<TaggedValue, String> {
    match (a, b) {
        (TaggedValue::Int(x), TaggedValue::Int(y)) => Ok(TaggedValue::Int(x.wrapping_add(*y))),
        (TaggedValue::Float(_), _) | (_, TaggedValue::Float(_)) => {
            let x = as_f64(a).ok_or_else(|| "add: non-numeric operand".to_string())?;
            let y = as_f64(b).ok_or_else(|| "add: non-numeric operand".to_string())?;
            Ok(TaggedValue::Float(x + y))
        }
        _ => Err("add: non-numeric operand".to_string()),
    }
}

/// Subtraction: same rules as [`add`].
pub fn sub(a: &TaggedValue, b: &TaggedValue) -> Result<TaggedValue, String> {
    match (a, b) {
        (TaggedValue::Int(x), TaggedValue::Int(y)) => Ok(TaggedValue::Int(x.wrapping_sub(*y))),
        (TaggedValue::Float(_), _) | (_, TaggedValue::Float(_)) => {
            let x = as_f64(a).ok_or_else(|| "sub: non-numeric operand".to_string())?;
            let y = as_f64(b).ok_or_else(|| "sub: non-numeric operand".to_string())?;
            Ok(TaggedValue::Float(x - y))
        }
        _ => Err("sub: non-numeric operand".to_string()),
    }
}

/// Multiplication: same rules as [`add`].
pub fn mul(a: &TaggedValue, b: &TaggedValue) -> Result<TaggedValue, String> {
    match (a, b) {
        (TaggedValue::Int(x), TaggedValue::Int(y)) => Ok(TaggedValue::Int(x.wrapping_mul(*y))),
        (TaggedValue::Float(_), _) | (_, TaggedValue::Float(_)) => {
            let x = as_f64(a).ok_or_else(|| "mul: non-numeric operand".to_string())?;
            let y = as_f64(b).ok_or_else(|| "mul: non-numeric operand".to_string())?;
            Ok(TaggedValue::Float(x * y))
        }
        _ => Err("mul: non-numeric operand".to_string()),
    }
}

/// Division: same rules as [`add`], except integer division by zero is an
/// error.
pub fn div(a: &TaggedValue, b: &TaggedValue) -> Result<TaggedValue, String> {
    match (a, b) {
        (TaggedValue::Int(x), TaggedValue::Int(y)) => {
            if *y == 0 {
                Err("div: division by zero".to_string())
            } else {
                Ok(TaggedValue::Int(x.wrapping_div(*y)))
            }
        }
        (TaggedValue::Float(_), _) | (_, TaggedValue::Float(_)) => {
            let x = as_f64(a).ok_or_else(|| "div: non-numeric operand".to_string())?;
            let y = as_f64(b).ok_or_else(|| "div: non-numeric operand".to_string())?;
            Ok(TaggedValue::Float(x / y))
        }
        _ => Err("div: non-numeric operand".to_string()),
    }
}

/// Modulo: same rules as [`add`], except integer modulo by zero is an error.
pub fn mod_(a: &TaggedValue, b: &TaggedValue) -> Result<TaggedValue, String> {
    match (a, b) {
        (TaggedValue::Int(x), TaggedValue::Int(y)) => {
            if *y == 0 {
                Err("mod: division by zero".to_string())
            } else {
                Ok(TaggedValue::Int(x.wrapping_rem(*y)))
            }
        }
        (TaggedValue::Float(_), _) | (_, TaggedValue::Float(_)) => {
            let x = as_f64(a).ok_or_else(|| "mod: non-numeric operand".to_string())?;
            let y = as_f64(b).ok_or_else(|| "mod: non-numeric operand".to_string())?;
            Ok(TaggedValue::Float(x % y))
        }
        _ => Err("mod: non-numeric operand".to_string()),
    }
}

/// Numeric less-than comparison. Both operands must be numeric.
pub fn lt(a: &TaggedValue, b: &TaggedValue) -> Result<bool, String> {
    match (a, b) {
        (TaggedValue::Int(x), TaggedValue::Int(y)) => Ok(x < y),
        (TaggedValue::Float(_), _) | (_, TaggedValue::Float(_)) => {
            let x = as_f64(a).ok_or_else(|| "lt: non-numeric operand".to_string())?;
            let y = as_f64(b).ok_or_else(|| "lt: non-numeric operand".to_string())?;
            Ok(x < y)
        }
        _ => Err("lt: non-numeric operand".to_string()),
    }
}

/// Structural equality of two [`TaggedValue`]s.
pub fn eq(a: &TaggedValue, b: &TaggedValue) -> bool {
    match (a, b) {
        (TaggedValue::Null, TaggedValue::Null) => true,
        (TaggedValue::Bool(x), TaggedValue::Bool(y)) => x == y,
        (TaggedValue::Int(x), TaggedValue::Int(y)) => x == y,
        (TaggedValue::Float(x), TaggedValue::Float(y)) => x == y,
        // Cross-numeric: compare as f64 for consistency with JSON semantics.
        (TaggedValue::Int(x), TaggedValue::Float(y))
        | (TaggedValue::Float(y), TaggedValue::Int(x)) => (*x as f64) == *y,
        (TaggedValue::Str(x), TaggedValue::Str(y)) => x == y,
        (TaggedValue::Bytes(x), TaggedValue::Bytes(y)) => x == y,
        (TaggedValue::Arr(x), TaggedValue::Arr(y)) => {
            x.len() == y.len() && x.iter().zip(y.iter()).all(|(a, b)| eq(a, b))
        }
        (TaggedValue::Obj(x), TaggedValue::Obj(y)) => {
            if x.len() != y.len() {
                return false;
            }
            x.iter()
                .all(|(k, v)| y.get(k.as_ref()).map(|w| eq(v, w)).unwrap_or(false))
        }
        (TaggedValue::Pair(p1), TaggedValue::Pair(p2)) => eq(&p1.0, &p2.0) && eq(&p1.1, &p2.1),
        (TaggedValue::EitherLeft(a), TaggedValue::EitherLeft(b)) => eq(a, b),
        (TaggedValue::EitherRight(a), TaggedValue::EitherRight(b)) => eq(a, b),
        (
            TaggedValue::Arrow {
                params: p1,
                rest: r1,
                body: b1,
                env: e1,
                array_pattern: ap1,
                ..
            },
            TaggedValue::Arrow {
                params: p2,
                rest: r2,
                body: b2,
                env: e2,
                array_pattern: ap2,
                ..
            },
        ) => {
            r1 == r2
                && ap1 == ap2
                && p1.len() == p2.len()
                && p1.iter().zip(p2.iter()).all(|(a, b)| a == b)
                && b1 == b2
                && {
                    if e1.len() != e2.len() {
                        return false;
                    }
                    e1.iter()
                        .all(|(k, v)| e2.get(k.as_ref()).map(|w| eq(v, w)).unwrap_or(false))
                }
        }
        // Resources are equal by opaque pointer identity.
        (TaggedValue::Resource(a), TaggedValue::Resource(b)) => a.ptr == b.ptr,
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// 2-cell runtime helpers (ADR-0104b frontier value model)
// ---------------------------------------------------------------------------

/// Build a `Cell2` tagged record from its source, target, and witness value.
pub fn cell2(src: TaggedValue, tgt: TaggedValue, value: TaggedValue) -> TaggedValue {
    let mut map = FxHashMap::with_capacity_and_hasher(4, Default::default());
    map.insert(Rc::from("__tag__"), TaggedValue::Str(Rc::from("Cell2")));
    map.insert(Rc::from("__src__"), src);
    map.insert(Rc::from("__tgt__"), tgt);
    map.insert(Rc::from("value"), value);
    TaggedValue::Obj(Rc::new(map))
}

/// Compose two 1-cell arrow values into a serializable `Arrow` record.
pub fn compose1(first: &TaggedValue, second: &TaggedValue) -> TaggedValue {
    let mut map = FxHashMap::with_capacity_and_hasher(3, Default::default());
    map.insert(Rc::from("__tag__"), TaggedValue::Str(Rc::from("Arrow")));
    map.insert(Rc::from("first"), first.clone());
    map.insert(Rc::from("second"), second.clone());
    TaggedValue::Obj(Rc::new(map))
}

/// `CellId(arrow)` — wrap the arrow's result in a `Cell2`.
pub fn cell2_id(arrow: &TaggedValue) -> TaggedValue {
    cell2(arrow.clone(), arrow.clone(), arrow.clone())
}

/// `CellCompV(first, second)` — vertical cell composition metadata.
pub fn cell2_comp_v(first: &TaggedValue, second: &TaggedValue) -> TaggedValue {
    let src = first.get("__src__").unwrap_or(first).clone();
    let tgt = second.get("__tgt__").unwrap_or(second).clone();
    let value = second.get("value").unwrap_or(second).clone();
    cell2(src, tgt, value)
}

/// `Src(cell)` — project the source 1-cell, falling back to the value itself.
pub fn cell2_src(cell: &TaggedValue) -> TaggedValue {
    cell.get("__src__").cloned().unwrap_or(cell.clone())
}

/// `Tgt(cell)` — project the target 1-cell, falling back to the value itself.
pub fn cell2_tgt(cell: &TaggedValue) -> TaggedValue {
    cell.get("__tgt__").cloned().unwrap_or(cell.clone())
}

/// `Whisker` — attach a 1-cell `arrow` to the left or right side of a 2-cell.
/// `side` is `"Left"` or `"Right"`.
pub fn cell2_whisker(side: &str, arrow: &TaggedValue, cell: &TaggedValue) -> TaggedValue {
    let src = cell.get("__src__").unwrap_or(cell);
    let tgt = cell.get("__tgt__").unwrap_or(cell);
    let value = cell.get("value").unwrap_or(cell).clone();
    let (new_src, new_tgt) = if side == "Right" {
        (compose1(src, arrow), compose1(tgt, arrow))
    } else {
        (compose1(arrow, src), compose1(arrow, tgt))
    };
    cell2(new_src, new_tgt, value)
}

/// `RecordProj` on tagged runtime values: `record[field]` or `Null`.
pub fn record_proj(record: &TaggedValue, field: &str) -> TaggedValue {
    match record {
        TaggedValue::Obj(map) => map.get(field).cloned().unwrap_or(TaggedValue::Null),
        _ => TaggedValue::Null,
    }
}

// ---------------------------------------------------------------------------
// tval! macro (like serde_json::json! but produces TaggedValue)
// ---------------------------------------------------------------------------

/// Trait used by the [`tval!`] macro to convert primitive literals into
/// [`TaggedValue`]s.
///
/// This is implemented for the common numeric, boolean, and string types so
/// that `tval!(42)`, `tval!(3.14)`, `tval!(true)`, and `tval!("hi")` all
/// resolve to the correct variant via type inference.
pub trait IntoTval {
    fn into_tval(self) -> TaggedValue;
}

macro_rules! impl_into_tval_int {
    ($($t:ty),*) => {
        $(
            impl IntoTval for $t {
                fn into_tval(self) -> TaggedValue {
                    TaggedValue::Int(self as i64)
                }
            }
        )*
    };
}

macro_rules! impl_into_tval_float {
    ($($t:ty),*) => {
        $(
            impl IntoTval for $t {
                fn into_tval(self) -> TaggedValue {
                    TaggedValue::Float(self as f64)
                }
            }
        )*
    };
}

impl_into_tval_int!(i8, i16, i32, i64, u8, u16, u32);
impl_into_tval_float!(f32, f64);

impl IntoTval for bool {
    fn into_tval(self) -> TaggedValue {
        TaggedValue::Bool(self)
    }
}

impl IntoTval for &str {
    fn into_tval(self) -> TaggedValue {
        TaggedValue::Str(Rc::from(self))
    }
}

impl IntoTval for String {
    fn into_tval(self) -> TaggedValue {
        TaggedValue::Str(Rc::from(self))
    }
}

impl IntoTval for Vec<u8> {
    fn into_tval(self) -> TaggedValue {
        TaggedValue::Bytes(Rc::new(self))
    }
}

impl IntoTval for &[u8] {
    fn into_tval(self) -> TaggedValue {
        TaggedValue::Bytes(Rc::new(self.to_vec()))
    }
}

impl IntoTval for TaggedValue {
    fn into_tval(self) -> TaggedValue {
        self
    }
}

/// A macro to build [`TaggedValue`]s, analogous to `serde_json::json!`.
///
/// # Examples
///
/// ```
/// use handl_value::{tval, TaggedValue};
///
/// let n = tval!(null);
/// assert!(n.is_null());
///
/// let s = tval!("hello");
/// assert_eq!(s.as_str(), Some("hello"));
///
/// let arr = tval!([1, 2, 3]);
/// assert_eq!(arr.as_array().map(|a| a.len()), Some(3));
///
/// let obj = tval!({"a": 1, "b": true});
/// assert!(obj.get("a").unwrap().as_i64() == Some(1));
/// ```
#[macro_export]
macro_rules! tval {
    // null
    (null) => { $crate::TaggedValue::Null };
    // bool literals
    (true) => { $crate::TaggedValue::Bool(true) };
    (false) => { $crate::TaggedValue::Bool(false) };
    // array
    ([$($elem:tt),* $(,)?]) => {
        $crate::TaggedValue::Arr(::std::rc::Rc::from(::std::vec![
            $( $crate::tval!($elem) ),*
        ]))
    };
    // object
    ({$($key:literal : $val:tt),* $(,)?}) => {
        {
            let mut __map = ::rustc_hash::FxHashMap::default();
            $(
                __map.insert(
                    ::std::rc::Rc::from($key),
                    $crate::tval!($val),
                );
            )*
            $crate::TaggedValue::Obj(::std::rc::Rc::new(__map))
        }
    };
    // any other expression: delegate to IntoTval for type inference
    ($e:expr) => { $crate::IntoTval::into_tval($e) };
}
