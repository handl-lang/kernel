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

use std::collections::HashMap;
use std::rc::Rc;

use serde_json::{Map, Number, Value};

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
    Arr(Rc<[TaggedValue]>),
    Obj(Rc<HashMap<String, TaggedValue>>),
    /// Arrow-calculus pair: `(a, b)` — used by `First`/`Loop`.
    Pair(Rc<(TaggedValue, TaggedValue)>),
    /// Arrow-calculus `Either`: `left v` — used by `Choice`/`Loop`.
    EitherLeft(Rc<TaggedValue>),
    /// Arrow-calculus `Either`: `right v` — used by `Choice`/`Loop`.
    EitherRight(Rc<TaggedValue>),
    /// Arrow-value (closure): `{"__arrow__": true, "params": [...], "body":
    /// <idx>, "env": {...}}`.
    Arrow {
        params: Rc<[String]>,
        body: usize, // AstRef index
        env: Rc<HashMap<String, TaggedValue>>,
    },
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

fn object_to_tagged(o: Map<String, Value>) -> TaggedValue {
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
        let value = o
            .get("value")
            .cloned()
            .unwrap_or(Value::Null);
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
    // "env": {...}}
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
            Some(Value::Object(env_map)) => {
                Rc::from(obj_map_to_hashmap(env_map.clone()))
            }
            _ => Rc::new(HashMap::new()),
        };
        return TaggedValue::Arrow { params, body, env };
    }
    map_to_obj(o)
}

fn map_to_obj(o: Map<String, Value>) -> TaggedValue {
    TaggedValue::Obj(Rc::new(obj_map_to_hashmap(o)))
}

fn obj_map_to_hashmap(o: Map<String, Value>) -> HashMap<String, TaggedValue> {
    o.into_iter()
        .map(|(k, v)| (k, TaggedValue::from(v)))
        .collect()
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
        TaggedValue::Float(f) => {
            serde_json::Number::from_f64(*f)
                .map(Value::Number)
                .unwrap_or(Value::Null)
        }
        TaggedValue::Str(s) => Value::String((*s).to_string()),
        TaggedValue::Arr(a) => {
            Value::Array(a.iter().map(tagged_to_value).collect())
        }
        TaggedValue::Obj(o) => {
            let mut map = Map::new();
            for (k, val) in o.iter() {
                map.insert(k.clone(), tagged_to_value(val));
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
        TaggedValue::Arrow { params, body, env } => {
            let mut env_map = Map::new();
            for (k, val) in env.iter() {
                env_map.insert(k.clone(), tagged_to_value(val));
            }
            serde_json::json!({
                "__arrow__": true,
                "params": params.iter().collect::<Vec<_>>(),
                "body": body,
                "env": Value::Object(env_map),
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

    /// Returns the value as a `&HashMap` if it is an object.
    pub fn as_object(&self) -> Option<&HashMap<String, TaggedValue>> {
        match self {
            TaggedValue::Obj(o) => Some(o),
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
        (TaggedValue::Int(x), TaggedValue::Float(y)) | (TaggedValue::Float(y), TaggedValue::Int(x)) => {
            (*x as f64) == *y
        }
        (TaggedValue::Str(x), TaggedValue::Str(y)) => x == y,
        (TaggedValue::Arr(x), TaggedValue::Arr(y)) => {
            x.len() == y.len() && x.iter().zip(y.iter()).all(|(a, b)| eq(a, b))
        }
        (TaggedValue::Obj(x), TaggedValue::Obj(y)) => {
            if x.len() != y.len() {
                return false;
            }
            x.iter().all(|(k, v)| y.get(k).map(|w| eq(v, w)).unwrap_or(false))
        }
        (TaggedValue::Pair(p1), TaggedValue::Pair(p2)) => {
            eq(&p1.0, &p2.0) && eq(&p1.1, &p2.1)
        }
        (TaggedValue::EitherLeft(a), TaggedValue::EitherLeft(b)) => eq(a, b),
        (TaggedValue::EitherRight(a), TaggedValue::EitherRight(b)) => eq(a, b),
        (
            TaggedValue::Arrow { params: p1, body: b1, env: e1 },
            TaggedValue::Arrow { params: p2, body: b2, env: e2 },
        ) => {
            p1.len() == p2.len()
                && p1.iter().zip(p2.iter()).all(|(a, b)| a == b)
                && b1 == b2
                && {
                    if e1.len() != e2.len() {
                        return false;
                    }
                    e1.iter()
                        .all(|(k, v)| e2.get(k).map(|w| eq(v, w)).unwrap_or(false))
                }
        }
        _ => false,
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
            let mut __map = ::std::collections::HashMap::new();
            $(
                __map.insert(
                    ::std::string::String::from($key),
                    $crate::tval!($val),
                );
            )*
            $crate::TaggedValue::Obj(::std::rc::Rc::new(__map))
        }
    };
    // any other expression: delegate to IntoTval for type inference
    ($e:expr) => { $crate::IntoTval::into_tval($e) };
}
