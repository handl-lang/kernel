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
use std::hash::{DefaultHasher, Hash, Hasher};
use std::rc::Rc;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};

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
// ---------------------------------------------------------------------------
// Sym — nominal identity (ADR-0106 §2, Phase 2 kernel primitives)
// ---------------------------------------------------------------------------

/// Global counter minting fresh nominal handles.
///
/// `sym()` mutates this global identity space (ADR-0106 "Negative":
/// cross-process/restart identity needs a stable naming or session-identity
/// story — follow-up ADR). Identity is the `handle`, not the display name:
/// two distinct syms with equal names are never equal, and a deserialized
/// sym compares equal to the live sym it was serialized from because the
/// handle is part of the explicit serialized data.
static SYM_NEXT_HANDLE: AtomicU64 = AtomicU64::new(1);

/// A nominal identity object — the `sym()` primitive of ADR-0106 §2.
///
/// A `Sym` is a first-class nominal identity with:
///
/// - a unique `handle` minted from a global counter (the identity — used
///   for equality and hashing),
/// - a display `name` (presentation only; two syms with the same name are
///   never equal — only the handle decides),
/// - an optional `parent`, which must itself be a [`Sym`]. The parent
///   structure is a single-parent tree by construction (diamonds are
///   impossible: each sym has exactly one parent, fixed at construction),
///   and cycles are impossible because a parent is always constructed
///   before its child (and JSON decoding is a tree, so it cannot create
///   one either).
///
/// # Equality
///
/// Identity equality, not structural equality: a sym equals itself, and two
/// distinct syms are never equal — even with identical names and identical
/// parent chains. `Sym`'s `PartialEq` compares handles; the display name is
/// not part of identity. Hashing agrees (`Hash` hashes the handle), so
/// hash/eq consistency holds.
///
/// # Serializability
///
/// The JSON encoding is `{"__sym__": {"handle": <n>, "name": "...",
/// "parent": <nested sym or null>}}` — explicit data with no closures and
/// no hidden state. Round-tripping preserves the handle, so a deserialized
/// sym compares equal to the live sym it was serialized from (within a
/// process; cross-process identity is a follow-up ADR per ADR-0106).
#[derive(Clone, Debug)]
pub struct Sym {
    /// The unique nominal handle (identity). Minted from
    /// [`SYM_NEXT_HANDLE`] at construction; preserved by serialization.
    handle: u64,
    /// Display name — presentation only, never part of identity.
    name: Rc<str>,
    /// Optional nominal parent (also a `Sym`). Single parent, no cycles.
    parent: Option<Rc<Sym>>,
}

impl Sym {
    /// Mint a fresh root nominal identity (no parent), with `name` as its
    /// display name.
    pub fn fresh(name: &str) -> Sym {
        let handle = SYM_NEXT_HANDLE.fetch_add(1, Ordering::SeqCst);
        Sym {
            handle,
            name: Rc::from(name),
            parent: None,
        }
    }

    /// Mint a fresh nominal identity whose parent is `parent` (also
    /// nominal). The parent chain is fixed at construction.
    pub fn fresh_with_parent(name: &str, parent: &Sym) -> Sym {
        let handle = SYM_NEXT_HANDLE.fetch_add(1, Ordering::SeqCst);
        Sym {
            handle,
            name: Rc::from(name),
            parent: Some(Rc::new(parent.clone())),
        }
    }

    /// The unique nominal handle — the identity of this sym.
    pub fn handle(&self) -> u64 {
        self.handle
    }

    /// The display name (presentation only — see the type docs).
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The nominal parent, or `None` for a root sym.
    pub fn parent(&self) -> Option<&Sym> {
        self.parent.as_deref()
    }

    /// Strict descendant check: `true` iff `other` appears in this sym's
    /// parent chain (excluding the sym itself — a sym is not its own
    /// strict descendant).
    pub fn is_descendant_of(&self, other: &Sym) -> bool {
        let mut cur = self.parent.as_deref();
        while let Some(p) = cur {
            if p == other {
                return true;
            }
            cur = p.parent.as_deref();
        }
        false
    }

    /// Inclusive ancestor check: `true` iff this sym equals `other` or
    /// `other` appears in its parent chain. This is the `instanceof` walk
    /// of ADR-0106 §2 (`Float instanceof Number`, `Float instanceof Float`).
    pub fn has_ancestor(&self, other: &Sym) -> bool {
        self == other || self.is_descendant_of(other)
    }

    /// The parent chain as a vector, root first, ending with `self`.
    /// Linear by construction (single parent, no cycles).
    pub fn chain(&self) -> Vec<Rc<Sym>> {
        let mut rev = Vec::new();
        let mut cur = Some(self);
        while let Some(s) = cur {
            rev.push(Rc::new(s.clone()));
            cur = s.parent.as_deref();
        }
        rev.reverse();
        rev
    }
}

impl PartialEq for Sym {
    fn eq(&self, other: &Sym) -> bool {
        // Identity is the handle, not the name: distinct syms with equal
        // display names are never equal (ADR-0106 §2).
        self.handle == other.handle
    }
}

impl Eq for Sym {}

impl Hash for Sym {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.handle.hash(state);
    }
}

impl fmt::Display for Sym {
    /// Debug-friendly display: `name#handle` (the handle disambiguates
    /// same-named syms).
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}#{}", self.name, self.handle)
    }
}

/// Fast tagged value representation for eval engines.
///
/// Replaces `serde_json::Value` in hot eval paths. Key differences:
/// - `Int(i64)` is a native integer, not a heap-allocated f64 wrapper
/// - `Pair`/`Either` are dedicated variants, not JSON objects with string keys
/// - Strings are `Rc<str>` for cheap cloning
/// - Arrays/Objects are `Rc`-backed for cheap cloning
/// - [`TaggedValue::Sym`] is a nominal identity (ADR-0106 §2): identity
///   equality by handle, not structural equality. `PartialEq`/`Hash` are
///   hand-written for this reason (see the [`Sym`] docs).
#[derive(Clone, Debug)]
pub enum TaggedValue {
    Null,
    Bool(bool),
    Int(i64),
    Float(f64),
    /// Nominal identity (ADR-0106 §2): the `sym()` primitive. Identity
    /// equality by handle; the display name inside is presentation only.
    /// JSON encoding: `{"__sym__": {"handle": <n>, "name": "...",
    /// "parent": <sym or null>}}`.
    Sym(Rc<Sym>),
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
    /// <idx>, "env": {...}}`, optionally `"body_def": <tv>`.
    ///
    /// `body_def` (ADR-0106 item 2) carries the body as explicit, serializable
    /// structure — see the field docs below. It is optional and additive; the
    /// `body`/`env`/`home` fields remain the fallback.
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
        /// The arrow's body as **explicit, serializable structure that lives
        /// in the value** (ADR-0106 §3/§6 item 2) — the fix for `body` being
        /// a process-local AST index. When present it holds an opaque tagged
        /// value carrying the language-level AST encoding
        /// `{"__ast__": <serialized Ast>}` (see `handl_language::ast_value`).
        ///
        /// `None` (the default) means the arrow relies on the `body`/`home`
        /// fallback exactly as before, so this field is purely additive. On
        /// the JSON side the key is `"body_def"`, emitted only when set.
        ///
        /// Because it is *derived* from `body` (the same body, pre-extracted
        /// into a standalone arena), it is deliberately **not part of the
        /// value's identity**: `eq` and `Hash` both ignore it, so two arrows
        /// with the same `params`/`rest`/`body`/`env`/`home`/`array_pattern`
        /// remain equal whether or not either carries a definition.
        ///
        /// The apply path does not yet consume this field (see the ADR's
        /// "serializable arrow representation (item 2)" migration order).
        body_def: Option<Rc<TaggedValue>>,
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
// Equality & hashing (hand-written — `Sym` is identity-equal, not
// structurally equal; ADR-0106 §2)
// ---------------------------------------------------------------------------

impl PartialEq for TaggedValue {
    fn eq(&self, other: &TaggedValue) -> bool {
        eq(self, other)
    }
}

impl Eq for TaggedValue {}

impl Hash for TaggedValue {
    /// Hash consistent with [`eq`]:
    ///
    /// - `Sym` hashes its handle only (identity equality).
    /// - Numerics hash as `f64` bits, because [`eq`] treats `Int`/`Float`
    ///   as cross-comparable (`Int(1) == Float(1.0)`).
    /// - Objects/arrows hash order-independently (sum of per-entry hashes),
    ///   because [`eq`] compares them unordered.
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            TaggedValue::Null => 0u8.hash(state),
            TaggedValue::Bool(b) => {
                1u8.hash(state);
                b.hash(state);
            }
            // Cross-numeric with Float (see `eq`): hash as f64 bits.
            TaggedValue::Int(i) => {
                2u8.hash(state);
                (*i as f64).to_bits().hash(state);
            }
            TaggedValue::Float(f) => {
                2u8.hash(state);
                f.to_bits().hash(state);
            }
            TaggedValue::Str(s) => {
                3u8.hash(state);
                s.hash(state);
            }
            TaggedValue::Bytes(b) => {
                4u8.hash(state);
                b.hash(state);
            }
            TaggedValue::Arr(a) => {
                5u8.hash(state);
                a.hash(state);
            }
            TaggedValue::Obj(o) => {
                6u8.hash(state);
                hash_map_entries(o.iter().map(|(k, v)| (k, v)), state);
            }
            TaggedValue::Pair(p) => {
                7u8.hash(state);
                p.hash(state);
            }
            TaggedValue::EitherLeft(v) => {
                8u8.hash(state);
                v.hash(state);
            }
            TaggedValue::EitherRight(v) => {
                9u8.hash(state);
                v.hash(state);
            }
            TaggedValue::Arrow {
                params,
                rest,
                body,
                env,
                home,
                array_pattern,
                // ADR-0106 item 2 step 1: `body_def` is **derived** data (the
                // same body, pre-extracted into a standalone arena), so it is
                // deliberately NOT part of the arrow's identity — `eq` ignores
                // it, and so must `Hash` (a field in neither keeps the
                // `Hash`/`Eq` contract intact). Binding it here with `_`
                // documents that omission.
                body_def: _,
            } => {
                10u8.hash(state);
                params.hash(state);
                rest.hash(state);
                body.hash(state);
                hash_map_entries(env.iter().map(|(k, v)| (k.as_ref(), v)), state);
                home.hash(state);
                array_pattern.hash(state);
            }
            TaggedValue::Resource(r) => {
                11u8.hash(state);
                (r.ptr as usize).hash(state);
            }
            TaggedValue::Sym(s) => {
                12u8.hash(state);
                s.hash(state);
            }
        }
    }
}

/// Order-independent hashing for `TaggedValue::Obj` and arrow `env` maps:
/// sum of per-entry hashes (equal maps hash equally regardless of
/// insertion order; collisions are allowed by the `Hash` contract).
fn hash_map_entries<'a, I, K, V>(entries: I, state: &mut impl Hasher)
where
    I: Iterator<Item = (K, V)> + 'a,
    K: Hash,
    V: Hash,
{
    let mut acc: u64 = 0;
    for (k, v) in entries {
        let mut h = DefaultHasher::new();
        k.hash(&mut h);
        v.hash(&mut h);
        acc = acc.wrapping_add(h.finish());
    }
    acc.hash(state);
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
    // Sym: {"__sym__": {"handle": <n>, "name": "...", "parent": <sym or
    // null>}} — a nominal identity (ADR-0106 §2). Malformed payloads fall
    // back to a plain object (matching the lenient `__bytes__` style).
    // Decoding is a pure tree walk: JSON cannot express the parent cycle,
    // so no cycle check is needed.
    if let Some(sym_val) = o.get("__sym__").and_then(|v| v.as_object()) {
        if let Some(s) = sym_from_json(sym_val) {
            return s;
        }
    }
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
    // "env": {...}, "array_pattern": <bool>, "body_def": <tv>}
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
        // Optional serialized body definition (ADR-0106 item 2): an opaque
        // tagged value (`{"__ast__": <serialized Ast>}`) carried by the arrow
        // so its body is self-contained. Absent -> `None`, preserving the
        // legacy `body`/`home` fallback.
        let body_def = o
            .get("body_def")
            .map(|v| Rc::new(TaggedValue::from(v.clone())));
        return TaggedValue::Arrow {
            params,
            rest,
            body,
            env,
            home,
            array_pattern,
            body_def,
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

/// Decode the inner payload of a `{"__sym__": {...}}` JSON object into a
/// nominal [`TaggedValue`]. Returns `None` when the payload is malformed
/// (missing/invalid `handle` or `name`, or a `parent` that is not itself a
/// sym encoding or `null`), so the caller can fall back to a plain object.
fn sym_from_json(sym_val: &Map<String, Value>) -> Option<TaggedValue> {
    let handle = sym_val.get("handle").and_then(|v| v.as_u64())?;
    if handle == 0 {
        return None;
    }
    let name = sym_val.get("name").and_then(|v| v.as_str())?;
    let parent = match sym_val.get("parent") {
        None | Some(Value::Null) => None,
        // The encoder nests the parent as a full {"__sym__": {...}} value;
        // unwrap the wrapper before recursing.
        Some(Value::Object(parent_obj)) => {
            let parent_sym = parent_obj.get("__sym__").and_then(|v| v.as_object())?;
            match sym_from_json(parent_sym) {
                Some(TaggedValue::Sym(p)) => Some(p),
                _ => return None,
            }
        }
        Some(_) => return None,
    };
    let sym = Sym {
        handle,
        name: Rc::from(name),
        parent,
    };
    Some(TaggedValue::Sym(Rc::new(sym)))
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
        TaggedValue::Sym(s) => {
            // Nominal identity (ADR-0106 §2): explicit data — handle (the
            // identity), name (presentation), and the parent chain nested
            // inline. The nested encoding keeps the value self-contained
            // (O(depth) per sym; chains in this kernel are short).
            let parent = match s.parent() {
                Some(p) => tagged_to_value(&TaggedValue::Sym(Rc::new(p.clone()))),
                None => Value::Null,
            };
            serde_json::json!({
                "__sym__": {
                    "handle": s.handle(),
                    "name": s.name(),
                    "parent": parent,
                }
            })
        }
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
            body_def,
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
            // Serialized body definition (ADR-0106 item 2): emitted only when
            // present, so the default arrow shape is unchanged.
            if let Some(bd) = body_def {
                v["body_def"] = tagged_to_value(bd);
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

    /// Returns the value as a [`Sym`] if it is a nominal identity
    /// (ADR-0106 §2).
    pub fn as_sym(&self) -> Option<&Sym> {
        match self {
            TaggedValue::Sym(s) => Some(s),
            _ => None,
        }
    }

    /// Returns `true` if the value is a nominal identity (`Sym`).
    pub fn is_sym(&self) -> bool {
        matches!(self, TaggedValue::Sym(_))
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

// ---------------------------------------------------------------------------
// Nominal identity helpers (ADR-0106 §2 — sym / parent chain / instanceof)
// ---------------------------------------------------------------------------

/// Mint a fresh root nominal identity (`sym()` of ADR-0106 §2) as a
/// [`TaggedValue`].
pub fn sym(name: &str) -> TaggedValue {
    TaggedValue::Sym(Rc::new(Sym::fresh(name)))
}

/// Mint a fresh nominal identity with `parent` (a [`Sym`]) as its nominal
/// parent (`sym(A)` of ADR-0106 §2), as a [`TaggedValue`].
pub fn sym_with_parent(name: &str, parent: &Sym) -> TaggedValue {
    TaggedValue::Sym(Rc::new(Sym::fresh_with_parent(name, parent)))
}

/// Mint a fresh nominal identity whose parent is taken from a
/// [`TaggedValue`] (`sym(A)` where `A` arrives as a value).
///
/// Returns an error when `parent` is not a nominal (`Sym`) value —
/// matching the VM primitive's `sym(A)` contract: `A` must itself be a
/// nominal object.
pub fn sym_from_parent_value(name: &str, parent: &TaggedValue) -> Result<TaggedValue, String> {
    match parent {
        TaggedValue::Sym(p) => Ok(sym_with_parent(name, p)),
        _ => Err("sym: parent is not a nominal object".to_string()),
    }
}

/// Whether a [`TaggedValue`] is a nominal (`Sym`) value.
pub fn is_nominal(v: &TaggedValue) -> bool {
    matches!(v, TaggedValue::Sym(_))
}

/// The nominal parent of a value, or `None` if the value is not nominal or
/// is a root sym.
pub fn nominal_parent(v: &TaggedValue) -> Option<&Sym> {
    v.as_sym().and_then(|s| s.parent())
}

/// Strict descendant check over values: `true` iff both are nominal and
/// `v` is a strict descendant of `other`. Non-nominal operands yield
/// `false`.
pub fn is_descendant_of(v: &TaggedValue, other: &TaggedValue) -> bool {
    match (v.as_sym(), other.as_sym()) {
        (Some(a), Some(b)) => a.is_descendant_of(b),
        _ => false,
    }
}

/// Inclusive ancestor check over values (`instanceof` semantics): `true`
/// iff both are nominal and `v` equals `other` or descends from it.
/// Non-nominal operands yield `false`.
pub fn has_ancestor(v: &TaggedValue, other: &TaggedValue) -> bool {
    match (v.as_sym(), other.as_sym()) {
        (Some(a), Some(b)) => a.has_ancestor(b),
        _ => false,
    }
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
///
/// Recognizes both `TaggedValue::EitherLeft` and the
/// `{"__either__": "left", "value": v}` object encoding — the wire form
/// [`tagged_to_value`] emits and generated `object` nodes construct
/// directly (ADR-0120 fold machines).
pub fn is_either_left(v: &TaggedValue) -> bool {
    match v {
        TaggedValue::EitherLeft(_) => true,
        TaggedValue::Obj(map) => map.get("__either__").and_then(|s| s.as_str()) == Some("left"),
        _ => false,
    }
}

/// Whether an Either value is a `right`.
///
/// See [`is_either_left`] for the recognized encodings.
pub fn is_either_right(v: &TaggedValue) -> bool {
    match v {
        TaggedValue::EitherRight(_) => true,
        TaggedValue::Obj(map) => map.get("__either__").and_then(|s| s.as_str()) == Some("right"),
        _ => false,
    }
}

/// Extract the carried value from an Either (left or right).
///
/// See [`is_either_left`] for the recognized encodings.
pub fn either_value(v: &TaggedValue) -> Option<&TaggedValue> {
    match v {
        TaggedValue::EitherLeft(inner) | TaggedValue::EitherRight(inner) => Some(inner),
        TaggedValue::Obj(map)
            if map
                .get("__either__")
                .and_then(|s| s.as_str())
                .is_some_and(|s| s == "left" || s == "right") =>
        {
            map.get("value")
        }
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
        // Nominal identities are always truthy (a sym exists).
        TaggedValue::Sym(_) => true,
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
        // Nominal identity (ADR-0106 §2): handle-based identity equality,
        // not structural equality.
        (TaggedValue::Sym(x), TaggedValue::Sym(y)) => x == y,
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

/// `CellCompV(first, second)` — vertical cell composition `∘₁`.
/// Delegates to [`cell2_comp_axis`], which enforces the globular
/// boundary law `tgt(first) = src(second)`.
pub fn cell2_comp_v(first: &TaggedValue, second: &TaggedValue) -> Result<TaggedValue, String> {
    cell2_comp_axis(1, first, second)
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

/// Whether `cell` is an identity 2-cell: `Cell2{src, src, src}`.
pub fn cell2_is_id(cell: &TaggedValue) -> bool {
    let is_cell2 = cell.get("__tag__").and_then(|v| v.as_str()) == Some("Cell2");
    if !is_cell2 {
        return false;
    }
    let src = cell2_src(cell);
    src == cell2_tgt(cell) && cell.get("value") == Some(&src)
}

/// Axis-`k` composition of n-cells (n > k) at the value level
/// (ADR-0120 Phase 5).
///
/// `∘₀` on 2-cells is *horizontal* composition: source and target
/// boundaries compose pairwise as 1-cell `Arrow` records. `∘ₖ` for
/// `k ≥ 1` is *vertical* composition: the target of `first` meets the
/// source of `second` (`cell2_comp_v`). The non-identity operand supplies
/// the witness `value`, matching `cell2_whisker` behavior; when `second`
/// is an identity cell, `first`'s witness is kept.
///
/// The globular boundary law `tgtₖ(first) = srcₖ(second)` is enforced
/// for `k ≥ 1`: the `Cell2` record carries only its 1-cell boundaries
/// (`__src__`/`__tgt__`), so that is exactly the boundary the law is
/// representable along — the 0-boundaries (objects) are not part of the
/// value model, which is why `∘₀` is unchecked. Non-`Cell2` values are
/// degenerate cells whose whole value stands for both boundaries, so
/// e.g. `3 ∘₁ 3` composes while `1 ∘₁ 2` is rejected.
pub fn cell2_comp_axis(
    axis: u64,
    first: &TaggedValue,
    second: &TaggedValue,
) -> Result<TaggedValue, String> {
    if axis >= 1 && cell2_tgt(first) != cell2_src(second) {
        return Err(format!(
            "cell composition along axis {axis}: boundary mismatch — \
             tgt of the first cell does not equal src of the second"
        ));
    }
    let witness = if cell2_is_id(second) {
        first.get("value").cloned().unwrap_or_else(|| first.clone())
    } else {
        second
            .get("value")
            .cloned()
            .unwrap_or_else(|| second.clone())
    };
    Ok(match axis {
        0 => cell2(
            compose1(&cell2_src(first), &cell2_src(second)),
            compose1(&cell2_tgt(first), &cell2_tgt(second)),
            witness,
        ),
        _ => cell2(cell2_src(first), cell2_tgt(second), witness),
    })
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
