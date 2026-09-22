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
//! - [`TaggedValue::Arrow`] is the arrow-value variant matching the
//!   `{"__arrow__": true, "params": [...], "body_def": {...}}` shape used
//!   by the arrow-calculus `App` combinator — self-contained serializable
//!   data with no captured environment (ADR-0106).


use std::ffi::c_void;
use std::fmt;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::rc::Rc;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};

use rustc_hash::{FxHashMap, FxHashSet};
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
    /// Arrow value — the only computational form (ADR-0106 §3).
    ///
    /// An arrow is **self-contained serializable data**: no closures, no
    /// captured lexical environment, no process-local frame references.
    /// The JSON encoding is
    /// `{"__arrow__": true, "params": [...], "body_def": <tv>}` with
    /// `rest`/`array_pattern`/`binds`/`handlers` emitted only when set.
    ///
    /// - `body_def` carries the body as explicit structure — a tagged
    ///   `{"__ast__": <serialized Ast>}` value (see
    ///   `handl_language::ast_value`). At mint time every **free**
    ///   variable in the body is substituted with its definition-site
    ///   value (`Ast::instantiate`), so the body is a closed term
    ///   applicable without any environment.
    /// - `binds` is the residual explicit binding map: names the body
    ///   still references that cannot be substituted — `eval_rec`-region
    ///   binders (fixpoint semantics need the name free so each pass can
    ///   re-resolve it) and values that do not serialize (e.g.
    ///   `Resource`). Plain serializable data, bound into the call scope
    ///   before the params at application.
    /// - `handlers` carries handlers attached by `handle <arrow> with <h>`
    ///   (deep-handler carry, ADR-0076) as explicit data — reinstalled on
    ///   each application; replaces the old `env["__handlers__"]` channel.
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
        /// Whether the arrow's params are an array-destructuring pattern.
        array_pattern: bool,
        /// The arrow's body as explicit, serializable structure — a tagged
        /// `{"__ast__": <serialized Ast>}` value. Required: there is no
        /// process-local body fallback.
        body_def: Rc<TaggedValue>,
        /// Residual explicit bindings the substituted body still
        /// references (rec-region binders, non-serializable captures).
        /// Serialized as `"binds"` when non-empty — inline for unshared
        /// maps, `{"__bindsref__": <id>}` for `Rc`-shared ones (shared
        /// maps intern into a thread-local registry so a binds DAG does
        /// not expand exponentially).
        binds: Rc<FxHashMap<Rc<str>, TaggedValue>>,
        /// Handlers carried by deep-handler attach (ADR-0076), as data.
        /// Serialized inline as `"handlers"` when non-empty.
        handlers: Rc<[TaggedValue]>,
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
                array_pattern,
                body_def,
                binds,
                handlers,
            } => {
                10u8.hash(state);
                params.hash(state);
                rest.hash(state);
                array_pattern.hash(state);
                body_def.hash(state);
                hash_map_entries(binds.iter().map(|(k, v)| (k.as_ref(), v)), state);
                handlers.hash(state);
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
        let mut ctx = DeCtx::default();
        collect_binds_defs(&v, &mut ctx);
        tagged_from(v, &mut ctx)
    }
}

/// Decode a [`serde_json::Value`] into a [`TaggedValue`], threading the
/// document-local [`DeCtx`] so `__bindsref__` markers resolve to the
/// shared map their `__binds_id__` definition produced.
fn tagged_from(v: Value, ctx: &mut DeCtx) -> TaggedValue {
    match v {
        Value::Null => TaggedValue::Null,
        Value::Bool(b) => TaggedValue::Bool(b),
        Value::Number(n) => number_to_tagged(n),
        Value::String(s) => TaggedValue::Str(Rc::from(s)),
        Value::Array(a) => {
            let els: Vec<TaggedValue> = a
                .into_iter()
                .map(|v| tagged_from(v, ctx))
                .collect();
            TaggedValue::Arr(Rc::from(els))
        }
        Value::Object(o) => object_to_tagged(o, ctx),
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

fn object_to_tagged(o: Map<String, Value>, ctx: &mut DeCtx) -> TaggedValue {
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
                let a = tagged_from(arr[0].clone(), ctx);
                let b = tagged_from(arr[1].clone(), ctx);
                return TaggedValue::Pair(Rc::new((a, b)));
            }
        }
    }
    // Either: {"__either__": "left"|"right", "value": v}
    if let Some(side) = o.get("__either__").and_then(|v| v.as_str()) {
        let value = o.get("value").cloned().unwrap_or(Value::Null);
        let inner = tagged_from(value, ctx);
        return match side {
            "left" => TaggedValue::EitherLeft(Rc::new(inner)),
            "right" => TaggedValue::EitherRight(Rc::new(inner)),
            _ => {
                // Unknown side: fall back to a plain object.
                map_to_obj(o, ctx)
            }
        };
    }
    // Arrow value: {"__arrow__": true, "params": [...], "body_def": <tv>,
    // "rest"?: str, "array_pattern"?: bool, "binds"?: {...},
    // "handlers"?: [...]} — self-contained serializable data (ADR-0106).
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
        let rest = o.get("rest").and_then(|v| v.as_str()).map(Rc::from);
        let array_pattern = o
            .get("array_pattern")
            .and_then(|v| v.as_bool())
            .unwrap_or(false);
        let body_def = o
            .get("body_def")
            .map(|v| Rc::new(tagged_from(v.clone(), ctx)))
            .unwrap_or_else(|| Rc::new(TaggedValue::Null));
        let binds = match o.get("binds") {
            Some(v) => binds_from_json(v, ctx).unwrap_or_default(),
            _ => Rc::new(FxHashMap::default()),
        };
        let handlers: Rc<[TaggedValue]> = match o.get("handlers") {
            Some(Value::Array(a)) => Rc::from(
                a.iter()
                    .map(|v| tagged_from(v.clone(), ctx))
                    .collect::<Vec<_>>(),
            ),
            _ => Rc::from(Vec::<TaggedValue>::new()),
        };
        return TaggedValue::Arrow {
            params,
            rest,
            array_pattern,
            body_def,
            binds,
            handlers,
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
    map_to_obj(o, ctx)
}

fn map_to_obj(o: Map<String, Value>, ctx: &mut DeCtx) -> TaggedValue {
    TaggedValue::Obj(Rc::new(obj_map_to_hashmap(o, ctx)))
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

fn obj_map_to_hashmap(
    o: Map<String, Value>,
    ctx: &mut DeCtx,
) -> FxHashMap<Rc<str>, TaggedValue> {
    o.into_iter()
        .map(|(k, v)| (Rc::from(k), tagged_from(v, ctx)))
        .collect()
}

// ---------------------------------------------------------------------------
// Arrow-binds dedup — shared `binds` maps serialize by document-local ref
// ---------------------------------------------------------------------------

/// Encode context for [`tagged_to_value`]: dedups `Rc`-shared `binds`
/// maps so a binds DAG does not expand exponentially into JSON.
///
/// Sibling arrows in a rec region share `binds` maps whose entries hold
/// further arrows carrying their own binds — inlining expands the shared
/// DAG into an exponentially duplicated tree (the same blowup the
/// removed `__envref__` registry fixed for the old `env` field). A
/// shared map's *first* occurrence serializes inline with a
/// `"__binds_id__": <n>` marker; later occurrences emit
/// `{"__bindsref__": <n>}`. Refs always point backward in document order
/// (the DFS emitter visits the definition first), so the encoding is
/// self-contained — no process-local registry — preserving ADR-0106's
/// "arrow = self-contained serializable data" contract.
///
/// Unshared maps (`Rc` strong count 1) always serialize inline: they
/// cannot recur, so the plain-object form keeps the exact round-trip.
#[derive(Default)]
struct SerCtx {
    /// `Rc` pointer address → document-local id, for maps already
    /// emitted (as `__binds_id__` definitions) in this document.
    by_ptr: FxHashMap<usize, u64>,
    next: u64,
}

/// Decode context for [`TaggedValue::from`]/[`tagged_from`]: maps each
/// `__binds_id__` definition to its decoded `Rc` map so later
/// `__bindsref__` occurrences resolve to the same shared map.
///
/// `defs` holds the raw JSON of every `__binds_id__` definition in the
/// document, pre-collected by [`collect_binds_defs`] before decoding
/// starts. `serde_json::Map` iterates keys in sorted order, not encoding
/// order, so a `__bindsref__` can be visited before its definition —
/// refs resolve lazily out of `defs` regardless of document position.
/// `in_progress` marks definitions currently being decoded so a cyclic
/// binds graph terminates (the cyclic edge decodes to an empty map).
#[derive(Default)]
struct DeCtx {
    by_id: FxHashMap<u64, Rc<FxHashMap<Rc<str>, TaggedValue>>>,
    defs: FxHashMap<u64, Value>,
    in_progress: FxHashSet<u64>,
}

/// Pre-scan a document for `"__binds_id__"` definitions so
/// [`binds_from_json`] can resolve refs in any visitation order.
fn collect_binds_defs(v: &Value, ctx: &mut DeCtx) {
    match v {
        Value::Object(m) => {
            if let Some(id) = m.get("__binds_id__").and_then(|v| v.as_u64()) {
                ctx.defs.entry(id).or_insert_with(|| v.clone());
            }
            for value in m.values() {
                collect_binds_defs(value, ctx);
            }
        }
        Value::Array(a) => {
            for value in a {
                collect_binds_defs(value, ctx);
            }
        }
        _ => {}
    }
}

/// Decode an arrow's `"binds"` JSON field into the shared map:
/// `{"__bindsref__": <id>}` resolves the `__binds_id__` definition —
/// decoded on demand from the document-wide [`DeCtx::defs`] table so a
/// ref is valid no matter where in the document its definition sits;
/// `{"__binds_id__": <id>, ...entries}` decodes the entries and
/// registers them under `id`; a plain object is an ordinary inline map.
/// Returns `None` when `v` is not an object; an unresolvable ref yields
/// an empty map (the same default as a missing `binds` field).
fn binds_from_json(
    v: &Value,
    ctx: &mut DeCtx,
) -> Option<Rc<FxHashMap<Rc<str>, TaggedValue>>> {
    let m = v.as_object()?;
    if let Some(id) = m.get("__bindsref__").and_then(|v| v.as_u64()) {
        return Some(resolve_binds_ref(id, ctx));
    }
    let id = m.get("__binds_id__").and_then(|v| v.as_u64());
    let marked = id.is_some_and(|id| ctx.in_progress.insert(id));
    let rc = decode_binds_map(m, id, ctx);
    if marked {
        ctx.in_progress.remove(&id.unwrap());
    }
    Some(rc)
}

/// Resolve a `__bindsref__` id to its shared map: returns the already
/// decoded map when present, otherwise decodes the definition's raw JSON
/// from [`DeCtx::defs`] on demand. A ref to a definition currently being
/// decoded (a cyclic edge) or absent from the document yields an empty
/// map — `Rc<FxHashMap>` cannot express a forward/cyclic placeholder.
fn resolve_binds_ref(
    id: u64,
    ctx: &mut DeCtx,
) -> Rc<FxHashMap<Rc<str>, TaggedValue>> {
    if let Some(rc) = ctx.by_id.get(&id) {
        return Rc::clone(rc);
    }
    let Some(def) = ctx.defs.get(&id).cloned() else {
        return Rc::default();
    };
    if !ctx.in_progress.insert(id) {
        return Rc::default();
    }
    let rc = match def.as_object() {
        Some(m) => decode_binds_map(m, Some(id), ctx),
        None => Rc::default(),
    };
    ctx.in_progress.remove(&id);
    rc
}

/// Decode a binds object's entries (excluding the `__binds_id__`
/// marker) into a fresh `Rc` map, registering it under `id` when given.
fn decode_binds_map(
    m: &Map<String, Value>,
    id: Option<u64>,
    ctx: &mut DeCtx,
) -> Rc<FxHashMap<Rc<str>, TaggedValue>> {
    let map: FxHashMap<Rc<str>, TaggedValue> = m
        .iter()
        .filter(|(k, _)| k.as_str() != "__binds_id__")
        .map(|(k, v)| (Rc::from(k.as_str()), tagged_from(v.clone(), ctx)))
        .collect();
    let rc = Rc::new(map);
    if let Some(id) = id {
        ctx.by_id.insert(id, Rc::clone(&rc));
    }
    rc
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
    tagged_to_value_ctx(v, &mut SerCtx::default())
}

/// The recursive [`tagged_to_value`] body, threading the document-local
/// [`SerCtx`] so `Rc`-shared `binds` maps dedup into `__binds_id__` /
/// `__bindsref__` markers.
fn tagged_to_value_ctx(v: &TaggedValue, ctx: &mut SerCtx) -> Value {
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
                Some(p) => tagged_to_value_ctx(&TaggedValue::Sym(Rc::new(p.clone())), ctx),
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
        TaggedValue::Arr(a) => Value::Array(
            a.iter()
                .map(|v| tagged_to_value_ctx(v, ctx))
                .collect(),
        ),
        TaggedValue::Obj(o) => {
            let mut map = Map::new();
            for (k, val) in o.iter() {
                map.insert(k.to_string(), tagged_to_value_ctx(val, ctx));
            }
            Value::Object(map)
        }
        TaggedValue::Pair(p) => {
            serde_json::json!({"__pair__": [
                tagged_to_value_ctx(&p.0, ctx),
                tagged_to_value_ctx(&p.1, ctx),
            ]})
        }
        TaggedValue::EitherLeft(inner) => {
            serde_json::json!({"__either__": "left", "value": tagged_to_value_ctx(inner, ctx)})
        }
        TaggedValue::EitherRight(inner) => {
            serde_json::json!({"__either__": "right", "value": tagged_to_value_ctx(inner, ctx)})
        }
        TaggedValue::Arrow {
            params,
            rest,
            array_pattern,
            body_def,
            binds,
            handlers,
        } => {
            let mut v = serde_json::json!({
                "__arrow__": true,
                "params": params.iter().collect::<Vec<_>>(),
                "body_def": tagged_to_value_ctx(body_def, ctx),
            });
            if let Some(r) = rest {
                v["rest"] = Value::String(r.to_string());
            }
            if *array_pattern {
                v["array_pattern"] = Value::Bool(true);
            }
            if !binds.is_empty() {
                // Shared binds (`Rc` strong count > 1 — sibling arrows,
                // rec-region references) dedup into document-local refs:
                // first occurrence emits the map with a `__binds_id__`
                // marker, repeats emit `{"__bindsref__": id}`. Inlining
                // every occurrence would expand the shared DAG
                // exponentially. Unshared maps stay inline so the
                // self-contained round-trip is preserved.
                if Rc::strong_count(binds) > 1 {
                    let key = Rc::as_ptr(binds) as usize;
                    match ctx.by_ptr.get(&key) {
                        Some(id) => {
                            v["binds"] = serde_json::json!({"__bindsref__": id});
                        }
                        None => {
                            let id = ctx.next;
                            ctx.next += 1;
                            ctx.by_ptr.insert(key, id);
                            let mut map = Map::new();
                            map.insert(
                                "__binds_id__".to_string(),
                                Value::from(id),
                            );
                            for (k, val) in binds.iter() {
                                map.insert(
                                    k.to_string(),
                                    tagged_to_value_ctx(val, ctx),
                                );
                            }
                            v["binds"] = Value::Object(map);
                        }
                    }
                } else {
                    let mut map = Map::new();
                    for (k, val) in binds.iter() {
                        map.insert(k.to_string(), tagged_to_value_ctx(val, ctx));
                    }
                    v["binds"] = Value::Object(map);
                }
            }
            if !handlers.is_empty() {
                v["handlers"] = Value::Array(
                    handlers
                        .iter()
                        .map(|v| tagged_to_value_ctx(v, ctx))
                        .collect(),
                );
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
                array_pattern: ap1,
                body_def: d1,
                binds: e1,
                handlers: h1,
            },
            TaggedValue::Arrow {
                params: p2,
                rest: r2,
                array_pattern: ap2,
                body_def: d2,
                binds: e2,
                handlers: h2,
            },
        ) => {
            r1 == r2
                && ap1 == ap2
                && p1.len() == p2.len()
                && p1.iter().zip(p2.iter()).all(|(a, b)| a == b)
                && eq(d1, d2)
                && h1.len() == h2.len()
                && h1.iter().zip(h2.iter()).all(|(a, b)| eq(a, b))
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
// n-cell runtime helpers (ADR-0120 globular cell model; the ADR-0104b
// `Cell2` frontier shapes are the dimension-2 special case)
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

/// Build a `Cell` tagged record of dimension `n` — the generalized
/// globular shape `{__tag__: "Cell", __dim__: n, __src__, __tgt__,
/// value}` whose `__src__`/`__tgt__` are `(n-1)`-cells. `n == 2` keeps
/// the legacy `Cell2` record shape so existing consumers see unchanged
/// values; `n == 1` is not a record at all (1-cells are ordinary
/// values), so callers only invoke this for `n >= 2`.
fn mk_cell(n: u64, src: TaggedValue, tgt: TaggedValue, witness: TaggedValue) -> TaggedValue {
    if n == 2 {
        return cell2(src, tgt, witness);
    }
    let mut map = FxHashMap::with_capacity_and_hasher(5, Default::default());
    map.insert(Rc::from("__tag__"), TaggedValue::Str(Rc::from("Cell")));
    map.insert(Rc::from("__dim__"), TaggedValue::Int(n as i64));
    map.insert(Rc::from("__src__"), src);
    map.insert(Rc::from("__tgt__"), tgt);
    map.insert(Rc::from("value"), witness);
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

/// The globular dimension of a runtime cell value (ADR-0120).
///
/// A record carrying `__dim__` is an n-cell directly (`Cell` records and
/// surface-built `{__dim__: n, __src__, __tgt__, value}` literals); a
/// `Cell2` record is a 2-cell. A `dim_arrow` value
/// (`{__tag__: "Arrow", inputs, grade, output}` — the `f ~[n]~> g`
/// morphism) is an n-cell whose boundaries are `inputs`/`output` —
/// `grade` is its declared dimension — mirroring the type-level rule.
/// Every other value is a 1-cell: its own degenerate boundary.
pub fn cell_dim(v: &TaggedValue) -> u64 {
    if let Some(d) = nat(v.get("__dim__")) {
        return d.max(1);
    }
    match v.get("__tag__").and_then(|t| t.as_str()) {
        Some("Cell2") => 2,
        Some("Arrow") if v.get("inputs").is_some() && v.get("output").is_some() => {
            nat(v.get("grade")).unwrap_or(1).max(1)
        }
        _ => 1,
    }
}

/// A natural number read from a value slot (`__dim__`, `grade`, `axis`).
fn nat(v: Option<&TaggedValue>) -> Option<u64> {
    v.and_then(|v| v.as_f64())
        .filter(|n| *n >= 0.0 && n.fract() == 0.0)
        .map(|n| n as u64)
}

/// Whether `v` is a cell record — a value whose globular boundaries are
/// stored fields rather than the degenerate self-boundary.
fn is_cell(v: &TaggedValue) -> bool {
    if v.get("__dim__").is_some() || v.get("__src__").is_some() {
        return true;
    }
    match v.get("__tag__").and_then(|t| t.as_str()) {
        Some("Cell2") | Some("Cell") => true,
        Some("Arrow") => v.get("inputs").is_some() && v.get("output").is_some(),
        _ => false,
    }
}

/// `Src(cell)` — project the source boundary.
///
/// Cell records read `__src__`; a `dim_arrow` record
/// (`{__tag__: "Arrow", inputs, grade, output}`) reads `inputs`; an
/// `Arrow{first, second}` composite's source is `first`'s source. Any
/// other value is a degenerate cell — its own boundary.
pub fn cell_src(v: &TaggedValue) -> TaggedValue {
    if let Some(s) = v.get("__src__") {
        return s.clone();
    }
    if v.get("__tag__").and_then(|t| t.as_str()) == Some("Arrow") {
        if v.get("inputs").is_some() && v.get("output").is_some() {
            if let Some(i) = v.get("inputs") {
                return i.clone();
            }
        }
        if let Some(f) = v.get("first") {
            return cell_src(f);
        }
    }
    v.clone()
}

/// `Tgt(cell)` — project the target boundary; see [`cell_src`].
pub fn cell_tgt(v: &TaggedValue) -> TaggedValue {
    if let Some(t) = v.get("__tgt__") {
        return t.clone();
    }
    if v.get("__tag__").and_then(|t| t.as_str()) == Some("Arrow") {
        if v.get("inputs").is_some() && v.get("output").is_some() {
            if let Some(o) = v.get("output") {
                return o.clone();
            }
        }
        if let Some(s) = v.get("second") {
            return cell_tgt(s);
        }
    }
    v.clone()
}

/// The witness a cell record carries (`value` field); a degenerate cell
/// witnesses itself.
pub fn cell_witness(v: &TaggedValue) -> TaggedValue {
    v.get("value").cloned().unwrap_or_else(|| v.clone())
}

/// Whether `v` is an identity cell: a cell whose boundaries coincide and
/// whose witness is that shared boundary — `id_c` pastes as a unit.
/// Mirrors the legacy `cell2_is_id` rule for `Cell2` records.
pub fn cell_is_id(v: &TaggedValue) -> bool {
    if is_cell(v) {
        let src = cell_src(v);
        return src == cell_tgt(v) && cell_witness(v) == src;
    }
    v.get("__tag__").is_none() && v.get("value") == Some(v)
}

/// `CellId(arrow)` — wrap the arrow's result in an identity `Cell2`.
pub fn cell2_id(arrow: &TaggedValue) -> TaggedValue {
    cell2(arrow.clone(), arrow.clone(), arrow.clone())
}

/// `CellCompV(first, second)` — vertical cell composition `∘₁`.
/// Delegates to [`cell_comp_axis`] at declared dimension 2, which
/// enforces the globular boundary law `tgt(first) = src(second)`.
pub fn cell2_comp_v(first: &TaggedValue, second: &TaggedValue) -> Result<TaggedValue, String> {
    cell_comp_axis(1, 2, first, second)
}

/// `Src(cell)` — project the source 1-cell, falling back to the value itself.
pub fn cell2_src(cell: &TaggedValue) -> TaggedValue {
    cell_src(cell)
}

/// `Tgt(cell)` — project the target 1-cell, falling back to the value itself.
pub fn cell2_tgt(cell: &TaggedValue) -> TaggedValue {
    cell_tgt(cell)
}

/// `Whisker` — attach a 1-cell `arrow` to the left or right side of a 2-cell.
/// `side` is `"Left"` or `"Right"`.
pub fn cell2_whisker(side: &str, arrow: &TaggedValue, cell: &TaggedValue) -> TaggedValue {
    let src = cell_src(cell);
    let tgt = cell_tgt(cell);
    let value = cell_witness(cell);
    let (new_src, new_tgt) = if side == "Right" {
        (compose1(&src, arrow), compose1(&tgt, arrow))
    } else {
        (compose1(arrow, &src), compose1(arrow, &tgt))
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
    cell_is_id(cell)
}

/// Lift a cell of dimension `d` to an `n`-cell (`d <= n`) as the
/// iterated identity `id^(n-d)(v)`: each level wraps source, target, and
/// witness in the cell one dimension up. A 1-cell `v` lifted to a 3-cell
/// is `Cell3{Cell2{v,v,v}, Cell2{v,v,v}, Cell2{v,v,v}}`.
fn promote(v: &TaggedValue, n: u64) -> TaggedValue {
    let mut cur = v.clone();
    let mut d = cell_dim(v).max(1);
    while d < n {
        cur = mk_cell(d + 1, cur.clone(), cur.clone(), cur.clone());
        d += 1;
    }
    cur
}

/// The axis-`k` boundary of an n-cell `c` (`k < n`), on the `tgt`
/// (`true`) or `src` (`false`) side. `k == n - 1` reads `c`'s own
/// `__src__`/`__tgt__`; deeper axes live inside the `(n-1)`-cell
/// boundaries — globularity makes the source and target boundaries
/// agree on all lower axes, so recursing through `src` suffices.
fn boundary_at(k: u64, n: u64, c: &TaggedValue, tgt_side: bool) -> TaggedValue {
    debug_assert!(k < n);
    if k + 1 == n {
        if tgt_side {
            cell_tgt(c)
        } else {
            cell_src(c)
        }
    } else {
        boundary_at(k, n - 1, &cell_src(c), tgt_side)
    }
}

/// `∘ₖ` of two normalized n-cells (`k < n`): the globular pasting law.
///
/// The boundary law `tgtₖ(a) = srcₖ(b)` is checked first; then the
/// composite's k-boundaries are `srcₖ(a)`/`tgtₖ(b)` and every other axis
/// `j` pastes the operands' j-boundaries pairwise (`∘ₖ` applied one
/// dimension down), which recursively enforces the lower boundary laws.
///
/// The witness follows the legacy `Cell2` convention at every level:
/// the non-identity operand supplies its `value` (`second` wins unless
/// it is an identity cell — `α ∘ₖ id` keeps `α`'s witness, `id ∘ₖ α`
/// keeps `α`'s). `∘₀` on 1-cells (`n == 1`) is sequential 1-cell
/// composition — the `Arrow{first, second}` record.
fn comp_at(k: u64, n: u64, a: &TaggedValue, b: &TaggedValue, b_id: bool) -> Result<TaggedValue, String> {
    if n <= 1 {
        // `∘₀` on 1-cells: sequential/whiskering composition.
        return Ok(compose1(a, b));
    }
    // The globular boundary law `tgtₖ(a) = srcₖ(b)`. Axis 0 is exempt:
    // 0-boundaries (objects) are not part of the value model — the
    // legacy `Cell2` convention treats `∘₀` as unchecked horizontal
    // composition, and deeper axes check `k >= 1` only.
    if k > 0 {
        let tgt_a = boundary_at(k, n, a, true);
        let src_b = boundary_at(k, n, b, false);
        if tgt_a != src_b {
            return Err(format!(
                "cell composition along axis {k}: boundary mismatch — \
                 tgt_{k} of the first cell does not equal src_{k} of the second"
            ));
        }
    }
    let sa = cell_src(a);
    let sb = cell_src(b);
    let ta = cell_tgt(a);
    let tb = cell_tgt(b);
    let src = if k + 1 == n {
        sa
    } else {
        let b_id = cell_is_id(&sb);
        comp_at(k, n - 1, &sa, &sb, b_id)?
    };
    let tgt = if k + 1 == n {
        tb
    } else {
        let b_id = cell_is_id(&tb);
        comp_at(k, n - 1, &ta, &tb, b_id)?
    };
    let witness = if b_id {
        cell_witness(a)
    } else {
        cell_witness(b)
    };
    Ok(mk_cell(n, src, tgt, witness))
}

/// Axis-`k` composition of cells at the value level (ADR-0120): the
/// runtime realization of `Seq{axis}` (`>>>`/`>>>[k]`) and the steps of
/// [`cell_compose`].
///
/// `declared_dim` is the operands' *declared* dimension — the eval
/// scheme's static lift (the canonical `>>>[k]` scheme declares `2`, so
/// plain values paste as degenerate 2-cells). The *effective* dimension
/// is `max(declared_dim, cell_dim(a), cell_dim(b))`: a value carrying a
/// higher dimension (`Cell`/`__dim__`/`dim_arrow` records) pastes at its
/// own height, so `>>>[2]` runs on 3-cell values. `k >= n` is a
/// dimension error; `k < n` enforces the globular boundary law
/// `tgtₖ(first) = srcₖ(second)` and produces the n-cell composite.
pub fn cell_comp_axis(
    axis: u64,
    declared_dim: u64,
    first: &TaggedValue,
    second: &TaggedValue,
) -> Result<TaggedValue, String> {
    let n = declared_dim
        .max(cell_dim(first))
        .max(cell_dim(second))
        .max(1);
    if axis >= n {
        return Err(format!(
            "axis-{axis} composition requires cells of dimension > {axis} \
             (declared dimension {declared_dim})"
        ));
    }
    // The witness preference consults identity on the *declared*
    // operand: a degenerate value lifted by promotion is an identity
    // cell in shape but not in content — `1 ∘₀ 2` keeps `2` as witness,
    // matching the legacy `cell2_comp_axis` rule.
    let b_id = cell_is_id(second);
    let a = promote(first, n);
    let b = promote(second, n);
    comp_at(axis, n, &a, &b, b_id)
}

/// Axis-`k` composition of 2-cells (ADR-0120 Phase 5) — the legacy
/// spelling; equivalent to `cell_comp_axis(axis, 2, a, b)`.
///
/// `∘₀` on 2-cells is *horizontal* composition (boundaries compose
/// pairwise as 1-cell `Arrow` records); `∘ₖ` for `k ≥ 1` is *vertical*
/// composition. Non-`Cell2` values are degenerate cells whose whole
/// value stands for both boundaries, so e.g. `3 ∘₁ 3` composes while
/// `1 ∘₁ 2` is rejected.
pub fn cell2_comp_axis(
    axis: u64,
    first: &TaggedValue,
    second: &TaggedValue,
) -> Result<TaggedValue, String> {
    cell_comp_axis(axis, 2, first, second)
}

/// `compose(diagram)` — generalized pasting/Kan filling (ADR-0120): the
/// n-ary generalization of `Seq{axis}`.
///
/// `diagram` is an array of pasting steps. The first element seeds the
/// composite with a cell; each later step is `{axis: k, cell: c}` (a
/// bare cell means `axis: 0`; a `{cell: c}` record without `axis` pastes
/// along axis 0) and computes `acc ∘ₖ c`, enforcing the globular
/// boundary law `tgtₖ(acc) = srcₖ(c)` per step. Step cells carry their
/// own dimensions — a `Cell`/`__dim__` record pastes at its own height —
/// with the declared dimension floored at `2`, the same atom→2-cell lift
/// `>>>[k]` applies.
pub fn cell_compose(diagram: &TaggedValue) -> Result<TaggedValue, String> {
    let steps = diagram.as_array().ok_or_else(|| {
        "compose: pasting diagram must be an array of {axis, cell} steps".to_string()
    })?;
    let mut iter = steps.iter();
    let seed = iter
        .next()
        .ok_or_else(|| "compose: empty pasting diagram".to_string())?;
    let (_, mut acc) =
        compose_step(seed).map_err(|e| format!("compose step 0: {e}"))?;
    for (i, step) in iter.enumerate() {
        let (axis, cell) = compose_step(step)
            .map_err(|e| format!("compose step {}: {e}", i + 1))?;
        acc = cell_comp_axis(axis, 2, &acc, &cell)
            .map_err(|e| format!("compose step {}: {e}", i + 1))?;
    }
    Ok(acc)
}

/// Split a `compose` step into `(axis, cell)`: a record carrying a
/// `cell` field is `{axis?: k, cell: c}` (`axis` defaults to 0);
/// anything else is a bare cell pasting along axis 0.
fn compose_step(step: &TaggedValue) -> Result<(u64, TaggedValue), String> {
    if let Some(cell) = step.get("cell") {
        let axis = match step.get("axis") {
            None => 0,
            Some(a) => nat(Some(a))
                .ok_or_else(|| format!("compose: step axis must be a natural number, got {a:?}"))?,
        };
        Ok((axis, cell.clone()))
    } else {
        Ok((0, step.clone()))
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

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod cell_tests {
    use super::*;

    /// `Cell` record `{__tag__: "Cell", __dim__: 3, __src__, __tgt__, value}`.
    fn cell3(src: TaggedValue, tgt: TaggedValue, witness: TaggedValue) -> TaggedValue {
        mk_cell(3, src, tgt, witness)
    }

    fn int(n: i64) -> TaggedValue {
        TaggedValue::Int(n)
    }

    #[test]
    fn cell_dim_recognizes_cell_shapes() {
        assert_eq!(cell_dim(&int(7)), 1);
        assert_eq!(cell_dim(&cell2(int(1), int(2), int(9))), 2);
        assert_eq!(cell_dim(&cell3(int(1), int(2), int(9))), 3);
        // `dim_arrow` records (`f ~[n]~> g`) carry their dimension in `grade`.
        let arr = TaggedValue::from(serde_json::json!({
            "__tag__": "Arrow", "inputs": 1, "grade": 3, "output": 2
        }));
        assert_eq!(cell_dim(&arr), 3);
        // A `∘₀` composite (`Arrow{first, second}`) stays a 1-cell.
        assert_eq!(cell_dim(&compose1(&int(1), &int(2))), 1);
    }

    #[test]
    fn arrow_record_boundaries() {
        let arr = TaggedValue::from(serde_json::json!({
            "__tag__": "Arrow", "inputs": 1, "grade": 2, "output": 2
        }));
        assert_eq!(cell_src(&arr), int(1));
        assert_eq!(cell_tgt(&arr), int(2));
        // `Arrow{first, second}`: boundaries recurse to the ends of the chain.
        let comp = compose1(&int(3), &compose1(&int(4), &int(5)));
        assert_eq!(cell_src(&comp), int(3));
        assert_eq!(cell_tgt(&comp), int(5));
    }

    #[test]
    fn comp_axis1_atoms_is_legacy_cell2() {
        // `3 ∘₁ 3` — degenerate cells compose, producing the legacy Cell2.
        let c = cell2_comp_axis(1, &int(3), &int(3)).unwrap();
        assert_eq!(
            tagged_to_value(&c),
            serde_json::json!({"__tag__": "Cell2", "__src__": 3, "__tgt__": 3, "value": 3})
        );
        // `1 ∘₁ 2` — boundary mismatch.
        assert!(cell2_comp_axis(1, &int(1), &int(2)).unwrap_err().contains("boundary"));
    }

    #[test]
    fn comp_axis0_keeps_horizontal_shape() {
        // `a ∘₀ b` on 2-cells: boundaries compose pairwise as Arrow records.
        let a = cell2(int(1), int(2), int(10));
        let b = cell2(int(2), int(3), int(20));
        let c = cell_comp_axis(0, 2, &a, &b).unwrap();
        assert_eq!(cell_dim(&c), 2);
        assert_eq!(
            cell_src(&c),
            TaggedValue::from(serde_json::json!({"__tag__": "Arrow", "first": 1, "second": 2}))
        );
    }

    #[test]
    fn comp_axis2_pastes_3cells() {
        // `α ∘₂ β` on 3-cells: tgt₂(α) = src₂(β) required; the composite
        // is a `Cell{__dim__: 3}` whose boundaries are src₂(α)/tgt₂(β).
        let shared = cell2(int(1), int(2), int(5));
        let a = cell3(cell2(int(0), int(1), int(8)), shared.clone(), int(100));
        let b = cell3(shared.clone(), cell2(int(2), int(3), int(9)), int(200));
        let c = cell_comp_axis(2, 2, &a, &b).unwrap();
        assert_eq!(cell_dim(&c), 3);
        assert_eq!(cell_src(&c), cell2(int(0), int(1), int(8)));
        assert_eq!(cell_tgt(&c), cell2(int(2), int(3), int(9)));
        assert_eq!(cell_witness(&c), int(200));
        assert_eq!(
            c.get("__tag__").and_then(|t| t.as_str()),
            Some("Cell")
        );
    }

    #[test]
    fn comp_axis2_boundary_mismatch() {
        let a = cell3(cell2(int(0), int(1), int(8)), cell2(int(1), int(2), int(5)), int(1));
        let b = cell3(cell2(int(7), int(2), int(5)), cell2(int(2), int(3), int(9)), int(2));
        let err = cell_comp_axis(2, 2, &a, &b).unwrap_err();
        assert!(err.contains("boundary"), "got {err}");
    }

    #[test]
    fn comp_axis1_on_3cells_pastes_lower_boundaries() {
        // `∘₁` on 3-cells: the 1-boundary check `tgt₁(a) = src₁(b)`
        // compares whole 2-cells; the composite's other boundaries are
        // the `∘₁` of the operands' boundaries.
        let shared = cell2(int(1), int(2), int(5));
        let a = cell3(cell2(int(0), int(1), int(8)), shared.clone(), int(100));
        let b = cell3(shared.clone(), cell2(int(2), int(9), int(4)), int(200));
        let c = cell_comp_axis(1, 2, &a, &b).unwrap();
        assert_eq!(cell_dim(&c), 3);
        // src boundary: `Cell2{0,1,8} ∘₁ Cell2{1,2,5}` = Cell2{0,2,5}.
        assert_eq!(cell_src(&c), cell2(int(0), int(2), int(5)));
        // tgt boundary: `Cell2{1,2,5} ∘₁ Cell2{2,9,4}` = Cell2{1,9,4}.
        assert_eq!(cell_tgt(&c), cell2(int(1), int(9), int(4)));
    }

    #[test]
    fn comp_promotes_lower_dimensional_operands() {
        // A 2-cell pasted at axis 2 against a 3-cell lifts to `id` of
        // itself; the boundary law then applies at dimension 3.
        let c2 = cell2(int(1), int(2), int(5));
        let a = cell3(c2.clone(), c2.clone(), c2.clone());
        let b = cell3(c2.clone(), cell2(int(2), int(3), int(9)), int(7));
        let c = cell_comp_axis(2, 2, &a, &b).unwrap();
        assert_eq!(cell_dim(&c), 3);
        assert_eq!(cell_src(&c), c2);
    }

    #[test]
    fn comp_axis_at_dimension_errors() {
        // `k >= n` is a dimension error — 1-cells cannot paste at axis 1+.
        let err = cell_comp_axis(1, 1, &int(1), &int(1)).unwrap_err();
        assert!(err.contains("dimension"), "got {err}");
        let err = cell_comp_axis(2, 2, &int(1), &int(1)).unwrap_err();
        assert!(err.contains("dimension"), "got {err}");
    }

    #[test]
    fn compose_runs_pasting_diagram() {
        // `[c, {axis: 1, cell: d}]` = `c ∘₁ d`.
        let c = cell2(int(1), int(2), int(10));
        let d = cell2(int(2), int(3), int(20));
        let diagram = TaggedValue::from(serde_json::json!([
            {"__tag__": "Cell2", "__src__": 1, "__tgt__": 2, "value": 10},
            {"axis": 1, "cell": {"__tag__": "Cell2", "__src__": 2, "__tgt__": 3, "value": 20}},
        ]));
        let out = cell_compose(&diagram).unwrap();
        assert_eq!(out, cell2(int(1), int(3), int(20)));
        let _ = (c, d);

        // Multi-step: `c ∘₁ d ∘₁ e`.
        let diagram = TaggedValue::from(serde_json::json!([
            {"__tag__": "Cell2", "__src__": 1, "__tgt__": 2, "value": 10},
            {"axis": 1, "cell": {"__tag__": "Cell2", "__src__": 2, "__tgt__": 3, "value": 20}},
            {"axis": 1, "cell": {"__tag__": "Cell2", "__src__": 3, "__tgt__": 4, "value": 30}},
        ]));
        let out = cell_compose(&diagram).unwrap();
        assert_eq!(out, cell2(int(1), int(4), int(30)));
    }

    #[test]
    fn compose_at_axis2_and_step_errors() {
        let shared = cell2(int(1), int(2), int(5));
        let a = cell3(cell2(int(0), int(1), int(8)), shared.clone(), int(100));
        let b = cell3(shared, cell2(int(2), int(3), int(9)), int(200));
        let diagram = TaggedValue::Arr(Rc::from(vec![
            a.clone(),
            TaggedValue::from(serde_json::json!({"axis": 2, "cell":
                tagged_to_value(&b)})),
        ]));
        let out = cell_compose(&diagram).unwrap();
        assert_eq!(cell_dim(&out), 3);

        // A bad step reports its position.
        let bad = TaggedValue::from(serde_json::json!([
            {"__tag__": "Cell2", "__src__": 1, "__tgt__": 2, "value": 10},
            {"axis": 1, "cell": {"__tag__": "Cell2", "__src__": 9, "__tgt__": 3, "value": 20}},
        ]));
        let err = cell_compose(&bad).unwrap_err();
        assert!(err.contains("step 1") && err.contains("boundary"), "got {err}");

        // Non-array and empty diagrams reject cleanly.
        assert!(cell_compose(&int(1)).is_err());
        assert!(cell_compose(&TaggedValue::Arr(Rc::from(vec![]))).is_err());
    }
}
