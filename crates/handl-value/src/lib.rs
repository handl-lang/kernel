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
//! - [`TaggedValue::Tensor`] is a dense row-major `f64` tensor carried
//!   opaquely through host functions — the `{"__tensor__": {"shape",
//!   "data", "dtype": "f64"}}` wire form `host-tensor` uses.

pub mod nbe;

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
// TensorValue — dense row-major f64 tensor (the host-tensor wire payload)
// ---------------------------------------------------------------------------

/// A dense, row-major `f64` tensor — the payload of
/// [`TaggedValue::Tensor`].
///
/// Mirrors the `{"__tensor__": {"shape": [d, ...], "data": [x, ...],
/// "dtype": "f64"}}` wire form `host-tensor` emits across its `Function`
/// boundary: `shape` is the extent per axis (rank = `shape.len()`),
/// `data` the flat row-major payload with `data.len() == product(shape)`.
/// `dtype` is implicit — `"f64"` is the only element type this variant
/// carries.
///
/// Unlike [`ForeignResource`], a tensor is a *value*, not an opaque
/// handle: equality is structural over `shape` + `data` (elementwise
/// `f64` `==`, matching [`TaggedValue::Float`]'s comparison — so `0.0`
/// and `-0.0` compare equal and a `NaN` element makes a tensor unequal
/// to itself), and hashing agrees (elements hash as `f64` bits with
/// `-0.0` normalized to `+0.0`, since `0.0 == -0.0` but their bit
/// patterns differ).
#[derive(Clone, PartialEq)]
pub struct TensorValue {
    /// Extent per axis; `shape.len()` is the rank. An empty `shape` is a
    /// scalar tensor (one element).
    pub shape: Vec<usize>,
    /// Flat row-major payload; `data.len() == product(shape)`. `Rc`-
    /// backed so a value-preserving view/reshape can share storage.
    pub data: Rc<Vec<f64>>,
}

impl TensorValue {
    /// Construct a tensor, enforcing `data.len() == product(shape)`
    /// (the product is checked — shape extents whose product overflows
    /// `usize` are rejected).
    pub fn new(shape: Vec<usize>, data: Vec<f64>) -> Result<TensorValue, String> {
        let expected = shape.iter().try_fold(1usize, |acc, &d| acc.checked_mul(d));
        match expected {
            Some(n) if n == data.len() => Ok(TensorValue {
                shape,
                data: Rc::new(data),
            }),
            Some(n) => Err(format!(
                "tensor: data length {} does not match product of shape {shape:?} ({n})",
                data.len()
            )),
            None => Err(format!(
                "tensor: product of shape {shape:?} overflows usize"
            )),
        }
    }

    /// The rank (number of axes).
    pub fn rank(&self) -> usize {
        self.shape.len()
    }
}

impl fmt::Debug for TensorValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Compact debug: the payload can be large, so print the shape
        // and element count rather than every element.
        f.debug_struct("TensorValue")
            .field("shape", &self.shape)
            .field("len", &self.data.len())
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
/// "parent": <nested sym or null>, "type": <nested sym or null>}}` —
/// explicit data with no closures and no hidden state. Round-tripping
/// preserves the handle, so a deserialized sym compares equal to the live
/// sym it was serialized from (within a process; cross-process identity is
/// a follow-up ADR per ADR-0106).
///
/// # The two links (ADR-0154 §2)
///
/// Membership and subtyping are two links, not one chain:
///
/// - `parent` is the **subtyping** link: `T <: U` walks `parent`
///   (`Nat <: Int <: Number`). Read by `has_ancestor`/`is_descendant_of`.
/// - `ty` is the **membership** link: a value *that is itself a type*
///   carries `ty` → the nominal of its type (`Int.ty = Type`, i.e.
///   `Int : Type`). Ordinary member values carry their `type` link as an
///   object field instead (the `{"type": …}` field of ctor values) — it
///   lives on `Sym` only for nominals, which have no other carrier.
///
/// Neither link is part of identity: `PartialEq`/`Hash` compare handles.
#[derive(Clone, Debug)]
pub struct Sym {
    /// The unique nominal handle (identity). Minted from
    /// [`SYM_NEXT_HANDLE`] at construction; preserved by serialization.
    handle: u64,
    /// Display name — presentation only, never part of identity.
    name: Rc<str>,
    /// Optional nominal parent (also a `Sym`). Single parent, no cycles.
    /// The `<:` edge (ADR-0154 §2).
    parent: Option<Rc<Sym>>,
    /// Optional `type` link (also a `Sym`) — the membership edge: what
    /// this nominal is *a member of* when the nominal is used as a type
    /// value (`Int.ty = Type`). `None` for non-type nominals.
    ty: Option<Rc<Sym>>,
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
            ty: None,
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
            ty: None,
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

    /// The `type` link — what this nominal is a member of when used as a
    /// type value (`Int.ty = Type`; ADR-0154 §2). `None` for non-type
    /// nominals.
    pub fn ty(&self) -> Option<&Sym> {
        self.ty.as_deref()
    }

    /// Construct a sym from explicit parts — used by `seeded` in `nbe`
    /// for deterministic handles (hash of the qualified name) and by
    /// deserialization. Fresh minting goes through `fresh*`.
    pub fn from_parts(
        handle: u64,
        name: String,
        parent: Option<Rc<Sym>>,
        ty: Option<Rc<Sym>>,
    ) -> Sym {
        Sym {
            handle,
            name: Rc::from(name),
            parent,
            ty,
        }
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
/// - [`TaggedValue::Tensor`] is a dense row-major `f64` tensor — a
///   pass-through carrier for host tensor ops (the `{"__tensor__": …}`
///   wire form `host-tensor` uses), structurally equal by shape + data.
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
    /// A dense row-major `f64` tensor — an opaque-to-the-VM host value
    /// carried through host functions (engines never interpret it).
    ///
    /// The JSON encoding is
    /// `{"__tensor__": {"shape": [d, ...], "data": [x, ...],
    /// "dtype": "f64"}}` — the same wire form `host-tensor` produces and
    /// consumes, so values round-trip across the `Function` boundary.
    /// `dtype` is optional on decode but only `"f64"` is accepted; a
    /// malformed payload (non-array `shape`/`data`, a negative or
    /// non-integer extent, a `data` length other than `product(shape)`,
    /// or another `dtype`) falls back to a plain object, matching the
    /// lenient `__bytes__`/`__sym__` convention.
    ///
    /// A tensor is a *value*: equality and hashing are structural over
    /// `shape` + `data`, not pointer identity (contrast
    /// [`TaggedValue::Resource`]). See [`TensorValue`].
    Tensor(Rc<TensorValue>),
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
            TaggedValue::Tensor(t) => {
                13u8.hash(state);
                t.shape.hash(state);
                for x in t.data.iter() {
                    // Hash consistent with elementwise `==` equality:
                    // normalize -0.0 → +0.0 (0.0 == -0.0 but their bit
                    // patterns differ). NaN never compares equal, so its
                    // payload bits are unconstrained.
                    let bits = if *x == 0.0 {
                        0.0f64.to_bits()
                    } else {
                        x.to_bits()
                    };
                    bits.hash(state);
                }
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
            let els: Vec<TaggedValue> = a.into_iter().map(|v| tagged_from(v, ctx)).collect();
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
    // Tensor: {"__tensor__": {"shape": [d, ...], "data": [x, ...],
    // "dtype"?: "f64"}} — a dense row-major f64 tensor, the host-tensor
    // wire form. Malformed payloads (bad dtype, non-integer extents, a
    // data length that is not product(shape)) fall back to a plain
    // object, matching the lenient `__bytes__`/`__sym__` style.
    if let Some(t) = o
        .get("__tensor__")
        .and_then(|v| v.as_object())
        .and_then(tensor_from_json)
    {
        return t;
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

/// Decode an optional nested sym link (`parent`/`type` in the `__sym__`
/// payload): `null`/absent → `None`, a `{"__sym__": {...}}` encoding →
/// the nested sym, anything else is malformed (`Err`).
fn sym_link_from_json(v: Option<&Value>) -> Result<Option<Rc<Sym>>, ()> {
    match v {
        None | Some(Value::Null) => Ok(None),
        // The encoder nests the link target as a full {"__sym__": {...}}
        // value; unwrap the wrapper before recursing.
        Some(Value::Object(obj)) => {
            let inner = obj
                .get("__sym__")
                .and_then(|v| v.as_object())
                .ok_or(())?;
            match sym_from_json(inner) {
                Some(TaggedValue::Sym(s)) => Ok(Some(s)),
                _ => Err(()),
            }
        }
        Some(_) => Err(()),
    }
}

/// Decode the inner payload of a `{"__sym__": {...}}` JSON object into a
/// nominal [`TaggedValue`]. Returns `None` when the payload is malformed
/// (missing/invalid `handle` or `name`, or a `parent`/`type` link that is
/// not itself a sym encoding or `null`), so the caller can fall back to a
/// plain object.
fn sym_from_json(sym_val: &Map<String, Value>) -> Option<TaggedValue> {
    let handle = sym_val.get("handle").and_then(|v| v.as_u64())?;
    if handle == 0 {
        return None;
    }
    let name = sym_val.get("name").and_then(|v| v.as_str())?;
    let parent = sym_link_from_json(sym_val.get("parent")).ok()?;
    // The `type` link (ADR-0154 §2): same nested-sym encoding as
    // `parent`; absent in pre-0154 payloads → `None`. Lenient: a `type`
    // payload that is not a sym encoding (e.g. a `{"__former__": …}` or
    // `{"__type__": i}` link written by another layer) is ignored rather
    // than poisoning the whole nominal — `Sym::ty` models nominal links
    // only.
    let ty = sym_link_from_json(sym_val.get("type")).ok().flatten();
    let sym = Sym {
        handle,
        name: Rc::from(name),
        parent,
        ty,
    };
    Some(TaggedValue::Sym(Rc::new(sym)))
}

/// Decode the inner payload of a `{"__tensor__": {...}}` JSON object into
/// a [`TaggedValue::Tensor`]. Returns `None` when the payload is
/// malformed — a `dtype` present but not `"f64"`, a non-array `shape` or
/// `data`, a negative/non-integer/`usize`-overflowing extent, a
/// non-numeric element, or a `data` length that is not `product(shape)` —
/// so the caller falls back to a plain object (the lenient `__bytes__`
/// convention). `dtype` is optional on decode, matching `host-tensor`'s
/// `decode_tensor`.
fn tensor_from_json(inner: &Map<String, Value>) -> Option<TaggedValue> {
    if let Some(dtype) = inner.get("dtype") {
        if dtype.as_str() != Some("f64") {
            return None;
        }
    }
    let shape: Vec<usize> = inner
        .get("shape")?
        .as_array()?
        .iter()
        .map(|d| d.as_u64().and_then(|n| usize::try_from(n).ok()))
        .collect::<Option<_>>()?;
    let data: Vec<f64> = inner
        .get("data")?
        .as_array()?
        .iter()
        .map(|x| x.as_f64())
        .collect::<Option<_>>()?;
    TensorValue::new(shape, data)
        .ok()
        .map(|t| TaggedValue::Tensor(Rc::new(t)))
}

fn obj_map_to_hashmap(o: Map<String, Value>, ctx: &mut DeCtx) -> FxHashMap<Rc<str>, TaggedValue> {
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
///
/// Serialization-scoped base for `__binds_id__` numbering.
///
/// Ids must be unique across a *decoded* document, and one document can
/// embed values that were serialized separately -- a module's bindings are
/// serialized once and later embedded in a module record -- each starting
/// its own numbering at 0. Colliding ids make a `__bindsref__` resolve to
/// the wrong definition, which is how an arrow ends up carrying *another*
/// arrow's binds (its `body_def` from one arrow, its `binds` from
/// another). A process-wide counter keeps ids unique across
/// serializations; ids are opaque `u64` labels in the JSON.
static BINDS_ID_BASE: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// Ids are handed out in blocks of this size, one block per serialization.
const BINDS_ID_STRIDE: u64 = 1 << 32;

#[derive(Default)]
struct SerCtx {
    /// `Rc` pointer address → document-local id, for maps already
    /// emitted (as `__binds_id__` definitions) in this document.
    by_ptr: FxHashMap<usize, u64>,
    /// The maps `by_ptr` is keyed by, held for the whole document.
    ///
    /// A bare address is only unique while the allocation lives: if an
    /// earlier arrow's `Rc` is dropped mid-document, the allocator can
    /// hand the same address to a *different* binds map, which then
    /// serializes as a `__bindsref__` to the first one's id — the arrow
    /// decodes with another arrow's binds (its `body_def` from one arrow,
    /// its `binds` from another). Keeping the `Rc`s alive makes the
    /// address a stable identity for the duration.
    keep_alive: Vec<Rc<FxHashMap<Rc<str>, TaggedValue>>>,
    next: u64,
}

impl SerCtx {
    /// A context whose `__binds_id__` numbering starts in a fresh block, so
    /// its ids never collide with another serialization's (see
    /// [`BINDS_ID_BASE`]).
    fn new() -> Self {
        Self {
            next: BINDS_ID_BASE.fetch_add(BINDS_ID_STRIDE, std::sync::atomic::Ordering::Relaxed),
            ..Self::default()
        }
    }
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
fn binds_from_json(v: &Value, ctx: &mut DeCtx) -> Option<Rc<FxHashMap<Rc<str>, TaggedValue>>> {
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
fn resolve_binds_ref(id: u64, ctx: &mut DeCtx) -> Rc<FxHashMap<Rc<str>, TaggedValue>> {
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

/// Self-reference marker — installed into a self-recursive arrow's
/// `binds` under its own bound name (e.g. `alen := (xs) ~> …alen…`).
///
/// `binds` is an immutable `Rc` snapshot taken at mint time, before the
/// bound name's own value exists, so a `name → itself` entry cannot be
/// constructed cyclically. Instead the binding site stores this marker
/// and the apply site (`apply_arrow_body`) re-seeds the name with the
/// arrow value being applied, which resolves self-calls at any depth.
/// The marker is plain serializable data so a serialized arrow keeps
/// working after a JSON round-trip.
pub fn self_ref_marker() -> TaggedValue {
    let mut m = FxHashMap::default();
    m.insert(
        Rc::from("__tag__"),
        TaggedValue::Str(Rc::from("__self_ref__")),
    );
    TaggedValue::Obj(Rc::new(m))
}

/// Whether `v` is the self-reference marker installed by
/// [`self_ref_marker`].
pub fn is_self_ref_marker(v: &TaggedValue) -> bool {
    matches!(v, TaggedValue::Obj(m)
        if m.get("__tag__").and_then(|t| t.as_str()) == Some("__self_ref__"))
}

/// Install the self-reference marker into an arrow's `binds` under
/// `name`. Used by binding sites (`:=`/`=`/`bind`) whose right-hand side
/// references the name being bound. No-op for non-arrow values.
pub fn with_self_ref_bind(value: &TaggedValue, name: &str) -> TaggedValue {
    if let TaggedValue::Arrow {
        params,
        rest,
        array_pattern,
        body_def,
        binds,
        handlers,
    } = value
    {
        let mut m = (**binds).clone();
        m.insert(Rc::from(name), self_ref_marker());
        TaggedValue::Arrow {
            params: params.clone(),
            rest: rest.clone(),
            array_pattern: *array_pattern,
            body_def: body_def.clone(),
            binds: Rc::new(m),
            handlers: handlers.clone(),
        }
    } else {
        value.clone()
    }
}

/// Convert a [`TaggedValue`] into a [`serde_json::Value`].
///
/// This borrows the value (cloning the inner data as needed) so it can be
/// used for both `From<TaggedValue>` and reference-based conversions.
pub fn tagged_to_value(v: &TaggedValue) -> Value {
    tagged_to_value_ctx(v, &mut SerCtx::new())
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
            // identity), name (presentation), and the `parent` (`<:`)
            // and `type` (membership) links nested inline (ADR-0154 §2).
            // The nested encoding keeps the value self-contained
            // (O(depth) per sym; chains in this kernel are short).
            let parent = match s.parent() {
                Some(p) => tagged_to_value_ctx(&TaggedValue::Sym(Rc::new(p.clone())), ctx),
                None => Value::Null,
            };
            let ty = match s.ty() {
                Some(t) => tagged_to_value_ctx(&TaggedValue::Sym(Rc::new(t.clone())), ctx),
                None => Value::Null,
            };
            serde_json::json!({
                "__sym__": {
                    "handle": s.handle(),
                    "name": s.name(),
                    "parent": parent,
                    "type": ty,
                }
            })
        }
        TaggedValue::Bytes(b) => bytes_to_value(b),
        TaggedValue::Arr(a) => {
            Value::Array(a.iter().map(|v| tagged_to_value_ctx(v, ctx)).collect())
        }
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
                            // Pin the map: the address is the identity, so
                            // it must not be freed and reused by another
                            // map while this document is being written.
                            ctx.keep_alive.push(Rc::clone(binds));
                            let mut map = Map::new();
                            map.insert("__binds_id__".to_string(), Value::from(id));
                            for (k, val) in binds.iter() {
                                map.insert(k.to_string(), tagged_to_value_ctx(val, ctx));
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
        TaggedValue::Tensor(t) => {
            // The host-tensor wire form: `{"__tensor__": {"shape": [...],
            // "data": [...], "dtype": "f64"}}`. serde_json renders
            // non-finite floats as `null` (matching `Float`'s encoding);
            // such a payload then decodes as a plain object rather than
            // a `Tensor`, the same graceful degradation `Float(NaN)` →
            // `Null` already applies.
            serde_json::json!({
                "__tensor__": {
                    "shape": t.shape,
                    "data": t.data.as_slice(),
                    "dtype": "f64",
                }
            })
        }
    }
}

// ---------------------------------------------------------------------------
// Process-boundary check
// ---------------------------------------------------------------------------

/// Verify a serialized [`serde_json::Value`] document is safe to send past
/// a process boundary — a file write, network send, or foreign consumer
/// that cannot see this process's decode context.
///
/// [`tagged_to_value`] output is self-contained within one document, so
/// in-process round-trips through [`TaggedValue::from`] never need this.
/// Call it at egress points before the document leaves. It rejects:
///
/// - `{"__envref__": <id>}` — the removed process-local env registry.
///   The `env` field it referenced is ignored on decode, so a persisted
///   document silently loses the closure environment.
/// - `{"__bindsref__": <id>}` with no `{"__binds_id__": <id>}` definition
///   in the same document — a dangling document-local ref (e.g. a subtree
///   extracted from a larger document); decode resolves it to an empty
///   binds map.
/// - `{"__resource__": {"ptr": <n>}}` — a raw process-local pointer; in
///   another run it decodes to a dangling [`ForeignResource`].
/// - `{"__compiled__": <id>}` — a compiled-program handle whose artifact
///   lives in this process's `COMPILED_REGISTRY` (`handl-runtime`'s
///   `COMPILED_VALUE_KEY`; spelled out here because the registry crate
///   depends on this one, not the reverse). In another process the id
///   indexes an empty or unrelated registry.
///
/// Returns `Err` describing the first offending reference found.
pub fn check_portable(v: &Value) -> Result<(), String> {
    let mut defs = FxHashSet::default();
    collect_binds_ids(v, &mut defs);
    check_portable_refs(v, &defs)
}

/// Pre-pass: collect every `__binds_id__` definition id in the document.
fn collect_binds_ids(v: &Value, defs: &mut FxHashSet<u64>) {
    match v {
        Value::Object(m) => {
            if let Some(id) = m.get("__binds_id__").and_then(|v| v.as_u64()) {
                defs.insert(id);
            }
            for val in m.values() {
                collect_binds_ids(val, defs);
            }
        }
        Value::Array(a) => {
            for val in a {
                collect_binds_ids(val, defs);
            }
        }
        _ => {}
    }
}

fn check_portable_refs(v: &Value, defs: &FxHashSet<u64>) -> Result<(), String> {
    match v {
        Value::Object(m) => {
            if let Some(id) = m.get("__envref__") {
                return Err(format!(
                    "__envref__ {id}: process-local env registry reference cannot cross a \
                     process boundary (the registry no longer exists; decode drops it silently)"
                ));
            }
            if let Some(id) = m.get("__bindsref__").and_then(|v| v.as_u64()) {
                if !defs.contains(&id) {
                    return Err(format!(
                        "__bindsref__ {id}: dangling document-local reference (no __binds_id__ \
                         definition in this document)"
                    ));
                }
            }
            if let Some(res) = m.get("__resource__") {
                if res.get("ptr").and_then(|v| v.as_i64()).is_some() {
                    return Err(
                        "__resource__: process-local pointer cannot cross a process boundary \
                         (decodes to a dangling foreign resource)"
                            .to_string(),
                    );
                }
            }
            if let Some(id) = m.get("__compiled__").and_then(|v| v.as_u64()) {
                return Err(format!(
                    "__compiled__ {id}: compiled-program handle cannot cross a process \
                     boundary (the artifact lives in this process's COMPILED_REGISTRY)"
                ));
            }
            for val in m.values() {
                check_portable_refs(val, defs)?;
            }
            Ok(())
        }
        Value::Array(a) => {
            for val in a {
                check_portable_refs(val, defs)?;
            }
            Ok(())
        }
        _ => Ok(()),
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

    /// Returns the value as a [`TensorValue`] reference if it is a
    /// `Tensor` (dense row-major `f64` host value).
    pub fn as_tensor(&self) -> Option<&TensorValue> {
        match self {
            TaggedValue::Tensor(t) => Some(t),
            _ => None,
        }
    }

    /// Returns `true` if the value is a `Tensor`.
    pub fn is_tensor(&self) -> bool {
        matches!(self, TaggedValue::Tensor(_))
    }

    /// Returns `true` if the value is a nominal identity (`Sym`).
    pub fn is_sym(&self) -> bool {
        matches!(self, TaggedValue::Sym(_))
    }

    /// The object a value *presents* for `.hnl` read-projection — the
    /// generic seam over the tagged encodings (ADR-0083 §2.1).
    ///
    /// `Obj` is its own view (an `Rc` clone, O(1)). The *opaque* variants
    /// — values with no other eval-vocabulary destructure — project their
    /// canonical `{"__x__": …}` wire record as a plain object:
    /// `Tensor` → `{"__tensor__": {shape, data, dtype}}`,
    /// `Bytes` → `{"__bytes__": [n, …]}`,
    /// `Sym` → `{"__sym__": {handle, name, parent, type}}`,
    /// `Resource` → `{"__resource__": {ptr}}`. This is the same shape
    /// [`tagged_to_value`] emits for the boundary, so field access,
    /// `has_field`, and record destructuring read an opaque value
    /// exactly as they read a `.hnl`-authored record with the same
    /// encoding — the two are the same *value* on the wire, and now the
    /// same observation in the language.
    ///
    /// Variants that already carry `.hnl`-visible projections
    /// (`Pair`, `Either`, `Arrow`, and every scalar kind) return `None`:
    /// their wire encoding is serialization data, not an object view.
    ///
    /// The view is *read-only*: it materializes a fresh `Obj` (the
    /// `Tensor`/`Bytes`/`Sym`/`Resource` arms allocate), so a program
    /// that writes through it produces a plain record — losing
    /// variant-ness — exactly like destructuring the wire form.
    pub fn object_view(&self) -> Option<TaggedValue> {
        match self {
            TaggedValue::Obj(_) => Some(self.clone()),
            TaggedValue::Tensor(t) => {
                let mut inner = FxHashMap::default();
                inner.insert(
                    Rc::from("shape"),
                    TaggedValue::Arr(Rc::from(
                        t.shape
                            .iter()
                            .map(|&d| TaggedValue::Int(d as i64))
                            .collect::<Vec<_>>(),
                    )),
                );
                inner.insert(
                    Rc::from("data"),
                    TaggedValue::Arr(Rc::from(
                        t.data
                            .iter()
                            .map(|&x| TaggedValue::Float(x))
                            .collect::<Vec<_>>(),
                    )),
                );
                inner.insert(Rc::from("dtype"), TaggedValue::Str(Rc::from("f64")));
                let mut outer = FxHashMap::default();
                outer.insert(
                    Rc::from("__tensor__"),
                    TaggedValue::Obj(Rc::new(inner)),
                );
                Some(TaggedValue::Obj(Rc::new(outer)))
            }
            TaggedValue::Bytes(b) => {
                let mut outer = FxHashMap::default();
                outer.insert(
                    Rc::from("__bytes__"),
                    TaggedValue::Arr(Rc::from(
                        b.iter()
                            .map(|&byte| TaggedValue::Int(byte as i64))
                            .collect::<Vec<_>>(),
                    )),
                );
                Some(TaggedValue::Obj(Rc::new(outer)))
            }
            TaggedValue::Sym(s) => {
                let mut inner = FxHashMap::default();
                inner.insert(
                    Rc::from("handle"),
                    TaggedValue::Int(s.handle() as i64),
                );
                inner.insert(
                    Rc::from("name"),
                    TaggedValue::Str(Rc::from(s.name())),
                );
                let link_view = |link: Option<&Sym>| {
                    link.map(|p| {
                        TaggedValue::Sym(Rc::new(p.clone()))
                            .object_view()
                            .unwrap_or(TaggedValue::Null)
                    })
                    .unwrap_or(TaggedValue::Null)
                };
                inner.insert(Rc::from("parent"), link_view(s.parent()));
                inner.insert(Rc::from("type"), link_view(s.ty()));
                let mut outer = FxHashMap::default();
                outer.insert(Rc::from("__sym__"), TaggedValue::Obj(Rc::new(inner)));
                Some(TaggedValue::Obj(Rc::new(outer)))
            }
            TaggedValue::Resource(r) => {
                let mut inner = FxHashMap::default();
                inner.insert(
                    Rc::from("ptr"),
                    TaggedValue::Int(r.ptr as usize as i64),
                );
                let mut outer = FxHashMap::default();
                outer.insert(
                    Rc::from("__resource__"),
                    TaggedValue::Obj(Rc::new(inner)),
                );
                Some(TaggedValue::Obj(Rc::new(outer)))
            }
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

/// Construct a `Tensor` value from a `shape` (extent per axis) and a
/// flat row-major `f64` payload — the [`TensorValue`] invariant
/// `data.len() == product(shape)` is enforced (see [`TensorValue::new`]).
pub fn tensor(shape: Vec<usize>, data: Vec<f64>) -> Result<TaggedValue, String> {
    TensorValue::new(shape, data).map(|t| TaggedValue::Tensor(Rc::new(t)))
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

// ---------------------------------------------------------------------------
// Seeded minting + the builtin `type.*` nominal graph (ADR-0154 §1/§2)
// ---------------------------------------------------------------------------

/// Mint (or recall) the seeded nominal for `seed` — the deterministic
/// `sym("name")` surface form of ADR-0154 §1. Idempotent; the handle is a
/// content hash of `seed`.
pub fn sym_seeded(seed: &str) -> TaggedValue {
    TaggedValue::Sym(Sym::seeded(seed))
}

/// Mint (or recall) the seeded nominal for `seed` with `parent`/`ty`
/// links taken from values (`sym("seed", parent, ty)` — `null` for an
/// absent link). Errors when a link argument is neither a nominal nor
/// null.
pub fn sym_seeded_with_links(
    seed: &str,
    parent: &TaggedValue,
    ty: &TaggedValue,
) -> Result<TaggedValue, String> {
    let link = |v: &TaggedValue, what: &str| -> Result<Option<Rc<Sym>>, String> {
        match v {
            TaggedValue::Sym(s) => Ok(Some(s.clone())),
            TaggedValue::Null => Ok(None),
            _ => Err(format!("sym: {what} is not a nominal object")),
        }
    };
    let parent = link(parent, "parent")?;
    let ty = link(ty, "type")?;
    Ok(TaggedValue::Sym(Sym::seeded_with_links(
        seed,
        parent.as_deref(),
        ty.as_deref(),
    )))
}

/// The canonical builtin `type.*` nominal graph — data, not code
/// (ADR-0154 §1/§2). Each row is `(seed, parent_seed, type_seed)`:
/// `parent` is the `<:` edge, `type` the membership edge (every declared
/// type is a member of `Type`). The `parent` graph encodes
/// `Nat <: Int <: Number <: Value`, `Float <: Number`, and every other
/// builtin type directly under `Value` (the top).
///
/// Seeds are the qualified *declared* names (`type.Int`), matching the
/// `data.<DeclName>` former convention — identity, so every engine that
/// mints or reads these nominals agrees on the seed spelling.
pub const BUILTIN_TYPE_GRAPH: &[(&str, Option<&str>, Option<&str>)] = &[
    ("type.Value", None, Some("type.Type")),
    ("type.Type", None, Some("type.Type")),
    ("type.Number", Some("type.Value"), Some("type.Type")),
    ("type.Int", Some("type.Number"), Some("type.Type")),
    ("type.Float", Some("type.Number"), Some("type.Type")),
    ("type.Nat", Some("type.Int"), Some("type.Type")),
    ("type.Str", Some("type.Value"), Some("type.Type")),
    ("type.Bool", Some("type.Value"), Some("type.Type")),
    ("type.Null", Some("type.Value"), Some("type.Type")),
    ("type.Obj", Some("type.Value"), Some("type.Type")),
    ("type.Array", Some("type.Value"), Some("type.Type")),
    ("type.Bytes", Some("type.Value"), Some("type.Type")),
    ("type.Arrow", Some("type.Value"), Some("type.Type")),
    ("type.Resource", Some("type.Value"), Some("type.Type")),
    ("type.Unit", Some("type.Value"), Some("type.Type")),
    ("type.Grade", None, Some("type.Type")),
];

/// Seed the whole [`BUILTIN_TYPE_GRAPH`] — idempotent, cheap (one memo
/// pass per call after the first). Every entry point that mints or reads
/// a builtin `type.*` nominal calls this first so `parent`/`type` links
/// exist regardless of mint order (`seeded_with_links` upgrades a bare
/// memoized sym in place, preserving its handle).
pub fn ensure_builtin_type_nominals() {
    for &(seed, parent, ty) in BUILTIN_TYPE_GRAPH {
        let parent = parent.map(Sym::seeded);
        let ty = ty.map(Sym::seeded);
        Sym::seeded_with_links(seed, parent.as_deref(), ty.as_deref());
    }
}

/// The seeded nominal for a builtin `type.*` seed — e.g.
/// `builtin_type("type.Int")`. The full graph is ensured first so the
/// returned sym carries its `parent`/`type` links.
pub fn builtin_type(seed: &str) -> TaggedValue {
    ensure_builtin_type_nominals();
    sym_seeded(seed)
}

/// The canonical `type.*` seed a scalar literal defaults to
/// (ADR-0154 §5): an integer literal's constrained meta defaults to
/// `Nat` (negative mints resolve to `Int` — `Nat`'s domain), a fraction
/// literal to `Float`; other scalars to their kind nominal.
fn literal_type_seed(v: &TaggedValue) -> &'static str {
    match v {
        TaggedValue::Int(i) if *i < 0 => "type.Int",
        TaggedValue::Int(_) => "type.Nat",
        TaggedValue::Float(_) => "type.Float",
        TaggedValue::Str(_) => "type.Str",
        TaggedValue::Bool(_) => "type.Bool",
        TaggedValue::Null => "type.Null",
        TaggedValue::Arr(_) => "type.Array",
        TaggedValue::Bytes(_) => "type.Bytes",
        TaggedValue::Arrow { .. } => "type.Arrow",
        TaggedValue::Resource(_) => "type.Resource",
        // Pair/Either/Tensor/plain objects all present as objects at the
        // boundary — the coarse kind nominal until product/sum/tensor
        // formers exist.
        _ => "type.Obj",
    }
}

/// The `type.*` seed a legacy `__tag__` string bridges to
/// (ADR-0106 migration note, extended by ADR-0154): a datum whose
/// `__tag__` is a builtin type tag has the seeded nominal as its type.
/// Unknown tags bridge to `None` — they keep the plain-object read.
fn legacy_type_seed(tag: &str) -> Option<&'static str> {
    Some(match tag {
        "int" => "type.Int",
        "nat" => "type.Nat",
        "float" => "type.Float",
        "number" => "type.Number",
        "str" | "string" => "type.Str",
        "bool" => "type.Bool",
        "null" => "type.Null",
        "obj" | "object" => "type.Obj",
        "array" => "type.Array",
        "bytes" => "type.Bytes",
        "arrow" | "function" => "type.Arrow",
        "resource" => "type.Resource",
        "unit" => "type.Unit",
        "value" | "any" => "type.Value",
        "type" => "type.Type",
        "grade" => "type.Grade",
        _ => return None,
    })
}

/// The standard nominal roles a legacy `__tag__` datum satisfies —
/// nearest first. Kept for the name-based bridge: pre-seeding nominals
/// are anonymous or hand-minted, so `instanceof` over them matched the
/// queried nominal's *presentation name* against this table.
/// `legacy_type_seed` + the real `parent` walk subsumes it for seeded
/// nominals; this table stays only for name-matched (unseeded) nominals
/// until `__tag__` deletion lands.
fn legacy_tag_roles(tag: &str) -> Option<&'static [&'static str]> {
    match tag {
        "int" => Some(&["Int", "Number"]),
        "float" => Some(&["Float", "Number"]),
        "nat" => Some(&["Nat", "Int", "Number"]),
        "number" => Some(&["Number"]),
        _ => None,
    }
}

/// Resolve a `type`-link-shaped value to its nominal head sym: a `Sym`
/// is its own head; `{"__former__": <sym>, …}` resolves to the former
/// sym; `{"__type__": i}` (a universe encoding) resolves to the `Type`
/// nominal; a `{"__tag__": t}` bridge resolves by tag. Anything else has
/// no nominal head.
pub fn nominal_head(v: &TaggedValue) -> Option<Rc<Sym>> {
    match v {
        TaggedValue::Sym(s) => Some(s.clone()),
        TaggedValue::Obj(m) => {
            if let Some(TaggedValue::Sym(s)) = m.get("__former__") {
                return Some(s.clone());
            }
            if let Some(TaggedValue::Obj(f)) = m.get("__former__") {
                if let Some(TaggedValue::Sym(s)) = f.get("sym") {
                    return Some(s.clone());
                }
            }
            if m.contains_key("__type__") {
                return Some(Sym::seeded("type.Type"));
            }
            if let Some(TaggedValue::Str(t)) = m.get("__tag__") {
                return legacy_type_seed(t).map(Sym::seeded);
            }
            None
        }
        _ => None,
    }
}

/// The `type` link of a value — `x : T` read (ADR-0154 §2).
///
/// - a `Sym` yields its `ty` link (`Int.ty = Type`);
/// - an object with a `"type"` field yields that field (ctor values
///   carry `{"type": F(i⃗)}`);
/// - a `__tag__` datum yields the seeded nominal its tag bridges to;
/// - a scalar literal yields its default kind nominal (`1 → type.Nat`,
///   `-1 → type.Int`, `1.5 → type.Float`, …);
/// - any other value (plain object, pair/either, tensor, arrow) yields
///   its coarse kind nominal (`type.Obj`/`type.Arrow`/…).
/// `None` only for a nominal with no `ty` link.
pub fn type_link(v: &TaggedValue) -> Option<TaggedValue> {
    match v {
        TaggedValue::Sym(s) => s.ty().map(|t| TaggedValue::Sym(Rc::new(t.clone()))),
        TaggedValue::Obj(m) => {
            if let Some(t) = m.get("type") {
                return Some(t.clone());
            }
            if let Some(TaggedValue::Str(tag)) = m.get("__tag__") {
                if let Some(seed) = legacy_type_seed(tag) {
                    return Some(TaggedValue::Sym(Sym::seeded(seed)));
                }
            }
            // A plain object literal is a member of `type.Obj` — the
            // scalar fallback, same as `Arr`/`Bytes` above.
            Some(TaggedValue::Sym(Sym::seeded(literal_type_seed(v))))
        }
        TaggedValue::Pair(_) | TaggedValue::EitherLeft(_) | TaggedValue::EitherRight(_) => {
            Some(TaggedValue::Sym(Sym::seeded("type.Obj")))
        }
        _ => Some(TaggedValue::Sym(Sym::seeded(literal_type_seed(v)))),
    }
}

/// `instanceof(value, nominal)` — ADR-0154 §2 membership + subtyping in
/// one read: `x : T` resolves `x`'s `type`-link head, then the `<:` walk
/// is `head.has_ancestor(nominal)` over `parent` links.
///
/// - `nominal` resolves to a head sym the same way ([`nominal_head`]) —
///   a `{"__former__": s}` family object is a valid `instanceof` target.
/// - A nominal *value* reads both its own `parent` chain (the `<:` read
///   — `instanceof(Float, Number)`) and its `ty` link (the membership
///   read — `instanceof(Int, Type)`).
/// - A `__tag__` datum bridges two ways: the seeded nominal's real
///   parent walk, *and* — for unseeded hand-minted nominals — the legacy
///   name match (`nominal.name` ∈ the datum's roles). Both stay until
///   `__tag__` deletion lands.
/// - Scalars resolve through the literal defaults (`1 instanceof Nat`,
///   `1.5 instanceof Float`).
pub fn instance_of(value: &TaggedValue, nominal: &TaggedValue) -> bool {
    ensure_builtin_type_nominals();
    let Some(n) = nominal_head(nominal) else {
        return false;
    };
    match value {
        TaggedValue::Sym(s) => {
            s.has_ancestor(&n) || s.ty().is_some_and(|t| t.has_ancestor(&n))
        }
        TaggedValue::Obj(m) => {
            // `type` link first, `__tag__` bridge second (0154 §2 read
            // order): a `"type"` field is authoritative; a bare
            // `__tag__` datum falls back to the tag bridges.
            if !m.contains_key("type") {
                if let Some(tag) = m.get("__tag__").and_then(|t| t.as_str()) {
                    // Bridge: the datum's type is the seeded nominal for
                    // its tag (real parent walk) — or, for hand-minted
                    // nominals, the presentation-name role match.
                    let seeded = legacy_type_seed(tag)
                        .is_some_and(|seed| Sym::seeded(seed).has_ancestor(&n));
                    let named = legacy_tag_roles(tag).is_some_and(|roles| {
                        let own = n.name().to_ascii_lowercase();
                        !own.is_empty() && roles.iter().any(|r| r.to_ascii_lowercase() == own)
                    });
                    return seeded || named;
                }
            }
            match type_link(value).as_ref().and_then(nominal_head) {
                Some(head) => head.has_ancestor(&n),
                None => false,
            }
        }
        _ => match type_link(value).as_ref().and_then(nominal_head) {
            Some(head) => head.has_ancestor(&n),
            None => false,
        },
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
        // Tensors are always truthy (an opaque host value exists —
        // unlike `Bytes`, emptiness is a shape property, not falsiness).
        TaggedValue::Tensor(_) => true,
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
        // Tensors are values: structural equality over shape + data
        // (elementwise f64 `==`, matching `Float`).
        (TaggedValue::Tensor(x), TaggedValue::Tensor(y)) => x == y,
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
fn comp_at(
    k: u64,
    n: u64,
    a: &TaggedValue,
    b: &TaggedValue,
    b_id: bool,
) -> Result<TaggedValue, String> {
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
    let (_, mut acc) = compose_step(seed).map_err(|e| format!("compose step 0: {e}"))?;
    for (i, step) in iter.enumerate() {
        let (axis, cell) =
            compose_step(step).map_err(|e| format!("compose step {}: {e}", i + 1))?;
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
        assert!(cell2_comp_axis(1, &int(1), &int(2))
            .unwrap_err()
            .contains("boundary"));
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
        assert_eq!(c.get("__tag__").and_then(|t| t.as_str()), Some("Cell"));
    }

    #[test]
    fn comp_axis2_boundary_mismatch() {
        let a = cell3(
            cell2(int(0), int(1), int(8)),
            cell2(int(1), int(2), int(5)),
            int(1),
        );
        let b = cell3(
            cell2(int(7), int(2), int(5)),
            cell2(int(2), int(3), int(9)),
            int(2),
        );
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
        assert!(
            err.contains("step 1") && err.contains("boundary"),
            "got {err}"
        );

        // Non-array and empty diagrams reject cleanly.
        assert!(cell_compose(&int(1)).is_err());
        assert!(cell_compose(&TaggedValue::Arr(Rc::from(vec![]))).is_err());
    }

    #[test]
    fn object_view_projects_opaque_wire_records() {
        // `Obj` is its own view.
        let obj = TaggedValue::from(serde_json::json!({"a": 1}));
        let view = obj.object_view().unwrap();
        assert!(matches!(view, TaggedValue::Obj(_)));
        assert_eq!(view.get("a"), Some(&TaggedValue::Int(1)));

        // `Tensor` projects `{"__tensor__": {shape, data, dtype}}` — the
        // same record a `.hnl` program authors and the wire form emits.
        let t = TaggedValue::from(serde_json::json!({
            "__tensor__": {"shape": [2, 2], "data": [1, 2, 3, 4], "dtype": "f64"}
        }));
        assert!(t.is_tensor());
        let tv = t.object_view().unwrap();
        let inner = tv.get("__tensor__").and_then(|i| i.as_object()).unwrap();
        assert_eq!(
            inner.get("shape").and_then(|s| s.as_array()).unwrap().len(),
            2
        );
        assert_eq!(
            inner.get("data").and_then(|d| d.as_array()).unwrap().len(),
            4
        );
        assert_eq!(
            inner.get("dtype").and_then(|d| d.as_str()),
            Some("f64")
        );

        // `Bytes` projects `{"__bytes__": [n, …]}`.
        let b = TaggedValue::from(serde_json::json!({"__bytes__": [104, 105]}));
        let bv = b.object_view().unwrap();
        assert_eq!(
            bv.get("__bytes__").and_then(|a| a.as_array()).unwrap().len(),
            2
        );

        // Variants with their own `.hnl` projections (Pair, Either) and
        // scalars have no object view.
        assert!(TaggedValue::from(serde_json::json!({"__pair__": [1, 2]}))
            .object_view()
            .is_none());
        assert!(TaggedValue::from(serde_json::json!({"__either__": "left", "value": 1}))
            .object_view()
            .is_none());
        assert!(TaggedValue::Int(1).object_view().is_none());
        assert!(TaggedValue::Null.object_view().is_none());
    }

    #[test]
    fn sym_ty_link_roundtrips_the_wire_encoding() {
        // A nominal carrying both links serializes `parent` and `type`
        // and decodes them back (ADR-0154 §2).
        ensure_builtin_type_nominals();
        let int = Sym::seeded("type.Int");
        assert_eq!(int.ty().map(|t| t.name()), Some("Type"));
        assert_eq!(int.parent().map(|p| p.name()), Some("Number"));

        let wire = tagged_to_value(&TaggedValue::Sym(int.clone()));
        let back = TaggedValue::from(wire.clone());
        let TaggedValue::Sym(decoded) = &back else {
            panic!("expected a Sym, got {back:?}")
        };
        assert_eq!(decoded, &int);
        assert_eq!(decoded.ty().map(|t| t.name()), Some("Type"));
        assert_eq!(decoded.parent().map(|p| p.name()), Some("Number"));
        // The wire form carries both links.
        assert!(wire["__sym__"]["type"]["__sym__"]["name"].is_string());
        assert_eq!(
            wire["__sym__"]["parent"]["__sym__"]["name"],
            Value::from("Number")
        );
    }

    #[test]
    fn builtin_graph_encodes_numeric_subtyping() {
        ensure_builtin_type_nominals();
        let nat = Sym::seeded("type.Nat");
        let int = Sym::seeded("type.Int");
        let number = Sym::seeded("type.Number");
        let float = Sym::seeded("type.Float");
        let value = Sym::seeded("type.Value");
        assert!(nat.is_descendant_of(&int));
        assert!(int.is_descendant_of(&number));
        assert!(nat.is_descendant_of(&number));
        assert!(float.is_descendant_of(&number));
        assert!(!int.is_descendant_of(&float));
        // `Value` tops the graph.
        assert!(number.is_descendant_of(&value));
        assert!(Sym::seeded("type.Str").is_descendant_of(&value));
        assert!(!value.is_descendant_of(&number));
        // Seeded mints are idempotent: the graph is ensured, not re-minted.
        assert_eq!(Sym::seeded("type.Int"), int);
    }

    #[test]
    fn seeded_with_links_upgrades_bare_mints() {
        // A bare `seeded` mint gains its links later (same handle).
        let bare = Sym::seeded("type.Kilo");
        let h = bare.handle();
        assert!(bare.parent().is_none() && bare.ty().is_none());
        let p = Sym::seeded("type.Scale");
        let t = Sym::seeded("type.Type");
        let full = Sym::seeded_with_links("type.Kilo", Some(&p), Some(&t));
        assert_eq!(full.handle(), h);
        assert_eq!(full.parent().map(|x| x.handle()), Some(p.handle()));
        assert_eq!(full.ty().map(|x| x.handle()), Some(t.handle()));
        // Links are set-once: a second declare keeps the first parents.
        let other = Sym::seeded("type.Other");
        let again = Sym::seeded_with_links("type.Kilo", Some(&other), None);
        assert_eq!(again.parent().map(|x| x.handle()), Some(p.handle()));
    }

    #[test]
    fn type_link_reads_membership() {
        ensure_builtin_type_nominals();
        // Literals default per ADR-0154 §5.
        let nat = TaggedValue::Sym(Sym::seeded("type.Nat"));
        let int = TaggedValue::Sym(Sym::seeded("type.Int"));
        let float = TaggedValue::Sym(Sym::seeded("type.Float"));
        assert_eq!(type_link(&TaggedValue::Int(1)), Some(nat.clone()));
        assert_eq!(type_link(&TaggedValue::Int(-2)), Some(int));
        assert_eq!(type_link(&TaggedValue::Float(1.5)), Some(float));
        assert_eq!(
            type_link(&TaggedValue::Bool(true)),
            Some(TaggedValue::Sym(Sym::seeded("type.Bool")))
        );
        // A ctor-shaped object yields its `type` field.
        let fapp = TaggedValue::from(serde_json::json!({
            "__former__": tagged_to_value(&TaggedValue::Sym(Sym::seeded("data.Vec"))),
            "indices": [0]
        }));
        let ctor = TaggedValue::from(serde_json::json!({
            "type": tagged_to_value(&fapp)
        }));
        assert_eq!(type_link(&ctor), Some(fapp));
        // A legacy `__tag__` datum bridges to its seeded nominal.
        let datum = TaggedValue::from(serde_json::json!({
            "__tag__": "int", "__registry__": "type", "kind": "primitive"
        }));
        assert_eq!(
            type_link(&datum),
            Some(TaggedValue::Sym(Sym::seeded("type.Int")))
        );
        // A nominal value yields its `ty` link.
        let int_sym = TaggedValue::Sym(Sym::seeded("type.Int"));
        assert_eq!(
            type_link(&int_sym),
            Some(TaggedValue::Sym(Sym::seeded("type.Type")))
        );
    }

    #[test]
    fn instance_of_reads_both_links() {
        ensure_builtin_type_nominals();
        let int = TaggedValue::Sym(Sym::seeded("type.Int"));
        let nat = TaggedValue::Sym(Sym::seeded("type.Nat"));
        let number = TaggedValue::Sym(Sym::seeded("type.Number"));
        let float = TaggedValue::Sym(Sym::seeded("type.Float"));
        let ty = TaggedValue::Sym(Sym::seeded("type.Type"));
        let strs = TaggedValue::Sym(Sym::seeded("type.Str"));

        // `<:` read on nominal values (parent walk).
        assert!(instance_of(&nat, &int));
        assert!(instance_of(&nat, &number));
        assert!(instance_of(&float, &number));
        assert!(!instance_of(&int, &float));
        assert!(!instance_of(&number, &int));
        // Membership read on type values (the `ty` link): `Int : Type`.
        assert!(instance_of(&int, &ty));
        assert!(!instance_of(&int, &strs));
        // Literal defaults.
        assert!(instance_of(&TaggedValue::Int(1), &nat));
        assert!(instance_of(&TaggedValue::Int(1), &int));
        assert!(instance_of(&TaggedValue::Int(1), &number));
        assert!(!instance_of(&TaggedValue::Int(1), &float));
        assert!(instance_of(&TaggedValue::Int(-1), &int));
        assert!(!instance_of(&TaggedValue::Int(-1), &nat));
        assert!(instance_of(&TaggedValue::Float(1.5), &float));
        assert!(instance_of(&TaggedValue::Str("s".into()), &strs));
        assert!(instance_of(&TaggedValue::Null, &TaggedValue::Sym(Sym::seeded("type.Null"))));
        // Former application as the nominal target.
        let vec = TaggedValue::from(serde_json::json!({
            "__former__": tagged_to_value(&TaggedValue::Sym(Sym::seeded("data.Vec"))),
            "indices": [2]
        }));
        let ctor = TaggedValue::from(serde_json::json!({
            "__ctor__": tagged_to_value(&TaggedValue::Sym(Sym::seeded("data.Vec.VCons"))),
            "type": tagged_to_value(&vec)
        }));
        assert!(instance_of(&ctor, &vec));
        assert!(!instance_of(&ctor, &nat));
    }

    #[test]
    fn instance_of_legacy_tag_bridge() {
        ensure_builtin_type_nominals();
        let datum = |t: &str| {
            TaggedValue::from(serde_json::json!({
                "__tag__": t, "__registry__": "type", "kind": "primitive"
            }))
        };
        // Seeded walk: tag → seeded nominal → `parent` chain.
        assert!(instance_of(&datum("int"), &TaggedValue::Sym(Sym::seeded("type.Int"))));
        assert!(instance_of(&datum("int"), &TaggedValue::Sym(Sym::seeded("type.Number"))));
        assert!(instance_of(&datum("nat"), &TaggedValue::Sym(Sym::seeded("type.Int"))));
        assert!(!instance_of(&datum("int"), &TaggedValue::Sym(Sym::seeded("type.Float"))));
        // Name bridge: an unseeded nominal named like a std type still
        // matches by presentation name (legacy semantics).
        let named = TaggedValue::Sym(Rc::new(Sym::fresh_with_parent(
            "Int",
            &Sym::fresh("Number"),
        )));
        assert!(instance_of(&datum("int"), &named));
        // Unknown tags stay false (no roles, no seed).
        assert!(!instance_of(&datum("custom"), &named));
    }
}
