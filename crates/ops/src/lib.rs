//! Shared op helpers for the `lib-*` crates.
//!
//! These primitives (argument requirements, value constructors, arrow-value
//! handling, function application) are used by every port crate that still has
//! Rust ops.
//!
//! **Throwaway.** An op is a Rust `Function` today; when it moves to
//! `handle … with ffi.call(…)` (plan `stdlib-lib-migration` Phase 7) the helper
//! it needs disappears with it. Nothing here should grow a permanent API.

pub mod function_value;
pub mod shared;
