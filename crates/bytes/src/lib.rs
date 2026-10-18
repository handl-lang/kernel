//! `bytes` — byte-buffer primitives for the `Bytes` scalar type.
//!
//! `src/index.hnl` is the single source of truth for the interface (eight
//! `op` declarations); `ops.rs` holds the Rust atoms behind them.
//!
//! Transitional: the ops are Rust `Function`s behind `handle … with rust_*`.
//! Plan `stdlib-lib-migration` Phase 7 rewrites them as
//! `handle … with ffi.call(…)` and deletes this crate.

/// The handl source declaring the `bytes` interface.
pub const BYTES_HNL: &str = include_str!("index.hnl");

pub mod ops;

pub use ops::{bytes_op_registry, BYTES_OPS};
