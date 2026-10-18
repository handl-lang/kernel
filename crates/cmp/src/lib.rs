//! `cmp` — Handl stdlib port.
//!
//! `src/index.hnl` is the interface; `ops.rs` holds the Rust atoms behind it.
//! Transitional: plan `stdlib-lib-migration` Phase 7 rewrites them as
//! `handle … with ffi.call(…)` and deletes this crate.

/// The handl source declaring the `cmp` interface.
pub const CMP_HNL: &str = include_str!("index.hnl");

pub mod ops;

pub use ops::{CMP_OPS, cmp_op_registry};
