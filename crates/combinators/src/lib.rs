//! `combinators` — Handl stdlib port.
//!
//! `src/index.hnl` is the interface; `ops.rs` holds the Rust atoms behind it.
//! Transitional: plan `stdlib-lib-migration` Phase 7 rewrites them as
//! `handle … with ffi.call(…)` and deletes this crate.

/// The handl source declaring the `combinators` interface.
pub const COMBINATORS_HNL: &str = include_str!("index.hnl");

pub mod ops;

pub use ops::{
    COMBINATORS_OPS, TRANSFORM_OPS, combinators_op_registry, transform_op_registry,
};
