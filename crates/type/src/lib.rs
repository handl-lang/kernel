//! `typeof` — Handl stdlib port (`src/index.hnl`).
//!
//! Transitional: the ops are Rust until plan `stdlib-lib-migration` Phase 7
//! rewrites them as `ffi.call` and deletes this crate.

pub const TYPEOF_HNL: &str = include_str!("index.hnl");

pub mod ops;

pub use ops::{type_op_registry, TYPE_OPS};
