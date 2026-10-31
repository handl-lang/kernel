//! # handl-lib-encoding
//!
//! `encoding` — generic codec dispatch for the handl runtime. The `.hnl`
//! `encoding.encode`/`encoding.decode` arrows dispatch on the codec object's
//! `encode`/`decode` arrow fields — codec objects are produced by
//! `hex.codec`, `base64.codec`, `json.json`, etc. Pure `.hnl`; no Rust impl.
#![allow(dead_code)]

pub const ENCODING_HNL: &str = include_str!("index.hnl");

/// The `encoding.*` op names declared in `index.hnl`.
pub const ENCODING_OPS: &[&str] = &["encoding.encode", "encoding.decode"];
