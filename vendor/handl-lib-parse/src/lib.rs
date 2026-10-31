//! # handl-lib-parse
//!
//! `parse` — generic parser dispatch contract. `parse.parse(input, parser)`
//! declares the op; parser objects are `.hnl` records carrying a `parse`
//! arrow (`url_rfc.url_rfc`, `url_whatwg.url_whatwg`, …). The meta-chain
//! `ParseModule` (language stage) serves `parse.*` calls today.
#![allow(dead_code)]

pub const PARSE_HNL: &str = include_str!("index.hnl");

/// The `parse.*` op names declared in `index.hnl`.
pub const PARSE_OPS: &[&str] = &["parse.parse"];
