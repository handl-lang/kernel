//! Term combinator versioning (ADR-0044 §7, ADR-0052).
//!
//! A `Language` declares a `SchemeVersion`; engines declare which versions
//! they support. The canonical kernel version is `"v2"` (the arrow-calculus
//! kernel, ADR-0052). Versioning is string comparison plus serialization.

use serde::{Deserialize, Serialize};

/// The scheme combinator version a `Language` targets.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct SchemeVersion(String);

impl SchemeVersion {
    /// Create a version from a string (e.g. `"v2"`).
    pub fn new(v: impl Into<String>) -> Self {
        Self(v.into())
    }

    /// The canonical arrow-calculus kernel version (ADR-0052).
    pub fn v2() -> Self {
        Self::new("v2")
    }

    /// The version string.
    pub fn as_str(&self) -> &str {
        &self.0
    }

    /// Whether an engine declaring support for `self` accepts a language
    /// targeting `lang_version`.
    ///
    /// Exact string equality. The v1 kernel has been removed (ADR-0052
    /// big-bang cutover); there is no longer a v1↔v2 backward-compatibility
    /// bridge — every `Language` targets `"v2"`.
    pub fn supports(&self, lang_version: &SchemeVersion) -> bool {
        self.0 == lang_version.0
    }
}

impl Default for SchemeVersion {
    fn default() -> Self {
        Self::v2()
    }
}

impl std::fmt::Display for SchemeVersion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[cfg(test)]
#[path = "version_test.rs"]
mod version_test;
