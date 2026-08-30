//! Scheme combinator versioning (ADR-0044 §7).
//!
//! A `Language` declares a `SchemeVersion` (e.g. `"v1"`); engines declare
//! which versions they support. Extending the core ships as a new version.
//! For Phase 1, versioning is string comparison plus serialization.

use serde::{Deserialize, Serialize};

/// The scheme combinator version a `Language` targets.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct SchemeVersion(String);

impl SchemeVersion {
    /// Create a version from a string (e.g. `"v1"`).
    pub fn new(v: impl Into<String>) -> Self {
        Self(v.into())
    }

    /// The canonical first version.
    pub fn v1() -> Self {
        Self::new("v1")
    }

    /// The version string.
    pub fn as_str(&self) -> &str {
        &self.0
    }

    /// Whether an engine declaring support for `self` accepts a language
    /// targeting `lang_version`.
    ///
    /// For Phase 1 this is exact string equality. (A future versioning scheme
    /// may allow backward-compatible acceptance, e.g. a `v2` engine accepting
    /// `v1` languages.)
    pub fn supports(&self, lang_version: &SchemeVersion) -> bool {
        self.0 == lang_version.0
    }
}

impl std::fmt::Display for SchemeVersion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn v1_constructs() {
        let v = SchemeVersion::v1();
        assert_eq!(v.as_str(), "v1");
        assert_eq!(v.to_string(), "v1");
    }

    #[test]
    fn supports_accepts_same_version() {
        let engine = SchemeVersion::v1();
        let lang = SchemeVersion::v1();
        assert!(engine.supports(&lang));
    }

    #[test]
    fn supports_rejects_different_version() {
        let engine = SchemeVersion::new("v2");
        let lang = SchemeVersion::v1();
        assert!(!engine.supports(&lang));
    }

    #[test]
    fn serde_roundtrip() {
        let v = SchemeVersion::v1();
        let j = serde_json::to_string(&v).unwrap();
        assert_eq!(j, "\"v1\"");
        let back: SchemeVersion = serde_json::from_str(&j).unwrap();
        assert_eq!(v, back);
    }

    #[test]
    fn equality() {
        assert_eq!(SchemeVersion::v1(), SchemeVersion::new("v1"));
        assert_ne!(SchemeVersion::v1(), SchemeVersion::new("v2"));
    }
}
