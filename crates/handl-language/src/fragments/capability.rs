//! Capability declaration fragment definitions.

use serde::{Deserialize, Serialize};

use crate::fragment::Fragment;

/// A declaration of a capability a language may exercise.
///
/// Identity key: `id` (see ADR-0044 §5). Merge uses **union (idempotent)**
/// semantics: merging a capability that already exists is a no-op, not an
/// error.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct CapabilityDecl {
    /// Stable identifier (e.g. `"fs.read"`).
    pub id: String,
    /// Optional human-readable description.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub description: Option<String>,
    /// ids this fragment declares it replaces.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub replaces: Vec<String>,
    /// ids this fragment hard-requires.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub requires: Vec<String>,
}

impl CapabilityDecl {
    /// Create a new capability declaration with the given id.
    pub fn new(id: impl Into<String>) -> Self {
        Self {
            id: id.into(),
            description: None,
            replaces: Vec::new(),
            requires: Vec::new(),
        }
    }

    /// Attach a description.
    pub fn with_description(mut self, desc: impl Into<String>) -> Self {
        self.description = Some(desc.into());
        self
    }

    /// Attach a `replaces` list.
    pub fn with_replaces(mut self, replaces: Vec<String>) -> Self {
        self.replaces = replaces;
        self
    }

    /// Attach a `requires` list.
    pub fn with_requires(mut self, requires: Vec<String>) -> Self {
        self.requires = requires;
        self
    }
}

impl Fragment for CapabilityDecl {
    fn id(&self) -> &str {
        &self.id
    }
    fn replaces(&self) -> &[String] {
        &self.replaces
    }
    fn requires(&self) -> &[String] {
        &self.requires
    }
    fn identity_key(&self) -> String {
        self.id.clone()
    }
    /// Capability declarations merge idempotently (union semantics).
    const UNION: bool = true;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn construct_and_accessors() {
        let c = CapabilityDecl::new("fs.read")
            .with_description("read files")
            .with_replaces(vec!["fs.read.old".into()])
            .with_requires(vec!["fs.open".into()]);
        assert_eq!(c.id(), "fs.read");
        assert_eq!(c.description.as_deref(), Some("read files"));
        assert_eq!(c.replaces(), &["fs.read.old".to_string()]);
        assert_eq!(c.requires(), &["fs.open".to_string()]);
        assert_eq!(c.identity_key(), "fs.read");
        assert!(CapabilityDecl::UNION);
    }

    #[test]
    fn serde_roundtrip() {
        let c = CapabilityDecl::new("net.connect").with_description("network");
        let j = serde_json::to_string(&c).unwrap();
        let back: CapabilityDecl = serde_json::from_str(&j).unwrap();
        assert_eq!(c, back);
    }

    #[test]
    fn equality() {
        assert_eq!(CapabilityDecl::new("a"), CapabilityDecl::new("a"));
        assert_ne!(CapabilityDecl::new("a"), CapabilityDecl::new("b"));
    }
}
