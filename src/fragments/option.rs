//! Option schema fragment definitions.
//!
//! `OptionSchema` is defined locally here rather than re-exported from
//! `handl-platform`. The platform's `OptionSchema` is not
//! `serde`-serializable (its `OptionScope` enum lacks serde derives and it is
//! coupled to the `Plugin`/`RuleAcceptor` runtime machinery), so reusing it
//! would either break serialization of `Language` or pull in plugin-system
//! coupling. This minimal data-only version keeps `Language` serializable end
//! to end while preserving the same `id`-keyed identity semantics.

use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::fragment::Fragment;

/// A declaration of an option, its default value, and allowed values.
///
/// Identity key: `id` (the option key, see ADR-0044 §5). Collision without
/// `replaces` is an error.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct OptionSchema {
    /// Stable identifier for the option (the option key).
    pub id: String,
    /// Default value when no override is provided.
    #[serde(default = "Value::default", skip_serializing_if = "is_value_null")]
    pub default: Value,
    /// Allowed values for this option.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub possible_values: Vec<Value>,
    /// Human-readable description.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub description: Option<String>,
    /// ids this fragment declares it replaces.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub replaces: Vec<String>,
    /// ids this fragment hard-requires.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub requires: Vec<String>,
}

fn is_value_null(v: &Value) -> bool {
    v == &Value::Null
}

impl OptionSchema {
    /// Create a new option schema with the given id and a null default.
    pub fn new(id: impl Into<String>) -> Self {
        Self {
            id: id.into(),
            default: Value::Null,
            possible_values: Vec::new(),
            description: None,
            replaces: Vec::new(),
            requires: Vec::new(),
        }
    }

    /// Attach a default value.
    pub fn with_default(mut self, default: Value) -> Self {
        self.default = default;
        self
    }

    /// Attach allowed values.
    pub fn with_possible_values(mut self, values: Vec<Value>) -> Self {
        self.possible_values = values;
        self
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

impl Fragment for OptionSchema {
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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn construct_and_accessors() {
        let o = OptionSchema::new("opt.indent")
            .with_default(Value::from(2))
            .with_possible_values(vec![Value::from(2), Value::from(4)])
            .with_description("indent width")
            .with_replaces(vec!["opt.indent.old".into()])
            .with_requires(vec!["opt.tab".into()]);
        assert_eq!(o.id(), "opt.indent");
        assert_eq!(o.default, Value::from(2));
        assert_eq!(o.possible_values.len(), 2);
        assert_eq!(o.description.as_deref(), Some("indent width"));
        assert_eq!(o.replaces(), &["opt.indent.old".to_string()]);
        assert_eq!(o.requires(), &["opt.tab".to_string()]);
        assert_eq!(o.identity_key(), "opt.indent");
    }

    #[test]
    fn serde_roundtrip() {
        let o = OptionSchema::new("opt.x")
            .with_default(Value::from(true))
            .with_description("a flag");
        let j = serde_json::to_string(&o).unwrap();
        let back: OptionSchema = serde_json::from_str(&j).unwrap();
        assert_eq!(o, back);
    }

    #[test]
    fn equality() {
        assert_eq!(OptionSchema::new("a"), OptionSchema::new("a"));
        assert_ne!(OptionSchema::new("a"), OptionSchema::new("b"));
    }
}
