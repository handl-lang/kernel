//! Standalone `FunctionValue` type for first-class functions.
//!
//! A first-class function is its parameter schemas, optional return schema,
//! a body expression string, and captured variables from the enclosing scope.
//! The whole value is plain data that serializes as JSON.
//!
//! A function value is detected by the presence of a `body` string field in
//! a JSON object. No special tag is needed.
//!
//! This is the ADR 0040 replacement for `plugin_vm_values_json::FunctionValue`,
//! without the `FunctionRepr` trait bound.

use serde_json::Value as JsonValue;

/// A serializable function value.
#[derive(Debug, Clone, PartialEq)]
pub struct FunctionValue {
    /// `(param_name, raw_schema)` pairs, in declaration order.
    pub params: Vec<(String, JsonValue)>,
    /// Raw schema value for the return type, if declared.
    pub return_schema: Option<JsonValue>,
    /// The body expression string (e.g. `"mul(x, 2)"`).
    pub body: String,
    /// Original pattern JSON for each parameter, in declaration order.
    pub patterns: Vec<JsonValue>,
    /// Captured variables from the enclosing scope, as `(name, value)` pairs.
    pub captured: Vec<(String, JsonValue)>,
}

impl From<FunctionValue> for JsonValue {
    fn from(value: FunctionValue) -> Self {
        value.to_json()
    }
}

impl FunctionValue {
    /// Encodes this function value as a plain JSON object.
    pub fn to_json(&self) -> JsonValue {
        let params = JsonValue::Array(
            self.params
                .iter()
                .enumerate()
                .map(|(i, (name, schema))| {
                    let pattern = self.patterns.get(i).cloned().unwrap_or(JsonValue::Null);
                    serde_json::json!({
                        "name": name,
                        "schema": schema,
                        "pattern": pattern
                    })
                })
                .collect(),
        );

        let mut obj = serde_json::Map::new();
        obj.insert("params".to_string(), params);
        if let Some(ret) = &self.return_schema {
            obj.insert("return".to_string(), ret.clone());
        }
        obj.insert("body".to_string(), JsonValue::String(self.body.clone()));
        if !self.captured.is_empty() {
            obj.insert(
                "captured".to_string(),
                JsonValue::Array(
                    self.captured
                        .iter()
                        .map(|(name, value)| serde_json::json!([name, value]))
                        .collect(),
                ),
            );
        }
        JsonValue::Object(obj)
    }

    /// Decodes a function value from a JSON object.
    ///
    /// Returns `None` if the value is not an object or does not have
    /// a `body` string field.
    pub fn from_json(value: &JsonValue) -> Option<Self> {
        let obj = value.as_object()?;
        let body = obj.get("body").and_then(|v| v.as_str())?.to_string();

        let params = obj
            .get("params")
            .map(|p| {
                if let Some(arr) = p.as_array() {
                    arr.iter()
                        .filter_map(|p| {
                            let name = p.get("name")?.as_str()?.to_string();
                            let schema = p.get("schema").cloned().unwrap_or(JsonValue::Null);
                            Some((name, schema))
                        })
                        .collect::<Vec<_>>()
                } else if let Some(map) = p.as_object() {
                    map.iter()
                        .map(|(name, schema)| (name.clone(), schema.clone()))
                        .collect::<Vec<_>>()
                } else {
                    Vec::new()
                }
            })
            .unwrap_or_default();

        let return_schema = obj.get("return").cloned();

        let patterns = obj
            .get("params")
            .and_then(|p| p.as_array())
            .map(|arr| {
                arr.iter()
                    .map(|p| p.get("pattern").cloned().unwrap_or(JsonValue::Null))
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();

        let captured = obj
            .get("captured")
            .and_then(|v| v.as_array())
            .map(|arr| {
                arr.iter()
                    .filter_map(|pair| {
                        let pair_arr = pair.as_array()?;
                        let name = pair_arr.first()?.as_str()?.to_string();
                        let value = pair_arr.get(1)?.clone();
                        Some((name, value))
                    })
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();

        Some(FunctionValue {
            params,
            return_schema,
            body,
            patterns,
            captured,
        })
    }
}
