//! AST shape fragment definitions.

use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::fragment::Fragment;

/// A specification for a single child of a desugar replacement node
/// (ADR-0053 §7 — data-driven desugar pass).
///
/// A child is either [`AstDesugarChild::Keep`] (reuse the original node's
/// child at the given index, remapped into the output arena),
/// [`AstDesugarChild::KeepPath`] (navigate through descendant children by
/// index path, e.g. `[0, 0]` takes child 0's child 0), or
/// [`AstDesugarChild::Create`] (allocate a fresh node, optionally with its
/// own children — the rewrite is recursive).
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum AstDesugarChild {
    /// Reuse the original node's child at the given index.
    Keep(usize),
    /// Reuse a descendant node by navigating through children by index path.
    /// `KeepPath([0, 0])` takes the original node's child 0, then that
    /// node's child 0, and remaps the final arena index into the output
    /// arena. Used by ADR-0058 to unwrap bracket-computed-key `array`
    /// wrappers during desugar.
    KeepPath(Vec<usize>),
    /// Allocate a new node with the given `kind`, optional `payload`, and
    /// nested `children` (themselves [`AstDesugarChild`]s).
    Create {
        /// The AST node kind of the created node.
        kind: String,
        /// Optional payload for the created node.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        payload: Option<Value>,
        /// Nested children of the created node.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        children: Vec<AstDesugarChild>,
    },
    /// Keep all children from the given index onward (ADR-0060). Unlike
    /// `Keep(i)` which keeps a single child, `KeepRest(N)` expands to all
    /// children from index `N` to the end, each remapped into the output
    /// arena. Used by desugar rules that need to preserve a variable-length
    /// tail of children (e.g. `json{...}(args)` → `json` node with all
    /// original children kept).
    KeepRest(usize),
}

/// A condition that guards whether a desugar rule applies (ADR-0058).
///
/// When present on an [`AstDesugarRule`], the pass only rewrites nodes whose
/// child at `child_index` has the AST node kind `child_kind`. Nodes that
/// don't match pass through unchanged. This lets a single shape carry a
/// desugar rule that only fires for a specific child variant (e.g. only
/// `entry` nodes whose key child is an `array`).
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct AstDesugarCondition {
    /// The index into the original node's `children` array to test.
    pub child_index: usize,
    /// The AST node kind the child must have for the rule to fire.
    pub child_kind: String,
}

/// A data-driven desugar rule (ADR-0053 §7).
///
/// Specifies the `target_kind` to rewrite a node into, plus the list of
/// [`AstDesugarChild`]s that become the rewritten node's children. Attached
/// to an [`AstShapeDef`] via [`AstShapeDef::with_desugar`].
///
/// An optional `when` condition (ADR-0058) gates the rewrite: the rule only
/// fires if the original node's child at `when.child_index` has kind
/// `when.child_kind`. Without `when`, the rule fires unconditionally (the
/// ADR-0053 behavior).
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct AstDesugarRule {
    /// The AST node kind to rewrite into.
    pub target_kind: String,
    /// The children of the rewritten node.
    pub children: Vec<AstDesugarChild>,
    /// Optional condition gating the rewrite (ADR-0058). When present, the
    /// rule only fires if the original node's child at `child_index` has
    /// kind `child_kind`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub when: Option<AstDesugarCondition>,
}

/// A named role for a single child position of an AST node (ADR-0081).
///
/// Children are referenced by **role** (e.g. `target`, `statements`, `params`)
/// rather than by positional index. Engines look up the positional index from
/// the [`AstShapeDef`] at runtime instead of hardcoding `kind ==` shape checks.
///
/// `variadic: true` means the role covers all children from its start index to
/// the end (e.g. `statements` in a `block`). A non-variadic role maps to
/// exactly one child position.
///
/// `optional: true` means the role may be **absent** from a node's children —
/// e.g. `match`'s optional `motive` child (`[scrutinee, (motive,) block]`) or
/// `assign`'s optional trailing `body` (`[target, value, (body)]`). Optional
/// roles make child positions **arity-dependent**: the index of a role after
/// an optional slot depends on the node's actual child count. Use
/// [`AstShapeDef::role_index_at`] (or `Language::child_role_index_for`) to
/// resolve a concrete node; [`AstShapeDef::role_index`] resolves the
/// full-form index (all optional roles present).
///
/// YAML accepts either the map form (`{role: motive, optional: true}`) or a
/// bare string shorthand (`- scrutinee` ≡ `{role: scrutinee}`).
#[derive(Debug, Clone, Serialize, PartialEq)]
pub struct ChildRoleSpec {
    /// The role name — meaningful within this shape only (per-shape, not
    /// global; `target` in `assign` is unrelated to `target` elsewhere).
    pub role: String,
    /// Whether the role spans this start index to the end of the children
    /// array. Absent/`false` = a single child position.
    #[serde(default, skip_serializing_if = "is_false")]
    pub variadic: bool,
    /// Whether the role may be absent from a node's children. Absent/`false`
    /// = the role always occupies a child position (backward compatible).
    #[serde(default, skip_serializing_if = "is_false")]
    pub optional: bool,
}

impl<'de> Deserialize<'de> for ChildRoleSpec {
    /// Deserialize either the full map form or a bare-string shorthand
    /// (`- scrutinee` ≡ `- {role: scrutinee}`), so plain-string `children`
    /// lists stay valid YAML.
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        #[derive(Deserialize)]
        #[serde(untagged)]
        enum Repr {
            Short(String),
            Full {
                role: String,
                #[serde(default)]
                variadic: bool,
                #[serde(default)]
                optional: bool,
            },
        }
        Ok(match Repr::deserialize(deserializer)? {
            Repr::Short(role) => ChildRoleSpec {
                role,
                variadic: false,
                optional: false,
            },
            Repr::Full {
                role,
                variadic,
                optional,
            } => ChildRoleSpec {
                role,
                variadic,
                optional,
            },
        })
    }
}

fn is_false(b: &bool) -> bool {
    !*b
}

/// A definition of an AST node kind and its payload shape.
///
/// Identity key: `node_kind` (see ADR-0044 §5). The `payload_schema` is a
/// `serde_json::Value` describing the payload shape (e.g. a JSON Schema
/// fragment), kept as opaque data so the crate stays engine-agnostic.
///
/// `children`, when present, declares the **named child roles** (ADR-0081).
/// Absent = opaque node whose children are referenced positionally (backward
/// compatible). When present, engines resolve child positions by role instead
/// of hardcoding `kind ==` shape checks.
///
/// AST shape declarations are **structural facts** ("this node kind exists
/// with this payload shape"), not behavioral definitions: two emitters
/// declaring the shape for `binary.add` are agreeing it exists, not
/// conflicting. Merge therefore uses **union (idempotent)** semantics —
/// merging a shape whose `node_kind` already exists is a no-op (the first
/// declaration is kept), not an error.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct AstShapeDef {
    /// Stable identifier (e.g. `"ast.binary.add"`).
    pub id: String,
    /// The AST node kind this shape describes.
    pub node_kind: String,
    /// An opaque description of the payload shape (e.g. a JSON Schema).
    #[serde(default = "Value::default", skip_serializing_if = "is_payload_null")]
    pub payload_schema: Value,
    /// Optional data-driven desugar rule (ADR-0053 §7). When present, the
    /// desugar pass rewrites nodes of this kind into `desugar.target_kind`
    /// with the specified children before evaluation.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub desugar: Option<AstDesugarRule>,
    /// ids this fragment declares it replaces.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub replaces: Vec<String>,
    /// ids this fragment hard-requires.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub requires: Vec<String>,
    /// Optional named child roles (ADR-0081). Absent = opaque, positional
    /// fallback (backward compatible). When present, engines resolve child
    /// positions by role instead of hardcoding `kind ==` shape checks.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub children: Option<Vec<ChildRoleSpec>>,
    /// Child node kinds that carry a **literal payload** when occupying a
    /// given role (ADR-0081 extension). Keyed by role name: a child node
    /// whose kind is listed for a role is data, not an expression — its
    /// payload is used directly instead of being evaluated (e.g. an object
    /// `entry` declares its `key` role literal for `var`/`string` children,
    /// while a computed `paren` key is still evaluated). Absent/empty =
    /// no literal children (backward compatible); engines fall back to
    /// their legacy heuristic for shapes that declare no list for a role.
    #[serde(default, skip_serializing_if = "std::collections::BTreeMap::is_empty")]
    pub literal_children: std::collections::BTreeMap<String, Vec<String>>,
    /// Optional pattern-role metadata (ADR-0081 extension). When present,
    /// a node of this kind may appear as a `match` pattern and the value
    /// tells pattern-matching engines how to interpret its children:
    /// `leaf` (a bare binder), `sequence` (an array-like list of element
    /// patterns), `entries` (an object-like list of field patterns),
    /// `entry` (one key/value field pattern), or `rest` (a spread/rest
    /// pattern). Absent = this node kind is not a pattern shape.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub pattern_role: Option<String>,
}

fn is_payload_null(v: &Value) -> bool {
    v == &Value::Null
}

impl AstShapeDef {
    /// Create a new AST shape definition with a null payload schema.
    pub fn new(id: impl Into<String>, node_kind: impl Into<String>) -> Self {
        Self {
            id: id.into(),
            node_kind: node_kind.into(),
            payload_schema: Value::Null,
            desugar: None,
            replaces: Vec::new(),
            requires: Vec::new(),
            children: None,
            literal_children: std::collections::BTreeMap::new(),
            pattern_role: None,
        }
    }

    /// Attach a payload schema.
    pub fn with_payload_schema(mut self, schema: Value) -> Self {
        self.payload_schema = schema;
        self
    }

    /// Attach a data-driven desugar rule (ADR-0053 §7).
    pub fn with_desugar(mut self, rule: AstDesugarRule) -> Self {
        self.desugar = Some(rule);
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

    /// Attach named child roles (ADR-0081).
    pub fn with_children(mut self, children: Vec<ChildRoleSpec>) -> Self {
        self.children = Some(children);
        self
    }

    /// Attach a pattern-role tag (ADR-0081 extension).
    pub fn with_pattern_role(mut self, role: impl Into<String>) -> Self {
        self.pattern_role = Some(role.into());
        self
    }

    /// Resolve a child role to its positional index in the shape's **full
    /// form** — the form where every declared (optional or not) role occupies
    /// a slot.
    ///
    /// Returns `Some(index)` when the shape declares a role with the given
    /// name, where `index` is the position of that role's first child.
    /// Non-variadic roles map to exactly one position (e.g. `target` → 0);
    /// variadic roles map to their start index. Returns `None` if the shape has
    /// no `children` declaration or the role is unknown.
    ///
    /// When the shape declares `optional` roles, this index is only correct
    /// for a node whose arity includes every optional slot (and for roles
    /// declared *before* the first optional slot, which never shift). For a
    /// concrete node use [`role_index_at`](Self::role_index_at) /
    /// `Language::child_role_index_for`, which resolve against the node's
    /// actual child count.
    pub fn role_index(&self, role: &str) -> Option<usize> {
        let children = self.children.as_ref()?;
        let mut idx = 0usize;
        for spec in children {
            if spec.role == role {
                return Some(idx);
            }
            // Each declared role occupies exactly one slot (variadic or not);
            // roles are declared in child order, so the next role starts after
            // this one.
            idx += 1;
        }
        None
    }

    /// Resolve a child role to its positional index for a node with `arity`
    /// children — the **arity-aware** counterpart of [`role_index`](Self::role_index).
    ///
    /// Optional roles make positions arity-dependent: given a node's actual
    /// child count, the occupied optional slots are the first
    /// `arity - (required role count)` optional roles in declaration order
    /// (clamped to the number of optional roles declared). Concretely, for
    /// `match`'s `[scrutinee, {motive, optional}, block]`:
    ///
    /// - arity 2 (`match s { .. }`): `motive` absent, `block` → 1.
    /// - arity 3 (`match s return m with { .. }`): `motive` → 1, `block` → 2.
    ///
    /// A role whose slot is absent at this arity resolves to `None` (e.g.
    /// `body` on a 2-child `assign`); a role after a variadic role keeps its
    /// declared-order position (optional and variadic roles are not expected
    /// to interleave — a variadic role consumes one slot position for
    /// role-index purposes). Returns `None` if the shape has no `children`
    /// declaration, the role is unknown, or `arity` cannot cover the required
    /// roles.
    pub fn role_index_at(&self, role: &str, arity: usize) -> Option<usize> {
        let children = self.children.as_ref()?;
        let required = children.iter().filter(|s| !s.optional).count();
        if arity < required {
            return None;
        }
        let optional_total = children.len() - required;
        let occupied_optionals = (arity - required).min(optional_total);
        let mut seen_optional = 0usize;
        let mut idx = 0usize;
        for spec in children {
            if spec.optional {
                let present = seen_optional < occupied_optionals;
                seen_optional += 1;
                if !present {
                    continue;
                }
            }
            if spec.role == role {
                return Some(idx);
            }
            idx += 1;
        }
        None
    }

    /// Whether the shape declares `role` as an **optional** child (ADR-0081
    /// optional-role extension).
    pub fn role_is_optional(&self, role: &str) -> bool {
        self.child_role(role).map(|s| s.optional).unwrap_or(false)
    }

    /// Return the [`ChildRoleSpec`] for a role, if declared.
    pub fn child_role(&self, role: &str) -> Option<&ChildRoleSpec> {
        self.children.as_ref()?.iter().find(|s| s.role == role)
    }

    /// Whether the role spans multiple children (variadic).
    pub fn role_is_variadic(&self, role: &str) -> bool {
        self.child_role(role).map(|s| s.variadic).unwrap_or(false)
    }

    /// Whether a child node of `child_kind` occupying `role` is declared
    /// **literal** — its payload is the datum itself rather than an
    /// expression to evaluate.
    ///
    /// Returns `Some(bool)` when this shape declares a `literal_children`
    /// list for `role` (`true` = `child_kind` is listed, `false` = the
    /// role is declared but this kind is not literal). Returns `None` when
    /// no list is declared for the role — callers keep their legacy
    /// fallback heuristic for such shapes (ADR-0081 role-less fallback).
    pub fn literal_child(&self, role: &str, child_kind: &str) -> Option<bool> {
        self.literal_children
            .get(role)
            .map(|kinds| kinds.iter().any(|k| k == child_kind))
    }
}

impl Fragment for AstShapeDef {
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
        self.node_kind.clone()
    }
    /// AST shape declarations merge idempotently (union semantics): two
    /// emitters declaring the shape for the same node kind are agreeing it
    /// exists, not conflicting, so the duplicate is silently dropped (first
    /// wins).
    const UNION: bool = true;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn construct_and_accessors() {
        let def = AstShapeDef::new("ast.binary.add", "binary.add")
            .with_payload_schema(serde_json::json!({"type": "object"}))
            .with_replaces(vec!["ast.add.old".into()])
            .with_requires(vec!["token.plus".into()]);
        assert_eq!(def.id(), "ast.binary.add");
        assert_eq!(def.node_kind, "binary.add");
        assert_eq!(def.payload_schema, serde_json::json!({"type": "object"}));
        assert_eq!(def.replaces(), &["ast.add.old".to_string()]);
        assert_eq!(def.requires(), &["token.plus".to_string()]);
        assert_eq!(def.identity_key(), "binary.add");
    }

    #[test]
    fn serde_roundtrip() {
        let def = AstShapeDef::new("ast.lit", "lit")
            .with_payload_schema(serde_json::json!({"type": "number"}));
        let j = serde_json::to_string(&def).unwrap();
        let back: AstShapeDef = serde_json::from_str(&j).unwrap();
        assert_eq!(def, back);
    }

    #[test]
    fn serde_skips_null_payload() {
        let def = AstShapeDef::new("ast.lit", "lit");
        let j = serde_json::to_string(&def).unwrap();
        assert!(!j.contains("payload_schema"));
    }

    #[test]
    fn equality() {
        let a = AstShapeDef::new("a", "k");
        let b = AstShapeDef::new("a", "k");
        assert_eq!(a, b);
    }

    #[test]
    fn is_union_type() {
        // AST shape declarations are structural facts, so they merge
        // idempotently rather than colliding.
        assert!(AstShapeDef::UNION);
    }

    #[test]
    fn default_children_is_none() {
        let def = AstShapeDef::new("ast.assign", "assign");
        assert!(def.children.is_none());
        // Positional fallback remains (backward compatible).
        assert_eq!(def.role_index("target"), None);
    }

    #[test]
    fn role_index_resolves_positional_roles() {
        use crate::ChildRoleSpec;
        let def = AstShapeDef::new("ast.assign", "assign").with_children(vec![
            ChildRoleSpec {
                role: "target".into(),
                variadic: false,
                optional: false,
            },
            ChildRoleSpec {
                role: "value".into(),
                variadic: false,
                optional: false,
            },
        ]);
        assert_eq!(def.role_index("target"), Some(0));
        assert_eq!(def.role_index("value"), Some(1));
        assert_eq!(def.role_index("nope"), None);
        assert!(def.child_role("value").is_some());
    }

    #[test]
    fn role_index_resolves_variadic_role() {
        use crate::ChildRoleSpec;
        let def = AstShapeDef::new("ast.block", "block").with_children(vec![ChildRoleSpec {
            role: "statements".into(),
            variadic: true,
            optional: false,
        }]);
        // Variadic role resolves to its start index (all children from here).
        assert_eq!(def.role_index("statements"), Some(0));
        assert!(def.role_is_variadic("statements"));
        assert!(!def.role_is_variadic("unknown"));
    }

    #[test]
    fn role_serde_roundtrip() {
        use crate::ChildRoleSpec;
        let def = AstShapeDef::new("ast.block", "block").with_children(vec![ChildRoleSpec {
            role: "statements".into(),
            variadic: true,
            optional: false,
        }]);
        let j = serde_json::to_string(&def).unwrap();
        let back: AstShapeDef = serde_json::from_str(&j).unwrap();
        assert_eq!(def, back);
        // With children declared, the field round-trips; variadic:false is
        // skipped on the wire (it is the default), but variadic:true is kept.
        assert!(j.contains("\"children\""));
        assert!(j.contains("\"variadic\":true") || j.contains("\"variadic\": true"));
        let plain = AstShapeDef::new("ast.assign", "assign");
        let jp = serde_json::to_string(&plain).unwrap();
        assert!(!jp.contains("\"children\""));
    }

    #[test]
    fn merge_same_node_kind_is_idempotent() {
        use crate::FragmentSet;
        let mut set: FragmentSet<AstShapeDef> = FragmentSet::new();
        let first = AstShapeDef::new("ast.binary.add", "binary.add")
            .with_payload_schema(serde_json::json!({"first": true}));
        let second = AstShapeDef::new("ast.binary.add.dup", "binary.add")
            .with_payload_schema(serde_json::json!({"first": false}));
        set.merge(first.clone()).expect("first merge ok");
        // Merging a second shape for the same node_kind is a no-op (union),
        // NOT a collision — even though the ids differ.
        set.merge(second).expect("duplicate merge is idempotent");
        assert_eq!(set.len(), 1);
        // The first declaration is kept.
        let kept = set.get_by_identity("binary.add").unwrap();
        assert_eq!(kept.id(), "ast.binary.add");
        assert_eq!(kept.payload_schema, serde_json::json!({"first": true}));
    }

    /// `match`'s `[scrutinee, {motive, optional}, block]` shape.
    fn match_shape() -> AstShapeDef {
        AstShapeDef::new("ast.match", "match").with_children(vec![
            ChildRoleSpec {
                role: "scrutinee".into(),
                variadic: false,
                optional: false,
            },
            ChildRoleSpec {
                role: "motive".into(),
                variadic: false,
                optional: true,
            },
            ChildRoleSpec {
                role: "block".into(),
                variadic: false,
                optional: false,
            },
        ])
    }

    #[test]
    fn role_index_optional_roles_full_form() {
        let def = match_shape();
        // `role_index` resolves the full form: every declared role occupies
        // a slot, optional included.
        assert_eq!(def.role_index("scrutinee"), Some(0));
        assert_eq!(def.role_index("motive"), Some(1));
        assert_eq!(def.role_index("block"), Some(2));
        assert!(def.role_is_optional("motive"));
        assert!(!def.role_is_optional("block"));
        assert!(!def.role_is_optional("unknown"));
    }

    #[test]
    fn role_index_at_resolves_optional_absent() {
        let def = match_shape();
        // arity 2 — `match s { .. }` (no motive): `block` shifts down.
        assert_eq!(def.role_index_at("scrutinee", 2), Some(0));
        assert_eq!(def.role_index_at("motive", 2), None);
        assert_eq!(def.role_index_at("block", 2), Some(1));
    }

    #[test]
    fn role_index_at_resolves_optional_present() {
        let def = match_shape();
        // arity 3 — `match s return m with { .. }`: full-form positions.
        assert_eq!(def.role_index_at("scrutinee", 3), Some(0));
        assert_eq!(def.role_index_at("motive", 3), Some(1));
        assert_eq!(def.role_index_at("block", 3), Some(2));
    }

    #[test]
    fn role_index_at_trailing_optional() {
        // `assign`'s `[target, value, {body, optional}]` shape.
        let def = AstShapeDef::new("ast.assign", "assign").with_children(vec![
            ChildRoleSpec {
                role: "target".into(),
                variadic: false,
                optional: false,
            },
            ChildRoleSpec {
                role: "value".into(),
                variadic: false,
                optional: false,
            },
            ChildRoleSpec {
                role: "body".into(),
                variadic: false,
                optional: true,
            },
        ]);
        // `x = v` — no body.
        assert_eq!(def.role_index_at("target", 2), Some(0));
        assert_eq!(def.role_index_at("value", 2), Some(1));
        assert_eq!(def.role_index_at("body", 2), None);
        // `x = v in body` — trailing body present.
        assert_eq!(def.role_index_at("body", 3), Some(2));
    }

    #[test]
    fn role_index_at_rejects_underflow() {
        let def = match_shape();
        // arity below the required-role count resolves nothing.
        assert_eq!(def.role_index_at("scrutinee", 1), None);
        assert_eq!(def.role_index_at("block", 1), None);
    }

    #[test]
    fn role_index_at_no_optional_is_arity_independent() {
        let def = AstShapeDef::new("ast.arm", "arm").with_children(vec![
            ChildRoleSpec {
                role: "pattern".into(),
                variadic: false,
                optional: false,
            },
            ChildRoleSpec {
                role: "body".into(),
                variadic: false,
                optional: false,
            },
        ]);
        assert_eq!(def.role_index_at("pattern", 2), Some(0));
        assert_eq!(def.role_index_at("body", 2), Some(1));
    }

    #[test]
    fn child_role_spec_string_shorthand() {
        // Plain-string children lists stay valid YAML/JSON (backward compat).
        let def: AstShapeDef = serde_json::from_str(
            r#"{"id":"ast.pair","node_kind":"pair","children":["left","right"]}"#,
        )
        .unwrap();
        let children = def.children.as_ref().unwrap();
        assert_eq!(children[0].role, "left");
        assert!(!children[0].variadic);
        assert!(!children[0].optional);
        assert_eq!(children[1].role, "right");
        assert_eq!(def.role_index("left"), Some(0));
        assert_eq!(def.role_index("right"), Some(1));
    }

    #[test]
    fn child_role_spec_optional_deserializes() {
        // Mixed list: bare strings + the map form with `optional: true`.
        let def: AstShapeDef = serde_json::from_str(
            r#"{"id":"ast.match","node_kind":"match","children":["scrutinee",{"role":"motive","optional":true},"block"]}"#,
        )
        .unwrap();
        assert_eq!(def.role_index("block"), Some(2));
        assert_eq!(def.role_index_at("block", 2), Some(1));
        assert_eq!(def.role_index_at("block", 3), Some(2));
    }

    #[test]
    fn optional_flag_skipped_on_wire_when_false() {
        let def = AstShapeDef::new("ast.assign", "assign").with_children(vec![ChildRoleSpec {
            role: "target".into(),
            variadic: false,
            optional: false,
        }]);
        let j = serde_json::to_string(&def).unwrap();
        assert!(!j.contains("optional"));
    }
}
