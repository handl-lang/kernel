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
    let def: AstShapeDef =
        serde_json::from_str(r#"{"id":"ast.pair","node_kind":"pair","children":["left","right"]}"#)
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
