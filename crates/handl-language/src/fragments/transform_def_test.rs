use super::*;
use crate::fragment_set::FragmentSet;
use crate::fragments::ast_shape::AstDesugarCondition;

fn sample_rule() -> TransformRule {
    TransformRule::Declarative {
        target_kind: "binary.add".into(),
        children: vec![
            RewriteStep::Keep(0),
            RewriteStep::KeepRole("value".into()),
            RewriteStep::Create {
                kind: "lit".into(),
                payload: Some(Value::from(1)),
                children: vec![],
            },
        ],
        payload: None,
    }
}

#[test]
fn construct_and_accessors() {
    let def = TransformDef::new(
        "transform.desugar.nullish",
        "desugar",
        "nullish",
        sample_rule(),
    )
    .with_priority(10)
    .with_when(TransformCondition::ChildCount(2))
    .with_replaces(vec!["transform.desugar.nullish.old".into()])
    .with_requires(vec!["ast.nullish".into()]);
    assert_eq!(def.id(), "transform.desugar.nullish");
    assert_eq!(def.pass, "desugar");
    assert_eq!(def.node_kind, "nullish");
    assert_eq!(def.priority, 10);
    assert_eq!(def.when, Some(TransformCondition::ChildCount(2)));
    assert_eq!(
        def.replaces(),
        &["transform.desugar.nullish.old".to_string()]
    );
    assert_eq!(def.requires(), &["ast.nullish".to_string()]);
    assert_eq!(def.identity_key(), "desugar:nullish:10");
}

#[test]
fn identity_key_includes_pass_kind_priority() {
    let a = TransformDef::new("a", "desugar", "x", TransformRule::Native("n".into()));
    let b = TransformDef::new("b", "lower", "x", TransformRule::Native("n".into()));
    let c =
        TransformDef::new("c", "desugar", "x", TransformRule::Native("n".into())).with_priority(1);
    assert_eq!(a.identity_key(), "desugar:x:0");
    assert_eq!(b.identity_key(), "lower:x:0");
    assert_eq!(c.identity_key(), "desugar:x:1");
}

#[test]
fn serde_roundtrip_declarative() {
    let def = TransformDef::new("t1", "desugar", "nullish", sample_rule())
        .with_priority(-2)
        .with_when(TransformCondition::And(vec![
            TransformCondition::KindAt {
                index: Some(0),
                role: None,
                kind: "array".into(),
            },
            TransformCondition::Not(Box::new(TransformCondition::PayloadEq {
                path: "op".into(),
                value: Value::from("??"),
            })),
        ]));
    let j = serde_json::to_string(&def).unwrap();
    let back: TransformDef = serde_json::from_str(&j).unwrap();
    assert_eq!(def, back);
}

#[test]
fn serde_roundtrip_native_and_all_steps() {
    let def = TransformDef::new(
        "t2",
        "desugar",
        "while",
        TransformRule::Native("desugar.while".into()),
    );
    let j = serde_json::to_string(&def).unwrap();
    let back: TransformDef = serde_json::from_str(&j).unwrap();
    assert_eq!(def, back);
    // Every RewriteStep / TransformCondition variant round-trips.
    let steps = vec![
        RewriteStep::Keep(0),
        RewriteStep::KeepRole("statements".into()),
        RewriteStep::KeepPath(vec![0, 0]),
        RewriteStep::KeepRest(2),
        RewriteStep::Splice(1),
        RewriteStep::Fresh("rec_v".into()),
        RewriteStep::Create {
            kind: "k".into(),
            payload: None,
            children: vec![RewriteStep::Apply {
                rule_id: "r".into(),
                index: 0,
            }],
        },
        RewriteStep::Apply {
            rule_id: "r2".into(),
            index: 3,
        },
    ];
    let j = serde_json::to_string(&steps).unwrap();
    let back: Vec<RewriteStep> = serde_json::from_str(&j).unwrap();
    assert_eq!(steps, back);

    let conds = vec![
        TransformCondition::KindAt {
            index: None,
            role: Some("key".into()),
            kind: "array".into(),
        },
        TransformCondition::PayloadEq {
            path: "p".into(),
            value: Value::from(true),
        },
        TransformCondition::AttrEq {
            path: vec![0, 1],
            attr: "dim".into(),
            value: Some(Value::from(-1)),
        },
        TransformCondition::AttrEq {
            path: vec![],
            attr: "chunks".into(),
            value: None,
        },
        TransformCondition::SameAttr {
            path_a: vec![0],
            attr_a: "dim".into(),
            path_b: vec![1, 0],
            attr_b: "dim".into(),
        },
        TransformCondition::ChildCount(0),
        TransformCondition::And(vec![]),
        TransformCondition::Or(vec![TransformCondition::ChildCount(1)]),
        TransformCondition::Not(Box::new(TransformCondition::ChildCount(9))),
    ];
    let j = serde_json::to_string(&conds).unwrap();
    let back: Vec<TransformCondition> = serde_json::from_str(&j).unwrap();
    assert_eq!(conds, back);
}

#[test]
fn serde_roundtrip_replace() {
    // `Replace` round-trips through JSON like every other rule form.
    // (The YAML `!Replace` tag spelling is pinned end-to-end by
    // `handl-kit-data-prelude`'s `catopt_fragments` test, which loads
    // catopt's emitted `!Replace` rows through `language_from_dir`.)
    let def = TransformDef::new(
        "t.replace",
        "optimize",
        "neg",
        TransformRule::Replace { path: vec![0, 0] },
    );
    let j = serde_json::to_string(&def).unwrap();
    assert!(j.contains("\"Replace\""), "{j}");
    let back: TransformDef = serde_json::from_str(&j).unwrap();
    assert_eq!(def, back);
}

#[test]
fn serde_skips_defaults() {
    let def = TransformDef::new("t", "desugar", "x", TransformRule::Native("n".into()));
    let j = serde_json::to_string(&def).unwrap();
    assert!(!j.contains("priority"));
    assert!(!j.contains("when"));
    assert!(!j.contains("replaces"));
    assert!(!j.contains("requires"));
    // Deserialize minimal input — defaults fill in.
    let back: TransformDef = serde_json::from_str(&j).unwrap();
    assert_eq!(back.priority, 0);
    assert!(back.when.is_none());
}

#[test]
fn merge_collision_same_pass_kind_priority() {
    let mut set: FragmentSet<TransformDef> = FragmentSet::new();
    set.merge(TransformDef::new(
        "t1",
        "desugar",
        "x",
        TransformRule::Native("a".into()),
    ))
    .unwrap();
    // Same pass+kind+priority, different id → collision.
    let err = set
        .merge(TransformDef::new(
            "t2",
            "desugar",
            "x",
            TransformRule::Native("b".into()),
        ))
        .unwrap_err();
    assert_eq!(
        err,
        crate::LangError::Collision {
            existing: "t1".into(),
            incoming: "t2".into()
        }
    );
    // Different priority → distinct identity key → ok.
    set.merge(
        TransformDef::new("t3", "desugar", "x", TransformRule::Native("c".into())).with_priority(1),
    )
    .unwrap();
    // Different pass → distinct identity key → ok.
    set.merge(TransformDef::new(
        "t4",
        "lower",
        "x",
        TransformRule::Native("d".into()),
    ))
    .unwrap();
    assert_eq!(set.len(), 3);
}

#[test]
fn merge_replaces_overrides() {
    let mut set: FragmentSet<TransformDef> = FragmentSet::new();
    set.merge(TransformDef::new(
        "t1",
        "desugar",
        "x",
        TransformRule::Native("a".into()),
    ))
    .unwrap();
    set.merge(
        TransformDef::new("t2", "desugar", "x", TransformRule::Native("b".into()))
            .with_replaces(vec!["t1".into()]),
    )
    .unwrap();
    assert_eq!(set.len(), 1);
    assert!(set.get_by_id("t1").is_none());
    assert!(set.get_by_id("t2").is_some());
    assert_eq!(set.override_chain(), &[("t2".into(), "t1".into())]);
}

#[test]
fn lower_desugar_rule_converts() {
    let rule = AstDesugarRule {
        target_kind: "binary.eq".into(),
        children: vec![
            AstDesugarChild::Keep(0),
            AstDesugarChild::KeepPath(vec![1, 0]),
            AstDesugarChild::KeepRest(2),
            AstDesugarChild::Create {
                kind: "lit".into(),
                payload: Some(Value::from(0)),
                children: vec![AstDesugarChild::Keep(3)],
            },
        ],
        when: Some(AstDesugarCondition {
            child_index: 0,
            child_kind: "array".into(),
        }),
    };
    let def = lower_desugar_rule("entry", &rule);
    assert_eq!(def.id, "transform.desugar.entry");
    assert_eq!(def.pass, "desugar");
    assert_eq!(def.node_kind, "entry");
    assert_eq!(def.priority, 0);
    assert_eq!(
        def.when,
        Some(TransformCondition::KindAt {
            index: Some(0),
            role: None,
            kind: "array".into()
        })
    );
    match def.rule {
        TransformRule::Declarative {
            target_kind,
            children,
            payload,
        } => {
            assert_eq!(target_kind, "binary.eq");
            assert_eq!(payload, None);
            assert_eq!(
                children,
                vec![
                    RewriteStep::Keep(0),
                    RewriteStep::KeepPath(vec![1, 0]),
                    RewriteStep::KeepRest(2),
                    RewriteStep::Create {
                        kind: "lit".into(),
                        payload: Some(Value::from(0)),
                        children: vec![RewriteStep::Keep(3)],
                    },
                ]
            );
        }
        _ => panic!("expected Declarative"),
    }
}
