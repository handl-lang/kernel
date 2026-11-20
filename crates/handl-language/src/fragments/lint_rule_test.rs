use super::*;
use crate::fragment_set::FragmentSet;

#[test]
fn serde_roundtrip_match_and_native() {
    let rules = vec![
        LintRuleDef::new(
            "lint.simplify-paren",
            "simplify-paren",
            "warning",
            "redundant parentheses around '{source:body}'",
            LintCheck::Match {
                node_kind: "paren".into(),
                when: Some(TransformCondition::ChildCount(1)),
            },
        )
        .with_fix(LintFix::Unwrap {
            index: None,
            role: Some("body".into()),
        }),
        LintRuleDef::new(
            "lint.scope.unbound-wire",
            "unbound-wire",
            "error",
            "reference to unbound name '{name}'",
            LintCheck::Native("scope.unbound-wire".into()),
        ),
    ];
    let j = serde_json::to_string(&rules).unwrap();
    let back: Vec<LintRuleDef> = serde_json::from_str(&j).unwrap();
    assert_eq!(rules, back);
}

#[test]
fn serde_skips_defaults() {
    let def = LintRuleDef::new(
        "lint.x",
        "x",
        "warning",
        "msg",
        LintCheck::Native("n".into()),
    );
    let j = serde_json::to_string(&def).unwrap();
    assert!(!j.contains("fix"));
    assert!(!j.contains("replaces"));
    assert!(!j.contains("requires"));
}

#[test]
fn merge_collision_same_id() {
    let mut set: FragmentSet<LintRuleDef> = FragmentSet::new();
    set.merge(LintRuleDef::new(
        "lint.a",
        "a",
        "warning",
        "m",
        LintCheck::Native("n".into()),
    ))
    .unwrap();
    // A different id is NOT a collision — `id` is the identity key.
    set.merge(LintRuleDef::new(
        "lint.b",
        "b",
        "warning",
        "m",
        LintCheck::Match {
            node_kind: "x".into(),
            when: None,
        },
    ))
    .unwrap();
    // Same id, different content, no `replaces` → collision.
    let err = set
        .merge(LintRuleDef::new(
            "lint.a",
            "a2",
            "warning",
            "m",
            LintCheck::Native("n2".into()),
        ))
        .unwrap_err();
    assert_eq!(
        err,
        crate::LangError::Collision {
            existing: "lint.a".into(),
            incoming: "lint.a".into()
        }
    );
    // `replaces` overrides cleanly.
    set.merge(
        LintRuleDef::new(
            "lint.a.v2",
            "a",
            "warning",
            "m",
            LintCheck::Native("n3".into()),
        )
        .with_replaces(vec!["lint.a".into()]),
    )
    .unwrap();
    assert!(set.get_by_id("lint.a").is_none());
    assert!(set.get_by_id("lint.a.v2").is_some());
}
