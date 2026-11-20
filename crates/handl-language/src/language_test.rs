use super::*;
use crate::fragments::TypeRuleDef;
use crate::fragments::ast_shape::{AstDesugarChild, AstDesugarCondition, AstDesugarRule};
use crate::fragments::grammar::{AstShapeRef, GrammarPosition};
use crate::fragments::{RewriteStep, TransformCondition, TransformRule};
use crate::term::{ArrSource, Term};
use handl_calculus::TermData;

fn td(t: TermData) -> Term {
    t.to_term().expect("TermData -> Term")
}

#[test]
fn new_is_empty_with_v2() {
    let lang = Language::new();
    assert!(lang.tokens.is_empty());
    assert_eq!(lang.scheme_version, SchemeVersion::v2());
}

#[test]
fn default_is_empty_with_v2() {
    let lang = Language::default();
    assert!(lang.tokens.is_empty());
    assert_eq!(lang.scheme_version, SchemeVersion::v2());
}

#[test]
fn token_classification_helpers_are_data_driven() {
    // A language whose token kinds use *noncanonical* ids still
    // classifies via `category`/`pair`/`doc`/`label` — this is the
    // genericity property ADR-0044 requires of host tooling.
    let mut lang = Language::new();
    lang.tokens
        .merge(
            TokenKindDef::new("tok::name")
                .with_category("identifier")
                .with_label("ident"),
        )
        .unwrap();
    lang.tokens
        .merge(
            TokenKindDef::new("tok::open")
                .with_category("open-bracket")
                .with_pair("tok::close"),
        )
        .unwrap();
    lang.tokens
        .merge(
            TokenKindDef::new("tok::close")
                .with_category("close-bracket")
                .with_pair("tok::open"),
        )
        .unwrap();
    lang.tokens
        .merge(
            TokenKindDef::new("tok::kw")
                .with_category("keyword")
                .with_doc("docs!"),
        )
        .unwrap();

    assert_eq!(lang.token_category("tok::name"), Some("identifier"));
    assert!(lang.token_in_category("tok::kw", "keyword"));
    assert!(!lang.token_in_category("tok::kw", "identifier"));
    assert_eq!(lang.token_pair("tok::open"), Some("tok::close"));
    assert_eq!(lang.token_pair("tok::close"), Some("tok::open"));
    assert_eq!(lang.token_doc("tok::kw"), Some("docs!"));
    assert_eq!(lang.token_kind_for_label("ident"), Some("tok::name"));
    assert_eq!(lang.token_category("tok::missing"), None);
    assert_eq!(lang.token_kind_for_label("missing"), None);
}

#[test]
fn merge_all_sets() {
    let mut base = Language::new();
    let mut other = Language::new();
    other.tokens.merge(TokenKindDef::new("token.num")).unwrap();
    other
        .grammar
        .merge(GrammarRow::new(
            "g1",
            "token.plus",
            GrammarPosition::Infix,
            AstShapeRef::new("binary.add", 2),
        ))
        .unwrap();
    other
        .eval
        .merge(EvalSchemeDef::new(
            "e1",
            "binary.add",
            td(TermData::op("add", vec![], &ArrSource::Native, None)),
        ))
        .unwrap();
    other
        .types
        .merge(TypeRuleDef::new(
            "t1",
            "lit",
            td(TermData::op(
                "synth_child",
                vec![],
                &ArrSource::Judgment,
                None,
            )),
        ))
        .unwrap();
    other
        .ast
        .merge(AstShapeDef::new("a1", "binary.add"))
        .unwrap();
    other.caps.merge(CapabilityDecl::new("fs.read")).unwrap();
    other.options.merge(OptionSchema::new("opt.x")).unwrap();
    base.merge(other).unwrap();
    assert_eq!(base.tokens.len(), 1);
    assert_eq!(base.grammar.len(), 1);
    assert_eq!(base.eval.len(), 1);
    assert_eq!(base.types.len(), 1);
    assert_eq!(base.ast.len(), 1);
    assert_eq!(base.caps.len(), 1);
    assert_eq!(base.options.len(), 1);
}

#[test]
fn partial_failure_rolls_back_atomically() {
    let mut base = Language::new();
    base.tokens.merge(TokenKindDef::new("token.num")).unwrap();

    let mut other = Language::new();
    // This token merges fine.
    other.tokens.merge(TokenKindDef::new("token.str")).unwrap();
    // This eval collides: base already has "binary.add".
    other
        .eval
        .merge(EvalSchemeDef::new(
            "e1",
            "binary.add",
            td(TermData::op("add", vec![], &ArrSource::Native, None)),
        ))
        .unwrap();
    // Set up the base to collide on the eval set.
    base.eval
        .merge(EvalSchemeDef::new(
            "e0",
            "binary.add",
            td(TermData::op("add", vec![], &ArrSource::Native, None)),
        ))
        .unwrap();
    let snapshot = base.clone();

    // `other.eval` has "binary.add" which collides with base's "binary.add".
    let err = base.merge(other).unwrap_err();
    assert_eq!(
        err,
        LangError::Collision {
            existing: "e0".into(),
            incoming: "e1".into()
        }
    );
    // base unchanged.
    assert_eq!(base, snapshot);
    assert_eq!(base.tokens.len(), 1);
}

#[test]
fn transforms_for_sorts_by_priority() {
    let mut lang = Language::new();
    lang.transforms
        .merge(
            TransformDef::new("t.hi", "desugar", "x", TransformRule::Native("a".into()))
                .with_priority(10),
        )
        .unwrap();
    lang.transforms
        .merge(
            TransformDef::new("t.lo", "desugar", "x", TransformRule::Native("b".into()))
                .with_priority(-5),
        )
        .unwrap();
    lang.transforms
        .merge(TransformDef::new(
            "t.zero",
            "desugar",
            "x",
            TransformRule::Native("c".into()),
        ))
        .unwrap();
    // Other pass / other kind are not returned.
    lang.transforms
        .merge(TransformDef::new(
            "t.other",
            "lower",
            "x",
            TransformRule::Native("d".into()),
        ))
        .unwrap();
    lang.transforms
        .merge(TransformDef::new(
            "t.other2",
            "desugar",
            "y",
            TransformRule::Native("e".into()),
        ))
        .unwrap();

    let rules = lang.transforms_for("desugar", "x");
    let ids: Vec<&str> = rules.iter().map(|d| d.id.as_str()).collect();
    assert_eq!(ids, vec!["t.lo", "t.zero", "t.hi"]);
    assert!(lang.transforms_for("desugar", "nope").is_empty());
    assert!(lang.transforms_for("nope", "x").is_empty());
}

#[test]
fn merge_ast_fragment_lowers_desugar_to_transform() {
    let mut lang = Language::new();
    let shape = AstShapeDef::new("ast.nullish", "nullish").with_desugar(AstDesugarRule {
        target_kind: "if".into(),
        children: vec![
            AstDesugarChild::Keep(0),
            AstDesugarChild::Create {
                kind: "lit".into(),
                payload: None,
                children: vec![],
            },
        ],
        when: Some(AstDesugarCondition {
            child_index: 0,
            child_kind: "array".into(),
        }),
    });
    lang.merge_ast_fragment(shape).unwrap();

    let def = lang
        .transforms
        .get_by_id("transform.desugar.nullish")
        .expect("desugar rule lowered to a TransformDef");
    assert_eq!(def.pass, "desugar");
    assert_eq!(def.node_kind, "nullish");
    assert_eq!(def.priority, 0);
    assert_eq!(
        def.when,
        Some(TransformCondition::KindAt {
            index: Some(0),
            role: None,
            kind: "array".into()
        })
    );
    match &def.rule {
        TransformRule::Declarative {
            target_kind,
            children,
            payload,
        } => {
            assert_eq!(target_kind, "if");
            assert_eq!(*payload, None);
            assert_eq!(
                *children,
                vec![
                    RewriteStep::Keep(0),
                    RewriteStep::Create {
                        kind: "lit".into(),
                        payload: None,
                        children: vec![],
                    },
                ]
            );
        }
        _ => panic!("expected Declarative rule"),
    }
    // Lookup path finds it.
    assert_eq!(lang.transforms_for("desugar", "nullish").len(), 1);
}

#[test]
fn language_merge_lowers_desugar_too() {
    let mut base = Language::new();
    let mut other = Language::new();
    other
        .ast
        .merge(AstShapeDef::new("ast.x", "x").with_desugar(AstDesugarRule {
            target_kind: "y".into(),
            children: vec![AstDesugarChild::KeepRest(1)],
            when: None,
        }))
        .unwrap();
    base.merge(other).unwrap();
    let def = base.transforms.get_by_id("transform.desugar.x").unwrap();
    assert_eq!(def.pass, "desugar");
    assert!(def.when.is_none());
    match &def.rule {
        TransformRule::Declarative { children, .. } => {
            assert_eq!(*children, vec![RewriteStep::KeepRest(1)]);
        }
        _ => panic!("expected Declarative rule"),
    }
}

#[test]
fn ast_union_drop_does_not_lower() {
    // A second shape declaring the same node_kind is a union no-op; its
    // desugar rule must be dropped with it.
    let mut lang = Language::new();
    lang.merge_ast_fragment(AstShapeDef::new("ast.x", "x").with_desugar(AstDesugarRule {
        target_kind: "y".into(),
        children: vec![],
        when: None,
    }))
    .unwrap();
    // Union-dropped duplicate — different id, same node_kind.
    lang.merge_ast_fragment(
        AstShapeDef::new("ast.x.dup", "x").with_desugar(AstDesugarRule {
            target_kind: "z".into(),
            children: vec![],
            when: None,
        }),
    )
    .unwrap();
    assert_eq!(lang.transforms.len(), 1);
    let def = lang.transforms.get_by_id("transform.desugar.x").unwrap();
    match &def.rule {
        TransformRule::Declarative { target_kind, .. } => assert_eq!(target_kind, "y"),
        _ => panic!("expected Declarative rule"),
    }
    // Re-merging the identical fragment stays idempotent — no collision.
    let again = lang.clone();
    lang.merge_ast_fragment(AstShapeDef::new("ast.x", "x").with_desugar(AstDesugarRule {
        target_kind: "y".into(),
        children: vec![],
        when: None,
    }))
    .unwrap();
    assert_eq!(lang, again);
}

#[test]
fn ast_replace_updates_lowered_transform() {
    // Replacing a shape that carried a desugar rule replaces the
    // synthesized TransformDef instead of colliding.
    let mut lang = Language::new();
    lang.merge_ast_fragment(AstShapeDef::new("ast.x", "x").with_desugar(AstDesugarRule {
        target_kind: "y".into(),
        children: vec![],
        when: None,
    }))
    .unwrap();
    lang.merge_ast_fragment(
        AstShapeDef::new("ast.x2", "x")
            .with_replaces(vec!["ast.x".into()])
            .with_desugar(AstDesugarRule {
                target_kind: "z".into(),
                children: vec![],
                when: None,
            }),
    )
    .unwrap();
    assert_eq!(lang.transforms.len(), 1);
    let def = lang.transforms.get_by_id("transform.desugar.x").unwrap();
    match &def.rule {
        TransformRule::Declarative { target_kind, .. } => assert_eq!(target_kind, "z"),
        _ => panic!("expected Declarative rule"),
    }

    // Replacing with a shape that drops `desugar` removes the stale rule.
    lang.merge_ast_fragment(AstShapeDef::new("ast.x3", "x").with_replaces(vec!["ast.x2".into()]))
        .unwrap();
    assert!(lang.transforms.is_empty());
}

#[test]
fn serde_roundtrip() {
    let mut lang = Language::new();
    lang.tokens.merge(TokenKindDef::new("token.num")).unwrap();
    lang.caps.merge(CapabilityDecl::new("fs.read")).unwrap();
    let j = serde_json::to_string(&lang).unwrap();
    let back: Language = serde_json::from_str(&j).unwrap();
    assert_eq!(lang, back);
}

#[test]
fn scheme_version_serializes() {
    let lang = Language::new();
    let j = serde_json::to_string(&lang).unwrap();
    assert!(j.contains("\"v2\""));
    let back: Language = serde_json::from_str(&j).unwrap();
    assert_eq!(back.scheme_version, SchemeVersion::v2());
}
