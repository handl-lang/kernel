//! Integration test: every conflict scenario from ADR-0044 §5, positive and
//! negative.

use handl_language::{
    AstShapeDef, AstShapeRef, CapabilityDecl, EvalSchemeDef, FragmentSet, GrammarPosition,
    GrammarRow, LangError, OptionSchema, Scheme, TokenKindDef,
};
use serde_json::Value;

// --- TokenKindDef: identity key = id, union (idempotent) ---

#[test]
fn token_duplicate_same_id_is_idempotent() {
    // TokenKindDef is a union type: token kind declarations are structural
    // facts ("this token exists"), so merging a duplicate is a no-op, not a
    // collision.
    let mut set: FragmentSet<TokenKindDef> = FragmentSet::new();
    set.merge(TokenKindDef::new("token.num").with_label("first"))
        .unwrap();
    // Same id, different content → idempotent (first wins), NOT a collision.
    set.merge(TokenKindDef::new("token.num").with_label("other"))
        .unwrap();
    assert_eq!(set.len(), 1);
    assert_eq!(
        set.get_by_id("token.num").unwrap().label.as_deref(),
        Some("first")
    );
}

#[test]
fn token_override_succeeds() {
    let mut set: FragmentSet<TokenKindDef> = FragmentSet::new();
    set.merge(TokenKindDef::new("token.num")).unwrap();
    set.merge(TokenKindDef::new("token.num2").with_replaces(vec!["token.num".into()]))
        .unwrap();
    assert!(set.get_by_id("token.num").is_none());
    assert!(set.get_by_id("token.num2").is_some());
}

// --- GrammarRow: identity key = (token, position) ---

#[test]
fn grammar_collision_same_token_position_errors() {
    let mut set: FragmentSet<GrammarRow> = FragmentSet::new();
    set.merge(GrammarRow::new(
        "g1",
        "token.plus",
        GrammarPosition::Infix,
        AstShapeRef::new("binary.add", 2),
    ))
    .unwrap();
    let err = set
        .merge(GrammarRow::new(
            "g2",
            "token.plus",
            GrammarPosition::Infix,
            AstShapeRef::new("binary.add", 2),
        ))
        .unwrap_err();
    assert_eq!(
        err,
        LangError::Collision {
            existing: "g1".into(),
            incoming: "g2".into()
        }
    );
}

#[test]
fn grammar_same_token_different_position_ok() {
    let mut set: FragmentSet<GrammarRow> = FragmentSet::new();
    set.merge(GrammarRow::new(
        "g1",
        "token.minus",
        GrammarPosition::Infix,
        AstShapeRef::new("binary.sub", 2),
    ))
    .unwrap();
    set.merge(GrammarRow::new(
        "g2",
        "token.minus",
        GrammarPosition::Prefix,
        AstShapeRef::new("unary.neg", 1),
    ))
    .unwrap();
    assert_eq!(set.len(), 2);
}

#[test]
fn grammar_override_succeeds() {
    let mut set: FragmentSet<GrammarRow> = FragmentSet::new();
    set.merge(GrammarRow::new(
        "g1",
        "token.plus",
        GrammarPosition::Infix,
        AstShapeRef::new("binary.add", 2),
    ))
    .unwrap();
    set.merge(
        GrammarRow::new(
            "g2",
            "token.plus",
            GrammarPosition::Infix,
            AstShapeRef::new("binary.add", 2),
        )
        .with_replaces(vec!["g1".into()]),
    )
    .unwrap();
    assert!(set.get_by_id("g1").is_none());
    assert!(set.get_by_id("g2").is_some());
}

// --- EvalSchemeDef: identity key = node_kind ---

#[test]
fn eval_collision_same_node_kind_errors() {
    let mut set: FragmentSet<EvalSchemeDef> = FragmentSet::new();
    set.merge(EvalSchemeDef::new(
        "e1",
        "binary.add",
        Scheme::lit(Value::Null),
    ))
    .unwrap();
    let err = set
        .merge(EvalSchemeDef::new(
            "e2",
            "binary.add",
            Scheme::lit(Value::Null),
        ))
        .unwrap_err();
    assert_eq!(
        err,
        LangError::Collision {
            existing: "e1".into(),
            incoming: "e2".into()
        }
    );
}

#[test]
fn eval_override_succeeds() {
    let mut set: FragmentSet<EvalSchemeDef> = FragmentSet::new();
    set.merge(EvalSchemeDef::new(
        "e1",
        "binary.add",
        Scheme::lit(Value::Null),
    ))
    .unwrap();
    set.merge(
        EvalSchemeDef::new("e2", "binary.add", Scheme::lit(Value::from(1)))
            .with_replaces(vec!["e1".into()]),
    )
    .unwrap();
    assert!(set.get_by_id("e1").is_none());
    assert!(set.get_by_id("e2").is_some());
}

// --- AstShapeDef: identity key = node_kind, union (idempotent) ---

#[test]
fn ast_shape_duplicate_same_node_kind_is_idempotent() {
    // AstShapeDef is a union type: AST shape declarations are structural
    // facts ("this node kind exists"), so merging a duplicate (same
    // node_kind) is a no-op, not a collision — even when the ids differ.
    let mut set: FragmentSet<AstShapeDef> = FragmentSet::new();
    set.merge(AstShapeDef::new("a1", "binary.add")).unwrap();
    // Same node_kind, different id → idempotent (first wins), NOT a collision.
    set.merge(AstShapeDef::new("a2", "binary.add")).unwrap();
    assert_eq!(set.len(), 1);
    assert!(set.get_by_id("a1").is_some());
    assert!(set.get_by_id("a2").is_none());
}

#[test]
fn ast_shape_override_succeeds() {
    let mut set: FragmentSet<AstShapeDef> = FragmentSet::new();
    set.merge(AstShapeDef::new("a1", "binary.add")).unwrap();
    set.merge(
        AstShapeDef::new("a2", "binary.add")
            .with_payload_schema(serde_json::json!({"type": "object"}))
            .with_replaces(vec!["a1".into()]),
    )
    .unwrap();
    assert!(set.get_by_id("a1").is_none());
    assert!(set.get_by_id("a2").is_some());
}

// --- CapabilityDecl: identity key = id, union (idempotent) ---

#[test]
fn capability_union_same_id_idempotent() {
    let mut set: FragmentSet<CapabilityDecl> = FragmentSet::new();
    set.merge(CapabilityDecl::new("fs.read")).unwrap();
    set.merge(CapabilityDecl::new("fs.read")).unwrap();
    assert_eq!(set.len(), 1);
}

#[test]
fn capability_distinct_ids_merge() {
    let mut set: FragmentSet<CapabilityDecl> = FragmentSet::new();
    set.merge(CapabilityDecl::new("fs.read")).unwrap();
    set.merge(CapabilityDecl::new("fs.write")).unwrap();
    assert_eq!(set.len(), 2);
}

// --- OptionSchema: identity key = id ---

#[test]
fn option_collision_same_id_errors() {
    let mut set: FragmentSet<OptionSchema> = FragmentSet::new();
    set.merge(OptionSchema::new("opt.x")).unwrap();
    let err = set.merge(OptionSchema::new("opt.x")).unwrap_err();
    assert_eq!(
        err,
        LangError::Collision {
            existing: "opt.x".into(),
            incoming: "opt.x".into()
        }
    );
}

#[test]
fn option_override_succeeds() {
    let mut set: FragmentSet<OptionSchema> = FragmentSet::new();
    set.merge(OptionSchema::new("opt.x")).unwrap();
    set.merge(
        OptionSchema::new("opt.x2")
            .with_default(Value::from(2))
            .with_replaces(vec!["opt.x".into()]),
    )
    .unwrap();
    assert!(set.get_by_id("opt.x").is_none());
    assert!(set.get_by_id("opt.x2").is_some());
}

// --- Cross-cutting: requires and cyclic replaces ---

#[test]
fn requires_absent_errors_negative() {
    let mut set: FragmentSet<TokenKindDef> = FragmentSet::new();
    let err = set
        .merge(TokenKindDef::new("token.call").with_requires(vec!["token.lparen".into()]))
        .unwrap_err();
    assert_eq!(
        err,
        LangError::MissingRequires {
            missing: vec!["token.lparen".into()]
        }
    );
}

#[test]
fn requires_present_positive() {
    let mut set: FragmentSet<TokenKindDef> = FragmentSet::new();
    set.merge(TokenKindDef::new("token.lparen")).unwrap();
    set.merge(TokenKindDef::new("token.call").with_requires(vec!["token.lparen".into()]))
        .unwrap();
    assert_eq!(set.len(), 2);
}

#[test]
fn cyclic_replace_errors() {
    let mut set: FragmentSet<TokenKindDef> = FragmentSet::new();
    set.merge(TokenKindDef::new("a")).unwrap();
    set.merge(TokenKindDef::new("b").with_replaces(vec!["a".into()]))
        .unwrap();
    let err = set
        .merge(TokenKindDef::new("a").with_replaces(vec!["b".into()]))
        .unwrap_err();
    assert_eq!(
        err,
        LangError::CyclicReplace {
            chain: vec!["a".into(), "b".into(), "a".into()]
        }
    );
}

#[test]
fn unknown_replace_errors() {
    let mut set: FragmentSet<TokenKindDef> = FragmentSet::new();
    let err = set
        .merge(TokenKindDef::new("a").with_replaces(vec!["ghost".into()]))
        .unwrap_err();
    assert_eq!(
        err,
        LangError::UnknownReplace {
            missing: "ghost".into()
        }
    );
}
