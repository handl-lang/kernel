use super::*;
use crate::fragments::grammar::{AstShapeRef, GrammarPosition};
use crate::fragments::{CapabilityDecl, EvalSchemeDef, GrammarRow, OptionSchema, TokenKindDef};
use crate::term::{ArrSource, Term};
use handl_calculus::TermData;
use serde_json::Value;

/// Convert `TermData` back to `Term` for APIs that require `Term`.
fn t(td: TermData) -> Term {
    td.to_term().expect("TermData -> Term conversion")
}

/// Native op with a literal payload (mirrors `TermData::op`).
fn op_lit(name: &str, args: Vec<TermData>, lit: impl Into<Value>) -> TermData {
    if name == "const" && args.is_empty() {
        TermData::arr(lit.into())
    } else {
        TermData::op(name, args, &ArrSource::Native, Some(lit.into()))
    }
}

#[test]
fn empty_set() {
    let set: FragmentSet<TokenKindDef> = FragmentSet::new();
    assert!(set.is_empty());
    assert_eq!(set.len(), 0);
    assert!(set.override_chain().is_empty());
}

#[test]
fn default_is_empty() {
    let set: FragmentSet<TokenKindDef> = FragmentSet::default();
    assert!(set.is_empty());
}

#[test]
fn single_merge() {
    let mut set: FragmentSet<TokenKindDef> = FragmentSet::new();
    set.merge(TokenKindDef::new("token.num")).unwrap();
    assert_eq!(set.len(), 1);
    assert!(set.get_by_id("token.num").is_some());
}

#[test]
fn multi_merge() {
    let mut set: FragmentSet<TokenKindDef> = FragmentSet::new();
    set.merge(TokenKindDef::new("token.num")).unwrap();
    set.merge(TokenKindDef::new("token.str")).unwrap();
    set.merge(TokenKindDef::new("token.op")).unwrap();
    assert_eq!(set.len(), 3);
}

#[test]
fn declared_override_records_chain() {
    let mut set: FragmentSet<TokenKindDef> = FragmentSet::new();
    set.merge(TokenKindDef::new("token.num")).unwrap();
    set.merge(TokenKindDef::new("token.num2").with_replaces(vec!["token.num".into()]))
        .unwrap();
    assert_eq!(set.len(), 1);
    assert!(set.get_by_id("token.num").is_none());
    assert!(set.get_by_id("token.num2").is_some());
    assert_eq!(
        set.override_chain(),
        &[("token.num2".into(), "token.num".into())]
    );
}

#[test]
fn collision_without_replaces_errors() {
    // EvalSchemeDef is a non-union (behavioral) type: two schemes for the
    // same node_kind without `replaces` is a real conflict. (TokenKindDef
    // and AstShapeDef are now union types, so they can't demonstrate the
    // collision path.)
    let mut set: FragmentSet<EvalSchemeDef> = FragmentSet::new();
    set.merge(EvalSchemeDef::new(
        "eval.x",
        "x",
        t(op_lit("proj_child", vec![], Value::from(0u64))),
    ))
    .unwrap();
    // Same identity key (node_kind "x"), different id/content → collision.
    let err = set
        .merge(EvalSchemeDef::new(
            "eval.x2",
            "x",
            t(op_lit("proj_child", vec![], Value::from(1u64))),
        ))
        .unwrap_err();
    assert_eq!(
        err,
        LangError::Collision {
            existing: "eval.x".into(),
            incoming: "eval.x2".into()
        }
    );
    // Original unchanged.
    assert_eq!(set.len(), 1);
    assert!(set.get_by_id("eval.x").is_some());
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

#[test]
fn cyclic_replace_errors() {
    let mut set: FragmentSet<TokenKindDef> = FragmentSet::new();
    // B replaces A.
    set.merge(TokenKindDef::new("a")).unwrap();
    set.merge(TokenKindDef::new("b").with_replaces(vec!["a".into()]))
        .unwrap();
    // Now A (re-added) replaces B → cycle.
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
fn diamond_replaces_no_cycle_revisits_node() {
    // Exercises detect_cycle's visited-revisit (false) and no-neighbors
    // (None) paths without forming a cycle.
    let mut set: FragmentSet<TokenKindDef> = FragmentSet::new();
    set.merge(TokenKindDef::new("d")).unwrap();
    set.merge(TokenKindDef::new("b").with_replaces(vec!["d".into()]))
        .unwrap();
    // Re-add d (it was removed by the replace).
    set.merge(TokenKindDef::new("d")).unwrap();
    set.merge(TokenKindDef::new("c").with_replaces(vec!["d".into()]))
        .unwrap();
    // a replaces [b, c] — diamond shape, no cycle.
    set.merge(TokenKindDef::new("a").with_replaces(vec!["b".into(), "c".into()]))
        .unwrap();
    assert!(set.get_by_id("a").is_some());
    assert!(set.get_by_id("b").is_none());
    assert!(set.get_by_id("c").is_none());
}

#[test]
fn union_already_present_with_missing_requires_errors() {
    let mut set: FragmentSet<CapabilityDecl> = FragmentSet::new();
    set.merge(CapabilityDecl::new("fs.read")).unwrap();
    // Same id (union, occupied) but incoming requires an absent id.
    let err = set
        .merge(CapabilityDecl::new("fs.read").with_requires(vec!["fs.open".into()]))
        .unwrap_err();
    assert_eq!(
        err,
        LangError::MissingRequires {
            missing: vec!["fs.open".into()]
        }
    );
    // Existing unchanged.
    assert_eq!(set.len(), 1);
}

#[test]
fn capability_union_idempotent() {
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

#[test]
fn grammar_identity_key_is_token_position() {
    let mut set: FragmentSet<GrammarRow> = FragmentSet::new();
    set.merge(GrammarRow::new(
        "g1",
        "token.plus",
        GrammarPosition::Infix,
        AstShapeRef::new("binary.add", 2),
    ))
    .unwrap();
    // Same token+position, different id → collision.
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
    // Same token, different position → ok.
    set.merge(GrammarRow::new(
        "g3",
        "token.plus",
        GrammarPosition::Prefix,
        AstShapeRef::new("unary.neg", 1),
    ))
    .unwrap();
    assert_eq!(set.len(), 2);
}

#[test]
fn eval_scheme_identity_key_is_node_kind() {
    let mut set: FragmentSet<EvalSchemeDef> = FragmentSet::new();
    set.merge(EvalSchemeDef::new(
        "e1",
        "binary.add",
        t(op_lit("const", vec![], Value::Null)),
    ))
    .unwrap();
    let err = set
        .merge(EvalSchemeDef::new(
            "e2",
            "binary.add",
            t(op_lit("const", vec![], Value::Null)),
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
fn option_identity_key_is_id() {
    let mut set: FragmentSet<OptionSchema> = FragmentSet::new();
    set.merge(OptionSchema::new("opt.x")).unwrap();
    let err = set
        .merge(OptionSchema::new("opt.x").with_default(Value::from(1)))
        .unwrap_err();
    assert_eq!(
        err,
        LangError::Collision {
            existing: "opt.x".into(),
            incoming: "opt.x".into()
        }
    );
}

#[test]
fn requires_absent_errors() {
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
fn requires_present_succeeds() {
    let mut set: FragmentSet<TokenKindDef> = FragmentSet::new();
    set.merge(TokenKindDef::new("token.lparen")).unwrap();
    set.merge(TokenKindDef::new("token.rparen")).unwrap();
    set.merge(
        TokenKindDef::new("token.call")
            .with_requires(vec!["token.lparen".into(), "token.rparen".into()]),
    )
    .unwrap();
    assert_eq!(set.len(), 3);
}

#[test]
fn missing_optional_merges_successfully() {
    // `optional` is not a Phase 1 field; a fragment with no `requires`
    // for an absent dependency simply merges.
    let mut set: FragmentSet<TokenKindDef> = FragmentSet::new();
    set.merge(TokenKindDef::new("token.call")).unwrap();
    assert_eq!(set.len(), 1);
}

#[test]
fn replace_then_requires_validates_against_post_merge_ids() {
    let mut set: FragmentSet<TokenKindDef> = FragmentSet::new();
    set.merge(TokenKindDef::new("token.lparen")).unwrap();
    set.merge(TokenKindDef::new("old")).unwrap();
    // Replacing `old` and requiring `token.lparen` (present) → ok.
    set.merge(
        TokenKindDef::new("new")
            .with_replaces(vec!["old".into()])
            .with_requires(vec!["token.lparen".into()]),
    )
    .unwrap();
    assert_eq!(set.len(), 2);
}

#[test]
fn replace_removes_required_id_then_requires_fails() {
    let mut set: FragmentSet<TokenKindDef> = FragmentSet::new();
    set.merge(TokenKindDef::new("dep")).unwrap();
    set.merge(TokenKindDef::new("old")).unwrap();
    // Replacing `dep` (removing it) while requiring `dep` → fails.
    let err = set
        .merge(
            TokenKindDef::new("new")
                .with_replaces(vec!["dep".into()])
                .with_requires(vec!["dep".into()]),
        )
        .unwrap_err();
    assert_eq!(
        err,
        LangError::MissingRequires {
            missing: vec!["dep".into()]
        }
    );
    // Nothing mutated.
    assert!(set.get_by_id("dep").is_some());
    assert!(set.get_by_id("old").is_some());
}

#[test]
fn union_requires_validated() {
    let mut set: FragmentSet<CapabilityDecl> = FragmentSet::new();
    let err = set
        .merge(CapabilityDecl::new("fs.read").with_requires(vec!["fs.open".into()]))
        .unwrap_err();
    assert_eq!(
        err,
        LangError::MissingRequires {
            missing: vec!["fs.open".into()]
        }
    );
}

#[test]
fn serde_roundtrip() {
    let mut set: FragmentSet<TokenKindDef> = FragmentSet::new();
    set.merge(TokenKindDef::new("a")).unwrap();
    set.merge(TokenKindDef::new("b").with_replaces(vec!["a".into()]))
        .unwrap();
    let j = serde_json::to_string(&set).unwrap();
    let back: FragmentSet<TokenKindDef> = serde_json::from_str(&j).unwrap();
    assert_eq!(set, back);
}

#[test]
fn get_by_identity_resolves_identity_key() {
    let mut set: FragmentSet<EvalSchemeDef> = FragmentSet::new();
    set.merge(EvalSchemeDef::new(
        "e1",
        "binary.add",
        t(op_lit("const", vec![], Value::Null)),
    ))
    .unwrap();
    // Identity key for EvalSchemeDef is node_kind, not id.
    assert!(set.get_by_identity("binary.add").is_some());
    assert!(set.get_by_identity("e1").is_none());
    assert!(set.get_by_identity("missing").is_none());
}

#[test]
fn get_by_identity_resolves_grammar_token_position() {
    let mut set: FragmentSet<GrammarRow> = FragmentSet::new();
    set.merge(GrammarRow::new(
        "g1",
        "token.plus",
        GrammarPosition::Infix,
        AstShapeRef::new("binary.add", 2),
    ))
    .unwrap();
    // Identity key for GrammarRow is "token@position".
    assert!(set.get_by_identity("token.plus@infix").is_some());
    assert!(set.get_by_identity("token.plus@prefix").is_none());
}
