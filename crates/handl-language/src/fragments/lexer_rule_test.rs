use super::*;
use crate::FragmentSet;

#[test]
fn construct_literal_rule() {
    let r = LexerRuleDef::new(
        "lex.plus",
        "token.plus",
        LexerPattern::Literal { text: "+".into() },
        20,
    );
    assert_eq!(r.id(), "lex.plus");
    assert_eq!(r.token_kind, "token.plus");
    assert_eq!(r.priority, 20);
    assert!(matches!(r.pattern, LexerPattern::Literal { .. }));
    assert_eq!(r.identity_key(), "lex.plus");
}

#[test]
fn construct_charclass_rule() {
    let r = LexerRuleDef::new(
        "lex.identifier",
        "token.identifier",
        LexerPattern::CharClass {
            start_chars: "a-zA-Z_".into(),
            continue_chars: "a-zA-Z0-9_".into(),
        },
        50,
    );
    assert!(matches!(r.pattern, LexerPattern::CharClass { .. }));
}

#[test]
fn construct_number_rule() {
    let r = LexerRuleDef::new("lex.number", "token.number", LexerPattern::Number, 40);
    assert!(matches!(r.pattern, LexerPattern::Number));
}

#[test]
fn construct_delimited_rule() {
    let r = LexerRuleDef::new(
        "lex.string",
        "token.string",
        LexerPattern::Delimited {
            open: "\"".into(),
            close: "\"".into(),
            escape: true,
            interpolation: false,
            close_at_eof: false,
            nesting_open: None,
        },
        40,
    );
    assert!(matches!(r.pattern, LexerPattern::Delimited { .. }));
}

#[test]
fn serde_roundtrip() {
    let r = LexerRuleDef::new(
        "lex.eqeq",
        "token.eqeq",
        LexerPattern::Literal { text: "==".into() },
        10,
    )
    .with_replaces(vec!["lex.eq".into()])
    .with_requires(vec!["token.eqeq".into()]);
    let j = serde_json::to_string(&r).unwrap();
    let back: LexerRuleDef = serde_json::from_str(&j).unwrap();
    assert_eq!(r, back);
}

#[test]
fn serde_roundtrip_delimited() {
    let r = LexerRuleDef::new(
        "lex.comment",
        "token.comment",
        LexerPattern::Delimited {
            open: "--".into(),
            close: "\n".into(),
            escape: false,
            interpolation: false,
            close_at_eof: true,
            nesting_open: None,
        },
        5,
    );
    let j = serde_json::to_string(&r).unwrap();
    let back: LexerRuleDef = serde_json::from_str(&j).unwrap();
    assert_eq!(r, back);
}

#[test]
fn skip_empty_fields_in_serde() {
    let r = LexerRuleDef::new("lex.x", "token.x", LexerPattern::Number, 40);
    let j = serde_json::to_string(&r).unwrap();
    assert!(!j.contains("replaces"));
    assert!(!j.contains("requires"));
}

#[test]
fn equality() {
    assert_eq!(
        LexerRuleDef::new("a", "token.a", LexerPattern::Number, 1),
        LexerRuleDef::new("a", "token.a", LexerPattern::Number, 1)
    );
    assert_ne!(
        LexerRuleDef::new("a", "token.a", LexerPattern::Number, 1),
        LexerRuleDef::new("b", "token.a", LexerPattern::Number, 1)
    );
}

#[test]
fn is_union_type() {
    assert!(LexerRuleDef::UNION);
}

#[test]
fn merge_same_id_is_idempotent() {
    let mut set: FragmentSet<LexerRuleDef> = FragmentSet::new();
    let first = LexerRuleDef::new(
        "lex.plus",
        "token.plus",
        LexerPattern::Literal { text: "+".into() },
        20,
    );
    let second = LexerRuleDef::new(
        "lex.plus",
        "token.plus",
        LexerPattern::Literal { text: "+".into() },
        99,
    );
    set.merge(first.clone()).expect("first merge ok");
    // Merging a second declaration with the same id is a no-op (union),
    // NOT a collision.
    set.merge(second).expect("duplicate merge is idempotent");
    assert_eq!(set.len(), 1);
    // The first declaration is kept (priority 20, not 99).
    assert_eq!(set.get_by_id("lex.plus").unwrap().priority, 20);
}

#[test]
fn merge_distinct_ids_same_token_kind_ok() {
    // Two rules with different ids but the same token_kind must both
    // merge successfully (identity key is id, not token_kind).
    let mut set: FragmentSet<LexerRuleDef> = FragmentSet::new();
    set.merge(LexerRuleDef::new(
        "lex.bool.true",
        "token.bool",
        LexerPattern::Literal {
            text: "true".into(),
        },
        15,
    ))
    .unwrap();
    set.merge(LexerRuleDef::new(
        "lex.bool.false",
        "token.bool",
        LexerPattern::Literal {
            text: "false".into(),
        },
        15,
    ))
    .unwrap();
    assert_eq!(set.len(), 2);
}
