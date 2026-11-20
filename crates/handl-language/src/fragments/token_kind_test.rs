use super::*;

#[test]
fn construct_and_accessors() {
    let t = TokenKindDef::new("token.number")
        .with_label("number")
        .with_replaces(vec!["token.int".into()])
        .with_requires(vec!["token.dot".into()]);
    assert_eq!(t.id(), "token.number");
    assert_eq!(t.label.as_deref(), Some("number"));
    assert_eq!(t.replaces(), &["token.int".to_string()]);
    assert_eq!(t.requires(), &["token.dot".to_string()]);
    assert_eq!(t.identity_key(), "token.number");
}

#[test]
fn serde_roundtrip() {
    let t = TokenKindDef::new("token.string").with_replaces(vec!["token.text".into()]);
    let j = serde_json::to_string(&t).unwrap();
    let back: TokenKindDef = serde_json::from_str(&j).unwrap();
    assert_eq!(t, back);
}

#[test]
fn category_pair_doc_serde_roundtrip() {
    let t = TokenKindDef::new("tok::open")
        .with_category("open-bracket")
        .with_pair("tok::close")
        .with_doc("opens a group");
    let j = serde_json::to_string(&t).unwrap();
    let back: TokenKindDef = serde_json::from_str(&j).unwrap();
    assert_eq!(t, back);
    assert_eq!(back.category.as_deref(), Some("open-bracket"));
    assert_eq!(back.pair.as_deref(), Some("tok::close"));
    assert_eq!(back.doc.as_deref(), Some("opens a group"));
}

#[test]
fn serde_backward_compat_without_new_fields() {
    // Third-party YAML/JSON without category/pair/doc still parses.
    let t: TokenKindDef = serde_json::from_str(r#"{"id":"tok::x"}"#).unwrap();
    assert_eq!(t.id(), "tok::x");
    assert!(t.category.is_none() && t.pair.is_none() && t.doc.is_none());
}

#[test]
fn equality() {
    assert_eq!(TokenKindDef::new("a"), TokenKindDef::new("a"));
    assert_ne!(TokenKindDef::new("a"), TokenKindDef::new("b"));
}

#[test]
fn skip_empty_fields_in_serde() {
    let t = TokenKindDef::new("token.x");
    let j = serde_json::to_string(&t).unwrap();
    assert!(!j.contains("replaces"));
    assert!(!j.contains("requires"));
    assert!(!j.contains("literal"));
    assert!(!j.contains("trivia"));
    assert!(!j.contains("category"));
    assert!(!j.contains("pair"));
    assert!(!j.contains("doc"));
}

#[test]
fn literal_kind_serde_roundtrip() {
    let t = TokenKindDef::new("token.number").with_literal(LiteralKind::Number);
    let j = serde_json::to_string(&t).unwrap();
    let back: TokenKindDef = serde_json::from_str(&j).unwrap();
    assert_eq!(t, back);
    assert!(j.contains("literal"));
}

#[test]
fn literal_kind_string_roundtrip() {
    let t = TokenKindDef::new("token.string").with_literal(LiteralKind::String {
        delim_chars: 1,
        escapes: vec![
            ("\\n".into(), "\n".into()),
            ("\\t".into(), "\t".into()),
            ("\\\"".into(), "\"".into()),
            ("\\\\".into(), "\\".into()),
        ],
    });
    let j = serde_json::to_string(&t).unwrap();
    let back: TokenKindDef = serde_json::from_str(&j).unwrap();
    assert_eq!(t, back);
}

#[test]
fn literal_kind_strip_affix_roundtrip() {
    let t = TokenKindDef::new("token.json").with_literal(LiteralKind::StripAffix {
        prefix: "json{".into(),
        suffix: "}".into(),
        wrap: Some(("{".into(), "}".into())),
    });
    let j = serde_json::to_string(&t).unwrap();
    let back: TokenKindDef = serde_json::from_str(&j).unwrap();
    assert_eq!(t, back);
}

#[test]
fn is_union_type() {
    // Token kind declarations are structural facts, so they merge
    // idempotently rather than colliding.
    assert!(TokenKindDef::UNION);
}

#[test]
fn merge_same_id_is_idempotent() {
    use crate::FragmentSet;
    let mut set: FragmentSet<TokenKindDef> = FragmentSet::new();
    let first = TokenKindDef::new("token.lparen").with_label("(");
    let second = TokenKindDef::new("token.lparen").with_label("(dup)");
    set.merge(first.clone()).expect("first merge ok");
    // Merging a second declaration with the same id is a no-op (union),
    // NOT a collision.
    set.merge(second).expect("duplicate merge is idempotent");
    assert_eq!(set.len(), 1);
    // The first declaration is kept.
    assert_eq!(
        set.get_by_id("token.lparen").unwrap().label.as_deref(),
        Some("(")
    );
}
