use super::*;

#[test]
fn construct_and_accessors() {
    let row = GrammarRow::new(
        "grammar.add.infix",
        "token.plus",
        GrammarPosition::Infix,
        AstShapeRef::new("binary.add", 2),
    )
    .with_binding_power(10, 11)
    .with_replaces(vec!["grammar.add.old".into()])
    .with_requires(vec!["token.plus".into()]);
    assert_eq!(row.id(), "grammar.add.infix");
    assert_eq!(row.token, "token.plus");
    assert_eq!(row.position, GrammarPosition::Infix);
    assert_eq!(row.binding_power, Some((10, 11)));
    assert_eq!(row.child_shape.arity, 2);
    assert_eq!(row.replaces(), &["grammar.add.old".to_string()]);
    assert_eq!(row.requires(), &["token.plus".to_string()]);
    assert_eq!(row.identity_key(), "token.plus@infix");
}

#[test]
fn prefix_identity_key() {
    let row = GrammarRow::new(
        "grammar.neg",
        "token.minus",
        GrammarPosition::Prefix,
        AstShapeRef::new("unary.neg", 1),
    );
    assert_eq!(row.identity_key(), "token.minus@prefix");
}

#[test]
fn serde_roundtrip() {
    let row = GrammarRow::new(
        "grammar.mul",
        "token.star",
        GrammarPosition::Infix,
        AstShapeRef::new("binary.mul", 2),
    )
    .with_binding_power(20, 21)
    .with_requires(vec!["token.star".into()]);
    let j = serde_json::to_string(&row).unwrap();
    let back: GrammarRow = serde_json::from_str(&j).unwrap();
    assert_eq!(row, back);
}

#[test]
fn equality() {
    let a = GrammarRow::new("a", "t", GrammarPosition::Infix, AstShapeRef::new("k", 1));
    let b = GrammarRow::new("a", "t", GrammarPosition::Infix, AstShapeRef::new("k", 1));
    assert_eq!(a, b);
}

#[test]
fn position_serde() {
    let j = serde_json::to_string(&GrammarPosition::Prefix).unwrap();
    assert_eq!(j, "\"Prefix\"");
    let back: GrammarPosition = serde_json::from_str(&j).unwrap();
    assert_eq!(back, GrammarPosition::Prefix);
}

#[test]
fn delimited_shape_roundtrip() {
    let shape = AstShapeRef::new("match", 2).with_delimited(DelimitedShape {
        open: "token.lbrace".into(),
        close: "token.rbrace".into(),
        separator: Some("token.comma".into()),
        container_kind: "block".into(),
        pair: Some(PairShape {
            separator: "token.colon".into(),
            node_kind: "arm".into(),
            record: false,
        }),
        open_is_operator_token: false,
        flatten: false,
        rest_token: None,
        newline_separator: false,
    });
    let row = GrammarRow::new(
        "grammar.match.prefix",
        "token.keyword.match",
        GrammarPosition::Prefix,
        shape,
    );
    let j = serde_json::to_string(&row).unwrap();
    let back: GrammarRow = serde_json::from_str(&j).unwrap();
    assert_eq!(row, back);
    assert!(j.contains("\"delimited\""));
    let plain = GrammarRow::new("g", "t", GrammarPosition::Infix, AstShapeRef::new("k", 1));
    let pj = serde_json::to_string(&plain).unwrap();
    assert!(!pj.contains("delimited"));
}
