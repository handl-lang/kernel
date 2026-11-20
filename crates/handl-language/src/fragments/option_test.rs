use super::*;

#[test]
fn construct_and_accessors() {
    let o = OptionSchema::new("opt.indent")
        .with_default(Value::from(2))
        .with_possible_values(vec![Value::from(2), Value::from(4)])
        .with_description("indent width")
        .with_replaces(vec!["opt.indent.old".into()])
        .with_requires(vec!["opt.tab".into()]);
    assert_eq!(o.id(), "opt.indent");
    assert_eq!(o.default, Value::from(2));
    assert_eq!(o.possible_values.len(), 2);
    assert_eq!(o.description.as_deref(), Some("indent width"));
    assert_eq!(o.replaces(), &["opt.indent.old".to_string()]);
    assert_eq!(o.requires(), &["opt.tab".to_string()]);
    assert_eq!(o.identity_key(), "opt.indent");
}

#[test]
fn serde_roundtrip() {
    let o = OptionSchema::new("opt.x")
        .with_default(Value::from(true))
        .with_description("a flag");
    let j = serde_json::to_string(&o).unwrap();
    let back: OptionSchema = serde_json::from_str(&j).unwrap();
    assert_eq!(o, back);
}

#[test]
fn equality() {
    assert_eq!(OptionSchema::new("a"), OptionSchema::new("a"));
    assert_ne!(OptionSchema::new("a"), OptionSchema::new("b"));
}
