use super::*;

#[test]
fn lex_returns_not_implemented() {
    let lang = Language::new();
    let src = Source::new("1 + 2");
    let err = lex(&lang, &src).unwrap_err();
    assert_eq!(err, LangError::NotImplemented);
}

#[test]
fn parse_returns_not_implemented() {
    let lang = Language::new();
    let toks = Tokens::new();
    let err = parse(&lang, &toks).unwrap_err();
    assert_eq!(err, LangError::NotImplemented);
}

#[test]
fn eval_returns_not_implemented() {
    let lang = Language::new();
    let ast = Ast::new();
    let err = eval(&lang, &ast).unwrap_err();
    assert_eq!(err, LangError::NotImplemented);
}

#[test]
fn run_returns_not_implemented() {
    let lang = Language::new();
    let src = Source::new("1 + 2");
    let err = run(&lang, &src).unwrap_err();
    assert_eq!(err, LangError::NotImplemented);
}

#[test]
fn source_constructors() {
    let s = Source::new("hi");
    assert_eq!(s.as_str(), "hi");
    let s2: Source = "ho".into();
    assert_eq!(s2.as_str(), "ho");
    let s3: Source = String::from("hey").into();
    assert_eq!(s3.as_str(), "hey");
}

#[test]
fn tokens_default_and_slice() {
    let t = Tokens::new();
    assert!(t.as_slice().is_empty());
}

#[test]
fn token_serde_roundtrip() {
    let t = Token {
        kind: "token.number".into(),
        text: "42".into(),
        start: 0,
        end: 2,
    };
    let j = serde_json::to_string(&t).unwrap();
    let back: Token = serde_json::from_str(&j).unwrap();
    assert_eq!(t, back);
}
