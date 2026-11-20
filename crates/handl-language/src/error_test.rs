use super::*;
use crate::ast::{AstNode, Span};

#[test]
fn from_serde_json_error() {
    let err = serde_json::from_str::<serde_json::Value>("{bad}").unwrap_err();
    let lang_err = LangError::from(err);
    assert!(matches!(lang_err, LangError::Serde(_)));
}

#[test]
fn display_messages() {
    assert_eq!(
        format!("{}", LangError::NotImplemented),
        "not implemented: no engine bound for this stage"
    );
    assert_eq!(
        format!(
            "{}",
            LangError::Collision {
                existing: "a".into(),
                incoming: "b".into()
            }
        ),
        "collision: existing a conflicts with incoming b"
    );
    assert_eq!(
        format!(
            "{}",
            LangError::UnknownReplace {
                missing: "x".into()
            }
        ),
        "unknown replace target: x"
    );
    assert_eq!(
        format!(
            "{}",
            LangError::MissingRequires {
                missing: vec!["y".into()]
            }
        ),
        "missing required fragments: [\"y\"]"
    );
    assert_eq!(
        format!(
            "{}",
            LangError::CyclicReplace {
                chain: vec!["a".into(), "b".into(), "a".into()]
            }
        ),
        "cyclic replace chain: [\"a\", \"b\", \"a\"]"
    );
    assert_eq!(
        format!("{}", LangError::AstIndexOutOfBounds { index: 5 }),
        "ast index out of bounds: 5"
    );
    assert_eq!(
        format!("{}", LangError::Serde("boom".into())),
        "serde error: boom"
    );
    assert_eq!(
        format!("{}", LangError::engine("nope")),
        "engine error: nope"
    );
    assert_eq!(
        format!(
            "{}",
            LangError::engine_node(
                "boom",
                &AstNode::new("binary.add").with_span(Span { start: 12, end: 15 })
            )
        ),
        "engine error: boom at 12..15 in binary.add"
    );
    assert_eq!(
        format!("{}", LangError::engine_node("boom", &AstNode::new("lit"))),
        "engine error: boom in lit"
    );
    assert_eq!(
        format!(
            "{}",
            LangError::engine_at("boom", Some(Span { start: 0, end: 3 }), Some("var"))
        ),
        "engine error: boom at 0..3 in var"
    );
    assert_eq!(
        format!("{}", LangError::UnknownVariable { name: "x".into() }),
        "unknown variable: x"
    );
    assert_eq!(
        format!(
            "{}",
            LangError::LexError {
                position: 7,
                message: "unrecognized character".into()
            }
        ),
        "lex error at position 7: unrecognized character"
    );
}

#[test]
fn span_accessor_returns_engine_span() {
    let with_span = LangError::engine_at("boom", Some(Span { start: 1, end: 4 }), Some("x"));
    assert_eq!(with_span.span(), Some(Span { start: 1, end: 4 }));
    let without_span = LangError::engine("boom");
    assert_eq!(without_span.span(), None);
    // Non-Engine variants never carry a span.
    assert_eq!(LangError::NotImplemented.span(), None);
}

#[test]
fn with_node_attaches_span_and_kind() {
    let err = LangError::engine("nope");
    assert!(err.span().is_none());
    let node = AstNode::new("binary.add").with_span(Span { start: 12, end: 15 });
    let err = err.with_node(&node);
    assert_eq!(err.span(), Some(Span { start: 12, end: 15 }));
    // Display now includes the source-location suffix.
    assert_eq!(
        format!("{}", err),
        "engine error: nope at 12..15 in binary.add"
    );
    match err {
        LangError::Engine {
            node_kind: Some(ref k),
            ..
        } => assert_eq!(k, "binary.add"),
        other => panic!("expected Engine variant, got {:?}", other),
    }
}

#[test]
fn with_node_is_idempotent_when_span_already_set() {
    let err = LangError::engine_node(
        "boom",
        &AstNode::new("lit").with_span(Span { start: 0, end: 1 }),
    );
    let original_span = err.span();
    let other = AstNode::new("binary.add").with_span(Span {
        start: 99,
        end: 100,
    });
    let err = err.with_node(&other);
    // Span already set → with_node must not overwrite it.
    assert_eq!(err.span(), original_span);
}

#[test]
fn with_span_attaches_explicit_span() {
    let err = LangError::engine("nope");
    let err = err.with_span(Span { start: 5, end: 8 });
    assert_eq!(err.span(), Some(Span { start: 5, end: 8 }));
    assert_eq!(format!("{}", err), "engine error: nope at 5..8");
}

#[test]
fn with_node_leaves_non_engine_variants_untouched() {
    let err = LangError::UnknownVariable { name: "x".into() };
    let node = AstNode::new("var").with_span(Span { start: 0, end: 1 });
    let err = err.with_node(&node);
    assert!(matches!(err, LangError::UnknownVariable { .. }));
    assert_eq!(err.span(), None);
}
