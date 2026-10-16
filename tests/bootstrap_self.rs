//! # bootstrap_self.rs — ADR-0041 Phase 3 self-hosting bootstrap test
//!
//! Tests that a handl **source program** can use `self` (an ambient global
//! variable holding the current `Language` value) and call
//! `eval(self, ast)` / `lex(self, text)` / `parse(self, tokens)` as ordinary
//! functions. The `run` host function is dropped (ADR-0047 §4); the composed
//! form `eval(self, parse(self, lex(self, text)))` is used instead.

use handl_kit_canonical::Kit;

/// `eval(self, parse(self, lex(self, "1 + 2")))` → `3`. The canonical
/// self-hosting bootstrap: a handl program evaluates handl source under
/// itself using the `self` global via the composed lex→parse→eval pipeline.
#[test]
fn handl_defining_handl_self_host_bootstrap() {
    let source = include_str!("../data/handl-defining-handl.hnl");
    let kit = Kit::new().expect("kit must assemble");
    let result = kit.run(source).expect("bootstrap must succeed");
    assert_eq!(
        result,
        serde_json::json!(3),
        "eval(self, parse(self, lex(self, '1 + 2'))) should return 3"
    );
}

/// `eval(self, parse(self, lex(self, "40 + 2")))` → `42`.
#[test]
fn run_self_inline() {
    let kit = Kit::new().expect("kit must assemble");
    let result = kit
        .run(r#"eval(self, parse(self, lex(self, "40 + 2")))"#)
        .expect("composed pipeline must succeed");
    assert_eq!(result, serde_json::json!(42));
}

/// Nested: `eval(self, parse(self, lex(self, "eval(self, parse(self, lex(self, \"1 + 1\")))")))` → `2`.
#[test]
fn nested_run_self() {
    let kit = Kit::new().expect("kit must assemble");
    let src =
        r#"eval(self, parse(self, lex(self, "eval(self, parse(self, lex(self, \"1 + 1\")))")))"#;
    let result = kit.run(src).expect("nested pipeline must succeed");
    assert_eq!(result, serde_json::json!(2));
}

/// `self` alone evaluates to the current `Language` value (a first-class
/// value carrying the actual `handl_language::Language` data).
#[test]
fn self_global_returns_language_value() {
    let kit = Kit::new().expect("kit must assemble");
    let result = kit.run("self").expect("self must succeed");
    assert!(
        handl_language::is_language_value(&result),
        "self should return a Language value, got: {}",
        result
    );
}

/// Full pipeline from source: `eval(self, parse(self, lex(self, "1 + 2")))` → `3`.
#[test]
fn full_pipeline_from_source() {
    let kit = Kit::new().expect("kit must assemble");
    let src = r#"eval(self, parse(self, lex(self, "1 + 2")))"#;
    let result = kit.run(src).expect("pipeline must succeed");
    assert_eq!(result, serde_json::json!(3));
}
