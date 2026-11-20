use super::*;

/// The corpus is non-empty and every case has a non-empty AST.
#[test]
fn corpus_is_nonempty() {
    let c = corpus();
    assert!(c.len() >= 38, "corpus should have at least 38 cases");
    for case in &c {
        assert!(!case.ast.is_empty(), "case '{}' has empty ast", case.name);
    }
}

/// The arrow corpus is non-empty and every case has a non-empty AST.
#[test]
fn proc_corpus_is_nonempty() {
    let c = proc_corpus();
    assert!(!c.is_empty(), "arrow corpus should have at least one case");
    for case in &c {
        assert!(
            !case.ast.is_empty(),
            "arrow case '{}' has empty ast",
            case.name
        );
    }
}
