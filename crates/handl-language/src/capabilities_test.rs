use super::*;
use crate::fragments::{CapabilityDecl, EvalSchemeDef};
use crate::language::Language;
use serde_json::Value;

/// Convert `TermData` back to `Term` for APIs that require `Term`.
fn t(td: TermData) -> Term {
    td.to_term().expect("TermData -> Term conversion")
}

/// Native op without a literal payload (mirrors `TermData::op`).
fn op_native(name: &str, args: Vec<TermData>) -> TermData {
    if name == "const" && args.is_empty() {
        TermData::arr(Value::Null)
    } else {
        TermData::op(name, args, &ArrSource::Native, None)
    }
}

/// Native op with a literal payload (mirrors `TermData::op`).
fn op_lit(name: &str, args: Vec<TermData>, lit: impl Into<Value>) -> TermData {
    if name == "const" && args.is_empty() {
        TermData::arr(lit.into())
    } else {
        TermData::op(name, args, &ArrSource::Native, Some(lit.into()))
    }
}

/// Foreign op (mirrors `TermData::op`).
fn op_foreign(name: &str, args: Vec<TermData>) -> TermData {
    TermData::op(name, args, &ArrSource::Foreign(name.to_string()), None)
}

#[test]
fn foreign_names_collects_recursively() {
    let s = t(TermData::choice(
        op_foreign("fs.read", vec![op_foreign("fs.open", vec![])]),
        TermData::app(
            op_foreign("net.send", vec![]),
            vec![op_native("id", vec![])],
        ),
    ));
    let names = foreign_names(&s);
    assert!(names.contains("fs.read"));
    assert!(names.contains("fs.open"));
    assert!(names.contains("net.send"));
    assert_eq!(names.len(), 3);
}

#[test]
fn no_foreign_returns_empty() {
    let s = t(op_native("add", vec![op_native("id", vec![])]));
    assert!(foreign_names(&s).is_empty());
}

#[test]
fn capabilities_combines_foreign_and_declared() {
    let mut lang = Language::new();
    lang.eval
        .merge(EvalSchemeDef::new(
            "eval.io",
            "io",
            t(op_foreign(
                "fs.read",
                vec![op_lit("proj_child", vec![], Value::from(0u64))],
            )),
        ))
        .unwrap();
    lang.caps.merge(CapabilityDecl::new("net.connect")).unwrap();
    let caps = capabilities(&lang);
    assert!(caps.contains("fs.read"));
    assert!(caps.contains("net.connect"));
    assert_eq!(caps.len(), 2);
}

#[test]
fn no_foreign_language_returns_only_declared() {
    let mut lang = Language::new();
    lang.eval
        .merge(EvalSchemeDef::new(
            "eval.add",
            "binary.add",
            t(op_native(
                "add",
                vec![
                    op_lit("proj_child", vec![], Value::from(0u64)),
                    op_lit("proj_child", vec![], Value::from(1u64)),
                ],
            )),
        ))
        .unwrap();
    lang.caps.merge(CapabilityDecl::new("pure")).unwrap();
    let caps = capabilities(&lang);
    assert_eq!(caps, ["pure".to_string()].into_iter().collect());
}

#[test]
fn subset_of_passes() {
    let needed: BTreeSet<String> = ["a", "b"].into_iter().map(String::from).collect();
    let allowed: BTreeSet<String> = ["a", "b", "c"].into_iter().map(String::from).collect();
    assert!(subset_of(&needed, &allowed));
}

#[test]
fn subset_of_fails() {
    let needed: BTreeSet<String> = ["a", "d"].into_iter().map(String::from).collect();
    let allowed: BTreeSet<String> = ["a", "b", "c"].into_iter().map(String::from).collect();
    assert!(!subset_of(&needed, &allowed));
}

#[test]
fn subset_of_empty_needed_passes() {
    let allowed: BTreeSet<String> = ["a"].into_iter().map(String::from).collect();
    assert!(subset_of(&BTreeSet::new(), &allowed));
}

#[test]
fn foreign_names_nested_seq_loop() {
    let s = t(TermData::seq(
        TermData::loop_feedback(op_foreign("fs.read", vec![])),
        TermData::first(op_foreign("net.send", vec![])),
    ));
    let names = foreign_names(&s);
    assert!(names.contains("fs.read"));
    assert!(names.contains("net.send"));
    assert_eq!(names.len(), 2);
}
