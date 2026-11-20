use super::*;
use crate::term::ArrSource;
use handl_calculus::TermData;
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

#[test]
fn rule_matches_and_produces() {
    // ternary: cond >>> arr(tag) >>> Choice(then, else)
    let produced_scheme = t(TermData::seq(
        TermData::seq(
            op_lit("proj_child", vec![], Value::from(0u64)),
            op_native("tag", vec![]),
        ),
        TermData::choice(
            op_lit("proj_child", vec![], Value::from(1u64)),
            op_lit("proj_child", vec![], Value::from(2u64)),
        ),
    ));
    let rules = vec![DesugarRule::new("ternary", produced_scheme.clone())];
    let produced = desugar(&rules, "ternary").unwrap();
    assert_eq!(produced, produced_scheme);
}

#[test]
fn unmatched_kind_returns_none() {
    let rules = vec![DesugarRule::new(
        "ternary",
        t(op_lit("const", vec![], Value::Null)),
    )];
    assert!(desugar(&rules, "binary.add").is_none());
}

#[test]
fn empty_rules_returns_none() {
    assert!(desugar(&[], "anything").is_none());
}

#[test]
fn first_match_wins() {
    let rules = vec![
        DesugarRule::new("k", t(op_lit("const", vec![], Value::from(1)))),
        DesugarRule::new("k", t(op_lit("const", vec![], Value::from(2)))),
    ];
    let produced = desugar(&rules, "k").unwrap();
    assert_eq!(produced, t(op_lit("const", vec![], Value::from(1))));
}
