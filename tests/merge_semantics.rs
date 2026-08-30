//! Integration test: full kit-like merge sequences.
//!
//! Builds a base language and merges 5 fragments with overrides and excludes
//! (excludes are modeled by simply not merging the excluded fragment), then
//! asserts the resulting `Language` matches expectations.

use handl_language::{
    capabilities, AstShapeDef, AstShapeRef, CapabilityDecl, EvalSchemeDef, FragmentSet,
    GrammarPosition, GrammarRow, Language, Scheme, SchemeVersion, TokenKindDef,
};
use serde_json::Value;

fn add_lang() -> Language {
    let mut lang = Language::new();
    // Token kinds.
    lang.tokens.merge(TokenKindDef::new("token.num")).unwrap();
    lang.tokens.merge(TokenKindDef::new("token.plus")).unwrap();
    // Grammar row for infix add.
    lang.grammar
        .merge(
            GrammarRow::new(
                "grammar.add.infix",
                "token.plus",
                GrammarPosition::Infix,
                AstShapeRef::new("binary.add", 2),
            )
            .with_binding_power(10, 11),
        )
        .unwrap();
    // AST shape for binary.add.
    lang.ast.merge(AstShapeDef::new("ast.binary.add", "binary.add")).unwrap();
    // Eval scheme for binary.add.
    lang.eval
        .merge(EvalSchemeDef::new(
            "eval.binary.add",
            "binary.add",
            Scheme::prim("add", vec![Scheme::child(0), Scheme::child(1)]),
        ))
        .unwrap();
    lang
}

#[test]
fn base_language_has_expected_fragments() {
    let lang = add_lang();
    assert_eq!(lang.tokens.len(), 2);
    assert_eq!(lang.grammar.len(), 1);
    assert_eq!(lang.ast.len(), 1);
    assert_eq!(lang.eval.len(), 1);
    assert_eq!(lang.scheme_version, SchemeVersion::v1());
}

#[test]
fn five_fragments_with_overrides_and_excludes() {
    let mut lang = add_lang();

    // Fragment 1: a new token kind (additive).
    lang.tokens.merge(TokenKindDef::new("token.star")).unwrap();

    // Fragment 2: a grammar row for infix mul (additive).
    lang.grammar
        .merge(
            GrammarRow::new(
                "grammar.mul.infix",
                "token.star",
                GrammarPosition::Infix,
                AstShapeRef::new("binary.mul", 2),
            )
            .with_binding_power(20, 21),
        )
        .unwrap();

    // Fragment 3: override the add grammar row with a higher binding power.
    lang.grammar
        .merge(
            GrammarRow::new(
                "grammar.add.infix.v2",
                "token.plus",
                GrammarPosition::Infix,
                AstShapeRef::new("binary.add", 2),
            )
            .with_binding_power(12, 13)
            .with_replaces(vec!["grammar.add.infix".into()]),
        )
        .unwrap();

    // Fragment 4: override the eval scheme for binary.add.
    lang.eval
        .merge(
            EvalSchemeDef::new(
                "eval.binary.add.v2",
                "binary.add",
                Scheme::prim("add_checked", vec![Scheme::child(0), Scheme::child(1)]),
            )
            .with_replaces(vec!["eval.binary.add".into()]),
        )
        .unwrap();

    // Fragment 5: a declared capability.
    lang.caps.merge(CapabilityDecl::new("fs.read")).unwrap();

    // Excluded fragment: a token we choose NOT to merge (excludes are a kit
    // concern — modeled by simply not merging it).
    // (e.g. TokenKindDef::new("token.bang") is excluded.)

    // Assertions.
    assert_eq!(lang.tokens.len(), 3); // num, plus, star
    assert_eq!(lang.grammar.len(), 2); // add (overridden), mul
    assert_eq!(lang.ast.len(), 1);
    assert_eq!(lang.eval.len(), 1); // add (overridden)
    assert_eq!(lang.caps.len(), 1);

    // The override chain recorded the grammar and eval overrides.
    let grammar_chain = lang.grammar.override_chain();
    assert!(grammar_chain
        .iter()
        .any(|(n, r)| n == "grammar.add.infix.v2" && r == "grammar.add.infix"));
    let eval_chain = lang.eval.override_chain();
    assert!(eval_chain
        .iter()
        .any(|(n, r)| n == "eval.binary.add.v2" && r == "eval.binary.add"));

    // The overridden grammar row is gone; the new one is present.
    assert!(lang.grammar.get_by_id("grammar.add.infix").is_none());
    assert!(lang.grammar.get_by_id("grammar.add.infix.v2").is_some());
    assert!(lang.eval.get_by_id("eval.binary.add").is_none());
    assert!(lang.eval.get_by_id("eval.binary.add.v2").is_some());

    // Capabilities: no Foreign tags, so only the declared cap.
    let caps = capabilities(&lang);
    assert_eq!(caps, ["fs.read".to_string()].into_iter().collect());
}

#[test]
fn merge_two_languages_combines() {
    let mut base = add_lang();
    let mut extra = Language::new();
    extra.tokens.merge(TokenKindDef::new("token.star")).unwrap();
    extra.caps.merge(CapabilityDecl::new("net.send")).unwrap();
    base.merge(extra).unwrap();
    assert_eq!(base.tokens.len(), 3);
    assert_eq!(base.caps.len(), 1);
}

#[test]
fn empty_fragment_set_default() {
    let set: FragmentSet<TokenKindDef> = FragmentSet::new();
    assert!(set.is_empty());
}

#[test]
fn lit_value_in_scheme() {
    let _ = Scheme::Lit(Value::from(42));
}
