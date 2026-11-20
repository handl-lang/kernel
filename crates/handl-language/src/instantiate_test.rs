use super::*;
use crate::fragments::ast_shape::ChildRoleSpec;
use crate::fragments::{AstShapeDef, EvalSchemeDef};
use crate::term::ArrSource;
use serde_json::json;
use std::collections::HashMap;

fn role(role: &str) -> ChildRoleSpec {
    ChildRoleSpec {
        role: role.into(),
        variadic: false,
        optional: false,
    }
}

fn var_role(role: &str) -> ChildRoleSpec {
    ChildRoleSpec {
        role: role.into(),
        variadic: true,
        optional: false,
    }
}

fn opt_role(role: &str) -> ChildRoleSpec {
    ChildRoleSpec {
        role: role.into(),
        variadic: false,
        optional: true,
    }
}

fn shape(kind: &str, roles: Vec<ChildRoleSpec>) -> AstShapeDef {
    AstShapeDef::new(format!("ast.{kind}"), kind).with_children(roles)
}

fn op_scheme(kind: &str, op: &str) -> EvalSchemeDef {
    EvalSchemeDef {
        id: format!("eval.{kind}"),
        node_kind: kind.into(),
        scheme: Term::Op {
            dim: Box::new(Term::Const {
                value: Value::from(1),
            }),
            name: op.into(),
            args: vec![],
            source: ArrSource::Native,
            lit: None,
            attrs: None,
        },
        replaces: vec![],
        requires: vec![],
    }
}

/// A minimal language covering the binder forms under test.
fn test_lang() -> Language {
    let mut lang = Language::new();
    let shapes = [
        shape("var", vec![]).with_pattern_role("leaf"),
        shape("rest", vec![role("subject")]).with_pattern_role("rest"),
        shape(
            "array",
            vec![ChildRoleSpec {
                role: "elements".into(),
                variadic: true,
                optional: false,
            }],
        )
        .with_pattern_role("sequence"),
        shape("function", vec![role("params"), role("body")]),
        shape(
            "paren",
            vec![ChildRoleSpec {
                role: "body".into(),
                variadic: true,
                optional: false,
            }],
        ),
        shape("binary.add", vec![role("left"), role("right")]),
        shape("call", vec![role("callee"), var_role("args")]),
        shape(
            "assign",
            vec![role("target"), role("value"), opt_role("body")],
        ),
        shape("bind", vec![]),
        shape("block", vec![var_role("statements")]),
        shape("rec", vec![var_role("statements")]),
        shape(
            "for",
            vec![role("pattern"), role("collection"), role("body")],
        ),
        shape("arm", vec![role("pattern"), role("body")]),
        shape("type-annot", vec![role("subject"), role("annot")]),
        shape("pi", vec![role("param"), role("body")]),
        shape("field-access", vec![role("target"), role("field")]),
        shape("entry", vec![role("key"), role("value")])
            .with_literal_children([("key".into(), vec!["var".into()])]),
        shape("object", vec![var_role("entries")]),
    ];
    for s in shapes {
        lang.ast.merge(s).unwrap();
    }
    for (kind, op) in [
        ("assign", "assign"),
        ("bind", "bind"),
        ("block", "eval_block"),
        ("rec", "eval_rec"),
        ("for", "eval_block"),
        ("function", "closure"),
        ("var", "proj_env"),
    ] {
        lang.eval.merge(op_scheme(kind, op)).unwrap();
    }
    lang
}

fn node(kind: &str, children: &[usize], extra: Value) -> AstNode {
    let mut payload = json!({ "children": children });
    if let (Some(o), Some(e)) = (payload.as_object_mut(), extra.as_object()) {
        for (k, v) in e {
            o.insert(k.clone(), v.clone());
        }
    }
    AstNode::new(kind).with_payload(payload)
}

fn var(name: &str) -> AstNode {
    AstNode::new("var").with_payload(json!(name))
}

fn num(n: i64) -> AstNode {
    AstNode::new("value").with_payload(json!({ "value": n }))
}

fn env_of(pairs: &[(&str, Value)]) -> HashMap<Rc<str>, Value> {
    pairs
        .iter()
        .map(|(k, v)| (Rc::from(*k), v.clone()))
        .collect()
}

/// Collect every `lit` payload in the arena (substituted leaves).
fn lits(ast: &Ast) -> Vec<Value> {
    ast.iter()
        .filter(|n| n.kind == LIT_KIND)
        .map(|n| n.payload.clone())
        .collect()
}

/// Whether any `var` node in the arena still carries `name`.
fn has_var(ast: &Ast, name: &str) -> bool {
    ast.iter()
        .any(|n| n.kind == "var" && n.payload.as_str() == Some(name))
}

#[test]
fn free_var_substitutes() {
    let lang = test_lang();
    let mut ast = Ast::new();
    let x = ast.push(var("x")).index();
    let one = ast.push(num(1)).index();
    let add = ast.push(node("binary.add", &[x, one], Value::Null)).index();
    let out = ast
        .instantiate(AstRef::new(add), &lang, &env_of(&[("x", json!(5))]))
        .unwrap();
    assert!(lits(&out).contains(&json!(5)));
    assert!(!has_var(&out, "x"));
}

#[test]
fn unbound_var_stays() {
    let lang = test_lang();
    let mut ast = Ast::new();
    let x = ast.push(var("x")).index();
    let out = ast
        .instantiate(AstRef::new(x), &lang, &env_of(&[("y", json!(5))]))
        .unwrap();
    assert!(has_var(&out, "x"));
    assert!(lits(&out).is_empty());
}

#[test]
fn function_params_shadow_env() {
    let lang = test_lang();
    let mut ast = Ast::new();
    // (x) ~> x + y   with env {x: 9, y: 2} → body is x + lit(2)
    let px = ast.push(var("x")).index();
    let params = ast.push(node("paren", &[px], Value::Null)).index();
    let x = ast.push(var("x")).index();
    let y = ast.push(var("y")).index();
    let body = ast.push(node("binary.add", &[x, y], Value::Null)).index();
    let f = ast
        .push(node("function", &[params, body], Value::Null))
        .index();
    let out = ast
        .instantiate(
            AstRef::new(f),
            &lang,
            &env_of(&[("x", json!(9)), ("y", json!(2))]),
        )
        .unwrap();
    assert!(has_var(&out, "x"));
    assert!(!has_var(&out, "y"));
    assert!(lits(&out).contains(&json!(2)));
    assert!(!lits(&out).contains(&json!(9)));
}

#[test]
fn block_binders_scope_forward_only() {
    let lang = test_lang();
    let mut ast = Ast::new();
    // { x + 1; x := 0; x + y } with env {x: 9, y: 2}
    //   → first stmt substitutes x=9; third keeps bound x, y→lit(2)
    let x1 = ast.push(var("x")).index();
    let one = ast.push(num(1)).index();
    let s1 = ast
        .push(node("binary.add", &[x1, one], Value::Null))
        .index();
    let t = ast.push(var("x")).index();
    let z = ast.push(num(0)).index();
    let s2 = ast.push(node("assign", &[t, z], Value::Null)).index();
    let x2 = ast.push(var("x")).index();
    let y = ast.push(var("y")).index();
    let s3 = ast.push(node("binary.add", &[x2, y], Value::Null)).index();
    let blk = ast.push(node("block", &[s1, s2, s3], Value::Null)).index();
    let out = ast
        .instantiate(
            AstRef::new(blk),
            &lang,
            &env_of(&[("x", json!(9)), ("y", json!(2))]),
        )
        .unwrap();
    assert!(lits(&out).contains(&json!(9)));
    assert!(lits(&out).contains(&json!(2)));
    // The binder `x` (assign target + third-stmt reference) survives.
    assert!(has_var(&out, "x"));
}

#[test]
fn rec_region_prebinds_all_names() {
    let lang = test_lang();
    let mut ast = Ast::new();
    // rec { f := x; x := 1 } with env {x: 7} — `x` in f's value refers
    // to the later sibling binder, not env.
    let t = ast.push(var("f")).index();
    let x = ast.push(var("x")).index();
    let s1 = ast.push(node("assign", &[t, x], Value::Null)).index();
    let t2 = ast.push(var("x")).index();
    let one = ast.push(num(1)).index();
    let s2 = ast.push(node("assign", &[t2, one], Value::Null)).index();
    let r = ast.push(node("rec", &[s1, s2], Value::Null)).index();
    let out = ast
        .instantiate(AstRef::new(r), &lang, &env_of(&[("x", json!(7))]))
        .unwrap();
    assert!(!lits(&out).contains(&json!(7)));
    assert!(has_var(&out, "x"));
}

#[test]
fn bind_node_scopes_payload_name() {
    let lang = test_lang();
    let mut ast = Ast::new();
    // bind x = 0 in (x + y)  with env {x: 9, y: 3}
    let z = ast.push(num(0)).index();
    let x = ast.push(var("x")).index();
    let y = ast.push(var("y")).index();
    let add = ast.push(node("binary.add", &[x, y], Value::Null)).index();
    let b = ast
        .push(node("bind", &[z, add], json!({ "name": "x" })))
        .index();
    let out = ast
        .instantiate(
            AstRef::new(b),
            &lang,
            &env_of(&[("x", json!(9)), ("y", json!(3))]),
        )
        .unwrap();
    assert!(lits(&out).contains(&json!(3)));
    assert!(!lits(&out).contains(&json!(9)));
    assert!(has_var(&out, "x"));
}

#[test]
fn assign_let_form_scopes_over_body() {
    let lang = test_lang();
    let mut ast = Ast::new();
    // assign [x, 0, x + y]  with env {x: 9, y: 4}
    let t = ast.push(var("x")).index();
    let z = ast.push(num(0)).index();
    let x = ast.push(var("x")).index();
    let y = ast.push(var("y")).index();
    let add = ast.push(node("binary.add", &[x, y], Value::Null)).index();
    let a = ast.push(node("assign", &[t, z, add], Value::Null)).index();
    let out = ast
        .instantiate(
            AstRef::new(a),
            &lang,
            &env_of(&[("x", json!(9)), ("y", json!(4))]),
        )
        .unwrap();
    assert!(lits(&out).contains(&json!(4)));
    assert!(!lits(&out).contains(&json!(9)));
    assert!(has_var(&out, "x"));
}

#[test]
fn arm_pattern_binders_shadow() {
    let lang = test_lang();
    // arm [h, ...t] → h + y  with env {h: 1, t: 2, y: 5}
    let mut ast = Ast::new();
    let h = ast.push(var("h")).index();
    let tv = ast.push(var("t")).index();
    let rest = ast.push(node("rest", &[tv], Value::Null)).index();
    let pat = ast.push(node("array", &[h, rest], Value::Null)).index();
    let hv = ast.push(var("h")).index();
    let yv = ast.push(var("y")).index();
    let add = ast.push(node("binary.add", &[hv, yv], Value::Null)).index();
    let a = ast.push(node("arm", &[pat, add], Value::Null)).index();
    let out = ast
        .instantiate(
            AstRef::new(a),
            &lang,
            &env_of(&[("h", json!(1)), ("t", json!(2)), ("y", json!(5))]),
        )
        .unwrap();
    assert!(lits(&out).contains(&json!(5)));
    assert!(has_var(&out, "h"));
    assert!(has_var(&out, "t"));
}

#[test]
fn literal_entry_key_not_substituted() {
    let lang = test_lang();
    let mut ast = Ast::new();
    // { x: y } with env {x: 9, y: 2} → key `x` is literal data.
    let k = ast.push(var("x")).index();
    let v = ast.push(var("y")).index();
    let e = ast.push(node("entry", &[k, v], Value::Null)).index();
    let o = ast.push(node("object", &[e], Value::Null)).index();
    let out = ast
        .instantiate(
            AstRef::new(o),
            &lang,
            &env_of(&[("x", json!(9)), ("y", json!(2))]),
        )
        .unwrap();
    assert!(has_var(&out, "x"));
    assert!(!has_var(&out, "y"));
}

#[test]
fn param_annot_subject_substitutes() {
    let lang = test_lang();
    // pi (x: T) → x  with env {T: <type>, x: 9} — `x` binds, `T` substs.
    let mut ast = Ast::new();
    let x = ast.push(var("x")).index();
    let t = ast.push(var("T")).index();
    let ann = ast.push(node("type-annot", &[x, t], Value::Null)).index();
    let body = ast.push(var("x")).index();
    let pi = ast.push(node("pi", &[ann, body], Value::Null)).index();
    let out = ast
        .instantiate(
            AstRef::new(pi),
            &lang,
            &env_of(&[("T", json!("Num")), ("x", json!(9))]),
        )
        .unwrap();
    assert!(lits(&out).contains(&json!("Num")));
    assert!(!lits(&out).contains(&json!(9)));
    assert!(has_var(&out, "x"));
}

#[test]
fn payload_body_ref_substitutes_under_params() {
    let lang = test_lang();
    // Closure payload form: {"params": ["x"], "body": <idx>} — the
    // body index is an arena ref bound by the payload params.
    let mut ast = Ast::new();
    let x = ast.push(var("x")).index();
    let y = ast.push(var("y")).index();
    let add = ast.push(node("binary.add", &[x, y], Value::Null)).index();
    let f = ast
        .push(AstNode::new("arrow-lit").with_payload(json!({
            "params": ["x"],
            "body": add,
        })))
        .index();
    let out = ast
        .instantiate(
            AstRef::new(f),
            &lang,
            &env_of(&[("x", json!(9)), ("y", json!(2))]),
        )
        .unwrap();
    assert!(lits(&out).contains(&json!(2)));
    assert!(!lits(&out).contains(&json!(9)));
    // The body arena ref was remapped into the output arena.
    let body_idx = out.iter().last().unwrap().payload["body"].as_u64().unwrap() as usize;
    assert!(body_idx < out.len());
    assert_eq!(out.at(AstRef::new(body_idx)).unwrap().kind, "binary.add");
}
