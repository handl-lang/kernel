use super::*;
use handl_value::Sym;
use handl_value::nbe::{ArrowVal, Spine};

fn root_kind(ast: &Ast) -> &str {
    ast.nodes().last().map(|n| n.kind.as_str()).unwrap_or("")
}

#[test]
fn const_reifies_to_lit_payload() {
    let store = MetaStore::default();
    let ast = reify_ast(&store, 0, &Val::Const(TaggedValue::Int(42)), &[]);
    assert_eq!(ast.len(), 1);
    let n = &ast.nodes()[0];
    assert_eq!(n.kind, "lit");
    assert_eq!(n.payload, serde_json::json!(42));
}

#[test]
fn nominal_reifies_to_sym_literal() {
    let store = MetaStore::default();
    let ast = reify_ast(&store, 0, &Val::Nominal(Sym::seeded("type.Int")), &[]);
    let n = &ast.nodes()[0];
    assert_eq!(n.kind, "lit");
    assert_eq!(n.payload["__sym__"]["name"], "Int");
}

#[test]
fn universe_reifies_to_type_literal() {
    let store = MetaStore::default();
    let ast = reify_ast(&store, 0, &Val::Universe(2), &[]);
    assert_eq!(ast.nodes()[0].payload, serde_json::json!({"__type__": 2}));
}

#[test]
fn former_reifies_to_former_literal() {
    let store = MetaStore::default();
    let v = Val::Former {
        head: Sym::seeded("vec.Vec"),
        args: vec![
            Val::Const(TaggedValue::Int(2)),
            Val::Nominal(Sym::seeded("type.Int")),
        ],
    };
    let ast = reify_ast(&store, 0, &v, &[]);
    let n = &ast.nodes()[0];
    assert_eq!(n.kind, "lit");
    assert_eq!(n.payload["__former__"]["sym"]["__sym__"]["name"], "Vec");
    assert_eq!(n.payload["__former__"]["args"][0], serde_json::json!(2));
    assert_eq!(n.payload["__former__"]["args"][1]["__sym__"]["name"], "Int");
}

#[test]
fn arrow_reifies_to_runnable_arrow_literal() {
    let store = MetaStore::default();
    let a = ArrowVal {
        params: Rc::from(vec!["x".to_string()]),
        body_def: TaggedValue::from(serde_json::json!({"__ast__": {"nodes": []}})),
        binds: Rc::new(
            [(Rc::from("k"), Val::Const(TaggedValue::Int(7)))]
                .into_iter()
                .collect(),
        ),
    };
    let ast = reify_ast(&store, 0, &Val::Arrow(Rc::new(a)), &[]);
    let n = &ast.nodes()[0];
    assert_eq!(n.kind, "lit");
    // The payload decodes back to a `TaggedValue::Arrow` — the
    // self-contained shape (params + body_def + binds), not
    // `quote`'s display-only {params, binds} map.
    let back = TaggedValue::from(n.payload.clone());
    match back {
        TaggedValue::Arrow {
            params,
            body_def,
            binds,
            ..
        } => {
            assert_eq!(&*params, &["x".to_string()][..]);
            assert!(binds.contains_key("k"));
            let bd = tagged_to_value(&body_def);
            assert!(bd.get("__ast__").is_some());
        }
        other => panic!("expected arrow, got {other:?}"),
    }
}

#[test]
fn rigid_named_reifies_to_var() {
    let store = MetaStore::default();
    let names = vec![Rc::from("n")];
    let v = Val::Rigid {
        lvl: 0,
        spine: Spine::default(),
    };
    let ast = reify_ast(&store, 1, &v, &names);
    assert_eq!(root_kind(&ast), "var");
    assert_eq!(ast.nodes()[0].payload, serde_json::json!("n"));
}

#[test]
fn rigid_unnamed_reifies_to_neutral_literal() {
    let store = MetaStore::default();
    let v = Val::Rigid {
        lvl: 0,
        spine: Spine::default(),
    };
    let ast = reify_ast(&store, 1, &v, &[]);
    assert_eq!(root_kind(&ast), "lit");
    assert_eq!(ast.nodes()[0].payload["__neutral__"]["head"], "rigid");
    assert_eq!(ast.nodes()[0].payload["__neutral__"]["index"], 0);
}

#[test]
fn unfold_reifies_to_var_call() {
    let store = MetaStore::default();
    let v = Val::Unfold {
        name: Rc::from("vec_map"),
        spine: Spine(vec![Val::Const(TaggedValue::Int(3))]),
        value: Rc::new(std::cell::OnceCell::new()),
    };
    let ast = reify_ast(&store, 0, &v, &[]);
    // [var(vec_map), lit(3), call(0, 1)] — root is the call.
    assert_eq!(ast.len(), 3);
    assert_eq!(root_kind(&ast), "call");
    assert_eq!(
        ast.nodes()[2].payload["children"],
        serde_json::json!([0, 1])
    );
}

#[test]
fn flex_reifies_to_meta_neutral_literal() {
    let store = MetaStore::default();
    let v = Val::Flex {
        meta: 9,
        spine: Spine::default(),
    };
    let ast = reify_ast(&store, 0, &v, &[]);
    assert_eq!(root_kind(&ast), "lit");
    assert_eq!(ast.nodes()[0].payload["__neutral__"]["head"], "meta");
    assert_eq!(ast.nodes()[0].payload["__neutral__"]["id"], 9);
}

#[test]
fn spine_args_reify_as_call_children() {
    let store = MetaStore::default();
    let names = vec![Rc::from("f")];
    let v = Val::Rigid {
        lvl: 0,
        spine: Spine(vec![
            Val::Const(TaggedValue::Int(1)),
            Val::Nominal(Sym::seeded("type.Int")),
        ]),
    };
    let ast = reify_ast(&store, 1, &v, &names);
    assert_eq!(root_kind(&ast), "call");
    // callee + two reified args.
    assert_eq!(
        ast.nodes()[ast.len() - 1].payload["children"]
            .as_array()
            .unwrap()
            .len(),
        3
    );
}

#[test]
fn ast_value_form_is_ast_tagged() {
    let store = MetaStore::default();
    let v = reify_ast_value(&store, 0, &Val::Universe(0), &[]);
    assert!(crate::is_ast_value(&v));
    let back = crate::as_ast(&v).expect("decodes");
    assert_eq!(back.nodes()[0].payload, serde_json::json!({"__type__": 0}));
}
