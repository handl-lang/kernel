use super::*;

#[test]
fn node_builders() {
    let n = AstNode::new("lit")
        .with_span(Span { start: 0, end: 3 })
        .with_payload(Value::from(42));
    assert_eq!(n.kind, "lit");
    assert_eq!(n.span, Some(Span { start: 0, end: 3 }));
    assert_eq!(n.payload, Value::from(42));
}

#[test]
fn arena_insert_and_resolve() {
    let mut ast = Ast::new();
    assert!(ast.is_empty());
    let a = ast.push(AstNode::new("a"));
    let b = ast.push(AstNode::new("b"));
    assert_eq!(ast.len(), 2);
    assert_eq!(ast.get(a).unwrap().kind, "a");
    assert_eq!(ast.get(b).unwrap().kind, "b");
    assert_eq!(ast[a].kind, "a");
    assert_eq!(ast[b].kind, "b");
}

#[test]
fn arena_get_mut() {
    let mut ast = Ast::new();
    let r = ast.push(AstNode::new("a"));
    ast.get_mut(r).unwrap().kind = "c".into();
    assert_eq!(ast.get(r).unwrap().kind, "c");
}

#[test]
fn arena_out_of_bounds() {
    let ast = Ast::new();
    assert_eq!(ast.get(AstRef::new(0)), None);
    let err = ast.at(AstRef::new(99)).unwrap_err();
    assert_eq!(err, LangError::AstIndexOutOfBounds { index: 99 });
}

#[test]
fn arena_growth_and_iter() {
    let mut ast = Ast::new();
    for i in 0..50 {
        ast.push(AstNode::new(format!("n{i}")));
    }
    assert_eq!(ast.len(), 50);
    let kinds: Vec<_> = ast.iter().map(|n| n.kind.clone()).collect();
    assert_eq!(kinds[0], "n0");
    assert_eq!(kinds[49], "n49");
}

#[test]
fn astref_index_accessor() {
    let r = AstRef::new(12);
    assert_eq!(r.index(), 12);
}

#[test]
fn ast_nodes_slice() {
    let mut ast = Ast::new();
    ast.push(AstNode::new("a"));
    ast.push(AstNode::new("b"));
    let slice = ast.nodes();
    assert_eq!(slice.len(), 2);
    assert_eq!(slice[1].kind, "b");
}

#[test]
fn astref_serde_roundtrip() {
    let r = AstRef::new(7);
    let j = serde_json::to_string(&r).unwrap();
    assert_eq!(j, "7");
    let back: AstRef = serde_json::from_str(&j).unwrap();
    assert_eq!(back, r);
}

#[test]
fn ast_serde_roundtrip() {
    let mut ast = Ast::new();
    ast.push(AstNode::new("x").with_payload(Value::from(1)));
    ast.push(AstNode::new("y"));
    let j = serde_json::to_string(&ast).unwrap();
    let back: Ast = serde_json::from_str(&j).unwrap();
    assert_eq!(ast, back);
}

#[test]
fn subtree_extracts_rooted_subtree() {
    // 0: lit(2), 1: lit(3), 2: binary.add {children:[0,1]}
    let mut ast = Ast::new();
    ast.push(AstNode::new("lit").with_payload(Value::from(2)));
    ast.push(AstNode::new("lit").with_payload(Value::from(3)));
    ast.push(AstNode::new("binary.add").with_payload(serde_json::json!({"children": [0, 1]})));
    let sub = ast.subtree(AstRef::new(2)).unwrap();
    // Root is the last node.
    assert_eq!(sub.len(), 3);
    assert_eq!(sub.nodes()[2].kind, "binary.add");
    // Children indices remapped to the new arena.
    let children = sub.nodes()[2]
        .payload
        .get("children")
        .unwrap()
        .as_array()
        .unwrap();
    assert_eq!(children[0], Value::from(0));
    assert_eq!(children[1], Value::from(1));
    assert_eq!(sub.nodes()[0].payload, Value::from(2));
    assert_eq!(sub.nodes()[1].payload, Value::from(3));
}

#[test]
fn subtree_single_node() {
    let mut ast = Ast::new();
    ast.push(AstNode::new("lit").with_payload(Value::from(42)));
    let sub = ast.subtree(AstRef::new(0)).unwrap();
    assert_eq!(sub.len(), 1);
    assert_eq!(sub.nodes()[0].payload, Value::from(42));
}

/// ADR-0106 item 2 step 2a: a named arena reference in the payload
/// (`body`, the closure form) is remapped too — the extracted arena is
/// genuinely standalone, not just `children`-complete.
#[test]
fn subtree_remaps_named_body_reference() {
    // Arena: 0: lit(1), 1: var(x), 2: binary.add[0,1],
    //        3: closure {params:["x"], body: 2}
    let mut ast = Ast::new();
    ast.push(AstNode::new("lit").with_payload(Value::from(1)));
    ast.push(AstNode::new("var").with_payload(Value::from("x")));
    ast.push(AstNode::new("binary.add").with_payload(serde_json::json!({ "children": [0, 1] })));
    ast.push(
        AstNode::new("closure").with_payload(serde_json::json!({ "params": ["x"], "body": 2 })),
    );

    let sub = ast.subtree(AstRef::new(3)).unwrap();
    // Post-order: children of the body first, then the body, then the
    // closure root last.
    assert_eq!(sub.len(), 4);
    assert_eq!(sub.nodes()[3].kind, "closure");

    // The closure's `body` now points at the *extracted* body node, and
    // that node's own `children` point at the extracted operands: every
    // reference resolves inside the new arena.
    let body_new = sub.nodes()[3].payload["body"].as_u64().unwrap() as usize;
    assert!(
        body_new < sub.len(),
        "remapped body index must be in range of the extracted arena",
    );
    assert_eq!(sub.nodes()[body_new].kind, "binary.add");
    let kids = sub.nodes()[body_new].payload["children"]
        .as_array()
        .unwrap();
    for k in kids {
        assert!((k.as_u64().unwrap() as usize) < sub.len());
    }
    assert_eq!(
        sub.nodes()[kids[0].as_u64().unwrap() as usize].payload,
        Value::from(1)
    );
    assert_eq!(
        sub.nodes()[kids[1].as_u64().unwrap() as usize].payload,
        Value::from("x"),
    );
}

/// Non-reference payload numbers, and out-of-range `body` values, are
/// left untouched — the remap must not rewrite unrelated payload data or
/// fail on malformed ancestors.
#[test]
fn subtree_leaves_non_reference_payload_numbers_alone() {
    let mut ast = Ast::new();
    ast.push(AstNode::new("lit").with_payload(Value::from(7)));
    ast.push(AstNode::new("func").with_payload(serde_json::json!({
        "arity": 99,
        "index": 12345,
        "body": 99, // out of range: not a reference in this arena
        "name": "f"
    })));
    let sub = ast.subtree(AstRef::new(1)).unwrap();
    assert_eq!(sub.len(), 1, "only the root is extracted (no children)");
    // Unmatched numeric payload keys survive verbatim.
    assert_eq!(sub.nodes()[0].payload["arity"], Value::from(99));
    assert_eq!(sub.nodes()[0].payload["index"], Value::from(12345));
    assert_eq!(sub.nodes()[0].payload["body"], Value::from(99));
    assert_eq!(sub.nodes()[0].payload["name"], Value::from("f"));
}

/// A `body` that is not an integer (some nodes carry structured payload
/// under that key) is not treated as a reference.
#[test]
fn subtree_ignores_non_integer_body_payload() {
    let mut ast = Ast::new();
    ast.push(AstNode::new("func").with_payload(serde_json::json!({
        "params": [],
        "body": { "kind": "lit", "value": 1 }
    })));
    let sub = ast.subtree(AstRef::new(0)).unwrap();
    assert_eq!(sub.len(), 1);
    assert_eq!(sub.nodes()[0].payload["body"]["kind"], Value::from("lit"));
}
