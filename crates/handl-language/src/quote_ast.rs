//! `Val → Ast` reification — the AST-surface half of `quote` (phase-2
//! spec WS-G; ADR-0154 §6 runtime-minted cells are legal values).
//!
//! [`handl_value::nbe::quote`] reifies the semantic domain to *boundary
//! data* (`__former__`/`__neutral__`/`__arrow__`/`__type__` tagged
//! values). [`reify_ast`] goes one step further: it materializes a `Val`
//! into an [`Ast`] arena whose nodes are the same surface shapes the
//! engines consume — `lit`/`var`/`call` — so a metaprogram's product can
//! re-enter the pipeline (inspect the arena, hand it to `eval`/
//! `typecheck`, embed it as an arrow `body_def` `{"__ast__": <arena>}`).
//!
//! ## The boundary — what reifies to what
//!
//! A `lit` node's payload *is* a boundary value: every exec engine
//! evaluates it as `TaggedValue::from(payload)` (the [`crate::instantiate`]
//! convention — `lit` declares no eval scheme). Reification therefore
//! targets boundary-faithful payloads, not new node kinds:
//!
//! - `Val::Const(tv)` → `lit` carrying `tagged_to_value(tv)` verbatim.
//!   Evaluates back to the identical `TaggedValue` on every engine.
//! - `Val::Nominal(sym)` → `lit` carrying the `{"__sym__": …}` encoding.
//!   Decodes to `TaggedValue::Sym`; `lift` recovers `Val::Nominal`.
//! - `Val::Universe(i)` → `lit` carrying `{"__type__": i}`.
//! - `Val::Former{head, args}` → `lit` carrying `{"__former__":
//!   {"sym": …, "args": […]}}` — `quote`'s own spelling, which `lift`
//!   reads back as `Val::Former` and `nominal_head`/`instance_of` accept
//!   directly. A `call`-shaped reification is deliberately **not**
//!   emitted: a former head is a nominal value, and applying a
//!   `Const(Sym)` callee is `NotAnArrow` in the domain — the literal
//!   is the faithful form.
//! - `Val::Arrow(a)` → `lit` carrying the [`TaggedValue::Arrow`] wire
//!   encoding (`{"__arrow__": true, "params": …, "body_def": …,
//!   "binds": …}`). Unlike `quote`'s display-only `{"__arrow__":
//!   {"params", "binds"}}` — which drops `body_def` — this reifies the
//!   *whole* self-contained arrow (params + body + residual binds,
//!   binds quoted recursively), so the literal decodes back to a
//!   runnable `TaggedValue::Arrow`.
//! - `Val::Unfold{name, spine}` → `var`/`call` over `name`: an unfold is
//!   a *named* top-level definition, so re-resolution by name is
//!   faithful.
//! - `Val::Rigid{lvl, spine}` → `var`/`call` when `names[lvl]` supplies
//!   the binder's declared name; otherwise the honest
//!   `{"__neutral__": …}` literal. A `var` re-entered under a binder of
//!   that name resolves again — how a metaprogram *closes* an open
//!   term.
//! - `Val::Flex{meta, spine}` → `lit` `{"__neutral__": {"head": "meta",
//!   "id": …}}`. Unsolved metas never re-enter as `var`s — a meta is a
//!   hole; its reification is honest stuck data, not a guessable name.
//!
//! ## What stays engine-internal
//!
//! `Flex`/`Unfold` *never serialize* (ADR-0106 domain doc): a meta is a
//! `MetaStore` index, an `Unfold`'s lazy `OnceCell` is a process-local
//! thunk — neither has meaning outside the checking context that
//! allocated it. Reification emits their stable *encodings* (`__meta__`
//! ids, the unfold head's name + spine) as data, but a metaprogram that
//! feeds a `__neutral__`/`__meta__` literal back into checking gets a
//! *fresh* stuck neutral — store identity does not round-trip. That is
//! the documented bound: **closed values round-trip; open terms reify
//! honestly but re-enter fresh.**

use std::rc::Rc;

use handl_value::nbe::{Lvl, MetaStore, Val, quote};
use handl_value::{TaggedValue, tagged_to_value};
use rustc_hash::FxHashMap;
use serde_json::Value;

use crate::ast::{Ast, AstNode, AstRef};
use crate::ast_value;

/// The node kind emitted for reified boundary values: `lit` declares no
/// eval scheme, so every engine evaluates it as
/// `TaggedValue::from(payload)` — exactly the convention
/// [`crate::instantiate::LIT_KIND`] documents for substituted values.
pub const REIFY_LIT_KIND: &str = "lit";

/// Reify `val` (at ambient level `lvl`) into an [`Ast`] arena.
///
/// `names`, in outermost-first order, supplies the declared binder names
/// for [`Val::Rigid`] heads (the same convention `quote` uses for
/// display): a rigid at level `l` becomes a `var` named `names[l]` when
/// present, or a `__neutral__` literal when absent. Pass an empty slice
/// to reify closed values (every `Rigid`/`Unfold` without a name
/// degrades to its literal encoding).
///
/// The returned arena follows the Pratt convention: the root node is the
/// last node in the arena. Wrap it with [`reify_ast_value`] for the
/// `{"__ast__": <arena>}` tagged form `body_def`/the meta `eval` host
/// function consume.
pub fn reify_ast(store: &MetaStore, lvl: Lvl, val: &Val, names: &[Rc<str>]) -> Ast {
    let mut ast = Ast::new();
    reify_into(store, lvl, val, names, &mut ast);
    ast
}

/// Reify `val` into the `{"__ast__": <arena>}` tagged boundary value —
/// the form an arrow `body_def` and the meta `eval`/`typecheck` host
/// functions consume directly.
pub fn reify_ast_value(store: &MetaStore, lvl: Lvl, val: &Val, names: &[Rc<str>]) -> Value {
    ast_value(&reify_ast(store, lvl, val, names))
}

/// The boundary-value shortcut: `lit` carrying `v`'s quote encoding.
fn push_lit(ast: &mut Ast, payload: Value) -> AstRef {
    ast.push(AstNode::new(REIFY_LIT_KIND).with_payload(payload))
}

/// `lit` carrying `val`'s `quote` boundary encoding (`__former__`/
/// `__neutral__`/`__type__`/`__sym__`/`__meta__` data).
fn push_quoted_lit(store: &MetaStore, lvl: Lvl, val: &Val, ast: &mut Ast) -> AstRef {
    push_lit(ast, tagged_to_value(&quote(store, lvl, val)))
}

/// `call` node: children `[callee, arg…]` (roles `callee` + `args`,
/// ADR-0081 — the surface application shape `eval.call` consumes).
fn push_call(ast: &mut Ast, callee: AstRef, args: Vec<AstRef>) -> AstRef {
    let mut children = vec![callee.index() as u64];
    children.extend(args.iter().map(|r| r.index() as u64));
    ast.push(
        AstNode::new("call").with_payload(serde_json::json!({ "children": children })),
    )
}

/// `var` node: the name rides the payload directly (the `eval.var`
/// scheme reads `$payload` as the resolved name).
fn push_var(ast: &mut Ast, name: &str) -> AstRef {
    ast.push(AstNode::new("var").with_payload(Value::from(name)))
}

/// Apply `head` to `spine` arguments, reifying each argument — the
/// `call`-chain half of a neutral/unfold reification.
fn reify_spine_call(
    store: &MetaStore,
    lvl: Lvl,
    head: AstRef,
    spine: &handl_value::nbe::Spine,
    names: &[Rc<str>],
    ast: &mut Ast,
) -> AstRef {
    if spine.is_empty() {
        return head;
    }
    let args: Vec<AstRef> = spine
        .0
        .iter()
        .map(|a| reify_into(store, lvl, a, names, ast))
        .collect();
    push_call(ast, head, args)
}

fn reify_into(store: &MetaStore, lvl: Lvl, val: &Val, names: &[Rc<str>], ast: &mut Ast) -> AstRef {
    match store.force_head(val) {
        // Closed data: the boundary encoding is the value — a `lit`
        // payload evaluates to the identical `TaggedValue` on every
        // engine.
        Val::Const(tv) => push_lit(ast, tagged_to_value(tv)),
        Val::Nominal(sym) => push_lit(ast, tagged_to_value(&TaggedValue::Sym(sym.clone()))),
        Val::Universe(i) => push_lit(ast, serde_json::json!({"__type__": i})),
        // A former application is a type-level *value*, not a call —
        // the `__former__` object literal is the 0152 surface spelling
        // (`IO(sig)` mints exactly this at runtime).
        v @ Val::Former { .. } => push_quoted_lit(store, lvl, v, ast),
        // The self-contained arrow: `body_def` + quoted `binds` reify
        // into the `TaggedValue::Arrow` wire form, which decodes back
        // to a runnable arrow value (unlike `quote`'s display-only
        // `{"__arrow__": {params, binds}}`, which drops the body).
        Val::Arrow(a) => {
            let binds: FxHashMap<Rc<str>, TaggedValue> = a
                .binds
                .iter()
                .map(|(k, v)| (k.clone(), quote(store, lvl, v)))
                .collect();
            let tv = TaggedValue::Arrow {
                params: a.params.clone(),
                rest: None,
                array_pattern: false,
                body_def: Rc::new(a.body_def.clone()),
                binds: Rc::new(binds),
                handlers: Rc::from(Vec::new()),
            };
            push_lit(ast, tagged_to_value(&tv))
        }
        // A named unfold head re-resolves by name — `var f(args…)` is
        // the surface spelling of the same term.
        Val::Unfold { name, spine, .. } => {
            let head = push_var(ast, name.as_ref());
            reify_spine_call(store, lvl, head, spine, names, ast)
        }
        // A rigid head is a bound variable: named binders re-enter as
        // `var`s (closing the open term); unnamed ones reify honestly
        // as `__neutral__` literals.
        v @ Val::Rigid { lvl: l, spine } => match names.get(*l as usize) {
            Some(name) => {
                let head = push_var(ast, name.as_ref());
                reify_spine_call(store, lvl, head, spine, names, ast)
            }
            None => push_quoted_lit(store, lvl, v, ast),
        },
        // An unsolved meta is a hole — honest stuck data, never a
        // guessable `var` (metas never serialize; the `__meta__`/`id`
        // encoding is a store-local index).
        v @ Val::Flex { .. } => push_quoted_lit(store, lvl, v, ast),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use handl_value::nbe::{ArrowVal, Spine};
    use handl_value::Sym;

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
        assert_eq!(
            n.payload["__former__"]["args"][1]["__sym__"]["name"],
            "Int"
        );
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
}
