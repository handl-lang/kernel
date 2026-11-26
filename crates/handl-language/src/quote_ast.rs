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
    ast.push(AstNode::new("call").with_payload(serde_json::json!({ "children": children })))
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
                param_defs: None,
                body_def: Rc::new(a.body_def.clone()),
                binds: Rc::new(binds),
                handlers: Rc::from(Vec::new()),
                sig: None,
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
#[path = "quote_ast_test.rs"]
mod quote_ast_test;
