//! Free-variable substitution for arrow bodies (ADR-0106 closure
//! elimination).
//!
//! [`Ast::instantiate`] extracts the subtree rooted at a closure body into a
//! fresh standalone arena — like [`Ast::subtree`] — while replacing every
//! **free** variable with a `lit` node carrying the definition-site value
//! (already serialized to [`Value`]). The result is a closed term: an arrow
//! minted over it needs no captured environment.
//!
//! Binder tracking is data-driven over `AstShapeDef` metadata and the eval
//! schemes, never `kind ==` checks:
//!
//! - `params`/`param`/`pattern` child roles introduce binders scoped over
//!   the sibling `body` role (`function`, `arm`, `for`, `pi`/`sigma`).
//! - A node declaring `target` + `value` roles is a binding (`assign`-like):
//!   its `target` names a binder scoped over the `body` role child when one
//!   is occupied (`x = v in body`), or over *subsequent siblings* when the
//!   node sits in a statement sequence (`x := v` in a `block`/`rec`/`for`).
//! - A `bind`-shaped node (payload `name` + `[value, body]`, no declared
//!   roles) scopes `name` over its second child.
//! - A node with a `subject` role and a string `name` payload
//!   (`type-annot`-like) scopes `name` over the `subject` child.
//! - Nodes whose eval scheme is the `eval_rec` op pre-bind every statement's
//!   names over the whole region (mutual recursion); `eval_block` sequences
//!   accumulate statement binders left-to-right.
//! - `stmt.import`-style statements contribute their `names`/`alias`
//!   payload entries as sibling binders; `stmt.export` and other
//!   declaration statements contribute `name`.
//! - Children in `literal_children`-declared roles (e.g. `entry.key`) copy
//!   raw — a `var` there is data, not a reference.
//! - Named arena references (`payload["body"]`, the closure payload form
//!   `{params: [...], body: <idx>}`) substitute under the payload's own
//!   `params`/`rest` names.
//!
//! Substituted literals use the `lit` node kind: it declares no eval
//! scheme, so every engine's scheme-less fallback evaluates it as
//! `TaggedValue::from(payload)` — exactly the inverse of the caller's
//! `tagged_to_value` serialization.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use serde_json::Value;

use crate::ast::{ARENA_REF_PAYLOAD_KEYS, Ast, AstNode, AstRef};
use crate::error::LangError;
use crate::language::Language;
use crate::term::Term;

/// The node kind emitted for substituted values: no eval scheme, so it
/// evaluates as `TaggedValue::from(payload)` on every engine.
pub const LIT_KIND: &str = "lit";

/// Statement-level ops whose node binds names for following siblings in a
/// statement sequence. `assign`-like nodes (target + value roles, arity 2)
/// are detected by shape, not name; this set covers the payload-driven
/// declaration forms.
const SEQ_DECL_OPS: &[&str] = &[
    "export", "import", "law", "rewrite", "op", "sort", "grade", "type", "trait", "impl", "data",
    "forall", "infer", "module",
];

/// A bound-name set passed down the instantiation walk.
type Bound = HashSet<Rc<str>>;

impl Ast {
    /// Extract the subtree rooted at `root` into a standalone arena with
    /// free variables substituted by their definition-site values.
    ///
    /// `env` maps a free variable's name to its serialized value
    /// (`tagged_to_value`). A `var` leaf whose name is in `env` and not
    /// shadowed by an enclosing binder becomes a `lit` node carrying the
    /// value; every other node copies through with its children remapped.
    ///
    /// # Errors
    ///
    /// Returns [`LangError::AstIndexOutOfBounds`] if a referenced child
    /// index is out of bounds.
    pub fn instantiate(
        &self,
        root: AstRef,
        lang: &Language,
        env: &HashMap<Rc<str>, Value>,
    ) -> Result<Ast, LangError> {
        let mut st = Instantiate {
            src: self,
            lang,
            env,
            out: Ast::new(),
        };
        st.copy(root, &Bound::new())?;
        Ok(st.out)
    }
}

struct Instantiate<'a> {
    src: &'a Ast,
    lang: &'a Language,
    env: &'a HashMap<Rc<str>, Value>,
    out: Ast,
}

impl Instantiate<'_> {
    /// Copy `r` into the output arena, substituting free vars. `bound` is
    /// the set of names bound by enclosing binders (not substituted).
    fn copy(&mut self, r: AstRef, bound: &Bound) -> Result<usize, LangError> {
        let node = self.src.at(r)?.clone();

        // Substitutable variable: a leaf-pattern kind with a string payload
        // (`var`; `arr` is also `leaf` but carries an object payload).
        if self.is_var(&node) {
            let name = node.payload.as_str().unwrap_or_default();
            if !bound.contains(name) {
                if let Some(v) = self.env.get(name) {
                    let lit = AstNode {
                        kind: LIT_KIND.to_string(),
                        span: node.span,
                        payload: v.clone(),
                    };
                    return Ok(self.out.push(lit).index());
                }
            }
        }

        let children: Vec<usize> = node
            .payload
            .get("children")
            .and_then(|c| c.as_array())
            .map(|a| {
                a.iter()
                    .filter_map(|v| v.as_u64().map(|i| i as usize))
                    .collect()
            })
            .unwrap_or_default();
        let arity = children.len();
        // `op` borrows `self.lang` — resolve the flags now so the borrow
        // ends before the `&mut self` child copies below.
        let (is_bind, sequential, is_rec) = {
            let op = self.head_op(&node);
            (
                op == Some("bind"),
                op == Some("eval_block") || op == Some("eval_rec"),
                op == Some("eval_rec"),
            )
        };

        // Per-child extra bound names and copy modes.
        let mut extra: Vec<Bound> = (0..arity).map(|_| Bound::new()).collect();
        let mut raw: Vec<bool> = vec![false; arity];
        let mut pattern_pos: Vec<bool> = vec![false; arity];
        let mut params_pos: Vec<bool> = vec![false; arity];
        let mut literal: Vec<bool> = vec![false; arity];

        for (i, &cidx) in children.iter().enumerate() {
            let Some(role) = self.lang.role_name_at(&node, i) else {
                continue;
            };
            let child_node = self.src.at(AstRef::new(cidx))?;
            // Literal positions copy raw — a `var` key is data, not a ref.
            match self.lang.literal_child(&node.kind, role, &child_node.kind) {
                Some(true) => {
                    literal[i] = true;
                    continue;
                }
                Some(false) => {}
                // Legacy fallback heuristic (role-less shapes): a `key`
                // role holding a string-payload child is literal.
                None => {
                    if role == "key" && child_node.payload.is_string() {
                        literal[i] = true;
                        continue;
                    }
                }
            }
            match role {
                "params" => {
                    // Copy the params node pattern-wise: binder leaves raw,
                    // `x: T` annot subjects substituted. `param_bound_names`
                    // flattens destructuring patterns (`([x, y]) ~>`,
                    // `({a, b}) ~>`) so every apply-time binder stays bound
                    // over the body — `param_names` would `Err` and fall
                    // back to over-binding every captured name.
                    params_pos[i] = true;
                    match self.lang.param_bound_names(self.src, child_node) {
                        Ok(names) => {
                            self.bind_over_body(&node, arity, &mut extra, names, None);
                        }
                        // Unresolvable params: substitute nothing under the
                        // body — over-binding is the safe direction.
                        Err(_) => {
                            self.bind_over_body_all(&node, arity, &mut extra);
                        }
                    }
                }
                "param" => {
                    // Single binder (`pi`/`sigma`/`for`-style): the child is
                    // a `var` or `x: T` annot — pattern-copy so `T`
                    // substitutes while `x` binds.
                    pattern_pos[i] = true;
                    let mut binders = Vec::new();
                    self.pattern_binders(AstRef::new(cidx), &mut binders)?;
                    if binders.is_empty() {
                        self.bind_over_body_all(&node, arity, &mut extra);
                    } else {
                        self.bind_over_body(&node, arity, &mut extra, binders, None);
                    }
                }
                "pattern" => {
                    pattern_pos[i] = true;
                    let mut binders = Vec::new();
                    self.pattern_binders(AstRef::new(cidx), &mut binders)?;
                    self.bind_over_body(&node, arity, &mut extra, binders, None);
                }
                // `target` is a binder only on binding shapes (target+value
                // roles, e.g. `assign`); on `field-access`/`dimension` it is
                // an evaluated expression.
                "target" if self.is_binding_node(&node) => {
                    raw[i] = true;
                    if let Ok(Some(body_pos)) = self.lang.child_role_index_for(&node, "body") {
                        if body_pos < arity {
                            if let Some(name) = self.lang.binding_target(self.src, &node) {
                                extra[body_pos].insert(Rc::from(name.as_str()));
                            }
                        }
                    }
                }
                // `name`-roled children are identifier data, not exprs.
                "name" => {
                    raw[i] = true;
                }
                _ => {}
            }
        }

        // `bind`-shaped node: payload `name`, children [value, body], no
        // declared roles — `name` is scoped over the body child.
        if is_bind && arity == 2 {
            if let Some(name) = node.payload.get("name").and_then(|v| v.as_str()) {
                extra[1].insert(Rc::from(name));
            }
        }
        // `type-annot`-shaped node: payload `name` + `subject` role — the
        // annot value binds `name` while the subject evaluates.
        if let Some(name) = node.payload.get("name").and_then(|v| v.as_str()) {
            if let Ok(Some(subject_pos)) = self.lang.child_role_index_for(&node, "subject") {
                if subject_pos < arity {
                    extra[subject_pos].insert(Rc::from(name));
                }
            }
        }

        // Statement sequences (`eval_block`-schemed nodes — `block`, `for`)
        // accumulate binders left-to-right; `eval_rec` pre-binds every
        // statement name over the whole region (mutual recursion).
        let mut seq_bound: Bound = Bound::new();
        if is_rec {
            for &cidx in &children {
                for n in self.seq_binders(self.src.at(AstRef::new(cidx))?) {
                    seq_bound.insert(n);
                }
            }
        }

        // Copy children in order.
        let mut new_children: Vec<u64> = Vec::with_capacity(arity);
        for (i, &cidx) in children.iter().enumerate() {
            let child_node = self.src.at(AstRef::new(cidx))?;
            let new_idx = if literal[i] || raw[i] {
                self.copy_raw(AstRef::new(cidx))?
            } else if pattern_pos[i] {
                self.copy_pattern(AstRef::new(cidx), bound)?
            } else if params_pos[i] {
                self.copy_params(AstRef::new(cidx), bound)?
            } else {
                let mut b = bound.clone();
                b.extend(extra[i].iter().cloned());
                b.extend(seq_bound.iter().cloned());
                self.copy(AstRef::new(cidx), &b)?
            };
            new_children.push(new_idx as u64);
            if sequential {
                for n in self.seq_binders(child_node) {
                    seq_bound.insert(n);
                }
            }
        }

        // Named arena references in the payload (e.g. the closure payload
        // form `{"params": [...], "body": <idx>}`): substitute under the
        // payload's own param names.
        let mut new_payload = node.payload.clone();
        for key in ARENA_REF_PAYLOAD_KEYS {
            if let Some(v) = node.payload.get(*key).and_then(|v| v.as_u64()) {
                let vidx = v as usize;
                if vidx < self.src.len() {
                    let mut b = bound.clone();
                    if *key == "body" {
                        if let Some(params) = node.payload.get("params").and_then(|p| p.as_array())
                        {
                            for p in params {
                                if let Some(s) = p.as_str() {
                                    b.insert(Rc::from(s));
                                }
                            }
                        }
                        if let Some(rest) = node.payload.get("rest").and_then(|p| p.as_str()) {
                            b.insert(Rc::from(rest));
                        }
                    }
                    let new_idx = self.copy(AstRef::new(vidx), &b)?;
                    if let Some(obj) = new_payload.as_object_mut() {
                        obj.insert((*key).to_string(), Value::from(new_idx as u64));
                    }
                }
            }
        }
        if let Some(cs) = new_payload
            .get_mut("children")
            .and_then(|c| c.as_array_mut())
        {
            for (i, &nidx) in new_children.iter().enumerate() {
                if let Some(slot) = cs.get_mut(i) {
                    *slot = Value::from(nidx);
                }
            }
        }
        let new_idx = self.out.push(AstNode {
            kind: node.kind.clone(),
            span: node.span,
            payload: new_payload,
        });
        Ok(new_idx.index())
    }

    /// Deep-copy a subtree without substitution (binder/literal positions).
    fn copy_raw(&mut self, r: AstRef) -> Result<usize, LangError> {
        let node = self.src.at(r)?.clone();
        let mut new_payload = node.payload.clone();
        if let Some(children) = node.payload.get("children").and_then(|c| c.as_array()) {
            let mut new_children = Vec::with_capacity(children.len());
            for c in children {
                if let Some(i) = c.as_u64() {
                    new_children.push(self.copy_raw(AstRef::new(i as usize))? as u64);
                }
            }
            if let Some(cs) = new_payload
                .get_mut("children")
                .and_then(|c| c.as_array_mut())
            {
                for (i, nidx) in new_children.iter().enumerate() {
                    if let Some(slot) = cs.get_mut(i) {
                        *slot = Value::from(*nidx);
                    }
                }
            }
        }
        for key in ARENA_REF_PAYLOAD_KEYS {
            if let Some(v) = node.payload.get(*key).and_then(|v| v.as_u64()) {
                if (v as usize) < self.src.len() {
                    let nidx = self.copy_raw(AstRef::new(v as usize))?;
                    if let Some(obj) = new_payload.as_object_mut() {
                        obj.insert((*key).to_string(), Value::from(nidx as u64));
                    }
                }
            }
        }
        Ok(self
            .out
            .push(AstNode {
                kind: node.kind,
                span: node.span,
                payload: new_payload,
            })
            .index())
    }

    /// Copy a pattern-position child: pattern nodes copy raw and
    /// contribute binders; unrecognized shapes are evaluated expressions
    /// and copy with substitution. Returns the new index.
    fn copy_pattern(&mut self, r: AstRef, bound: &Bound) -> Result<usize, LangError> {
        let node = self.src.at(r)?.clone();
        match self.lang.pattern_role(&node.kind) {
            Some("leaf") | Some("rest") | Some("sequence") | Some("entries") | Some("entry") => {
                // Pure binder structure — copy raw.
                self.copy_raw(r)
            }
            Some(_) => self.copy_raw(r),
            None => {
                // Tag patterns (`ok(x)`) are `call`-shaped: `callee` is the
                // tag name (literal), `args` are sub-patterns.
                if self.role_pos(&node, "callee").is_some() {
                    return self.copy_call_pattern(r, bound);
                }
                // Wrapper shapes (`type-annot` subject, `paren` body): the
                // binder side recurses as a pattern, the annot side is an
                // evaluated type expression.
                if let Some(subject) = self.role_pos(&node, "subject") {
                    return self.copy_wrapper_pattern(r, bound, subject);
                }
                if let Some(body) = self.role_pos(&node, "body") {
                    return self.copy_wrapper_pattern(r, bound, body);
                }
                // An evaluated literal/expression pattern — substitute.
                self.copy(r, bound)
            }
        }
    }

    /// `call`-shaped tag pattern: `callee` copies raw (tag name), `args`
    /// children copy as patterns.
    fn copy_call_pattern(&mut self, r: AstRef, bound: &Bound) -> Result<usize, LangError> {
        let node = self.src.at(r)?.clone();
        let children: Vec<usize> = node
            .payload
            .get("children")
            .and_then(|c| c.as_array())
            .map(|a| {
                a.iter()
                    .filter_map(|v| v.as_u64().map(|i| i as usize))
                    .collect()
            })
            .unwrap_or_default();
        let callee_pos = self.role_pos(&node, "callee").unwrap_or(0);
        let mut new_children = Vec::with_capacity(children.len());
        for (i, &cidx) in children.iter().enumerate() {
            let nidx = if i == callee_pos {
                self.copy_raw(AstRef::new(cidx))?
            } else {
                self.copy_pattern(AstRef::new(cidx), bound)?
            };
            new_children.push(nidx as u64);
        }
        let mut new_payload = node.payload.clone();
        if let Some(cs) = new_payload
            .get_mut("children")
            .and_then(|c| c.as_array_mut())
        {
            for (i, nidx) in new_children.iter().enumerate() {
                if let Some(slot) = cs.get_mut(i) {
                    *slot = Value::from(*nidx);
                }
            }
        }
        Ok(self
            .out
            .push(AstNode {
                kind: node.kind,
                span: node.span,
                payload: new_payload,
            })
            .index())
    }

    /// `params`-roled node (an arrow parameter list): every child is a
    /// param — `var`/`rest` leaves copy raw, `x: T` annots substitute `T`.
    fn copy_params(&mut self, r: AstRef, bound: &Bound) -> Result<usize, LangError> {
        let node = self.src.at(r)?.clone();
        let children: Vec<usize> = node
            .payload
            .get("children")
            .and_then(|c| c.as_array())
            .map(|a| {
                a.iter()
                    .filter_map(|v| v.as_u64().map(|i| i as usize))
                    .collect()
            })
            .unwrap_or_default();
        let mut new_children = Vec::with_capacity(children.len());
        for &cidx in &children {
            new_children.push(self.copy_pattern(AstRef::new(cidx), bound)? as u64);
        }
        let mut new_payload = node.payload.clone();
        if let Some(cs) = new_payload
            .get_mut("children")
            .and_then(|c| c.as_array_mut())
        {
            for (i, nidx) in new_children.iter().enumerate() {
                if let Some(slot) = cs.get_mut(i) {
                    *slot = Value::from(*nidx);
                }
            }
        }
        Ok(self
            .out
            .push(AstNode {
                kind: node.kind,
                span: node.span,
                payload: new_payload,
            })
            .index())
    }

    /// Wrapper pattern (`type-annot`/`paren`-like): the binder-side child
    /// recurses as a pattern; every other child is evaluated and copies
    /// with substitution.
    fn copy_wrapper_pattern(
        &mut self,
        r: AstRef,
        bound: &Bound,
        binder_pos: usize,
    ) -> Result<usize, LangError> {
        let node = self.src.at(r)?.clone();
        let children: Vec<usize> = node
            .payload
            .get("children")
            .and_then(|c| c.as_array())
            .map(|a| {
                a.iter()
                    .filter_map(|v| v.as_u64().map(|i| i as usize))
                    .collect()
            })
            .unwrap_or_default();
        let mut new_children = Vec::with_capacity(children.len());
        for (i, &cidx) in children.iter().enumerate() {
            let nidx = if i == binder_pos {
                self.copy_pattern(AstRef::new(cidx), bound)?
            } else {
                self.copy(AstRef::new(cidx), bound)?
            };
            new_children.push(nidx as u64);
        }
        let mut new_payload = node.payload.clone();
        if let Some(cs) = new_payload
            .get_mut("children")
            .and_then(|c| c.as_array_mut())
        {
            for (i, nidx) in new_children.iter().enumerate() {
                if let Some(slot) = cs.get_mut(i) {
                    *slot = Value::from(*nidx);
                }
            }
        }
        Ok(self
            .out
            .push(AstNode {
                kind: node.kind,
                span: node.span,
                payload: new_payload,
            })
            .index())
    }

    /// Collect the names a pattern-position child binds (leaf binders,
    /// `rest` subjects, sequence/entry element patterns, tag-pattern args).
    fn pattern_binders(&self, r: AstRef, out: &mut Vec<String>) -> Result<(), LangError> {
        let node = self.src.at(r)?;
        match self.lang.pattern_role(&node.kind) {
            Some("leaf") => {
                if let Some(name) = node.payload.as_str() {
                    out.push(name.to_string());
                }
            }
            Some("rest") | None => {
                // `rest`: its `subject` child names the binding. `None`
                // covers tag patterns (`callee`+`args`: binders are the
                // args) and wrappers (`subject`/`body` child).
                if let Some(subject) = self.role_pos(node, "subject") {
                    if let Some(c) = self.child_at(node, subject) {
                        return self.pattern_binders(c, out);
                    }
                }
                if let Some(body) = self.role_pos(node, "body") {
                    if let Some(c) = self.child_at(node, body) {
                        return self.pattern_binders(c, out);
                    }
                }
                let callee_pos = self.role_pos(node, "callee");
                if callee_pos.is_some() {
                    if let Some(children) = node.payload.get("children").and_then(|c| c.as_array())
                    {
                        for (i, c) in children.iter().enumerate() {
                            if Some(i) == callee_pos {
                                continue;
                            }
                            if let Some(idx) = c.as_u64() {
                                self.pattern_binders(AstRef::new(idx as usize), out)?;
                            }
                        }
                    }
                }
            }
            Some("sequence") | Some("entries") | Some("entry") => {
                if let Some(children) = node.payload.get("children").and_then(|c| c.as_array()) {
                    for (i, c) in children.iter().enumerate() {
                        // `entry`: the `key` child is literal — only the
                        // `value` child can hold binders.
                        if self.lang.pattern_role_is(&node.kind, "entry") == Some(true) {
                            if let Some(key_pos) = self.role_pos(node, "key") {
                                if i == key_pos {
                                    continue;
                                }
                            }
                        }
                        if let Some(idx) = c.as_u64() {
                            self.pattern_binders(AstRef::new(idx as usize), out)?;
                        }
                    }
                }
            }
            Some(_) => {}
        }
        Ok(())
    }

    /// Names a statement binds for subsequent siblings in a statement
    /// sequence. `assign`-like nodes declare `target` + `value` roles and
    /// bind only in the 2-child form (`x := v`); declaration statements
    /// carry the name in `payload.name` or a `name`-roled child.
    fn seq_binders(&self, node: &AstNode) -> Vec<Rc<str>> {
        let mut names = Vec::new();
        let arity = node
            .payload
            .get("children")
            .and_then(|c| c.as_array())
            .map(|a| a.len())
            .unwrap_or(0);
        if self.is_binding_node(node) && arity == 2 {
            if let Some(name) = self.lang.binding_target(self.src, node) {
                names.push(Rc::from(name.as_str()));
            }
            return names;
        }
        match self.head_op(node) {
            Some("import") => {
                if let Some(arr) = node.payload.get("names").and_then(|v| v.as_array()) {
                    for n in arr {
                        if let Some(s) = n.as_str() {
                            names.push(Rc::from(s));
                        } else if let Some(s) = n.get("name").and_then(|v| v.as_str()) {
                            names.push(Rc::from(s));
                        }
                        if let Some(s) = n.get("alias").and_then(|v| v.as_str()) {
                            names.push(Rc::from(s));
                        }
                    }
                }
                if let Some(a) = node.payload.get("alias").and_then(|v| v.as_str()) {
                    names.push(Rc::from(a));
                }
            }
            Some(op) if SEQ_DECL_OPS.contains(&op) => {
                if let Some(s) = node.payload.get("name").and_then(|v| v.as_str()) {
                    names.push(Rc::from(s));
                } else if let Some(pos) = self.role_pos(node, "name") {
                    if let Some(crefr) = self.child_at(node, pos) {
                        if let Ok(child) = self.src.at(crefr) {
                            if let Some(s) = child.payload.as_str() {
                                names.push(Rc::from(s));
                            }
                        }
                    }
                }
            }
            _ => {}
        }
        names
    }

    /// Whether `node` is a binding shape: declares `target` + `value`
    /// roles (`assign`-like; `field-access`/`dimension` lack `value`).
    fn is_binding_node(&self, node: &AstNode) -> bool {
        let target = self.lang.child_role_index(&node.kind, "target");
        let value = self.lang.child_role_index(&node.kind, "value");
        matches!(target, Ok(Some(_))) && matches!(value, Ok(Some(_)))
    }

    /// Whether `node` is a substitutable variable leaf (`var`).
    fn is_var(&self, node: &AstNode) -> bool {
        node.payload.is_string()
            && self
                .lang
                .pattern_role_is(&node.kind, "leaf")
                .unwrap_or(node.kind == "var")
    }

    /// The head op name of the node's eval scheme, when the scheme is a
    /// bare `Op` term (e.g. `assign`, `bind`, `eval_block`, `eval_rec`,
    /// `import`, `export`).
    fn head_op(&self, node: &AstNode) -> Option<&str> {
        self.lang
            .eval
            .get_by_identity(&node.kind)
            .and_then(|def| match &def.scheme {
                Term::Op { name, .. } => Some(name.as_str()),
                _ => None,
            })
    }

    /// The positional index of `role` on `node`, if occupied.
    fn role_pos(&self, node: &AstNode, role: &str) -> Option<usize> {
        self.lang.child_role_index_for(node, role).ok().flatten()
    }

    /// The child `AstRef` at position `pos` on `node`.
    fn child_at(&self, node: &AstNode, pos: usize) -> Option<AstRef> {
        node.payload
            .get("children")
            .and_then(|c| c.as_array())
            .and_then(|a| a.get(pos))
            .and_then(|v| v.as_u64())
            .map(|i| AstRef::new(i as usize))
    }

    /// Add `names` (+ optional `rest`) to the bound set of every `body`-roled
    /// child of `node`; when no `body` role exists, bind over every
    /// non-binder child position.
    fn bind_over_body(
        &self,
        node: &AstNode,
        arity: usize,
        extra: &mut [Bound],
        names: Vec<String>,
        rest: Option<&str>,
    ) {
        let mut set: Bound = Bound::new();
        for n in names {
            set.insert(Rc::from(n.as_str()));
        }
        if let Some(r) = rest {
            set.insert(Rc::from(r));
        }
        self.bind_over_body_set(node, arity, extra, set);
    }

    /// Bind every env name over the `body` role (unresolvable binders —
    /// substitute nothing beneath them).
    fn bind_over_body_all(&self, node: &AstNode, arity: usize, extra: &mut [Bound]) {
        let set: Bound = self.env.keys().cloned().collect();
        self.bind_over_body_set(node, arity, extra, set);
    }

    fn bind_over_body_set(&self, node: &AstNode, arity: usize, extra: &mut [Bound], set: Bound) {
        if set.is_empty() {
            return;
        }
        if let Ok(Some(body_pos)) = self.lang.child_role_index_for(node, "body") {
            if body_pos < arity {
                extra[body_pos].extend(set);
                return;
            }
        }
        // No occupied `body` role: bind over all other positions.
        for slot in extra.iter_mut() {
            slot.extend(set.iter().cloned());
        }
    }
}

#[cfg(test)]
#[path = "instantiate_test.rs"]
mod instantiate_test;
