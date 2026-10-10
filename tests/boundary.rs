//! Process-boundary check (`check_portable`): serialized documents that
//! carry process-local or dangling references must be rejected before they
//! leave the process; ordinary and self-contained documents pass.

use std::rc::Rc;

use handl_value::{check_portable, tagged_to_value, TaggedValue};
use rustc_hash::FxHashMap;
use serde_json::json;

fn arrow(binds: Rc<FxHashMap<Rc<str>, TaggedValue>>) -> TaggedValue {
    TaggedValue::Arrow {
        params: Rc::from(vec!["x".to_string()]),
        rest: None,
        array_pattern: false,
        body_def: Rc::new(TaggedValue::Null),
        binds,
        handlers: Rc::from(Vec::<TaggedValue>::new()),
    }
}

#[test]
fn plain_values_are_portable() {
    for v in [
        json!(null),
        json!(42),
        json!({"a": [1, {"b": "c"}]}),
        json!({"__sym__": {"handle": 1, "name": "s", "parent": null}}),
    ] {
        check_portable(&v).unwrap_or_else(|e| panic!("{v} rejected: {e}"));
    }
}

#[test]
fn self_contained_binds_refs_are_portable() {
    // Two sibling arrows sharing one binds map serialize as one
    // `__binds_id__` definition plus a `__bindsref__` repeat — the
    // document carries its own definition, so it is portable.
    let mut binds = FxHashMap::default();
    binds.insert(Rc::from("k"), TaggedValue::Int(1));
    let shared = Rc::new(binds);
    let doc = tagged_to_value(&TaggedValue::Arr(Rc::from(vec![
        arrow(Rc::clone(&shared)),
        arrow(Rc::clone(&shared)),
    ])));
    let text = doc.to_string();
    assert!(text.contains("__binds_id__") && text.contains("__bindsref__"));
    check_portable(&doc).unwrap();
}

#[test]
fn legacy_envref_is_rejected() {
    let v = json!({"__arrow__": true, "params": [], "env": {"__envref__": 7}});
    let err = check_portable(&v).unwrap_err();
    assert!(err.contains("__envref__"), "unexpected error: {err}");
}

#[test]
fn dangling_bindsref_is_rejected() {
    // A subtree lifted out of a larger document keeps the ref marker but
    // loses its `__binds_id__` definition.
    let v = json!({"outer": [{"binds": {"__bindsref__": 3}}]});
    let err = check_portable(&v).unwrap_err();
    assert!(err.contains("__bindsref__"), "unexpected error: {err}");
}

#[test]
fn bindsref_with_definition_in_document_passes() {
    let v = json!({
        "a": {"binds": {"__binds_id__": 0, "k": 1}},
        "b": {"binds": {"__bindsref__": 0}},
    });
    check_portable(&v).unwrap();
}

#[test]
fn resource_pointer_is_rejected() {
    let v = json!({"r": {"__resource__": {"ptr": 4096}}});
    let err = check_portable(&v).unwrap_err();
    assert!(err.contains("__resource__"), "unexpected error: {err}");
}

#[test]
fn compiled_handle_is_rejected() {
    // `{"__compiled__": id, "target": ...}` indexes the emitting process's
    // COMPILED_REGISTRY — meaningless to any other consumer.
    let v = json!({"program": {"__compiled__": 3, "target": "cranelift"}});
    let err = check_portable(&v).unwrap_err();
    assert!(err.contains("__compiled__"), "unexpected error: {err}");
}

#[test]
fn non_marker_lookalikes_pass() {
    // Reserved keys that do not match the shapes decode interprets are
    // foreign data, not references.
    check_portable(&json!({"__resource__": "label"})).unwrap();
    check_portable(&json!({"__bindsref__": "0"})).unwrap();
}
