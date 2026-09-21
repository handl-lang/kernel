//! Tests for the closure-env registry: arrows serialize `env` as
//! `{"__envref__": id}` against a thread-local registry instead of
//! inlining the map — shared env DAGs must not expand exponentially.

use handl_value::{
    env_from_json, env_ref_lookup, intern_env, stamp_env_home, tagged_to_value, TaggedValue,
};
use rustc_hash::FxHashMap;
use serde_json::{json, Value};
use std::rc::Rc;

fn env_of(pairs: Vec<(&str, TaggedValue)>) -> Rc<FxHashMap<Rc<str>, TaggedValue>> {
    let mut m = FxHashMap::default();
    for (k, v) in pairs {
        m.insert(Rc::from(k), v);
    }
    Rc::new(m)
}

fn arrow(body: usize, env: Rc<FxHashMap<Rc<str>, TaggedValue>>) -> TaggedValue {
    TaggedValue::Arrow {
        params: Rc::from(vec!["x".to_string()]),
        rest: None,
        body,
        env,
        home: None,
        array_pattern: false,
        body_def: None,
    }
}

fn envref_id(v: &Value) -> u64 {
    v.get("env")
        .and_then(|e| e.get("__envref__"))
        .and_then(|r| r.as_u64())
        .expect("arrow env should serialize as {\"__envref__\": id}")
}

#[test]
fn intern_same_rc_same_id() {
    let env = env_of(vec![("a", TaggedValue::Int(1))]);
    assert_eq!(intern_env(&env), intern_env(&env));
}

#[test]
fn intern_distinct_rcs_distinct_ids() {
    let a = env_of(vec![("a", TaggedValue::Int(1))]);
    let b = env_of(vec![("a", TaggedValue::Int(1))]);
    assert_ne!(intern_env(&a), intern_env(&b));
}

#[test]
fn lookup_resolves_interned_env() {
    let env = env_of(vec![("a", TaggedValue::Int(1))]);
    let id = intern_env(&env);
    let resolved = env_ref_lookup(id).expect("interned env resolves");
    assert!(Rc::ptr_eq(&env, &resolved));
}

#[test]
fn arrow_serializes_env_by_ref() {
    let env = env_of(vec![("z", TaggedValue::Int(3))]);
    let v = tagged_to_value(&arrow(5, Rc::clone(&env)));
    let id = envref_id(&v);
    let resolved = env_ref_lookup(id).expect("envref resolves");
    assert!(Rc::ptr_eq(&env, &resolved));
}

#[test]
fn envref_round_trips_to_same_rc() {
    let env = env_of(vec![("z", TaggedValue::Int(3))]);
    let v = tagged_to_value(&arrow(5, Rc::clone(&env)));
    let t: TaggedValue = v.into();
    match t {
        TaggedValue::Arrow { env: got, .. } => assert!(Rc::ptr_eq(&env, &got)),
        other => panic!("expected arrow, got {other:?}"),
    }
}

#[test]
fn legacy_inline_env_decodes() {
    let t: TaggedValue = json!({
        "__arrow__": true, "params": ["x"], "body": 1, "env": {"z": 3}
    })
    .into();
    match t {
        TaggedValue::Arrow { env, .. } => {
            assert_eq!(env.get("z").and_then(|v| v.as_i64()), Some(3));
        }
        other => panic!("expected arrow, got {other:?}"),
    }
}

#[test]
fn env_from_json_accepts_both_forms() {
    let env = env_of(vec![("k", TaggedValue::Int(9))]);
    let id = intern_env(&env);
    let by_ref = env_from_json(&json!({"__envref__": id})).unwrap();
    assert!(Rc::ptr_eq(&env, &by_ref));
    let inline = env_from_json(&json!({"k": 9})).unwrap();
    assert_eq!(inline.get("k").and_then(|v| v.as_i64()), Some(9));
}

#[test]
fn nested_arrows_serialize_by_ref() {
    let inner_env = env_of(vec![("deep", TaggedValue::Int(1))]);
    let inner = arrow(1, inner_env);
    let outer_env = env_of(vec![("inner", inner)]);
    let v = tagged_to_value(&arrow(2, outer_env));
    // Outer env is a ref; the arrow inside it serializes its own env as a
    // ref too — nothing is inlined.
    let id = envref_id(&v);
    let resolved = env_ref_lookup(id).unwrap();
    let inner_v = tagged_to_value(resolved.get("inner").unwrap());
    envref_id(&inner_v);
}

#[test]
fn stamp_env_home_stamps_nested_arrows() {
    // env_outer -> f (unhomed, env_mid) ; env_mid -> g (unhomed)
    let g = arrow(3, env_of(vec![]));
    let env_mid = env_of(vec![("g", g)]);
    let f = arrow(2, env_mid);
    let env_outer = env_of(vec![("f", f)]);
    let id = intern_env(&env_outer);

    stamp_env_home(id, 42);

    let stamped = env_ref_lookup(id).unwrap();
    let TaggedValue::Arrow {
        home: f_home,
        env: f_env,
        ..
    } = stamped.get("f").unwrap()
    else {
        panic!("f should be an arrow");
    };
    assert_eq!(*f_home, Some(42));
    // f's env was re-registered under its own id — resolve it to see g.
    let mid_id = intern_env(f_env);
    let stamped_mid = env_ref_lookup(mid_id).unwrap();
    let TaggedValue::Arrow { home: g_home, .. } = stamped_mid.get("g").unwrap() else {
        panic!("g should be an arrow");
    };
    assert_eq!(*g_home, Some(42));
}

#[test]
fn stamp_env_home_preserves_existing_home() {
    let mut homed = arrow(1, env_of(vec![]));
    if let TaggedValue::Arrow { home, .. } = &mut homed {
        *home = Some(7);
    }
    let env = env_of(vec![("h", homed)]);
    let id = intern_env(&env);
    stamp_env_home(id, 42);
    let stamped = env_ref_lookup(id).unwrap();
    let TaggedValue::Arrow { home, .. } = stamped.get("h").unwrap() else {
        panic!("h should be an arrow");
    };
    assert_eq!(*home, Some(7));
}

/// The regression: k arrows each capturing all previous ones is a shared
/// DAG of size O(k²) internally — serialization must stay linear-ish, not
/// expand to ~2^k nodes.
#[test]
fn serialization_is_bounded_for_shared_envs() {
    let mut prev: Vec<TaggedValue> = Vec::new();
    for i in 0..64usize {
        let mut m = FxHashMap::default();
        for (j, p) in prev.iter().enumerate() {
            let key: Rc<str> = Rc::from(format!("p{j}"));
            m.insert(key, p.clone());
        }
        prev.push(arrow(i, Rc::new(m)));
    }
    let env = env_of(
        prev.iter()
            .enumerate()
            .map(|(i, p)| {
                // Leak the key string — test-only convenience.
                let key: &'static str = Box::leak(format!("p{i}").into_boxed_str());
                (key, p.clone())
            })
            .collect(),
    );
    let v = tagged_to_value(&arrow(999, env));
    let s = serde_json::to_string(&v).unwrap();
    // 64 nested arrows inlined would be astronomically large; by-ref keeps
    // this to a few hundred bytes.
    assert!(s.len() < 4_096, "serialized arrow too large: {} bytes", s.len());
}
