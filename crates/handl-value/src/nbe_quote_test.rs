use super::*;

#[test]
fn quote_former_and_neutral() {
    let store = MetaStore::default();
    let v = Val::Former {
        head: Sym::seeded("vec.Vec"),
        args: vec![
            Val::Rigid {
                lvl: 0,
                spine: Spine::default(),
            },
            Val::Nominal(Sym::seeded("type.Int")),
        ],
    };
    let q = quote(&store, 1, &v);
    let j = Value::from(q);
    assert_eq!(j["__former__"]["sym"]["__sym__"]["name"], "Vec");
    assert_eq!(j["__former__"]["args"][0]["__neutral__"]["index"], 0);
}

#[test]
fn quote_solved_meta_shows_solution() {
    let mut store = MetaStore::default();
    let m = store.fresh();
    store.solve(m, Val::Universe(0));
    let v = Val::Flex {
        meta: m,
        spine: Spine::default(),
    };
    let j = Value::from(quote(&store, 0, &v));
    assert_eq!(j["__type__"], 0);
}
