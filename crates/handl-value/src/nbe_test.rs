use super::*;

#[test]
fn seeded_sym_is_stable_and_idempotent() {
    let a = Sym::seeded("vec.Vec");
    let b = Sym::seeded("vec.Vec");
    let c = Sym::seeded("list.List");
    assert!(Rc::ptr_eq(&a, &b));
    assert_eq!(a, b);
    assert_ne!(a, c);
    assert!(a.is_seeded());
    assert_eq!(a.name(), "Vec");
    // Fresh syms never collide with seeded handles.
    let f = Sym::fresh("Vec");
    assert_ne!(*a, f);
    assert!(!f.is_seeded());
}

#[test]
fn seeded_parent_chain() {
    let number = Sym::seeded("type.Number");
    let int = Sym::seeded_with_parent("type.Int", &number);
    assert!(int.is_descendant_of(&number));
    assert!(int.has_ancestor(&number));
    assert!(!number.is_descendant_of(&int));
}

#[test]
fn seeded_parent_upgrades_parentless_mint() {
    // A bare `seeded` mint before the declaration is known does not
    // lock the nominal into parentlessness: `seeded_with_parent`
    // upgrades the memo entry (same handle — `==` still holds).
    let bare = Sym::seeded("type.decimal");
    let dec = Sym::seeded_with_parent("type.decimal", &Sym::seeded("type.number"));
    assert!(dec.is_descendant_of(&Sym::seeded("type.number")));
    assert_eq!(*bare, *dec);
    assert!(!Rc::ptr_eq(&bare, &dec));
    // A second parent declaration does not re-parent.
    let other = Sym::seeded_with_parent("type.decimal", &Sym::seeded("type.other"));
    assert!(Rc::ptr_eq(&dec, &other));
    assert!(!dec.is_descendant_of(&Sym::seeded("type.other")));
}

#[test]
fn env_shares_tails() {
    let e = Env::new().extend(Some("a".into()), Val::Universe(0));
    let e2 = e.extend(
        Some("b".into()),
        Val::Rigid {
            lvl: 0,
            spine: Spine::default(),
        },
    );
    assert_eq!(e2.len(), 2);
    assert!(matches!(e2.lookup(0), Some(Val::Rigid { .. })));
    assert!(matches!(e2.lookup(1), Some(Val::Universe(0))));
    // The outer env is unaffected (persistent).
    assert_eq!(e.len(), 1);
}

#[test]
fn meta_constraint_descendant() {
    let mut store = MetaStore::default();
    let num = Sym::seeded("type.Number");
    let int = Sym::seeded_with_parent("type.Int", &num);
    let m = store.fresh_constrained(MetaConstraint::DescendantOf(num.clone()));
    // Solving to Int (a Number descendant) succeeds.
    assert!(store.solve(m, Val::Nominal(int.clone())));
    // A second solve is refused.
    assert!(!store.solve(m, Val::Nominal(num)));
}

#[test]
fn meta_constraint_rejects_non_descendant() {
    let mut store = MetaStore::default();
    let num = Sym::seeded("type.Number");
    let s = Sym::seeded("type.Str");
    let m = store.fresh_constrained(MetaConstraint::DescendantOf(num));
    assert!(!store.solve(m, Val::Nominal(s)));
    assert!(store.solution(m).is_none());
}

#[test]
fn occurs_finds_flex_meta() {
    let store = MetaStore::default();
    let nested = Val::Flex {
        meta: 7,
        spine: Spine(vec![Val::Universe(0)]),
    };
    let outer = Val::Former {
        head: Sym::seeded("type.Vec"),
        args: vec![nested],
    };
    assert!(store.occurs(7, &outer));
    assert!(!store.occurs(9, &outer));
}
