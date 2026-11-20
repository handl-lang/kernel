use super::*;

#[test]
fn former_conv_nominal_head_structural_args() {
    let mut store = MetaStore::default();
    let vec = Sym::seeded("vec.Vec");
    let int = Sym::seeded("type.Int");
    let two_a = Val::Former {
        head: vec.clone(),
        args: vec![Val::Const(TaggedValue::Int(2)), Val::Nominal(int.clone())],
    };
    let two_b = Val::Former {
        head: vec.clone(),
        args: vec![Val::Const(TaggedValue::Int(2)), Val::Nominal(int)],
    };
    assert!(conv(&mut store, 0, &two_a, &two_b));
    let three = Val::Former {
        head: vec,
        args: vec![
            Val::Const(TaggedValue::Int(3)),
            Val::Nominal(Sym::seeded("type.Int")),
        ],
    };
    assert!(!conv(&mut store, 0, &two_a, &three));
}

#[test]
fn flex_solves_to_rigid() {
    let mut store = MetaStore::default();
    let m = store.fresh();
    let r = Val::Rigid {
        lvl: 0,
        spine: Spine::default(),
    };
    assert!(conv(
        &mut store,
        1,
        &Val::Flex {
            meta: m,
            spine: Spine::default()
        },
        &r
    ));
    assert!(store.solution(m).is_some());
}

#[test]
fn flex_occurs_rejects_cycle() {
    let mut store = MetaStore::default();
    let m = store.fresh();
    let cyclic = Val::Former {
        head: Sym::seeded("type.Int"),
        args: vec![Val::Flex {
            meta: m,
            spine: Spine::default(),
        }],
    };
    assert!(!conv(
        &mut store,
        0,
        &Val::Flex {
            meta: m,
            spine: Spine::default()
        },
        &cyclic
    ));
    assert!(store.solution(m).is_none());
}

#[test]
fn literal_meta_solves_numeric() {
    let mut store = MetaStore::default();
    let num = Sym::seeded("type.Number");
    let int = Sym::seeded_with_parent("type.Int", &num);
    let m = store.fresh_constrained(MetaConstraint::DescendantOf(num));
    assert!(conv(
        &mut store,
        0,
        &Val::Flex {
            meta: m,
            spine: Spine::default()
        },
        &Val::Nominal(int)
    ));
    // A non-numeric type cannot solve the literal meta.
    let m2 = store.fresh_constrained(MetaConstraint::DescendantOf(Sym::seeded("type.Number")));
    assert!(!conv(
        &mut store,
        0,
        &Val::Flex {
            meta: m2,
            spine: Spine::default()
        },
        &Val::Nominal(Sym::seeded("type.Str"))
    ));
}

// --- comp-tree normal forms (phase-3 WS-B) -------------------------

fn cell_comp(k: i64, a: Val, b: Val) -> Val {
    Val::Former {
        head: Sym::seeded("cell.comp"),
        args: vec![Val::Const(TaggedValue::Int(k)), a, b],
    }
}

fn cell_id(k: i64, x: Val) -> Val {
    Val::Former {
        head: Sym::seeded("cell.id"),
        args: vec![Val::Const(TaggedValue::Int(k)), x],
    }
}

fn rigid(l: u32) -> Val {
    Val::Rigid {
        lvl: l,
        spine: Spine::default(),
    }
}

#[test]
fn comp_nf_associativity() {
    let mut store = MetaStore::default();
    let (a, b, c) = (rigid(0), rigid(1), rigid(2));
    let lhs = cell_comp(2, cell_comp(2, a.clone(), b.clone()), c.clone());
    let rhs = cell_comp(2, a.clone(), cell_comp(2, b.clone(), c.clone()));
    assert!(conv(&mut store, 3, &lhs, &rhs));
    // Order still matters — different order does not convert.
    let rhs2 = cell_comp(2, a, cell_comp(2, c, b));
    assert!(!conv(&mut store, 3, &lhs, &rhs2));
}

#[test]
fn comp_nf_unit_absorbs() {
    let mut store = MetaStore::default();
    let (e, f) = (rigid(0), rigid(1));
    // `id₂(f) ∘₂ e ≡ e` and `e ∘₂ id₂(g) ≡ e`.
    let lhs = cell_comp(2, cell_id(2, f.clone()), e.clone());
    assert!(conv(&mut store, 2, &lhs, &e));
    let rhs = cell_comp(2, e.clone(), cell_id(2, rigid(2)));
    assert!(conv(&mut store, 3, &rhs, &e));
    // Units drop mid-chain too: `a ∘ id ∘ b ≡ a ∘ b`.
    let a = rigid(3);
    let chain = cell_comp(2, a.clone(), cell_comp(2, cell_id(2, f.clone()), e.clone()));
    let flat = cell_comp(2, a, e.clone());
    assert!(conv(&mut store, 4, &chain, &flat));
    // `id` towers absorb at deep axes: `id₃(id₂(y))` is a `∘₁` unit.
    let y = rigid(1);
    let tower = cell_id(3, cell_id(2, y));
    let lhs = cell_comp(1, tower, e.clone());
    assert!(conv(&mut store, 2, &lhs, &e));
    // But `id₂` is NOT a `∘₀` unit on a non-id payload —
    // `id₂(f) ∘₀ e` is whiskering, not the identity.
    let whisker = cell_comp(0, cell_id(2, f), e.clone());
    assert!(!conv(&mut store, 2, &whisker, &e));
    // `id₁(A)` on an object IS a `∘₀` unit.
    let obj_id = cell_id(1, Val::Nominal(Sym::seeded("type.Int")));
    let lhs = cell_comp(0, obj_id, e.clone());
    assert!(conv(&mut store, 2, &lhs, &e));
    // And object leaves themselves promote to degenerate cells —
    // `A ∘ₖ e ≡ e` for a type value at any axis.
    let obj = Val::Nominal(Sym::seeded("type.Int"));
    for k in [0, 1, 4] {
        let lhs = cell_comp(k, obj.clone(), e.clone());
        assert!(conv(&mut store, 2, &lhs, &e), "axis {k}");
    }
}

#[test]
fn comp_nf_interchange_grid() {
    let mut store = MetaStore::default();
    // `(a ∘₀ c) ∘₂ (b ∘₀ d) ≡ (a ∘₂ b) ∘₀ (c ∘₂ d)` — the exchange
    // law; the canonical form sorts the smaller axis outward.
    let (a, b, c, d) = (rigid(0), rigid(1), rigid(2), rigid(3));
    let lhs = cell_comp(
        2,
        cell_comp(0, a.clone(), c.clone()),
        cell_comp(0, b.clone(), d.clone()),
    );
    let rhs = cell_comp(
        0,
        cell_comp(2, a.clone(), b.clone()),
        cell_comp(2, c.clone(), d.clone()),
    );
    assert!(conv(&mut store, 4, &lhs, &rhs));
    // The user's verify shape: `(f ∘₁ g) ∘₂ (f' ∘₁ g') ≡
    // (f ∘₂ f') ∘₁ (g ∘₂ g')` — axes 1 < 2 transpose the same way.
    let (f, g, f2, g2) = (rigid(0), rigid(1), rigid(2), rigid(3));
    let lhs = cell_comp(
        2,
        cell_comp(1, f.clone(), g.clone()),
        cell_comp(1, f2.clone(), g2.clone()),
    );
    let rhs = cell_comp(
        1,
        cell_comp(2, f.clone(), f2.clone()),
        cell_comp(2, g.clone(), g2.clone()),
    );
    assert!(conv(&mut store, 4, &lhs, &rhs));
    // n-ary grids transpose as blocks:
    // `(a∘₀c∘₀e) ∘₂ (b∘₀d∘₀h) ≡ (a∘₂b) ∘₀ (c∘₂d) ∘₀ (e∘₂h)`.
    let (a, b, c, d, e2, h) = (rigid(0), rigid(1), rigid(2), rigid(3), rigid(4), rigid(5));
    let lhs = cell_comp(
        2,
        cell_comp(0, cell_comp(0, a.clone(), c.clone()), e2.clone()),
        cell_comp(0, cell_comp(0, b.clone(), d.clone()), h.clone()),
    );
    let rhs = cell_comp(
        0,
        cell_comp(0, cell_comp(2, a, b), cell_comp(2, c, d)),
        cell_comp(2, e2, h),
    );
    assert!(conv(&mut store, 6, &lhs, &rhs));
    // A non-uniform grid stays stuck: `(a ∘₀ b) ∘₂ (c ∘₁ d)` —
    // mixed inner axes don't exchange (structural only).
    let lhs = cell_comp(
        2,
        cell_comp(0, rigid(0), rigid(1)),
        cell_comp(1, rigid(2), rigid(3)),
    );
    let rhs = cell_comp(
        0,
        cell_comp(2, rigid(0), rigid(2)),
        cell_comp(1, rigid(1), rigid(3)),
    );
    assert!(!conv(&mut store, 4, &lhs, &rhs));
}

#[test]
fn comp_nf_nested_under_hom() {
    let mut store = MetaStore::default();
    let hom = |n: i64, s: Val, t: Val| Val::Former {
        head: Sym::seeded("type.hom"),
        args: vec![Val::Const(TaggedValue::Int(n)), s, t],
    };
    let (a, b, c) = (rigid(0), rigid(1), rigid(2));
    // Comp trees nested inside `Hom` args normalize too —
    // `Hom(4, (a∘b)∘c, a∘(b∘c))` arg-wise converts.
    let lhs = hom(
        4,
        cell_comp(2, cell_comp(2, a.clone(), b.clone()), c.clone()),
        rigid(9),
    );
    let rhs = hom(4, cell_comp(2, a, cell_comp(2, b, c)), rigid(9));
    assert!(conv(&mut store, 10, &lhs, &rhs));
    // An `id`-absorbing tree nested under `Hom`:
    let lhs = hom(4, cell_comp(2, cell_id(2, rigid(5)), rigid(6)), rigid(9));
    let rhs = hom(4, rigid(6), rigid(9));
    assert!(conv(&mut store, 10, &lhs, &rhs));
}

/// WS-H microbench: `conv` over a deep `Former` nest. The zero-copy
/// `force_head_rc` change makes each level O(1) view + O(width)
/// structural work; previously every level deep-cloned the whole
/// remaining nest (O(depth²) clones per `conv`). Run with
/// `--nocapture` for the timing line.
#[test]
fn conv_bench_deep_former() {
    let mut store = MetaStore::default();
    let nest = |inner: &Val| Val::Former {
        head: Sym::seeded("type.Vec"),
        args: vec![inner.clone()],
    };
    let mut a = Val::Nominal(Sym::seeded("type.Int"));
    for _ in 0..64 {
        a = nest(&a);
    }
    let b = a.clone(); // structurally equal, independently allocated
    let t0 = std::time::Instant::now();
    let iters = 200;
    for _ in 0..iters {
        assert!(conv(&mut store, 0, &a, &b));
    }
    eprintln!(
        "conv_bench_deep_former: {iters} conv() over 64-deep Former nest: {:?}",
        t0.elapsed()
    );
}

/// WS-H microbench: flex solving — each `conv(?m, v)` hands `v` to
/// the store as an `Rc` (solutions no longer deep-clone per call).
#[test]
fn conv_bench_flex_solve() {
    let mut store = MetaStore::default();
    let v = Val::Former {
        head: Sym::seeded("type.Vec"),
        args: vec![Val::Nominal(Sym::seeded("type.Int"))],
    };
    let metas: Vec<MetaId> = (0..1000).map(|_| store.fresh()).collect();
    let t0 = std::time::Instant::now();
    for m in metas {
        assert!(conv(
            &mut store,
            0,
            &Val::Flex {
                meta: m,
                spine: Spine::default(),
            },
            &v
        ));
    }
    eprintln!(
        "conv_bench_flex_solve: 1000 flex solves: {:?}",
        t0.elapsed()
    );
}

/// WS-H microbench: repeat-pair conversions — the same `(a, b)`
/// Former pair re-derived `iters` times, the workload a conv memo
/// would collapse to one structural walk + `iters-1` lookups.
/// Measured to bound the upside of memoizing `conv` (the
/// `HNL_CONV_STATS` dup-pair counter says how often real checks
/// repeat a pair).
#[test]
fn conv_bench_repeat_pairs() {
    let mut store = MetaStore::default();
    let mut a = Val::Nominal(Sym::seeded("type.Int"));
    for _ in 0..64 {
        a = Val::Former {
            head: Sym::seeded("type.Hom"),
            args: vec![Val::Universe(2), a],
        };
    }
    let b = a.clone();
    assert!(conv(&mut store, 0, &a, &b));
    let t0 = std::time::Instant::now();
    let iters = 500;
    for _ in 0..iters {
        assert!(conv(&mut store, 0, &a, &b));
    }
    eprintln!(
        "conv_bench_repeat_pairs: {iters} conv() of the same 16-deep Former pair: {:?}",
        t0.elapsed()
    );
}

/// WS-H microbench: ptr-identical pairs — the `std::ptr::eq` fast
/// path's cost floor; the delta against `repeat_pairs` is what a
/// structural-fingerprint memo could recover at best.
#[test]
fn conv_bench_ptr_shared() {
    let mut store = MetaStore::default();
    let mut a = Val::Nominal(Sym::seeded("type.Int"));
    for _ in 0..64 {
        a = Val::Former {
            head: Sym::seeded("type.Hom"),
            args: vec![Val::Universe(2), a],
        };
    }
    let t0 = std::time::Instant::now();
    let iters = 500;
    for _ in 0..iters {
        assert!(conv(&mut store, 0, &a, &a));
    }
    eprintln!(
        "conv_bench_ptr_shared: {iters} conv() of the ptr-identical 64-deep pair: {:?}",
        t0.elapsed()
    );
}
