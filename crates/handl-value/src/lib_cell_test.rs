use super::*;

/// `Cell` record `{__tag__: "Cell", __dim__: 3, __src__, __tgt__, value}`.
fn cell3(src: TaggedValue, tgt: TaggedValue, witness: TaggedValue) -> TaggedValue {
    mk_cell(3, src, tgt, witness)
}

fn int(n: i64) -> TaggedValue {
    TaggedValue::Int(n)
}

#[test]
fn cell_dim_recognizes_cell_shapes() {
    assert_eq!(cell_dim(&int(7)), 1);
    assert_eq!(cell_dim(&cell2(int(1), int(2), int(9))), 2);
    assert_eq!(cell_dim(&cell3(int(1), int(2), int(9))), 3);
    // `dim_arrow` records (`f ~[n]~> g`) carry their dimension in `grade`.
    let arr = TaggedValue::from(serde_json::json!({
        "__tag__": "Arrow", "inputs": 1, "grade": 3, "output": 2
    }));
    assert_eq!(cell_dim(&arr), 3);
    // A `∘₀` composite (`Arrow{first, second}`) stays a 1-cell.
    assert_eq!(cell_dim(&compose1(&int(1), &int(2))), 1);
}

#[test]
fn arrow_record_boundaries() {
    let arr = TaggedValue::from(serde_json::json!({
        "__tag__": "Arrow", "inputs": 1, "grade": 2, "output": 2
    }));
    assert_eq!(cell_src(&arr), int(1));
    assert_eq!(cell_tgt(&arr), int(2));
    // `Arrow{first, second}`: boundaries recurse to the ends of the chain.
    let comp = compose1(&int(3), &compose1(&int(4), &int(5)));
    assert_eq!(cell_src(&comp), int(3));
    assert_eq!(cell_tgt(&comp), int(5));
}

#[test]
fn comp_axis1_atoms_is_legacy_cell2() {
    // `3 ∘₁ 3` — degenerate cells compose, producing the legacy Cell2.
    let c = cell2_comp_axis(1, &int(3), &int(3)).unwrap();
    assert_eq!(
        tagged_to_value(&c),
        serde_json::json!({"__tag__": "Cell2", "__src__": 3, "__tgt__": 3, "value": 3})
    );
    // `1 ∘₁ 2` — boundary mismatch.
    assert!(cell2_comp_axis(1, &int(1), &int(2))
        .unwrap_err()
        .contains("boundary"));
}

#[test]
fn comp_axis0_keeps_horizontal_shape() {
    // `a ∘₀ b` on 2-cells: boundaries compose pairwise as Arrow records.
    let a = cell2(int(1), int(2), int(10));
    let b = cell2(int(2), int(3), int(20));
    let c = cell_comp_axis(0, 2, &a, &b).unwrap();
    assert_eq!(cell_dim(&c), 2);
    assert_eq!(
        cell_src(&c),
        TaggedValue::from(serde_json::json!({"__tag__": "Arrow", "first": 1, "second": 2}))
    );
}

#[test]
fn comp_axis2_pastes_3cells() {
    // `α ∘₂ β` on 3-cells: tgt₂(α) = src₂(β) required; the composite
    // is a `Cell{__dim__: 3}` whose boundaries are src₂(α)/tgt₂(β).
    let shared = cell2(int(1), int(2), int(5));
    let a = cell3(cell2(int(0), int(1), int(8)), shared.clone(), int(100));
    let b = cell3(shared.clone(), cell2(int(2), int(3), int(9)), int(200));
    let c = cell_comp_axis(2, 2, &a, &b).unwrap();
    assert_eq!(cell_dim(&c), 3);
    assert_eq!(cell_src(&c), cell2(int(0), int(1), int(8)));
    assert_eq!(cell_tgt(&c), cell2(int(2), int(3), int(9)));
    assert_eq!(cell_witness(&c), int(200));
    assert_eq!(c.get("__tag__").and_then(|t| t.as_str()), Some("Cell"));
}

#[test]
fn comp_axis2_boundary_mismatch() {
    let a = cell3(
        cell2(int(0), int(1), int(8)),
        cell2(int(1), int(2), int(5)),
        int(1),
    );
    let b = cell3(
        cell2(int(7), int(2), int(5)),
        cell2(int(2), int(3), int(9)),
        int(2),
    );
    let err = cell_comp_axis(2, 2, &a, &b).unwrap_err();
    assert!(err.contains("boundary"), "got {err}");
}

#[test]
fn comp_axis1_on_3cells_pastes_lower_boundaries() {
    // `∘₁` on 3-cells: the 1-boundary check `tgt₁(a) = src₁(b)`
    // compares whole 2-cells; the composite's other boundaries are
    // the `∘₁` of the operands' boundaries.
    let shared = cell2(int(1), int(2), int(5));
    let a = cell3(cell2(int(0), int(1), int(8)), shared.clone(), int(100));
    let b = cell3(shared.clone(), cell2(int(2), int(9), int(4)), int(200));
    let c = cell_comp_axis(1, 2, &a, &b).unwrap();
    assert_eq!(cell_dim(&c), 3);
    // src boundary: `Cell2{0,1,8} ∘₁ Cell2{1,2,5}` = Cell2{0,2,5}.
    assert_eq!(cell_src(&c), cell2(int(0), int(2), int(5)));
    // tgt boundary: `Cell2{1,2,5} ∘₁ Cell2{2,9,4}` = Cell2{1,9,4}.
    assert_eq!(cell_tgt(&c), cell2(int(1), int(9), int(4)));
}

#[test]
fn comp_promotes_lower_dimensional_operands() {
    // A 2-cell pasted at axis 2 against a 3-cell lifts to `id` of
    // itself; the boundary law then applies at dimension 3.
    let c2 = cell2(int(1), int(2), int(5));
    let a = cell3(c2.clone(), c2.clone(), c2.clone());
    let b = cell3(c2.clone(), cell2(int(2), int(3), int(9)), int(7));
    let c = cell_comp_axis(2, 2, &a, &b).unwrap();
    assert_eq!(cell_dim(&c), 3);
    assert_eq!(cell_src(&c), c2);
}

#[test]
fn comp_axis_at_dimension_errors() {
    // `k >= n` is a dimension error — 1-cells cannot paste at axis 1+.
    let err = cell_comp_axis(1, 1, &int(1), &int(1)).unwrap_err();
    assert!(err.contains("dimension"), "got {err}");
    let err = cell_comp_axis(2, 2, &int(1), &int(1)).unwrap_err();
    assert!(err.contains("dimension"), "got {err}");
}

#[test]
fn compose_runs_pasting_diagram() {
    // `[c, {axis: 1, cell: d}]` = `c ∘₁ d`.
    let c = cell2(int(1), int(2), int(10));
    let d = cell2(int(2), int(3), int(20));
    let diagram = TaggedValue::from(serde_json::json!([
        {"__tag__": "Cell2", "__src__": 1, "__tgt__": 2, "value": 10},
        {"axis": 1, "cell": {"__tag__": "Cell2", "__src__": 2, "__tgt__": 3, "value": 20}},
    ]));
    let out = cell_compose(&diagram).unwrap();
    assert_eq!(out, cell2(int(1), int(3), int(20)));
    let _ = (c, d);

    // Multi-step: `c ∘₁ d ∘₁ e`.
    let diagram = TaggedValue::from(serde_json::json!([
        {"__tag__": "Cell2", "__src__": 1, "__tgt__": 2, "value": 10},
        {"axis": 1, "cell": {"__tag__": "Cell2", "__src__": 2, "__tgt__": 3, "value": 20}},
        {"axis": 1, "cell": {"__tag__": "Cell2", "__src__": 3, "__tgt__": 4, "value": 30}},
    ]));
    let out = cell_compose(&diagram).unwrap();
    assert_eq!(out, cell2(int(1), int(4), int(30)));
}

#[test]
fn compose_at_axis2_and_step_errors() {
    let shared = cell2(int(1), int(2), int(5));
    let a = cell3(cell2(int(0), int(1), int(8)), shared.clone(), int(100));
    let b = cell3(shared, cell2(int(2), int(3), int(9)), int(200));
    let diagram = TaggedValue::Arr(Rc::from(vec![
        a.clone(),
        TaggedValue::from(serde_json::json!({"axis": 2, "cell":
            tagged_to_value(&b)})),
    ]));
    let out = cell_compose(&diagram).unwrap();
    assert_eq!(cell_dim(&out), 3);

    // A bad step reports its position.
    let bad = TaggedValue::from(serde_json::json!([
        {"__tag__": "Cell2", "__src__": 1, "__tgt__": 2, "value": 10},
        {"axis": 1, "cell": {"__tag__": "Cell2", "__src__": 9, "__tgt__": 3, "value": 20}},
    ]));
    let err = cell_compose(&bad).unwrap_err();
    assert!(
        err.contains("step 1") && err.contains("boundary"),
        "got {err}"
    );

    // Non-array and empty diagrams reject cleanly.
    assert!(cell_compose(&int(1)).is_err());
    assert!(cell_compose(&TaggedValue::Arr(Rc::from(vec![]))).is_err());
}

#[test]
fn object_view_projects_opaque_wire_records() {
    // `Obj` is its own view.
    let obj = TaggedValue::from(serde_json::json!({"a": 1}));
    let view = obj.object_view().unwrap();
    assert!(matches!(view, TaggedValue::Obj(_)));
    assert_eq!(view.get("a"), Some(&TaggedValue::Int(1)));

    // `Tensor` projects `{"__tensor__": {shape, data, dtype}}` — the
    // same record a `.hnl` program authors and the wire form emits.
    let t = TaggedValue::from(serde_json::json!({
        "__tensor__": {"shape": [2, 2], "data": [1, 2, 3, 4], "dtype": "f64"}
    }));
    assert!(t.is_tensor());
    let tv = t.object_view().unwrap();
    let inner = tv.get("__tensor__").and_then(|i| i.as_object()).unwrap();
    assert_eq!(
        inner.get("shape").and_then(|s| s.as_array()).unwrap().len(),
        2
    );
    assert_eq!(
        inner.get("data").and_then(|d| d.as_array()).unwrap().len(),
        4
    );
    assert_eq!(inner.get("dtype").and_then(|d| d.as_str()), Some("f64"));

    // `Bytes` projects `{"__bytes__": [n, …]}`.
    let b = TaggedValue::from(serde_json::json!({"__bytes__": [104, 105]}));
    let bv = b.object_view().unwrap();
    assert_eq!(
        bv.get("__bytes__")
            .and_then(|a| a.as_array())
            .unwrap()
            .len(),
        2
    );

    // Variants with their own `.hnl` projections (Pair, Either) and
    // scalars have no object view.
    assert!(TaggedValue::from(serde_json::json!({"__pair__": [1, 2]}))
        .object_view()
        .is_none());
    assert!(
        TaggedValue::from(serde_json::json!({"__either__": "left", "value": 1}))
            .object_view()
            .is_none()
    );
    assert!(TaggedValue::Int(1).object_view().is_none());
    assert!(TaggedValue::Null.object_view().is_none());
}

#[test]
fn sym_ty_link_roundtrips_the_wire_encoding() {
    // A nominal carrying both links serializes `parent` and `type`
    // and decodes them back (ADR-0154 §2).
    ensure_builtin_type_nominals();
    let int = Sym::seeded("type.Int");
    assert_eq!(int.ty().map(|t| t.name()), Some("Type"));
    assert_eq!(int.parent().map(|p| p.name()), Some("Number"));

    let wire = tagged_to_value(&TaggedValue::Sym(int.clone()));
    let back = TaggedValue::from(wire.clone());
    let TaggedValue::Sym(decoded) = &back else {
        panic!("expected a Sym, got {back:?}")
    };
    assert_eq!(decoded, &int);
    assert_eq!(decoded.ty().map(|t| t.name()), Some("Type"));
    assert_eq!(decoded.parent().map(|p| p.name()), Some("Number"));
    // The wire form carries both links.
    assert!(wire["__sym__"]["type"]["__sym__"]["name"].is_string());
    assert_eq!(
        wire["__sym__"]["parent"]["__sym__"]["name"],
        Value::from("Number")
    );
}

#[test]
fn builtin_graph_encodes_numeric_subtyping() {
    ensure_builtin_type_nominals();
    let nat = Sym::seeded("type.Nat");
    let int = Sym::seeded("type.Int");
    let number = Sym::seeded("type.Number");
    let float = Sym::seeded("type.Float");
    let value = Sym::seeded("type.Value");
    assert!(nat.is_descendant_of(&int));
    assert!(int.is_descendant_of(&number));
    assert!(nat.is_descendant_of(&number));
    assert!(float.is_descendant_of(&number));
    assert!(!int.is_descendant_of(&float));
    // `Value` tops the graph.
    assert!(number.is_descendant_of(&value));
    assert!(Sym::seeded("type.Str").is_descendant_of(&value));
    assert!(!value.is_descendant_of(&number));
    // Seeded mints are idempotent: the graph is ensured, not re-minted.
    assert_eq!(Sym::seeded("type.Int"), int);
}

#[test]
fn seeded_with_links_upgrades_bare_mints() {
    // A bare `seeded` mint gains its links later (same handle).
    let bare = Sym::seeded("type.Kilo");
    let h = bare.handle();
    assert!(bare.parent().is_none() && bare.ty().is_none());
    let p = Sym::seeded("type.Scale");
    let t = Sym::seeded("type.Type");
    let full = Sym::seeded_with_links("type.Kilo", Some(&p), Some(&t));
    assert_eq!(full.handle(), h);
    assert_eq!(full.parent().map(|x| x.handle()), Some(p.handle()));
    assert_eq!(full.ty().map(|x| x.handle()), Some(t.handle()));
    // Links are set-once: a second declare keeps the first parents.
    let other = Sym::seeded("type.Other");
    let again = Sym::seeded_with_links("type.Kilo", Some(&other), None);
    assert_eq!(again.parent().map(|x| x.handle()), Some(p.handle()));
}

#[test]
fn type_link_reads_membership() {
    ensure_builtin_type_nominals();
    // Literals default per ADR-0154 §5.
    let nat = TaggedValue::Sym(Sym::seeded("type.Nat"));
    let int = TaggedValue::Sym(Sym::seeded("type.Int"));
    let float = TaggedValue::Sym(Sym::seeded("type.Float"));
    assert_eq!(type_link(&TaggedValue::Int(1)), Some(nat.clone()));
    assert_eq!(type_link(&TaggedValue::Int(-2)), Some(int));
    assert_eq!(type_link(&TaggedValue::Float(1.5)), Some(float));
    assert_eq!(
        type_link(&TaggedValue::Bool(true)),
        Some(TaggedValue::Sym(Sym::seeded("type.Bool")))
    );
    // A ctor-shaped object yields its `type` field.
    let fapp = TaggedValue::from(serde_json::json!({
        "__former__": tagged_to_value(&TaggedValue::Sym(Sym::seeded("data.Vec"))),
        "indices": [0]
    }));
    let ctor = TaggedValue::from(serde_json::json!({
        "type": tagged_to_value(&fapp)
    }));
    assert_eq!(type_link(&ctor), Some(fapp));
    // A `__tag__` datum no longer bridges — it is a plain object,
    // a member of `type.Obj`.
    let datum = TaggedValue::from(serde_json::json!({
        "__tag__": "int", "__registry__": "type", "kind": "primitive"
    }));
    assert_eq!(
        type_link(&datum),
        Some(TaggedValue::Sym(Sym::seeded("type.Obj")))
    );
    // A nominal value yields its `ty` link.
    let int_sym = TaggedValue::Sym(Sym::seeded("type.Int"));
    assert_eq!(
        type_link(&int_sym),
        Some(TaggedValue::Sym(Sym::seeded("type.Type")))
    );
}

#[test]
fn instance_of_reads_both_links() {
    ensure_builtin_type_nominals();
    let int = TaggedValue::Sym(Sym::seeded("type.Int"));
    let nat = TaggedValue::Sym(Sym::seeded("type.Nat"));
    let number = TaggedValue::Sym(Sym::seeded("type.Number"));
    let float = TaggedValue::Sym(Sym::seeded("type.Float"));
    let ty = TaggedValue::Sym(Sym::seeded("type.Type"));
    let strs = TaggedValue::Sym(Sym::seeded("type.Str"));

    // `<:` read on nominal values (parent walk).
    assert!(instance_of(&nat, &int));
    assert!(instance_of(&nat, &number));
    assert!(instance_of(&float, &number));
    assert!(!instance_of(&int, &float));
    assert!(!instance_of(&number, &int));
    // Membership read on type values (the `ty` link): `Int : Type`.
    assert!(instance_of(&int, &ty));
    assert!(!instance_of(&int, &strs));
    // Literal defaults.
    assert!(instance_of(&TaggedValue::Int(1), &nat));
    assert!(instance_of(&TaggedValue::Int(1), &int));
    assert!(instance_of(&TaggedValue::Int(1), &number));
    assert!(!instance_of(&TaggedValue::Int(1), &float));
    assert!(instance_of(&TaggedValue::Int(-1), &int));
    assert!(!instance_of(&TaggedValue::Int(-1), &nat));
    assert!(instance_of(&TaggedValue::Float(1.5), &float));
    assert!(instance_of(&TaggedValue::Str("s".into()), &strs));
    assert!(instance_of(
        &TaggedValue::Null,
        &TaggedValue::Sym(Sym::seeded("type.Null"))
    ));
    // Former application as the nominal target.
    let vec = TaggedValue::from(serde_json::json!({
        "__former__": tagged_to_value(&TaggedValue::Sym(Sym::seeded("data.Vec"))),
        "indices": [2]
    }));
    let ctor = TaggedValue::from(serde_json::json!({
        "__ctor__": tagged_to_value(&TaggedValue::Sym(Sym::seeded("data.Vec.VCons"))),
        "type": tagged_to_value(&vec)
    }));
    assert!(instance_of(&ctor, &vec));
    assert!(!instance_of(&ctor, &nat));
}

#[test]
fn instance_of_tag_datum_is_plain_object() {
    // Post-deletion: a `__tag__` datum has no nominal bridge — it is
    // a plain object, a member of `type.Obj` and nothing else.
    ensure_builtin_type_nominals();
    let datum = |t: &str| {
        TaggedValue::from(serde_json::json!({
            "__tag__": t, "__registry__": "type", "kind": "primitive"
        }))
    };
    assert!(instance_of(
        &datum("int"),
        &TaggedValue::Sym(Sym::seeded("type.Obj"))
    ));
    assert!(!instance_of(
        &datum("int"),
        &TaggedValue::Sym(Sym::seeded("type.Int"))
    ));
    assert!(!instance_of(
        &datum("int"),
        &TaggedValue::Sym(Sym::seeded("type.Number"))
    ));
    // An unseeded nominal named like a std type no longer matches.
    let named = TaggedValue::Sym(Rc::new(Sym::fresh_with_parent(
        "Int",
        &Sym::fresh("Number"),
    )));
    assert!(!instance_of(&datum("int"), &named));
}
