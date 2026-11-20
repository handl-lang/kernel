use super::*;

fn t(td: TermData) -> Term {
    td.to_term().expect("TermData -> Term conversion")
}

fn id() -> Term {
    t(TermData::op("id", vec![], &ArrSource::Native, None))
}

#[test]
fn instantiate_var_produces_bound_scheme() {
    let mut subst = LawSubst::new();
    subst.bind(
        "f",
        t(TermData::op("concrete_f", vec![], &ArrSource::Native, None)),
    );
    let result = instantiate(&LawExpr::Var(LawVar("f".into())), &subst);
    assert_eq!(
        result,
        t(TermData::op("concrete_f", vec![], &ArrSource::Native, None))
    );
}

#[test]
fn instantiate_id_produces_identity_arrow() {
    let subst = LawSubst::new();
    let result = instantiate(&LawExpr::Id, &subst);
    assert_eq!(result, id());
}

#[test]
fn instantiate_const_produces_base_arrow() {
    let subst = LawSubst::new();
    let result = instantiate(&LawExpr::Const("sort".into()), &subst);
    assert_eq!(
        result,
        t(TermData::op("sort", vec![], &ArrSource::Native, None))
    );
}

#[test]
#[should_panic(expected = "unbound law variable: f")]
fn instantiate_unbound_var_panics() {
    let subst = LawSubst::new();
    let _ = instantiate(&LawExpr::Var(LawVar("f".into())), &subst);
}

#[test]
fn instantiate_seq_produces_scheme_seq() {
    let f = TermData::op("a", vec![], &ArrSource::Native, None);
    let g = TermData::op("b", vec![], &ArrSource::Native, None);
    let mut subst = LawSubst::new();
    subst.bind("f", t(f.clone()));
    subst.bind("g", t(g.clone()));
    let result = instantiate(
        &LawExpr::Seq(
            Box::new(LawExpr::Var(LawVar("f".into()))),
            Box::new(LawExpr::Var(LawVar("g".into()))),
        ),
        &subst,
    );
    assert_eq!(result, t(TermData::seq(f, g)));
}

#[test]
fn check_functor_identity_satisfied() {
    let catalog = builtin_quantified_laws();
    let law = catalog
        .iter()
        .find(|l| l.name == "functor_identity")
        .expect("functor_identity in catalog");
    assert_eq!(check_quantified_law(law), LawCheckResult::Satisfied);
}

#[test]
fn check_functor_composition_satisfied() {
    let catalog = builtin_quantified_laws();
    let law = catalog
        .iter()
        .find(|l| l.name == "functor_composition")
        .expect("functor_composition in catalog");
    assert_eq!(check_quantified_law(law), LawCheckResult::Satisfied);
}

#[test]
fn check_id_left_satisfied() {
    let catalog = builtin_quantified_laws();
    let law = catalog
        .iter()
        .find(|l| l.name == "id_left")
        .expect("id_left in catalog");
    assert_eq!(check_quantified_law(law), LawCheckResult::Satisfied);
}

#[test]
fn check_id_right_satisfied() {
    let catalog = builtin_quantified_laws();
    let law = catalog
        .iter()
        .find(|l| l.name == "id_right")
        .expect("id_right in catalog");
    assert_eq!(check_quantified_law(law), LawCheckResult::Satisfied);
}

#[test]
fn check_roundtrip_not_applicable() {
    let catalog = builtin_quantified_laws();
    let law = catalog
        .iter()
        .find(|l| l.name == "roundtrip")
        .expect("roundtrip in catalog");
    assert!(law.axiom.is_some());
    assert_eq!(law.axiom.as_deref(), Some("hinv"));
    assert_eq!(check_quantified_law(law), LawCheckResult::NotApplicable);
}

#[test]
fn generate_test_substitutions_zero_vars_one_subst() {
    let vars: Vec<LawVar> = vec![];
    let substs = generate_test_substitutions(&vars);
    assert_eq!(substs.len(), 1, "0 vars -> 1 substitution");
}

#[test]
fn generate_test_substitutions_one_var_four_substs() {
    let vars = vec![LawVar("f".into())];
    let substs = generate_test_substitutions(&vars);
    assert_eq!(substs.len(), 4, "1 var -> 4 substitutions");
}

#[test]
fn generate_test_substitutions_two_vars_sixteen_substs() {
    let vars = vec![LawVar("f".into()), LawVar("g".into())];
    let substs = generate_test_substitutions(&vars);
    assert_eq!(substs.len(), 16, "2 vars -> 16 substitutions");
}

#[test]
fn catalog_has_exactly_five_laws() {
    let catalog = builtin_quantified_laws();
    assert_eq!(
        catalog.len(),
        5,
        "exactly 5 laws (4 CutElim-proven + 1 axiom)"
    );
    let proven = catalog.iter().filter(|l| l.axiom.is_none()).count();
    let axiom = catalog.iter().filter(|l| l.axiom.is_some()).count();
    assert_eq!(proven, 4, "4 CutElim-proven laws");
    assert_eq!(axiom, 1, "1 axiom-requiring law");
}

#[test]
fn bogus_law_first_eq_f_is_violated() {
    // first(f) = f is NOT true: first adds a product component.
    let bogus = QuantifiedLaw {
        name: "bogus_first_eq_f".into(),
        vars: vec![LawVar("f".into())],
        lhs: LawExpr::First(Box::new(LawExpr::Var(LawVar("f".into())))),
        rhs: LawExpr::Var(LawVar("f".into())),
        axiom: None,
    };
    assert_eq!(check_quantified_law(&bogus), LawCheckResult::Violated);
    // Specifically: it fails under the arr("test_f") substitution.
    let mut subst = LawSubst::new();
    subst.bind(
        "f",
        t(TermData::op("test_f", vec![], &ArrSource::Native, None)),
    );
    let lhs = instantiate(&bogus.lhs, &subst);
    let rhs = instantiate(&bogus.rhs, &subst);
    assert!(
        !law_equal(&lhs, &rhs),
        "first(arr(\"test_f\")) != arr(\"test_f\") under CutElim"
    );
}

#[test]
fn display_uses_forall_explicitly() {
    let catalog = builtin_quantified_laws();
    let law = catalog
        .iter()
        .find(|l| l.name == "functor_composition")
        .expect("functor_composition in catalog");
    let display = format!("{}", law);
    assert!(
        display.contains("forall"),
        "display uses 'forall' explicitly: {}",
        display
    );
    assert!(
        display.contains("forall f g"),
        "display shows 'forall f g': {}",
        display
    );
}

#[test]
fn display_law_expr() {
    assert_eq!(format!("{}", LawExpr::Id), "id");
    assert_eq!(format!("{}", LawExpr::Const("sort".into())), "sort");
    assert_eq!(format!("{}", LawExpr::Var(LawVar("f".into()))), "f");
    assert_eq!(
        format!("{}", LawExpr::First(Box::new(LawExpr::Id))),
        "first(id)"
    );
}
