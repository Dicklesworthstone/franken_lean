use super::*;
use fln_env::constants::{
    ConstantInfo, ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints,
};

fn name(label: &str) -> Name {
    Name::from_components([label])
}
fn nat() -> Expr {
    Expr::const_(name("Nat"), vec![])
}
fn universe() -> Expr {
    Expr::sort(Level::one())
}
fn constructor_type() -> Expr {
    Expr::forall_e(name("A"), universe(), universe(), BinderInfo::Default)
}
fn budget() -> Budget {
    Budget::for_stack_bytes(2 * 1024 * 1024)
}
fn fixture() -> Environment {
    crate::seed::bootstrap_nat_environment(budget()).unwrap()
}

fn with_family(env: &Environment, label: &str, body: Expr) -> Environment {
    // Explicit, well-scoped type fixtures only. Each source result below is
    // still checked by ordinary declaration admission; no instance is mocked.
    env.add_decl(ConstantInfo::Defn(DefinitionVal {
        base: ConstantVal {
            name: name(label),
            level_params: vec![],
            type_: constructor_type(),
        },
        value: Expr::lam(name("A"), universe(), body, BinderInfo::Default),
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Safe,
        all: vec![name(label)],
    }))
    .unwrap()
}

fn reader_fixture() -> Environment {
    with_family(
        &fixture(),
        "ReaderLike",
        Expr::forall_e(
            name("state"),
            nat(),
            Expr::bvar(1).unwrap(),
            BinderInfo::Default,
        ),
    )
}

#[test]
fn source_result_selects_the_implicit_constructor_before_its_value_argument() {
    let env = reader_fixture();
    for source in [
        "def inferred (m : Type -> Type) (factory : {n : Type -> Type} -> Nat -> n Nat) : m Nat := factory 7",
        "def inferred (m : Type -> Type) (factory : {n : Type -> Type} -> (value : Nat) -> n Nat) : m Nat := factory (value := 7)",
        "def inferred (factory : {n : Type -> Type} -> Nat -> n Nat) : ReaderLike Nat := factory 7",
        "def inferred (factory : {n : Type -> Type} -> (value : Nat) -> n Nat) : ReaderLike Nat := factory (value := 7)",
    ] {
        let checked = crate::check_definition_source(source.as_bytes(), &env, budget())
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));
        assert!(matches!(
            checked.outcome,
            Outcome::Complete(Verdict::Accepted { .. })
        ));
        let Declaration::Defn(definition) = checked.declaration else {
            panic!("definition expected");
        };
        assert!(!definition.value.has_expr_mvar());
        assert!(!definition.value.has_level_mvar());
    }
}

#[test]
fn expected_function_backed_constructor_can_infer_an_unknown_result_element() {
    let mut context = Context::new(&reader_fixture(), budget());
    let family = context.hole(constructor_type()).unwrap();
    let element = context.hole(universe()).unwrap();
    let reader = Expr::const_(name("ReaderLike"), vec![]);
    let actual = Expr::app(family.clone(), nat());
    let expected = Expr::app(reader.clone(), element.clone());
    context.constrain_result_hint(&actual, &expected).unwrap();
    assert_eq!(context.instantiate(&family).unwrap(), reader);
    assert_eq!(context.instantiate(&element).unwrap(), nat());
    assert!(context.coercion_eq(&actual, &expected).unwrap());
}

#[test]
fn ordinary_erasing_family_conversion_retains_its_existing_inference() {
    let env = with_family(&reader_fixture(), "Erase", nat());
    let mut context = Context::new(&env, budget());
    let element = context.hole(universe()).unwrap();
    let erase = Expr::const_(name("Erase"), vec![]);
    let actual = Expr::app(erase.clone(), element.clone());
    let expected = Expr::app(erase.clone(), nat());
    // In this seed-only environment the original result hint first calls
    // constrain. Preserve its actual choice; do not prescribe injectivity or
    // non-injectivity for its already existing inference heuristics.
    let mut baseline = context.clone();
    baseline.constrain(&actual, &expected).unwrap();
    context.constrain_result_hint(&actual, &expected).unwrap();
    assert_eq!(
        context.instantiate(&element).unwrap(),
        baseline.instantiate(&element).unwrap()
    );
    let mut actual_state = context.txn.clone();
    actual_state.budget = baseline.txn.budget.clone();
    assert_eq!(actual_state, baseline.txn);
    assert_eq!(context.next, baseline.next);
    assert!(context.coercion_eq(&actual, &expected).unwrap());

    // Fixed, unequal arguments still convert because this family erases them.
    // The new approximation must never replace that existing equality with
    // a requirement that Nat and ReaderLike Nat themselves be equal.
    let actual = Expr::app(erase.clone(), nat());
    let expected = Expr::app(
        erase,
        Expr::app(Expr::const_(name("ReaderLike"), vec![]), nat()),
    );
    context.constrain_result_hint(&actual, &expected).unwrap();
    assert!(context.coercion_eq(&actual, &expected).unwrap());
}

#[test]
fn unsuccessful_argument_match_rolls_back_prior_argument_assignments() {
    let mut context = Context::new(&fixture(), budget());
    let family_type = Expr::forall_e(
        name("A"),
        universe(),
        constructor_type(),
        BinderInfo::Default,
    );
    let family = context.hole(family_type).unwrap();
    let element = context.hole(universe()).unwrap();
    // Rightmost comparison can choose element := Nat, but the preceding
    // Nat = Type mismatch must roll that choice back with the family hole.
    let actual = Expr::app(Expr::app(family.clone(), nat()), element.clone());
    let expected = Expr::app(Expr::app(family.clone(), universe()), nat());
    let before = context.txn.clone();
    let next = context.next;
    context.first_order_result_hint(&actual, &expected).unwrap();
    assert!(context.txn.budget.heartbeats_consumed > before.budget.heartbeats_consumed);
    assert_eq!(context.instantiate(&element).unwrap(), element);
    assert_eq!(context.instantiate(&family).unwrap(), family);
    let mut after = context.txn.clone();
    after.budget = before.budget.clone();
    assert_eq!(after, before);
    assert_eq!(context.next, next);
}

#[test]
fn expected_constructor_hint_does_not_discard_a_resource_stop() {
    let mut context = Context::new(&fixture(), budget());
    let family = context.hole(constructor_type()).unwrap();
    let expected = Expr::app(family.clone(), nat());
    let actual = Expr::app(family, nat());
    context.txn.budget.max_heartbeats = context.txn.budget.heartbeats_consumed + 1;
    let before = context.txn.clone();
    let next = context.next;
    assert!(matches!(
        context.first_order_result_hint(&actual, &expected),
        Err(NatDefinitionElabError::Inference(
            SourceInferenceError::ResourceLimit
        ))
    ));
    assert!(context.txn.budget.heartbeats_consumed > before.budget.heartbeats_consumed);
    let mut after = context.txn.clone();
    after.budget = before.budget.clone();
    assert_eq!(after, before);
    assert_eq!(context.next, next);
}
