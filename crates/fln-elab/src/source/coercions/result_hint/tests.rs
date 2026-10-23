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

#[test]
fn expected_family_keeps_a_parameter_already_in_the_holes_context() {
    let mut context = Context::new(&reader_fixture(), budget());
    let sigma = FVarId(name("sigma"));
    context
        .txn
        .lctx
        .add_param(sigma.clone(), name("S"), universe(), BinderInfo::Implicit);
    let element = Expr::fvar(sigma.clone());
    let family = context.hole(constructor_type()).unwrap();
    let actual = Expr::app(family.clone(), element.clone());
    let expected = Expr::app(Expr::const_(name("ReaderLike"), vec![]), element);
    assert!(context.flexible_non_pattern(&actual).unwrap());
    let value = context.hole(actual.clone()).unwrap();
    context
        .finish_explicit_term(
            Typed {
                value,
                type_: actual,
            },
            Some(&expected),
        )
        .unwrap();
    assert_eq!(
        context.instantiate(&family).unwrap(),
        Expr::const_(name("ReaderLike"), vec![])
    );
}

#[test]
fn a_local_created_after_the_hole_remains_a_genuine_pattern_argument() {
    let mut context = Context::new(&reader_fixture(), budget());
    let family = context.hole(constructor_type()).unwrap();
    let sigma = FVarId(name("sigma"));
    context
        .txn
        .lctx
        .add_param(sigma.clone(), name("S"), universe(), BinderInfo::Implicit);
    let actual = Expr::app(family, Expr::fvar(sigma));
    assert!(!context.flexible_non_pattern(&actual).unwrap());
}

#[test]
fn an_early_result_hint_does_not_abstract_a_captured_family_parameter() {
    let mut context = Context::new(&reader_fixture(), budget());
    let sigma = FVarId(name("sigma"));
    context
        .txn
        .lctx
        .add_param(sigma.clone(), name("S"), universe(), BinderInfo::Implicit);
    let element = Expr::fvar(sigma);
    let family = context.hole(constructor_type()).unwrap();
    let actual = Expr::app(family.clone(), element.clone());
    let reader = Expr::const_(name("ReaderLike"), vec![]);
    let expected = Expr::app(reader.clone(), element);
    context.constrain_result_hint(&actual, &expected).unwrap();
    assert_eq!(context.instantiate(&family).unwrap(), reader);
}

fn captured_family() -> (Context, Expr, Expr, Expr, Expr) {
    let mut context = Context::new(&fixture(), budget());
    let carrier = FVarId(name("carrier"));
    context.txn.lctx.add_param(
        carrier.clone(),
        name("C"),
        Expr::forall_e(
            name("S"),
            universe(),
            constructor_type(),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let sigma = FVarId(name("sigma"));
    context
        .txn
        .lctx
        .add_param(sigma.clone(), name("S"), universe(), BinderInfo::Implicit);
    let element = Expr::fvar(sigma);
    let family = context.hole(constructor_type()).unwrap();
    let actual = Expr::app(family.clone(), element.clone());
    let selected = Expr::app(Expr::fvar(carrier), element.clone());
    let expected = Expr::app(selected.clone(), element);
    (context, family, actual, expected, selected)
}

#[test]
fn both_hint_orientations_preserve_the_captured_prefix_not_just_eta_equality() {
    for reverse in [false, true] {
        let (mut context, family, actual, expected, selected) = captured_family();
        let result = if reverse {
            context.contextual_result_hint(&expected, &actual)
        } else {
            context.contextual_result_hint(&actual, &expected)
        };
        assert!(result.unwrap());
        assert_eq!(context.instantiate(&family).unwrap(), selected);
        assert!(context.coercion_eq(&actual, &expected).unwrap());
    }
}

#[test]
fn contextual_hint_resource_stops_restore_assignments_but_charge_work() {
    let (original, family, actual, expected, selected) = captured_family();
    let mut complete = original.clone();
    assert!(complete.contextual_result_hint(&expected, &actual).unwrap());
    let used = complete.txn.budget.heartbeats_consumed - original.txn.budget.heartbeats_consumed;
    assert!(used > 16);
    for allowance in [1, 16, used / 2, used - 1] {
        let mut trial = original.clone();
        trial.txn.budget.max_heartbeats = trial.txn.budget.heartbeats_consumed + allowance;
        let before = trial.txn.clone();
        let next = trial.next;
        let error = trial
            .contextual_result_hint(&expected, &actual)
            .unwrap_err();
        assert!(
            match &error {
                NatDefinitionElabError::Inference(SourceInferenceError::ResourceLimit) => true,
                NatDefinitionElabError::Inference(SourceInferenceError::Unification(cause)) => {
                    matches!(
                        cause.as_ref(),
                        UnificationError::HeartbeatLimit
                            | UnificationError::StepLimit { .. }
                            | UnificationError::NodeLimit { .. }
                    )
                }
                _ => false,
            },
            "{error:?}"
        );
        assert!(trial.txn.budget.heartbeats_consumed > before.budget.heartbeats_consumed);
        trial.txn.budget = before.budget.clone();
        assert_eq!(trial.txn, before);
        assert_eq!(trial.next, next);
        trial.txn.budget.max_heartbeats = 0;
        assert!(trial.contextual_result_hint(&expected, &actual).unwrap());
        assert_eq!(trial.instantiate(&family).unwrap(), selected);
    }
}

#[test]
fn contextual_hint_cannot_capture_a_later_local_or_solve_an_opaque_goal() {
    let (original, family, actual, expected, _) = captured_family();
    let mut escaping = original.clone();
    let foreign = FVarId(name("foreign"));
    escaping.txn.lctx.add_param(
        foreign.clone(),
        name("foreign"),
        constructor_type(),
        BinderInfo::Default,
    );
    let ExprNode::App { a, .. } = actual.node() else {
        panic!("applied family");
    };
    let target = Expr::app(Expr::fvar(foreign), a.clone());
    let before = escaping.txn.clone();
    assert!(!escaping.contextual_result_hint(&actual, &target).unwrap());
    escaping.txn.budget = before.budget.clone();
    assert_eq!(escaping.txn, before);
    let mut opaque = original;
    let id = MVarId(name("opaque"));
    opaque.txn.mvars.declare(
        id.clone(),
        name("opaque"),
        constructor_type(),
        opaque.txn.lctx.clone(),
        MetavarKind::SyntheticOpaque,
        0,
        None,
    );
    let opaque_application = Expr::app(Expr::mvar(id.clone()), a.clone());
    let before = opaque.txn.clone();
    assert!(
        !opaque
            .contextual_result_hint(&opaque_application, &expected)
            .unwrap()
    );
    assert!(!opaque.txn.mvars.is_assigned(&id));
    opaque.txn.budget = before.budget.clone();
    assert_eq!(opaque.txn, before);
    assert_eq!(opaque.instantiate(&family).unwrap(), family);
}
