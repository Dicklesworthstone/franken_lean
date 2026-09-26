//! Structural controls; runtime_quotients separately admits actual source.
use super::*;
use fln_core::level::Level;
use fln_env::constants::{AxiomVal, ConstantVal, QuotKind};

fn environment(changed: bool) -> Environment {
    let Declaration::Quotient(declarations) = fln_elab::seed::quotient_seed_declaration() else {
        panic!("quotient quartet");
    };
    let mut environment = Environment::new();
    for mut declaration in declarations {
        if changed && declaration.kind == QuotKind::Lift {
            declaration.kind = QuotKind::Ind;
        }
        environment = environment.add_decl(ConstantInfo::Quot(declaration)).unwrap();
    }
    environment
}
fn ty(label: &str) -> Expr {
    Expr::const_(name(label), Vec::new())
}
fn head(label: &str, levels: usize) -> Expr {
    Expr::const_(name(label), vec![Level::one(); levels])
}
fn app(function: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(function, Expr::app)
}
fn q(carrier: Expr, relation: Expr) -> Expr {
    app(head("Quot", 1), [carrier, relation])
}
fn b(index: u32) -> Expr {
    Expr::bvar(index).unwrap()
}

#[test]
fn carrier_erasure_does_not_inspect_the_relation_or_its_captures() {
    let environment = environment(false);
    let source = q(ty("Nat"), app(ty("unavailableRelation"), [b(0)]));
    let actual = Preparation::new(&environment, IngressLimits::default())
        .erase_data_indices(&source)
        .unwrap();
    assert_eq!(actual, ty("Nat"));
}

#[test]
fn nested_quotients_are_erased_on_the_existing_type_worklist() {
    let environment = environment(false);
    let mut source = ty("String");
    for _ in 0..64 {
        source = q(source, ty("relation"));
    }
    let actual = Preparation::new(&environment, IngressLimits::default())
        .erase_data_indices(&source)
        .unwrap();
    assert_eq!(actual, ty("String"));
}

#[test]
fn name_collisions_and_changed_quartets_cannot_authorize_erasure() {
    let impostor = Environment::new()
        .add_decl(ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: name("Quot"),
                level_params: Vec::new(),
                type_: Expr::sort(Level::one()),
            },
            is_unsafe: false,
        }))
        .unwrap();
    for environment in [impostor, environment(true), Environment::new()] {
        assert!(
            Preparation::new(&environment, IngressLimits::default())
                .erase_data_indices(&q(ty("Nat"), ty("relation")))
                .is_err()
        );
    }
}

#[test]
fn constructor_retains_the_exact_representative_computation() {
    let environment = environment(false);
    let payload = app(ty("observe"), [b(0)]);
    let actual = Preparation::new(&environment, IngressLimits::default())
        .quotient_operation(
            &head("Quot.mk", 1),
            &[ty("Nat"), ty("relation"), payload.clone()],
        )
        .unwrap()
        .unwrap();
    assert_eq!(actual, payload);
}

#[test]
fn lift_binds_function_then_representative_without_copying_either() {
    let environment = environment(false);
    let function = app(ty("makeFunction"), [b(0)]);
    let representative = app(ty("makeRepresentative"), [b(1)]);
    let actual = Preparation::new(&environment, IngressLimits::default())
        .quotient_operation(
            &head("Quot.lift", 2),
            &[
                ty("Nat"),
                ty("relation"),
                ty("Nat"),
                function.clone(),
                ty("checkedRespectfulness"),
                representative,
            ],
        )
        .unwrap()
        .unwrap();
    let expected = Expr::let_e(
        Name::anonymous(),
        Expr::forall_e(Name::anonymous(), ty("Nat"), ty("Nat"), BinderInfo::Default),
        function,
        Expr::let_e(
            Name::anonymous(),
            ty("Nat"),
            app(ty("makeRepresentative"), [b(2)]),
            Expr::app(b(1), b(0)),
            false,
        ),
        false,
    );
    assert_eq!(actual, expected);
}

#[test]
fn malformed_arities_and_proof_only_primitives_are_not_runtime_values() {
    let environment = environment(false);
    for (label, levels, count) in [
        ("Quot.mk", 0, 3),
        ("Quot.mk", 1, 4),
        ("Quot.lift", 1, 6),
        ("Quot.ind", 1, 5),
        ("Quot.sound", 1, 5),
    ] {
        assert!(
            Preparation::new(&environment, IngressLimits::default())
                .quotient_operation(&head(label, levels), &vec![ty("Nat"); count])
                .unwrap()
                .is_none()
        );
    }
}

#[test]
fn quotient_lowering_respects_work_and_context_budgets() {
    let environment = environment(false);
    let mut limits = IngressLimits::default();
    limits.max_nodes = 0;
    assert!(
        Preparation::new(&environment, limits)
            .erase_data_indices(&q(ty("Nat"), ty("relation")))
            .is_err()
    );
    let mut limits = IngressLimits::default();
    limits.max_context_depth = 1;
    assert!(matches!(
        Preparation::new(&environment, limits).quotient_operation(
            &head("Quot.lift", 2),
            &[ty("Nat"), ty("r"), ty("Nat"), ty("f"), ty("h"), b(0)]
        ),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::ContextDepth,
            ..
        })
    ));
}

#[test]
fn partial_constructors_have_a_typed_identity_body() {
    let environment = environment(false);
    let actual = Preparation::new(&environment, IngressLimits::default())
        .quotient_operation(&head("Quot.mk", 1), &[ty("Nat"), ty("r")])
        .unwrap()
        .unwrap();
    let ExprNode::LetE { value, body, .. } = actual.node() else {
        panic!("typed constructor function");
    };
    assert_eq!(*body, b(0));
    let ExprNode::Lam { binder_type, body, .. } = value.node() else {
        panic!("missing representative parameter");
    };
    assert_eq!(*binder_type, ty("Nat"));
    assert_eq!(*body, b(0));
}

#[test]
fn partial_lift_captures_the_supplied_function_before_returning() {
    let environment = environment(false);
    let function = app(ty("makeFunction"), [b(0)]);
    let actual = Preparation::new(&environment, IngressLimits::default())
        .quotient_operation(
            &head("Quot.lift", 2),
            &[ty("Nat"), ty("r"), ty("Nat"), function.clone(), ty("proof")],
        )
        .unwrap()
        .unwrap();
    let ExprNode::LetE { value, body, .. } = actual.node() else {
        panic!("strict function initializer");
    };
    assert_eq!(*value, function);
    let ExprNode::LetE { value, .. } = body.node() else {
        panic!("typed residual function");
    };
    let ExprNode::Lam { binder_type, body, .. } = value.node() else {
        panic!("representative parameter");
    };
    assert_eq!(*binder_type, ty("Nat"));
    assert_eq!(*body, Expr::app(b(1), b(0)));
}

#[test]
fn an_overapplied_result_finishes_lifting_before_its_next_argument() {
    let environment = environment(false);
    let result_type = Expr::forall_e(Name::anonymous(), ty("Nat"), ty("Nat"), BinderInfo::Default);
    let actual = Preparation::new(&environment, IngressLimits::default())
        .quotient_operation(
            &head("Quot.lift", 2),
            &[
                ty("Nat"), ty("r"), result_type, ty("f"), ty("proof"),
                app(ty("representative"), [b(0)]), app(ty("afterLift"), [b(0)]),
            ],
        )
        .unwrap()
        .unwrap();
    let ExprNode::LetE { value, body, .. } = actual.node() else {
        panic!("lifting must finish first");
    };
    assert!(matches!(value.node(), ExprNode::LetE { .. }));
    let ExprNode::LetE { value, .. } = body.node() else {
        panic!("then the trailing argument");
    };
    assert_eq!(*value, app(ty("afterLift"), [b(1)]));
}

#[test]
fn scalar_overapplication_is_not_dropped_and_argument_budgets_remain_enforced() {
    let environment = environment(false);
    let args = [ty("Nat"), ty("r"), ty("Nat"), ty("f"), ty("proof"), b(0), b(1)];
    assert!(
        Preparation::new(&environment, IngressLimits::default())
            .quotient_operation(&head("Quot.lift", 2), &args)
            .is_err()
    );
    let limits = IngressLimits { max_application_args: 6, ..IngressLimits::default() };
    assert!(matches!(
        Preparation::new(&environment, limits).quotient_operation(&head("Quot.lift", 2), &args),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::ApplicationArguments,
            limit: 6,
            observed: 7,
        })
    ));
}
