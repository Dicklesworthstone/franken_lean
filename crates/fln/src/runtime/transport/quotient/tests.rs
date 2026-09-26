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
