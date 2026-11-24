//! Exercise the real matcher and original proof applications independently of
//! source syntax imports. Every fixture declaration is ordinarily admitted.
use super::*;
use fln_core::expr::NatLit;
use fln_core::outcome::Outcome;
use fln_env::constants::{AxiomVal, ConstantVal, OpaqueVal, TheoremVal};
use fln_env::environment::{DeclarationBudget, DeclarationCommitted};
use fln_env::pmap::CollisionBudget;
use fln_kernel::capability::{Published, admit};
use fln_kernel::council::{Council, CouncilOutcome, convene};

fn budget() -> Budget {
    Budget::for_stack_bytes(2 * 1024 * 1024)
}
fn publish(environment: &Environment, declaration: Declaration) -> Environment {
    let Outcome::Complete(admitted) = admit(environment, declaration, budget()) else {
        panic!("fixture admission did not complete");
    };
    let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted) else {
        panic!("fixture declaration was rejected");
    };
    match checked.publish(
        DeclarationBudget::default(),
        CollisionBudget::default(),
        None,
    ) {
        Outcome::Complete(Published::Committed(DeclarationCommitted::Published(result))) => {
            result.environment
        }
        Outcome::Complete(Published::BlockCommitted(result)) => result.environment,
        other => panic!("fixture publication failed: {other:?}"),
    }
}
fn axiom(environment: &Environment, text: &str, type_: Expr) -> Environment {
    publish(
        environment,
        Declaration::Axiom(AxiomVal {
            base: ConstantVal {
                name: name(text),
                level_params: Vec::new(),
                type_,
            },
            is_unsafe: false,
        }),
    )
}
fn bv(index: u32) -> Expr {
    Expr::bvar(index).unwrap()
}
fn number(value: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(value)))
}
fn relation(text: &str, left: Expr, right: Expr) -> Expr {
    apply(constant(text), [left, right])
}
fn fixture() -> (Context, crate::grind_patterns::GrindPattern) {
    let mut environment = crate::seed::bootstrap_nat_environment(budget()).unwrap();
    for text in ["R", "S"] {
        environment = axiom(
            &environment,
            text,
            arrow(
                constant("Nat"),
                arrow(constant("Nat"), Expr::sort(Level::zero())),
            ),
        );
    }
    let type_ = arrow(
        constant("Nat"),
        arrow(
            constant("Nat"),
            arrow(
                relation("R", bv(1), bv(0)),
                arrow(relation("S", bv(1), bv(2)), relation("R", bv(3), bv(3))),
            ),
        ),
    );
    environment = axiom(&environment, "rule", type_);
    (
        Context::new(&environment, budget()),
        crate::grind_patterns::GrindPattern {
            declaration: name("rule"),
            num_params: 4,
            data_params: 2,
            patterns: vec![relation("R", bv(3), bv(2)), relation("S", bv(2), bv(3))],
            captured: None,
        },
    )
}

#[test]
fn simultaneous_user_patterns_preserve_full_telescope_proof_premises() {
    let (mut context, row) = fixture();
    let before = context.txn.lctx.clone();
    let (evidence, levels) = context.grind_global_lemma(&row.declaration).unwrap();
    let mut quantifiers = Quantifiers::default();
    quantifiers
        .register_explicit(&mut context, &evidence, &levels, &row)
        .unwrap();
    assert_eq!(context.txn.lctx, before);
    let first = relation("R", number(0), number(1));
    let second = relation("S", number(1), number(0));
    let mut graph = Equalities::default();
    graph.intern(&mut context, &first).unwrap();
    assert!(
        quantifiers
            .instantiate(&mut context, &graph)
            .unwrap()
            .is_empty()
    );
    graph.intern(&mut context, &second).unwrap();
    let instances = quantifiers.instantiate(&mut context, &graph).unwrap();
    assert_eq!(instances.len(), 1);
    let instance = &instances[0];
    assert_eq!(
        instance.value,
        apply(constant("rule"), [number(0), number(1)])
    );
    assert_eq!(
        instance.type_,
        arrow(first, arrow(second, relation("R", number(0), number(0)))),
    );
    // Re-admit the emitted proof at its actual implication type. The matcher
    // has selected data arguments, not manufactured proofs of either premise.
    let published = publish(
        &context.txn.env,
        Declaration::Thm(TheoremVal {
            base: ConstantVal {
                name: name("checked_instance"),
                level_params: Vec::new(),
                type_: instance.type_.clone(),
            },
            value: instance.value.clone(),
            all: vec![name("checked_instance")],
        }),
    );
    assert!(published.contains(&name("checked_instance")));
    assert!(
        quantifiers
            .instantiate(&mut context, &graph)
            .unwrap()
            .is_empty()
    );
}

#[test]
fn ground_user_pattern_instantiates_without_data_parameters() {
    let environment = crate::seed::bootstrap_nat_environment(budget()).unwrap();
    let environment = axiom(&environment, "P", Expr::sort(Level::zero()));
    let environment = axiom(&environment, "assumption", constant("P"));
    let environment = publish(
        &environment,
        Declaration::Opaque(OpaqueVal {
            base: ConstantVal {
                name: name("witness"),
                level_params: Vec::new(),
                type_: constant("P"),
            },
            value: constant("assumption"),
            is_unsafe: false,
            all: vec![name("witness")],
        }),
    );
    let mut context = Context::new(&environment, budget());
    let row = crate::grind_patterns::GrindPattern {
        declaration: name("witness"),
        num_params: 0,
        data_params: 0,
        patterns: vec![constant("P")],
        captured: None,
    };
    let mut quantifiers = Quantifiers::default();
    context
        .grind_registered_pattern(&mut quantifiers, &row)
        .unwrap();
    let mut graph = Equalities::default();
    graph.intern(&mut context, &constant("P")).unwrap();
    let instances = quantifiers.instantiate(&mut context, &graph).unwrap();
    assert_eq!(instances.len(), 1);
    assert_eq!(instances[0].value, constant("witness"));
    assert_eq!(instances[0].type_, constant("P"));
}

#[test]
fn invalid_user_telescope_restores_locals_without_registering_a_template() {
    let (mut context, mut row) = fixture();
    let before = context.txn.lctx.clone();
    let (evidence, levels) = context.grind_global_lemma(&row.declaration).unwrap();
    row.num_params -= 1;
    let mut quantifiers = Quantifiers::default();
    assert!(
        quantifiers
            .register_explicit(&mut context, &evidence, &levels, &row)
            .is_err()
    );
    assert_eq!(context.txn.lctx, before);
    assert!(quantifiers.theorems.is_empty());
    row.num_params += 1;
    quantifiers
        .register_explicit(&mut context, &evidence, &levels, &row)
        .unwrap();
    assert_eq!(context.txn.lctx, before);
    assert_eq!(quantifiers.theorems.len(), 1);
}

fn poly_axiom(environment: &Environment, text: &str, type_: Expr) -> Environment {
    publish(
        environment,
        Declaration::Axiom(AxiomVal {
            base: ConstantVal {
                name: name(text),
                level_params: vec![name("u")],
                type_,
            },
            is_unsafe: false,
        }),
    )
}
fn poly_application(text: &str, level: Level, alpha: Expr, value: Expr) -> Expr {
    apply(Expr::const_(name(text), vec![level]), [alpha, value])
}

#[test]
fn captured_support_wildcards_match_original_polymorphic_proof_applications() {
    use crate::grind_patterns::{CapturedPatterns, GrindPattern};
    let environment = crate::seed::bootstrap_nat_environment(budget()).unwrap();
    let environment = axiom(&environment, "P", Expr::sort(Level::zero()));
    let u = Level::param(name("u"));
    let function_type = arrow(Expr::sort(u.clone()), arrow(bv(0), bv(1)));
    let environment = poly_axiom(&environment, "leftTrigger", function_type.clone());
    let environment = poly_axiom(&environment, "rightTrigger", function_type);
    let environment = poly_axiom(
        &environment,
        "polyRule",
        arrow(Expr::sort(u.clone()), arrow(bv(0), constant("P"))),
    );
    let raw = vec![
        poly_application("leftTrigger", u.clone(), bv(1), bv(0)),
        poly_application("rightTrigger", u.clone(), bv(1), bv(0)),
    ];
    let row = GrindPattern {
        declaration: name("polyRule"),
        num_params: 2,
        data_params: 2,
        patterns: raw.clone(),
        captured: Some(CapturedPatterns {
            patterns: vec![
                raw[0].clone(),
                poly_application("rightTrigger", u, crate::grind_patterns::wildcard(), bv(0)),
            ],
            symbols: vec![name("leftTrigger"), name("rightTrigger")],
        }),
    };
    let mut context = Context::new(&environment, budget());
    let mut quantifiers = Quantifiers::default();
    context
        .grind_registered_pattern(&mut quantifiers, &row)
        .unwrap();
    let mut graph = Equalities::default();
    graph
        .intern(
            &mut context,
            &poly_application("leftTrigger", Level::one(), constant("Nat"), number(0)),
        )
        .unwrap();
    assert!(
        quantifiers
            .instantiate(&mut context, &graph)
            .unwrap()
            .is_empty()
    );
    graph
        .intern(
            &mut context,
            &poly_application("rightTrigger", Level::one(), constant("Nat"), number(0)),
        )
        .unwrap();
    let instances = quantifiers.instantiate(&mut context, &graph).unwrap();
    assert_eq!(instances.len(), 1);
    assert_eq!(
        instances[0].value,
        poly_application("polyRule", Level::one(), constant("Nat"), number(0)),
    );
    assert_eq!(instances[0].type_, constant("P"));
    let published = publish(
        &environment,
        Declaration::Thm(TheoremVal {
            base: ConstantVal {
                name: name("checked_poly_instance"),
                level_params: Vec::new(),
                type_: instances[0].type_.clone(),
            },
            value: instances[0].value.clone(),
            all: vec![name("checked_poly_instance")],
        }),
    );
    assert!(published.contains(&name("checked_poly_instance")));
    assert!(!published.contains(&name("[grind_dontcare]")));
}

#[test]
fn captured_ground_annotations_test_the_argument_instead_of_matching_metadata_as_a_constant() {
    use crate::grind_patterns::{CapturedPatterns, GrindPattern, mark_ground};
    let environment = crate::seed::bootstrap_nat_environment(budget()).unwrap();
    let environment = axiom(&environment, "P", Expr::sort(Level::zero()));
    let environment = axiom(&environment, "proof", constant("P"));
    let environment = axiom(
        &environment,
        "marker",
        arrow(constant("Nat"), Expr::sort(Level::zero())),
    );
    let environment = axiom(
        &environment,
        "combine",
        arrow(constant("Nat"), arrow(constant("Nat"), constant("Nat"))),
    );
    let row = GrindPattern {
        declaration: name("proof"),
        num_params: 0,
        data_params: 0,
        patterns: vec![Expr::app(constant("marker"), number(0))],
        captured: Some(CapturedPatterns {
            patterns: vec![Expr::app(constant("marker"), mark_ground(number(0)))],
            symbols: vec![name("marker")],
        }),
    };
    let mut context = Context::new(&environment, budget());
    let mut quantifiers = Quantifiers::default();
    context
        .grind_registered_pattern(&mut quantifiers, &row)
        .unwrap();
    let mut graph = Equalities::default();
    // Eighteen shared binary layers contain only dozens of unique nodes.
    // A tree walk of every graph node would exhaust the matcher budget before
    // even considering the independent ground trigger below.
    let mut shared = number(2);
    for _ in 0..18 {
        shared = apply(constant("combine"), [shared.clone(), shared]);
    }
    graph.intern(&mut context, &shared).unwrap();
    assert!(graph.nodes.len() < 64);
    graph
        .intern(&mut context, &Expr::app(constant("marker"), number(1)))
        .unwrap();
    assert!(
        quantifiers
            .instantiate(&mut context, &graph)
            .unwrap()
            .is_empty()
    );
    graph
        .intern(&mut context, &Expr::app(constant("marker"), number(0)))
        .unwrap();
    let instances = quantifiers.instantiate(&mut context, &graph).unwrap();
    assert_eq!(instances.len(), 1);
    assert_eq!(instances[0].value, constant("proof"));
    assert_eq!(instances[0].type_, constant("P"));
}
