//! Recheck captured foreign patterns through ordinary declaration admission.
use super::*;
use crate::grind_patterns::CapturedPatterns;
use fln_core::expr::{Literal, NatLit};
use fln_core::outcome::Outcome;
use fln_env::constants::{AxiomVal, ConstantVal};
use fln_env::environment::{DeclarationBudget, DeclarationCommitted};
use fln_env::pmap::CollisionBudget;
use fln_kernel::capability::{Published, admit};
use fln_kernel::council::{Council, CouncilOutcome, convene};

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}
fn c(text: &str) -> Expr {
    Expr::const_(n(text), Vec::new())
}
fn b(index: u32) -> Expr {
    Expr::bvar(index).unwrap()
}
fn pi(label: &str, type_: Expr, body: Expr) -> Expr {
    Expr::forall_e(n(label), type_, body, BinderInfo::Default)
}
fn budget() -> Budget {
    Budget::for_stack_bytes(2 * 1024 * 1024)
}
fn axiom(env: &Environment, text: &str, levels: Vec<Name>, type_: Expr) -> Environment {
    let declaration = Declaration::Axiom(AxiomVal {
        base: ConstantVal {
            name: n(text),
            level_params: levels,
            type_,
        },
        is_unsafe: false,
    });
    let Outcome::Complete(admitted) = admit(env, declaration, budget()) else {
        panic!("fixture admission did not complete");
    };
    let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted) else {
        panic!("fixture declaration rejected");
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
fn fixture() -> Environment {
    let env = crate::seed::bootstrap_nat_environment(budget()).unwrap();
    let env = axiom(&env, "P", vec![], Expr::sort(Level::zero()));
    let u = Level::param(n("u"));
    let env = axiom(
        &env,
        "tag",
        vec![n("u")],
        pi("alpha", Expr::sort(u.clone()), pi("x", b(0), b(1))),
    );
    let env = axiom(
        &env,
        "rule",
        vec![n("u")],
        pi("alpha", Expr::sort(u), pi("x", b(0), c("P"))),
    );
    let env = axiom(&env, "groundRule", vec![], c("P"));
    axiom(&env, "value", vec![], c("Nat"))
}
fn pattern(level: Level, alpha: Expr, value: Expr) -> Expr {
    Expr::app(Expr::app(Expr::const_(n("tag"), vec![level]), alpha), value)
}

#[test]
fn repeated_support_variables_are_captured_once_and_reimported_without_fake_constants() {
    let env = fixture();
    let u = Level::param(n("u"));
    let raw = pattern(u.clone(), b(1), b(0));
    let mut context = Context::new(&env, budget());
    context.level_params = vec![n("u")];
    let captured = context
        .capture_grind_patterns(&[raw.clone(), raw.clone()])
        .unwrap();
    assert_eq!(
        captured,
        CapturedPatterns {
            patterns: vec![raw.clone(), pattern(u.clone(), registry::wildcard(), b(0)),],
            symbols: vec![n("tag")],
        }
    );
    let proof = Expr::const_(n("rule"), vec![u]);
    let imported = import_captured(
        &env,
        budget(),
        &n("rule"),
        &proof,
        2,
        &captured.patterns,
        &captured.symbols,
    )
    .unwrap();
    assert_eq!(imported.data_params, 2);
    assert_eq!(imported.patterns, [raw.clone(), raw]);
    assert_eq!(imported.captured, Some(captured));
    assert!(!env.contains(&n("[grind_dontcare]")));
    let registered = registry::register(&env, std::slice::from_ref(&imported)).unwrap();
    assert_eq!(registry::read(&registered).unwrap(), [imported]);
}

#[test]
fn ground_wrappers_and_symbol_order_come_from_registration_not_a_later_match() {
    let env = fixture();
    let raw = pattern(Level::one(), c("Nat"), c("value"));
    let mut context = Context::new(&env, budget());
    let captured = context
        .capture_grind_patterns(std::slice::from_ref(&raw))
        .unwrap();
    assert_eq!(
        captured.patterns,
        [pattern(
            Level::one(),
            registry::mark_ground(c("Nat")),
            registry::mark_ground(c("value")),
        )]
    );
    // Nat is a supporting type; value is an ordinary ground argument.
    assert_eq!(captured.symbols, [n("tag"), n("value")]);
    let imported = import_captured(
        &env,
        budget(),
        &n("groundRule"),
        &c("groundRule"),
        0,
        &captured.patterns,
        &captured.symbols,
    )
    .unwrap();
    assert_eq!(imported.patterns, [raw]);
    assert_eq!(imported.captured, Some(captured));

    let literal = pattern(
        Level::one(),
        c("Nat"),
        Expr::lit(Literal::Nat(NatLit::from_u64(7))),
    );
    let capture = context.capture_grind_patterns(&[literal]).unwrap();
    assert_eq!(capture.symbols, [n("tag")]);
    import_captured(
        &env,
        budget(),
        &n("groundRule"),
        &c("groundRule"),
        0,
        &capture.patterns,
        &capture.symbols,
    )
    .unwrap();
}

#[test]
fn forged_proof_counts_symbols_and_application_types_are_invalid_not_deferred() {
    let env = fixture();
    let u = Level::param(n("u"));
    let raw = pattern(u.clone(), b(1), b(0));
    let mut context = Context::new(&env, budget());
    let capture = context
        .capture_grind_patterns(std::slice::from_ref(&raw))
        .unwrap();
    let proof = Expr::const_(n("rule"), vec![u]);
    let malformed = registry_error(GrindPatternError::Malformed);
    assert_eq!(
        import_captured(
            &env,
            budget(),
            &n("rule"),
            &proof,
            1,
            &capture.patterns,
            &capture.symbols
        ),
        Err(malformed.clone()),
    );
    assert_eq!(
        import_captured(
            &env,
            budget(),
            &n("rule"),
            &c("groundRule"),
            2,
            &capture.patterns,
            &capture.symbols
        ),
        Err(malformed.clone()),
    );
    assert_eq!(
        import_captured(
            &env,
            budget(),
            &n("rule"),
            &Expr::const_(n("rule"), vec![Level::zero()]),
            2,
            &capture.patterns,
            &capture.symbols,
        ),
        Err(malformed.clone()),
    );
    assert_eq!(
        import_captured(
            &env,
            budget(),
            &n("rule"),
            &proof,
            2,
            &capture.patterns,
            &[n("tag"), n("Nat")]
        ),
        Err(malformed.clone()),
    );
    let overapplied = Expr::app(raw, b(0));
    assert_eq!(
        import_captured(
            &env,
            budget(),
            &n("rule"),
            &proof,
            2,
            &[overapplied],
            &[n("tag")]
        ),
        Err(malformed),
    );
    assert!(registry::read(&env).unwrap().is_empty());
}

#[test]
fn malformed_counts_cannot_hide_behind_unsupported_proof_telescope_shapes() {
    let env = fixture();
    let env = axiom(
        &env,
        "proofPredicate",
        vec![],
        pi("h", c("P"), Expr::sort(Level::zero())),
    );
    let env = axiom(
        &env,
        "dependentRule",
        vec![],
        pi("h", c("P"), Expr::app(c("proofPredicate"), b(0))),
    );
    for count in [0, 2] {
        assert_eq!(
            import_captured(
                &env,
                budget(),
                &n("dependentRule"),
                &c("dependentRule"),
                count,
                &[c("P")],
                &[n("P")],
            ),
            Err(registry_error(GrindPatternError::Malformed)),
        );
    }
    // The correctly described row is valid foreign metadata whose dependent
    // proof telescope is outside this native matching fragment.
    assert!(matches!(
        import_captured(
            &env,
            budget(),
            &n("dependentRule"),
            &c("dependentRule"),
            1,
            &[c("P")],
            &[n("P")],
        ),
        Err(NatDefinitionElabError::Inference(
            SourceInferenceError::GrindPattern(GrindPatternError::Unsupported(_),)
        )),
    ));
}
