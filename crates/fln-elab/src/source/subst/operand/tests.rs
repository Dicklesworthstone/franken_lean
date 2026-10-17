use super::*;
use fln_env::environment::DeclarationBudget;
use fln_env::pmap::CollisionBudget;
use fln_kernel::capability::{Published, admit};
use fln_kernel::council::{Council, CouncilOutcome, convene};
use fln_syntax::source::{ByteSpan, SourceInfo};

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn local(context: &mut Context, text: &str, type_: Expr) -> Expr {
    let id = FVarId(name(text));
    context
        .txn
        .lctx
        .add_param(id.clone(), name(text), type_, BinderInfo::Default);
    Expr::fvar(id)
}

fn syntax() -> Syntax {
    Syntax::Ident {
        info: SourceInfo::None,
        raw_val: ByteSpan::default(),
        val: name("hp"),
        preresolved: Vec::new(),
    }
}

fn setup(unrelated: bool) -> (Context, Equality, Expr, Expr) {
    setup_with_equality(unrelated, true)
}

fn setup_with_equality(unrelated: bool, include_equality: bool) -> (Context, Equality, Expr, Expr) {
    let budget = Budget::for_stack_bytes(2 * 1024 * 1024);
    let mut env = crate::seed::bootstrap_nat_environment(budget).unwrap();
    if include_equality {
        // The Nat-only fixture does not contain Eq, its constructor, or its
        // recursor. Admit the ordinary indexed family rather than testing casts
        // against dangling types or introducing unchecked equality constants.
        let Outcome::Complete(admitted) = admit(&env, crate::seed::eq_seed_declaration(), budget)
        else {
            panic!("Eq seed admission did not complete");
        };
        let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted)
        else {
            panic!("Eq seed was rejected");
        };
        let Outcome::Complete(Published::BlockCommitted(publication)) = checked.publish(
            DeclarationBudget::default(),
            CollisionBudget::default(),
            None,
        ) else {
            panic!("Eq seed publication did not complete");
        };
        env = publication.environment;
        for constant in ["Eq", "Eq.refl", "Eq.rec"] {
            assert!(env.contains(&name(constant)));
        }
    }
    let mut context = Context::new(&env, budget);
    let family_type = Expr::forall_e(
        name("n"),
        nat_const(),
        Expr::sort(Level::zero()),
        BinderInfo::Default,
    );
    let p = local(&mut context, "P", family_type.clone());
    let q = local(&mut context, "Q", family_type);
    let lhs = local(&mut context, "a", nat_const());
    let rhs = local(&mut context, "b", nat_const());
    let equality = Equality {
        level: Level::one(),
        alpha: nat_const(),
        lhs,
        rhs,
    };
    let proof_type = eq(
        &equality.level,
        &equality.alpha,
        equality.lhs.clone(),
        equality.rhs.clone(),
    );
    let proof = local(&mut context, "h", proof_type);
    let operand_type = Expr::app(if unrelated { q } else { p.clone() }, equality.rhs.clone());
    local(&mut context, "hp", operand_type);
    let expected = Expr::app(p, equality.lhs.clone());
    (context, equality, proof, expected)
}

#[test]
fn reverse_cast_is_an_ordinary_equality_recursor() {
    let (mut context, equality, proof, expected) = setup(false);
    let term = context
        .substitution_operand(&syntax(), &expected, &equality, &proof)
        .unwrap();
    assert_eq!(term.type_, expected);
    let (head, arguments) = operators::spine(&term.value);
    assert!(matches!(head.node(), ExprNode::Const { name: n, .. } if *n == name("Eq.rec")));
    assert_eq!(arguments.len(), 6);
    assert_eq!(arguments[1], equality.rhs);
    assert_eq!(arguments[4], equality.lhs);
    let (head, arguments) = operators::spine(&arguments[5]);
    assert!(matches!(head.node(), ExprNode::Const { name: n, .. } if *n == name("Eq.rec")));
    assert_eq!(arguments.len(), 6);
    assert_eq!(arguments[1], equality.lhs);
    assert_eq!(arguments[4], equality.rhs);
    assert_eq!(arguments.last(), Some(&proof));
    assert!(!context.txn.env.contains(&name("Eq.symm")));
    let reconstructed = context.known_type(&term.value).unwrap().unwrap();
    assert!(context.coercion_eq(&reconstructed, &expected).unwrap());
}

#[test]
fn failed_retry_preserves_the_callers_transaction_and_charges_work() {
    let (mut context, equality, proof, expected) = setup(true);
    let unassigned = context.hole(nat_const()).unwrap();
    let before = context.clone();
    assert!(
        context
            .substitution_operand(&syntax(), &expected, &equality, &proof)
            .is_err()
    );
    assert_eq!(context.instantiate(&unassigned).unwrap(), unassigned);
    assert_eq!(context.next, before.next);
    assert_eq!(context.equations.len(), before.equations.len());
    assert_eq!(context.instance_goals, before.instance_goals);
    assert_eq!(
        context.txn.lctx.decls().len(),
        before.txn.lctx.decls().len()
    );
    assert_eq!(
        context.txn.mvars.assignments(),
        before.txn.mvars.assignments()
    );
    assert!(context.txn.budget.heartbeats_consumed > before.txn.budget.heartbeats_consumed);
}

#[test]
fn exhausted_attempt_does_not_restart_with_a_fresh_budget() {
    let (mut context, equality, proof, expected) = setup(false);
    // Zero means unlimited, not exhausted. First spend real work and then
    // cap the budget at that positive amount so the next attempt must stop.
    context.tick().unwrap();
    assert!(context.txn.budget.heartbeats_consumed > 0);
    context.txn.budget.max_heartbeats = context.txn.budget.heartbeats_consumed;
    let result = context.substitution_operand(&syntax(), &expected, &equality, &proof);
    assert!(matches!(
        result,
        Err(NatDefinitionElabError::Inference(
            SourceInferenceError::ResourceLimit
        ))
    ));
    assert!(context.txn.mvars.assignments().is_empty());
}

#[test]
fn inspection_and_inconclusive_failures_are_not_type_mismatches() {
    for error in [
        SourceInferenceError::ResourceLimit,
        SourceInferenceError::ObservationComplete,
        SourceInferenceError::UnknownConstant(name("missing")),
        SourceInferenceError::Unification(Box::new(UnificationError::Deferred(
            UnificationDeferred::UnsupportedEquation,
        ))),
    ] {
        assert!(!definite_mismatch(&failure(error)));
    }
    assert!(definite_mismatch(&failure(
        SourceInferenceError::TypeMismatch {
            actual: "P b".into(),
            expected: "P a".into(),
        }
    )));
    assert!(observation_complete(&failure(
        SourceInferenceError::ObservationComplete
    )));
}

#[test]
fn tactic_attempts_retry_only_after_an_independent_closed_refutation() {
    let (mut context, equality, proof, expected) = setup(false);
    context.attempt_depth = 1;
    let direct = context.clone().term(&syntax(), Some(expected.clone()));
    assert!(matches!(direct, Err(ref error) if attempt_deferral(error)));
    let term = context
        .substitution_operand(&syntax(), &expected, &equality, &proof)
        .unwrap();
    assert_eq!(term.type_, expected);
    let actual = context.known_type(&term.value).unwrap().unwrap();
    assert!(context.coercion_eq(&actual, &expected).unwrap());
}

#[test]
fn tactic_retry_still_refuses_unrelated_types_without_publishing_assignments() {
    let (mut context, equality, proof, expected) = setup(true);
    context.attempt_depth = 1;
    let before = context.clone();
    let result = context.substitution_operand(&syntax(), &expected, &equality, &proof);
    assert!(matches!(result, Err(ref error) if attempt_deferral(error)));
    assert_eq!(context.next, before.next);
    assert_eq!(
        context.txn.mvars.assignments(),
        before.txn.mvars.assignments()
    );
    assert_eq!(context.equations.len(), before.equations.len());
    assert!(context.txn.budget.heartbeats_consumed > before.txn.budget.heartbeats_consumed);
    for reason in [
        UnificationDeferred::InvalidLocalContext,
        UnificationDeferred::UnknownMetavariable(fln_core::expr::MVarId(name("unknown"))),
    ] {
        assert!(!attempt_deferral(&failure(
            SourceInferenceError::Unification(Box::new(UnificationError::Deferred(reason),))
        )));
    }
}

#[test]
fn absent_equality_family_remains_a_typed_refusal() {
    let (mut context, equality, proof, expected) = setup_with_equality(false, false);
    let before = context.txn.env.clone();
    assert!(!before.contains(&name("Eq")));
    let result = context.substitution_operand(&syntax(), &expected, &equality, &proof);
    assert!(matches!(
        result,
        Err(NatDefinitionElabError::Inference(
            SourceInferenceError::ExpectedType
        ))
    ));
    assert_eq!(context.txn.env, before);
    assert!(context.txn.mvars.assignments().is_empty());
}

#[test]
fn zero_heartbeat_limit_is_unlimited_not_an_exhaustion_fixture() {
    let (mut context, equality, proof, expected) = setup(false);
    context.txn.budget.max_heartbeats = 0;
    let before = context.txn.budget.heartbeats_consumed;
    let term = context
        .substitution_operand(&syntax(), &expected, &equality, &proof)
        .unwrap();
    assert_eq!(term.type_, expected);
    assert!(context.txn.budget.heartbeats_consumed > before);
}
