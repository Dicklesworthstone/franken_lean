//! Result inference must not postpone a lift whose monads are already known.
use super::*;

#[test]
fn expected_action_element_is_inferred_by_the_registered_lift() {
    let (mut context, action, expected) = context(true);
    let ExprNode::App { f: target, .. } = expected.node() else {
        panic!("action type");
    };
    let element = context.hole(universe()).unwrap();
    let expected = Expr::app(target.clone(), element.clone());
    let result = context.coerce_expected(action, &expected).unwrap();
    assert!(
        has_lift(&result.value),
        "the action must actually be lifted"
    );
    assert_eq!(context.instantiate(&element).unwrap(), c("Nat"));
    assert!(context.coercion_eq(&result.type_, &expected).unwrap());
}

#[test]
fn an_implicit_action_domain_is_inferred_before_a_higher_order_call() {
    let source = "def lifted (m n : Type -> Type) [inst : MonadLiftT m n] (use : {A : Type} -> n A -> Nat) (x : m Nat) : Nat := use x";
    assert!(has_lift(&source_value(source)));
}

#[test]
fn same_monad_result_inference_does_not_insert_a_lift() {
    let (mut context, action, _) = context(true);
    let ExprNode::App { f: source, .. } = action.type_.node() else {
        panic!("action type");
    };
    let element = context.hole(universe()).unwrap();
    let expected = Expr::app(source.clone(), element.clone());
    let original = action.value.clone();
    let result = context.coerce_expected(action, &expected).unwrap();
    assert_eq!(result.value, original);
    assert!(!has_lift(&result.value));
    assert_eq!(context.instantiate(&element).unwrap(), c("Nat"));
}

#[test]
fn missing_or_disabled_lift_keeps_the_original_typing_obligation() {
    for disabled in [false, true] {
        let (mut context, action, expected) = context(disabled);
        if disabled {
            context
                .txn
                .options
                .insert(n("autoLift"), DataValue::OfBool(false));
        }
        let ExprNode::App { f: target, .. } = expected.node() else {
            panic!("action type");
        };
        let element = context.hole(universe()).unwrap();
        let expected = Expr::app(target.clone(), element.clone());
        let original = action.value.clone();
        let spent = context.txn.budget.heartbeats_consumed;
        let result = context.coerce_expected(action, &expected).unwrap();
        assert_eq!(result.value, original);
        assert!(!has_lift(&result.value));
        assert_eq!(context.instantiate(&element).unwrap(), element);
        assert!(
            !context.equations.is_empty(),
            "the mismatch must not disappear"
        );
        assert!(context.txn.budget.heartbeats_consumed > spent);
        assert!(
            context.instance_goals.is_empty(),
            "failed search must not leak a dictionary goal"
        );
    }
}

#[test]
fn source_without_a_lift_cannot_hide_the_mismatch_in_an_implicit_argument() {
    let env = environment();
    for source in [
        "def bad (m n : Type -> Type) (use : {A : Type} -> n A -> Nat) (x : m Nat) : Nat := use x",
        "def bad (m n : Type -> Type) [inst : MonadLiftT n m] (use : {A : Type} -> n A -> Nat) (x : m Nat) : Nat := use x",
    ] {
        if let Ok(checked) = crate::check_definition_source(source.as_bytes(), &env, budget()) {
            assert!(
                !matches!(checked.outcome, Outcome::Complete(Verdict::Accepted { .. })),
                "{source}"
            );
        }
    }
    // Failed declarations do not mutate the admitted fixture; recovery uses
    // the same environment, not a newly constructed instance registry.
    let valid = "def recovered (m n : Type -> Type) [inst : MonadLiftT m n] (use : {A : Type} -> n A -> Nat) (x : m Nat) : Nat := use x";
    let checked = crate::check_definition_source(valid.as_bytes(), &env, budget()).unwrap();
    assert!(matches!(
        checked.outcome,
        Outcome::Complete(Verdict::Accepted { .. })
    ));
}

#[test]
fn inference_exhaustion_preserves_state_instead_of_reporting_a_missing_lift() {
    let (mut context, action, expected) = context(true);
    let ExprNode::App { f: target, .. } = expected.node() else {
        panic!("action type");
    };
    let element = context.hole(universe()).unwrap();
    let expected = Expr::app(target.clone(), element);
    context.txn.budget.max_heartbeats = context.txn.budget.heartbeats_consumed + 5;
    let before = context.txn.clone();
    let next = context.next;
    assert!(matches!(
        context.coerce_expected(action, &expected),
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
