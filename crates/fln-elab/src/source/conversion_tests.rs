//! Inference may retry conversion, never suppress a cycle or broaden selection.
use super::*;
use fln_env::constants::ConstantInfo;

fn context() -> Context {
    let environment = crate::seed::bootstrap_nat_environment(Budget::DEFAULT).unwrap();
    let type_ = Expr::sort(Level::one());
    let identity = DefinitionVal {
        base: ConstantVal {
            name: Name::from_components(["Identity"]),
            level_params: Vec::new(),
            type_: Expr::forall_e(
                Name::anonymous(),
                type_.clone(),
                type_.clone(),
                BinderInfo::Default,
            ),
        },
        value: Expr::lam(
            Name::anonymous(),
            type_,
            Expr::bvar(0).unwrap(),
            BinderInfo::Default,
        ),
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Safe,
        all: Vec::new(),
    };
    let environment = environment.add_decl(ConstantInfo::Defn(identity)).unwrap();
    Context::new(&environment, Budget::DEFAULT)
}
fn unknown(context: &mut Context) -> Expr {
    context.hole(Expr::sort(Level::one())).unwrap()
}
fn identity(value: Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_components(["Identity"]), Vec::new()),
        value,
    )
}

#[test]
fn reducible_self_occurrences_are_conversion_not_recursive_assignments() {
    let mut context = context();
    let hole = unknown(&mut context);
    let before = context.txn.budget.heartbeats_consumed;
    context
        .unify_source_batch(&[(hole.clone(), identity(hole.clone()))], true)
        .unwrap();
    assert!(context.txn.mvars.assignments().is_empty());
    assert_eq!(context.instantiate(&hole).unwrap(), hole);
    assert!(context.txn.budget.heartbeats_consumed > before);
}

#[test]
fn failed_first_attempt_rolls_back_before_replaying_the_entire_batch() {
    let mut context = context();
    let first = unknown(&mut context);
    let second = unknown(&mut context);
    let pairs = [
        (first.clone(), nat_const()),
        (second.clone(), identity(second.clone())),
    ];
    assert!(matches!(
        context.unify_source_batch(&pairs, false),
        Err(UnificationError::Metavariable(
            MetavarError::OccursCheckFailed { .. }
        ))
    ));
    assert!(context.txn.mvars.assignments().is_empty());
    let spent = context.txn.budget.heartbeats_consumed;
    context.unify_source_batch(&pairs, true).unwrap();
    assert_eq!(context.instantiate(&first).unwrap(), nat_const());
    assert_eq!(context.instantiate(&second).unwrap(), second);
    assert_eq!(context.txn.mvars.assignments().len(), 1);
    assert!(context.txn.budget.heartbeats_consumed > spent);
}

#[test]
fn genuine_infinite_types_still_fail_atomically_and_fresh_equations_recover() {
    let mut context = context();
    let first = unknown(&mut context);
    let second = unknown(&mut context);
    let cycle = identity(Expr::forall_e(
        Name::anonymous(),
        nat_const(),
        second.clone(),
        BinderInfo::Default,
    ));
    assert!(matches!(
        context.unify_source_batch(
            &[(first.clone(), nat_const()), (second.clone(), cycle)],
            true
        ),
        Err(UnificationError::Metavariable(
            MetavarError::OccursCheckFailed { .. }
        ))
    ));
    assert!(context.txn.mvars.assignments().is_empty());
    context
        .unify_source_batch(
            &[(first.clone(), nat_const()), (second.clone(), nat_const())],
            true,
        )
        .unwrap();
    assert_eq!(context.instantiate(&first).unwrap(), nat_const());
    assert_eq!(context.instantiate(&second).unwrap(), nat_const());
}

#[test]
fn successful_narrow_assignments_keep_alias_syntax_for_later_instance_selection() {
    let mut context = context();
    let hole = unknown(&mut context);
    let named = identity(nat_const());
    context
        .unify_source_batch(&[(hole.clone(), named.clone())], true)
        .unwrap();
    assert_eq!(context.instantiate(&hole).unwrap(), named);
}

#[test]
fn resource_exhaustion_does_not_become_a_conversion_retry_or_assignment() {
    let mut context = context();
    let hole = unknown(&mut context);
    context.txn.budget.max_heartbeats = context.txn.budget.heartbeats_consumed + 1;
    assert!(matches!(
        context.unify_source_batch(&[(hole.clone(), identity(hole))], true),
        Err(UnificationError::HeartbeatLimit)
    ));
    assert!(context.txn.mvars.assignments().is_empty());
}
