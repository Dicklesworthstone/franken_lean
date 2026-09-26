//! Resolution-only controls for generated anonymous local-context slots.
use super::*;

fn context() -> Context {
    let mut context = Context::new(&Environment::new(), Budget::DEFAULT);
    context.txn.lctx.add_param(
        FVarId(Name::from_components(["internal"])),
        Name::anonymous(),
        nat_const(),
        BinderInfo::Default,
    );
    context
}

#[test]
fn empty_prefixes_never_select_an_internal_anonymous_receiver() {
    for parts in [
        vec!["true"],
        vec!["false"],
        vec!["missing"],
        vec!["unknown", "value"],
    ] {
        let mut context = context();
        let before = context.txn.lctx.clone();
        assert!(
            context
                .qualified_field_receiver(&Name::from_components(parts))
                .unwrap()
                .is_none()
        );
        assert_eq!(context.txn.lctx, before);
    }
}

#[test]
fn a_nonempty_named_prefix_resolves_but_an_escaped_dot_does_not_split() {
    let mut context = context();
    let id = FVarId(Name::from_components(["named"]));
    context.txn.lctx.add_param(
        id.clone(),
        Name::from_components(["box"]),
        nat_const(),
        BinderInfo::Default,
    );
    let (receiver, path) = context
        .qualified_field_receiver(&Name::from_components(["box", "value"]))
        .unwrap()
        .expect("an actual receiver prefix");
    assert_eq!(receiver.value, Expr::fvar(id));
    assert_eq!(path, Name::from_components(["value"]));
    assert!(
        context
            .qualified_field_receiver(&Name::from_components(["box.value"]))
            .unwrap()
            .is_none()
    );
}

#[test]
fn exact_local_names_keep_precedence_and_resolution_remains_budgeted() {
    let mut context = context();
    let name = Name::from_components(["box", "value"]);
    context.txn.lctx.add_param(
        FVarId(Name::from_components(["exact"])),
        name.clone(),
        nat_const(),
        BinderInfo::Default,
    );
    assert!(context.qualified_field_receiver(&name).unwrap().is_none());
    context.txn.budget.max_heartbeats = 1;
    context.txn.budget.heartbeats_consumed = 1;
    assert!(
        context
            .qualified_field_receiver(&Name::from_components(["missing"]))
            .is_err()
    );
}
