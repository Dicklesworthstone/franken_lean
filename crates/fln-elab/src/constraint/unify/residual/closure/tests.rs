//! Structural and bounded-work contracts for checked telescope closure.
use super::*;
use fln_core::expr::BinderInfo;
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::options::{DataValue, KVMap};
use std::cell::Cell;

fn name(value: &str) -> Name {
    Name::from_components([value])
}

fn nat() -> Expr {
    Expr::const_(name("Nat"), Vec::new())
}

fn bvar(index: u32) -> Expr {
    Expr::bvar(index).unwrap()
}

fn meter(cancelled: &dyn Fn() -> bool) -> Meter<'_> {
    Meter {
        steps: 0,
        nodes: 0,
        max_steps: 100_000,
        max_nodes: 100_000,
        heartbeat_bound: false,
        cancelled,
    }
}

// The previous checked construction is an independent structural oracle.
// Keep its repeated abstraction here only for these small equivalence cases.
fn sequential(mut value: Expr, mut type_: Expr, telescope: &LocalContext) -> (Expr, Expr) {
    for local in telescope.decls().iter().rev() {
        value = value.abstract_fvar(&local.id, 0).unwrap();
        type_ = type_.abstract_fvar(&local.id, 0).unwrap();
        if let Some(local_value) = &local.value {
            value = Expr::let_e(
                local.user_name.clone(),
                local.type_.clone(),
                local_value.clone(),
                value,
                false,
            );
            type_ = Expr::let_e(
                local.user_name.clone(),
                local.type_.clone(),
                local_value.clone(),
                type_,
                false,
            );
        } else {
            value = Expr::lam(
                local.user_name.clone(),
                local.type_.clone(),
                value,
                local.binder_info,
            );
            type_ = Expr::forall_e(
                local.user_name.clone(),
                local.type_.clone(),
                type_,
                local.binder_info,
            );
        }
    }
    (value, type_)
}

fn compare(value: Expr, type_: Expr, telescope: &LocalContext) -> (Expr, Expr) {
    let expected = sequential(value.clone(), type_.clone(), telescope);
    let before = telescope.clone();
    let actual = close(value, type_, telescope, &mut meter(&|| false)).unwrap();
    assert_eq!(actual, expected);
    assert_eq!(telescope, &before);
    actual
}

#[test]
fn dependent_domains_and_let_values_match_the_original_checked_telescope() {
    let mut telescope = LocalContext::new();
    let a = FVarId(name("type"));
    let x = FVarId(name("value"));
    let alias = FVarId(name("alias"));
    let y = FVarId(name("copied"));
    telescope.add_param(
        a.clone(),
        name("same"),
        Expr::sort(Level::one()),
        BinderInfo::Implicit,
    );
    telescope.add_param(
        x.clone(),
        name("same"),
        Expr::fvar(a.clone()),
        BinderInfo::StrictImplicit,
    );
    telescope.add_let(
        alias.clone(),
        name("same"),
        Expr::sort(Level::one()),
        Expr::fvar(a),
    );
    telescope.add_let(
        y.clone(),
        name("same"),
        Expr::fvar(alias.clone()),
        Expr::fvar(x.clone()),
    );
    let value = Expr::lam(
        name("same"),
        Expr::fvar(alias.clone()),
        Expr::fvar(x),
        BinderInfo::InstImplicit,
    );
    let type_ = Expr::forall_e(
        name("same"),
        Expr::fvar(alias.clone()),
        Expr::fvar(alias.clone()),
        BinderInfo::InstImplicit,
    );
    let result = compare(value, type_, &telescope);
    assert!(!result.0.has_fvar() && !result.1.has_fvar());
    assert!(!result.0.has_loose_bvars() && !result.1.has_loose_bvars());
    compare(Expr::fvar(y), Expr::fvar(alias), &telescope);
}

#[test]
fn shared_nodes_at_different_depths_preserve_all_expression_fields() {
    let mut telescope = LocalContext::new();
    let x = FVarId(name("x"));
    let y = FVarId(name("y"));
    telescope.add_param(x.clone(), name("same"), nat(), BinderInfo::StrictImplicit);
    telescope.add_param(y.clone(), name("same"), nat(), BinderInfo::InstImplicit);
    let shared = Expr::app(Expr::fvar(x.clone()), Expr::fvar(y));
    let mut metadata = KVMap::new();
    metadata.insert(name("closure_marker"), DataValue::OfNat(23));
    for non_dep in [false, true] {
        let decorated = Expr::mdata(
            metadata.clone(),
            Expr::proj(name("Payload"), 2, shared.clone()),
        );
        let inner = Expr::let_e(
            name("same"),
            Expr::fvar(x.clone()),
            shared.clone(),
            Expr::app(bvar(0), decorated),
            non_dep,
        );
        let value = Expr::app(
            shared.clone(),
            Expr::lam(name("same"), nat(), inner, BinderInfo::Implicit),
        );
        let type_ = Expr::forall_e(
            name("same"),
            nat(),
            shared.clone(),
            BinderInfo::InstImplicit,
        );
        let result = compare(value, type_, &telescope);
        assert!(!result.0.has_fvar() && !result.1.has_fvar());
        assert!(!result.0.has_loose_bvars() && !result.1.has_loose_bvars());
    }
}

#[test]
fn self_future_and_external_local_references_remain_free_for_validation_to_reject() {
    for target in ["first", "later", "external"] {
        let mut telescope = LocalContext::new();
        let first = FVarId(name("first"));
        let later = FVarId(name("later"));
        telescope.add_param(
            first.clone(),
            name("first"),
            Expr::fvar(FVarId(name(target))),
            BinderInfo::Default,
        );
        telescope.add_param(later.clone(), name("later"), nat(), BinderInfo::Default);
        let result = compare(Expr::fvar(first), Expr::fvar(later), &telescope);
        assert!(result.0.has_fvar() && result.1.has_fvar());
    }
}

#[test]
fn duplicate_local_identities_are_rejected_before_closure() {
    let mut telescope = LocalContext::new();
    let id = FVarId(name("duplicate"));
    telescope.add_param(id.clone(), name("first"), nat(), BinderInfo::Default);
    telescope.add_param(id, name("second"), nat(), BinderInfo::Default);
    assert!(matches!(
        close(nat(), nat(), &telescope, &mut meter(&|| false)),
        Err(UnificationError::Deferred(
            UnificationDeferred::InvalidLocalContext
        )),
    ));
}

#[test]
fn a_large_telescope_closes_with_linear_work_and_obeys_cancellation() {
    const LOCALS: u32 = 256;
    let mut telescope = LocalContext::new();
    for index in 0..LOCALS {
        telescope.add_param(
            FVarId(Name::num(name("local"), u64::from(index))),
            name("same"),
            nat(),
            BinderInfo::Default,
        );
    }
    let value = Expr::fvar(FVarId(Name::num(name("local"), 0)));
    let before = telescope.clone();
    let calls = Cell::new(0_u64);
    let never = || {
        calls.set(calls.get() + 1);
        false
    };
    let mut bounded = meter(&never);
    bounded.max_steps = 2_048;
    bounded.max_nodes = 1_024;
    let actual = close(value.clone(), nat(), &telescope, &mut bounded).unwrap();
    let mut expected_value = bvar(LOCALS - 1);
    let mut expected_type = nat();
    for _ in 0..LOCALS {
        expected_value = Expr::lam(name("same"), nat(), expected_value, BinderInfo::Default);
        expected_type = Expr::forall_e(name("same"), nat(), expected_type, BinderInfo::Default);
    }
    assert_eq!(actual, (expected_value, expected_type));
    assert!(bounded.steps <= 2_048 && bounded.nodes <= 1_024);
    for cut in [0, calls.get() / 2, calls.get() - 1] {
        let polls = Cell::new(0);
        let cancelled = || {
            let current = polls.get();
            polls.set(current + 1);
            current >= cut
        };
        assert!(matches!(
            close(value.clone(), nat(), &telescope, &mut meter(&cancelled)),
            Err(UnificationError::Cancelled),
        ));
        assert_eq!(telescope, before);
    }
    let not_cancelled = || false;
    let mut limited = meter(&not_cancelled);
    limited.max_nodes = 32;
    assert!(matches!(
        close(value, nat(), &telescope, &mut limited),
        Err(UnificationError::NodeLimit { limit: 32 }),
    ));
    assert!(limited.steps > 0);
    assert_eq!(telescope, before);
}
