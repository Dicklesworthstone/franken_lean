//! Reducer invariants independent of parser elision and source pretty-printing.
use super::*;

fn context() -> Context {
    let budget = Budget::for_stack_bytes(2 * 1024 * 1024);
    let env = crate::seed::bootstrap_nat_environment(budget).unwrap();
    Context::new(&env, budget)
}
fn local(context: &mut Context, text: &str, type_: Expr) -> Expr {
    let name = Name::from_components([text]);
    let id = FVarId(name.clone());
    context.txn.lctx.add_param(id.clone(), name, type_, BinderInfo::Default);
    Expr::fvar(id)
}
fn lambda(type_: Expr, body: Expr) -> Expr {
    Expr::lam(Name::from_components(["x"]), type_, body, BinderInfo::Default)
}

#[test]
fn beta_zeta_revisits_exposed_redexes() {
    let mut ctx = context();
    let x = local(&mut ctx, "n", nat_const());
    let identity = lambda(nat_const(), Expr::bvar(0).unwrap());
    let body = Expr::app(identity.clone(), Expr::bvar(0).unwrap());
    let redex = Expr::let_e(Name::anonymous(), nat_const(), x.clone(), body, false);
    assert_ne!(redex, x);
    assert_eq!(ctx.dsimp_expression(&redex, &Rules::default()).unwrap(), x);
}

#[test]
fn dependent_binders_keep_original_names_and_no_fresh_locals_escape() {
    let mut ctx = context();
    let type_ = Expr::sort(Level::one());
    let body = Expr::app(lambda(type_.clone(), Expr::bvar(0).unwrap()), Expr::bvar(0).unwrap());
    let expression = lambda(type_.clone(), body);
    let expected = lambda(type_, Expr::bvar(0).unwrap());
    let lctx = ctx.txn.lctx.clone();
    let result = ctx.dsimp_expression(&expression, &Rules::default()).unwrap();
    assert_eq!(result, expected);
    assert!(!result.has_fvar());
    assert!(!result.has_loose_bvars());
    assert_eq!(ctx.txn.lctx, lctx);
}

#[test]
fn proofs_are_not_beta_reduced_even_inside_data_expressions() {
    let mut ctx = context();
    let p = local(&mut ctx, "P", Expr::sort(Level::zero()));
    let h = local(&mut ctx, "h", p.clone());
    let redex = Expr::app(lambda(p.clone(), Expr::bvar(0).unwrap()), h);
    let f = local(&mut ctx, "f", Expr::forall_e(Name::anonymous(), p, nat_const(), BinderInfo::Default));
    let expression = Expr::app(f, redex);
    assert_eq!(ctx.dsimp_expression(&expression, &Rules::default()).unwrap(), expression);
}

#[test]
fn local_unfolding_is_selected_by_identity_not_name() {
    let mut ctx = context();
    let old = FVarId(Name::from_components(["old"]));
    let new = FVarId(Name::from_components(["new"]));
    let name = Name::from_components(["value"]);
    let value = Expr::lit(Literal::Nat(fln_core::expr::NatLit::from_u64(3)));
    ctx.txn.lctx.add_let(old.clone(), name.clone(), nat_const(), value.clone());
    ctx.txn.lctx.add_let(new.clone(), name, nat_const(), Expr::fvar(old.clone()));
    let mut rules = Rules::default();
    rules.lets.insert(old.clone(), value.clone());
    assert_eq!(ctx.dsimp_expression(&Expr::fvar(old), &rules).unwrap(), value);
    assert_eq!(ctx.dsimp_expression(&Expr::fvar(new.clone()), &rules).unwrap(), Expr::fvar(new));
}

#[test]
fn shared_data_dags_retain_shared_results() {
    let mut ctx = context();
    let nat = nat_const();
    let f_type = Expr::forall_e(Name::anonymous(), nat.clone(),
        Expr::forall_e(Name::anonymous(), nat.clone(), nat.clone(), BinderInfo::Default), BinderInfo::Default);
    let f = local(&mut ctx, "f", f_type);
    let n = local(&mut ctx, "n", nat.clone());
    let mut expr = Expr::app(lambda(nat, Expr::bvar(0).unwrap()), n);
    for _ in 0..16 { expr = app(f.clone(), [expr.clone(), expr]); }
    let mut result = ctx.dsimp_expression(&expr, &Rules::default()).unwrap();
    for _ in 0..16 {
        let ExprNode::App { f, a: right } = result.node() else { panic!("binary data application"); };
        let ExprNode::App { a: left, .. } = f.node() else { panic!("left argument"); };
        assert_eq!(left.allocation_identity(), right.allocation_identity());
        result = left.clone();
    }
}

#[test]
fn every_binder_interruption_restores_state_but_charges_work() {
    let mut original = context();
    let type_ = Expr::sort(Level::one());
    let inner = Expr::app(lambda(type_.clone(), Expr::bvar(0).unwrap()), Expr::bvar(0).unwrap());
    let expression = lambda(type_, inner);
    original.hole(nat_const()).unwrap();
    let start = original.txn.budget.heartbeats_consumed;
    let mut complete = original.clone();
    complete.dsimp_expression(&expression, &Rules::default()).unwrap();
    let used = complete.txn.budget.heartbeats_consumed - start;
    assert!(used > 0);
    for allowance in 0..used {
        let mut limited = original.clone();
        limited.txn.budget.max_heartbeats = start + allowance;
        let problem = limited.dsimp_expression(&expression, &Rules::default()).unwrap_err();
        assert!(!backtrack::recoverable(&problem), "{allowance}: {problem:?}");
        assert!(limited.txn.budget.heartbeats_consumed >= start + allowance);
        limited.txn.budget = original.txn.budget.clone();
        assert_eq!(limited.txn, original.txn, "{allowance}");
        assert_eq!(limited.next, original.next, "{allowance}");
    }
}
