//! Pure reducer and transaction-boundary regressions. Source-level admission
//! tests live in fln/tests/source_dsimp.rs; these tests do not claim admission.
use super::*;
use fln_syntax::source::SourceInfo;

fn context() -> Context {
    Context::new(
        &Environment::new(),
        Budget::for_stack_bytes(2 * 1024 * 1024),
    )
}
fn local(ctx: &mut Context, name: &str, type_: Expr) -> Expr {
    let name = Name::from_components([name]);
    let id = FVarId(name.clone());
    ctx.txn
        .lctx
        .add_param(id.clone(), name, type_, BinderInfo::Default);
    Expr::fvar(id)
}
fn arrow(domain: Expr, body: Expr) -> Expr {
    Expr::forall_e(Name::anonymous(), domain, body, BinderInfo::Default)
}
fn identity(domain: Expr) -> Expr {
    Expr::lam(
        Name::from_components(["x"]),
        domain,
        Expr::bvar(0).unwrap(),
        BinderInfo::Default,
    )
}
fn empty() -> DsimpSet<'static> {
    DsimpSet {
        definitions: Vec::new(),
        ..DsimpSet::default()
    }
}
fn arguments() -> Vec<Syntax> {
    let null = || Syntax::node(Name::from_components(["null"]), Vec::new());
    vec![
        Syntax::atom(SourceInfo::None, "dsimp"),
        Syntax::node(parser_kind(&["Tactic", "optConfig"]), vec![null()]),
        null(),
        Syntax::node(
            Name::from_components(["null"]),
            vec![Syntax::atom(SourceInfo::None, "only")],
        ),
        null(),
        null(),
    ]
}
fn proof(ctx: &Context, goal: &ProofGoal, siblings: Vec<Work<'static>>) -> ProofState<'static> {
    ProofState {
        extent: None,
        saved: ctx.txn.lctx.clone(),
        target: goal.target.clone(),
        root: Expr::mvar(goal.id.clone()),
        instructions: Vec::new(),
        cursor: 0,
        work: siblings,
        controls: Vec::new(),
    }
}

#[test]
fn beta_zeta_beneath_a_dependent_binder_preserves_scope_and_names() {
    let mut ctx = context();
    let a = local(&mut ctx, "A", Expr::sort(Level::one()));
    let p = local(&mut ctx, "P", arrow(a.clone(), Expr::sort(Level::zero())));
    let value = Expr::app(identity(a.clone()), Expr::bvar(0).unwrap());
    let body = Expr::let_e(
        Name::anonymous(),
        a.clone(),
        value,
        Expr::app(p.clone(), Expr::bvar(0).unwrap()),
        false,
    );
    let target = Expr::forall_e(
        Name::from_components(["P"]),
        a.clone(),
        body,
        BinderInfo::Default,
    );
    let expected = Expr::forall_e(
        Name::from_components(["P"]),
        a,
        Expr::app(p, Expr::bvar(0).unwrap()),
        BinderInfo::Default,
    );
    let saved = ctx.txn.lctx.clone();
    let reduced = ctx.dsimp_expression(&target, &empty()).unwrap();
    assert_eq!(reduced, expected);
    assert!(!reduced.has_loose_bvars());
    assert_eq!(ctx.txn.lctx, saved);
}

#[test]
fn shared_dags_are_not_expanded_into_trees() {
    let mut ctx = context();
    let a = local(&mut ctx, "A", Expr::sort(Level::one()));
    let x = local(&mut ctx, "x", a.clone());
    let f = local(&mut ctx, "f", arrow(a.clone(), arrow(a.clone(), a)));
    // Use a well-scoped value of A as the shared leaf, rather than a fabricated
    // declaration; all reduction is beta substitution inside the local context.
    let domain = ctx
        .txn
        .lctx
        .find_by_user_name(&Name::from_components(["x"]))
        .unwrap()
        .type_
        .clone();
    let mut target = Expr::app(identity(domain), x.clone());
    for _ in 0..24 {
        target = app(f.clone(), [target.clone(), target]);
    }
    let mut reduced = ctx.dsimp_expression(&target, &empty()).unwrap();
    for _ in 0..24 {
        let (_, children) = ctx.dsimp_spine(&reduced).unwrap();
        assert_eq!(children.len(), 2);
        assert_eq!(
            children[0].allocation_identity(),
            children[1].allocation_identity()
        );
        reduced = children[0].clone();
    }
    assert_eq!(reduced, x);
}

#[test]
fn proof_arguments_are_not_rewritten_even_when_their_beta_redex_is_visible() {
    let mut ctx = context();
    let p = local(&mut ctx, "P", Expr::sort(Level::zero()));
    let h = local(&mut ctx, "h", p.clone());
    let f = local(&mut ctx, "F", arrow(p.clone(), Expr::sort(Level::one())));
    let evidence = Expr::app(identity(p), h);
    let target = Expr::app(f, evidence);
    assert_eq!(ctx.dsimp_expression(&target, &empty()).unwrap(), target);
}

#[test]
fn selected_local_values_do_not_override_the_instance_argument_boundary() {
    let mut ctx = context();
    let a = local(&mut ctx, "A", Expr::sort(Level::one()));
    let x = local(&mut ctx, "x", a.clone());
    let id = FVarId(Name::from_components(["dictionary"]));
    let decl = LocalDecl {
        id: id.clone(),
        user_name: id.0.clone(),
        type_: a.clone(),
        value: Some(x.clone()),
        binder_info: BinderInfo::Default,
        index: ctx.txn.lctx.len(),
    };
    eliminate::add_local(&mut ctx.txn.lctx, &decl);
    let f = local(
        &mut ctx,
        "f",
        Expr::forall_e(Name::anonymous(), a.clone(), a, BinderInfo::InstImplicit),
    );
    let selected = Expr::fvar(id.clone());
    let target = Expr::app(f, selected.clone());
    let set = DsimpSet {
        definitions: vec![Selection::Local(id, x.clone())],
        ..DsimpSet::default()
    };
    assert_eq!(ctx.dsimp_expression(&target, &set).unwrap(), target);
    assert_eq!(ctx.dsimp_expression(&selected, &set).unwrap(), x);
}

#[test]
fn ordinary_equality_evidence_is_not_a_reflexivity_certificate() {
    let mut ctx = context();
    let a = local(&mut ctx, "A", Expr::sort(Level::one()));
    let x = local(&mut ctx, "x", a.clone());
    let y = local(&mut ctx, "y", a.clone());
    let equation = equality::equation(Level::one(), a, x, y);
    let h = local(&mut ctx, "h", equation.clone());
    assert!(
        !ctx.dsimp_rfl_proof(
            Typed {
                value: h,
                type_: equation
            },
            &std::collections::BTreeSet::new()
        )
        .unwrap()
    );
}

#[test]
fn wildcard_hypotheses_exclude_data_lets_and_dependency_targets() {
    let mut ctx = context();
    let p = local(&mut ctx, "P", Expr::sort(Level::zero()));
    let h = local(&mut ctx, "h", p.clone());
    let family = local(&mut ctx, "F", arrow(p.clone(), Expr::sort(Level::one())));
    local(&mut ctx, "dependent", Expr::app(family, h));
    let independent = local(&mut ctx, "available", p.clone());
    let (_, goal) = ctx.proof_goal(p).unwrap();
    let ExprNode::FVar { id } = independent.node() else {
        unreachable!()
    };
    assert_eq!(
        ctx.dsimp_nondependent_hypotheses(&goal).unwrap(),
        vec![id.clone()]
    );
}

#[test]
fn every_budget_cutoff_preserves_the_transaction_and_the_callers_goal_stack() {
    let mut original = context();
    let a = local(&mut original, "A", Expr::sort(Level::one()));
    let x = local(&mut original, "x", a.clone());
    let p = local(
        &mut original,
        "P",
        arrow(a.clone(), Expr::sort(Level::zero())),
    );
    let expected = Expr::app(p.clone(), x.clone());
    let target = Expr::app(p, Expr::app(identity(a), x));
    let (_, goal) = original.proof_goal(target).unwrap();
    let (_, sibling) = original.proof_goal(expected.clone()).unwrap();
    let pending = proof(&original, &goal, vec![Work::Goal(sibling.clone())]);
    let start = original.txn.budget.heartbeats_consumed;
    let mut complete = original.clone();
    let mut completed = pending.clone();
    complete
        .dsimplify_proof_goal(&mut completed, goal.clone(), &arguments())
        .unwrap();
    assert!(
        matches!(completed.work.as_slice(), [Work::Goal(a), Work::Goal(b)] if a.id == sibling.id && b.target == expected)
    );
    let used = complete.txn.budget.heartbeats_consumed - start;
    for allowance in 0..used {
        let mut limited = original.clone();
        let mut untouched = pending.clone();
        limited.txn.budget.max_heartbeats = start + allowance;
        let error = limited
            .dsimplify_proof_goal(&mut untouched, goal.clone(), &arguments())
            .unwrap_err();
        assert!(!backtrack::recoverable(&error), "{allowance}: {error:?}");
        assert!(limited.txn.budget.heartbeats_consumed >= start + allowance);
        limited.txn.budget = original.txn.budget.clone();
        assert_eq!(limited.txn, original.txn);
        assert_eq!(limited.next, original.next);
        assert_eq!(limited.instance_goals, original.instance_goals);
        assert!(matches!(untouched.work.as_slice(), [Work::Goal(g)] if g.id == sibling.id));
    }
}

#[test]
fn ordinary_no_progress_is_recoverable_but_not_successful() {
    let mut ctx = context();
    let p = local(&mut ctx, "P", Expr::sort(Level::zero()));
    let (_, goal) = ctx.proof_goal(p).unwrap();
    let mut pending = proof(&ctx, &goal, Vec::new());
    let before = ctx.clone();
    let problem = ctx
        .dsimplify_proof_goal(&mut pending, goal.clone(), &arguments())
        .unwrap_err();
    assert!(matches!(
        problem,
        NatDefinitionElabError::Inference(SourceInferenceError::Tactic(
            TacticError::DefinitionalSimplificationNoProgress
        ))
    ));
    assert!(backtrack::recoverable(&problem));
    assert!(!ctx.txn.mvars.is_assigned(&goal.id));
    assert!(pending.work.is_empty());
    assert!(ctx.txn.budget.heartbeats_consumed > before.txn.budget.heartbeats_consumed);
    ctx.txn.budget = before.txn.budget.clone();
    assert_eq!(ctx.txn, before.txn);
    assert_eq!(ctx.next, before.next);
}
