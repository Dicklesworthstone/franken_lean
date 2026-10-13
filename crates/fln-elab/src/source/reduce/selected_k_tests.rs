//! Explicit selection can traverse checked dependent transports, not guess indices.
use super::{source_k_tests::*, *};

fn beta(value: Expr) -> Expr {
    Expr::app(
        Expr::lam(
            Name::anonymous(),
            nat(),
            Expr::bvar(0).unwrap(),
            BinderInfo::Default,
        ),
        value,
    )
}

fn selected(ctx: &mut Context, input: &Expr) -> Result<Option<Expr>, NatDefinitionElabError> {
    let mut head = input;
    let mut arguments = Vec::new();
    while let ExprNode::App { f, a } = head.node() {
        arguments.push(a.clone());
        head = f;
    }
    let ExprNode::Const { name, .. } = head.node() else {
        panic!("test cast must have a recursor head");
    };
    let ConstantInfo::Rec(recursor) = ctx.txn.env.find(name).unwrap().clone() else {
        panic!("test recursor must be admitted");
    };
    ctx.source_k_iota_checked(head, &recursor, &arguments, KEndpointCheck::Kernel)
}

fn unchanged(ctx: &Context, before: &ElabTxn) {
    assert_eq!(ctx.txn.env, before.env);
    assert_eq!(ctx.txn.lctx, before.lctx);
    assert_eq!(ctx.txn.mvars, before.mvars);
    assert_eq!(ctx.txn.universes, before.universes);
    assert_eq!(ctx.txn.constraints, before.constraints);
}

#[test]
fn selected_k_conversion_opens_only_the_real_local_telescope() {
    let env = environment();
    let mut ctx = Context::new(&env, Budget::DEFAULT);
    let n = FVarId(Name::from_components(["n"]));
    ctx.txn
        .lctx
        .add_param(n.clone(), n.0.clone(), nat(), BinderInfo::Default);
    let input = cast(Expr::fvar(n.clone()), beta(Expr::fvar(n)), number(9));
    let before = ctx.txn.clone();
    // Default reduction retains its old gate, even with a local scope available.
    assert_eq!(ctx.whnf(&input).unwrap(), input);
    let rhs = selected(&mut ctx, &input)
        .unwrap()
        .expect("checked endpoint equation");
    assert_eq!(ctx.whnf(&rhs).unwrap(), number(9));
    unchanged(&ctx, &before);
    assert!(ctx.txn.budget.heartbeats_consumed > before.budget.heartbeats_consumed);
}

#[test]
fn selected_k_conversion_never_guesses_indices_or_an_external_binder() {
    let env = environment();
    let mut ctx = Context::new(&env, Budget::DEFAULT);
    let hole = ctx.hole(nat()).unwrap();
    for input in [
        cast(number(7), number(8), number(9)),
        cast(number(7), hole, number(9)),
        cast(
            Expr::bvar(0).unwrap(),
            beta(Expr::bvar(0).unwrap()),
            number(9),
        ),
    ] {
        let before = ctx.txn.clone();
        assert!(selected(&mut ctx, &input).unwrap().is_none());
        unchanged(&ctx, &before);
    }
}

#[test]
fn selected_k_kernel_nonanswers_are_not_folded_branches_or_success() {
    let env = environment();
    let mut ctx = Context::new(&env, Budget::DEFAULT.narrowed(1, Budget::DEFAULT.depth));
    let input = cast(number(7), beta(number(7)), number(9));
    let before = ctx.txn.clone();
    assert!(matches!(
        selected(&mut ctx, &input),
        Err(NatDefinitionElabError::Inference(SourceInferenceError::TypeObligation(outcome)))
            if matches!(*outcome, Outcome::Inconclusive(_))
    ));
    unchanged(&ctx, &before);
    assert!(ctx.txn.budget.heartbeats_consumed > before.budget.heartbeats_consumed);
    ctx.kernel = Budget::DEFAULT;
    assert!(selected(&mut ctx, &input).unwrap().is_some());
}
