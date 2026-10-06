//! Cache hits are exercised with actual admitted universe-polymorphic records.
use super::*;
use crate::records::{RecordBudget, RecordSpec, record_declarations};
use fln_core::expr::NatLit;
use fln_env::environment::{DeclarationBudget, DeclarationCommitted};
use fln_env::pmap::CollisionBudget;
use fln_kernel::capability::{Published, admit};
use fln_kernel::council::{Council, CouncilOutcome, convene};

fn n(s: &str) -> Name {
    Name::from_components(s.split('.'))
}
fn c(s: &str) -> Expr {
    Expr::const_(n(s), vec![])
}
fn carrier(u: Level, alpha: Expr) -> Expr {
    Expr::app(Expr::const_(n("Carrier"), vec![u]), alpha)
}
fn dictionary(u: Level, alpha: Expr) -> Expr {
    [alpha, Expr::lit(Literal::Nat(NatLit::from_u64(42)))]
        .into_iter()
        .fold(Expr::const_(n("Carrier.mk"), vec![u]), Expr::app)
}
fn publish(env: &Environment, d: Declaration, budget: Budget) -> Environment {
    let Outcome::Complete(admitted) = admit(env, d, budget) else {
        panic!("fixture admission nonanswer")
    };
    let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted) else {
        panic!("fixture admission rejected")
    };
    match checked.publish(
        DeclarationBudget::default(),
        CollisionBudget::default(),
        None,
    ) {
        Outcome::Complete(Published::BlockCommitted(p)) => p.environment,
        Outcome::Complete(Published::Committed(DeclarationCommitted::Published(p))) => {
            p.environment
        }
        other => panic!("fixture publication {other:?}"),
    }
}
fn fixture() -> (Context, InstanceRegistry) {
    let budget = Budget::for_stack_bytes(2 * 1024 * 1024);
    let mut env = crate::seed::bootstrap_nat_environment(budget).unwrap();
    env = publish(&env, crate::seed::out_param_seed_declaration(), budget);
    let u = Level::param(n("u"));
    let mut locals = LocalContext::new();
    let alpha = locals
        .add_param(
            FVarId(n("alpha")),
            n("alpha"),
            Expr::app(
                Expr::const_(n("outParam"), vec![u.clone().succ().unwrap()]),
                Expr::sort(u),
            ),
            BinderInfo::Default,
        )
        .clone();
    let field = locals
        .add_param(
            FVarId(n("value")),
            n("value"),
            c("Nat"),
            BinderInfo::Default,
        )
        .clone();
    for d in record_declarations(
        &RecordSpec {
            name: n("Carrier"),
            level_params: vec![n("u")],
            parameters: vec![alpha],
            fields: vec![field],
            result_level: Level::one(),
            is_class: true,
        },
        RecordBudget::default(),
    )
    .unwrap()
    {
        env = publish(&env, d, budget);
    }
    env = crate::instances::register_class(&env, &n("Carrier")).unwrap();
    let registry = InstanceRegistry::read(&env).unwrap();
    (Context::new(&env, budget), registry)
}
fn query(
    ctx: &mut Context,
    registry: &InstanceRegistry,
    level: Option<Level>,
) -> (Frame, Level, Expr) {
    let u = level.unwrap_or_else(|| ctx.level().unwrap());
    let alpha = ctx.hole(Expr::sort(u.clone())).unwrap();
    let goal = ctx
        .instance_hole(carrier(u.clone(), alpha.clone()))
        .unwrap();
    let ExprNode::MVar { id } = goal.node() else {
        unreachable!()
    };
    let ambient = ctx.txn.lctx.clone();
    let frame = ctx
        .instance_frame(id.clone(), registry, &ambient, None, true)
        .unwrap()
        .unwrap();
    (frame, u, alpha)
}
fn make_path(frame: &Frame) -> [Frame; 1] {
    [Frame {
        goal: MVarId(n("root")),
        target: c("Root"),
        expected: c("Root"),
        key: c("Root"),
        binders: vec![],
        base: frame.base.clone(),
        candidates: vec![],
        cursor: 0,
        chosen: None,
        children: vec![],
        resumable: false,
        replay_first: false,
        returned: false,
        default_application: false,
    }]
}
fn solved() -> (Context, InstanceRegistry, GroundTable, [Frame; 1]) {
    let (mut ctx, registry) = fixture();
    let (frame, _, _) = query(&mut ctx, &registry, None);
    let path = make_path(&frame);
    let actual = carrier(Level::one(), c("Nat"));
    ctx.unify_source_batch(&[(actual.clone(), frame.target.clone())], false)
        .unwrap();
    ctx.reconcile_instance_outputs(&frame, actual, frame.expected.clone())
        .unwrap();
    let value = dictionary(Level::one(), c("Nat"));
    let mut table = GroundTable::default();
    table.remember(&mut ctx, &frame, &path, &value).unwrap();
    assert_eq!(
        table.entries, 1,
        "freshened output universes must admit typed answer keys"
    );
    (ctx, registry, table, path)
}
fn unchanged(ctx: &Context, before: &Context) {
    assert_eq!(ctx.txn.mvars, before.txn.mvars);
    assert_eq!(ctx.txn.universes, before.txn.universes);
    assert_eq!(ctx.txn.constraints, before.txn.constraints);
    assert_eq!(ctx.txn.env, before.txn.env);
    assert_eq!(ctx.txn.lctx, before.txn.lctx);
    assert_eq!(ctx.equations.len(), before.equations.len());
}

#[test]
fn output_universe_replay_assigns_each_queries_own_type_and_level_holes() {
    let (mut ctx, registry, table, path) = solved();
    for _ in 0..3 {
        let (frame, u, alpha) = query(&mut ctx, &registry, None);
        let before = ctx.txn.mvars.len();
        let value = dictionary(Level::one(), c("Nat"));
        assert_eq!(
            table.lookup(&mut ctx, &frame, &path).unwrap(),
            Some(Answer::Solved(value.clone()))
        );
        assert_eq!(ctx.instantiate(&alpha).unwrap(), c("Nat"));
        assert_eq!(
            ctx.instantiate(&Expr::sort(u)).unwrap(),
            Expr::sort(Level::one())
        );
        assert_eq!(
            ctx.txn.mvars.len(),
            before,
            "foreign holes must never be imported"
        );
        assert!(!ctx.txn.mvars.is_assigned(&frame.goal));
        ctx.assign_instance_answer(&frame, value).unwrap();
    }
}

#[test]
fn fixed_universes_and_path_anchored_unknowns_do_not_share_the_open_answer() {
    let (mut ctx, registry, table, path) = solved();
    for level in [
        Level::zero(),
        Level::one(),
        Level::one().succ().unwrap(),
        Level::param(n("v")),
    ] {
        let (frame, _, _) = query(&mut ctx, &registry, Some(level));
        let before = ctx.clone();
        assert!(table.lookup(&mut ctx, &frame, &path).unwrap().is_none());
        unchanged(&ctx, &before);
    }
    let (frame, u, _) = query(&mut ctx, &registry, None);
    let mut anchored = make_path(&frame);
    anchored[0].key = Expr::const_(n("Root"), vec![u]);
    let before = ctx.clone();
    assert!(table.lookup(&mut ctx, &frame, &anchored).unwrap().is_none());
    unchanged(&ctx, &before);
}

#[test]
fn output_universe_replay_failure_restores_assignments_and_can_recover() {
    let (mut ctx, registry, table, path) = solved();
    let (frame, _, _) = query(&mut ctx, &registry, None);
    let before = ctx.clone();
    let mut control = ctx.clone();
    assert!(table.lookup(&mut control, &frame, &path).unwrap().is_some());
    ctx.txn.budget.max_heartbeats = control.txn.budget.heartbeats_consumed - 1;
    assert!(table.lookup(&mut ctx, &frame, &path).is_err());
    unchanged(&ctx, &before);
    assert_eq!(table.entries, 1);
    ctx.txn.budget.max_heartbeats = control.txn.budget.max_heartbeats;
    assert!(table.lookup(&mut ctx, &frame, &path).unwrap().is_some());
}

#[test]
fn changed_live_universe_does_not_rewrite_the_saved_key_or_partially_replay() {
    let (mut ctx, registry, table, path) = solved();
    let (frame, u, _) = query(&mut ctx, &registry, None);
    ctx.unify_source_batch(
        &[(Expr::sort(u), Expr::sort(Level::one().succ().unwrap()))],
        false,
    )
    .unwrap();
    let before = ctx.clone();
    assert!(table.lookup(&mut ctx, &frame, &path).unwrap().is_none());
    unchanged(&ctx, &before);
    assert_eq!(table.entries, 1);
}

#[test]
fn head_compatibility_keeps_nonoutput_universes_rigid_and_checks_arity() {
    let (mut ctx, _) = fixture();
    let u = Level::mvar(LMVarId(n("fresh")));
    let placeholder = Level::param(Name::num(n("_fln_instance_output_universe"), 1));
    let original = Expr::const_(n("C"), vec![Level::one(), Level::zero()]);
    let prepared = Expr::const_(n("C"), vec![Level::one(), u]);
    let shape = Expr::const_(n("C"), vec![Level::one(), placeholder.clone()]);
    assert!(compatible_heads(&mut ctx, &original, &prepared, &shape).unwrap());
    for wrong in [
        Expr::const_(n("D"), vec![Level::one(), placeholder.clone()]),
        Expr::const_(n("C"), vec![placeholder.clone()]),
        Expr::const_(n("C"), vec![Level::zero(), placeholder]),
        Expr::const_(
            n("C"),
            vec![
                Level::one(),
                Level::param(Name::num(n("_fln_instance_output_universe"), 0)),
            ],
        ),
    ] {
        assert!(!compatible_heads(&mut ctx, &original, &prepared, &wrong).unwrap());
    }
}
