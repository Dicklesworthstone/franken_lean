//! Real admitted dependent dictionaries, fresh holes and complete table replay.
use super::*;
use crate::records::{RecordBudget, RecordSpec, record_declarations};
use fln_env::environment::{DeclarationBudget, DeclarationCommitted};
use fln_env::pmap::CollisionBudget;
use fln_kernel::capability::{Published, admit};
use fln_kernel::council::{Council, CouncilOutcome, convene};

fn name(s: &str) -> Name {
    Name::from_components(s.split('.'))
}
fn constant(s: &str) -> Expr {
    Expr::const_(name(s), vec![])
}
fn apply(s: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(constant(s), Expr::app)
}
fn inhabited(alpha: Expr) -> Expr {
    Expr::app(Expr::const_(name("Inhabited"), vec![Level::one()]), alpha)
}
fn dictionary() -> Expr {
    [
        constant("Nat"),
        Expr::lit(Literal::Nat(fln_core::expr::NatLit::from_u64(7))),
    ]
    .into_iter()
    .fold(
        Expr::const_(name("Inhabited.mk"), vec![Level::one()]),
        Expr::app,
    )
}
fn publish(env: &Environment, d: Declaration) -> Environment {
    let Outcome::Complete(admitted) = admit(env, d, Budget::for_stack_bytes(2 * 1024 * 1024))
    else {
        panic!("fixture admission nonanswer");
    };
    let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted) else {
        panic!("fixture admission rejected");
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
        other => panic!("fixture publication: {other:?}"),
    }
}
fn fixture() -> (Context, InstanceRegistry) {
    let budget = Budget::for_stack_bytes(2 * 1024 * 1024);
    let mut env = crate::seed::bootstrap_nat_environment(budget).unwrap();
    for d in [
        crate::seed::out_param_seed_declaration(),
        crate::seed::inhabited::inhabited_seed_declaration(),
    ] {
        env = publish(&env, d);
    }
    let mut lctx = LocalContext::new();
    let alpha = lctx
        .add_param(
            FVarId(name("alpha")),
            name("alpha"),
            Expr::app(
                Expr::const_(name("outParam"), vec![Level::one().succ().unwrap()]),
                Expr::sort(Level::one()),
            ),
            BinderInfo::Default,
        )
        .clone();
    let d = lctx
        .add_param(
            FVarId(name("dict")),
            name("dict"),
            inhabited(Expr::fvar(alpha.id.clone())),
            BinderInfo::InstImplicit,
        )
        .clone();
    for d in record_declarations(
        &RecordSpec {
            name: name("Output"),
            level_params: vec![],
            parameters: vec![alpha, d],
            fields: vec![],
            result_level: Level::one(),
            is_class: true,
        },
        RecordBudget::default(),
    )
    .unwrap()
    {
        env = publish(&env, d);
    }
    for class in ["Output", "Inhabited"] {
        env = crate::instances::register_class(&env, &name(class)).unwrap();
    }
    let registry = InstanceRegistry::read(&env).unwrap();
    (Context::new(&env, budget), registry)
}
fn query(ctx: &mut Context, registry: &InstanceRegistry) -> (Frame, MVarId, MVarId) {
    let alpha = ctx.hole(Expr::sort(Level::one())).unwrap();
    let dictionary = ctx.instance_hole(inhabited(alpha.clone())).unwrap();
    let root = ctx
        .instance_hole(apply("Output", [alpha.clone(), dictionary.clone()]))
        .unwrap();
    let ExprNode::MVar { id: root } = root.node() else {
        unreachable!()
    };
    let ambient = ctx.txn.lctx.clone();
    let frame = ctx
        .instance_frame(root.clone(), registry, &ambient, None, true)
        .unwrap()
        .unwrap();
    let ExprNode::MVar { id: alpha } = alpha.node() else {
        unreachable!()
    };
    let ExprNode::MVar { id: dictionary } = dictionary.node() else {
        unreachable!()
    };
    (frame, alpha.clone(), dictionary.clone())
}
fn path(ctx: &Context) -> [Frame; 1] {
    [Frame {
        goal: MVarId(name("root")),
        target: constant("Root"),
        expected: constant("Root"),
        key: constant("Root"),
        binders: vec![],
        base: ctx.clone(),
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
fn actual() -> Expr {
    apply("Output", [constant("Nat"), dictionary()])
}
fn value() -> Expr {
    apply("Output.mk", [constant("Nat"), dictionary()])
}
fn unchanged(ctx: &Context, before: &Context) {
    assert_eq!(ctx.txn.mvars, before.txn.mvars);
    assert_eq!(ctx.txn.universes, before.txn.universes);
    assert_eq!(ctx.txn.constraints, before.txn.constraints);
    assert_eq!(ctx.txn.lctx, before.txn.lctx);
    assert_eq!(ctx.txn.env, before.txn.env);
    assert_eq!(ctx.equations.len(), before.equations.len());
    for (actual, expected) in ctx.equations.iter().zip(&before.equations) {
        assert_eq!(actual.sides, expected.sides);
        assert!(actual.policy == expected.policy);
    }
}
fn learned() -> (Context, InstanceRegistry, GroundTable, [Frame; 1]) {
    let (mut ctx, registry) = fixture();
    let path = path(&ctx);
    let (frame, _, _) = query(&mut ctx, &registry);
    ctx.unify_source_batch(&[(actual(), frame.target.clone())], false)
        .unwrap();
    ctx.reconcile_instance_outputs(&frame, actual(), frame.expected.clone())
        .unwrap();
    let mut table = GroundTable::default();
    table.remember(&mut ctx, &frame, &path, &value()).unwrap();
    assert_eq!(
        table.entries, 1,
        "a completed dependent dictionary should be tabled"
    );
    (ctx, registry, table, path)
}

#[test]
fn cached_dictionary_answers_fill_fresh_dependent_outputs_without_copying_assignments() {
    let (mut ctx, registry, table, path) = learned();
    for _ in 0..3 {
        let (frame, alpha, d) = query(&mut ctx, &registry);
        let hole_count = ctx.txn.mvars.len();
        assert!(!ctx.txn.mvars.is_assigned(&d));
        assert_eq!(
            table.lookup(&mut ctx, &frame, &path).unwrap(),
            Some(Answer::Solved(value()))
        );
        assert_eq!(
            ctx.txn.mvars.get_assigned_expr(&alpha),
            Some(&constant("Nat"))
        );
        assert_eq!(ctx.txn.mvars.get_assigned_expr(&d), Some(&dictionary()));
        assert_eq!(
            ctx.txn.mvars.get_decl(&d).unwrap().kind,
            MetavarKind::SyntheticOpaque
        );
        assert_eq!(
            ctx.txn.mvars.len(),
            hole_count,
            "replay must not import foreign holes"
        );
        assert!(!ctx.txn.mvars.is_assigned(&frame.goal));
        ctx.assign_instance_answer(&frame, value()).unwrap();
    }
}

#[test]
fn opaque_keys_remain_ineligible_for_tactic_goals_semi_outputs_and_foreign_scopes() {
    let (mut ctx, registry, table, path) = learned();
    for mode in 0..3 {
        let (mut frame, _, d) = query(&mut ctx, &registry);
        match mode {
            0 => frame.base.instance_goals.retain(|id| id != &d),
            1 => {
                let ExprNode::App { f, .. } = frame.key.node() else {
                    unreachable!()
                };
                frame.key = Expr::app(f.clone(), Expr::bvar(1).unwrap());
            }
            _ => {
                frame.base.txn.lctx.add_param(
                    FVarId(name("foreign")),
                    name("foreign"),
                    constant("Nat"),
                    BinderInfo::Default,
                );
            }
        }
        let before = ctx.clone();
        assert!(table.lookup(&mut ctx, &frame, &path).unwrap().is_none());
        unchanged(&ctx, &before);
    }
}

#[test]
fn replay_failure_rolls_back_prepared_outputs_and_never_caches_exhaustion() {
    let (mut ctx, registry, table, path) = learned();
    let (frame, _, _) = query(&mut ctx, &registry);
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
fn selected_output_replay_uses_default_conversion_without_widening_input_matching() {
    let (mut ctx, registry) = fixture();
    let source = b"def Id (A : Type) : Type := A";
    let checked = crate::check_definition_source(source, &ctx.txn.env, ctx.kernel).unwrap();
    ctx.txn.env = publish(&ctx.txn.env, checked.declaration);
    let (mut frame, _, d) = query(&mut ctx, &registry);
    frame.expected = apply(
        "Output",
        [apply("Id", [constant("Nat")]), Expr::mvar(d.clone())],
    );
    assert!(replay_outputs(&mut ctx, &frame, &actual()).unwrap());
    assert_eq!(ctx.txn.mvars.get_assigned_expr(&d), Some(&dictionary()));
}

#[test]
fn dependent_key_aliases_use_saved_assignments_not_later_search_results() {
    let (mut ctx, registry) = fixture();
    let path = path(&ctx);
    let old = ctx.hole(Expr::sort(Level::one())).unwrap();
    let d = ctx.instance_hole(inhabited(old.clone())).unwrap();
    let alpha = ctx.hole(Expr::sort(Level::one())).unwrap();
    let ExprNode::MVar { id: old_id } = old.node() else {
        unreachable!()
    };
    ctx.txn
        .assign_mvar(
            old_id.clone(),
            alpha.clone(),
            AssignmentJustification::DirectDefEq,
        )
        .unwrap();
    let root = ctx
        .instance_hole(apply("Output", [alpha.clone(), d]))
        .unwrap();
    let ExprNode::MVar { id } = root.node() else {
        unreachable!()
    };
    let ambient = ctx.txn.lctx.clone();
    let frame = ctx
        .instance_frame(id.clone(), &registry, &ambient, None, true)
        .unwrap()
        .unwrap();
    let before = key(&mut ctx, &frame, &path)
        .unwrap()
        .expect("saved type aliases are tableable");
    let (fresh, _, _) = query(&mut ctx, &registry);
    assert!(Some(before.clone()) == key(&mut ctx, &fresh, &path).unwrap());
    ctx.unify_source_batch(&[(alpha, constant("Nat"))], false)
        .unwrap();
    assert!(
        Some(before) == key(&mut ctx, &frame, &path).unwrap(),
        "later candidate assignments must not change the saved query"
    );
}
