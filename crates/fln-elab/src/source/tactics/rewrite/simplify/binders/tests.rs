//! Interruption must leave no fresh locals or speculative rewrite assignments.
use super::*;

fn context() -> Context {
    use fln_env::environment::{DeclarationBudget, DeclarationCommitted};
    use fln_env::pmap::CollisionBudget;
    use fln_kernel::capability::{Published, admit};
    use fln_kernel::council::{Council, CouncilOutcome, convene};
    let mut env = Environment::new();
    let budget = Budget::for_stack_bytes(2 * 1024 * 1024);
    for declaration in crate::seed::source_seed_declarations() {
        let Outcome::Complete(admitted) = admit(&env, declaration, budget) else {
            panic!("seed nonanswer")
        };
        let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted)
        else {
            panic!("seed rejected")
        };
        env = match checked.publish(
            DeclarationBudget::default(),
            CollisionBudget::default(),
            None,
        ) {
            Outcome::Complete(Published::Committed(DeclarationCommitted::Published(result))) => {
                result.environment
            }
            Outcome::Complete(Published::BlockCommitted(result)) => result.environment,
            other => panic!("seed publication {other:?}"),
        };
    }
    Context::new(&env, budget)
}
fn local(context: &mut Context, name: &str, type_: Expr) -> Expr {
    let name = Name::from_components([name]);
    let id = FVarId(name.clone());
    context
        .txn
        .lctx
        .add_param(id.clone(), name, type_, BinderInfo::Default);
    Expr::fvar(id)
}
fn arrow(domain: Expr, body: Expr) -> Expr {
    Expr::forall_e(Name::anonymous(), domain, body, BinderInfo::Default)
}

#[test]
fn every_lambda_rewrite_cutoff_restores_the_entire_transaction() {
    let mut original = context();
    let a = local(&mut original, "A", Expr::sort(Level::one()));
    let f = local(&mut original, "f", arrow(a.clone(), a.clone()));
    let g = local(&mut original, "g", arrow(a.clone(), a.clone()));
    let x = Expr::bvar(0).unwrap();
    let left = Expr::app(f, x.clone());
    let right = Expr::app(g, x);
    let statement = arrow(
        a.clone(),
        equality::equation(Level::one(), a.clone(), left.clone(), right),
    );
    local(&mut original, "h", statement);
    // An unrelated pending hole must survive every failed speculative visit.
    original.hole(a.clone()).unwrap();
    let target = Expr::lam(Name::from_components(["x"]), a, left, BinderInfo::Default);
    let rule = SimpRule::Local(FVarId(Name::from_components(["h"])));
    let start = original.txn.budget.heartbeats_consumed;
    let mut complete = original.clone();
    let proof = complete
        .simp_binder_rule(&target, &rule, &[])
        .unwrap()
        .unwrap();
    assert!(!proof.value.has_expr_mvar());
    assert!(!proof.value.has_loose_bvars());
    let used = complete.txn.budget.heartbeats_consumed - start;
    assert!(used > 0);
    for allowance in 0..used {
        let mut limited = original.clone();
        limited.txn.budget.max_heartbeats = start + allowance;
        let problem = limited
            .simp_binder_rule(&target, &rule, &[])
            .err()
            .expect("interrupted evidence is not a rewrite");
        assert!(
            !backtrack::recoverable(&problem),
            "{allowance}: {problem:?}"
        );
        assert!(
            limited.txn.budget.heartbeats_consumed >= start + allowance,
            "{allowance}: spent {}, {problem:?}",
            limited.txn.budget.heartbeats_consumed - start
        );
        limited.txn.budget = original.txn.budget.clone();
        assert_eq!(limited.txn, original.txn, "{allowance}");
        assert_eq!(limited.next, original.next);
        assert_eq!(limited.instance_goals, original.instance_goals);
        assert_eq!(limited.goal_tags, original.goal_tags);
        assert_eq!(limited.trace_local_names, original.trace_local_names);
        assert!(limited.equations.is_empty());
    }
}

#[test]
fn quantified_rewrites_and_leaf_closure_restore_every_interrupted_context() {
    let mut initial = context();
    let a = local(&mut initial, "A", Expr::sort(Level::one()));
    let f = local(&mut initial, "f", arrow(a.clone(), a.clone()));
    let g = local(&mut initial, "g", arrow(a.clone(), a.clone()));
    let p = local(
        &mut initial,
        "P",
        arrow(a.clone(), Expr::sort(Level::zero())),
    );
    let x = Expr::bvar(0).unwrap();
    let left = Expr::app(f, x.clone());
    local(
        &mut initial,
        "h",
        arrow(
            a.clone(),
            equality::equation(
                Level::one(),
                a.clone(),
                left.clone(),
                Expr::app(g, x.clone()),
            ),
        ),
    );
    let rewrite_target = arrow(a.clone(), Expr::app(p, left));
    let reflexive_target = arrow(
        a.clone(),
        equality::equation(Level::one(), a.clone(), x.clone(), x),
    );
    let true_target = arrow(
        a.clone(),
        Expr::const_(Name::from_components(["True"]), vec![]),
    );
    initial.hole(a).unwrap();
    for (target, rewriting) in [
        (rewrite_target, true),
        (reflexive_target, false),
        (true_target, false),
    ] {
        let mut original = initial.clone();
        let (_, goal) = original.proof_goal(target.clone()).unwrap();
        let run = |ctx: &mut Context| {
            if rewriting {
                ctx.simp_binder_rule(
                    &target,
                    &SimpRule::Local(FVarId(Name::from_components(["h"]))),
                    &[],
                )
                .map(|result| result.map(|term| term.value))
            } else {
                ctx.simp_quantified_reflexivity(&goal, target.clone())
            }
        };
        let start = original.txn.budget.heartbeats_consumed;
        let mut complete = original.clone();
        let proof = run(&mut complete).unwrap().unwrap();
        assert!(!proof.has_expr_mvar());
        assert!(!proof.has_level_mvar());
        assert!(!proof.has_loose_bvars());
        assert_eq!(complete.txn.lctx, original.txn.lctx);
        let used = complete.txn.budget.heartbeats_consumed - start;
        for allowance in 0..used {
            let mut limited = original.clone();
            limited.txn.budget.max_heartbeats = start + allowance;
            let problem = run(&mut limited).err().expect("not completed evidence");
            assert!(
                !backtrack::recoverable(&problem),
                "{allowance}: {problem:?}"
            );
            assert!(limited.txn.budget.heartbeats_consumed >= start + allowance);
            limited.txn.budget = original.txn.budget.clone();
            assert_eq!(limited.txn, original.txn, "{allowance}");
            assert_eq!(limited.next, original.next);
            assert_eq!(limited.instance_goals, original.instance_goals);
            assert_eq!(limited.goal_tags, original.goal_tags);
            assert_eq!(limited.trace_local_names, original.trace_local_names);
            assert!(limited.equations.is_empty());
        }
    }
}
