//! Budget cutoffs exercise the real tactic entry, including dependent suffixes.
use super::*;

fn seeded_context() -> Context {
    use fln_env::environment::{DeclarationBudget, DeclarationCommitted};
    use fln_env::pmap::CollisionBudget;
    use fln_kernel::capability::{Published, admit};
    use fln_kernel::council::{Council, CouncilOutcome, convene};
    let mut env = Environment::new();
    let budget = Budget::for_stack_bytes(2 * 1024 * 1024);
    for declaration in crate::seed::source_seed_declarations() {
        let Outcome::Complete(admitted) = admit(&env, declaration, budget) else {
            panic!("seed nonanswer");
        };
        let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted)
        else {
            panic!("seed rejected");
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
        .add_param(id.clone(), name.clone(), type_, BinderInfo::Default);
    context.trace_local_names.insert(id.clone(), name);
    Expr::fvar(id)
}
fn arrow(domain: Expr, range: Expr) -> Expr {
    Expr::forall_e(Name::anonymous(), domain, range, BinderInfo::Default)
}

#[test]
fn every_congruence_budget_stop_restores_the_transaction_and_sibling_work() {
    let seed = seeded_context();
    for shape in ["ordinary", "dependent", "implication"] {
        let mut original = seed.clone();
        let a = local(&mut original, "A", Expr::sort(Level::one()));
        let x = local(&mut original, "x", a.clone());
        let y = local(&mut original, "y", a.clone());
        let (domain, left, right) = if shape == "implication" {
            let b = local(&mut original, "B", Expr::sort(Level::one()));
            (
                Expr::sort(Level::one()),
                arrow(a.clone(), a.clone()),
                arrow(b.clone(), b),
            )
        } else if shape == "dependent" {
            let family = local(
                &mut original,
                "F",
                arrow(a.clone(), Expr::sort(Level::one())),
            );
            let ftype = Expr::forall_e(
                Name::anonymous(),
                a.clone(),
                arrow(Expr::app(family.clone(), Expr::bvar(0).unwrap()), a.clone()),
                BinderInfo::Default,
            );
            let f = local(&mut original, "f", ftype);
            let vx = local(&mut original, "vx", Expr::app(family.clone(), x.clone()));
            let vy = local(&mut original, "vy", Expr::app(family, y.clone()));
            (
                a.clone(),
                Expr::app(Expr::app(f.clone(), x), vx),
                Expr::app(Expr::app(f, y), vy),
            )
        } else {
            let f = local(&mut original, "f", arrow(a.clone(), a.clone()));
            (a, Expr::app(f.clone(), x), Expr::app(f, y))
        };
        let level = original.congruence_sort(&domain).unwrap();
        let target = equality::equation(level, domain, left, right);
        let (root, goal) = original.proof_goal(target.clone()).unwrap();
        let (_, sibling) = original.proof_goal(target.clone()).unwrap();
        original
            .goal_tags
            .insert(sibling.id.clone(), Name::from_components(["sibling"]));
        let proof = ProofState {
            extent: None,
            saved: original.txn.lctx.clone(),
            target,
            root,
            instructions: Vec::new(),
            cursor: 0,
            work: vec![Work::Goal(sibling.clone())],
            controls: Vec::new(),
        };
        let args = [
            Syntax::Atom {
                info: fln_syntax::source::SourceInfo::None,
                val: "congr".to_owned(),
            },
            Syntax::node(Name::from_components(["null"]), vec![]),
        ];
        let start = original.txn.budget.heartbeats_consumed;
        let mut completed = original.clone();
        let mut completed_proof = proof.clone();
        completed
            .congruence_proof_goal(&mut completed_proof, goal.clone(), &args)
            .unwrap();
        let used = completed.txn.budget.heartbeats_consumed - start;
        assert!(used > 0);
        assert!(completed.txn.mvars.len() > original.txn.mvars.len());
        assert_eq!(completed.txn.lctx, original.txn.lctx);
        for allowance in 0..used {
            let mut limited = original.clone();
            limited.txn.budget.max_heartbeats = start + allowance;
            let before = limited.clone();
            let mut pending = proof.clone();
            let problem = limited
                .congruence_proof_goal(&mut pending, goal.clone(), &args)
                .expect_err("a smaller budget must not complete congruence");
            assert!(
                !backtrack::recoverable(&problem),
                "shape={shape}, allowance={allowance}: {problem:?}"
            );
            let spent = limited.txn.budget.heartbeats_consumed;
            assert!(spent >= start + allowance);
            let mut expected = before.txn.clone();
            expected.budget.heartbeats_consumed = spent;
            assert_eq!(
                limited.txn, expected,
                "shape={shape}, allowance={allowance}"
            );
            assert_eq!(limited.next, before.next);
            assert_eq!(limited.instance_goals, before.instance_goals);
            assert_eq!(limited.goal_tags, before.goal_tags);
            assert_eq!(limited.trace_local_names, before.trace_local_names);
            assert!(limited.equations.is_empty());
            assert!(matches!(pending.work.as_slice(), [Work::Goal(g)] if g.id == sibling.id));
        }
    }
}
