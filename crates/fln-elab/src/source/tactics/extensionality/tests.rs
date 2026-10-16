//! Every interrupted extensionality step restores semantic state, never work.
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
fn every_funext_budget_stop_restores_binders_metavariables_and_siblings() {
    let seed = seeded_context();
    for dependent in [false, true] {
        let mut original = seed.clone();
        let a = local(&mut original, "A", Expr::sort(Level::one()));
        let function_type = if dependent {
            let family = local(
                &mut original,
                "F",
                arrow(a.clone(), Expr::sort(Level::one())),
            );
            Expr::forall_e(
                Name::from_components(["x"]),
                a.clone(),
                Expr::app(family, Expr::bvar(0).unwrap()),
                BinderInfo::Default,
            )
        } else {
            arrow(a.clone(), a)
        };
        let f = local(&mut original, "f", function_type.clone());
        let g = local(&mut original, "g", function_type.clone());
        let target = equality::equation(Level::one(), function_type, f, g);
        let (root, goal) = original.proof_goal(target.clone()).unwrap();
        let (_, sibling) = original.proof_goal(target.clone()).unwrap();
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
            Syntax::atom(fln_syntax::source::SourceInfo::None, "funext"),
            Syntax::node(Name::from_components(["null"]), Vec::new()),
        ];
        let start = original.txn.budget.heartbeats_consumed;
        let mut completed = original.clone();
        let mut output = proof.clone();
        completed
            .funext_proof_goal(&mut output, goal.clone(), &args)
            .unwrap();
        let used = completed.txn.budget.heartbeats_consumed - start;
        assert!(used > 0);
        assert!(
            matches!(output.work.as_slice(), [Work::Goal(s), Work::Close(p, _), Work::Goal(c)]
            if s.id == sibling.id && p.id == goal.id && c.id != goal.id && c.introduced.len() == 1)
        );
        for allowance in 0..used {
            let mut limited = original.clone();
            limited.txn.budget.max_heartbeats = start + allowance;
            let before = limited.clone();
            let mut pending = proof.clone();
            let problem = limited
                .funext_proof_goal(&mut pending, goal.clone(), &args)
                .expect_err("interrupted function extensionality is not a successful repeat");
            assert!(
                !backtrack::recoverable(&problem),
                "{dependent}/{allowance}: {problem:?}"
            );
            let spent = limited.txn.budget.heartbeats_consumed;
            assert!(spent >= start + allowance);
            let mut expected = before.txn.clone();
            expected.budget.heartbeats_consumed = spent;
            assert_eq!(limited.txn, expected, "{dependent}/{allowance}");
            assert_eq!(limited.next, before.next);
            assert_eq!(limited.instance_goals, before.instance_goals);
            assert_eq!(limited.goal_tags, before.goal_tags);
            assert_eq!(limited.trace_local_names, before.trace_local_names);
            assert!(limited.equations.is_empty());
            assert!(matches!(pending.work.as_slice(), [Work::Goal(g)] if g.id == sibling.id));
        }
    }
}

fn introduction_args(script: &str, funext: bool) -> Vec<Syntax> {
    let source = format!("theorem t : True := by {script}");
    let parsed = fln_parse::parse_definition(source.as_bytes()).unwrap();
    let wanted = if funext {
        Name::from_components(["tacticFunext___"])
    } else {
        parser_kind(&["Tactic", "intro"])
    };
    let mut pending = vec![parsed.syntax()];
    while let Some(syntax) = pending.pop() {
        if let Syntax::Node { kind, args, .. } = syntax {
            if kind == &wanted {
                return args.clone();
            }
            pending.extend(args);
        }
    }
    panic!("no introduction in {source}");
}

#[test]
fn typed_and_pattern_introduction_cutoffs_restore_refinement_frames_and_pending_goals() {
    let seed = seeded_context();
    for (script, extensionality) in [
        ("intro (x : Nat)", false),
        ("intro ⟨p, q⟩", false),
        ("funext (x : Nat)", true),
    ] {
        let mut original = seed.clone();
        let nat = Expr::const_(Name::from_components(["Nat"]), Vec::new());
        let truth = Expr::const_(Name::from_components(["True"]), Vec::new());
        let target = if extensionality {
            let ftype = arrow(nat.clone(), nat.clone());
            let f = local(&mut original, "f", ftype.clone());
            let g = local(&mut original, "g", ftype.clone());
            equality::equation(Level::one(), ftype, f, g)
        } else if script.contains('⟨') {
            let both = Expr::app(
                Expr::app(
                    Expr::const_(Name::from_components(["And"]), Vec::new()),
                    truth.clone(),
                ),
                truth.clone(),
            );
            arrow(both, truth.clone())
        } else {
            arrow(nat, truth.clone())
        };
        let (_, goal) = original.proof_goal(target).unwrap();
        let (_, sibling) = original.proof_goal(truth).unwrap();
        let mut proof = introductions::frame(&goal);
        proof.work.push(Work::Goal(sibling.clone()));
        let args = introduction_args(script, extensionality);
        let call = |context: &mut Context, proof: &mut ProofState<'_>| {
            if extensionality {
                context.funext_proof_goal(proof, goal.clone(), &args)
            } else {
                context.intro_proof_patterns(
                    proof,
                    goal.clone(),
                    expect_null_args(&args[1], "patterns").unwrap(),
                )
            }
        };
        let mut completed = original.clone();
        call(&mut completed, &mut proof.clone()).unwrap();
        let before = original.txn.budget.heartbeats_consumed;
        let used = completed.txn.budget.heartbeats_consumed - before;
        for allowance in 0..used {
            let mut limited = original.clone();
            limited.txn.budget.max_heartbeats = before + allowance;
            let mut pending = proof.clone();
            let problem = call(&mut limited, &mut pending)
                .expect_err("no partially introduced pattern may commit");
            assert!(
                !backtrack::recoverable(&problem),
                "{script}/{allowance}: {problem:?}"
            );
            assert!(limited.txn.budget.heartbeats_consumed >= before + allowance);
            limited.txn.budget = original.txn.budget.clone();
            assert_eq!(limited.txn, original.txn, "{script}/{allowance}");
            assert_eq!(limited.next, original.next);
            assert_eq!(limited.instance_goals, original.instance_goals);
            assert_eq!(limited.goal_tags, original.goal_tags);
            assert_eq!(limited.trace_local_names, original.trace_local_names);
            assert!(limited.refinements.is_empty());
            assert!(limited.equations.is_empty());
            assert!(matches!(pending.work.as_slice(), [Work::Goal(g)] if g.id == sibling.id));
        }
    }
}
