//! KR-955 reduction against the independently checked canonical quartet.
#![forbid(unsafe_code)]
use super::*;
use fln_checker::defeq::{DefEqOutcome, def_eq};
use fln_checker::whnf::{FreeBinding, WhnfContext, WhnfOutcome, whnf, whnf_with};
use fln_core::expr::FVarId;

fn context() -> WhnfContext {
    let mut environment = equality_environment(false, false);
    let entries = quotient_entries();
    assert!(admit_quotient(&environment, &entries, AdmissionBudget::unlimited()).is_admitted());
    for entry in entries {
        let EnvironmentOutcome::Complete {
            environment: next, ..
        } = environment.extend(entry, EnvironmentBudget::unlimited())
        else {
            panic!("checked quartet");
        };
        environment = next;
    }
    WhnfContext::new(Vec::new(), Vec::new(), environment)
}
fn free(s: &str) -> Expr {
    Expr::fvar(FVarId(primary_name(s)))
}
fn nat() -> Expr {
    Expr::const_(primary_name("Nat"), Vec::new())
}
fn lam(body: Expr) -> Expr {
    Expr::lam(primary_name("a"), nat(), body, BinderInfo::Default)
}
fn apps(head: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(head, Expr::app)
}
fn primitive(s: &str, levels: Vec<Level>) -> Expr {
    Expr::const_(Name::from_components(["Quot", s]), levels)
}
fn mk(value: Expr) -> Expr {
    apps(
        primitive("mk", vec![Level::one()]),
        [nat(), free("r"), value],
    )
}
fn lift(function: Expr, major: Expr) -> Expr {
    apps(
        primitive("lift", vec![Level::one(), Level::one()]),
        [nat(), free("r"), nat(), function, free("respect"), major],
    )
}
fn induction(branch: Expr, major: Expr) -> Expr {
    apps(
        primitive("ind", vec![Level::one()]),
        [nat(), free("r"), free("motive"), branch, major],
    )
}
fn same(left: &Expr, right: &Expr, context: &WhnfContext) {
    for (a, b) in [(left, right), (right, left)] {
        let result = def_eq(&decoded(a), &decoded(b), context, DefEqBudget::unlimited());
        assert!(matches!(result, DefEqOutcome::Equal(_)), "{result:?}");
    }
}
fn normalized(term: &Expr, context: &WhnfContext) -> fln_checker::whnf::WhnfResult {
    let result = whnf(&decoded(term), context, WhnfBudget::unlimited());
    let WhnfOutcome::Complete(result) = result else {
        panic!("{result:?}");
    };
    result
}
#[test]
fn lift_and_induction_reduce_before_application_congruence() {
    let context = context();
    for (call, function) in [
        (lift(free("f"), mk(free("a"))), free("f")),
        (induction(free("minor"), mk(free("a"))), free("minor")),
    ] {
        same(&call, &Expr::app(function, free("a")), &context);
    }
}
#[test]
fn function_valued_quotients_preserve_all_trailing_arguments() {
    let context = context();
    let call = apps(lift(free("f"), mk(free("a"))), [free("x"), free("y")]);
    same(
        &call,
        &apps(free("f"), [free("a"), free("x"), free("y")]),
        &context,
    );
    let call = Expr::app(induction(free("minor"), mk(free("a"))), free("x"));
    same(
        &call,
        &apps(free("minor"), [free("a"), free("x")]),
        &context,
    );
}
#[test]
fn neutral_and_malformed_majors_do_not_compute() {
    let context = context();
    for major in [
        free("q"),
        primitive("mk", vec![Level::one()]),
        apps(primitive("mk", vec![Level::one()]), [nat(), free("r")]),
        apps(mk(free("a")), [free("extra")]),
        apps(
            primitive("mk", vec![Level::zero()]),
            [nat(), free("r"), free("a")],
        ),
    ] {
        for call in [
            lift(free("f"), major.clone()),
            induction(free("minor"), major),
        ] {
            assert_eq!(normalized(&call, &context).reductions, 0);
            assert!(!matches!(
                def_eq(
                    &decoded(&call),
                    &decoded(&Expr::app(free("f"), free("a"))),
                    &context,
                    DefEqBudget::unlimited()
                ),
                DefEqOutcome::Equal(_)
            ));
        }
    }
}
#[test]
fn partial_eliminators_wrong_levels_and_unregistered_names_stay_blocked() {
    let context = context();
    for call in [
        apps(
            primitive("lift", vec![Level::one(), Level::one()]),
            [nat(), free("r"), nat(), free("f"), free("respect")],
        ),
        apps(
            primitive("lift", vec![Level::one()]),
            [
                nat(),
                free("r"),
                nat(),
                free("f"),
                free("respect"),
                mk(free("a")),
            ],
        ),
        apps(
            primitive("ind", Vec::new()),
            [
                nat(),
                free("r"),
                free("motive"),
                free("minor"),
                mk(free("a")),
            ],
        ),
    ] {
        assert_eq!(normalized(&call, &context).reductions, 0);
    }
    let call = lift(free("f"), mk(free("a")));
    assert_eq!(normalized(&call, &WhnfContext::default()).reductions, 0);
    let incomplete = WhnfContext::new(
        Vec::new(),
        Vec::new(),
        environment_of(vec![quotient_entries()[2].clone()]),
    );
    assert_eq!(normalized(&call, &incomplete).reductions, 0);
}
#[test]
fn blocked_major_retains_beta_progress_and_reaches_a_fixed_point() {
    let context = context();
    let input = lift(free("f"), Expr::app(lam(Expr::bvar(0).unwrap()), free("q")));
    let result = normalized(&input, &context);
    assert_eq!(result.reductions, 1);
    same(&input, &lift(free("f"), free("q")), &context);
    let WhnfOutcome::Complete(again) = whnf(&result.term, &context, WhnfBudget::unlimited()) else {
        panic!("fixed point");
    };
    assert_eq!(again.reductions, 0);
    assert_eq!(result.term, again.term);
}
#[test]
fn demanding_a_local_major_does_not_poison_reuse_in_the_selected_branch() {
    let context = context();
    let local = WhnfContext::new(
        vec![FreeBinding::new(checker_name("q"), decoded(&mk(free("a"))))],
        Vec::new(),
        context.constants().clone(),
    );
    let call = lift(lam(free("q")), free("q"));
    same(&call, &mk(free("a")), &local);
}
#[test]
fn quotient_budget_stops_and_late_cancellation_do_not_poison_recovery() {
    let context = context();
    let input = decoded(&lift(lam(Expr::bvar(0).unwrap()), mk(free("a"))));
    let WhnfOutcome::Complete(full) = whnf(&input, &context, WhnfBudget::unlimited()) else {
        panic!("reduces");
    };
    for budget in [
        WhnfBudget::new(full.steps - 1, u64::MAX, TermBudget::unlimited()),
        WhnfBudget::new(u64::MAX, full.reductions - 1, TermBudget::unlimited()),
    ] {
        assert!(matches!(
            whnf(&input, &context, budget),
            WhnfOutcome::Inconclusive(_)
        ));
    }
    let mut total = 0;
    assert!(matches!(
        whnf_with(&input, &context, WhnfBudget::unlimited(), || {
            total += 1;
            false
        }),
        WhnfOutcome::Complete(_)
    ));
    let mut count = 0;
    assert!(matches!(
        whnf_with(&input, &context, WhnfBudget::unlimited(), || {
            count += 1;
            count == total - 1
        }),
        WhnfOutcome::Inconclusive(_)
    ));
    let WhnfOutcome::Complete(recovered) = whnf(&input, &context, WhnfBudget::unlimited()) else {
        panic!("recovers");
    };
    assert_eq!(full, recovered);
}
#[test]
fn nested_quotient_majors_use_heap_continuations_on_a_small_stack() {
    let context = context();
    // Construct and drop primary expressions on the ordinary test stack. The
    // small-stack worker receives only independent checker-owned flat arenas.
    let mut term = mk(free("a"));
    for _ in 0..2000 {
        term = lift(lam(mk(Expr::bvar(0).unwrap())), term);
    }
    let input = decoded(&term);
    let expected = decoded(&mk(free("a")));
    std::thread::Builder::new()
        .stack_size(64 * 1024)
        .spawn(move || {
            let WhnfOutcome::Complete(result) = whnf(&input, &context, WhnfBudget::unlimited())
            else {
                panic!("bounded-stack reduction");
            };
            assert!(matches!(
                def_eq(&result.term, &expected, &context, DefEqBudget::unlimited()),
                DefEqOutcome::Equal(_)
            ));
        })
        .unwrap()
        .join()
        .unwrap();
}
