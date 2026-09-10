//! Conversion regressions using independently admitted recursor metadata.
#![forbid(unsafe_code)]
use super::*;
use fln_checker::defeq::{DefEqOutcome, def_eq, def_eq_with};
use fln_checker::whnf::{FreeBinding, WhnfContext};
use fln_core::expr::FVarId;

fn context() -> WhnfContext {
    let entries = nat_entries();
    let verdict = admit_inductive(
        &ConstantEnvironment::empty(),
        &entries,
        AdmissionBudget::unlimited(),
        EnvironmentBudget::unlimited(),
    );
    assert!(verdict.is_admitted(), "{verdict:?}");
    WhnfContext::new(Vec::new(), Vec::new(), environment_of(entries))
}
fn nat() -> Expr {
    Expr::const_(primary_name("Nat"), Vec::new())
}
fn zero() -> Expr {
    Expr::const_(Name::from_components(["Nat", "zero"]), Vec::new())
}
fn succ(n: Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_components(["Nat", "succ"]), Vec::new()),
        n,
    )
}
fn bv(n: u32) -> Expr {
    Expr::bvar(n).unwrap()
}
fn lam(domain: Expr, body: Expr) -> Expr {
    Expr::lam(Name::anonymous(), domain, body, BinderInfo::Default)
}
fn beta(term: Expr) -> Expr {
    Expr::app(lam(nat(), bv(0)), term)
}
fn recursor(result: Expr, zero_case: Expr, step: Expr) -> Expr {
    [lam(nat(), result), zero_case, step].into_iter().fold(
        Expr::const_(Name::from_components(["Nat", "rec"]), vec![Level::one()]),
        Expr::app,
    )
}
fn assert_equal(left: Expr, right: Expr, context: &WhnfContext) {
    for (a, b) in [(&left, &right), (&right, &left)] {
        let outcome = def_eq(&decoded(a), &decoded(b), context, DefEqBudget::unlimited());
        assert!(matches!(outcome, DefEqOutcome::Equal(_)), "{outcome:?}");
    }
}

#[test]
fn saturated_iota_is_reduced_before_tearing_off_the_major_argument() {
    let context = context();
    // A recursor application and a constructor application have different
    // arities. Congruence before iota would strip the major off the former.
    let step = lam(nat(), lam(nat(), succ(bv(1))));
    for n in [0, 1, 4, 1024] {
        let major = Expr::lit(Literal::Nat(NatLit::from_u64(n)));
        let left = Expr::app(recursor(nat(), zero(), step.clone()), major.clone());
        assert_equal(succ(left), succ(major), &context);
    }
}

#[test]
fn recursor_reduction_retains_function_result_arguments() {
    let context = context();
    let function_type = primary_pi("x", BinderInfo::Default, nat(), nat());
    let step = lam(nat(), lam(function_type.clone(), lam(nat(), succ(bv(0)))));
    let rec = recursor(function_type, lam(nat(), bv(0)), step);
    let call = Expr::app(Expr::app(rec, succ(zero())), succ(succ(zero())));
    assert_equal(call, succ(succ(succ(zero()))), &context);
}

#[test]
fn neutral_and_partial_recursors_keep_sufficient_congruence() {
    let context = context();
    let n = Expr::fvar(FVarId(primary_name("neutral_n")));
    let plain = recursor(nat(), zero(), lam(nat(), lam(nat(), bv(1))));
    let converted = recursor(nat(), beta(zero()), lam(nat(), lam(nat(), beta(bv(1)))));
    assert_equal(plain.clone(), converted.clone(), &context);
    assert_equal(
        Expr::app(plain.clone(), n.clone()),
        Expr::app(converted, n.clone()),
        &context,
    );
    let wrong = recursor(nat(), zero(), lam(nat(), lam(nat(), bv(0))));
    let outcome = def_eq(
        &decoded(&Expr::app(plain, n.clone())),
        &decoded(&Expr::app(wrong, n)),
        &context,
        DefEqBudget::unlimited(),
    );
    assert!(!matches!(outcome, DefEqOutcome::Equal(_)), "{outcome:?}");
}

#[test]
fn a_local_major_is_demanded_and_stops_remain_recoverable_nonanswers() {
    let base = context();
    let context = WhnfContext::new(
        vec![FreeBinding::new(
            checker_name("major"),
            decoded(&succ(zero())),
        )],
        Vec::new(),
        base.constants().clone(),
    );
    let call = Expr::app(
        recursor(nat(), zero(), lam(nat(), lam(nat(), succ(bv(1))))),
        Expr::fvar(FVarId(primary_name("major"))),
    );
    let expected = succ(zero());
    let left = decoded(&call);
    let right = decoded(&expected);
    assert!(matches!(
        def_eq_with(&left, &right, &context, DefEqBudget::unlimited(), || true),
        DefEqOutcome::Inconclusive(_)
    ));
    let mut budget = DefEqBudget::unlimited();
    budget.max_normalizations = 0;
    assert!(matches!(
        def_eq(&left, &right, &context, budget),
        DefEqOutcome::Inconclusive(_)
    ));
    assert_equal(call, expected, &context);
}
