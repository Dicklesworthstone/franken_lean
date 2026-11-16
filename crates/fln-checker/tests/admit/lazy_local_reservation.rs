//! Binder-free `proof_conversion` queries under large `let`-bound local values
//! must not rescan `context.locals()` on every domain comparison.
//!
//! In `CategoryTheory.Limits.colimitLimitToLimitColimit_surjective`
//! (`Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit`), 99.64%
//! of `proof_conversion` steps were spent eagerly scanning 32 `let`-bound local
//! definitions (~12,600 nodes per call) into `Probe.reserved` even though over
//! 99% of calls discharged by congruence + proof irrelevance without opening
//! any fresh local (`local_fresh == 0`). Seeding `Probe.reserved` lazily on the
//! first fresh-local allocation mirrors `InferenceEngine::initialize_reserved_names`
//! while keeping fresh-local hygiene exact whenever binders or eta open a local.
#![forbid(unsafe_code)]
use super::*;

fn c(label: &str) -> Expr {
    Expr::const_(primary_name(label), vec![])
}

fn app(f: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(f, Expr::app)
}

fn arrow(domain: Expr, body: Expr) -> Expr {
    Expr::forall_e(primary_name("x"), domain, body, BinderInfo::Default)
}

fn pi(name: &str, domain: Expr, body: Expr) -> Expr {
    Expr::forall_e(primary_name(name), domain, body, BinderInfo::Default)
}

fn lam(name: &str, domain: Expr, body: Expr) -> Expr {
    Expr::lam(primary_name(name), domain, body, BinderInfo::Default)
}

fn let_in(name: &str, ty: Expr, value: Expr, body: Expr) -> Expr {
    Expr::let_e(primary_name(name), ty, value, body, false)
}

fn bv(index: u32) -> Expr {
    Expr::bvar(index).expect("small bound index")
}

fn ty() -> Expr {
    Expr::sort(Level::one())
}

fn prop() -> Expr {
    Expr::sort(Level::zero())
}

fn typed_axiom(label: &str, decl_ty: Expr) -> ConstantEntry {
    ConstantEntry::new(
        checker_name(label),
        header(
            vec![],
            decoded(&decl_ty),
            ConstantKind::Axiom,
            ConstantSafety::Safe,
        ),
    )
}

/// Build an unshared binary tree of `comb c0 c0` nodes (~`2^(depth+1)` nodes) so
/// `WireExpr` holds thousands of distinct arena nodes in `local.value()`.
fn comb_tree(depth: usize) -> Expr {
    if depth == 0 {
        c("c0")
    } else {
        let left = comb_tree(depth - 1);
        let right = app(c("comb"), [c("c0"), comb_tree(depth - 1)]);
        app(c("comb"), [left, right])
    }
}

fn environment() -> ConstantEnvironment {
    let t = c("T");
    // `P : T -> Prop`, `p q : (x : T) -> P x`, `h : (x : T) -> P x -> T`
    // `Q : T -> Prop`, `mkQ : (x : T) -> Q (h x (p x))`
    // `useQ : (x : T) -> Q (h x (q x)) -> Prop -> Prop`
    let p_ty = pi("x", t.clone(), app(c("P"), [bv(0)]));
    let h_ty = pi("x", t.clone(), arrow(app(c("P"), [bv(0)]), t.clone()));
    let mk_q_ty = pi(
        "x",
        t.clone(),
        app(c("Q"), [app(c("h"), [bv(0), app(c("p"), [bv(0)])])]),
    );
    let use_q_ty = pi(
        "x",
        t.clone(),
        arrow(
            app(c("Q"), [app(c("h"), [bv(0), app(c("q"), [bv(0)])])]),
            arrow(prop(), prop()),
        ),
    );
    let use_fn_ty = arrow(
        app(
            c("QF"),
            [lam(
                "z",
                t.clone(),
                app(c("h"), [bv(0), app(c("q"), [bv(0)])]),
            )],
        ),
        prop(),
    );
    environment_of(vec![
        typed_axiom("T", ty()),
        typed_axiom("c0", t.clone()),
        typed_axiom("c1", t.clone()),
        typed_axiom("comb", arrow(t.clone(), arrow(t.clone(), t.clone()))),
        typed_axiom("P", arrow(t.clone(), prop())),
        typed_axiom("p", p_ty.clone()),
        typed_axiom("q", p_ty),
        typed_axiom("h", h_ty),
        typed_axiom("Q", arrow(t.clone(), prop())),
        typed_axiom("mkQ", mk_q_ty),
        typed_axiom("useQ", use_q_ty),
        typed_axiom("TrueProp", prop()),
        typed_axiom("trivialProof", c("TrueProp")),
        typed_axiom("QF", arrow(arrow(t.clone(), t.clone()), prop())),
        typed_axiom(
            "mkQF",
            app(
                c("QF"),
                [lam("z", t, app(c("h"), [bv(0), app(c("p"), [bv(0)])]))],
            ),
        ),
        typed_axiom("useQF", use_fn_ty),
    ])
}

/// With a ~4,090-node `let` value in scope and 180 binder-free proof-conversion
/// domain checks, eager reservation scans >730,000 local-value nodes and
/// exhausts `STEP_BUDGET`; lazy reservation skips `ensure_reserved()` on every
/// binder-free call and settles well under `STEP_BUDGET`.
const STEP_BUDGET: u64 = 120_000;
const CALLS: usize = 180;

fn budget() -> AdmissionBudget {
    AdmissionBudget::new(
        InferenceBudget::new(
            STEP_BUDGET,
            u64::MAX,
            TermBudget::unlimited(),
            TermBudget::unlimited(),
        ),
        WhnfBudget::unlimited(),
        InferenceBudget::unlimited().defeq,
    )
}

#[test]
fn binder_free_proof_conversions_do_not_rescan_large_let_values() {
    let env = environment();
    let big = comb_tree(10);
    let mut chain = c("TrueProp");
    for _ in 0..CALLS {
        // `useQ c0 (mkQ c0) chain`: `mkQ c0 : Q (h c0 (p c0))` vs expected
        // `Q (h c0 (q c0))` defers to `proof_conversion` and settles by
        // congruence + proof irrelevance without opening any binder.
        chain = app(c("useQ"), [c("c0"), app(c("mkQ"), [c("c0")]), chain]);
    }
    let body = let_in("big", c("T"), big, chain);
    let candidate = definition("many_domain_checks", decoded(&prop()), decoded(&body));
    let verdict = admit(&env, &candidate, budget());
    assert!(matches!(verdict, Verdict::Admitted(_)), "{verdict:?}");
}

#[test]
fn distinct_value_under_large_let_context_is_still_not_admitted() {
    let env = environment();
    let big = comb_tree(10);
    let mut chain = c("TrueProp");
    for index in 0..CALLS {
        let arg = if index + 1 == CALLS { c("c1") } else { c("c0") };
        chain = app(c("useQ"), [c("c0"), app(c("mkQ"), [arg]), chain]);
    }
    let body = let_in("big", c("T"), big, chain);
    let candidate = definition("bad_domain_check", decoded(&prop()), decoded(&body));
    let verdict = admit(&env, &candidate, budget());
    assert!(
        matches!(
            verdict,
            Verdict::Deferred(AdmissionDeferred::BodyTypeInference { .. })
        ),
        "{verdict:?}"
    );
}

#[test]
fn binder_opening_proof_conversion_under_large_let_context_still_admits() {
    let env = environment();
    let big = comb_tree(10);
    let body = let_in("big", c("T"), big, app(c("useQF"), [c("mkQF")]));
    let candidate = definition("binder_domain_check", decoded(&prop()), decoded(&body));
    let verdict = admit(&env, &candidate, budget());
    assert!(matches!(verdict, Verdict::Admitted(_)), "{verdict:?}");
}
