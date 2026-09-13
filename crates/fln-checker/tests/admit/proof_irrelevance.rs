//! KR-305 at typed conversion sites, with independently authored wire fixtures.
#![forbid(unsafe_code)]
use super::*;
use fln_core::expr::FVarId;
fn c(label: &str) -> Expr {
    Expr::const_(primary_name(label), vec![])
}
fn app(f: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(f, Expr::app)
}
fn pi(domain: Expr, body: Expr) -> Expr {
    Expr::forall_e(primary_name("x"), domain, body, BinderInfo::Default)
}
fn lam(domain: Expr, body: Expr) -> Expr {
    Expr::lam(primary_name("x"), domain, body, BinderInfo::Default)
}
fn entry(label: &str, ty: Expr) -> ConstantEntry {
    ConstantEntry::new(
        checker_name(label),
        header(
            vec![],
            decoded(&ty),
            ConstantKind::Axiom,
            ConstantSafety::Safe,
        ),
    )
}
fn environment() -> ConstantEnvironment {
    environment_of(vec![
        entry("A", Expr::sort(Level::one())),
        entry("P", Expr::sort(Level::zero())),
        entry("Q", Expr::sort(Level::zero())),
        entry("p", c("P")),
        entry("q", c("P")),
        entry("other", c("Q")),
        entry("a", c("A")),
        entry("b", c("A")),
        entry("f", pi(c("P"), c("A"))),
        entry("g", pi(c("A"), c("P"))),
        entry("h", pi(c("A"), c("P"))),
        entry("T", pi(c("A"), Expr::sort(Level::one()))),
        entry("w", app(c("T"), [app(c("f"), [c("q")])])),
        entry("consume", pi(app(c("T"), [app(c("f"), [c("p")])]), c("A"))),
    ])
}
fn target(proof: Expr) -> Expr {
    app(c("T"), [app(c("f"), [proof])])
}
fn candidate(label: &str, ty: Expr, value: Expr) -> ConstantEntry {
    definition(label, decoded(&ty), decoded(&value))
}
fn accepted(env: &ConstantEnvironment, decl: &ConstantEntry) {
    let outcome = admit(env, decl, AdmissionBudget::unlimited());
    assert!(matches!(outcome, Verdict::Admitted(_)), "{outcome:?}");
}
fn refused(env: &ConstantEnvironment, decl: &ConstantEntry) {
    let outcome = admit(env, decl, AdmissionBudget::unlimited());
    assert!(
        matches!(outcome, Verdict::Rejected(_) | Verdict::Deferred(_)),
        "{outcome:?}"
    );
}
#[test]
fn typed_final_application_and_let_conversions_identify_only_proofs() {
    let env = environment();
    accepted(&env, &candidate("final", target(c("p")), c("w")));
    accepted(
        &env,
        &candidate("application", c("A"), app(c("consume"), [c("w")])),
    );
    accepted(
        &env,
        &candidate(
            "let",
            target(c("p")),
            Expr::let_e(
                primary_name("z"),
                target(c("p")),
                c("w"),
                Expr::bvar(0).unwrap(),
                false,
            ),
        ),
    );
    let body = lam(
        c("A"),
        lam(
            target(app(c("g"), [Expr::bvar(0).unwrap()])),
            Expr::bvar(0).unwrap(),
        ),
    );
    // The witness's dependent type is compared underneath both open binders.
    let expected = pi(
        c("A"),
        pi(
            target(app(c("g"), [Expr::bvar(0).unwrap()])),
            target(app(c("h"), [Expr::bvar(1).unwrap()])),
        ),
    );
    accepted(&env, &candidate("under_binders", expected, body));
}
#[test]
fn propositions_data_and_mismatched_domains_never_collapse() {
    let env = environment();
    refused(&env, &candidate("wrong_prop", c("P"), c("other")));
    refused(
        &env,
        &candidate(
            "wrong_data",
            app(c("T"), [c("a")]),
            Expr::let_e(
                primary_name("x"),
                app(c("T"), [c("b")]),
                c("w"),
                Expr::bvar(0).unwrap(),
                false,
            ),
        ),
    );
    refused(
        &env,
        &candidate("wrong_domain", pi(c("Q"), c("A")), lam(c("P"), c("a"))),
    );
    refused(
        &env,
        &candidate("not_a_proof", target(c("p")), app(c("f"), [c("a")])),
    );
    let left = pi(c("A"), pi(c("A"), app(c("T"), [Expr::bvar(0).unwrap()])));
    let right = pi(c("A"), pi(c("A"), app(c("T"), [Expr::bvar(1).unwrap()])));
    let mut rows = env
        .constants()
        .map(|(name, decl)| ConstantEntry::new(name.clone(), decl.clone()))
        .collect::<Vec<_>>();
    rows.push(entry("foreign_witness", right));
    refused(
        &environment_of(rows),
        &candidate("bound_capture", left, c("foreign_witness")),
    );
}
#[test]
fn equality_of_proofs_requires_conversion_of_their_propositions() {
    let mut rows = environment()
        .constants()
        .map(|(name, decl)| ConstantEntry::new(name.clone(), decl.clone()))
        .collect::<Vec<_>>();
    let d_type = pi(
        Expr::sort(Level::zero()),
        pi(Expr::bvar(0).unwrap(), Expr::sort(Level::one())),
    );
    rows.push(entry("D", d_type));
    rows.push(entry("dw", app(c("D"), [c("Q"), c("other")])));
    refused(
        &environment_of(rows),
        &candidate(
            "different_propositions",
            app(c("D"), [c("P"), c("p")]),
            c("dw"),
        ),
    );
}
#[test]
fn proof_arguments_cannot_hide_invalid_unused_annotations() {
    let env = environment();
    let bad = Expr::let_e(primary_name("ignored"), c("Q"), c("p"), c("w"), false);
    let outcome = admit(
        &env,
        &candidate("bad", target(c("p")), bad),
        AdmissionBudget::unlimited(),
    );
    assert!(
        matches!(outcome, Verdict::Rejected(_) | Verdict::Deferred(_)),
        "{outcome:?}"
    );
}
#[test]
fn a_symbolic_sort_is_not_assumed_propositional() {
    let u = Level::param(primary_name("u"));
    let a = FVarId(primary_name("A"));
    let p = FVarId(primary_name("p"));
    let q = FVarId(primary_name("q"));
    let f = FVarId(primary_name("f"));
    let t = FVarId(primary_name("T"));
    let w = FVarId(primary_name("w"));
    let locals = [
        (a.clone(), Expr::sort(u)),
        (p.clone(), Expr::fvar(a.clone())),
        (q.clone(), Expr::fvar(a.clone())),
        (f.clone(), pi(Expr::fvar(a.clone()), c("A"))),
        (t.clone(), pi(c("A"), Expr::sort(Level::one()))),
        (
            w.clone(),
            app(
                Expr::fvar(t.clone()),
                [app(Expr::fvar(f.clone()), [Expr::fvar(q.clone())])],
            ),
        ),
    ];
    let mut ty = app(Expr::fvar(t), [app(Expr::fvar(f), [Expr::fvar(p)])]);
    let mut body = Expr::fvar(w);
    for (id, domain) in locals.iter().rev() {
        ty = Expr::forall_e(
            id.0.clone(),
            domain.clone(),
            ty.abstract_fvar(id, 0).unwrap(),
            BinderInfo::Default,
        );
        body = Expr::lam(
            id.0.clone(),
            domain.clone(),
            body.abstract_fvar(id, 0).unwrap(),
            BinderInfo::Default,
        );
    }
    let decl = ConstantEntry::new(
        checker_name("symbolic"),
        ConstantDeclaration::definition(
            vec![checker_name("u")],
            decoded(&ty),
            ConstantSafety::Safe,
            DefinitionBody::new(
                decoded(&body),
                ReducibilityHint::Regular(0),
                DefinitionSafety::Safe,
                vec![],
            ),
        ),
    );
    refused(&environment(), &decl);
}
#[test]
fn cancellation_and_bounded_typed_conversion_are_recoverable() {
    let env = environment();
    let decl = candidate("final", target(c("p")), c("w"));
    let mut polls = 0u64;
    let result = admit_with(&env, &decl, AdmissionBudget::unlimited(), || {
        polls += 1;
        false
    });
    assert!(matches!(result, Verdict::Admitted(_)), "{result:?}");
    for threshold in [0, polls / 2, polls.saturating_sub(1)] {
        let mut count = 0;
        let result = admit_with(&env, &decl, AdmissionBudget::unlimited(), || {
            count += 1;
            count > threshold
        });
        assert!(
            matches!(result, Verdict::Inconclusive(_)),
            "{threshold}: {result:?}"
        );
    }
    let mut budget = AdmissionBudget::unlimited();
    budget.inference.max_steps = 0;
    assert!(matches!(
        admit(&env, &decl, budget),
        Verdict::Inconclusive(_)
    ));
    accepted(&env, &decl);
}

#[test]
fn typed_conversion_opens_deep_telescope_on_a_small_stack() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let mut left = target(c("p"));
            let mut right = target(c("q"));
            for _ in 0..64 {
                left = pi(c("A"), left);
                right = pi(c("A"), right);
            }
            let mut rows = environment()
                .constants()
                .map(|(n, d)| ConstantEntry::new(n.clone(), d.clone()))
                .collect::<Vec<_>>();
            rows.push(entry("deep_witness", right));
            accepted(
                &environment_of(rows),
                &candidate("deep", left, c("deep_witness")),
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn unsafe_proof_sources_do_not_gain_admission_from_irrelevance() {
    let mut rows = environment()
        .constants()
        .map(|(n, d)| ConstantEntry::new(n.clone(), d.clone()))
        .collect::<Vec<_>>();
    rows.push(ConstantEntry::new(
        checker_name("unsafe_proof"),
        header(
            vec![],
            decoded(&c("P")),
            ConstantKind::Axiom,
            ConstantSafety::Unsafe,
        ),
    ));
    let outcome = admit(
        &environment_of(rows),
        &candidate(
            "unsafe_body",
            target(c("p")),
            Expr::let_e(
                primary_name("bad"),
                c("P"),
                c("unsafe_proof"),
                c("w"),
                false,
            ),
        ),
        AdmissionBudget::unlimited(),
    );
    assert!(matches!(outcome, Verdict::Rejected(_)), "{outcome:?}");
}
