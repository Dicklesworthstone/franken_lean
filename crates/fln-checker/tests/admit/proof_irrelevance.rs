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
fn proofs_that_differ_only_in_a_literal_are_still_one_proof() {
    // `mk 0` and `mk 1` are both proofs of `P`, so `T (f (mk 0))` and
    // `T (f (mk 1))` are one type. Untyped congruence reaches `0 ≟ 1` below
    // them and used to call the whole conversion unequal, rejecting a
    // declaration the Reference accepts (`Fin.zero_eq_one_iff`'s
    // `Nat.mod_lt 0 _` against `Nat.mod_lt 1 _`).
    let nat = |value: u64| {
        Expr::lit(fln_core::expr::Literal::Nat(
            fln_core::expr::NatLit::from_u64(value),
        ))
    };
    let mut rows = environment()
        .constants()
        .map(|(name, decl)| ConstantEntry::new(name.clone(), decl.clone()))
        .collect::<Vec<_>>();
    rows.push(entry("Nat", Expr::sort(Level::one())));
    rows.push(entry("mk", pi(c("Nat"), c("P"))));
    rows.push(entry("w0", target(app(c("mk"), [nat(0)]))));
    rows.push(entry("S", pi(c("Nat"), Expr::sort(Level::one()))));
    rows.push(entry("v", app(c("S"), [nat(0)])));
    let env = environment_of(rows);
    accepted(
        &env,
        &candidate("literal_proofs", target(app(c("mk"), [nat(1)])), c("w0")),
    );
    // The same literals as data stay distinct.
    refused(
        &env,
        &candidate("literal_data", app(c("S"), [nat(1)]), c("v")),
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

/// Both callers reach the typed lane only after untyped conversion has deferred
/// the root pair, so the lane must not ask untyped conversion that question
/// again. Measured in polls of the one cancellation hook: the declared type
/// `T (slow p)` and the body type `T (slow q)` differ only in a proof under
/// `slow`, which unfolds to a `WRAPS`-deep tower, so every untyped walk of the
/// pair costs about the same. Admission makes one before the lane, and the lane
/// needs one more, for `slow q ≟ slow p`, before proof irrelevance closes it.
/// Asking the root again would add a third.
#[test]
fn the_typed_lane_does_not_repeat_the_deferred_root_query() {
    use fln_checker::defeq::{DefEqOutcome, def_eq_with};
    use fln_checker::whnf::WhnfContext;
    const WRAPS: usize = 200;
    let bound = Expr::bvar(0).expect("bound variable");
    let tower = (0..WRAPS).fold(bound, |inner, _| app(c("wrapP"), [inner]));
    let slow = |proof: &str| app(c("slow"), [c(proof)]);
    let env = environment_of(vec![
        entry("P", Expr::sort(Level::zero())),
        entry("p", c("P")),
        entry("q", c("P")),
        entry("wrapP", pi(c("P"), c("P"))),
        entry("T", pi(c("P"), Expr::sort(Level::one()))),
        definition(
            "slow",
            decoded(&pi(c("P"), c("P"))),
            decoded(&lam(c("P"), tower)),
        ),
        entry("w", app(c("T"), [slow("q")])),
    ]);
    let declared = app(c("T"), [slow("p")]);
    let body_type = app(c("T"), [slow("q")]);

    let walk_polls = Cell::new(0_u64);
    let walk = def_eq_with(
        &decoded(&body_type),
        &decoded(&declared),
        &WhnfContext::new(Vec::new(), Vec::new(), env.clone()),
        DefEqBudget::unlimited(),
        || {
            walk_polls.set(walk_polls.get() + 1);
            false
        },
    );
    assert!(
        matches!(walk, DefEqOutcome::Deferred { .. }),
        "untyped conversion must defer the pair for this test to mean anything: {walk:?}"
    );
    let walk = walk_polls.get();
    assert!(
        walk > u64::try_from(WRAPS).expect("small"),
        "one walk: {walk} polls"
    );

    let candidate = definition("d", decoded(&declared), decoded(&c("w")));
    let polls = Cell::new(0_u64);
    let verdict = admit_with(&env, &candidate, AdmissionBudget::unlimited(), || {
        polls.set(polls.get() + 1);
        false
    });
    assert!(matches!(verdict, Verdict::Admitted(_)), "{verdict:?}");
    let admission = polls.get();
    assert!(
        2 * admission < 5 * walk,
        "admission polled {admission} times, at least two and a half untyped walks of the \
         deferred pair ({walk} each): the typed lane asked the root again"
    );
}

/// `T3 (slow a) (slow b) (slow c)`.
fn t3_of_slow(proofs: [&str; 3]) -> Expr {
    app(c("T3"), proofs.map(|proof| app(c("slow"), [c(proof)])))
}

/// `T3 : P → P → P → Type`, and `slow : P → P`, a regular definition unfolding
/// to a `WRAPS`-deep tower, so each argument pair `slow a ≟ slow b` costs the
/// typed lane one untyped walk before proof irrelevance closes it. `w` has type
/// `T3` over `witness`.
fn three_slow_proofs(witness: [&str; 3]) -> ConstantEnvironment {
    const WRAPS: usize = 200;
    let bound = Expr::bvar(0).expect("bound variable");
    let tower = (0..WRAPS).fold(bound, |inner, _| app(c("wrapP"), [inner]));
    environment_of(vec![
        entry("P", Expr::sort(Level::zero())),
        entry("p", c("P")),
        entry("q", c("P")),
        entry("wrapP", pi(c("P"), c("P"))),
        entry(
            "T3",
            pi(c("P"), pi(c("P"), pi(c("P"), Expr::sort(Level::one())))),
        ),
        definition(
            "slow",
            decoded(&pi(c("P"), c("P"))),
            decoded(&lam(c("P"), tower)),
        ),
        entry("w", t3_of_slow(witness)),
    ])
}

/// A task the typed lane has already taken on is not taken on again: the run
/// succeeds only if every task holds, so a repeat adds nothing. Here the one
/// argument obligation `slow q ≟ slow p` arises three times, once per
/// application layer, and is walked once.
#[test]
fn the_typed_lane_takes_on_each_obligation_once() {
    let env = three_slow_proofs(["q", "q", "q"]);
    let candidate = definition("d", decoded(&t3_of_slow(["p", "p", "p"])), decoded(&c("w")));
    let slow_polls = |left: &str, right: &str| {
        use fln_checker::defeq::def_eq_with;
        use fln_checker::whnf::WhnfContext;
        let polls = Cell::new(0_u64);
        let _ = def_eq_with(
            &decoded(&app(c("slow"), [c(left)])),
            &decoded(&app(c("slow"), [c(right)])),
            &WhnfContext::new(Vec::new(), Vec::new(), env.clone()),
            DefEqBudget::unlimited(),
            || {
                polls.set(polls.get() + 1);
                false
            },
        );
        polls.get()
    };
    let walk = slow_polls("q", "p");
    let polls = Cell::new(0_u64);
    let verdict = admit_with(&env, &candidate, AdmissionBudget::unlimited(), || {
        polls.set(polls.get() + 1);
        false
    });
    assert!(matches!(verdict, Verdict::Admitted(_)), "{verdict:?}");
    let admission = polls.get();
    assert!(
        2 * admission < 11 * walk,
        "admission polled {admission} times, at least five and a half walks of the \
         repeated argument pair ({walk} each): an obligation was taken on again"
    );
}

/// Two applications of one head whose arguments differ only in a proof are
/// equal by congruence, which the typed lane now tries first, as the pin tries
/// it before unfolding a regular definition. `U q (slow q)` against
/// `U p (slow p)`: untyped conversion defers at `q ≟ p` before it reaches the
/// `slow` pair, and the lane then closes `slow q ≟ slow p` by proof
/// irrelevance on `q ≟ p` without unfolding `slow`. Without the attempt, the
/// lane walks `slow q ≟ slow p` untyped first. Measured on
/// `utf8DecodeChar?_eq_assemble₄`, whose `b[0]` differ only in their bound
/// proofs: 941 s to an exhausted budget, then 5.6 s.
#[test]
fn a_proof_argument_under_one_head_closes_by_congruence() {
    use fln_checker::defeq::{DefEqOutcome, def_eq_with};
    use fln_checker::whnf::WhnfContext;
    const WRAPS: usize = 200;
    let bound = Expr::bvar(0).expect("bound variable");
    let tower = (0..WRAPS).fold(bound, |inner, _| app(c("wrapP"), [inner]));
    let slow = |proof: &str| app(c("slow"), [c(proof)]);
    let u = |proof: &str| app(c("U"), [c(proof), slow(proof)]);
    let env = environment_of(vec![
        entry("P", Expr::sort(Level::zero())),
        entry("p", c("P")),
        entry("q", c("P")),
        entry("wrapP", pi(c("P"), c("P"))),
        entry("U", pi(c("P"), pi(c("P"), Expr::sort(Level::one())))),
        definition(
            "slow",
            decoded(&pi(c("P"), c("P"))),
            decoded(&lam(c("P"), tower)),
        ),
        entry("w", u("q")),
    ]);
    let walk_polls = Cell::new(0_u64);
    let walk = def_eq_with(
        &decoded(&slow("q")),
        &decoded(&slow("p")),
        &WhnfContext::new(Vec::new(), Vec::new(), env.clone()),
        DefEqBudget::unlimited(),
        || {
            walk_polls.set(walk_polls.get() + 1);
            false
        },
    );
    assert!(
        matches!(walk, DefEqOutcome::Deferred { .. }),
        "untyped conversion must defer the pair for this test to mean anything: {walk:?}"
    );
    let walk = walk_polls.get();
    assert!(
        walk > u64::try_from(WRAPS).expect("small"),
        "one walk: {walk} polls"
    );
    let candidate = definition("d", decoded(&u("p")), decoded(&c("w")));
    let polls = Cell::new(0_u64);
    let verdict = admit_with(&env, &candidate, AdmissionBudget::unlimited(), || {
        polls.set(polls.get() + 1);
        false
    });
    assert!(matches!(verdict, Verdict::Admitted(_)), "{verdict:?}");
    let admission = polls.get();
    assert!(
        2 * admission < walk,
        "admission polled {admission} times, half an untyped walk of \
         `slow q ≟ slow p` ({walk}): the lane unfolded `slow` instead of trying \
         congruence"
    );
}

/// Congruence is only sufficient. `T2 (k b) q` against `T2 (k a) p` reaches the
/// typed lane, since untyped conversion defers the proofs `q ≟ p`. There the
/// attempt on `k b ≟ k a` fails, `b` and `a` being distinct data, although `k`
/// ignores its argument; the pair goes on to the rules that unfold `k`, and the
/// whole is admitted. Distinct data under a head that keeps it stays refused.
#[test]
fn a_pair_congruence_cannot_establish_takes_the_other_rules() {
    let t2 = |data: Expr, proof: &str| app(c("T2"), [data, c(proof)]);
    let env = environment_of(vec![
        entry("A", Expr::sort(Level::one())),
        entry("a", c("A")),
        entry("b", c("A")),
        entry("P", Expr::sort(Level::zero())),
        entry("p", c("P")),
        entry("q", c("P")),
        entry("T2", pi(c("A"), pi(c("P"), Expr::sort(Level::one())))),
        definition(
            "k",
            decoded(&pi(c("A"), c("A"))),
            decoded(&lam(c("A"), c("a"))),
        ),
        definition(
            "keep",
            decoded(&pi(c("A"), c("A"))),
            decoded(&lam(c("A"), Expr::bvar(0).expect("bound variable"))),
        ),
        entry("wk", t2(app(c("k"), [c("b")]), "q")),
        entry("wkeep", t2(app(c("keep"), [c("b")]), "q")),
    ]);
    accepted(
        &env,
        &candidate("ignored", t2(app(c("k"), [c("a")]), "p"), c("wk")),
    );
    refused(
        &env,
        &candidate("kept", t2(app(c("keep"), [c("a")]), "p"), c("wkeep")),
    );
}

/// A failed congruence attempt is not made again. `F` is an opaque constant, so
/// `S (Fⁿ b) ≟ S (Fⁿ a)` fails congruence at every depth, and each failure hands
/// its pair to the other rules, whose decomposition reaches the pair below
/// again. Remembering the failed attempts keeps the work polynomial in the
/// depth: doubling the depth multiplies it by far less than eight. Repeating
/// them would double it with every level, which the poll cap turns into an
/// inconclusive verdict instead of a hang.
#[test]
fn a_failed_congruence_attempt_is_not_made_again() {
    let chain =
        |depth: usize, base: &str| (0..depth).fold(c(base), |inner, _| app(c("F"), [inner]));
    let run = |depth: usize, cap: u64| {
        let env = environment_of(vec![
            entry("A", Expr::sort(Level::one())),
            entry("a", c("A")),
            entry("b", c("A")),
            entry("F", pi(c("A"), c("A"))),
            entry("S", pi(c("A"), Expr::sort(Level::one()))),
            entry("w", app(c("S"), [chain(depth, "b")])),
        ]);
        let candidate = definition(
            "d",
            decoded(&app(c("S"), [chain(depth, "a")])),
            decoded(&c("w")),
        );
        let polls = Cell::new(0_u64);
        let verdict = admit_with(&env, &candidate, AdmissionBudget::unlimited(), || {
            polls.set(polls.get() + 1);
            polls.get() > cap
        });
        (verdict, polls.get())
    };
    let (shallow, shallow_polls) = run(10, u64::MAX);
    assert!(
        matches!(shallow, Verdict::Rejected(_) | Verdict::Deferred(_)),
        "{shallow:?}"
    );
    let (deep, deep_polls) = run(20, 8 * shallow_polls);
    assert!(
        matches!(deep, Verdict::Rejected(_) | Verdict::Deferred(_)),
        "depth 20 did not finish within eight times depth 10's {shallow_polls} polls \
         ({deep_polls} polled): {deep:?}"
    );
}
