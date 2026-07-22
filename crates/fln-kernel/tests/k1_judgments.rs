//! K1 bootstrap judgment tests (bead franken_lean-zht), each tagged to its
//! KERNEL_CONTRACT.md rule and driven ONLY through the public authority
//! (`check` / `check_def_eq`) — the kernel has no other door.

#![forbid(unsafe_code)]

use fln_core::expr::{BinderInfo, Expr};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_env::constants::{
    AxiomVal, ConstantInfo, ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints,
    TheoremVal,
};
use fln_env::environment::Environment;
use fln_kernel::verdict::{Budget, ExhaustionReason, RejectClass, Verdict};
use fln_kernel::{Declaration, check, check_def_eq};

fn n(s: &str) -> Name {
    Name::str(Name::anonymous(), s)
}

fn sort1() -> Expr {
    Expr::sort(Level::one())
}

fn prop() -> Expr {
    Expr::sort(Level::zero())
}

fn axiom(name: &str, type_: Expr) -> Declaration {
    Declaration::Axiom(AxiomVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![],
            type_,
        },
        is_unsafe: false,
    })
}

fn defn(name: &str, type_: Expr, value: Expr) -> Declaration {
    Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![],
            type_,
        },
        value,
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Safe,
        all: vec![n(name)],
    })
}

fn admit(env: &Environment, decl: &Declaration) -> Environment {
    let verdict = check(env, decl, Budget::DEFAULT);
    assert!(
        verdict.is_accepted(),
        "expected acceptance, got {verdict:?}"
    );
    let info = match decl.clone() {
        Declaration::Axiom(v) => ConstantInfo::Axiom(v),
        Declaration::Defn(v) => ConstantInfo::Defn(v),
        Declaration::Thm(v) => ConstantInfo::Thm(v),
    };
    env.add_decl(info).expect("kernel-accepted decl adds")
}

fn reject_class(verdict: &Verdict) -> Option<RejectClass> {
    match verdict {
        Verdict::Rejected { class, .. } => Some(*class),
        _ => None,
    }
}

#[test]
fn kr104_kr972_a_sort_typed_axiom_is_admitted() {
    let env = Environment::new();
    let verdict = check(&env, &axiom("A", sort1()), Budget::DEFAULT);
    assert!(verdict.is_accepted(), "{verdict:?}");
}

#[test]
fn kr970_the_one_name_one_constant_law() {
    let env = admit(&Environment::new(), &axiom("A", sort1()));
    let verdict = check(&env, &axiom("A", sort1()), Budget::DEFAULT);
    assert_eq!(reject_class(&verdict), Some(RejectClass::AlreadyDeclared));
}

#[test]
fn kr971_duplicate_level_params_are_rejected() {
    let env = Environment::new();
    let decl = Declaration::Axiom(AxiomVal {
        base: ConstantVal {
            name: n("A"),
            level_params: vec![n("u"), n("u")],
            type_: Expr::sort(Level::param(n("u"))),
        },
        is_unsafe: false,
    });
    let verdict = check(&env, &decl, Budget::DEFAULT);
    assert_eq!(
        reject_class(&verdict),
        Some(RejectClass::DuplicateLevelParams)
    );
}

#[test]
fn kr140_undefined_level_params_are_rejected() {
    let env = Environment::new();
    let decl = Declaration::Axiom(AxiomVal {
        base: ConstantVal {
            name: n("A"),
            level_params: vec![],
            type_: Expr::sort(Level::param(n("u"))),
        },
        is_unsafe: false,
    });
    let verdict = check(&env, &decl, Budget::DEFAULT);
    assert_eq!(
        reject_class(&verdict),
        Some(RejectClass::UndefinedLevelParam)
    );
}

#[test]
fn kr100_loose_bvars_are_a_typed_rejection() {
    let env = Environment::new();
    let loose = Expr::bvar(0).expect("packs");
    let verdict = check(&env, &axiom("A", loose), Budget::DEFAULT);
    assert_eq!(reject_class(&verdict), Some(RejectClass::LooseBVar));
}

#[test]
fn kr103_metavariables_are_a_typed_rejection() {
    let env = Environment::new();
    let mvar = Expr::mvar(fln_core::expr::MVarId(n("m")));
    let verdict = check(&env, &axiom("A", mvar), Budget::DEFAULT);
    assert_eq!(reject_class(&verdict), Some(RejectClass::MVarInKernel));
}

#[test]
fn kr105_universe_arity_is_checked() {
    // A.{u} : Sort u, then a body referencing A with zero levels.
    let poly = Declaration::Axiom(AxiomVal {
        base: ConstantVal {
            name: n("A"),
            level_params: vec![n("u")],
            type_: Expr::sort(Level::param(n("u")).succ().expect("packs")),
        },
        is_unsafe: false,
    });
    let env = admit(&Environment::new(), &poly);
    let bad = axiom("B", Expr::const_(n("A"), vec![]));
    let verdict = check(&env, &bad, Budget::DEFAULT);
    assert_eq!(
        reject_class(&verdict),
        Some(RejectClass::UniverseArityMismatch)
    );
}

#[test]
fn kr107_kr108_the_polymorphic_identity_function_checks() {
    // def id : ∀ (α : Sort 1) (x : α), α := fun (α : Sort 1) (x : α) => x
    let ty = Expr::forall_e(
        n("alpha"),
        sort1(),
        Expr::forall_e(
            n("x"),
            Expr::bvar(0).expect("packs"),
            Expr::bvar(1).expect("packs"),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let value = Expr::lam(
        n("alpha"),
        sort1(),
        Expr::lam(
            n("x"),
            Expr::bvar(0).expect("packs"),
            Expr::bvar(0).expect("packs"),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let verdict = check(&Environment::new(), &defn("id", ty, value), Budget::DEFAULT);
    assert!(verdict.is_accepted(), "{verdict:?}");
}

#[test]
fn kr108_kr500_prop_impredicativity_via_imax() {
    // thm t : ∀ (p : Prop) (h : p), p := fun p h => h — the ∀ lives in Prop
    // because imax 1 0 = 0 (KR-108 + KR-500), so the THEOREM admits.
    let ty = Expr::forall_e(
        n("p"),
        prop(),
        Expr::forall_e(
            n("h"),
            Expr::bvar(0).expect("packs"),
            Expr::bvar(1).expect("packs"),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let value = Expr::lam(
        n("p"),
        prop(),
        Expr::lam(
            n("h"),
            Expr::bvar(0).expect("packs"),
            Expr::bvar(0).expect("packs"),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let decl = Declaration::Thm(TheoremVal {
        base: ConstantVal {
            name: n("t"),
            level_params: vec![],
            type_: ty,
        },
        value,
        all: vec![n("t")],
    });
    let verdict = check(&Environment::new(), &decl, Budget::DEFAULT);
    assert!(verdict.is_accepted(), "{verdict:?}");
}

#[test]
fn kr974_theorems_must_be_propositions() {
    let decl = Declaration::Thm(TheoremVal {
        base: ConstantVal {
            name: n("t"),
            level_params: vec![],
            type_: sort1(),
        },
        value: prop(),
        all: vec![n("t")],
    });
    let verdict = check(&Environment::new(), &decl, Budget::DEFAULT);
    assert_eq!(reject_class(&verdict), Some(RejectClass::TheoremNotProp));
}

#[test]
fn kr974_body_type_mismatch_is_rejected() {
    // bad : ∀ (α : Sort 1), α  :=  fun (α : Sort 1) => α — body type is
    // ∀ α, Sort 1, not ∀ α, α.
    let ty = Expr::forall_e(
        n("alpha"),
        sort1(),
        Expr::bvar(0).expect("packs"),
        BinderInfo::Default,
    );
    let value = Expr::lam(
        n("alpha"),
        sort1(),
        Expr::bvar(0).expect("packs"),
        BinderInfo::Default,
    );
    // value type: ∀ α : Sort 1, Sort 1... wait: body IS the bound α, so the body
    // type is α's type = Sort 1, giving ∀ α, Sort 1 ≠ ∀ α, α.
    let verdict = check(
        &Environment::new(),
        &defn("bad", ty, value),
        Budget::DEFAULT,
    );
    assert_eq!(
        reject_class(&verdict),
        Some(RejectClass::DefinitionTypeMismatch)
    );
}

#[test]
fn kr202_beta_and_kr203_zeta_in_defeq() {
    let env = admit(&Environment::new(), &axiom("A", sort1()));
    let a = Expr::const_(n("A"), vec![]);
    // (fun (x : Sort 1) => x) A  ≟  A
    let beta = Expr::app(
        Expr::lam(
            n("x"),
            sort1(),
            Expr::bvar(0).expect("packs"),
            BinderInfo::Default,
        ),
        a.clone(),
    );
    assert!(check_def_eq(&env, &[], &beta, &a, Budget::DEFAULT).is_accepted());
    // let x := A; x  ≟  A
    let zeta = Expr::let_e(
        n("x"),
        sort1(),
        a.clone(),
        Expr::bvar(0).expect("packs"),
        false,
    );
    assert!(check_def_eq(&env, &[], &zeta, &a, Budget::DEFAULT).is_accepted());
}

#[test]
fn kr200_kr309_delta_unfolds_definitions() {
    let env = admit(&Environment::new(), &axiom("A", sort1()));
    let a = Expr::const_(n("A"), vec![]);
    let env = admit(&env, &defn("d", sort1(), a.clone()));
    let d = Expr::const_(n("d"), vec![]);
    assert!(check_def_eq(&env, &[], &d, &a, Budget::DEFAULT).is_accepted());
    // And through one more layer: e := d.
    let env = admit(&env, &defn("e", sort1(), d.clone()));
    let e = Expr::const_(n("e"), vec![]);
    assert!(check_def_eq(&env, &[], &e, &a, Budget::DEFAULT).is_accepted());
}

#[test]
fn kr312_function_eta() {
    // f : Sort 1 → Sort 1 (axiom); (fun x => f x) ≟ f.
    let arrow = Expr::forall_e(n("x"), sort1(), sort1(), BinderInfo::Default);
    let env = admit(&Environment::new(), &axiom("f", arrow));
    let f = Expr::const_(n("f"), vec![]);
    let expanded = Expr::lam(
        n("x"),
        sort1(),
        Expr::app(f.clone(), Expr::bvar(0).expect("packs")),
        BinderInfo::Default,
    );
    assert!(check_def_eq(&env, &[], &expanded, &f, Budget::DEFAULT).is_accepted());
}

#[test]
fn kr306_proof_irrelevance_in_prop() {
    // p : Prop; h1 h2 : p — proofs are definitionally equal.
    let env = admit(&Environment::new(), &axiom("p", prop()));
    let p = Expr::const_(n("p"), vec![]);
    let env = admit(&env, &axiom("h1", p.clone()));
    let env = admit(&env, &axiom("h2", p.clone()));
    let h1 = Expr::const_(n("h1"), vec![]);
    let h2 = Expr::const_(n("h2"), vec![]);
    assert!(check_def_eq(&env, &[], &h1, &h2, Budget::DEFAULT).is_accepted());
}

#[test]
fn kr306_proof_irrelevance_does_not_leak_to_type() {
    // THE soundness boundary of KR-306: proof irrelevance must fire ONLY in Prop.
    // T : Sort 1 (a genuine type, NOT a proposition); a b : T are DISTINCT data.
    // If they were made defeq, the kernel would equate distinct inhabitants of a
    // Type — an unsoundness. This kills any `is_prop` that admits Sort 1.
    let env = admit(&Environment::new(), &axiom("T", sort1()));
    let t = Expr::const_(n("T"), vec![]);
    let env = admit(&env, &axiom("a", t.clone()));
    let env = admit(&env, &axiom("b", t.clone()));
    let a = Expr::const_(n("a"), vec![]);
    let b = Expr::const_(n("b"), vec![]);
    let verdict = check_def_eq(&env, &[], &a, &b, Budget::DEFAULT);
    assert_eq!(
        reject_class(&verdict),
        Some(RejectClass::NotDefEq),
        "proof irrelevance leaked out of Prop into Type — UNSOUND: {verdict:?}"
    );
}

#[test]
fn kr306_proof_irrelevance_requires_defeq_propositions() {
    // The other half of KR-306's guard: two proofs of DIFFERENT propositions are
    // NOT definitionally equal. p and q are distinct Props; hp : p, hq : q. If the
    // type-equality half of proof irrelevance were dropped, every proof would be
    // defeq to every other — catastrophically unsound. `kr306_..._in_prop` cannot
    // catch that (it uses one shared prop); this test does.
    let env = admit(&Environment::new(), &axiom("p", prop()));
    let env = admit(&env, &axiom("q", prop()));
    let p = Expr::const_(n("p"), vec![]);
    let q = Expr::const_(n("q"), vec![]);
    let env = admit(&env, &axiom("hp", p.clone()));
    let env = admit(&env, &axiom("hq", q.clone()));
    let hp = Expr::const_(n("hp"), vec![]);
    let hq = Expr::const_(n("hq"), vec![]);
    let verdict = check_def_eq(&env, &[], &hp, &hq, Budget::DEFAULT);
    assert_eq!(
        reject_class(&verdict),
        Some(RejectClass::NotDefEq),
        "proofs of distinct propositions were equated — UNSOUND: {verdict:?}"
    );
}

#[test]
fn distinct_axioms_are_not_defeq() {
    let env = admit(&Environment::new(), &axiom("A", sort1()));
    let env = admit(&env, &axiom("B", sort1()));
    let a = Expr::const_(n("A"), vec![]);
    let b = Expr::const_(n("B"), vec![]);
    let verdict = check_def_eq(&env, &[], &a, &b, Budget::DEFAULT);
    assert_eq!(reject_class(&verdict), Some(RejectClass::NotDefEq));
}

#[test]
fn fl_inv_07_exhaustion_is_inconclusive_never_rejected() {
    // The identity-function check under a 5-step budget: must be Inconclusive
    // with a consumption profile — categorically NOT a rejection.
    let ty = Expr::forall_e(
        n("alpha"),
        sort1(),
        Expr::forall_e(
            n("x"),
            Expr::bvar(0).expect("packs"),
            Expr::bvar(1).expect("packs"),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let value = Expr::lam(
        n("alpha"),
        sort1(),
        Expr::lam(
            n("x"),
            Expr::bvar(0).expect("packs"),
            Expr::bvar(0).expect("packs"),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let tiny = Budget {
        steps: 5,
        depth: 4096,
    };
    let verdict = check(
        &Environment::new(),
        &defn("id", ty.clone(), value.clone()),
        tiny,
    );
    assert!(
        matches!(
            &verdict,
            Verdict::Inconclusive {
                reason: ExhaustionReason::Steps,
                ..
            }
        ),
        "FL-INV-07 violated: expected Steps-exhaustion Inconclusive, got {verdict:?}"
    );
    if let Verdict::Inconclusive { consumption, .. } = &verdict {
        assert!(consumption.steps_used >= 5);
    }
    assert!(!verdict.is_rejected() && !verdict.is_accepted());

    // Depth exhaustion likewise.
    let shallow = Budget {
        steps: 1_000_000,
        depth: 1,
    };
    let verdict = check(&Environment::new(), &defn("id", ty, value), shallow);
    assert!(
        matches!(
            verdict,
            Verdict::Inconclusive {
                reason: ExhaustionReason::Depth,
                ..
            }
        ),
        "{verdict:?}"
    );
}

#[test]
fn kr106_application_type_mismatch() {
    // f : Prop → Prop applied to Sort 1's inhabitant type: (f A) with A : Sort 1
    // must reject at the application.
    let arrow = Expr::forall_e(n("x"), prop(), prop(), BinderInfo::Default);
    let env = admit(&Environment::new(), &axiom("f", arrow));
    let env = admit(&env, &axiom("A", sort1()));
    let bad_app = Expr::app(Expr::const_(n("f"), vec![]), Expr::const_(n("A"), vec![]));
    // Admitting a definition whose body contains the ill-typed application.
    let verdict = check(&env, &defn("bad", prop(), bad_app), Budget::DEFAULT);
    assert_eq!(reject_class(&verdict), Some(RejectClass::TypeMismatch));
}
