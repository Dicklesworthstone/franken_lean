//! K1 bootstrap judgment tests (bead franken_lean-zht), each tagged to its
//! KERNEL_CONTRACT.md rule and driven ONLY through the public authority
//! (`check` / `check_def_eq`) — the kernel has no other door.

#![forbid(unsafe_code)]

use fln_core::expr::{BinderInfo, Expr};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_env::constants::{
    AxiomVal, ConstantInfo, ConstantVal, ConstructorVal, DefinitionSafety, DefinitionVal,
    InductiveVal, ReducibilityHints, TheoremVal,
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

// ---- KR-112 projection inference (previously untested) ------------------------------

/// Add a constant directly (the K1 kernel does not yet admit inductives/constructors;
/// projection inference reads them from the environment, so tests populate it — the
/// same door `admit` uses for axioms, minus the kernel check).
fn add_info(env: &Environment, info: ConstantInfo) -> Environment {
    env.add_decl(info).expect("adds")
}

/// A one-constructor structure `name : sort_type` whose constructor `ctor` takes the
/// given field types (no parameters, no indices).
fn add_structure(
    env: &Environment,
    name: &str,
    ctor: &str,
    sort_type: Expr,
    field_types: &[Expr],
) -> Environment {
    let mut ctor_ty = Expr::const_(n(name), vec![]);
    for field in field_types.iter().rev() {
        ctor_ty = Expr::forall_e(n("_f"), field.clone(), ctor_ty, BinderInfo::Default);
    }
    let ind = ConstantInfo::Induct(InductiveVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![],
            type_: sort_type,
        },
        num_params: 0,
        num_indices: 0,
        all: vec![n(name)],
        ctors: vec![n(ctor)],
        num_nested: 0,
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    });
    let env = add_info(env, ind);
    let ctor_info = ConstantInfo::Ctor(ConstructorVal {
        base: ConstantVal {
            name: n(ctor),
            level_params: vec![],
            type_: ctor_ty,
        },
        induct: n(name),
        cidx: 0,
        num_params: 0,
        num_fields: field_types.len() as u32,
        is_unsafe: false,
    });
    add_info(&env, ctor_info)
}

#[test]
fn kr112_projection_infers_the_field_type() {
    // D : Sort 1 (data); structure S : Sort 1 with mk : D → D → S; s : S.
    // `proj S 0 s` and `proj S 1 s` both have type D.
    let env = admit(&Environment::new(), &axiom("D", sort1()));
    let d = Expr::const_(n("D"), vec![]);
    let env = add_structure(&env, "S", "mk", sort1(), &[d.clone(), d.clone()]);
    let env = admit(&env, &axiom("s", Expr::const_(n("S"), vec![])));
    let s = Expr::const_(n("s"), vec![]);

    for idx in [0u64, 1] {
        let proj = Expr::proj(n("S"), idx, s.clone());
        let verdict = check(
            &env,
            &defn(&format!("px{idx}"), d.clone(), proj),
            Budget::DEFAULT,
        );
        assert!(verdict.is_accepted(), "proj S {idx} s : D — {verdict:?}");
    }

    // A projection asserted at the WRONG field type is a real mismatch.
    let env2 = admit(&env, &axiom("E", sort1()));
    let e = Expr::const_(n("E"), vec![]);
    let wrong = check(
        &env2,
        &defn("bad_ty", e, Expr::proj(n("S"), 0, s.clone())),
        Budget::DEFAULT,
    );
    assert_eq!(
        reject_class(&wrong),
        Some(RejectClass::DefinitionTypeMismatch),
        "proj S 0 s has type D, not E — {wrong:?}"
    );
}

#[test]
fn kr901_projection_cannot_leak_data_out_of_prop() {
    // THE soundness guard (KR-901): a Prop-valued structure whose field is a genuine
    // datum (D : Sort 1) must NOT let a projection extract that datum — otherwise the
    // kernel would pull data out of a proof, defeating proof irrelevance.
    // Pstruct : Prop, pmk : D → Pstruct, hp : Pstruct; `proj Pstruct 0 hp` is illegal.
    let env = admit(&Environment::new(), &axiom("D", sort1()));
    let d = Expr::const_(n("D"), vec![]);
    let env = add_structure(&env, "Pstruct", "pmk", prop(), std::slice::from_ref(&d));
    let env = admit(&env, &axiom("hp", Expr::const_(n("Pstruct"), vec![])));
    let hp = Expr::const_(n("hp"), vec![]);

    let leak = Expr::proj(n("Pstruct"), 0, hp);
    let verdict = check(&env, &defn("leak", d, leak), Budget::DEFAULT);
    assert_eq!(
        reject_class(&verdict),
        Some(RejectClass::InvalidProjection),
        "a non-Prop field was projected out of a Prop structure — UNSOUND: {verdict:?}"
    );

    // Control: an all-Prop structure projects its (Prop) field fine — the guard is
    // discriminating, not a blanket ban on projecting from Prop structures.
    let env = admit(&Environment::new(), &axiom("Q", prop()));
    let q = Expr::const_(n("Q"), vec![]);
    let env = add_structure(&env, "QBox", "qmk", prop(), std::slice::from_ref(&q));
    let env = admit(&env, &axiom("hq", Expr::const_(n("QBox"), vec![])));
    let hq = Expr::const_(n("hq"), vec![]);
    let ok = check(
        &env,
        &defn("unbox", q, Expr::proj(n("QBox"), 0, hq)),
        Budget::DEFAULT,
    );
    assert!(
        ok.is_accepted(),
        "projecting a Prop field from a Prop box is fine: {ok:?}"
    );
}

#[test]
fn kr310_same_constant_defeq_iff_levels_are_equivalent() {
    // F.{u} : Sort u — a universe-polymorphic axiom.
    let poly = Declaration::Axiom(AxiomVal {
        base: ConstantVal {
            name: n("F"),
            level_params: vec![n("u")],
            type_: Expr::sort(Level::param(n("u"))),
        },
        is_unsafe: false,
    });
    let env = admit(&Environment::new(), &poly);
    let u = Level::param(n("u"));

    // SOUNDNESS: F.{0} : Sort 0 and F.{1} : Sort 1 are DISTINCT constants; equating
    // them would be unsound. Kills a KR-310 that skips the per-level equivalence check.
    let f0 = Expr::const_(n("F"), vec![Level::zero()]);
    let f1 = Expr::const_(n("F"), vec![Level::one()]);
    let verdict = check_def_eq(&env, &[], &f0, &f1, Budget::DEFAULT);
    assert_eq!(
        reject_class(&verdict),
        Some(RejectClass::NotDefEq),
        "F.<0> and F.<1> must not be definitionally equal — UNSOUND: {verdict:?}"
    );

    // DISCRIMINATING: equivalent levels ARE defeq (max u u ≡ u), so KR-310 is not a
    // blanket rejection of same-name constants.
    let f_maxuu = Expr::const_(
        n("F"),
        vec![Level::max(u.clone(), u.clone()).expect("packs")],
    );
    let f_u = Expr::const_(n("F"), vec![u.clone()]);
    assert!(
        check_def_eq(&env, &[n("u")], &f_maxuu, &f_u, Budget::DEFAULT).is_accepted(),
        "F.<max u u> and F.<u> should be defeq (max u u normalizes to u)"
    );
}

#[test]
fn kr109_let_inference_zeta_substitutes_the_value_into_the_body_type() {
    // A : Sort 1; a : A. `def g : A := let x := a; x` — the let's body has type
    // `x`'s declared type A, and the returned declaration type must be that (with
    // the let-local zeta-substituted out), so g admits at type A.
    let env = admit(&Environment::new(), &axiom("A", sort1()));
    let a_ty = Expr::const_(n("A"), vec![]);
    let env = admit(&env, &axiom("a", a_ty.clone()));
    let a = Expr::const_(n("a"), vec![]);

    let body = Expr::let_e(
        n("x"),
        a_ty.clone(),
        a.clone(),
        Expr::bvar(0).expect("packs"), // the let-bound x
        false,
    );
    let ok = check(
        &env,
        &defn("g", a_ty.clone(), body.clone()),
        Budget::DEFAULT,
    );
    assert!(ok.is_accepted(), "let body infers to A: {ok:?}");

    // The declared type must actually be checked: asserting the WRONG type rejects.
    let env2 = admit(&env, &axiom("B", sort1()));
    let b_ty = Expr::const_(n("B"), vec![]);
    let wrong = check(&env2, &defn("g_bad", b_ty, body), Budget::DEFAULT);
    assert_eq!(
        reject_class(&wrong),
        Some(RejectClass::DefinitionTypeMismatch),
        "let body has type A, not B: {wrong:?}"
    );

    // KR-109 also checks the let VALUE against its ascribed type: `let x : A := b`
    // where b : B (≠ A) must reject at the let, not silently accept.
    let env3 = admit(&env2, &axiom("b", Expr::const_(n("B"), vec![])));
    let mistyped_let = Expr::let_e(
        n("x"),
        a_ty.clone(),                 // ascribed type A
        Expr::const_(n("b"), vec![]), // value b : B
        Expr::bvar(0).expect("packs"),
        false,
    );
    let bad_val = check(&env3, &defn("g_val", a_ty, mistyped_let), Budget::DEFAULT);
    assert_eq!(
        reject_class(&bad_val),
        Some(RejectClass::TypeMismatch),
        "let value b : B does not match ascribed type A: {bad_val:?}"
    );
}

#[test]
fn kr107_binder_domain_that_is_not_a_type_is_rejected() {
    // A : Sort 1; a : A (a term, not a type). `fun (x : a) => x` uses a term as a
    // binder domain — ensure_sort_of must reject it (KR-107/KR-108 well-formedness),
    // never treat a proof/datum as a type.
    let env = admit(&Environment::new(), &axiom("A", sort1()));
    let env = admit(&env, &axiom("a", Expr::const_(n("A"), vec![])));
    let a = Expr::const_(n("a"), vec![]);
    let bad_lam = Expr::lam(
        n("x"),
        a, // <- a term where a type is required
        Expr::bvar(0).expect("packs"),
        BinderInfo::Default,
    );
    let verdict = check(&env, &defn("bad", sort1(), bad_lam), Budget::DEFAULT);
    assert_eq!(
        reject_class(&verdict),
        Some(RejectClass::SortExpected),
        "a binder domain that is not a type must be rejected: {verdict:?}"
    );
}

#[test]
fn kr200_unsafe_definitions_are_not_delta_unfolded() {
    // The kernel treats unsafe/partial definitions as irreducible: they bypass the
    // logic's termination/consistency guarantees, so unfolding one in defeq could
    // import inconsistency. A SAFE def unfolds; an UNSAFE def with the same body
    // does NOT. Note: this property is guarded by defense-in-depth — BOTH
    // `unfold_definition` and `definition_height` gate on `safety == Safe`, so a
    // single-gate mutation is masked by the other; this test fails only if the
    // whole irreducibility mechanism is removed (both gates), which is the property
    // that actually matters for soundness.
    let env = admit(&Environment::new(), &axiom("A", sort1()));
    let a = Expr::const_(n("A"), vec![]);

    // safe d := A  →  d ≟ A holds (delta unfolds).
    let env = admit(&env, &defn("d_safe", sort1(), a.clone()));
    let d_safe = Expr::const_(n("d_safe"), vec![]);
    assert!(
        check_def_eq(&env, &[], &d_safe, &a, Budget::DEFAULT).is_accepted(),
        "a safe definition unfolds under delta"
    );

    // unsafe u := A  →  u ≟ A must NOT hold (never unfolded).
    let unsafe_def = Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: n("u_unsafe"),
            level_params: vec![],
            type_: sort1(),
        },
        value: a.clone(),
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Unsafe,
        all: vec![n("u_unsafe")],
    });
    let env = admit(&env, &unsafe_def);
    let u_unsafe = Expr::const_(n("u_unsafe"), vec![]);
    let verdict = check_def_eq(&env, &[], &u_unsafe, &a, Budget::DEFAULT);
    assert_eq!(
        reject_class(&verdict),
        Some(RejectClass::NotDefEq),
        "an unsafe definition must not be delta-unfolded by the kernel: {verdict:?}"
    );
}

#[test]
fn kr204_projection_of_a_constructor_reduces_to_the_field() {
    // D : Sort 1; d0, d1 : D; structure S : Sort 1 with mk : D → D → S.
    // whnf reduces `proj S i (mk d0 d1)` to the i-th field, so it is defeq to di
    // and NOT to the other field.
    let env = admit(&Environment::new(), &axiom("D", sort1()));
    let d = Expr::const_(n("D"), vec![]);
    let env = admit(&env, &axiom("d0", d.clone()));
    let env = admit(&env, &axiom("d1", d.clone()));
    let env = add_structure(&env, "S", "mk", sort1(), &[d.clone(), d.clone()]);

    let d0 = Expr::const_(n("d0"), vec![]);
    let d1 = Expr::const_(n("d1"), vec![]);
    let mk_app = Expr::app(
        Expr::app(Expr::const_(n("mk"), vec![]), d0.clone()),
        d1.clone(),
    );

    // proj 0 reduces to d0; proj 1 reduces to d1.
    let proj0 = Expr::proj(n("S"), 0, mk_app.clone());
    let proj1 = Expr::proj(n("S"), 1, mk_app.clone());
    assert!(
        check_def_eq(&env, &[], &proj0, &d0, Budget::DEFAULT).is_accepted(),
        "proj S 0 (mk d0 d1) should reduce to d0"
    );
    assert!(
        check_def_eq(&env, &[], &proj1, &d1, Budget::DEFAULT).is_accepted(),
        "proj S 1 (mk d0 d1) should reduce to d1"
    );
    // And it must NOT reduce to the wrong field.
    assert_eq!(
        reject_class(&check_def_eq(&env, &[], &proj0, &d1, Budget::DEFAULT)),
        Some(RejectClass::NotDefEq),
        "proj S 0 must not equal the second field d1"
    );
}

#[test]
fn kr202_over_applied_lambda_beta_reduces_and_reapplies() {
    // ((fun (x : Sort 1) => x) A) is `A` after beta; applied to an extra arg the
    // spine machinery must re-apply the leftover. Here: (fun x => x) reduces so
    // `(fun (x:Sort 1) => x) A ≟ A`, exercising batched beta over a collected spine.
    let env = admit(&Environment::new(), &axiom("A", sort1()));
    let env = admit(
        &env,
        &axiom(
            "f",
            Expr::forall_e(n("_"), sort1(), sort1(), BinderInfo::Default),
        ),
    );
    let a = Expr::const_(n("A"), vec![]);
    // id := fun (x : Sort 1) => x
    let id_lam = Expr::lam(
        n("x"),
        sort1(),
        Expr::bvar(0).expect("packs"),
        BinderInfo::Default,
    );
    // (id A) ≟ A  (single beta over a spine head that is itself a redex)
    let applied = Expr::app(id_lam.clone(), a.clone());
    assert!(
        check_def_eq(&env, &[], &applied, &a, Budget::DEFAULT).is_accepted(),
        "(fun x => x) A should beta-reduce to A"
    );
    // f (id A) ≟ f A — the redex under an application head reduces, congruence closes.
    let f = Expr::const_(n("f"), vec![]);
    let lhs = Expr::app(f.clone(), applied);
    let rhs = Expr::app(f, a);
    assert!(
        check_def_eq(&env, &[], &lhs, &rhs, Budget::DEFAULT).is_accepted(),
        "f ((fun x => x) A) should equal f A"
    );
}

#[test]
fn kr112_kr204_parameterized_structure_projection() {
    // A PARAMETERIZED structure exercises the param-instantiation loop in infer_proj
    // and the num_params offset in reduce_proj — the most complex projection path.
    //   Box (α : Sort 1) : Sort 1
    //   mk  : ∀ (α : Sort 1) (x : α), Box α        -- num_params = 1, num_fields = 1
    //   A : Sort 1, a : A
    //   proj Box 0 (mk A a)  infers to A  and reduces to a.
    let env = admit(&Environment::new(), &axiom("A", sort1()));
    let a_ty = Expr::const_(n("A"), vec![]);
    let env = admit(&env, &axiom("a", a_ty.clone()));

    // Box : ∀ (α : Sort 1), Sort 1
    let box_ty = Expr::forall_e(n("alpha"), sort1(), sort1(), BinderInfo::Default);
    let box_ind = ConstantInfo::Induct(InductiveVal {
        base: ConstantVal {
            name: n("Box"),
            level_params: vec![],
            type_: box_ty,
        },
        num_params: 1,
        num_indices: 0,
        all: vec![n("Box")],
        ctors: vec![n("mkBox")],
        num_nested: 0,
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    });
    let env = add_info(&env, box_ind);

    // mkBox : ∀ (α : Sort 1) (x : α), Box α
    let mk_ty = Expr::forall_e(
        n("alpha"),
        sort1(),
        Expr::forall_e(
            n("x"),
            Expr::bvar(0).expect("packs"), // α
            Expr::app(
                Expr::const_(n("Box"), vec![]),
                Expr::bvar(1).expect("packs"),
            ), // Box α
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let mk_ctor = ConstantInfo::Ctor(ConstructorVal {
        base: ConstantVal {
            name: n("mkBox"),
            level_params: vec![],
            type_: mk_ty,
        },
        induct: n("Box"),
        cidx: 0,
        num_params: 1,
        num_fields: 1,
        is_unsafe: false,
    });
    let env = add_info(&env, mk_ctor);

    let a = Expr::const_(n("a"), vec![]);
    // mkBox A a : Box A
    let mk_app = Expr::app(
        Expr::app(Expr::const_(n("mkBox"), vec![]), a_ty.clone()),
        a.clone(),
    );

    // Inference: proj Box 0 (mkBox A a) : A (the field type with α := A substituted).
    let proj = Expr::proj(n("Box"), 0, mk_app.clone());
    let inferred = check(
        &env,
        &defn("px", a_ty.clone(), proj.clone()),
        Budget::DEFAULT,
    );
    assert!(
        inferred.is_accepted(),
        "proj of a parameterized structure infers the field type A: {inferred:?}"
    );

    // Reduction: proj Box 0 (mkBox A a) reduces to the stored field a.
    assert!(
        check_def_eq(&env, &[], &proj, &a, Budget::DEFAULT).is_accepted(),
        "proj Box 0 (mkBox A a) should reduce to a"
    );

    // The param offset matters: asserting the wrong result type rejects.
    let env2 = admit(&env, &axiom("B", sort1()));
    let wrong = check(
        &env2,
        &defn("px_bad", Expr::const_(n("B"), vec![]), proj),
        Budget::DEFAULT,
    );
    assert_eq!(
        reject_class(&wrong),
        Some(RejectClass::DefinitionTypeMismatch),
        "the projected field has type A, not B: {wrong:?}"
    );
}
