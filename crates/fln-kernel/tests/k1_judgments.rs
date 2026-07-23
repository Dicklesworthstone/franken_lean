//! K1 bootstrap judgment tests (bead franken_lean-zht), each tagged to its
//! KERNEL_CONTRACT.md rule and driven ONLY through the public authority
//! (`check` / `check_def_eq`) — the kernel has no other door.

#![forbid(unsafe_code)]

use fln_core::expr::{BinderInfo, Expr, Literal, NatLit};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_env::constants::{
    AxiomVal, ConstantInfo, ConstantVal, ConstructorVal, DefinitionSafety, DefinitionVal,
    InductiveVal, QuotKind, QuotVal, RecursorRule, RecursorVal, ReducibilityHints, TheoremVal,
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
    let rhs = Expr::app(f.clone(), a.clone());
    assert!(
        check_def_eq(&env, &[], &lhs, &rhs, Budget::DEFAULT).is_accepted(),
        "f ((fun x => x) A) should equal f A"
    );

    // Genuine OVER-application: (fun (h : Sort 1 → Sort 1) => h) f A applies the
    // function-identity to f (yielding f), then RE-APPLIES the leftover argument A —
    // exercising the spine machinery's `args[consumed..]` re-application path, which
    // the exact-application cases above never reach (their spines are fully consumed).
    let arrow = Expr::forall_e(n("_"), sort1(), sort1(), BinderInfo::Default);
    let fn_id = Expr::lam(
        n("h"),
        arrow,
        Expr::bvar(0).expect("packs"),
        BinderInfo::Default,
    );
    let over_applied = Expr::app(Expr::app(fn_id, f), a);
    assert!(
        check_def_eq(&env, &[], &over_applied, &rhs, Budget::DEFAULT).is_accepted(),
        "(fun h => h) f A should reduce to f A (leftover arg re-applied)"
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

#[test]
fn fl_inv_01_kernel_verdicts_are_deterministic() {
    // FL-INV-01 at the kernel: the same (environment, declaration, budget) yields a
    // byte-identical verdict INCLUDING its consumption profile, run after run — no
    // hidden nondeterminism (map iteration order, fresh-fvar counter leakage, etc.).
    let env = admit(&Environment::new(), &axiom("A", sort1()));
    let env = admit(&env, &axiom("B", sort1()));

    // A checked declaration: the polymorphic identity again (nontrivial traversal).
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
    let decl = defn("id", ty, value);
    let first = check(&env, &decl, Budget::DEFAULT);
    for _ in 0..8 {
        assert_eq!(
            check(&env, &decl, Budget::DEFAULT),
            first,
            "kernel acceptance verdict + consumption must be deterministic"
        );
    }
    assert!(first.is_accepted());

    // A rejection verdict is likewise stable (class, message, consumption).
    let a = Expr::const_(n("A"), vec![]);
    let b = Expr::const_(n("B"), vec![]);
    let neq = check_def_eq(&env, &[], &a, &b, Budget::DEFAULT);
    for _ in 0..8 {
        assert_eq!(
            check_def_eq(&env, &[], &a, &b, Budget::DEFAULT),
            neq,
            "kernel rejection verdict + consumption must be deterministic"
        );
    }
    assert_eq!(reject_class(&neq), Some(RejectClass::NotDefEq));
}

#[test]
fn kr110_literal_inference_maps_nat_and_string() {
    // Nat/String literals infer to the constants `Nat`/`String`. Stand-in axioms
    // provide those names (KR-110 returns the const without checking existence;
    // the surrounding declaration's declared type is what forces the name lookup).
    let env = admit(&Environment::new(), &axiom("Nat", sort1()));
    let env = admit(&env, &axiom("String", sort1()));
    let nat_ty = Expr::const_(n("Nat"), vec![]);
    let str_ty = Expr::const_(n("String"), vec![]);

    let nat_lit = Expr::lit(Literal::Nat(NatLit::from_u64(42)));
    let str_lit = Expr::lit(Literal::Str("hi".to_string()));

    assert!(
        check(
            &env,
            &defn("a", nat_ty.clone(), nat_lit.clone()),
            Budget::DEFAULT
        )
        .is_accepted(),
        "a Nat literal has type Nat"
    );
    assert!(
        check(
            &env,
            &defn("b", str_ty.clone(), str_lit.clone()),
            Budget::DEFAULT
        )
        .is_accepted(),
        "a String literal has type String"
    );
    // Cross-typed: a String literal ascribed type Nat must reject.
    assert_eq!(
        reject_class(&check(&env, &defn("c", nat_ty, str_lit), Budget::DEFAULT)),
        Some(RejectClass::DefinitionTypeMismatch),
        "a String literal is not a Nat"
    );
}

#[test]
fn kr111_kr201_mdata_is_transparent_to_typing_and_reduction() {
    // MData is metadata: `mdata m e` has e's type (KR-111) and whnf strips it
    // (KR-201), so it is defeq to e.
    let env = admit(&Environment::new(), &axiom("A", sort1()));
    let a_ty = Expr::const_(n("A"), vec![]);
    let env = admit(&env, &axiom("x", a_ty.clone()));
    let x = Expr::const_(n("x"), vec![]);
    let wrapped = Expr::mdata(KVMap::new(), x.clone());

    // Typing: mdata {} x : A.
    assert!(
        check(&env, &defn("f", a_ty, wrapped.clone()), Budget::DEFAULT).is_accepted(),
        "mdata is transparent to typing"
    );
    // Reduction/defeq: mdata {} x ≟ x.
    assert!(
        check_def_eq(&env, &[], &wrapped, &x, Budget::DEFAULT).is_accepted(),
        "whnf strips mdata"
    );
}

#[test]
fn kr303_sorts_are_defeq_iff_their_levels_are_equivalent() {
    // KR-303: Sort u ≟ Sort v iff u ≡ v. Sort (max 1 1) ≟ Sort 1 holds (levels
    // normalize equal); Sort 0 (Prop) ≟ Sort 1 does not.
    let env = Environment::new();
    let s1 = Expr::sort(Level::one());
    let s_max = Expr::sort(Level::max(Level::one(), Level::one()).expect("packs"));
    assert!(
        check_def_eq(&env, &[], &s_max, &s1, Budget::DEFAULT).is_accepted(),
        "Sort (max 1 1) and Sort 1 are defeq"
    );
    assert_eq!(
        reject_class(&check_def_eq(&env, &[], &prop(), &s1, Budget::DEFAULT)),
        Some(RejectClass::NotDefEq),
        "Sort 0 (Prop) and Sort 1 are distinct sorts"
    );
}

// ---- recursor reduction (KR-205/316/317/955; bead franken_lean-5p2) -----------------

/// Shorthand for a dotted two-segment name, e.g. `nn("E", "a")` = `E.a`.
fn nn(outer: &str, inner: &str) -> Name {
    Name::str(n(outer), inner)
}

/// A two-constructor enum `E : Sort 1` with nullary constructors `E.a`/`E.b` and
/// the standard recursor `E.rec.{u} : ∀ (motive : E → Sort u) (ca : motive E.a)
/// (cb : motive E.b) (t : E), motive t` — each rule returning its own minor.
fn add_enum_e(env: &Environment) -> Environment {
    let e = n("E");
    let env = add_info(
        env,
        ConstantInfo::Induct(InductiveVal {
            base: ConstantVal {
                name: e.clone(),
                level_params: vec![],
                type_: sort1(),
            },
            num_params: 0,
            num_indices: 0,
            all: vec![e.clone()],
            ctors: vec![nn("E", "a"), nn("E", "b")],
            num_nested: 0,
            is_rec: false,
            is_unsafe: false,
            is_reflexive: false,
        }),
    );
    let mut env = env;
    for (idx, ctor) in ["a", "b"].iter().enumerate() {
        env = add_info(
            &env,
            ConstantInfo::Ctor(ConstructorVal {
                base: ConstantVal {
                    name: nn("E", ctor),
                    level_params: vec![],
                    type_: Expr::const_(e.clone(), vec![]),
                },
                induct: e.clone(),
                cidx: idx as u32,
                num_params: 0,
                num_fields: 0,
                is_unsafe: false,
            }),
        );
    }
    let u = n("u");
    let motive_ty = Expr::forall_e(
        n("t"),
        Expr::const_(e.clone(), vec![]),
        Expr::sort(Level::param(u.clone())),
        BinderInfo::Default,
    );
    // ∀ (motive) (ca : motive E.a) (cb : motive E.b) (t : E), motive t
    let rec_ty = Expr::forall_e(
        n("motive"),
        motive_ty.clone(),
        Expr::forall_e(
            n("ca"),
            Expr::app(
                Expr::bvar(0).expect("packs"),
                Expr::const_(nn("E", "a"), vec![]),
            ),
            Expr::forall_e(
                n("cb"),
                Expr::app(
                    Expr::bvar(1).expect("packs"),
                    Expr::const_(nn("E", "b"), vec![]),
                ),
                Expr::forall_e(
                    n("t"),
                    Expr::const_(e.clone(), vec![]),
                    Expr::app(Expr::bvar(3).expect("packs"), Expr::bvar(0).expect("packs")),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    // rule rhs: fun (motive) (ca) (cb) => <the matching minor>.
    let rule_rhs = |pick: u32| {
        Expr::lam(
            n("motive"),
            motive_ty.clone(),
            Expr::lam(
                n("ca"),
                Expr::app(
                    Expr::bvar(0).expect("packs"),
                    Expr::const_(nn("E", "a"), vec![]),
                ),
                Expr::lam(
                    n("cb"),
                    Expr::app(
                        Expr::bvar(1).expect("packs"),
                        Expr::const_(nn("E", "b"), vec![]),
                    ),
                    Expr::bvar(pick).expect("packs"),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        )
    };
    add_info(
        &env,
        ConstantInfo::Rec(RecursorVal {
            base: ConstantVal {
                name: nn("E", "rec"),
                level_params: vec![u],
                type_: rec_ty,
            },
            all: vec![e],
            num_params: 0,
            num_indices: 0,
            num_motives: 1,
            num_minors: 2,
            rules: vec![
                RecursorRule {
                    ctor: nn("E", "a"),
                    nfields: 0,
                    rhs: rule_rhs(1),
                },
                RecursorRule {
                    ctor: nn("E", "b"),
                    nfields: 0,
                    rhs: rule_rhs(0),
                },
            ],
            k: false,
            is_unsafe: false,
        }),
    )
}

/// The motive/minor axioms for `E.rec` at u := 1: `M : E → Sort 1`,
/// `ca : M E.a`, `cb : M E.b`.
fn add_enum_e_axioms(env: &Environment) -> Environment {
    let motive_ty = Expr::forall_e(
        n("t"),
        Expr::const_(n("E"), vec![]),
        sort1(),
        BinderInfo::Default,
    );
    let env = add_info(
        env,
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("M"),
                level_params: vec![],
                type_: motive_ty,
            },
            is_unsafe: false,
        }),
    );
    let env = add_info(
        &env,
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("ca"),
                level_params: vec![],
                type_: Expr::app(
                    Expr::const_(n("M"), vec![]),
                    Expr::const_(nn("E", "a"), vec![]),
                ),
            },
            is_unsafe: false,
        }),
    );
    add_info(
        &env,
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("cb"),
                level_params: vec![],
                type_: Expr::app(
                    Expr::const_(n("M"), vec![]),
                    Expr::const_(nn("E", "b"), vec![]),
                ),
            },
            is_unsafe: false,
        }),
    )
}

fn e_rec_app(major: Expr) -> Expr {
    let mut app = Expr::const_(nn("E", "rec"), vec![Level::one()]);
    for arg in [
        Expr::const_(n("M"), vec![]),
        Expr::const_(n("ca"), vec![]),
        Expr::const_(n("cb"), vec![]),
        major,
    ] {
        app = Expr::app(app, arg);
    }
    app
}

#[test]
fn kr316_iota_selects_the_matching_rule_per_constructor() {
    // KR-316: `E.rec M ca cb E.a ≟ ca` and `E.rec M ca cb E.b ≟ cb` — and the
    // CROSS pairings must fail, killing any always-take-the-first-rule mutant.
    let env = add_enum_e_axioms(&add_enum_e(&Environment::new()));
    let ca = Expr::const_(n("ca"), vec![]);
    let cb = Expr::const_(n("cb"), vec![]);
    let on_a = e_rec_app(Expr::const_(nn("E", "a"), vec![]));
    let on_b = e_rec_app(Expr::const_(nn("E", "b"), vec![]));
    assert!(
        check_def_eq(&env, &[], &on_a, &ca, Budget::DEFAULT).is_accepted(),
        "iota on E.a reduces to the first minor"
    );
    assert!(
        check_def_eq(&env, &[], &on_b, &cb, Budget::DEFAULT).is_accepted(),
        "iota on E.b reduces to the second minor"
    );
    assert_eq!(
        reject_class(&check_def_eq(&env, &[], &on_a, &cb, Budget::DEFAULT)),
        Some(RejectClass::NotDefEq),
        "iota must select the rule OF THE MAJOR'S CONSTRUCTOR"
    );
    assert_eq!(
        reject_class(&check_def_eq(&env, &[], &on_b, &ca, Budget::DEFAULT)),
        Some(RejectClass::NotDefEq),
        "iota must select the rule OF THE MAJOR'S CONSTRUCTOR"
    );
}

#[test]
fn kr316_iota_is_stuck_without_a_constructor_major_or_full_arity() {
    // A non-constructor major (an axiom of type E, on a 2-ctor inductive that is
    // NOT structure-eta eligible) must leave the recursor application stuck —
    // a typed NotDefEq, never a panic or a wrong acceptance. Likewise an
    // under-applied recursor (major premise missing) must not fire.
    let env = add_enum_e_axioms(&add_enum_e(&Environment::new()));
    let env = add_info(
        &env,
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("e0"),
                level_params: vec![],
                type_: Expr::const_(n("E"), vec![]),
            },
            is_unsafe: false,
        }),
    );
    let ca = Expr::const_(n("ca"), vec![]);
    let stuck = e_rec_app(Expr::const_(n("e0"), vec![]));
    assert_eq!(
        reject_class(&check_def_eq(&env, &[], &stuck, &ca, Budget::DEFAULT)),
        Some(RejectClass::NotDefEq),
        "an opaque major premise cannot fire iota on a multi-constructor inductive"
    );
    // Under-applied: E.rec M ca cb (no major) against ca.
    let mut under = Expr::const_(nn("E", "rec"), vec![Level::one()]);
    for arg in [
        Expr::const_(n("M"), vec![]),
        Expr::const_(n("ca"), vec![]),
        Expr::const_(n("cb"), vec![]),
    ] {
        under = Expr::app(under, arg);
    }
    assert_eq!(
        reject_class(&check_def_eq(&env, &[], &under, &ca, Budget::DEFAULT)),
        Some(RejectClass::NotDefEq),
        "an under-applied recursor (missing major) must not fire"
    );
}

#[test]
fn kr316_iota_preserves_trailing_arguments() {
    // Trailing arguments after the major premise must be re-applied to the
    // reduced right-hand side (kills a dropped-extras mutant). Motive returns a
    // function type: M2 := fun _ : E => (D → D); minors are function-valued.
    let env = add_enum_e(&Environment::new());
    let env = add_info(
        &env,
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("D"),
                level_params: vec![],
                type_: sort1(),
            },
            is_unsafe: false,
        }),
    );
    let d = || Expr::const_(n("D"), vec![]);
    let d_to_d = Expr::forall_e(n("x"), d(), d(), BinderInfo::Default);
    let env = add_info(
        &env,
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("f"),
                level_params: vec![],
                type_: d_to_d.clone(),
            },
            is_unsafe: false,
        }),
    );
    let env = add_info(
        &env,
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("g"),
                level_params: vec![],
                type_: d_to_d.clone(),
            },
            is_unsafe: false,
        }),
    );
    let env = add_info(
        &env,
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("d0"),
                level_params: vec![],
                type_: d(),
            },
            is_unsafe: false,
        }),
    );
    // motive := fun _ : E => D → D, passed inline.
    let motive = Expr::lam(
        n("t"),
        Expr::const_(n("E"), vec![]),
        d_to_d,
        BinderInfo::Default,
    );
    let mut lhs = Expr::const_(nn("E", "rec"), vec![Level::one()]);
    for arg in [
        motive,
        Expr::const_(n("f"), vec![]),
        Expr::const_(n("g"), vec![]),
        Expr::const_(nn("E", "a"), vec![]),
        Expr::const_(n("d0"), vec![]), // trailing argument after the major
    ] {
        lhs = Expr::app(lhs, arg);
    }
    let rhs = Expr::app(Expr::const_(n("f"), vec![]), Expr::const_(n("d0"), vec![]));
    assert!(
        check_def_eq(&env, &[], &lhs, &rhs, Budget::DEFAULT).is_accepted(),
        "trailing arguments ride along: E.rec … E.a d0 ≟ f d0"
    );
    let wrong = Expr::app(Expr::const_(n("g"), vec![]), Expr::const_(n("d0"), vec![]));
    assert_eq!(
        reject_class(&check_def_eq(&env, &[], &lhs, &wrong, Budget::DEFAULT)),
        Some(RejectClass::NotDefEq),
        "…and still through the MATCHING rule"
    );
}

/// A Nat-like inductive under the REAL name `Nat` (so KR-316's
/// literal-to-constructor conversion resolves `Nat.zero`/`Nat.succ`), with the
/// standard recursor whose succ rule takes the field and the inductive
/// hypothesis: `fun motive mz ms n => ms n (Nat.rec motive mz ms n)`.
fn add_nat_with_rec(env: &Environment) -> Environment {
    let nat = n("Nat");
    let nat_c = || Expr::const_(n("Nat"), vec![]);
    let env = add_info(
        env,
        ConstantInfo::Induct(InductiveVal {
            base: ConstantVal {
                name: nat.clone(),
                level_params: vec![],
                type_: sort1(),
            },
            num_params: 0,
            num_indices: 0,
            all: vec![nat.clone()],
            ctors: vec![nn("Nat", "zero"), nn("Nat", "succ")],
            num_nested: 0,
            is_rec: true,
            is_unsafe: false,
            is_reflexive: false,
        }),
    );
    let env = add_info(
        &env,
        ConstantInfo::Ctor(ConstructorVal {
            base: ConstantVal {
                name: nn("Nat", "zero"),
                level_params: vec![],
                type_: nat_c(),
            },
            induct: nat.clone(),
            cidx: 0,
            num_params: 0,
            num_fields: 0,
            is_unsafe: false,
        }),
    );
    let env = add_info(
        &env,
        ConstantInfo::Ctor(ConstructorVal {
            base: ConstantVal {
                name: nn("Nat", "succ"),
                level_params: vec![],
                type_: Expr::forall_e(n("n"), nat_c(), nat_c(), BinderInfo::Default),
            },
            induct: nat.clone(),
            cidx: 1,
            num_params: 0,
            num_fields: 1,
            is_unsafe: false,
        }),
    );
    let u = n("u");
    let motive_ty = Expr::forall_e(
        n("t"),
        nat_c(),
        Expr::sort(Level::param(u.clone())),
        BinderInfo::Default,
    );
    // minor_succ type: ∀ (n : Nat), motive n → motive (Nat.succ n). Every use
    // site has [motive, mz] in scope, so under the `n` binder motive is bvar 2
    // and under the `ih` binder it is bvar 3.
    let ms_ty = || {
        Expr::forall_e(
            n("n"),
            nat_c(),
            Expr::forall_e(
                n("ih"),
                Expr::app(Expr::bvar(2).expect("packs"), Expr::bvar(0).expect("packs")),
                Expr::app(
                    Expr::bvar(3).expect("packs"),
                    Expr::app(
                        Expr::const_(nn("Nat", "succ"), vec![]),
                        Expr::bvar(1).expect("packs"),
                    ),
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        )
    };
    // ∀ (motive) (mz : motive Nat.zero) (ms : …) (t : Nat), motive t
    let rec_ty = Expr::forall_e(
        n("motive"),
        motive_ty.clone(),
        Expr::forall_e(
            n("mz"),
            Expr::app(
                Expr::bvar(0).expect("packs"),
                Expr::const_(nn("Nat", "zero"), vec![]),
            ),
            Expr::forall_e(
                n("ms"),
                ms_ty(),
                Expr::forall_e(
                    n("t"),
                    nat_c(),
                    Expr::app(Expr::bvar(3).expect("packs"), Expr::bvar(0).expect("packs")),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    // zero rhs: fun motive mz ms => mz
    let zero_rhs = Expr::lam(
        n("motive"),
        motive_ty.clone(),
        Expr::lam(
            n("mz"),
            Expr::app(
                Expr::bvar(0).expect("packs"),
                Expr::const_(nn("Nat", "zero"), vec![]),
            ),
            Expr::lam(
                n("ms"),
                ms_ty(),
                Expr::bvar(1).expect("packs"),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    // succ rhs: fun motive mz ms n => ms n (Nat.rec.{u} motive mz ms n)
    let succ_rhs = Expr::lam(
        n("motive"),
        motive_ty,
        Expr::lam(
            n("mz"),
            Expr::app(
                Expr::bvar(0).expect("packs"),
                Expr::const_(nn("Nat", "zero"), vec![]),
            ),
            Expr::lam(
                n("ms"),
                ms_ty(),
                Expr::lam(
                    n("n"),
                    nat_c(),
                    {
                        let mut ih = Expr::const_(nn("Nat", "rec"), vec![Level::param(u.clone())]);
                        for arg in [
                            Expr::bvar(3).expect("packs"),
                            Expr::bvar(2).expect("packs"),
                            Expr::bvar(1).expect("packs"),
                            Expr::bvar(0).expect("packs"),
                        ] {
                            ih = Expr::app(ih, arg);
                        }
                        Expr::app(
                            Expr::app(Expr::bvar(1).expect("packs"), Expr::bvar(0).expect("packs")),
                            ih,
                        )
                    },
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    add_info(
        &env,
        ConstantInfo::Rec(RecursorVal {
            base: ConstantVal {
                name: nn("Nat", "rec"),
                level_params: vec![u],
                type_: rec_ty,
            },
            all: vec![nat.clone()],
            num_params: 0,
            num_indices: 0,
            num_motives: 1,
            num_minors: 2,
            rules: vec![
                RecursorRule {
                    ctor: nn("Nat", "zero"),
                    nfields: 0,
                    rhs: zero_rhs,
                },
                RecursorRule {
                    ctor: nn("Nat", "succ"),
                    nfields: 1,
                    rhs: succ_rhs,
                },
            ],
            k: false,
            is_unsafe: false,
        }),
    )
}

/// `Nat.rec.{1} NM nmz nms <major>` over axioms NM/nmz/nms.
fn nat_rec_app(env: &Environment, major: Expr) -> (Environment, Expr) {
    let nat_c = || Expr::const_(n("Nat"), vec![]);
    let env = add_info(
        env,
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("NM"),
                level_params: vec![],
                type_: Expr::forall_e(n("t"), nat_c(), sort1(), BinderInfo::Default),
            },
            is_unsafe: false,
        }),
    );
    let env = add_info(
        &env,
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("nmz"),
                level_params: vec![],
                type_: Expr::app(
                    Expr::const_(n("NM"), vec![]),
                    Expr::const_(nn("Nat", "zero"), vec![]),
                ),
            },
            is_unsafe: false,
        }),
    );
    // nms : ∀ (n : Nat), NM n → NM (Nat.succ n)
    let env = add_info(
        &env,
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("nms"),
                level_params: vec![],
                type_: Expr::forall_e(
                    n("n"),
                    nat_c(),
                    Expr::forall_e(
                        n("ih"),
                        Expr::app(Expr::const_(n("NM"), vec![]), Expr::bvar(0).expect("packs")),
                        Expr::app(
                            Expr::const_(n("NM"), vec![]),
                            Expr::app(
                                Expr::const_(nn("Nat", "succ"), vec![]),
                                Expr::bvar(1).expect("packs"),
                            ),
                        ),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
            },
            is_unsafe: false,
        }),
    );
    let mut app = Expr::const_(nn("Nat", "rec"), vec![Level::one()]);
    for arg in [
        Expr::const_(n("NM"), vec![]),
        Expr::const_(n("nmz"), vec![]),
        Expr::const_(n("nms"), vec![]),
        major,
    ] {
        app = Expr::app(app, arg);
    }
    (env, app)
}

#[test]
fn kr316_iota_applies_constructor_fields_and_the_inductive_hypothesis() {
    // Syntactic-constructor major: Nat.rec … (Nat.succ Nat.zero) must equal
    // nms Nat.zero nmz — the field is passed to the rule AND the recursive
    // occurrence computes (kills a fields-slice-offset mutant).
    let env = add_nat_with_rec(&Environment::new());
    let succ_zero = Expr::app(
        Expr::const_(nn("Nat", "succ"), vec![]),
        Expr::const_(nn("Nat", "zero"), vec![]),
    );
    let (env, lhs) = nat_rec_app(&env, succ_zero);
    let rhs = Expr::app(
        Expr::app(
            Expr::const_(n("nms"), vec![]),
            Expr::const_(nn("Nat", "zero"), vec![]),
        ),
        Expr::const_(n("nmz"), vec![]),
    );
    assert!(
        check_def_eq(&env, &[], &lhs, &rhs, Budget::DEFAULT).is_accepted(),
        "iota on succ: field + inductive hypothesis"
    );
}

#[test]
fn kr316_nat_literal_majors_convert_to_constructor_form() {
    // KR-316's Nat-literal gate: a literal major converts through
    // Nat.zero/Nat.succ before rule matching. Lit(0) takes the zero rule;
    // Lit(2) recurses down to `nms lit1 (nms lit0 nmz)`-shape (checked against
    // the fully symbolic expansion); and Lit(1) against the ZERO minor fails.
    let env = add_nat_with_rec(&Environment::new());
    let lit = |v: u64| Expr::lit(Literal::Nat(NatLit::from_u64(v)));
    let (env, on_zero_lit) = nat_rec_app(&env, lit(0));
    assert!(
        check_def_eq(
            &env,
            &[],
            &on_zero_lit,
            &Expr::const_(n("nmz"), vec![]),
            Budget::DEFAULT
        )
        .is_accepted(),
        "literal 0 reduces through the Nat.zero rule"
    );
    // Same env already carries NM/nmz/nms; build further apps by hand.
    let rec_on = |major: Expr| {
        let mut app = Expr::const_(nn("Nat", "rec"), vec![Level::one()]);
        for arg in [
            Expr::const_(n("NM"), vec![]),
            Expr::const_(n("nmz"), vec![]),
            Expr::const_(n("nms"), vec![]),
            major,
        ] {
            app = Expr::app(app, arg);
        }
        app
    };
    let on_two_lit = rec_on(lit(2));
    // Fully-literal expansion: rec on lit 2 unrolls through the succ rule twice
    // and the zero rule once, staying in literal form throughout. (Comparing
    // against the SYMBOLIC succ (succ zero) major would additionally need
    // KR-313 Nat acceleration — `lit 1 ≟ Nat.succ Nat.zero` in argument
    // position — which is the fln-bignum follow-up slice, not iota.)
    let expected_two = Expr::app(
        Expr::app(Expr::const_(n("nms"), vec![]), lit(1)),
        Expr::app(
            Expr::app(Expr::const_(n("nms"), vec![]), lit(0)),
            Expr::const_(n("nmz"), vec![]),
        ),
    );
    assert!(
        check_def_eq(&env, &[], &on_two_lit, &expected_two, Budget::DEFAULT).is_accepted(),
        "literal 2 unrolls through succ, succ, zero rules"
    );
    assert_eq!(
        reject_class(&check_def_eq(
            &env,
            &[],
            &rec_on(lit(1)),
            &Expr::const_(n("nmz"), vec![]),
            Budget::DEFAULT
        )),
        Some(RejectClass::NotDefEq),
        "literal 1 must take the SUCC rule, not the zero rule"
    );
}

#[test]
fn fl_inv_07_iota_chain_exhaustion_is_inconclusive_never_rejected() {
    // A large literal drives a long succ-rule chain that stays in HEAD position:
    // the succ minor is `fun n ih => ih`, so each iota step beta-reduces
    // straight into the next recursor application. A tiny budget must yield a
    // typed Inconclusive (FL-INV-07) — not acceptance, not rejection. (An
    // axiom minor would NOT work here: reduction would stick behind the axiom
    // head after one step and terminate as an honest NotDefEq.)
    let env = add_nat_with_rec(&Environment::new());
    let (env, _) = nat_rec_app(&env, Expr::lit(Literal::Nat(NatLit::from_u64(0))));
    let nat_c = || Expr::const_(n("Nat"), vec![]);
    let ih_minor = Expr::lam(
        n("n"),
        nat_c(),
        Expr::lam(
            n("ih"),
            Expr::app(Expr::const_(n("NM"), vec![]), Expr::bvar(0).expect("packs")),
            Expr::bvar(0).expect("packs"),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let mut lhs = Expr::const_(nn("Nat", "rec"), vec![Level::one()]);
    for arg in [
        Expr::const_(n("NM"), vec![]),
        Expr::const_(n("nmz"), vec![]),
        ih_minor,
        Expr::lit(Literal::Nat(NatLit::from_u64(1_000_000))),
    ] {
        lhs = Expr::app(lhs, arg);
    }
    let verdict = check_def_eq(
        &env,
        &[],
        &lhs,
        &Expr::const_(n("nmz"), vec![]),
        Budget {
            steps: 2_000,
            depth: 64,
        },
    );
    assert!(
        matches!(verdict, Verdict::Inconclusive { .. }),
        "budget exhaustion in an iota chain is Inconclusive, got {verdict:?}"
    );
}

#[test]
fn kr317_k_like_recursor_reduces_an_opaque_proof() {
    // KR-317: `T : Prop` with one nullary constructor `T.intro`; T.rec is
    // K-flagged. The major premise is an OPAQUE axiom `h : T` — never
    // syntactically a constructor — yet the recursor must reduce, because K
    // conversion replaces h by T.intro after the type check. Kills a
    // missing-K-conversion mutant (without it the application is stuck).
    let t = n("T");
    let env = add_info(
        &Environment::new(),
        ConstantInfo::Induct(InductiveVal {
            base: ConstantVal {
                name: t.clone(),
                level_params: vec![],
                type_: prop(),
            },
            num_params: 0,
            num_indices: 0,
            all: vec![t.clone()],
            ctors: vec![nn("T", "intro")],
            num_nested: 0,
            is_rec: false,
            is_unsafe: false,
            is_reflexive: false,
        }),
    );
    let env = add_info(
        &env,
        ConstantInfo::Ctor(ConstructorVal {
            base: ConstantVal {
                name: nn("T", "intro"),
                level_params: vec![],
                type_: Expr::const_(t.clone(), vec![]),
            },
            induct: t.clone(),
            cidx: 0,
            num_params: 0,
            num_fields: 0,
            is_unsafe: false,
        }),
    );
    let u = n("u");
    let motive_ty = Expr::forall_e(
        n("t"),
        Expr::const_(t.clone(), vec![]),
        Expr::sort(Level::param(u.clone())),
        BinderInfo::Default,
    );
    // ∀ (motive) (c : motive T.intro) (h : T), motive h
    let rec_ty = Expr::forall_e(
        n("motive"),
        motive_ty.clone(),
        Expr::forall_e(
            n("c"),
            Expr::app(
                Expr::bvar(0).expect("packs"),
                Expr::const_(nn("T", "intro"), vec![]),
            ),
            Expr::forall_e(
                n("h"),
                Expr::const_(t.clone(), vec![]),
                Expr::app(Expr::bvar(2).expect("packs"), Expr::bvar(0).expect("packs")),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    // rule rhs: fun motive c => c
    let rhs = Expr::lam(
        n("motive"),
        motive_ty,
        Expr::lam(
            n("c"),
            Expr::app(
                Expr::bvar(0).expect("packs"),
                Expr::const_(nn("T", "intro"), vec![]),
            ),
            Expr::bvar(0).expect("packs"),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let env = add_info(
        &env,
        ConstantInfo::Rec(RecursorVal {
            base: ConstantVal {
                name: nn("T", "rec"),
                level_params: vec![u],
                type_: rec_ty,
            },
            all: vec![t.clone()],
            num_params: 0,
            num_indices: 0,
            num_motives: 1,
            num_minors: 1,
            rules: vec![RecursorRule {
                ctor: nn("T", "intro"),
                nfields: 0,
                rhs,
            }],
            k: true,
            is_unsafe: false,
        }),
    );
    // Motive/minor/proof axioms: TM : T → Sort 1, tc : TM T.intro, h : T.
    let env = add_info(
        &env,
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("TM"),
                level_params: vec![],
                type_: Expr::forall_e(
                    n("t"),
                    Expr::const_(t.clone(), vec![]),
                    sort1(),
                    BinderInfo::Default,
                ),
            },
            is_unsafe: false,
        }),
    );
    let env = add_info(
        &env,
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("tc"),
                level_params: vec![],
                type_: Expr::app(
                    Expr::const_(n("TM"), vec![]),
                    Expr::const_(nn("T", "intro"), vec![]),
                ),
            },
            is_unsafe: false,
        }),
    );
    let env = add_info(
        &env,
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("h"),
                level_params: vec![],
                type_: Expr::const_(t.clone(), vec![]),
            },
            is_unsafe: false,
        }),
    );
    let mut lhs = Expr::const_(nn("T", "rec"), vec![Level::one()]);
    for arg in [
        Expr::const_(n("TM"), vec![]),
        Expr::const_(n("tc"), vec![]),
        Expr::const_(n("h"), vec![]),
    ] {
        lhs = Expr::app(lhs, arg);
    }
    assert!(
        check_def_eq(
            &env,
            &[],
            &lhs,
            &Expr::const_(n("tc"), vec![]),
            Budget::DEFAULT
        )
        .is_accepted(),
        "K-like reduction fires on an opaque proof of a K-eligible inductive"
    );
}

#[test]
fn kr316_structure_eta_coercion_fires_the_recursor_on_an_opaque_major() {
    // KR-316's structure-eta gate: `S` is a one-constructor, index-free,
    // non-recursive structure; the major is an OPAQUE axiom `s : S`. The
    // coercion rewrites it to `S.mk (proj 0 s) (proj 1 s)`, so S.rec must
    // reduce to `minor (proj 0 s) (proj 1 s)` (kills a missing-eta mutant).
    let env = add_info(
        &Environment::new(),
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("D"),
                level_params: vec![],
                type_: sort1(),
            },
            is_unsafe: false,
        }),
    );
    let d = || Expr::const_(n("D"), vec![]);
    let env = add_structure(&env, "S", "mk", sort1(), &[d(), d()]);
    let s_c = || Expr::const_(n("S"), vec![]);
    let u = n("u");
    let motive_ty = Expr::forall_e(
        n("t"),
        s_c(),
        Expr::sort(Level::param(u.clone())),
        BinderInfo::Default,
    );
    // minor : ∀ (f0 f1 : D), motive (S.mk f0 f1); at its use site [motive] is in
    // scope, so under f0/f1 motive is bvar 1/2 respectively.
    let minor_ty = Expr::forall_e(
        n("f0"),
        d(),
        Expr::forall_e(
            n("f1"),
            d(),
            Expr::app(
                Expr::bvar(2).expect("packs"),
                Expr::app(
                    Expr::app(Expr::const_(n("mk"), vec![]), Expr::bvar(1).expect("packs")),
                    Expr::bvar(0).expect("packs"),
                ),
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    // ∀ (motive) (minor : …) (t : S), motive t
    let rec_ty = Expr::forall_e(
        n("motive"),
        motive_ty.clone(),
        Expr::forall_e(
            n("minor"),
            minor_ty.clone(),
            Expr::forall_e(
                n("t"),
                s_c(),
                Expr::app(Expr::bvar(2).expect("packs"), Expr::bvar(0).expect("packs")),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    // rule rhs: fun motive minor f0 f1 => minor f0 f1
    let rhs = Expr::lam(
        n("motive"),
        motive_ty,
        Expr::lam(
            n("minor"),
            minor_ty,
            Expr::lam(
                n("f0"),
                d(),
                Expr::lam(
                    n("f1"),
                    d(),
                    Expr::app(
                        Expr::app(Expr::bvar(2).expect("packs"), Expr::bvar(1).expect("packs")),
                        Expr::bvar(0).expect("packs"),
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let env = add_info(
        &env,
        ConstantInfo::Rec(RecursorVal {
            base: ConstantVal {
                name: nn("S", "rec"),
                level_params: vec![u],
                type_: rec_ty,
            },
            all: vec![n("S")],
            num_params: 0,
            num_indices: 0,
            num_motives: 1,
            num_minors: 1,
            rules: vec![RecursorRule {
                ctor: n("mk"),
                nfields: 2,
                rhs,
            }],
            k: false,
            is_unsafe: false,
        }),
    );
    let env = add_info(
        &env,
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("SM"),
                level_params: vec![],
                type_: Expr::forall_e(n("t"), s_c(), sort1(), BinderInfo::Default),
            },
            is_unsafe: false,
        }),
    );
    // minor axiom: sm : ∀ (f0 f1 : D), SM (mk f0 f1)
    let env = add_info(
        &env,
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("sm"),
                level_params: vec![],
                type_: Expr::forall_e(
                    n("f0"),
                    d(),
                    Expr::forall_e(
                        n("f1"),
                        d(),
                        Expr::app(
                            Expr::const_(n("SM"), vec![]),
                            Expr::app(
                                Expr::app(
                                    Expr::const_(n("mk"), vec![]),
                                    Expr::bvar(1).expect("packs"),
                                ),
                                Expr::bvar(0).expect("packs"),
                            ),
                        ),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
            },
            is_unsafe: false,
        }),
    );
    let env = add_info(
        &env,
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("s"),
                level_params: vec![],
                type_: s_c(),
            },
            is_unsafe: false,
        }),
    );
    let mut lhs = Expr::const_(nn("S", "rec"), vec![Level::one()]);
    for arg in [
        Expr::const_(n("SM"), vec![]),
        Expr::const_(n("sm"), vec![]),
        Expr::const_(n("s"), vec![]),
    ] {
        lhs = Expr::app(lhs, arg);
    }
    let s0 = Expr::proj(n("S"), 0, Expr::const_(n("s"), vec![]));
    let s1 = Expr::proj(n("S"), 1, Expr::const_(n("s"), vec![]));
    let rhs_expected = Expr::app(Expr::app(Expr::const_(n("sm"), vec![]), s0), s1);
    assert!(
        check_def_eq(&env, &[], &lhs, &rhs_expected, Budget::DEFAULT).is_accepted(),
        "structure-eta coercion lets the recursor fire on an opaque structure value"
    );
}

/// The Quot machinery as QuotVals (types are structural placeholders — KR-955
/// computation never consults them, exactly like the pin's quot_reduce_rec).
fn add_quot(env: &Environment) -> Environment {
    let mut env = env.clone();
    for (name_, kind) in [
        (n("Quot"), QuotKind::Type),
        (nn("Quot", "mk"), QuotKind::Ctor),
        (nn("Quot", "lift"), QuotKind::Lift),
        (nn("Quot", "ind"), QuotKind::Ind),
    ] {
        env = add_info(
            &env,
            ConstantInfo::Quot(QuotVal {
                base: ConstantVal {
                    name: name_,
                    level_params: vec![],
                    type_: sort1(),
                },
                kind,
            }),
        );
    }
    // Scaffolding axioms: A, R, B, f, H, a, P, Mo.
    for (name_, type_) in [("A", sort1()), ("B", sort1()), ("R", prop()), ("H", prop())] {
        env = add_info(
            &env,
            ConstantInfo::Axiom(AxiomVal {
                base: ConstantVal {
                    name: n(name_),
                    level_params: vec![],
                    type_,
                },
                is_unsafe: false,
            }),
        );
    }
    for (name_, type_) in [
        ("a", Expr::const_(n("A"), vec![])),
        (
            "f",
            Expr::forall_e(
                n("x"),
                Expr::const_(n("A"), vec![]),
                Expr::const_(n("B"), vec![]),
                BinderInfo::Default,
            ),
        ),
        ("hp", Expr::const_(n("H"), vec![])),
        (
            "P",
            Expr::forall_e(
                n("x"),
                Expr::const_(n("A"), vec![]),
                Expr::const_(n("B"), vec![]),
                BinderInfo::Default,
            ),
        ),
        ("Mo", sort1()),
    ] {
        env = add_info(
            &env,
            ConstantInfo::Axiom(AxiomVal {
                base: ConstantVal {
                    name: n(name_),
                    level_params: vec![],
                    type_,
                },
                is_unsafe: false,
            }),
        );
    }
    env
}

fn quot_mk_a() -> Expr {
    let mut mk = Expr::const_(nn("Quot", "mk"), vec![]);
    for arg in [
        Expr::const_(n("A"), vec![]),
        Expr::const_(n("R"), vec![]),
        Expr::const_(n("a"), vec![]),
    ] {
        mk = Expr::app(mk, arg);
    }
    mk
}

#[test]
fn kr955_quot_lift_and_ind_compute() {
    // KR-955: `Quot.lift A R B f hp (Quot.mk A R a) ≟ f a` (mk at position 5, f
    // at 3) and `Quot.ind A R Mo P (Quot.mk A R a) ≟ P a` (mk at 4, P at 3).
    // The cross-check `… ≟ f a` vs a WRONG argument kills swapped-position
    // mutants.
    let env = add_quot(&Environment::new());
    let mut lift = Expr::const_(nn("Quot", "lift"), vec![]);
    for arg in [
        Expr::const_(n("A"), vec![]),
        Expr::const_(n("R"), vec![]),
        Expr::const_(n("B"), vec![]),
        Expr::const_(n("f"), vec![]),
        Expr::const_(n("hp"), vec![]),
        quot_mk_a(),
    ] {
        lift = Expr::app(lift, arg);
    }
    let f_a = Expr::app(Expr::const_(n("f"), vec![]), Expr::const_(n("a"), vec![]));
    assert!(
        check_def_eq(&env, &[], &lift, &f_a, Budget::DEFAULT).is_accepted(),
        "Quot.lift computes: lift f h (mk r a) ≟ f a"
    );
    let hp_a = Expr::app(Expr::const_(n("hp"), vec![]), Expr::const_(n("a"), vec![]));
    assert_eq!(
        reject_class(&check_def_eq(&env, &[], &lift, &hp_a, Budget::DEFAULT)),
        Some(RejectClass::NotDefEq),
        "the FUNCTION is at position 3, not the proof at 4"
    );
    let mut ind = Expr::const_(nn("Quot", "ind"), vec![]);
    for arg in [
        Expr::const_(n("A"), vec![]),
        Expr::const_(n("R"), vec![]),
        Expr::const_(n("Mo"), vec![]),
        Expr::const_(n("P"), vec![]),
        quot_mk_a(),
    ] {
        ind = Expr::app(ind, arg);
    }
    let p_a = Expr::app(Expr::const_(n("P"), vec![]), Expr::const_(n("a"), vec![]));
    assert!(
        check_def_eq(&env, &[], &ind, &p_a, Budget::DEFAULT).is_accepted(),
        "Quot.ind computes: ind p (mk r a) ≟ p a"
    );
}

#[test]
fn kr955_quot_computation_preserves_trailing_args_and_requires_a_saturated_mk() {
    let env = add_quot(&Environment::new());
    // Trailing argument: motive B := fun _ => (B → B) shape is overkill; reuse
    // f : A → B and apply the lift result is already B. Instead check the
    // under-saturated mk: `Quot.lift A R B f hp (Quot.mk A R)` must be STUCK
    // (mk has 2 args, not 3), not wrongly reduced.
    let mut partial_mk = Expr::const_(nn("Quot", "mk"), vec![]);
    for arg in [Expr::const_(n("A"), vec![]), Expr::const_(n("R"), vec![])] {
        partial_mk = Expr::app(partial_mk, arg);
    }
    let mut lift = Expr::const_(nn("Quot", "lift"), vec![]);
    for arg in [
        Expr::const_(n("A"), vec![]),
        Expr::const_(n("R"), vec![]),
        Expr::const_(n("B"), vec![]),
        Expr::const_(n("f"), vec![]),
        Expr::const_(n("hp"), vec![]),
        partial_mk,
    ] {
        lift = Expr::app(lift, arg);
    }
    let f_alone = Expr::const_(n("f"), vec![]);
    assert_eq!(
        reject_class(&check_def_eq(&env, &[], &lift, &f_alone, Budget::DEFAULT)),
        Some(RejectClass::NotDefEq),
        "an under-saturated Quot.mk must not fire quotient computation"
    );
    // Trailing argument preservation: Quot.ind with one extra argument after the
    // mk — `Quot.ind A R Mo P (mk …) extra ≟ P a extra`.
    let env = add_info(
        &env,
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("extra"),
                level_params: vec![],
                type_: Expr::const_(n("B"), vec![]),
            },
            is_unsafe: false,
        }),
    );
    let mut ind = Expr::const_(nn("Quot", "ind"), vec![]);
    for arg in [
        Expr::const_(n("A"), vec![]),
        Expr::const_(n("R"), vec![]),
        Expr::const_(n("Mo"), vec![]),
        Expr::const_(n("P"), vec![]),
        quot_mk_a(),
        Expr::const_(n("extra"), vec![]),
    ] {
        ind = Expr::app(ind, arg);
    }
    let expected = Expr::app(
        Expr::app(Expr::const_(n("P"), vec![]), Expr::const_(n("a"), vec![])),
        Expr::const_(n("extra"), vec![]),
    );
    assert!(
        check_def_eq(&env, &[], &ind, &expected, Budget::DEFAULT).is_accepted(),
        "trailing arguments after the mk position are preserved"
    );
}

#[test]
fn kr316_parameterized_iota_takes_the_last_nfields_arguments() {
    // `Opt` has one parameter, so a constructor application's spine is
    // [param, field]. The rule must receive the LAST nfields arguments (the
    // field x), never the leading parameter — kills a fields-slice-offset
    // mutant that num_params = 0 fixtures cannot see.
    let a_ty = || Expr::const_(n("AT"), vec![]);
    let opt = |arg: Expr| Expr::app(Expr::const_(n("Opt"), vec![]), arg);
    let env = add_info(
        &Environment::new(),
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("AT"),
                level_params: vec![],
                type_: sort1(),
            },
            is_unsafe: false,
        }),
    );
    // Opt : Sort 1 → Sort 1, one ctor `Opt.some : ∀ (A : Sort 1) (a : A), Opt A`.
    let env = add_info(
        &env,
        ConstantInfo::Induct(InductiveVal {
            base: ConstantVal {
                name: n("Opt"),
                level_params: vec![],
                type_: Expr::forall_e(n("A"), sort1(), sort1(), BinderInfo::Default),
            },
            num_params: 1,
            num_indices: 0,
            all: vec![n("Opt")],
            ctors: vec![nn("Opt", "some")],
            num_nested: 0,
            is_rec: false,
            is_unsafe: false,
            is_reflexive: false,
        }),
    );
    let env = add_info(
        &env,
        ConstantInfo::Ctor(ConstructorVal {
            base: ConstantVal {
                name: nn("Opt", "some"),
                level_params: vec![],
                type_: Expr::forall_e(
                    n("A"),
                    sort1(),
                    Expr::forall_e(
                        n("a"),
                        Expr::bvar(0).expect("packs"),
                        Expr::app(
                            Expr::const_(n("Opt"), vec![]),
                            Expr::bvar(1).expect("packs"),
                        ),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
            },
            induct: n("Opt"),
            cidx: 0,
            num_params: 1,
            num_fields: 1,
            is_unsafe: false,
        }),
    );
    let u = n("u");
    // motive : Opt A → Sort u (with A = the bvar of the enclosing param binder).
    // Opt.rec.{u} : ∀ (A : Sort 1) (motive : Opt A → Sort u)
    //                 (msome : ∀ (a : A), motive (Opt.some A a)) (t : Opt A), motive t
    let rec_ty = Expr::forall_e(
        n("A"),
        sort1(),
        Expr::forall_e(
            n("motive"),
            Expr::forall_e(
                n("t"),
                opt(Expr::bvar(0).expect("packs")),
                Expr::sort(Level::param(u.clone())),
                BinderInfo::Default,
            ),
            Expr::forall_e(
                n("msome"),
                Expr::forall_e(
                    n("a"),
                    Expr::bvar(1).expect("packs"),
                    Expr::app(
                        Expr::bvar(1).expect("packs"),
                        Expr::app(
                            Expr::app(
                                Expr::const_(nn("Opt", "some"), vec![]),
                                Expr::bvar(2).expect("packs"),
                            ),
                            Expr::bvar(0).expect("packs"),
                        ),
                    ),
                    BinderInfo::Default,
                ),
                Expr::forall_e(
                    n("t"),
                    opt(Expr::bvar(2).expect("packs")),
                    Expr::app(Expr::bvar(2).expect("packs"), Expr::bvar(0).expect("packs")),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    // rule rhs: fun A motive msome a => msome a
    let rhs = Expr::lam(
        n("A"),
        sort1(),
        Expr::lam(
            n("motive"),
            Expr::forall_e(
                n("t"),
                opt(Expr::bvar(0).expect("packs")),
                Expr::sort(Level::param(u.clone())),
                BinderInfo::Default,
            ),
            Expr::lam(
                n("msome"),
                Expr::forall_e(
                    n("a"),
                    Expr::bvar(1).expect("packs"),
                    Expr::app(
                        Expr::bvar(1).expect("packs"),
                        Expr::app(
                            Expr::app(
                                Expr::const_(nn("Opt", "some"), vec![]),
                                Expr::bvar(2).expect("packs"),
                            ),
                            Expr::bvar(0).expect("packs"),
                        ),
                    ),
                    BinderInfo::Default,
                ),
                Expr::lam(
                    n("a"),
                    // a : A — at scope [A, motive, msome], A is bvar 2.
                    Expr::bvar(2).expect("packs"),
                    Expr::app(Expr::bvar(1).expect("packs"), Expr::bvar(0).expect("packs")),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let env = add_info(
        &env,
        ConstantInfo::Rec(RecursorVal {
            base: ConstantVal {
                name: nn("Opt", "rec"),
                level_params: vec![u],
                type_: rec_ty,
            },
            all: vec![n("Opt")],
            num_params: 1,
            num_indices: 0,
            num_motives: 1,
            num_minors: 1,
            rules: vec![RecursorRule {
                ctor: nn("Opt", "some"),
                nfields: 1,
                rhs,
            }],
            k: false,
            is_unsafe: false,
        }),
    );
    // OM : Opt AT → Sort 1; om : ∀ (a : AT), OM (Opt.some AT a); x : AT.
    let env = add_info(
        &env,
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("OM"),
                level_params: vec![],
                type_: Expr::forall_e(n("t"), opt(a_ty()), sort1(), BinderInfo::Default),
            },
            is_unsafe: false,
        }),
    );
    let env = add_info(
        &env,
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("om"),
                level_params: vec![],
                type_: Expr::forall_e(
                    n("a"),
                    a_ty(),
                    Expr::app(
                        Expr::const_(n("OM"), vec![]),
                        Expr::app(
                            Expr::app(Expr::const_(nn("Opt", "some"), vec![]), a_ty()),
                            Expr::bvar(0).expect("packs"),
                        ),
                    ),
                    BinderInfo::Default,
                ),
            },
            is_unsafe: false,
        }),
    );
    let env = add_info(
        &env,
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("x"),
                level_params: vec![],
                type_: a_ty(),
            },
            is_unsafe: false,
        }),
    );
    let some_x = Expr::app(
        Expr::app(Expr::const_(nn("Opt", "some"), vec![]), a_ty()),
        Expr::const_(n("x"), vec![]),
    );
    let mut lhs = Expr::const_(nn("Opt", "rec"), vec![Level::one()]);
    for arg in [
        a_ty(),
        Expr::const_(n("OM"), vec![]),
        Expr::const_(n("om"), vec![]),
        some_x,
    ] {
        lhs = Expr::app(lhs, arg);
    }
    let om_x = Expr::app(Expr::const_(n("om"), vec![]), Expr::const_(n("x"), vec![]));
    assert!(
        check_def_eq(&env, &[], &lhs, &om_x, Budget::DEFAULT).is_accepted(),
        "the rule receives the FIELD x, not the leading parameter"
    );
    let om_a = Expr::app(Expr::const_(n("om"), vec![]), a_ty());
    assert_eq!(
        reject_class(&check_def_eq(&env, &[], &lhs, &om_a, Budget::DEFAULT)),
        Some(RejectClass::NotDefEq),
        "…and NOT the parameter AT (the fields-offset mutant's output)"
    );
}

// ---- defeq head rules re-run after reduction (KR-302/303/305; bead fln-d4x) ---------

/// An `Abbrev` type definition, the `outParam`/`ReaderT` shape.
fn abbrev(name: &str, type_: Expr, value: Expr) -> ConstantInfo {
    ConstantInfo::Defn(DefinitionVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![],
            type_,
        },
        value,
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![n(name)],
    })
}

#[test]
fn kr303_sort_equivalence_discovered_by_delta() {
    // `M := Sort (max 2 2)` (an abbrev). `M ≟ Sort 2` holds only if the
    // sort-equivalence rule re-runs AFTER lazy delta exposes the Sort — the
    // levels are equivalent but not structurally equal, so quick equality can
    // never catch it. This is the decoded `outParam`/motive-universe shape
    // from the Init.Prelude replay (bead fln-d4x probe).
    let two = Level::one().succ().expect("packs");
    let max22 = Level::max(two.clone(), two.clone()).expect("packs");
    let env = add_info(
        &Environment::new(),
        abbrev(
            "M",
            Expr::sort(max22.clone().succ().expect("packs")),
            Expr::sort(max22),
        ),
    );
    let verdict = check_def_eq(
        &env,
        &[],
        &Expr::const_(n("M"), vec![]),
        &Expr::sort(two),
        Budget::DEFAULT,
    );
    assert!(
        verdict.is_accepted(),
        "Sort equivalence must be re-checked after delta: {verdict:?}"
    );
}

#[test]
fn kr303_sort_equivalence_discovered_by_beta() {
    // `(fun _ : D => Sort (max 2 2)) d ≟ Sort 2`: whnf_core beta exposes the
    // Sort pair; the head rules must re-run on the REDUCED pair (the decoded
    // `Lean.Name.below` motive shape from the replay probe).
    let env = add_info(
        &Environment::new(),
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("D"),
                level_params: vec![],
                type_: sort1(),
            },
            is_unsafe: false,
        }),
    );
    let env = add_info(
        &env,
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("d"),
                level_params: vec![],
                type_: Expr::const_(n("D"), vec![]),
            },
            is_unsafe: false,
        }),
    );
    let two = Level::one().succ().expect("packs");
    let max22 = Level::max(two.clone(), two.clone()).expect("packs");
    let redex = Expr::app(
        Expr::lam(
            n("x"),
            Expr::const_(n("D"), vec![]),
            Expr::sort(max22),
            BinderInfo::Default,
        ),
        Expr::const_(n("d"), vec![]),
    );
    let verdict = check_def_eq(&env, &[], &redex, &Expr::sort(two), Budget::DEFAULT);
    assert!(
        verdict.is_accepted(),
        "Sort equivalence must be re-checked after whnf_core beta: {verdict:?}"
    );
}

#[test]
fn kr302_binder_congruence_discovered_by_delta() {
    // `Id2 := D` and `Arr := D → Id2` (abbrevs). `Arr ≟ (D → D)` requires the
    // binder-congruence rule to re-run after delta turns `Arr` into a Pi whose
    // BODY still needs another unfolding — the decoded `ReaderT.pure` shape
    // (a function-type abbrev compared against its expansion).
    let env = add_info(
        &Environment::new(),
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("D"),
                level_params: vec![],
                type_: sort1(),
            },
            is_unsafe: false,
        }),
    );
    let d = || Expr::const_(n("D"), vec![]);
    let env = add_info(&env, abbrev("Id2", sort1(), d()));
    let arr_value = Expr::forall_e(
        n("x"),
        d(),
        Expr::const_(n("Id2"), vec![]),
        BinderInfo::Default,
    );
    let env = add_info(&env, abbrev("Arr", sort1(), arr_value));
    let plain = Expr::forall_e(n("x"), d(), d(), BinderInfo::Default);
    let verdict = check_def_eq(
        &env,
        &[],
        &Expr::const_(n("Arr"), vec![]),
        &plain,
        Budget::DEFAULT,
    );
    assert!(
        verdict.is_accepted(),
        "binder congruence must be re-checked after delta: {verdict:?}"
    );
    // Soundness guard: the re-run must not equate DIFFERENT function types.
    let env = add_info(
        &env,
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("E2"),
                level_params: vec![],
                type_: sort1(),
            },
            is_unsafe: false,
        }),
    );
    let wrong = Expr::forall_e(
        n("x"),
        d(),
        Expr::const_(n("E2"), vec![]),
        BinderInfo::Default,
    );
    assert_eq!(
        reject_class(&check_def_eq(
            &env,
            &[],
            &Expr::const_(n("Arr"), vec![]),
            &wrong,
            Budget::DEFAULT
        )),
        Some(RejectClass::NotDefEq),
        "re-run congruence must stay sound"
    );
}
