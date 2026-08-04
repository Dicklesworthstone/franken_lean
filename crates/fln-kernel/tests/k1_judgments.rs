//! K1 bootstrap judgment tests (bead franken_lean-zht), each tagged to its
//! KERNEL_CONTRACT.md rule and driven ONLY through the public authority
//! (`check` / `check_def_eq`) — the kernel has no other door.

#![forbid(unsafe_code)]

use fln_core::expr::{BinderInfo, Expr, ExprNode, Literal, NatLit};
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
        // Block declarations use their own admission helpers in these tests.
        Declaration::Inductive(_) | Declaration::Quotient(_) => {
            unreachable!("admit() is only used for single-constant declarations")
        }
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

// ---- structure eta + unit-like eta in defeq (KR-903/KR-315; bead fln-d4x) -----------

#[test]
fn kr903_structure_eta_in_defeq_both_directions() {
    // `s ≟ mk (s.0) (s.1)` for an opaque s of a one-constructor, index-free,
    // non-recursive structure — and the mirror orientation. The negative
    // guards soundness: a DIFFERENT opaque value's projections must not close
    // the equation.
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
    let env = add_info(
        &env,
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("s"),
                level_params: vec![],
                type_: Expr::const_(n("S"), vec![]),
            },
            is_unsafe: false,
        }),
    );
    let env = add_info(
        &env,
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("s2"),
                level_params: vec![],
                type_: Expr::const_(n("S"), vec![]),
            },
            is_unsafe: false,
        }),
    );
    let s = || Expr::const_(n("s"), vec![]);
    let eta_of = |of: Expr| {
        Expr::app(
            Expr::app(
                Expr::const_(n("mk"), vec![]),
                Expr::proj(n("S"), 0, of.clone()),
            ),
            Expr::proj(n("S"), 1, of),
        )
    };
    assert!(
        check_def_eq(&env, &[], &s(), &eta_of(s()), Budget::DEFAULT).is_accepted(),
        "s ≟ mk s.0 s.1 (structure eta)"
    );
    assert!(
        check_def_eq(&env, &[], &eta_of(s()), &s(), Budget::DEFAULT).is_accepted(),
        "mk s.0 s.1 ≟ s (mirror orientation)"
    );
    assert_eq!(
        reject_class(&check_def_eq(
            &env,
            &[],
            &Expr::const_(n("s2"), vec![]),
            &eta_of(s()),
            Budget::DEFAULT
        )),
        Some(RejectClass::NotDefEq),
        "s2 ≟ mk s.0 s.1 must fail — eta must compare the fields of THIS value"
    );
}

#[test]
fn kr315_unit_like_values_are_defeq_when_their_types_are() {
    // Two opaque values of the same zero-field structure type are defeq;
    // values of DIFFERENT unit-like types are not — the type-agreement gate
    // is what separates KR-315 from unsoundness (kills a dropped-type-check
    // mutant in either eta rule, since `U2.mk` is a saturated zero-field
    // constructor that try_eta_struct also inspects).
    let env = add_structure(&Environment::new(), "U", "U.mk", sort1(), &[]);
    let env = add_structure(&env, "U2", "U2.mk", sort1(), &[]);
    let env = add_info(
        &env,
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("u1"),
                level_params: vec![],
                type_: Expr::const_(n("U"), vec![]),
            },
            is_unsafe: false,
        }),
    );
    let env = add_info(
        &env,
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("u2"),
                level_params: vec![],
                type_: Expr::const_(n("U"), vec![]),
            },
            is_unsafe: false,
        }),
    );
    assert!(
        check_def_eq(
            &env,
            &[],
            &Expr::const_(n("u1"), vec![]),
            &Expr::const_(n("u2"), vec![]),
            Budget::DEFAULT
        )
        .is_accepted(),
        "two values of one unit-like type are defeq"
    );
    assert_eq!(
        reject_class(&check_def_eq(
            &env,
            &[],
            &Expr::const_(n("u1"), vec![]),
            &Expr::const_(n("U2.mk"), vec![]),
            Budget::DEFAULT
        )),
        Some(RejectClass::NotDefEq),
        "a value of U is NOT defeq to the constructor of the DIFFERENT unit-like U2"
    );
}

// ---- KR-313 / KR-314: literal acceleration (bead franken_lean-irm) ------------------

fn lit(v: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(v)))
}

fn str_lit(s: &str) -> Expr {
    Expr::lit(Literal::Str(s.to_string()))
}

fn nat_op_app(op: &str, a: Expr, b: Expr) -> Expr {
    Expr::app(Expr::app(Expr::const_(nn("Nat", op), vec![]), a), b)
}

fn bool_true() -> Expr {
    Expr::const_(nn("Bool", "true"), vec![])
}

fn bool_false() -> Expr {
    Expr::const_(nn("Bool", "false"), vec![])
}

/// Every KR-313 name with an honest type, so any ladder rung that infers
/// (proof irrelevance, eta, unit-like) stays total during these tests: `Nat`
/// and `Bool` as opaque type constants, `Nat.zero : Nat`, `Nat.succ : Nat →
/// Nat`, the binary operator table at `Nat → Nat → Nat`, and the comparison
/// table (including the deliberately-unaccelerated `blt`) at `Nat → Nat →
/// Bool`, plus `Bool.true`/`Bool.false`. KR-313 dispatches on NAMES, exactly
/// as the pin's `g_nat_*` expression comparisons do — these axioms exist for
/// the typing rungs, not for the reduction.
fn add_nat_literal_axioms(env: &Environment) -> Environment {
    let nat_c = || Expr::const_(n("Nat"), vec![]);
    let bool_c = || Expr::const_(n("Bool"), vec![]);
    let arrow = |a: Expr, b: Expr| Expr::forall_e(n("_x"), a, b, BinderInfo::Default);
    let ax = |name: Name, type_: Expr| {
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name,
                level_params: vec![],
                type_,
            },
            is_unsafe: false,
        })
    };
    let mut env = add_info(env, ax(n("Nat"), sort1()));
    env = add_info(&env, ax(n("Bool"), sort1()));
    env = add_info(&env, ax(nn("Bool", "true"), bool_c()));
    env = add_info(&env, ax(nn("Bool", "false"), bool_c()));
    env = add_info(&env, ax(nn("Nat", "zero"), nat_c()));
    env = add_info(&env, ax(nn("Nat", "succ"), arrow(nat_c(), nat_c())));
    for op in [
        "add",
        "sub",
        "mul",
        "pow",
        "gcd",
        "mod",
        "div",
        "land",
        "lor",
        "xor",
        "shiftLeft",
        "shiftRight",
    ] {
        env = add_info(
            &env,
            ax(nn("Nat", op), arrow(nat_c(), arrow(nat_c(), nat_c()))),
        );
    }
    for op in ["beq", "ble", "blt"] {
        env = add_info(
            &env,
            ax(nn("Nat", op), arrow(nat_c(), arrow(nat_c(), bool_c()))),
        );
    }
    env
}

#[test]
fn kr313_the_pin_operation_table_computes_literal_results() {
    // The exact binary table of reduce_nat (pin type_checker.cpp:609), Lean
    // semantics pinned per row — truncated sub, x/0 = 0, x%0 = x — plus a
    // multi-limb carry so the fln-bignum wiring (not a u64 shortcut) is what
    // computes. A wrong op mapping (div↔mod swap, xor↔lor, …) fails its row.
    let env = add_nat_literal_axioms(&Environment::new());
    let table: &[(&str, u64, u64, u64)] = &[
        ("add", 2, 3, 5),
        ("sub", 5, 2, 3),
        ("sub", 2, 5, 0),
        ("mul", 7, 6, 42),
        ("div", 7, 2, 3),
        ("div", 7, 0, 0),
        ("mod", 7, 2, 1),
        ("mod", 7, 0, 7),
        ("gcd", 12, 18, 6),
        ("pow", 2, 10, 1024),
        ("pow", 7, 0, 1),
        ("land", 6, 3, 2),
        ("lor", 6, 3, 7),
        ("xor", 6, 3, 5),
        ("shiftLeft", 1, 8, 256),
        ("shiftRight", 256, 3, 32),
    ];
    for (op, a, b, expected) in table {
        assert!(
            check_def_eq(
                &env,
                &[],
                &nat_op_app(op, lit(*a), lit(*b)),
                &lit(*expected),
                Budget::DEFAULT
            )
            .is_accepted(),
            "Nat.{op} {a} {b} must compute to {expected}"
        );
    }
    // u64::MAX + 1 carries into a second limb: [0, 1].
    let carried = Expr::lit(Literal::Nat(NatLit::from_limbs_le(vec![0, 1])));
    assert!(
        check_def_eq(
            &env,
            &[],
            &nat_op_app("add", lit(u64::MAX), lit(1)),
            &carried,
            Budget::DEFAULT
        )
        .is_accepted(),
        "literal arithmetic must carry across limbs"
    );
    // And a discriminating negative: the table must not over-accept.
    assert_eq!(
        reject_class(&check_def_eq(
            &env,
            &[],
            &nat_op_app("add", lit(2), lit(3)),
            &lit(6),
            Budget::DEFAULT
        )),
        Some(RejectClass::NotDefEq),
        "2 + 3 is not 6"
    );
}

#[test]
fn kr313_comparisons_produce_bool_constants() {
    // beq/ble land on `Bool.true`/`Bool.false` (the pin's mk_bool_true/false).
    // The Bool.true rows also exercise the KR-313 reflection fast path (`t`
    // closed, `s` literally Bool.true ⇒ whnf `t`), which is how decide-style
    // proofs close. An inverted predicate fails the matching negative row.
    let env = add_nat_literal_axioms(&Environment::new());
    for (op, a, b, expected) in [
        ("beq", 2u64, 2u64, true),
        ("beq", 2, 3, false),
        ("ble", 2, 3, true),
        ("ble", 3, 3, true),
        ("ble", 3, 2, false),
    ] {
        let want = if expected { bool_true() } else { bool_false() };
        assert!(
            check_def_eq(
                &env,
                &[],
                &nat_op_app(op, lit(a), lit(b)),
                &want,
                Budget::DEFAULT
            )
            .is_accepted(),
            "Nat.{op} {a} {b} must be Bool.{expected}"
        );
    }
    assert_eq!(
        reject_class(&check_def_eq(
            &env,
            &[],
            &nat_op_app("beq", lit(2), lit(2)),
            &bool_false(),
            Budget::DEFAULT
        )),
        Some(RejectClass::NotDefEq),
        "2 == 2 is not Bool.false"
    );
}

#[test]
fn kr313_nat_zero_and_reduced_arguments_are_literal_operands() {
    // `is_nat_lit_ext` (pin :569): the bare constant `Nat.zero` counts as a
    // literal operand — and operands are whnf'd first, so an argument that is
    // itself literal arithmetic (succ towers included) reduces on the way in.
    let env = add_nat_literal_axioms(&Environment::new());
    let nat_zero = Expr::const_(nn("Nat", "zero"), vec![]);
    let succ = |e: Expr| Expr::app(Expr::const_(nn("Nat", "succ"), vec![]), e);
    assert!(
        check_def_eq(
            &env,
            &[],
            &nat_op_app("add", nat_zero.clone(), lit(3)),
            &lit(3),
            Budget::DEFAULT
        )
        .is_accepted(),
        "Nat.zero is a literal operand"
    );
    assert!(
        check_def_eq(&env, &[], &succ(nat_zero), &lit(1), Budget::DEFAULT).is_accepted(),
        "Nat.succ Nat.zero computes to the literal 1"
    );
    assert!(
        check_def_eq(
            &env,
            &[],
            &nat_op_app("add", lit(2), succ(succ(lit(1)))),
            &lit(5),
            Budget::DEFAULT
        )
        .is_accepted(),
        "arguments reduce (succ (succ 1) ⟶ 3) before the outer operation"
    );
}

#[test]
fn kr313_pow_honors_the_reduce_pow_max_exp_cap() {
    // The pin caps pow exponents at 2^24 (ReducePowMaxExp): at the cap the
    // operation computes; one past it the term stays STUCK (not Inconclusive,
    // not wrong) — killing a dropped-cap mutant, which would accept the
    // second row.
    let env = add_nat_literal_axioms(&Environment::new());
    let cap = 1u64 << 24;
    assert!(
        check_def_eq(
            &env,
            &[],
            &nat_op_app("pow", lit(1), lit(cap)),
            &lit(1),
            Budget::DEFAULT
        )
        .is_accepted(),
        "an exponent AT the cap computes"
    );
    assert_eq!(
        reject_class(&check_def_eq(
            &env,
            &[],
            &nat_op_app("pow", lit(1), lit(cap + 1)),
            &lit(1),
            Budget::DEFAULT
        )),
        Some(RejectClass::NotDefEq),
        "an exponent past the cap leaves the term stuck"
    );
}

#[test]
fn kr313_no_nat_blt_at_this_pin() {
    // Divergence note pinned as a test: the pin's reduce_nat table has NO
    // Nat.blt (beq/ble only), so `Nat.blt 2 3` must stay stuck rather than
    // compute to Bool.true. A table that helpfully adds blt diverges from the
    // pin and fails here.
    let env = add_nat_literal_axioms(&Environment::new());
    assert_eq!(
        reject_class(&check_def_eq(
            &env,
            &[],
            &nat_op_app("blt", lit(2), lit(3)),
            &bool_true(),
            Budget::DEFAULT
        )),
        Some(RejectClass::NotDefEq),
        "Nat.blt is not accelerated at this pin"
    );
}

#[test]
fn kr313_dispatch_requires_bare_heads_and_exact_arity() {
    // The pin compares whole head expressions (`f == *g_nat_add`), so a
    // level-decorated head, an over-applied spine, or an unknown Nat-namespace
    // name must all stay stuck.
    let env = add_nat_literal_axioms(&Environment::new());
    let leveled = Expr::app(
        Expr::app(Expr::const_(nn("Nat", "add"), vec![Level::zero()]), lit(2)),
        lit(3),
    );
    assert_eq!(
        reject_class(&check_def_eq(&env, &[], &leveled, &lit(5), Budget::DEFAULT)),
        Some(RejectClass::NotDefEq),
        "a level-bearing Nat.add head is not the pin's constant"
    );
    let over_applied = Expr::app(nat_op_app("add", lit(2), lit(3)), lit(4));
    assert_eq!(
        reject_class(&check_def_eq(
            &env,
            &[],
            &over_applied,
            &lit(5),
            Budget::DEFAULT
        )),
        Some(RejectClass::NotDefEq),
        "three arguments is not the binary table's arity"
    );
    assert_eq!(
        reject_class(&check_def_eq(
            &env,
            &[],
            &nat_op_app("quux", lit(2), lit(3)),
            &lit(5),
            Budget::DEFAULT
        )),
        Some(RejectClass::NotDefEq),
        "an unknown Nat-namespace operator stays stuck"
    );
}

#[test]
fn kr313_offset_closes_literal_vs_constructor_forms() {
    // The is_def_eq_offset machinery (pin :961): zero forms unify across the
    // literal/constant boundary, positive literals peel against symbolic
    // `Nat.succ` spines — in both orientations — and a peel that bottoms out
    // unequal is decisively NOT defeq. This is exactly the boundary the
    // kr316_nat_literal_majors comment marked as the KR-313 follow-up.
    let env = add_nat_with_rec(&Environment::new());
    let nat_zero = Expr::const_(nn("Nat", "zero"), vec![]);
    let succ = |e: Expr| Expr::app(Expr::const_(nn("Nat", "succ"), vec![]), e);
    assert!(
        check_def_eq(&env, &[], &nat_zero, &lit(0), Budget::DEFAULT).is_accepted(),
        "Nat.zero ≟ literal 0"
    );
    assert!(
        check_def_eq(&env, &[], &lit(1), &succ(nat_zero.clone()), Budget::DEFAULT).is_accepted(),
        "literal 1 ≟ Nat.succ Nat.zero"
    );
    assert!(
        check_def_eq(&env, &[], &succ(lit(4)), &lit(5), Budget::DEFAULT).is_accepted(),
        "Nat.succ (literal 4) ≟ literal 5 (symmetric orientation)"
    );
    assert_eq!(
        reject_class(&check_def_eq(
            &env,
            &[],
            &lit(2),
            &succ(nat_zero),
            Budget::DEFAULT
        )),
        Some(RejectClass::NotDefEq),
        "literal 2 peels to 1 against Nat.zero — decisively unequal"
    );
}

#[test]
fn kr313_delta_exposed_literals_decide_in_lazy_delta() {
    // The decoded-residual mechanics from franken_lean-d4x: a definition
    // unfolds to a literal only DURING lazy delta, so the offset/arithmetic
    // machinery must run inside that loop (pin lazy_delta_reduction, :973) —
    // running it only before delta leaves these stuck and false-rejects.
    let env = add_nat_with_rec(&Environment::new());
    let env = admit(
        &env,
        &defn("zeroDef", Expr::const_(n("Nat"), vec![]), lit(0)),
    );
    let env = admit(&env, &defn("two", Expr::const_(n("Nat"), vec![]), lit(2)));
    let nat_zero = Expr::const_(nn("Nat", "zero"), vec![]);
    let succ = |e: Expr| Expr::app(Expr::const_(nn("Nat", "succ"), vec![]), e);
    assert!(
        check_def_eq(
            &env,
            &[],
            &Expr::const_(n("zeroDef"), vec![]),
            &nat_zero,
            Budget::DEFAULT
        )
        .is_accepted(),
        "zeroDef delta-exposes literal 0, which the offset rule closes against Nat.zero"
    );
    assert!(
        check_def_eq(
            &env,
            &[],
            &Expr::const_(n("two"), vec![]),
            &succ(succ(Expr::const_(nn("Nat", "zero"), vec![]))),
            Budget::DEFAULT
        )
        .is_accepted(),
        "a symbolic succ tower computes to a literal inside lazy delta and matches `two`"
    );
}

#[test]
fn kr301_distinct_literals_are_decisively_not_defeq() {
    // The literal half of the quick rules (pin quick_is_def_eq, Lit case):
    // literal pairs decide by value with NO environment and NO reduction —
    // including across the Nat/String literal kinds. A mutant equating
    // distinct literals is an over-acceptance and dies here.
    let env = Environment::new();
    assert!(
        check_def_eq(&env, &[], &lit(2), &lit(2), Budget::DEFAULT).is_accepted(),
        "equal Nat literals are defeq"
    );
    for (t, s, label) in [
        (lit(2), lit(3), "distinct Nat literals"),
        (str_lit("a"), str_lit("b"), "distinct String literals"),
        (lit(97), str_lit("a"), "a Nat literal vs a String literal"),
    ] {
        assert_eq!(
            reject_class(&check_def_eq(&env, &[], &t, &s, Budget::DEFAULT)),
            Some(RejectClass::NotDefEq),
            "{label} must be decisively not defeq"
        );
    }
}

#[test]
fn fl_inv_07_oversized_shift_results_are_typed_exhaustion() {
    // A shiftLeft whose RESULT would dwarf the step budget converts to typed
    // Inconclusive BEFORE any allocation — never a rejection, never an
    // acceptance, never an abort (FL-INV-07). The pin has no such guard (it
    // grinds or exhausts memory); Behavior Note recorded on franken_lean-irm.
    let env = add_nat_literal_axioms(&Environment::new());
    let huge_count = nat_op_app("shiftLeft", lit(1), lit(1u64 << 40));
    let verdict = check_def_eq(&env, &[], &huge_count, &lit(0), Budget::DEFAULT);
    assert!(
        verdict.is_inconclusive() && !verdict.is_rejected() && !verdict.is_accepted(),
        "an infeasible shift is a verdict about the RUN, got {verdict:?}"
    );
    // A count beyond u64 entirely (2^64, limbs [0,1]) takes the same typed path.
    let beyond_u64 = nat_op_app(
        "shiftLeft",
        lit(1),
        Expr::lit(Literal::Nat(NatLit::from_limbs_le(vec![0, 1]))),
    );
    let verdict = check_def_eq(&env, &[], &beyond_u64, &lit(0), Budget::DEFAULT);
    assert!(
        verdict.is_inconclusive(),
        "a beyond-u64 shift count is typed exhaustion, got {verdict:?}"
    );
    // shiftRight only shrinks: the same beyond-u64 count simply zeroes.
    let shr_all = nat_op_app(
        "shiftRight",
        lit(7),
        Expr::lit(Literal::Nat(NatLit::from_limbs_le(vec![0, 1]))),
    );
    assert!(
        check_def_eq(&env, &[], &shr_all, &lit(0), Budget::DEFAULT).is_accepted(),
        "shifting right past every bit is zero"
    );
}

/// The KR-314 world at this pin, miniaturized honestly. At the pin, `String`
/// is ByteArray-backed (`ofByteArray ::`, Prelude:3505) and `String.ofList` is
/// a DEFINITION (Prelude:3525) — so every literal-expansion consumer must whnf
/// the generated `String.ofList …` spine down to the real constructor. This
/// fixture preserves exactly that must-unfold property: the constructor is
/// `String.mk (data : List.{0} Char)` and `String.ofList := fun data =>
/// String.mk data` is a Safe Regular definition. Builds on
/// `add_nat_literal_axioms` (Char.ofNat consumes Nat).
fn add_string_fixture(env: &Environment) -> Environment {
    let u = n("u");
    let sort_u1 = || Expr::sort(Level::param(n("u")).succ().expect("packs"));
    let list_u =
        |alpha: Expr| Expr::app(Expr::const_(n("List"), vec![Level::param(n("u"))]), alpha);
    let list0_char = || {
        Expr::app(
            Expr::const_(n("List"), vec![Level::zero()]),
            Expr::const_(n("Char"), vec![]),
        )
    };
    let string_c = || Expr::const_(n("String"), vec![]);
    let ax = |name: Name, level_params: Vec<Name>, type_: Expr| {
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name,
                level_params,
                type_,
            },
            is_unsafe: false,
        })
    };
    let mut env = add_info(env, ax(n("Char"), vec![], sort1()));
    env = add_info(
        &env,
        ax(
            nn("Char", "ofNat"),
            vec![],
            Expr::forall_e(
                n("_x"),
                Expr::const_(n("Nat"), vec![]),
                Expr::const_(n("Char"), vec![]),
                BinderInfo::Default,
            ),
        ),
    );
    // List.{u} : Sort (u+1) → Sort (u+1)
    env = add_info(
        &env,
        ax(
            n("List"),
            vec![u.clone()],
            Expr::forall_e(n("_a"), sort_u1(), sort_u1(), BinderInfo::Default),
        ),
    );
    // List.cons.{u} : ∀ (α : Sort (u+1)), α → List.{u} α → List.{u} α
    env = add_info(
        &env,
        ax(
            nn("List", "cons"),
            vec![u.clone()],
            Expr::forall_e(
                n("a"),
                sort_u1(),
                Expr::forall_e(
                    n("_h"),
                    Expr::bvar(0).expect("packs"),
                    Expr::forall_e(
                        n("_t"),
                        list_u(Expr::bvar(1).expect("packs")),
                        list_u(Expr::bvar(2).expect("packs")),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
        ),
    );
    // List.nil.{u} : ∀ (α : Sort (u+1)), List.{u} α
    env = add_info(
        &env,
        ax(
            nn("List", "nil"),
            vec![u.clone()],
            Expr::forall_e(
                n("a"),
                sort_u1(),
                list_u(Expr::bvar(0).expect("packs")),
                BinderInfo::Default,
            ),
        ),
    );
    // String: a one-constructor structure over List.{0} Char.
    env = add_info(
        &env,
        ConstantInfo::Induct(InductiveVal {
            base: ConstantVal {
                name: n("String"),
                level_params: vec![],
                type_: sort1(),
            },
            num_params: 0,
            num_indices: 0,
            all: vec![n("String")],
            ctors: vec![nn("String", "mk")],
            num_nested: 0,
            is_rec: false,
            is_unsafe: false,
            is_reflexive: false,
        }),
    );
    env = add_info(
        &env,
        ConstantInfo::Ctor(ConstructorVal {
            base: ConstantVal {
                name: nn("String", "mk"),
                level_params: vec![],
                type_: Expr::forall_e(n("data"), list0_char(), string_c(), BinderInfo::Default),
            },
            induct: n("String"),
            cidx: 0,
            num_params: 0,
            num_fields: 1,
            is_unsafe: false,
        }),
    );
    // String.ofList : List.{0} Char → String := fun data => String.mk data
    env = add_info(
        &env,
        ConstantInfo::Defn(DefinitionVal {
            base: ConstantVal {
                name: nn("String", "ofList"),
                level_params: vec![],
                type_: Expr::forall_e(n("data"), list0_char(), string_c(), BinderInfo::Default),
            },
            value: Expr::lam(
                n("data"),
                list0_char(),
                Expr::app(
                    Expr::const_(nn("String", "mk"), vec![]),
                    Expr::bvar(0).expect("packs"),
                ),
                BinderInfo::Default,
            ),
            hints: ReducibilityHints::Regular(1),
            safety: DefinitionSafety::Safe,
            all: vec![nn("String", "ofList")],
        }),
    );
    // String.rec.{u} : ∀ motive, (∀ data, motive (String.mk data)) → ∀ t, motive t
    let motive_ty = Expr::forall_e(
        n("_t"),
        string_c(),
        Expr::sort(Level::param(u.clone())),
        BinderInfo::Default,
    );
    let minor_ty = |motive_bvar: u32| {
        Expr::forall_e(
            n("data"),
            list0_char(),
            Expr::app(
                Expr::bvar(motive_bvar + 1).expect("packs"),
                Expr::app(
                    Expr::const_(nn("String", "mk"), vec![]),
                    Expr::bvar(0).expect("packs"),
                ),
            ),
            BinderInfo::Default,
        )
    };
    let rec_ty = Expr::forall_e(
        n("motive"),
        motive_ty.clone(),
        Expr::forall_e(
            n("m"),
            minor_ty(0),
            Expr::forall_e(
                n("t"),
                string_c(),
                Expr::app(Expr::bvar(2).expect("packs"), Expr::bvar(0).expect("packs")),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    // mk-rule rhs: fun motive m data => m data
    let rhs = Expr::lam(
        n("motive"),
        motive_ty,
        Expr::lam(
            n("m"),
            minor_ty(0),
            Expr::lam(
                n("data"),
                list0_char(),
                Expr::app(Expr::bvar(1).expect("packs"), Expr::bvar(0).expect("packs")),
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
                name: nn("String", "rec"),
                level_params: vec![u],
                type_: rec_ty,
            },
            all: vec![n("String")],
            num_params: 0,
            num_indices: 0,
            num_motives: 1,
            num_minors: 1,
            rules: vec![RecursorRule {
                ctor: nn("String", "mk"),
                nfields: 1,
                rhs,
            }],
            k: false,
            is_unsafe: false,
        }),
    )
}

/// The `List.cons.{0} Char (Char.ofNat cᵢ) …` spine for the given code points,
/// hand-rolled here as an independent oracle for the kernel's generator.
fn char_list_spine(codes: &[u64]) -> Expr {
    let char_c = Expr::const_(n("Char"), vec![]);
    let cons = Expr::app(
        Expr::const_(nn("List", "cons"), vec![Level::zero()]),
        char_c.clone(),
    );
    let nil = Expr::app(Expr::const_(nn("List", "nil"), vec![Level::zero()]), char_c);
    let of_nat = Expr::const_(nn("Char", "ofNat"), vec![]);
    let mut spine = nil;
    for code in codes.iter().rev() {
        spine = Expr::app(
            Expr::app(cons.clone(), Expr::app(of_nat.clone(), lit(*code))),
            spine,
        );
    }
    spine
}

fn of_list_app(spine: Expr) -> Expr {
    Expr::app(Expr::const_(nn("String", "ofList"), vec![]), spine)
}

#[test]
fn kr314_string_literal_defeq_its_oflist_spine() {
    // The defeq half of KR-314 (pin try_string_lit_expansion + reduce_proj_core
    // string expansion): a String literal equals its `String.ofList` code-point
    // spine — in both orientations — and mismatched or reordered code points
    // are decisively rejected, killing wrong-value and unreversed-fold mutants
    // in the expansion generator.
    let env = add_string_fixture(&add_nat_literal_axioms(&Environment::new()));
    assert!(
        check_def_eq(
            &env,
            &[],
            &str_lit("ab"),
            &of_list_app(char_list_spine(&[97, 98])),
            Budget::DEFAULT
        )
        .is_accepted(),
        "\"ab\" ≟ String.ofList ['a','b']"
    );
    assert!(
        check_def_eq(
            &env,
            &[],
            &of_list_app(char_list_spine(&[97, 98])),
            &str_lit("ab"),
            Budget::DEFAULT
        )
        .is_accepted(),
        "the expansion works in the symmetric orientation"
    );
    assert!(
        check_def_eq(
            &env,
            &[],
            &str_lit(""),
            &of_list_app(char_list_spine(&[])),
            Budget::DEFAULT
        )
        .is_accepted(),
        "the empty string is the nil spine"
    );
    // Unicode: 'λ' is code point 955 — one char, one cons cell.
    assert!(
        check_def_eq(
            &env,
            &[],
            &str_lit("λ"),
            &of_list_app(char_list_spine(&[955])),
            Budget::DEFAULT
        )
        .is_accepted(),
        "expansion decodes code points, not bytes"
    );
    assert_eq!(
        reject_class(&check_def_eq(
            &env,
            &[],
            &str_lit("ab"),
            &of_list_app(char_list_spine(&[97, 99])),
            Budget::DEFAULT
        )),
        Some(RejectClass::NotDefEq),
        "a wrong code point is decisively unequal"
    );
    assert_eq!(
        reject_class(&check_def_eq(
            &env,
            &[],
            &str_lit("ab"),
            &of_list_app(char_list_spine(&[98, 97])),
            Budget::DEFAULT
        )),
        Some(RejectClass::NotDefEq),
        "reversed code points are decisively unequal (kills an unreversed-fold mutant)"
    );
}

#[test]
fn kr314_projection_expands_string_literal_scrutinees() {
    // The reduce_proj half (pin reduce_proj_core, :358): projecting field 0
    // out of a String LITERAL expands the literal, whnfs `String.ofList` down
    // to the constructor, and extracts the spine.
    let env = add_string_fixture(&add_nat_literal_axioms(&Environment::new()));
    let proj = Expr::proj(n("String"), 0, str_lit("ab"));
    assert!(
        check_def_eq(
            &env,
            &[],
            &proj,
            &char_list_spine(&[97, 98]),
            Budget::DEFAULT
        )
        .is_accepted(),
        "(\"ab\").data reduces to the ['a','b'] spine"
    );
    assert_eq!(
        reject_class(&check_def_eq(
            &env,
            &[],
            &proj,
            &char_list_spine(&[98, 97]),
            Budget::DEFAULT
        )),
        Some(RejectClass::NotDefEq),
        "the projected spine is order-exact"
    );
}

#[test]
fn kr314_string_recursor_fires_on_a_literal_major() {
    // The iota half (pin inductive.h:95): a String-literal major expands and
    // whnfs to the constructor, the mk-rule fires, and the minor receives the
    // spine. A mutant that skips the whnf after expansion leaves the major
    // `String.ofList`-headed — no rule matches and this stays stuck.
    let env = add_string_fixture(&add_nat_literal_axioms(&Environment::new()));
    // motive SM : String → Sort 1 and minor sm : ∀ data, SM (String.mk data).
    let env = add_info(
        &env,
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("SM"),
                level_params: vec![],
                type_: Expr::forall_e(
                    n("_t"),
                    Expr::const_(n("String"), vec![]),
                    sort1(),
                    BinderInfo::Default,
                ),
            },
            is_unsafe: false,
        }),
    );
    let list0_char = Expr::app(
        Expr::const_(n("List"), vec![Level::zero()]),
        Expr::const_(n("Char"), vec![]),
    );
    let env = add_info(
        &env,
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("sm"),
                level_params: vec![],
                type_: Expr::forall_e(
                    n("data"),
                    list0_char,
                    Expr::app(
                        Expr::const_(n("SM"), vec![]),
                        Expr::app(
                            Expr::const_(nn("String", "mk"), vec![]),
                            Expr::bvar(0).expect("packs"),
                        ),
                    ),
                    BinderInfo::Default,
                ),
            },
            is_unsafe: false,
        }),
    );
    let mut rec_app = Expr::const_(nn("String", "rec"), vec![Level::one()]);
    for arg in [
        Expr::const_(n("SM"), vec![]),
        Expr::const_(n("sm"), vec![]),
        str_lit("a"),
    ] {
        rec_app = Expr::app(rec_app, arg);
    }
    assert!(
        check_def_eq(
            &env,
            &[],
            &rec_app,
            &Expr::app(Expr::const_(n("sm"), vec![]), char_list_spine(&[97])),
            Budget::DEFAULT
        )
        .is_accepted(),
        "String.rec on \"a\" reduces to `sm ['a']`"
    );
    assert_eq!(
        reject_class(&check_def_eq(
            &env,
            &[],
            &rec_app,
            &Expr::app(Expr::const_(n("sm"), vec![]), char_list_spine(&[98])),
            Budget::DEFAULT
        )),
        Some(RejectClass::NotDefEq),
        "the recursor delivers the literal's actual code points"
    );
}

// ---- KR-6xx/7xx/8xx/95x/97x: block admission (bead franken_lean-ap6) ----------------

use fln_kernel::InductiveBlock;

fn cval(name: Name, level_params: Vec<Name>, type_: Expr) -> ConstantVal {
    ConstantVal {
        name,
        level_params,
        type_,
    }
}

/// A single-type block declaration from raw parts.
fn block_decl(
    types: Vec<InductiveVal>,
    ctors: Vec<ConstructorVal>,
    recursors: Vec<RecursorVal>,
) -> Declaration {
    Declaration::Inductive(InductiveBlock {
        types,
        ctors,
        recursors,
    })
}

/// `MyNat` — a large-eliminating recursive type — with its decoded rows
/// exactly as the pin's generation produces them (the acceptance test IS the
/// regeneration cross-check: any drift in elim levels, K-targeting, implicit
/// inference, minor naming, or iota rhs shape rejects).
fn mynat_block() -> (Vec<InductiveVal>, Vec<ConstructorVal>, Vec<RecursorVal>) {
    let mynat = || Expr::const_(n("MyNat"), vec![]);
    let ind = InductiveVal {
        base: cval(n("MyNat"), vec![], sort1()),
        num_params: 0,
        num_indices: 0,
        all: vec![n("MyNat")],
        ctors: vec![nn("MyNat", "zero"), nn("MyNat", "succ")],
        num_nested: 0,
        is_rec: true,
        is_unsafe: false,
        is_reflexive: false,
    };
    let zero = ConstructorVal {
        base: cval(nn("MyNat", "zero"), vec![], mynat()),
        induct: n("MyNat"),
        cidx: 0,
        num_params: 0,
        num_fields: 0,
        is_unsafe: false,
    };
    let succ = ConstructorVal {
        base: cval(
            nn("MyNat", "succ"),
            vec![],
            Expr::forall_e(n("n"), mynat(), mynat(), BinderInfo::Default),
        ),
        induct: n("MyNat"),
        cidx: 1,
        num_params: 0,
        num_fields: 1,
        is_unsafe: false,
    };
    // MyNat.rec.{u} : {motive : MyNat → Sort u} → motive MyNat.zero →
    //   ((n : MyNat) → motive n → motive (MyNat.succ n)) → (t : MyNat) → motive t
    let u = Level::param(n("u"));
    let motive_ty = Expr::forall_e(n("t"), mynat(), Expr::sort(u.clone()), BinderInfo::Default);
    let bv = |i: u32| Expr::bvar(i).expect("packs");
    let succ_minor_ty = |motive: Expr| {
        // (n : MyNat) → motive n → motive (MyNat.succ n), motive at the given bvar
        Expr::forall_e(
            n("n"),
            mynat(),
            Expr::forall_e(
                n("n_ih"),
                Expr::app(shift(&motive, 1), bv(0)),
                Expr::app(
                    shift(&motive, 2),
                    Expr::app(Expr::const_(nn("MyNat", "succ"), vec![]), bv(1)),
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        )
    };
    let rec_ty = Expr::forall_e(
        n("motive"),
        motive_ty.clone(),
        Expr::forall_e(
            n("zero"),
            Expr::app(bv(0), Expr::const_(nn("MyNat", "zero"), vec![])),
            Expr::forall_e(
                n("succ"),
                succ_minor_ty(bv(1)),
                Expr::forall_e(
                    n("t"),
                    mynat(),
                    Expr::app(bv(3), bv(0)),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Implicit,
    );
    // zero rule rhs: fun (motive) (zero) (succ) => zero
    let zero_rhs = Expr::lam(
        n("motive"),
        motive_ty.clone(),
        Expr::lam(
            n("zero"),
            Expr::app(bv(0), Expr::const_(nn("MyNat", "zero"), vec![])),
            Expr::lam(n("succ"), succ_minor_ty(bv(1)), bv(1), BinderInfo::Default),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    // succ rule rhs: fun motive zero succ (n) => succ n (MyNat.rec.{u} motive zero succ n)
    let rec_call = {
        let mut app = Expr::const_(nn("MyNat", "rec"), vec![u]);
        for arg in [bv(3), bv(2), bv(1), bv(0)] {
            app = Expr::app(app, arg);
        }
        app
    };
    let succ_rhs = Expr::lam(
        n("motive"),
        motive_ty.clone(),
        Expr::lam(
            n("zero"),
            Expr::app(bv(0), Expr::const_(nn("MyNat", "zero"), vec![])),
            Expr::lam(
                n("succ"),
                succ_minor_ty(bv(1)),
                Expr::lam(
                    n("n"),
                    mynat(),
                    Expr::app(Expr::app(bv(1), bv(0)), rec_call),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let rec = RecursorVal {
        base: cval(nn("MyNat", "rec"), vec![n("u")], rec_ty),
        all: vec![n("MyNat")],
        num_params: 0,
        num_indices: 0,
        num_motives: 1,
        num_minors: 2,
        rules: vec![
            RecursorRule {
                ctor: nn("MyNat", "zero"),
                nfields: 0,
                rhs: zero_rhs,
            },
            RecursorRule {
                ctor: nn("MyNat", "succ"),
                nfields: 1,
                rhs: succ_rhs,
            },
        ],
        k: false,
        is_unsafe: false,
    };
    (vec![ind], vec![zero, succ], vec![rec])
}

/// Shift loose bvars in `e` up by `d` (test helper for hand-built types).
fn shift(e: &Expr, d: u32) -> Expr {
    fn go(e: &Expr, d: u32, cutoff: u32) -> Expr {
        match e.node() {
            ExprNode::BVar { idx } if *idx >= cutoff => Expr::bvar(idx + d).expect("packs"),
            ExprNode::App { f, a } => Expr::app(go(f, d, cutoff), go(a, d, cutoff)),
            ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => Expr::lam(
                binder_name.clone(),
                go(binder_type, d, cutoff),
                go(body, d, cutoff + 1),
                *binder_info,
            ),
            ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => Expr::forall_e(
                binder_name.clone(),
                go(binder_type, d, cutoff),
                go(body, d, cutoff + 1),
                *binder_info,
            ),
            _ => e.clone(),
        }
    }
    go(e, d, 0)
}

fn reject_message(verdict: &Verdict) -> String {
    match verdict {
        Verdict::Rejected { message, .. } => message.clone(),
        other => panic!("expected rejection, got {other:?}"),
    }
}

#[test]
fn kr6xx_a_recursive_block_admits_with_byte_exact_recursor_regeneration() {
    // The acceptance test IS the KR-800..803 cross-check: the decoded rows
    // (flags, counts, elim level, K, implicit inference, minor/ih naming,
    // iota right-hand sides) must equal the kernel's own regeneration
    // byte-for-byte. An inverted KR-604 universe condition, a dropped
    // consume_type_annotations, or any generation drift rejects this block.
    let (types, ctors, recursors) = mynat_block();
    let verdict = check(
        &Environment::new(),
        &block_decl(types, ctors, recursors),
        Budget::DEFAULT,
    );
    assert!(
        verdict.is_accepted(),
        "MyNat block must admit; got {verdict:?}"
    );
}

#[test]
fn kr606_negative_occurrences_are_rejected() {
    // MANDATED MUTANT (AGENTS testing policy: "skipped positivity check"):
    // `Bad.mk : (Bad → Bad) → Bad` places the block in a Π DOMAIN — the
    // classic non-positive occurrence that makes the theory inconsistent.
    // The assertion pins the positivity MESSAGE, so a mutant that skips
    // check_positivity fails here even if a later cross-check still rejects.
    let bad = || Expr::const_(n("Bad"), vec![]);
    let ind = InductiveVal {
        base: cval(n("Bad"), vec![], sort1()),
        num_params: 0,
        num_indices: 0,
        all: vec![n("Bad")],
        ctors: vec![nn("Bad", "mk")],
        num_nested: 0,
        is_rec: true,
        is_unsafe: false,
        is_reflexive: true,
    };
    let mk = ConstructorVal {
        base: cval(
            nn("Bad", "mk"),
            vec![],
            Expr::forall_e(
                n("f"),
                Expr::forall_e(n("x"), bad(), bad(), BinderInfo::Default),
                bad(),
                BinderInfo::Default,
            ),
        ),
        induct: n("Bad"),
        cidx: 0,
        num_params: 0,
        num_fields: 1,
        is_unsafe: false,
    };
    let verdict = check(
        &Environment::new(),
        &block_decl(vec![ind], vec![mk], vec![]),
        Budget::DEFAULT,
    );
    assert_eq!(reject_class(&verdict), Some(RejectClass::BlockMismatch));
    assert!(
        reject_message(&verdict).contains("non positive"),
        "the rejection must be the KR-606 positivity judgment, got: {}",
        reject_message(&verdict)
    );
}

#[test]
fn kr604_oversized_constructor_fields_are_rejected() {
    // MANDATED MUTANT (AGENTS testing policy: "inverted universe condition"):
    // a `Type`-level datatype with a `Type 1` field violates KR-604. The
    // message is pinned; the ACCEPT side of the same condition is pinned by
    // the MyNat test (an inversion rejects every valid block).
    let big = || Expr::const_(n("Big"), vec![]);
    let ind = InductiveVal {
        base: cval(n("Big"), vec![], sort1()),
        num_params: 0,
        num_indices: 0,
        all: vec![n("Big")],
        ctors: vec![nn("Big", "mk")],
        num_nested: 0,
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    };
    let mk = ConstructorVal {
        base: cval(
            nn("Big", "mk"),
            vec![],
            Expr::forall_e(n("x"), sort1(), big(), BinderInfo::Default),
        ),
        induct: n("Big"),
        cidx: 0,
        num_params: 0,
        num_fields: 1,
        is_unsafe: false,
    };
    let verdict = check(
        &Environment::new(),
        &block_decl(vec![ind], vec![mk], vec![]),
        Budget::DEFAULT,
    );
    assert_eq!(reject_class(&verdict), Some(RejectClass::BlockMismatch));
    assert!(
        reject_message(&verdict).contains("too big"),
        "the rejection must be the KR-604 universe judgment, got: {}",
        reject_message(&verdict)
    );
}

#[test]
fn kr605_indices_may_not_mention_the_block() {
    // Soundness-critical (pin is_valid_ind_app, leanprover/lean4#2125): a
    // constructor whose RESULT applies the inductive to an index that itself
    // mentions the block must reject.
    let ind = InductiveVal {
        base: cval(
            n("J"),
            vec![],
            Expr::forall_e(n("i"), prop(), prop(), BinderInfo::Default),
        ),
        num_params: 0,
        num_indices: 1,
        all: vec![n("J")],
        ctors: vec![nn("J", "mk")],
        num_nested: 0,
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    };
    let env = admit(&Environment::new(), &axiom("TrueP", prop()));
    let mk = ConstructorVal {
        base: cval(
            nn("J", "mk"),
            vec![],
            Expr::app(
                Expr::const_(n("J"), vec![]),
                Expr::app(
                    Expr::const_(n("J"), vec![]),
                    Expr::const_(n("TrueP"), vec![]),
                ),
            ),
        ),
        induct: n("J"),
        cidx: 0,
        num_params: 0,
        num_fields: 0,
        is_unsafe: false,
    };
    let verdict = check(
        &env,
        &block_decl(vec![ind], vec![mk], vec![]),
        Budget::DEFAULT,
    );
    assert_eq!(reject_class(&verdict), Some(RejectClass::BlockMismatch));
    assert!(
        reject_message(&verdict).contains("invalid return type"),
        "the rejection must be the KR-605 occurrence judgment, got: {}",
        reject_message(&verdict)
    );
}

#[test]
fn kr700_restricted_elimination_and_kr317_k_flags_are_regenerated() {
    // Two decoded-observable cross-checks that kill comparison-drop mutants:
    // (a) `W : Prop` with two nullary constructors is elimination-restricted
    // (KR-700) — a decoded recursor claiming the large-elim level parameter
    // must reject; (b) MyNat's recursor decoded with `k: true` must reject
    // (K-targeting is REGENERATED, never trusted).
    let w = || Expr::const_(n("W"), vec![]);
    let ind = InductiveVal {
        base: cval(n("W"), vec![], prop()),
        num_params: 0,
        num_indices: 0,
        all: vec![n("W")],
        ctors: vec![nn("W", "a"), nn("W", "b")],
        num_nested: 0,
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    };
    let ctor = |name: Name, cidx: u32| ConstructorVal {
        base: cval(name, vec![], w()),
        induct: n("W"),
        cidx,
        num_params: 0,
        num_fields: 0,
        is_unsafe: false,
    };
    // A decoded recursor that wrongly claims LARGE elimination (level param).
    let wrong_rec = RecursorVal {
        base: cval(
            nn("W", "rec"),
            vec![n("u")],
            Expr::sort(Level::one()), // shape is irrelevant; lparams diverge first
        ),
        all: vec![n("W")],
        num_params: 0,
        num_indices: 0,
        num_motives: 1,
        num_minors: 2,
        rules: vec![],
        k: false,
        is_unsafe: false,
    };
    let verdict = check(
        &Environment::new(),
        &block_decl(
            vec![ind],
            vec![ctor(nn("W", "a"), 0), ctor(nn("W", "b"), 1)],
            vec![wrong_rec],
        ),
        Budget::DEFAULT,
    );
    assert_eq!(
        reject_class(&verdict),
        Some(RejectClass::BlockMismatch),
        "a Prop 2-ctor type eliminates only into Prop — large-elim lparams must reject"
    );
    // (b) K-flag forgery on an otherwise byte-exact MyNat recursor.
    let (types, ctors, mut recursors) = mynat_block();
    recursors[0].k = true;
    let verdict = check(
        &Environment::new(),
        &block_decl(types, ctors, recursors),
        Budget::DEFAULT,
    );
    assert_eq!(reject_class(&verdict), Some(RejectClass::BlockMismatch));
    assert!(
        reject_message(&verdict).contains("observables diverge"),
        "K is regenerated, never trusted; got: {}",
        reject_message(&verdict)
    );
}

#[test]
fn kr317_a_k_target_block_admits_with_k_true() {
    // `MyTrue : Prop` with one nullary constructor is a K-target that still
    // eliminates LARGE (empty to_check ⇒ KR-701 passes): the generated
    // recursor carries k=true and the elim level parameter. An
    // always-false K-targeting mutant rejects this acceptance.
    let mytrue = || Expr::const_(n("MyTrue"), vec![]);
    let ind = InductiveVal {
        base: cval(n("MyTrue"), vec![], prop()),
        num_params: 0,
        num_indices: 0,
        all: vec![n("MyTrue")],
        ctors: vec![nn("MyTrue", "intro")],
        num_nested: 0,
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    };
    let intro = ConstructorVal {
        base: cval(nn("MyTrue", "intro"), vec![], mytrue()),
        induct: n("MyTrue"),
        cidx: 0,
        num_params: 0,
        num_fields: 0,
        is_unsafe: false,
    };
    let u = Level::param(n("u"));
    let bv = |i: u32| Expr::bvar(i).expect("packs");
    let motive_ty = Expr::forall_e(n("t"), mytrue(), Expr::sort(u), BinderInfo::Default);
    let rec_ty = Expr::forall_e(
        n("motive"),
        motive_ty.clone(),
        Expr::forall_e(
            n("intro"),
            Expr::app(bv(0), Expr::const_(nn("MyTrue", "intro"), vec![])),
            Expr::forall_e(
                n("t"),
                mytrue(),
                Expr::app(bv(2), bv(0)),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Implicit,
    );
    let rhs = Expr::lam(
        n("motive"),
        motive_ty,
        Expr::lam(
            n("intro"),
            Expr::app(bv(0), Expr::const_(nn("MyTrue", "intro"), vec![])),
            bv(0),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let rec = RecursorVal {
        base: cval(nn("MyTrue", "rec"), vec![n("u")], rec_ty),
        all: vec![n("MyTrue")],
        num_params: 0,
        num_indices: 0,
        num_motives: 1,
        num_minors: 1,
        rules: vec![RecursorRule {
            ctor: nn("MyTrue", "intro"),
            nfields: 0,
            rhs,
        }],
        k: true,
        is_unsafe: false,
    };
    let verdict = check(
        &Environment::new(),
        &block_decl(vec![ind], vec![intro], vec![rec]),
        Budget::DEFAULT,
    );
    assert!(
        verdict.is_accepted(),
        "MyTrue is a K-target with large elimination; got {verdict:?}"
    );
}

#[test]
fn kr700_a_restricted_block_admits_with_prop_elimination() {
    // `W : Prop` with TWO nullary constructors eliminates only into Prop
    // (KR-700): the generated recursor has NO extra level parameter and its
    // motive lands in Sort 0. An elimination-restriction-drop mutant
    // generates the large-elim recursor instead and rejects this acceptance.
    let w = || Expr::const_(n("W"), vec![]);
    let ind = InductiveVal {
        base: cval(n("W"), vec![], prop()),
        num_params: 0,
        num_indices: 0,
        all: vec![n("W")],
        ctors: vec![nn("W", "a"), nn("W", "b")],
        num_nested: 0,
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    };
    let ctor = |name: Name, cidx: u32| ConstructorVal {
        base: cval(name, vec![], w()),
        induct: n("W"),
        cidx,
        num_params: 0,
        num_fields: 0,
        is_unsafe: false,
    };
    let bv = |i: u32| Expr::bvar(i).expect("packs");
    let motive_ty = Expr::forall_e(n("t"), w(), prop(), BinderInfo::Default);
    let rec_ty = Expr::forall_e(
        n("motive"),
        motive_ty.clone(),
        Expr::forall_e(
            n("a"),
            Expr::app(bv(0), Expr::const_(nn("W", "a"), vec![])),
            Expr::forall_e(
                n("b"),
                Expr::app(bv(1), Expr::const_(nn("W", "b"), vec![])),
                Expr::forall_e(n("t"), w(), Expr::app(bv(3), bv(0)), BinderInfo::Default),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Implicit,
    );
    let minor_domain =
        |i: u32, ctor_leaf: &str| Expr::app(bv(i), Expr::const_(nn("W", ctor_leaf), vec![]));
    let rhs_a = Expr::lam(
        n("motive"),
        motive_ty.clone(),
        Expr::lam(
            n("a"),
            minor_domain(0, "a"),
            Expr::lam(n("b"), minor_domain(1, "b"), bv(1), BinderInfo::Default),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let rhs_b = Expr::lam(
        n("motive"),
        motive_ty,
        Expr::lam(
            n("a"),
            minor_domain(0, "a"),
            Expr::lam(n("b"), minor_domain(1, "b"), bv(0), BinderInfo::Default),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let rec = RecursorVal {
        base: cval(nn("W", "rec"), vec![], rec_ty),
        all: vec![n("W")],
        num_params: 0,
        num_indices: 0,
        num_motives: 1,
        num_minors: 2,
        rules: vec![
            RecursorRule {
                ctor: nn("W", "a"),
                nfields: 0,
                rhs: rhs_a,
            },
            RecursorRule {
                ctor: nn("W", "b"),
                nfields: 0,
                rhs: rhs_b,
            },
        ],
        k: false,
        is_unsafe: false,
    };
    let verdict = check(
        &Environment::new(),
        &block_decl(
            vec![ind],
            vec![ctor(nn("W", "a"), 0), ctor(nn("W", "b"), 1)],
            vec![rec],
        ),
        Budget::DEFAULT,
    );
    assert!(
        verdict.is_accepted(),
        "a 2-ctor Prop inductive admits with Prop-restricted elimination; got {verdict:?}"
    );
}

#[test]
fn kr607_decoded_flags_are_cross_checked() {
    // The decoded is_rec flag is UNTRUSTED: MyNat decoded as non-recursive
    // must reject (a flags-comparison-drop mutant dies here).
    let (mut types, ctors, recursors) = mynat_block();
    types[0].is_rec = false;
    let verdict = check(
        &Environment::new(),
        &block_decl(types, ctors, recursors),
        Budget::DEFAULT,
    );
    assert_eq!(reject_class(&verdict), Some(RejectClass::BlockMismatch));
    assert!(
        reject_message(&verdict).contains("recursivity flags"),
        "got: {}",
        reject_message(&verdict)
    );
}

#[test]
fn kr95x_quotient_initialization_requires_the_exact_eq_shape() {
    // KR-950: without the expected `Eq`, quotient initialization rejects.
    let verdict = check(
        &Environment::new(),
        &Declaration::Quotient(vec![]),
        Budget::DEFAULT,
    );
    assert_eq!(reject_class(&verdict), Some(RejectClass::BlockMismatch));
    assert!(
        reject_message(&verdict).contains("does not have 'Eq'"),
        "got: {}",
        reject_message(&verdict)
    );
}

#[test]
fn kr973_nonsafe_definitions_check_and_safe_references_are_gated() {
    // Pin add_definition/add_mutual semantics: a PARTIAL definition may
    // reference itself (header → add → body in the scratch env); a SAFE
    // definition may reference neither partial nor unsafe declarations
    // (KR-973), while an UNSAFE definition may reference unsafe ones.
    let env = admit(&Environment::new(), &axiom("A", sort1()));
    let a = || Expr::const_(n("A"), vec![]);
    let mk_defn = |name: &str, safety: DefinitionSafety, value: Expr| {
        Declaration::Defn(DefinitionVal {
            base: cval(
                n(name),
                vec![],
                Expr::forall_e(n("x"), a(), a(), BinderInfo::Default),
            ),
            value,
            hints: ReducibilityHints::Regular(1),
            safety,
            all: vec![n(name)],
        })
    };
    // Self-recursive partial: fun (x : A) => selfRec x — legal only because
    // the body checks AFTER the scratch add.
    let self_body = Expr::lam(
        n("x"),
        a(),
        Expr::app(
            Expr::const_(n("selfRec"), vec![]),
            Expr::bvar(0).expect("packs"),
        ),
        BinderInfo::Default,
    );
    let partial_decl = mk_defn("selfRec", DefinitionSafety::Partial, self_body.clone());
    let verdict = check(&env, &partial_decl, Budget::DEFAULT);
    assert!(
        verdict.is_accepted(),
        "self-recursive partial definitions admit via the scratch env; got {verdict:?}"
    );
    // The SAME body as a SAFE definition rejects: no pre-add, unknown constant
    // (rename to keep the one-name law out of the picture).
    let safe_self = Declaration::Defn(DefinitionVal {
        base: cval(
            n("selfSafe"),
            vec![],
            Expr::forall_e(n("x"), a(), a(), BinderInfo::Default),
        ),
        value: Expr::lam(
            n("x"),
            a(),
            Expr::app(
                Expr::const_(n("selfSafe"), vec![]),
                Expr::bvar(0).expect("packs"),
            ),
            BinderInfo::Default,
        ),
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Safe,
        all: vec![n("selfSafe")],
    });
    assert_eq!(
        reject_class(&check(&env, &safe_self, Budget::DEFAULT)),
        Some(RejectClass::UnknownConstant),
        "safe definitions cannot be self-recursive"
    );
    // Admit the partial def, then: a SAFE definition referencing it rejects
    // (KR-973), an UNSAFE definition referencing an unsafe one admits.
    let env = add_info(
        &env,
        ConstantInfo::Defn(DefinitionVal {
            base: cval(
                n("selfRec"),
                vec![],
                Expr::forall_e(n("x"), a(), a(), BinderInfo::Default),
            ),
            value: self_body,
            hints: ReducibilityHints::Regular(1),
            safety: DefinitionSafety::Partial,
            all: vec![n("selfRec")],
        }),
    );
    let safe_uses_partial = mk_defn(
        "usesPartial",
        DefinitionSafety::Safe,
        Expr::const_(n("selfRec"), vec![]),
    );
    assert_eq!(
        reject_class(&check(&env, &safe_uses_partial, Budget::DEFAULT)),
        Some(RejectClass::SafetyViolation),
        "a safe definition must not reference a partial one (KR-973)"
    );
    let unsafe_id = mk_defn(
        "unsafeId",
        DefinitionSafety::Unsafe,
        Expr::lam(
            n("x"),
            a(),
            Expr::bvar(0).expect("packs"),
            BinderInfo::Default,
        ),
    );
    let verdict = check(&env, &unsafe_id, Budget::DEFAULT);
    assert!(
        verdict.is_accepted(),
        "unsafe definitions admit; got {verdict:?}"
    );
    let env = add_info(
        &env,
        ConstantInfo::Defn(DefinitionVal {
            base: cval(
                n("unsafeId"),
                vec![],
                Expr::forall_e(n("x"), a(), a(), BinderInfo::Default),
            ),
            value: Expr::lam(
                n("x"),
                a(),
                Expr::bvar(0).expect("packs"),
                BinderInfo::Default,
            ),
            hints: ReducibilityHints::Regular(1),
            safety: DefinitionSafety::Unsafe,
            all: vec![n("unsafeId")],
        }),
    );
    assert_eq!(
        reject_class(&check(
            &env,
            &mk_defn(
                "safeUsesUnsafe",
                DefinitionSafety::Safe,
                Expr::const_(n("unsafeId"), vec![])
            ),
            Budget::DEFAULT
        )),
        Some(RejectClass::SafetyViolation),
        "a safe definition must not reference an unsafe one (KR-973)"
    );
    let uses_unsafe = mk_defn(
        "unsafeUsesUnsafe",
        DefinitionSafety::Unsafe,
        Expr::const_(n("unsafeId"), vec![]),
    );
    let verdict = check(&env, &uses_unsafe, Budget::DEFAULT);
    assert!(
        verdict.is_accepted(),
        "unsafe may reference unsafe; got {verdict:?}"
    );
}

#[test]
fn kr310_projection_congruence_on_stuck_scrutinees() {
    // KR-310's projection half (pin is_def_eq_core:1101): same-index
    // projections close on defeq scrutinees. The scrutinees here are recursor
    // applications STUCK on an opaque major — whnf cannot reduce the
    // projection away, and one side hides a metadata wrapper inside the spine,
    // so only scrutinee-level defeq (which strips it) can close the pair.
    // This is byte-for-byte the shape of the final Init.Prelude residual
    // (List.get.match_1: `PProd.0 (List.rec … x)` against the same term with
    // mdata around `x`).
    let env = add_nat_with_rec(&Environment::new());
    let env = add_structure(&env, "PP", "PP.mk", sort1(), &[sort1()]);
    let nat_c = Expr::const_(n("Nat"), vec![]);
    let env = add_info(
        &env,
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("nx"),
                level_params: vec![],
                type_: nat_c.clone(),
            },
            is_unsafe: false,
        }),
    );
    let env = add_info(
        &env,
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("ny"),
                level_params: vec![],
                type_: nat_c,
            },
            is_unsafe: false,
        }),
    );
    let (env, _) = nat_rec_app(&env, Expr::const_(n("nx"), vec![]));
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
    let plain = rec_on(Expr::const_(n("nx"), vec![]));
    let wrapped = rec_on(Expr::mdata(KVMap::default(), Expr::const_(n("nx"), vec![])));
    assert!(
        check_def_eq(
            &env,
            &[],
            &Expr::proj(n("PP"), 0, plain.clone()),
            &Expr::proj(n("PP"), 0, wrapped.clone()),
            Budget::DEFAULT
        )
        .is_accepted(),
        "same-index projections of defeq stuck scrutinees are defeq"
    );
    assert_eq!(
        reject_class(&check_def_eq(
            &env,
            &[],
            &Expr::proj(n("PP"), 0, plain.clone()),
            &Expr::proj(n("PP"), 1, wrapped),
            Budget::DEFAULT
        )),
        Some(RejectClass::NotDefEq),
        "DIFFERENT indices do not close (kills a dropped-index-guard mutant)"
    );
    assert_eq!(
        reject_class(&check_def_eq(
            &env,
            &[],
            &Expr::proj(n("PP"), 0, plain),
            &Expr::proj(n("PP"), 0, rec_on(Expr::const_(n("ny"), vec![]))),
            Budget::DEFAULT
        )),
        Some(RejectClass::NotDefEq),
        "projections of NON-defeq scrutinees stay apart"
    );
}

// ---------------------------------------------------------------------------
// KR-608: the nested-inductive auxiliary translation (bead franken_lean-8ce).
//
// `MyTree` nests `MyList MyTree` (the minimal analogue of Lean.Syntax nesting
// `Array Syntax`): admission must translate the occurrence into an auxiliary
// copy of `MyList` instantiated at `MyTree`, run the FULL ruleset on the
// synthesized two-type mutual block, regenerate BOTH recursors, restore
// (`MyTree.rec`, `MyTree.rec_1`, original constructor names), and compare
// byte-exactly against the decoded rows below — which are hand-built in
// exactly the restored form the pin serializes.
// ---------------------------------------------------------------------------

/// The environment rows the translation copies: a plain parameterized
/// `MyList` (α : Type) with nil/cons, monomorphic for fixture clarity.
fn mylist_env() -> Environment {
    let mylist = InductiveVal {
        base: cval(
            n("MyList"),
            vec![],
            Expr::forall_e(n("α"), sort1(), sort1(), BinderInfo::Default),
        ),
        num_params: 1,
        num_indices: 0,
        all: vec![n("MyList")],
        ctors: vec![nn("MyList", "nil"), nn("MyList", "cons")],
        num_nested: 0,
        is_rec: true,
        is_unsafe: false,
        is_reflexive: false,
    };
    let bv = |i: u32| Expr::bvar(i).expect("packs");
    let nil = ConstructorVal {
        base: cval(
            nn("MyList", "nil"),
            vec![],
            Expr::forall_e(
                n("α"),
                sort1(),
                Expr::app(Expr::const_(n("MyList"), vec![]), bv(0)),
                BinderInfo::Default,
            ),
        ),
        induct: n("MyList"),
        cidx: 0,
        num_params: 1,
        num_fields: 0,
        is_unsafe: false,
    };
    let cons = ConstructorVal {
        base: cval(
            nn("MyList", "cons"),
            vec![],
            Expr::forall_e(
                n("α"),
                sort1(),
                Expr::forall_e(
                    n("head"),
                    bv(0),
                    Expr::forall_e(
                        n("tail"),
                        Expr::app(Expr::const_(n("MyList"), vec![]), bv(1)),
                        Expr::app(Expr::const_(n("MyList"), vec![]), bv(2)),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
        ),
        induct: n("MyList"),
        cidx: 1,
        num_params: 1,
        num_fields: 2,
        is_unsafe: false,
    };
    Environment::new()
        .add_decl(ConstantInfo::Induct(mylist))
        .expect("env")
        .add_decl(ConstantInfo::Ctor(nil))
        .expect("env")
        .add_decl(ConstantInfo::Ctor(cons))
        .expect("env")
}

/// The decoded (restored-form) nested block: `MyTree.node : MyList MyTree →
/// MyTree`, with the two restored recursors the pin would serialize.
fn mytree_block() -> (Vec<InductiveVal>, Vec<ConstructorVal>, Vec<RecursorVal>) {
    let tree = || Expr::const_(n("MyTree"), vec![]);
    let mlt = || Expr::app(Expr::const_(n("MyList"), vec![]), tree());
    let bv = |i: u32| Expr::bvar(i).expect("packs");
    let u = Level::param(n("u"));
    let ind = InductiveVal {
        base: cval(n("MyTree"), vec![], sort1()),
        num_params: 0,
        num_indices: 0,
        all: vec![n("MyTree")],
        ctors: vec![nn("MyTree", "node")],
        num_nested: 1,
        is_rec: true,
        is_unsafe: false,
        is_reflexive: false,
    };
    let node = ConstructorVal {
        base: cval(
            nn("MyTree", "node"),
            vec![],
            Expr::forall_e(n("l"), mlt(), tree(), BinderInfo::Default),
        ),
        induct: n("MyTree"),
        cidx: 0,
        num_params: 0,
        num_fields: 1,
        is_unsafe: false,
    };
    // Shared telescope: {motive_1 : MyTree → Sort u} {motive_2 : MyList
    // MyTree → Sort u} (node …) (nil …) (cons …); result binders differ.
    let motive_1_ty = Expr::forall_e(n("t"), tree(), Expr::sort(u.clone()), BinderInfo::Default);
    let motive_2_ty = Expr::forall_e(n("t"), mlt(), Expr::sort(u.clone()), BinderInfo::Default);
    // node : Π (l : MyList MyTree), motive_2 l → motive_1 (MyTree.node l)
    // (at intro: m1 = #1, m2 = #0)
    let node_minor_ty = Expr::forall_e(
        n("l"),
        mlt(),
        Expr::forall_e(
            n("l_ih"),
            Expr::app(bv(1), bv(0)),
            Expr::app(
                bv(3),
                Expr::app(Expr::const_(nn("MyTree", "node"), vec![]), bv(1)),
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    // nil : motive_2 (MyList.nil MyTree)   (at intro: m1 = #2, m2 = #1)
    let nil_minor_ty = Expr::app(
        bv(1),
        Expr::app(Expr::const_(nn("MyList", "nil"), vec![]), tree()),
    );
    // cons : Π (head : MyTree) (tail : MyList MyTree), motive_1 head →
    //   motive_2 tail → motive_2 (MyList.cons MyTree head tail)
    // (at intro: m1 = #3, m2 = #2)
    let cons_minor_ty = Expr::forall_e(
        n("head"),
        tree(),
        Expr::forall_e(
            n("tail"),
            mlt(),
            Expr::forall_e(
                n("head_ih"),
                Expr::app(bv(5), bv(1)),
                Expr::forall_e(
                    n("tail_ih"),
                    Expr::app(bv(5), bv(1)),
                    Expr::app(
                        bv(6),
                        Expr::app(
                            Expr::app(
                                Expr::app(Expr::const_(nn("MyList", "cons"), vec![]), tree()),
                                bv(3),
                            ),
                            bv(2),
                        ),
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let telescope = |major_ty: Expr, result_motive_at: u32| {
        Expr::forall_e(
            n("motive_1"),
            motive_1_ty.clone(),
            Expr::forall_e(
                n("motive_2"),
                motive_2_ty.clone(),
                Expr::forall_e(
                    n("node"),
                    node_minor_ty.clone(),
                    Expr::forall_e(
                        n("nil"),
                        nil_minor_ty.clone(),
                        Expr::forall_e(
                            n("cons"),
                            cons_minor_ty.clone(),
                            Expr::forall_e(
                                n("t"),
                                major_ty,
                                Expr::app(bv(result_motive_at), bv(0)),
                                BinderInfo::Default,
                            ),
                            BinderInfo::Default,
                        ),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Implicit,
            ),
            BinderInfo::Implicit,
        )
    };
    let rec_ty = telescope(tree(), 5);
    let rec_1_ty = telescope(mlt(), 4);
    // Rule right-hand sides: λ motive_1 motive_2 node nil cons fields… .
    let lam5 = |body: Expr, field_lams: &[(Name, Expr)]| {
        let mut inner = body;
        for (name, ty) in field_lams.iter().rev() {
            inner = Expr::lam(name.clone(), ty.clone(), inner, BinderInfo::Default);
        }
        Expr::lam(
            n("motive_1"),
            motive_1_ty.clone(),
            Expr::lam(
                n("motive_2"),
                motive_2_ty.clone(),
                Expr::lam(
                    n("node"),
                    node_minor_ty.clone(),
                    Expr::lam(
                        n("nil"),
                        nil_minor_ty.clone(),
                        Expr::lam(n("cons"), cons_minor_ty.clone(), inner, BinderInfo::Default),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        )
    };
    let rec_call = |rec: &str, args: &[u32]| {
        let mut app = Expr::const_(nn("MyTree", rec), vec![u.clone()]);
        for a in args {
            app = Expr::app(app, bv(*a));
        }
        app
    };
    // node rule: … (l) => node l (MyTree.rec_1 m1 m2 node nil cons l)
    let node_rhs = lam5(
        Expr::app(
            Expr::app(bv(3), bv(0)),
            rec_call("rec_1", &[5, 4, 3, 2, 1, 0]),
        ),
        &[(n("l"), mlt())],
    );
    // nil rule: … => nil
    let nil_rhs = lam5(bv(1), &[]);
    // cons rule: … (head) (tail) => cons head tail (MyTree.rec … head)
    //   (MyTree.rec_1 … tail)
    let cons_rhs = lam5(
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(bv(2), bv(1)), bv(0)),
                rec_call("rec", &[6, 5, 4, 3, 2, 1]),
            ),
            rec_call("rec_1", &[6, 5, 4, 3, 2, 0]),
        ),
        &[(n("head"), tree()), (n("tail"), mlt())],
    );
    let mk_rec = |name: Name, ty: Expr, rules: Vec<RecursorRule>| RecursorVal {
        base: cval(name, vec![n("u")], ty),
        all: vec![n("MyTree")],
        num_params: 0,
        num_indices: 0,
        num_motives: 2,
        num_minors: 3,
        rules,
        k: false,
        is_unsafe: false,
    };
    let rec = mk_rec(
        nn("MyTree", "rec"),
        rec_ty,
        vec![RecursorRule {
            ctor: nn("MyTree", "node"),
            nfields: 1,
            rhs: node_rhs,
        }],
    );
    let rec_1 = mk_rec(
        nn("MyTree", "rec_1"),
        rec_1_ty,
        vec![
            RecursorRule {
                ctor: nn("MyList", "nil"),
                nfields: 0,
                rhs: nil_rhs,
            },
            RecursorRule {
                ctor: nn("MyList", "cons"),
                nfields: 2,
                rhs: cons_rhs,
            },
        ],
    );
    (vec![ind], vec![node], vec![rec, rec_1])
}

#[test]
fn kr608_nested_block_admits_with_byte_exact_translated_regeneration() {
    // The acceptance test IS the translation: positivity and regeneration run
    // on the synthesized `MyTree + _nested.MyList` block, and the restored
    // recursors (renamed, original constructor names, original occurrences
    // re-instated) must equal these hand-built restored rows byte-for-byte.
    let (types, ctors, recursors) = mytree_block();
    let verdict = check(
        &mylist_env(),
        &block_decl(types, ctors, recursors),
        Budget::DEFAULT,
    );
    assert!(
        verdict.is_accepted(),
        "nested MyTree block must admit under the FULL ruleset; got {verdict:?}"
    );
}

#[test]
fn kr608_positivity_is_enforced_through_the_translation() {
    // MUTANT (bead franken_lean-8ce: "skipped positivity on the translated
    // block"): nest `MyList (MyTree → MyTree)` — the occurrence is nested
    // (its parameter mentions the block), and the auxiliary copy places
    // `MyTree` in a Π domain, so KR-606 must fire ON THE TRANSLATED BLOCK.
    let (mut types, mut ctors, recursors) = mytree_block();
    let bad_field = Expr::app(
        Expr::const_(n("MyList"), vec![]),
        Expr::forall_e(
            n("x"),
            Expr::const_(n("MyTree"), vec![]),
            Expr::const_(n("MyTree"), vec![]),
            BinderInfo::Default,
        ),
    );
    ctors[0].base.type_ = Expr::forall_e(
        n("l"),
        bad_field,
        Expr::const_(n("MyTree"), vec![]),
        BinderInfo::Default,
    );
    types[0].is_reflexive = true;
    let verdict = check(
        &mylist_env(),
        &block_decl(types, ctors, recursors),
        Budget::DEFAULT,
    );
    assert_eq!(reject_class(&verdict), Some(RejectClass::BlockMismatch));
    assert!(
        reject_message(&verdict).contains("non positive"),
        "the rejection must be the KR-606 positivity judgment on the \
         translated block, got: {}",
        reject_message(&verdict)
    );
}

#[test]
fn kr608_decoded_nested_recursors_are_never_trusted() {
    // MUTANT ("trusted decoded rules" / "corrupted motive-minor mapping"):
    // swap the two rule right-hand sides of the decoded auxiliary recursor.
    // A kernel that trusted the decoded rows would admit the corruption; the
    // translated regeneration must catch it byte-exactly.
    let (types, ctors, mut recursors) = mytree_block();
    let rhs0 = recursors[1].rules[0].rhs.clone();
    recursors[1].rules[0].rhs = recursors[1].rules[1].rhs.clone();
    recursors[1].rules[1].rhs = rhs0;
    let verdict = check(
        &mylist_env(),
        &block_decl(types, ctors, recursors),
        Budget::DEFAULT,
    );
    assert_eq!(reject_class(&verdict), Some(RejectClass::BlockMismatch));
    assert!(
        reject_message(&verdict).contains("diverges from regeneration"),
        "decoded auxiliary rules must be regenerated, never trusted: {}",
        reject_message(&verdict)
    );
}

#[test]
fn kr608_num_nested_must_count_the_minted_auxiliaries() {
    // MUTANT ("altered auxiliary accounting"): the decoded num_nested claims
    // two auxiliaries where the translation mints exactly one.
    let (mut types, ctors, recursors) = mytree_block();
    types[0].num_nested = 2;
    let verdict = check(
        &mylist_env(),
        &block_decl(types, ctors, recursors),
        Budget::DEFAULT,
    );
    assert_eq!(reject_class(&verdict), Some(RejectClass::BlockMismatch));
    assert!(
        reject_message(&verdict).contains("num_nested"),
        "auxiliary count must be cross-checked: {}",
        reject_message(&verdict)
    );
}

#[test]
fn kr608_phantom_nesting_rejects() {
    // MUTANT ("removed/misrouted nested occurrence"): num_nested is nonzero
    // but no constructor field actually nests — the translation must refuse
    // to fabricate auxiliaries.
    let (mut types, mut ctors, mut recursors) = mytree_block();
    ctors[0].base.type_ = Expr::forall_e(
        n("l"),
        Expr::const_(n("MyTree"), vec![]),
        Expr::const_(n("MyTree"), vec![]),
        BinderInfo::Default,
    );
    types[0].num_nested = 1;
    recursors.truncate(1);
    let verdict = check(
        &mylist_env(),
        &block_decl(types, ctors, recursors),
        Budget::DEFAULT,
    );
    assert_eq!(reject_class(&verdict), Some(RejectClass::BlockMismatch));
    assert!(
        reject_message(&verdict).contains("no nested occurrence"),
        "phantom nesting must reject typed: {}",
        reject_message(&verdict)
    );
}

#[test]
fn kr608_translate_back_restores_the_original_recursor_names() {
    // MUTANT ("broken translate-back"): the decoded auxiliary recursor
    // carries the wrong restored name — the by-name match must fail typed,
    // never fall back to positional trust.
    let (types, ctors, mut recursors) = mytree_block();
    recursors[1].base.name = nn("MyTree", "rec_2");
    let verdict = check(
        &mylist_env(),
        &block_decl(types, ctors, recursors),
        Budget::DEFAULT,
    );
    assert_eq!(reject_class(&verdict), Some(RejectClass::BlockMismatch));
    assert!(
        reject_message(&verdict).contains("lacks recursor"),
        "restored recursor names must match by name: {}",
        reject_message(&verdict)
    );
}

#[test]
fn kr608_nested_translation_exhaustion_is_typed() {
    // FL-INV-07 on the translation path: a starved budget yields
    // Inconclusive — never acceptance, never rejection.
    let (types, ctors, recursors) = mytree_block();
    let verdict = check(
        &mylist_env(),
        &block_decl(types, ctors, recursors),
        Budget {
            steps: 5,
            depth: 4096,
        },
    );
    assert!(
        verdict.is_inconclusive(),
        "budget exhaustion in the translation must be typed Inconclusive; got {verdict:?}"
    );
    assert!(!verdict.is_accepted() && !verdict.is_rejected());
}
