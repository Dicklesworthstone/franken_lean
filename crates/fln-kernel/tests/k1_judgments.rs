//! K1 bootstrap judgment tests (bead franken_lean-zht), each tagged to its
//! KERNEL_CONTRACT.md rule and driven ONLY through the public authority
//! (`check` / `check_def_eq`) — the kernel has no other door.

#![forbid(unsafe_code)]

use fln_core::diag::ResourceReason;
use fln_core::expr::{BinderInfo, Expr, ExprNode, FVarId, Literal, NatLit};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::{Authority, CacheAdmission, InconclusiveCause, Outcome, ResourceUsage};
use fln_env::constants::{
    AxiomVal, ConstantInfo, ConstantVal, ConstructorVal, DefinitionSafety, DefinitionVal,
    InductiveVal, OpaqueVal, QuotKind, QuotVal, RecursorRule, RecursorVal, ReducibilityHints,
    TheoremVal,
};
use fln_env::environment::{DeclarationBudget, Environment};
use fln_env::pmap::CollisionBudget;
use fln_kernel::capability::{Published, admit as capability_admit};
use fln_kernel::council::{Council, CouncilOutcome, convene};
use fln_kernel::verdict::{Budget, RejectClass, Verdict};
use fln_kernel::{Declaration, check, check_def_eq};

trait KernelOutcomeAssertions {
    fn is_accepted(&self) -> bool;
    fn is_rejected(&self) -> bool;
    fn is_inconclusive(&self) -> bool;
}

impl KernelOutcomeAssertions for Outcome<Verdict> {
    fn is_accepted(&self) -> bool {
        matches!(self, Outcome::Complete(Verdict::Accepted { .. }))
    }

    fn is_rejected(&self) -> bool {
        matches!(self, Outcome::Complete(Verdict::Rejected { .. }))
    }

    fn is_inconclusive(&self) -> bool {
        matches!(self, Outcome::Inconclusive(_))
    }
}

fn exhausted_usage(outcome: &Outcome<Verdict>) -> &ResourceUsage {
    match outcome {
        Outcome::Inconclusive(inconclusive) => match &inconclusive.cause {
            InconclusiveCause::ResourceExhausted { usage } => usage,
            other => panic!("expected resource exhaustion, got {other:?}"),
        },
        other => panic!("expected an inconclusive kernel outcome, got {other:?}"),
    }
}

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
        Declaration::Opaque(v) => ConstantInfo::Opaque(v),
        // Block declarations use their own admission helpers in these tests.
        Declaration::Mutual(_) | Declaration::Inductive(_) | Declaration::Quotient(_) => {
            unreachable!("admit() is only used for single-constant declarations")
        }
    };
    env.add_decl(info).expect("kernel-accepted decl adds")
}

fn reject_class(verdict: &Outcome<Verdict>) -> Option<RejectClass> {
    match verdict {
        Outcome::Complete(Verdict::Rejected { class, .. }) => Some(*class),
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
fn kr972_a_declaration_type_that_is_not_a_sort_is_rejected() {
    // KR-972: a declaration's TYPE must itself check to a sort. The existing
    // kr104_kr972 case covers the direction where it does; a mutation campaign
    // found the refusal unguarded — deleting the check left all 98 tests
    // passing, because nothing ever declared something whose type is not a
    // type.
    //
    // `dd : D` and `D : Sort 1`, so the type expression `dd` infers to `D`,
    // which is a Const and not a Sort. Admitting `bad : dd` would put a
    // constant in the environment whose type is not a type at all, and every
    // later judgment about `bad` would be reasoning about a non-type.
    let env = admit(&Environment::new(), &axiom("D", sort1()));
    let env = admit(&env, &axiom("dd", Expr::const_(n("D"), vec![])));
    let verdict = check(
        &env,
        &axiom("bad", Expr::const_(n("dd"), vec![])),
        Budget::DEFAULT,
    );
    assert_eq!(
        reject_class(&verdict),
        Some(RejectClass::SortExpected),
        "a declaration whose type is not a sort must be refused; got {verdict:?}"
    );

    // CONTROL: the same shape one level up still admits, so this is not a
    // blanket refusal of constants-as-types.
    assert!(
        check(
            &env,
            &axiom("fine", Expr::const_(n("D"), vec![])),
            Budget::DEFAULT
        )
        .is_accepted(),
        "a declaration whose type IS a sort-typed constant must still admit"
    );
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
fn kr102_free_variables_are_telescope_bound_or_rejected() {
    // A caller-supplied fvar has no local declaration and must never acquire a
    // type by name coincidence or defaulting.
    let unknown = Expr::fvar(FVarId(n("x")));
    let verdict = check(&Environment::new(), &axiom("bad", unknown), Budget::DEFAULT);
    assert_eq!(
        reject_class(&verdict),
        Some(RejectClass::UnknownFVar),
        "an fvar outside the kernel's local telescope must be a typed rejection"
    );

    // CONTROL: public binders are opened to fresh fvars internally and those
    // locals do type correctly. This arm keeps the test discriminating rather
    // than accepting a blanket refusal of every fvar.
    let identity = defn(
        "id",
        Expr::forall_e(n("A"), sort1(), sort1(), BinderInfo::Default),
        Expr::lam(
            n("A"),
            sort1(),
            Expr::bvar(0).expect("packs"),
            BinderInfo::Default,
        ),
    );
    let verdict = check(&Environment::new(), &identity, Budget::DEFAULT);
    assert!(
        verdict.is_accepted(),
        "a fresh fvar introduced by a valid binder telescope must type; got {verdict:?}"
    );
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
fn kr105_unknown_constants_are_rejected() {
    let missing = Expr::const_(n("Missing"), vec![]);
    let verdict = check(&Environment::new(), &axiom("bad", missing), Budget::DEFAULT);
    assert_eq!(
        reject_class(&verdict),
        Some(RejectClass::UnknownConstant),
        "a constant absent from the environment must be a typed rejection"
    );

    // CONTROL: the same declaration shape admits when the referenced constant
    // is present with a sort-typed declaration.
    let env = admit(&Environment::new(), &axiom("Present", sort1()));
    let verdict = check(
        &env,
        &axiom("good", Expr::const_(n("Present"), vec![])),
        Budget::DEFAULT,
    );
    assert!(
        verdict.is_accepted(),
        "a present constant with the right universe arity must type; got {verdict:?}"
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
    // The identity-function check under a 5-step budget: must be an
    // outcome-level Inconclusive with bounded usage facts — categorically not
    // a domain verdict.
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
    let tiny = Budget::DEFAULT.narrowed(5, 4096);
    let verdict = check(
        &Environment::new(),
        &defn("id", ty.clone(), value.clone()),
        tiny,
    );
    let usage = exhausted_usage(&verdict);
    assert!(usage.observed > tiny.steps);
    assert_eq!(usage.allowed, tiny.steps);
    assert_eq!(usage.reason, ResourceReason::ExecutionSteps);
    assert_eq!(
        verdict.cache_admission(),
        CacheAdmission::Refused {
            authority: Authority::NonAuthoritative,
        }
    );
    assert!(verdict.as_complete().is_none());

    // Depth exhaustion likewise. The checker now peels this consecutive
    // lambda/Pi telescope iteratively, so depth 1 is sufficient; a zero-depth
    // allowance forces the first genuine nested judgment to stop without
    // reinstating stack growth merely to preserve the old fixture.
    let shallow = Budget::DEFAULT.narrowed(1_000_000, 0);
    let verdict = check(&Environment::new(), &defn("id", ty, value), shallow);
    let usage = exhausted_usage(&verdict);
    assert_eq!(
        usage.reason,
        ResourceReason::RecursionDepth {
            limit: u64::from(shallow.depth),
        }
    );
    assert_eq!(usage.allowed, u64::from(shallow.depth));
    assert!(usage.observed > usage.allowed);
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

/// A safe definition can expose a recursor whose major is itself stuck.  This
/// is the pin-independent shape behind `Init.PropLemmas.ite_not`:
/// `instDecidableNot p h` unfolds to a match on the opaque decision `h`, and
/// that stuck match becomes the major of an outer match.
///
/// Before the identity result was cached in `whnf_recursor_chain`, the
/// suspended outer reduction reopened the safe definition forever.  The real
/// declaration consumed every 10,000,001-step default budget; this structural
/// witness must instead return the ordinary `NotDefEq` answer under 512 steps.
#[test]
fn kr316_stuck_recursor_exposed_by_a_definition_terminates_under_an_outer_recursor() {
    let env = add_enum_e(&Environment::new());
    let e = Expr::const_(n("E"), vec![]);
    let motive = Expr::lam(n("_"), e.clone(), e.clone(), BinderInfo::Default);
    let fold_e = |major: Expr| {
        let mut app = Expr::const_(nn("E", "rec"), vec![Level::one()]);
        for arg in [
            motive.clone(),
            Expr::const_(nn("E", "a"), vec![]),
            Expr::const_(nn("E", "b"), vec![]),
            major,
        ] {
            app = Expr::app(app, arg);
        }
        app
    };

    let env = admit(&env, &axiom("e0", e.clone()));
    let exposing_body = Expr::lam(
        n("major"),
        e.clone(),
        fold_e(Expr::bvar(0).expect("packs")),
        BinderInfo::Default,
    );
    let exposing_type = Expr::forall_e(n("major"), e.clone(), e.clone(), BinderInfo::Default);
    let env = admit(&env, &defn("exposeStuck", exposing_type, exposing_body));

    let exposed = Expr::app(
        Expr::const_(n("exposeStuck"), vec![]),
        Expr::const_(n("e0"), vec![]),
    );
    let outer = fold_e(exposed);
    let verdict = check_def_eq(
        &env,
        &[],
        &outer,
        &Expr::const_(nn("E", "a"), vec![]),
        Budget::DEFAULT.narrowed(512, 32),
    );

    assert_eq!(
        reject_class(&verdict),
        Some(RejectClass::NotDefEq),
        "a nested stuck recursor must terminate as ordinary inequality, not exhaust: {verdict:?}"
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
        Budget::DEFAULT.narrowed(2_000, 64),
    );
    assert!(
        verdict.is_inconclusive(),
        "budget exhaustion in an iota chain is Inconclusive, got {verdict:?}"
    );
}

#[test]
fn nested_recursor_majors_use_steps_instead_of_logical_depth() {
    // Each outer recursor must normalize another recursor before it can choose
    // its own rule. The Reference uses native recursion for this chain; K1
    // carries an explicit continuation stack so hostile nesting remains inside
    // the governed step budget. Keeping the logical depth allowance at 64
    // makes a recursive mutant fail as typed exhaustion long before host-stack
    // safety could be involved.
    const NESTING: usize = 256;
    let env = add_nat_with_rec(&Environment::new());
    let nat = Expr::const_(n("Nat"), vec![]);
    let zero = Expr::const_(nn("Nat", "zero"), vec![]);
    let succ = Expr::const_(nn("Nat", "succ"), vec![]);
    let motive = Expr::lam(n("t"), nat.clone(), nat.clone(), BinderInfo::Default);
    let succ_minor = Expr::lam(
        n("n"),
        nat.clone(),
        Expr::lam(
            n("ih"),
            nat,
            Expr::app(succ, Expr::bvar(0).expect("packs")),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let rec_on = |major: Expr| {
        let mut app = Expr::const_(nn("Nat", "rec"), vec![Level::one()]);
        for arg in [motive.clone(), zero.clone(), succ_minor.clone(), major] {
            app = Expr::app(app, arg);
        }
        app
    };
    let mut nested = zero.clone();
    for _ in 0..NESTING {
        nested = rec_on(nested);
    }

    let verdict = check_def_eq(
        &env,
        &[],
        &nested,
        &zero,
        Budget::DEFAULT.narrowed(250_000, 64),
    );
    assert!(
        verdict.is_accepted(),
        "an explicit recursor-major worklist must normalize {NESTING} nested majors; got {verdict:?}"
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
fn kr317_k_conversion_refuses_a_major_whose_index_does_not_match_the_constructor() {
    // KR-317's GATE. K conversion replaces an opaque major with the nullary
    // constructor, but only after checking that the constructor's type is defeq
    // to the major's. `kr317_k_like_recursor_reduces_an_opaque_proof` above
    // covers the direction where K must FIRE; a mutation campaign found the
    // direction where it must NOT fire completely unguarded — replacing the
    // defeq gate with `if false` left all 97 tests passing, even though the
    // gate is reached (a planted panic there fires in exactly one test).
    //
    // SOUNDNESS STAKE, and it is the worst in the campaign so far. `E` here is
    // Eq-shaped: one parameter, one index, one constructor `E.refl : (a : D) →
    // E a a`. For an opaque `h : E x y` the nullary constructor at those
    // parameters is `E.refl x : E x x`, which is NOT defeq to `E x y`. Without
    // the gate the kernel rewrites `h` to `E.refl x` and iota-reduces, so a
    // recursor application at index `y` computes as though it were at `x` —
    // that is a proof of `x = y` for arbitrary distinct `x` and `y`.
    let env = admit(&Environment::new(), &axiom("D", sort1()));
    let d = || Expr::const_(n("D"), vec![]);
    let env = admit(&env, &axiom("x", d()));
    let env = admit(&env, &axiom("y", d()));
    let x = || Expr::const_(n("x"), vec![]);
    let y = || Expr::const_(n("y"), vec![]);
    let e = || Expr::const_(n("E"), vec![]);
    let bv = |i: u32| Expr::bvar(i).expect("packs");
    let u = n("u");

    // E : (a : D) → D → Prop, with `a` a parameter and the second D an index.
    let env = add_info(
        &env,
        ConstantInfo::Induct(InductiveVal {
            base: cval(
                n("E"),
                vec![],
                Expr::forall_e(
                    n("a"),
                    d(),
                    Expr::forall_e(n("b"), d(), prop(), BinderInfo::Default),
                    BinderInfo::Default,
                ),
            ),
            num_params: 1,
            num_indices: 1,
            all: vec![n("E")],
            ctors: vec![nn("E", "refl")],
            num_nested: 0,
            is_rec: false,
            is_unsafe: false,
            is_reflexive: false,
        }),
    );
    // E.refl : (a : D) → E a a
    let env = add_info(
        &env,
        ConstantInfo::Ctor(ConstructorVal {
            base: cval(
                nn("E", "refl"),
                vec![],
                Expr::forall_e(
                    n("a"),
                    d(),
                    Expr::app(Expr::app(e(), bv(0)), bv(0)),
                    BinderInfo::Default,
                ),
            ),
            induct: n("E"),
            cidx: 0,
            num_params: 1,
            num_fields: 0,
            is_unsafe: false,
        }),
    );

    // motive : (b : D) → E a b → Sort u   (under the `a` binder)
    let motive_ty = Expr::forall_e(
        n("b"),
        d(),
        Expr::forall_e(
            n("h"),
            Expr::app(Expr::app(e(), bv(1)), bv(0)),
            Expr::sort(Level::param(u.clone())),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    // refl_case : motive a (E.refl a)   (under a, motive)
    let refl_case_ty = Expr::app(
        Expr::app(bv(0), bv(1)),
        Expr::app(Expr::const_(nn("E", "refl"), vec![]), bv(1)),
    );
    // E.rec : {a} {motive} (refl_case) {b} (h : E a b) → motive b h
    let rec_ty = Expr::forall_e(
        n("a"),
        d(),
        Expr::forall_e(
            n("motive"),
            motive_ty.clone(),
            Expr::forall_e(
                n("refl_case"),
                refl_case_ty.clone(),
                Expr::forall_e(
                    n("b"),
                    d(),
                    Expr::forall_e(
                        n("h"),
                        Expr::app(Expr::app(e(), bv(3)), bv(0)),
                        Expr::app(Expr::app(bv(3), bv(1)), bv(0)),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Implicit,
        ),
        BinderInfo::Implicit,
    );
    // rule rhs: fun a motive refl_case => refl_case
    let rhs = Expr::lam(
        n("a"),
        d(),
        Expr::lam(
            n("motive"),
            motive_ty,
            Expr::lam(n("refl_case"), refl_case_ty, bv(0), BinderInfo::Default),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let env = add_info(
        &env,
        ConstantInfo::Rec(RecursorVal {
            base: cval(nn("E", "rec"), vec![u], rec_ty),
            all: vec![n("E")],
            num_params: 1,
            num_indices: 1,
            num_motives: 1,
            num_minors: 1,
            rules: vec![RecursorRule {
                ctor: nn("E", "refl"),
                nfields: 0,
                rhs,
            }],
            k: true,
            is_unsafe: false,
        }),
    );
    // EM : (b : D) → E x b → Sort 1;  ec : EM x (E.refl x);  h : E x y
    let env = admit(
        &env,
        &axiom(
            "EM",
            Expr::forall_e(
                n("b"),
                d(),
                Expr::forall_e(
                    n("h"),
                    Expr::app(Expr::app(e(), x()), bv(0)),
                    sort1(),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
        ),
    );
    let em = || Expr::const_(n("EM"), vec![]);
    let env = admit(
        &env,
        &axiom(
            "ec",
            Expr::app(
                Expr::app(em(), x()),
                Expr::app(Expr::const_(nn("E", "refl"), vec![]), x()),
            ),
        ),
    );
    let env = admit(&env, &axiom("h", Expr::app(Expr::app(e(), x()), y())));

    // E.rec.{1} x EM ec y h  —  stuck, because K may not rewrite `h : E x y`
    // into `E.refl x : E x x`.
    let mut lhs = Expr::const_(nn("E", "rec"), vec![Level::one()]);
    for arg in [
        x(),
        em(),
        Expr::const_(n("ec"), vec![]),
        y(),
        Expr::const_(n("h"), vec![]),
    ] {
        lhs = Expr::app(lhs, arg);
    }
    assert!(
        !check_def_eq(
            &env,
            &[],
            &lhs,
            &Expr::const_(n("ec"), vec![]),
            Budget::DEFAULT
        )
        .is_accepted(),
        "K conversion must NOT fire when the nullary constructor's type is not \
         defeq to the major's: reducing here proves `x = y` for distinct x, y"
    );

    // CONTROL: at the MATCHING index the gate passes and K does fire, so the
    // test is not merely asserting that this recursor never reduces.
    let mut ok = Expr::const_(nn("E", "rec"), vec![Level::one()]);
    for arg in [
        x(),
        em(),
        Expr::const_(n("ec"), vec![]),
        x(),
        Expr::app(Expr::const_(nn("E", "refl"), vec![]), x()),
    ] {
        ok = Expr::app(ok, arg);
    }
    assert!(
        check_def_eq(
            &env,
            &[],
            &ok,
            &Expr::const_(n("ec"), vec![]),
            Budget::DEFAULT
        )
        .is_accepted(),
        "at the matching index the recursor must still reduce"
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
fn kr301_structural_equality_closes_at_the_one_step_boundary() {
    let env = admit(&Environment::new(), &axiom("A", sort1()));
    let env = admit(&env, &axiom("B", sort1()));
    let a = Expr::const_(n("A"), vec![]);
    let b = Expr::const_(n("B"), vec![]);
    let one_step = Budget::DEFAULT.narrowed(1, Budget::DEFAULT.depth);

    let same = check_def_eq(&env, &[], &a, &a, one_step);
    assert!(
        same.is_accepted(),
        "structural equality must close immediately after the counted entry hook; got {same:?}"
    );

    // CONTROL: the one-step ceiling is genuinely tight. A non-identical pair
    // cannot enter normalization and therefore yields typed exhaustion rather
    // than being blanket-accepted.
    let distinct = check_def_eq(&env, &[], &a, &b, one_step);
    assert!(
        distinct.is_inconclusive(),
        "a distinct pair must not pass the structural fast path; got {distinct:?}"
    );
}

#[test]
fn kr311_application_congruence_checks_heads_and_arguments() {
    let env = admit(&Environment::new(), &axiom("A", sort1()));
    let a_ty = Expr::const_(n("A"), vec![]);
    let env = admit(&env, &axiom("a", a_ty.clone()));
    let env = admit(&env, &axiom("b", a_ty.clone()));
    let arrow = Expr::forall_e(n("_"), a_ty.clone(), a_ty, BinderInfo::Default);
    let env = admit(&env, &axiom("f", arrow.clone()));
    let env = admit(&env, &axiom("g", arrow));
    let a = Expr::const_(n("a"), vec![]);
    let b = Expr::const_(n("b"), vec![]);
    let f = Expr::const_(n("f"), vec![]);
    let g = Expr::const_(n("g"), vec![]);

    let id = Expr::lam(
        n("x"),
        Expr::const_(n("A"), vec![]),
        Expr::bvar(0).expect("packs"),
        BinderInfo::Default,
    );
    let beta_a = Expr::app(id, a.clone());
    assert!(
        check_def_eq(
            &env,
            &[],
            &Expr::app(f.clone(), beta_a),
            &Expr::app(f.clone(), a.clone()),
            Budget::DEFAULT
        )
        .is_accepted(),
        "application congruence must close defeq arguments after reduction"
    );
    assert_eq!(
        reject_class(&check_def_eq(
            &env,
            &[],
            &Expr::app(f.clone(), a.clone()),
            &Expr::app(g, a.clone()),
            Budget::DEFAULT
        )),
        Some(RejectClass::NotDefEq),
        "application congruence must compare the function head"
    );
    assert_eq!(
        reject_class(&check_def_eq(
            &env,
            &[],
            &Expr::app(f.clone(), a),
            &Expr::app(f, b),
            Budget::DEFAULT
        )),
        Some(RejectClass::NotDefEq),
        "application congruence must compare every argument"
    );
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
    let usage = exhausted_usage(&verdict);
    assert_eq!(usage.allowed, Budget::DEFAULT.steps);
    assert!(usage.observed > usage.allowed);
    assert_eq!(
        usage.reason,
        ResourceReason::ExecutionSteps,
        "an infeasible shift is an outcome about the run"
    );
    // A count beyond u64 entirely (2^64, limbs [0,1]) takes the same typed path.
    let beyond_u64 = nat_op_app(
        "shiftLeft",
        lit(1),
        Expr::lit(Literal::Nat(NatLit::from_limbs_le(vec![0, 1]))),
    );
    let verdict = check_def_eq(&env, &[], &beyond_u64, &lit(0), Budget::DEFAULT);
    let usage = exhausted_usage(&verdict);
    assert_eq!(
        (usage.allowed, usage.observed),
        (Budget::DEFAULT.steps, Budget::DEFAULT.steps + 1),
        "a beyond-u64 shift count records the minimal forecasted overrun"
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

fn reject_message(verdict: &Outcome<Verdict>) -> String {
    match verdict {
        Outcome::Complete(Verdict::Rejected { message, .. }) => message.clone(),
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
    let declaration = block_decl(types, ctors, recursors);
    let env = Environment::new();
    let verdict = check(&env, &declaration, Budget::DEFAULT);
    assert!(
        verdict.is_accepted(),
        "MyNat block must admit; got {verdict:?}"
    );

    // The capability handoff must carry every row the block checker compared,
    // in the same type/constructor/recursor order, and expose no prefix.
    let admitted = match capability_admit(&env, declaration, Budget::DEFAULT) {
        Outcome::Complete(admitted) => admitted,
        Outcome::Inconclusive(_) => {
            panic!("an accepted MyNat block became inconclusive at the capability boundary")
        }
        Outcome::InternalFault(_) => {
            panic!("an accepted MyNat block faulted at the capability boundary")
        }
    };
    let checked = match convene(&Council::nobody_was_asked(), admitted) {
        CouncilOutcome::Agreed(checked) => checked,
        CouncilOutcome::KernelRejected { class, .. } => {
            panic!("the capability path rejected the accepted MyNat block as {class:?}")
        }
        CouncilOutcome::Halted(halt) => {
            panic!(
                "an empty council halted the MyNat block: {}",
                halt.summary()
            )
        }
    };
    match checked.publish(
        DeclarationBudget::UNBOUNDED,
        CollisionBudget::default(),
        None,
    ) {
        Outcome::Complete(Published::BlockCommitted(publication)) => {
            assert_eq!(
                publication.names,
                vec![
                    n("MyNat"),
                    nn("MyNat", "zero"),
                    nn("MyNat", "succ"),
                    nn("MyNat", "rec")
                ]
            );
            assert!(matches!(
                publication.environment.find(&n("MyNat")),
                Some(ConstantInfo::Induct(_))
            ));
            assert!(matches!(
                publication.environment.find(&nn("MyNat", "zero")),
                Some(ConstantInfo::Ctor(_))
            ));
            assert!(matches!(
                publication.environment.find(&nn("MyNat", "succ")),
                Some(ConstantInfo::Ctor(_))
            ));
            assert!(matches!(
                publication.environment.find(&nn("MyNat", "rec")),
                Some(ConstantInfo::Rec(_))
            ));
        }
        other => panic!("the checked MyNat block did not publish atomically: {other:?}"),
    }
    assert_eq!(
        env.len(),
        0,
        "publishing the block must not mutate its checked base"
    );
}

#[test]
fn kr600_block_preconditions_reject_empty_and_colliding_names() {
    let empty = block_decl(vec![], vec![], vec![]);
    let verdict = check(&Environment::new(), &empty, Budget::DEFAULT);
    assert_eq!(reject_class(&verdict), Some(RejectClass::BlockMismatch));
    assert!(
        reject_message(&verdict).contains("empty inductive block"),
        "the empty-block precondition must be explicit; got {}",
        reject_message(&verdict)
    );

    let (types, ctors, recursors) = mynat_block();
    let env = add_info(
        &Environment::new(),
        ConstantInfo::Axiom(AxiomVal {
            base: cval(n("MyNat"), vec![], sort1()),
            is_unsafe: false,
        }),
    );
    let verdict = check(
        &env,
        &block_decl(types.clone(), ctors.clone(), recursors.clone()),
        Budget::DEFAULT,
    );
    assert_eq!(
        reject_class(&verdict),
        Some(RejectClass::AlreadyDeclared),
        "an inductive type name must be fresh"
    );

    let env = add_info(
        &Environment::new(),
        ConstantInfo::Axiom(AxiomVal {
            base: cval(nn("MyNat", "rec"), vec![], sort1()),
            is_unsafe: false,
        }),
    );
    let verdict = check(
        &env,
        &block_decl(types.clone(), ctors.clone(), recursors.clone()),
        Budget::DEFAULT,
    );
    assert_eq!(
        reject_class(&verdict),
        Some(RejectClass::AlreadyDeclared),
        "an inductive recursor name must be fresh"
    );

    assert!(
        check(
            &Environment::new(),
            &block_decl(types, ctors, recursors),
            Budget::DEFAULT
        )
        .is_accepted(),
        "the exact block must remain a positive control"
    );
}

#[test]
fn kr601_mutual_block_parameters_must_match() {
    let names = vec![n("Left"), n("Right")];
    let row = |name: &str, parameter_type: Expr| InductiveVal {
        base: cval(
            n(name),
            vec![],
            Expr::forall_e(n("p"), parameter_type, sort1(), BinderInfo::Default),
        ),
        num_params: 1,
        num_indices: 0,
        all: names.clone(),
        ctors: vec![],
        num_nested: 0,
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    };
    let mismatched = block_decl(
        vec![row("Left", sort1()), row("Right", prop())],
        vec![],
        vec![],
    );
    let verdict = check(&Environment::new(), &mismatched, Budget::DEFAULT);
    assert_eq!(reject_class(&verdict), Some(RejectClass::BlockMismatch));
    assert!(
        reject_message(&verdict).contains("parameters of all inductive datatypes must match"),
        "the rejection must come from the shared-parameter judgment; got {}",
        reject_message(&verdict)
    );

    let matching = block_decl(
        vec![row("Left", sort1()), row("Right", sort1())],
        vec![],
        vec![],
    );
    let verdict = check(&Environment::new(), &matching, Budget::DEFAULT);
    assert!(
        !reject_message(&verdict).contains("parameters of all inductive datatypes must match"),
        "matching parameter telescopes must pass KR-601 before later decoded-row checks"
    );
}

#[test]
fn kr602_mutual_results_share_one_universe_and_end_in_sorts() {
    let names = vec![n("Left"), n("Right")];
    let row = |name: &str, type_: Expr| InductiveVal {
        base: cval(n(name), vec![], type_),
        num_params: 0,
        num_indices: 0,
        all: names.clone(),
        ctors: vec![],
        num_nested: 0,
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    };
    let mismatched = block_decl(
        vec![row("Left", sort1()), row("Right", prop())],
        vec![],
        vec![],
    );
    let verdict = check(&Environment::new(), &mismatched, Budget::DEFAULT);
    assert_eq!(reject_class(&verdict), Some(RejectClass::BlockMismatch));
    assert!(
        reject_message(&verdict).contains("must live in the same universe"),
        "the rejection must come from the one-universe judgment; got {}",
        reject_message(&verdict)
    );

    let env = admit(&Environment::new(), &axiom("Carrier", sort1()));
    let non_sort = block_decl(
        vec![row("Left", Expr::const_(n("Carrier"), vec![]))],
        vec![],
        vec![],
    );
    let verdict = check(&env, &non_sort, Budget::DEFAULT);
    assert_eq!(
        reject_class(&verdict),
        Some(RejectClass::SortExpected),
        "an inductive type must end in a sort"
    );
}

#[test]
fn kr603_constructor_metadata_and_return_type_are_cross_checked() {
    let (types, ctors, recursors) = mynat_block();

    let mut wrong_index = ctors.clone();
    wrong_index[0].cidx = 1;
    let verdict = check(
        &Environment::new(),
        &block_decl(types.clone(), wrong_index, recursors.clone()),
        Budget::DEFAULT,
    );
    assert_eq!(reject_class(&verdict), Some(RejectClass::BlockMismatch));
    assert!(
        reject_message(&verdict).contains("constructor observables mismatch"),
        "constructor indices are decoded evidence, never authority; got {}",
        reject_message(&verdict)
    );

    let mut wrong_order = ctors.clone();
    wrong_order.swap(0, 1);
    let verdict = check(
        &Environment::new(),
        &block_decl(types.clone(), wrong_order, recursors.clone()),
        Budget::DEFAULT,
    );
    assert_eq!(reject_class(&verdict), Some(RejectClass::BlockMismatch));
    assert!(
        reject_message(&verdict).contains("decoded ctor order mismatch"),
        "constructor order must match the parent row; got {}",
        reject_message(&verdict)
    );

    let mut wrong_return = ctors.clone();
    wrong_return[0].base.type_ = sort1();
    let verdict = check(
        &Environment::new(),
        &block_decl(types.clone(), wrong_return, recursors.clone()),
        Budget::DEFAULT,
    );
    assert_eq!(reject_class(&verdict), Some(RejectClass::BlockMismatch));
    assert!(
        reject_message(&verdict).contains("invalid return type"),
        "a constructor must return its declared inductive; got {}",
        reject_message(&verdict)
    );

    assert!(
        check(
            &Environment::new(),
            &block_decl(types, ctors, recursors),
            Budget::DEFAULT
        )
        .is_accepted(),
        "the exact constructor rows must remain a positive control"
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
fn kr701_a_single_constructor_prop_carrying_data_is_elimination_restricted() {
    // KR-701's subsingleton rule: a ONE-constructor `Prop` may eliminate large
    // only if every non-parameter field is itself a Prop, or is pinned by the
    // result's arguments. `S : Prop` with a single field `d : D`, `D : Sort 1`,
    // satisfies neither — `D` is data, and `S` has no indices for `d` to occur
    // in — so `S` eliminates ONLY into Prop, and the Prop-restricted recursor
    // below is the one the kernel must regenerate.
    //
    // SOUNDNESS STAKE: large elimination here would let a proof of `S` be
    // destructed into `Sort 1`, carrying the `D` witness out of Prop. That is
    // proof-irrelevance broken at the recursor, not at a projection.
    //
    // WHY THIS TEST EXISTS: a mutation campaign inverted each half of the
    // KR-701 test independently — the field-sort check and the
    // occurs-in-result-args check — and BOTH mutants survived all 93 kernel
    // tests. Every pre-existing KR-700/701 case used nullary constructors, so
    // the field loop this rule lives in was never entered. The two-constructor
    // rule above it was guarded; the single-constructor rule was not.
    let env = admit(&Environment::new(), &axiom("D", sort1()));
    let s = || Expr::const_(n("S"), vec![]);
    let d = || Expr::const_(n("D"), vec![]);
    let bv = |i: u32| Expr::bvar(i).expect("packs");

    let ind = InductiveVal {
        base: cval(n("S"), vec![], prop()),
        num_params: 0,
        num_indices: 0,
        all: vec![n("S")],
        ctors: vec![nn("S", "mk")],
        num_nested: 0,
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    };
    let ctor = ConstructorVal {
        base: cval(
            nn("S", "mk"),
            vec![],
            Expr::forall_e(n("d"), d(), s(), BinderInfo::Default),
        ),
        induct: n("S"),
        cidx: 0,
        num_params: 0,
        num_fields: 1,
        is_unsafe: false,
    };

    // {motive : S -> Prop} -> (mk : (d : D) -> motive (S.mk d)) -> (t : S) -> motive t
    let motive_ty = Expr::forall_e(n("t"), s(), prop(), BinderInfo::Default);
    let minor_ty = Expr::forall_e(
        n("d"),
        d(),
        Expr::app(bv(1), Expr::app(Expr::const_(nn("S", "mk"), vec![]), bv(0))),
        BinderInfo::Default,
    );
    let rec_ty = Expr::forall_e(
        n("motive"),
        motive_ty.clone(),
        Expr::forall_e(
            n("mk"),
            minor_ty.clone(),
            Expr::forall_e(n("t"), s(), Expr::app(bv(2), bv(0)), BinderInfo::Default),
            BinderInfo::Default,
        ),
        BinderInfo::Implicit,
    );
    // fun motive mk d => mk d
    let rhs = Expr::lam(
        n("motive"),
        motive_ty,
        Expr::lam(
            n("mk"),
            minor_ty,
            Expr::lam(n("d"), d(), Expr::app(bv(1), bv(0)), BinderInfo::Default),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let rec = RecursorVal {
        base: cval(nn("S", "rec"), vec![], rec_ty),
        all: vec![n("S")],
        num_params: 0,
        num_indices: 0,
        num_motives: 1,
        num_minors: 1,
        rules: vec![RecursorRule {
            ctor: nn("S", "mk"),
            nfields: 1,
            rhs,
        }],
        k: false,
        is_unsafe: false,
    };
    let verdict = check(
        &env,
        &block_decl(vec![ind], vec![ctor], vec![rec]),
        Budget::DEFAULT,
    );
    assert!(
        verdict.is_accepted(),
        "a 1-ctor Prop with a data field must admit with Prop-RESTRICTED \
         elimination; got {verdict:?}"
    );
}

#[test]
fn kr302_binder_congruence_compares_the_domain_not_only_the_body() {
    // KR-302: two binders are defeq only if their DOMAINS are defeq and their
    // bodies agree under a shared local. Dropping the domain half leaves the
    // body comparison, which still succeeds — so `B -> A` would be accepted
    // where `A -> A` was declared, for arbitrary unrelated `A` and `B`.
    //
    // A mutation campaign found this unguarded: replacing the domain check
    // with `if false` left all 94 kernel tests passing. Every pre-existing
    // binder-congruence case (KR-312 eta, KR-202 beta, the lambda cases) had
    // matching domains, so nothing ever exercised the disagreeing branch.
    //
    // SOUNDNESS STAKE: function types would become defeq up to their argument
    // types, so a proof about `B -> A` could be used where `A -> A` is
    // required, and the kernel would admit the substitution silently.
    let env = admit(&Environment::new(), &axiom("A", sort1()));
    let env = admit(&env, &axiom("B", sort1()));
    let env = admit(&env, &axiom("a", Expr::const_(n("A"), vec![])));
    let a_ty = || Expr::const_(n("A"), vec![]);
    let b_ty = || Expr::const_(n("B"), vec![]);

    // value : A -> A  (fun _ : A => a)
    let value = Expr::lam(
        n("x"),
        a_ty(),
        Expr::const_(n("a"), vec![]),
        BinderInfo::Default,
    );
    // declared : B -> A — same body type, DIFFERENT domain.
    let declared = Expr::forall_e(n("x"), b_ty(), a_ty(), BinderInfo::Default);
    let verdict = check(&env, &defn("f", declared, value), Budget::DEFAULT);
    assert_eq!(
        reject_class(&verdict),
        Some(RejectClass::DefinitionTypeMismatch),
        "a binder whose DOMAIN differs must not be defeq; got {verdict:?}"
    );

    // The matching-domain version still admits, so the rule is not a blanket
    // refusal of binder congruence.
    let ok = Expr::forall_e(n("x"), a_ty(), a_ty(), BinderInfo::Default);
    let value_ok = Expr::lam(
        n("x"),
        a_ty(),
        Expr::const_(n("a"), vec![]),
        BinderInfo::Default,
    );
    assert!(
        check(&env, &defn("g", ok, value_ok), Budget::DEFAULT).is_accepted(),
        "matching domains must still admit"
    );
}

#[test]
fn kr802_decoded_recursor_arity_observables_are_cross_checked() {
    // KR-802: the decoded recursor's observables are REGENERATED, never
    // trusted. `num_motives` and `num_minors` are not decoration — tc.rs uses
    // them to locate the major premise in an application spine
    // (num_params + num_motives + num_minors + num_indices), so a decoded lie
    // makes iota reduce against the WRONG argument while the recursor's own
    // type still checks out.
    //
    // A mutation campaign found both unguarded: deleting either comparison
    // from the observables check left all 94 kernel tests passing. The type
    // comparison beside it does not cover them, because these are separate
    // decoded fields that can disagree with a perfectly well-formed type.
    // kr607 pins the decoded *flags* (is_rec); nothing pinned the arities.
    for (label, corrupt) in [
        (
            "num_minors",
            (|r: &mut RecursorVal| r.num_minors += 1) as fn(&mut RecursorVal),
        ),
        ("num_motives", |r: &mut RecursorVal| r.num_motives += 1),
    ] {
        let (types, ctors, mut recursors) = mynat_block();
        corrupt(&mut recursors[0]);
        let verdict = check(
            &Environment::new(),
            &block_decl(types, ctors, recursors),
            Budget::DEFAULT,
        );
        assert_eq!(
            reject_class(&verdict),
            Some(RejectClass::BlockMismatch),
            "a decoded recursor overstating {label} must be rejected; got {verdict:?}"
        );
    }
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

fn eq_environment_with_refl(refl_type: Expr) -> Environment {
    let u = n("u");
    let level = Level::param(u.clone());
    let bv = |index: u32| Expr::bvar(index).expect("packs");
    let eq_type = Expr::forall_e(
        n("α"),
        Expr::sort(level.clone()),
        Expr::forall_e(
            n("a"),
            bv(0),
            Expr::forall_e(n("b"), bv(1), prop(), BinderInfo::Default),
            BinderInfo::Default,
        ),
        BinderInfo::Implicit,
    );
    let eq = ConstantInfo::Induct(InductiveVal {
        base: cval(n("Eq"), vec![u.clone()], eq_type),
        num_params: 1,
        num_indices: 2,
        all: vec![n("Eq")],
        ctors: vec![nn("Eq", "refl")],
        num_nested: 0,
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    });
    let refl = ConstantInfo::Ctor(ConstructorVal {
        base: cval(nn("Eq", "refl"), vec![u], refl_type),
        induct: n("Eq"),
        cidx: 0,
        num_params: 1,
        num_fields: 1,
        is_unsafe: false,
    });
    add_info(&add_info(&Environment::new(), eq), refl)
}

fn exact_eq_environment() -> Environment {
    let level = Level::param(n("u"));
    let bv = |index: u32| Expr::bvar(index).expect("packs");
    let refl_type = Expr::forall_e(
        n("α"),
        Expr::sort(level.clone()),
        Expr::forall_e(
            n("a"),
            bv(0),
            Expr::app(
                Expr::app(Expr::app(Expr::const_(n("Eq"), vec![level]), bv(1)), bv(0)),
                bv(0),
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Implicit,
    );
    eq_environment_with_refl(refl_type)
}

fn exact_quotient_rows() -> Vec<QuotVal> {
    let arrow = |domain: Expr, codomain: Expr| {
        Expr::forall_e(n("a"), domain, codomain, BinderInfo::Default)
    };
    let pi = |name: &str, info: BinderInfo, type_: Expr, body: Expr| {
        Expr::forall_e(n(name), type_, body, info)
    };
    let quot = n("Quot");
    let u_name = n("u");
    let v_name = n("v");
    let u = Level::param(u_name.clone());
    let v = Level::param(v_name.clone());
    let bv = |index: u32| Expr::bvar(index).expect("packs");

    let quot_type = pi(
        "α",
        BinderInfo::Implicit,
        Expr::sort(u.clone()),
        arrow(arrow(bv(0), arrow(bv(1), prop())), Expr::sort(u.clone())),
    );
    let quot_app = |alpha: Expr, relation: Expr| {
        Expr::app(
            Expr::app(Expr::const_(quot.clone(), vec![u.clone()]), alpha),
            relation,
        )
    };
    let quot_mk_type = pi(
        "α",
        BinderInfo::Implicit,
        Expr::sort(u.clone()),
        pi(
            "r",
            BinderInfo::Default,
            arrow(bv(0), arrow(bv(1), prop())),
            pi("a", BinderInfo::Default, bv(1), quot_app(bv(2), bv(1))),
        ),
    );

    let eq_name = n("Eq");
    let soundness = pi(
        "a",
        BinderInfo::Default,
        bv(3),
        pi(
            "b",
            BinderInfo::Default,
            bv(4),
            arrow(
                Expr::app(Expr::app(bv(4), bv(1)), bv(0)),
                Expr::app(
                    Expr::app(
                        Expr::app(Expr::const_(eq_name, vec![v.clone()]), bv(4)),
                        Expr::app(bv(3), bv(2)),
                    ),
                    Expr::app(bv(3), bv(1)),
                ),
            ),
        ),
    );
    let quot_lift_type = pi(
        "α",
        BinderInfo::Implicit,
        Expr::sort(u.clone()),
        pi(
            "r",
            BinderInfo::Implicit,
            arrow(bv(0), arrow(bv(1), prop())),
            pi(
                "β",
                BinderInfo::Implicit,
                Expr::sort(v.clone()),
                pi(
                    "f",
                    BinderInfo::Default,
                    arrow(bv(2), bv(1)),
                    arrow(
                        soundness,
                        arrow(
                            Expr::app(
                                Expr::app(Expr::const_(quot.clone(), vec![u.clone()]), bv(4)),
                                bv(3),
                            ),
                            bv(3),
                        ),
                    ),
                ),
            ),
        ),
    );

    let quot_mk = nn("Quot", "mk");
    let quot_ind_type = pi(
        "α",
        BinderInfo::Implicit,
        Expr::sort(u.clone()),
        pi(
            "r",
            BinderInfo::Implicit,
            arrow(bv(0), arrow(bv(1), prop())),
            pi(
                "β",
                BinderInfo::Implicit,
                arrow(
                    Expr::app(
                        Expr::app(Expr::const_(quot.clone(), vec![u.clone()]), bv(1)),
                        bv(0),
                    ),
                    prop(),
                ),
                pi(
                    "mk",
                    BinderInfo::Default,
                    pi(
                        "a",
                        BinderInfo::Default,
                        bv(2),
                        Expr::app(
                            bv(1),
                            Expr::app(
                                Expr::app(
                                    Expr::app(
                                        Expr::const_(quot_mk.clone(), vec![u.clone()]),
                                        bv(3),
                                    ),
                                    bv(2),
                                ),
                                bv(0),
                            ),
                        ),
                    ),
                    pi(
                        "q",
                        BinderInfo::Default,
                        Expr::app(
                            Expr::app(Expr::const_(quot.clone(), vec![u.clone()]), bv(3)),
                            bv(2),
                        ),
                        Expr::app(bv(2), bv(0)),
                    ),
                ),
            ),
        ),
    );

    vec![
        QuotVal {
            base: cval(quot, vec![u_name.clone()], quot_type),
            kind: QuotKind::Type,
        },
        QuotVal {
            base: cval(quot_mk, vec![u_name.clone()], quot_mk_type),
            kind: QuotKind::Ctor,
        },
        QuotVal {
            base: cval(
                nn("Quot", "lift"),
                vec![u_name.clone(), v_name],
                quot_lift_type,
            ),
            kind: QuotKind::Lift,
        },
        QuotVal {
            base: cval(nn("Quot", "ind"), vec![u_name], quot_ind_type),
            kind: QuotKind::Ind,
        },
    ]
}

#[test]
fn kr951_kr952_kr953_kr954_quotient_rows_are_checked_individually() {
    let env = exact_eq_environment();
    let rows = exact_quotient_rows();
    let verdict = check(&env, &Declaration::Quotient(rows.clone()), Budget::DEFAULT);
    assert!(
        verdict.is_accepted(),
        "the exact Quot, Quot.mk, Quot.lift, and Quot.ind rows must initialize; got {verdict:?}"
    );

    for (index, rule) in ["KR-951", "KR-952", "KR-953", "KR-954"]
        .into_iter()
        .enumerate()
    {
        let mut corrupted = rows.clone();
        corrupted[index].base.type_ = sort1();
        let verdict = check(&env, &Declaration::Quotient(corrupted), Budget::DEFAULT);
        assert_eq!(
            reject_class(&verdict),
            Some(RejectClass::BlockMismatch),
            "{rule}: a decoded quotient type must not override the pin-derived row"
        );
        assert!(
            reject_message(&verdict).contains("type diverges"),
            "{rule}: the first divergence must identify the corrupt row; got {}",
            reject_message(&verdict)
        );
    }
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
fn kr950_quotient_init_checks_the_eq_constructor_not_only_the_eq_type() {
    // KR-950 validates BOTH halves of the pinned equality: the `Eq` type AND
    // its `Eq.refl` constructor. A mutation campaign found the constructor
    // half unguarded — replacing its structural comparison with `if false`
    // left all 96 tests passing, because the only existing KR-95x case removes
    // `Eq` from the environment entirely and returns long before the
    // constructor is ever looked at.
    //
    // SOUNDNESS STAKE: `Quot.sound` is stated in terms of this `Eq`. An
    // `Eq.refl` of the wrong type is a different equality wearing the right
    // name, and quotient soundness is what rests on it.
    let u = n("u");
    let lvl = Level::param(u.clone());
    let bv = |i: u32| Expr::bvar(i).expect("packs");

    // A "refl" that is NOT reflexive: forall {a} (x y : a), Eq a x y — it
    // relates two DIFFERENT values, so it proves everything equal.
    let bad_refl = Expr::forall_e(
        n("α"),
        Expr::sort(lvl.clone()),
        Expr::forall_e(
            n("x"),
            bv(0),
            Expr::forall_e(
                n("y"),
                bv(1),
                Expr::app(
                    Expr::app(
                        Expr::app(Expr::const_(n("Eq"), vec![lvl.clone()]), bv(2)),
                        bv(1),
                    ),
                    bv(0),
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Implicit,
    );
    let verdict = check(
        &eq_environment_with_refl(bad_refl),
        &Declaration::Quotient(vec![]),
        Budget::DEFAULT,
    );
    assert_eq!(reject_class(&verdict), Some(RejectClass::BlockMismatch));
    assert!(
        reject_message(&verdict).contains("type for 'Eq' type constructor"),
        "a non-reflexive `Eq.refl` must be refused by name; got: {}",
        reject_message(&verdict)
    );

    // CONTROL: with the correct refl the run gets PAST this check — it then
    // fails on the absent quotient declarations instead. Without this the test
    // could pass for any reason at all.
    let control = check(
        &exact_eq_environment(),
        &Declaration::Quotient(vec![]),
        Budget::DEFAULT,
    );
    assert!(
        !reject_message(&control).contains("type for 'Eq' type constructor"),
        "the correct refl must clear the constructor check; got: {}",
        reject_message(&control)
    );
}

#[test]
fn kr974_opaque_declarations_check_the_body_and_stay_opaque_to_defeq() {
    // Pin environment.cpp:add_opaque checks an opaque's header and body with
    // the ordinary safe type checker, then stores it as ConstantInfo::Opaque.
    // The body is evidence for admission, not a delta-reduction rule.
    let env = admit(&Environment::new(), &axiom("A", sort1()));
    let a_type = || Expr::const_(n("A"), vec![]);
    let env = admit(&env, &axiom("a", a_type()));
    let opaque = OpaqueVal {
        base: cval(n("sealed"), vec![], a_type()),
        value: Expr::const_(n("a"), vec![]),
        is_unsafe: false,
        all: vec![n("sealed")],
    };
    let verdict = check(&env, &Declaration::Opaque(opaque.clone()), Budget::DEFAULT);
    assert!(
        verdict.is_accepted(),
        "a well-typed opaque must admit; got {verdict:?}"
    );

    let with_opaque = add_info(&env, ConstantInfo::Opaque(opaque));
    assert_eq!(
        reject_class(&check_def_eq(
            &with_opaque,
            &[],
            &Expr::const_(n("sealed"), vec![]),
            &Expr::const_(n("a"), vec![]),
            Budget::DEFAULT
        )),
        Some(RejectClass::NotDefEq),
        "an admitted opaque body must not become a delta-reduction rule"
    );

    let bad = OpaqueVal {
        base: cval(n("badOpaque"), vec![], a_type()),
        value: Expr::const_(n("A"), vec![]),
        is_unsafe: false,
        all: vec![n("badOpaque")],
    };
    assert_eq!(
        reject_class(&check(&env, &Declaration::Opaque(bad), Budget::DEFAULT)),
        Some(RejectClass::DefinitionTypeMismatch),
        "an opaque body still has to inhabit its declared type"
    );

    // This is subtle pin behavior: OpaqueVal.isUnsafe is metadata, but
    // add_opaque constructs the ordinary SAFE checker. Marking the declaration
    // unsafe therefore does not let its body reference an unsafe definition.
    let function_type = Expr::forall_e(n("x"), a_type(), a_type(), BinderInfo::Default);
    let unsafe_info = DefinitionVal {
        base: cval(n("unsafeId"), vec![], function_type.clone()),
        value: Expr::lam(
            n("x"),
            a_type(),
            Expr::bvar(0).expect("packs"),
            BinderInfo::Default,
        ),
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Unsafe,
        all: vec![n("unsafeId")],
    };
    let unsafe_env = add_info(&env, ConstantInfo::Defn(unsafe_info));
    let unsafe_opaque = OpaqueVal {
        base: cval(n("unsafeOpaque"), vec![], function_type),
        value: Expr::const_(n("unsafeId"), vec![]),
        is_unsafe: true,
        all: vec![n("unsafeOpaque")],
    };
    assert_eq!(
        reject_class(&check(
            &unsafe_env,
            &Declaration::Opaque(unsafe_opaque),
            Budget::DEFAULT
        )),
        Some(RejectClass::SafetyViolation),
        "OpaqueVal.isUnsafe must not silently widen the pin's safe body checker"
    );
}

#[test]
fn kr977_mutual_definitions_predeclare_the_whole_block_and_fail_atomically() {
    let env = admit(&Environment::new(), &axiom("A", sort1()));
    let a_type = || Expr::const_(n("A"), vec![]);
    let function_type = || Expr::forall_e(n("x"), a_type(), a_type(), BinderInfo::Default);
    let all = vec![n("mutualF"), n("mutualG")];
    let member = |name: &str, target: &str| DefinitionVal {
        base: cval(n(name), vec![], function_type()),
        value: Expr::lam(
            n("x"),
            a_type(),
            Expr::app(
                Expr::const_(n(target), vec![]),
                Expr::bvar(0).expect("packs"),
            ),
            BinderInfo::Default,
        ),
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Partial,
        all: all.clone(),
    };
    let f = member("mutualF", "mutualG");
    let g = member("mutualG", "mutualF");

    // A single partial definition sees itself, but not its not-yet-added peer.
    // The same first member therefore fails outside the block. This is the
    // discriminating control for "predeclare EVERY member before ANY body".
    assert_eq!(
        reject_class(&check(&env, &Declaration::Defn(f.clone()), Budget::DEFAULT)),
        Some(RejectClass::UnknownConstant)
    );

    let block = Declaration::Mutual(vec![f.clone(), g.clone()]);
    let verdict = check(&env, &block, Budget::DEFAULT);
    let used = match verdict {
        Outcome::Complete(Verdict::Accepted { consumption }) => consumption.steps_used,
        other => panic!("a well-typed partial mutual block must admit: {other:?}"),
    };
    assert!(used > 1, "the block must perform real shared work");

    // The allowance is shared across headers and bodies. Exact work passes;
    // moving the boundary by one produces typed Inconclusive, never rejection.
    assert!(
        check(
            &env,
            &block,
            Budget::DEFAULT.narrowed(used, Budget::DEFAULT.depth)
        )
        .is_accepted(),
        "the exact measured step boundary must admit"
    );
    assert!(
        check(
            &env,
            &block,
            Budget::DEFAULT.narrowed(used - 1, Budget::DEFAULT.depth)
        )
        .is_inconclusive(),
        "one step below the shared boundary must be typed Inconclusive"
    );

    let mut bad_g = g;
    bad_g.value = Expr::sort(Level::zero());
    assert_eq!(
        reject_class(&check(
            &env,
            &Declaration::Mutual(vec![f, bad_g]),
            Budget::DEFAULT
        )),
        Some(RejectClass::DefinitionTypeMismatch)
    );
    assert!(
        !env.contains(&n("mutualF")) && !env.contains(&n("mutualG")),
        "checking a block must not publish an accepted prefix"
    );
}

#[test]
fn kr977_mutual_definition_shape_is_nonempty_uniform_and_nonsafe() {
    let env = admit(&Environment::new(), &axiom("A", sort1()));
    let a_type = || Expr::const_(n("A"), vec![]);
    let function_type = || Expr::forall_e(n("x"), a_type(), a_type(), BinderInfo::Default);
    let member = |name: &str, safety: DefinitionSafety| DefinitionVal {
        base: cval(n(name), vec![], function_type()),
        value: Expr::lam(
            n("x"),
            a_type(),
            Expr::bvar(0).expect("packs"),
            BinderInfo::Default,
        ),
        hints: ReducibilityHints::Regular(1),
        safety,
        all: vec![n("shapeF"), n("shapeG")],
    };

    assert_eq!(
        reject_class(&check(&env, &Declaration::Mutual(vec![]), Budget::DEFAULT)),
        Some(RejectClass::BlockMismatch),
        "the pin refuses an empty mutual definition"
    );
    assert_eq!(
        reject_class(&check(
            &env,
            &Declaration::Mutual(vec![member("safeMutual", DefinitionSafety::Safe)]),
            Budget::DEFAULT
        )),
        Some(RejectClass::BlockMismatch),
        "safe mutual definitions are not a kernel declaration form"
    );
    assert_eq!(
        reject_class(&check(
            &env,
            &Declaration::Mutual(vec![
                member("shapeF", DefinitionSafety::Partial),
                member("shapeG", DefinitionSafety::Unsafe),
            ]),
            Budget::DEFAULT
        )),
        Some(RejectClass::BlockMismatch),
        "every mutual member must carry the same safety annotation"
    );

    let duplicate = member("duplicateMutual", DefinitionSafety::Partial);
    assert_eq!(
        reject_class(&check(
            &env,
            &Declaration::Mutual(vec![duplicate.clone(), duplicate]),
            Budget::DEFAULT
        )),
        Some(RejectClass::AlreadyDeclared),
        "the private scratch environment must preserve one-name-one-constant"
    );
}

#[test]
fn kr973_kr975_kr976_nonsafe_definitions_check_and_safe_references_are_gated() {
    // Pin add_definition/add_mutual semantics: a PARTIAL definition may
    // reference itself (header → add → body in the scratch env); a SAFE
    // definition may reference neither partial nor unsafe declarations
    // (KR-976/KR-975), while an UNSAFE definition may reference unsafe ones.
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
    // (KR-976), an UNSAFE definition referencing an unsafe one admits.
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
        "a safe definition must not reference a partial one (KR-976)"
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
        "a safe definition must not reference an unsafe one (KR-975)"
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
    let (mylist, ctors) = mylist_rows();
    let mut env = Environment::new()
        .add_decl(ConstantInfo::Induct(mylist))
        .expect("env");
    for ctor in ctors {
        env = env.add_decl(ConstantInfo::Ctor(ctor)).expect("env");
    }
    env
}

/// `MyList`'s rows on their own, so an environment can declare the families in
/// either order (the declaration-order permutation).
fn mylist_rows() -> (InductiveVal, Vec<ConstructorVal>) {
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
    (mylist, vec![nil, cons])
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
        Budget::DEFAULT.narrowed(5, 4096),
    );
    assert!(
        verdict.is_inconclusive(),
        "budget exhaustion in the translation must be typed Inconclusive; got {verdict:?}"
    );
    assert!(!verdict.is_accepted() && !verdict.is_rejected());
}

// ---------------------------------------------------------------------------
// KR-608, second channel: TRANSITIVE (worklist) discovery, deduplication, and
// auxiliary accounting — the pin's cascade (bead franken_lean-8ce PIN-PROBE
// CORRECTION). At the pin, `Lean.Syntax.node` nests `Array Syntax` directly;
// copying `Array` at `Syntax` exposes `Array.mk : List Syntax → Array Syntax`,
// whose field is itself nested, so `List` is copied too and `num_nested = 2`.
// The second occurrence exists in NO declared row — only in a minted one — so
// it is reachable only by iterating the worklist over the auxiliaries.
//
// `MyArr` below plays `Array`, `MyList` plays `List`, `MyTree` plays `Syntax`.
// ---------------------------------------------------------------------------

/// [`mylist_env`] extended with `MyArr α`, whose ONLY constructor carries a
/// `MyList α` field. Nothing here is nested by itself: the cascade appears
/// only once `MyArr` is copied at `MyTree`.
fn myarr_env() -> Environment {
    cascade_env(false)
}

/// Both families, with `arr_first` choosing which is DECLARED first. The
/// translation resolves nested heads by name out of the environment, so this
/// order must not be observable anywhere in the result.
fn cascade_env(arr_first: bool) -> Environment {
    let (mylist, list_ctors) = mylist_rows();
    let (myarr, arr_ctor) = myarr_rows();
    let list: Vec<ConstantInfo> = std::iter::once(ConstantInfo::Induct(mylist))
        .chain(list_ctors.into_iter().map(ConstantInfo::Ctor))
        .collect();
    let arr = vec![ConstantInfo::Induct(myarr), ConstantInfo::Ctor(arr_ctor)];
    let (first, second) = if arr_first { (arr, list) } else { (list, arr) };
    let mut env = Environment::new();
    for info in first.into_iter().chain(second) {
        env = env.add_decl(info).expect("env");
    }
    env
}

/// `MyArr`'s rows: the family whose copy exposes the cascade.
fn myarr_rows() -> (InductiveVal, ConstructorVal) {
    let bv = |i: u32| Expr::bvar(i).expect("packs");
    let myarr = InductiveVal {
        base: cval(
            n("MyArr"),
            vec![],
            Expr::forall_e(n("α"), sort1(), sort1(), BinderInfo::Default),
        ),
        num_params: 1,
        num_indices: 0,
        all: vec![n("MyArr")],
        ctors: vec![nn("MyArr", "mk")],
        num_nested: 0,
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    };
    let mk = ConstructorVal {
        base: cval(
            nn("MyArr", "mk"),
            vec![],
            Expr::forall_e(
                n("α"),
                sort1(),
                Expr::forall_e(
                    n("data"),
                    Expr::app(Expr::const_(n("MyList"), vec![]), bv(0)),
                    Expr::app(Expr::const_(n("MyArr"), vec![]), bv(1)),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
        ),
        induct: n("MyArr"),
        cidx: 0,
        num_params: 1,
        num_fields: 1,
        is_unsafe: false,
    };
    (myarr, mk)
}

/// Decoded rows for the cascading block: `MyTree.node : MyArr MyTree → MyTree`
/// (`with_direct_list` adds a second field `MyList MyTree`, which the `MyArr`
/// copy ALSO reaches — the duplicate-reachability case). `num_nested` is a
/// parameter because it is the observable each cascade case pins.
fn cascaded_mytree_rows(
    num_nested: u32,
    with_direct_list: bool,
) -> (Vec<InductiveVal>, Vec<ConstructorVal>) {
    let tree = || Expr::const_(n("MyTree"), vec![]);
    let arr_tree = Expr::app(Expr::const_(n("MyArr"), vec![]), tree());
    let list_tree = Expr::app(Expr::const_(n("MyList"), vec![]), tree());
    let node_ty = if with_direct_list {
        Expr::forall_e(
            n("a"),
            arr_tree,
            Expr::forall_e(n("l"), list_tree, tree(), BinderInfo::Default),
            BinderInfo::Default,
        )
    } else {
        Expr::forall_e(n("a"), arr_tree, tree(), BinderInfo::Default)
    };
    let ind = InductiveVal {
        base: cval(n("MyTree"), vec![], sort1()),
        num_params: 0,
        num_indices: 0,
        all: vec![n("MyTree")],
        ctors: vec![nn("MyTree", "node")],
        num_nested,
        is_rec: true,
        is_unsafe: false,
        is_reflexive: false,
    };
    let node = ConstructorVal {
        base: cval(nn("MyTree", "node"), vec![], node_ty),
        induct: n("MyTree"),
        cidx: 0,
        num_params: 0,
        num_fields: if with_direct_list { 2 } else { 1 },
        is_unsafe: false,
    };
    (vec![ind], vec![node])
}

/// The cascading block in full restored form: the decoded rows the pin would
/// serialize for `MyTree.node : MyArr MyTree → MyTree`, including all THREE
/// recursors. Auxiliary creation order is observable here and nowhere else:
/// `MyTree.rec_1` eliminates the first auxiliary (`MyArr MyTree`, minted from
/// the declared field) and `MyTree.rec_2` the second (`MyList MyTree`, minted
/// from inside the first auxiliary's constructor).
fn cascaded_mytree_block() -> (Vec<InductiveVal>, Vec<ConstructorVal>, Vec<RecursorVal>) {
    let (types, ctors) = cascaded_mytree_rows(2, false);
    let tree = || Expr::const_(n("MyTree"), vec![]);
    let arr = || Expr::app(Expr::const_(n("MyArr"), vec![]), tree());
    let list = || Expr::app(Expr::const_(n("MyList"), vec![]), tree());
    let bv = |i: u32| Expr::bvar(i).expect("packs");
    let u = Level::param(n("u"));
    let motive_ty =
        |major: Expr| Expr::forall_e(n("t"), major, Expr::sort(u.clone()), BinderInfo::Default);
    let motive_1_ty = motive_ty(tree());
    let motive_2_ty = motive_ty(arr());
    let motive_3_ty = motive_ty(list());
    // node : Π (a : MyArr MyTree), motive_2 a → motive_1 (MyTree.node a)
    let node_minor_ty = Expr::forall_e(
        n("a"),
        arr(),
        Expr::forall_e(
            n("a_ih"),
            Expr::app(bv(2), bv(0)),
            Expr::app(
                bv(4),
                Expr::app(Expr::const_(nn("MyTree", "node"), vec![]), bv(1)),
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    // mk : Π (data : MyList MyTree), motive_3 data → motive_2 (MyArr.mk MyTree data)
    let mk_minor_ty = Expr::forall_e(
        n("data"),
        list(),
        Expr::forall_e(
            n("data_ih"),
            Expr::app(bv(2), bv(0)),
            Expr::app(
                bv(4),
                Expr::app(
                    Expr::app(Expr::const_(nn("MyArr", "mk"), vec![]), tree()),
                    bv(1),
                ),
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    // nil : motive_3 (MyList.nil MyTree)
    let nil_minor_ty = Expr::app(
        bv(2),
        Expr::app(Expr::const_(nn("MyList", "nil"), vec![]), tree()),
    );
    // cons : Π (head : MyTree) (tail : MyList MyTree), motive_1 head →
    //   motive_3 tail → motive_3 (MyList.cons MyTree head tail)
    let cons_minor_ty = Expr::forall_e(
        n("head"),
        tree(),
        Expr::forall_e(
            n("tail"),
            list(),
            Expr::forall_e(
                n("head_ih"),
                Expr::app(bv(7), bv(1)),
                Expr::forall_e(
                    n("tail_ih"),
                    Expr::app(bv(6), bv(1)),
                    Expr::app(
                        bv(7),
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
    let minors = [
        (n("node"), node_minor_ty.clone()),
        (n("mk"), mk_minor_ty.clone()),
        (n("nil"), nil_minor_ty.clone()),
        (n("cons"), cons_minor_ty.clone()),
    ];
    let telescope = |major_ty: Expr, result_motive_at: u32| {
        let mut body = Expr::forall_e(
            n("t"),
            major_ty,
            Expr::app(bv(result_motive_at), bv(0)),
            BinderInfo::Default,
        );
        for (name, ty) in minors.iter().rev() {
            body = Expr::forall_e(name.clone(), ty.clone(), body, BinderInfo::Default);
        }
        for (name, ty) in [
            (n("motive_3"), motive_3_ty.clone()),
            (n("motive_2"), motive_2_ty.clone()),
            (n("motive_1"), motive_1_ty.clone()),
        ] {
            body = Expr::forall_e(name, ty, body, BinderInfo::Implicit);
        }
        body
    };
    // λ motive_1 motive_2 motive_3 node mk nil cons, λ fields…, body
    let lam7 = |body: Expr, field_lams: &[(Name, Expr)]| {
        let mut inner = body;
        for (name, ty) in field_lams.iter().rev() {
            inner = Expr::lam(name.clone(), ty.clone(), inner, BinderInfo::Default);
        }
        for (name, ty) in minors.iter().rev() {
            inner = Expr::lam(name.clone(), ty.clone(), inner, BinderInfo::Default);
        }
        for (name, ty) in [
            (n("motive_3"), motive_3_ty.clone()),
            (n("motive_2"), motive_2_ty.clone()),
            (n("motive_1"), motive_1_ty.clone()),
        ] {
            inner = Expr::lam(name, ty, inner, BinderInfo::Default);
        }
        inner
    };
    let rec_call = |rec: &str, args: &[u32]| {
        let mut app = Expr::const_(nn("MyTree", rec), vec![u.clone()]);
        for a in args {
            app = Expr::app(app, bv(*a));
        }
        app
    };
    // node rule: … (a) => node a (MyTree.rec_1 … a)
    let node_rhs = lam7(
        Expr::app(
            Expr::app(bv(4), bv(0)),
            rec_call("rec_1", &[7, 6, 5, 4, 3, 2, 1, 0]),
        ),
        &[(n("a"), arr())],
    );
    // mk rule: … (data) => mk data (MyTree.rec_2 … data)
    let mk_rhs = lam7(
        Expr::app(
            Expr::app(bv(3), bv(0)),
            rec_call("rec_2", &[7, 6, 5, 4, 3, 2, 1, 0]),
        ),
        &[(n("data"), list())],
    );
    // nil rule: … => nil
    let nil_rhs = lam7(bv(1), &[]);
    // cons rule: … (head) (tail) => cons head tail (MyTree.rec … head)
    //   (MyTree.rec_2 … tail)
    let cons_rhs = lam7(
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(bv(2), bv(1)), bv(0)),
                rec_call("rec", &[8, 7, 6, 5, 4, 3, 2, 1]),
            ),
            rec_call("rec_2", &[8, 7, 6, 5, 4, 3, 2, 0]),
        ),
        &[(n("head"), tree()), (n("tail"), list())],
    );
    let mk_rec = |name: Name, ty: Expr, rules: Vec<RecursorRule>| RecursorVal {
        base: cval(name, vec![n("u")], ty),
        all: vec![n("MyTree")],
        num_params: 0,
        num_indices: 0,
        num_motives: 3,
        num_minors: 4,
        rules,
        k: false,
        is_unsafe: false,
    };
    let recursors = vec![
        mk_rec(
            nn("MyTree", "rec"),
            telescope(tree(), 7),
            vec![RecursorRule {
                ctor: nn("MyTree", "node"),
                nfields: 1,
                rhs: node_rhs,
            }],
        ),
        mk_rec(
            nn("MyTree", "rec_1"),
            telescope(arr(), 6),
            vec![RecursorRule {
                ctor: nn("MyArr", "mk"),
                nfields: 1,
                rhs: mk_rhs,
            }],
        ),
        mk_rec(
            nn("MyTree", "rec_2"),
            telescope(list(), 5),
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
        ),
    ];
    (types, ctors, recursors)
}

#[test]
fn kr608_cascaded_block_admits_with_byte_exact_translated_regeneration() {
    // The cascade end to end: two auxiliaries (one of them discovered only
    // inside the other), the full ordinary ruleset on the synthesized
    // three-type block, three regenerated recursors, restored names and
    // occurrences — byte-equal to these hand-built restored rows.
    let (types, ctors, recursors) = cascaded_mytree_block();
    let verdict = check(
        &myarr_env(),
        &block_decl(types, ctors, recursors),
        Budget::DEFAULT,
    );
    assert!(
        verdict.is_accepted(),
        "the cascaded MyTree block must admit under the FULL ruleset; got {verdict:?}"
    );
}

#[test]
fn kr608_auxiliary_recursor_numbering_follows_creation_order() {
    // MUTANT ("reordered auxiliaries"): swap the two auxiliary recursors'
    // majors. `rec_1` must eliminate the FIRST-minted auxiliary (`MyArr`) and
    // `rec_2` the one minted from inside it (`MyList`); a translation that
    // numbered auxiliaries by any other order — environment order, name
    // order, discovery-set iteration order — admits this swap.
    let (types, ctors, mut recursors) = cascaded_mytree_block();
    let rec_1_ty = recursors[1].base.type_.clone();
    recursors[1].base.type_ = recursors[2].base.type_.clone();
    recursors[2].base.type_ = rec_1_ty;
    let verdict = check(
        &myarr_env(),
        &block_decl(types, ctors, recursors),
        Budget::DEFAULT,
    );
    assert_eq!(reject_class(&verdict), Some(RejectClass::BlockMismatch));
    assert!(
        reject_message(&verdict).contains("diverges from regeneration"),
        "auxiliary recursor numbering must follow creation order: {}",
        reject_message(&verdict)
    );
}

// ---------------------------------------------------------------------------
// KR-608 permutations (bead franken_lean-8ce). Auxiliaries are minted in
// OCCURRENCE order, so permuting the constructor's fields permutes the
// translated block's types — and with them the motive positions, the minor
// order, and which auxiliary `rec_1` eliminates. Permuting the ENVIRONMENT's
// declaration order must change nothing at all: nested heads are resolved by
// name. Both blocks below nest `MyArr MyTree` and `MyList MyTree` directly and
// differ only in which field comes first.
// ---------------------------------------------------------------------------

/// One minor binder — name and type — in telescope order.
type Minor = (Name, Expr);
/// An auxiliary recursor: its restored name suffix and its rules, each a
/// constructor with that constructor's field count.
type AuxRecursorSpec = (&'static str, Vec<(Name, u32)>);

/// The two-field cascading block. `arr_first` puts `MyArr MyTree` before
/// `MyList MyTree` in `MyTree.node`'s telescope.
fn permuted_rows(arr_first: bool) -> (Vec<InductiveVal>, Vec<ConstructorVal>) {
    let tree = || Expr::const_(n("MyTree"), vec![]);
    let arr = || Expr::app(Expr::const_(n("MyArr"), vec![]), tree());
    let list = || Expr::app(Expr::const_(n("MyList"), vec![]), tree());
    let ((first, first_ty), (second, second_ty)) = if arr_first {
        ((n("a"), arr()), (n("l"), list()))
    } else {
        ((n("l"), list()), (n("a"), arr()))
    };
    let ind = InductiveVal {
        base: cval(n("MyTree"), vec![], sort1()),
        num_params: 0,
        num_indices: 0,
        all: vec![n("MyTree")],
        ctors: vec![nn("MyTree", "node")],
        num_nested: 2,
        is_rec: true,
        is_unsafe: false,
        is_reflexive: false,
    };
    let node = ConstructorVal {
        base: cval(
            nn("MyTree", "node"),
            vec![],
            Expr::forall_e(
                first,
                first_ty,
                Expr::forall_e(second, second_ty, tree(), BinderInfo::Default),
                BinderInfo::Default,
            ),
        ),
        induct: n("MyTree"),
        cidx: 0,
        num_params: 0,
        num_fields: 2,
        is_unsafe: false,
    };
    (vec![ind], vec![node])
}

/// The same block in full restored form, with the three recursors the pin
/// would serialize for THAT field order. The two orders are genuinely
/// different decoded rows, not a relabelling: `motive_2`/`motive_3` swap
/// meaning, the minors reorder (`node mk nil cons` versus `node nil cons mk`),
/// and every rule right-hand side shifts with them.
fn permuted_block(arr_first: bool) -> (Vec<InductiveVal>, Vec<ConstructorVal>, Vec<RecursorVal>) {
    let (types, ctors) = permuted_rows(arr_first);
    let tree = || Expr::const_(n("MyTree"), vec![]);
    let arr = || Expr::app(Expr::const_(n("MyArr"), vec![]), tree());
    let list = || Expr::app(Expr::const_(n("MyList"), vec![]), tree());
    let bv = |i: u32| Expr::bvar(i).expect("packs");
    let u = Level::param(n("u"));
    let motive_ty =
        |major: Expr| Expr::forall_e(n("t"), major, Expr::sort(u.clone()), BinderInfo::Default);
    // Motive order IS translated-type order: main, then auxiliaries in
    // creation order — which is the field order.
    let (aux_1, aux_2) = if arr_first {
        (arr(), list())
    } else {
        (list(), arr())
    };
    let motive_1_ty = motive_ty(tree());
    let motive_2_ty = motive_ty(aux_1.clone());
    let motive_3_ty = motive_ty(aux_2.clone());
    // The `node` minor is index-identical under both orders: whichever field
    // comes first is the first-minted auxiliary and therefore `motive_2`.
    let (f1, f1_ty, f2, f2_ty) = if arr_first {
        (n("a"), arr(), n("l"), list())
    } else {
        (n("l"), list(), n("a"), arr())
    };
    let node_minor_ty = Expr::forall_e(
        f1.clone(),
        f1_ty,
        Expr::forall_e(
            f2.clone(),
            f2_ty,
            Expr::forall_e(
                Name::str(Name::anonymous(), format!("{}_ih", f1.to_display_string())),
                Expr::app(bv(3), bv(1)),
                Expr::forall_e(
                    Name::str(Name::anonymous(), format!("{}_ih", f2.to_display_string())),
                    Expr::app(bv(3), bv(1)),
                    Expr::app(
                        bv(6),
                        Expr::app(
                            Expr::app(Expr::const_(nn("MyTree", "node"), vec![]), bv(3)),
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
    let mk_app = |data: Expr| {
        Expr::app(
            Expr::app(Expr::const_(nn("MyArr", "mk"), vec![]), tree()),
            data,
        )
    };
    let nil_app = || Expr::app(Expr::const_(nn("MyList", "nil"), vec![]), tree());
    let cons_app = |head: Expr, tail: Expr| {
        Expr::app(
            Expr::app(
                Expr::app(Expr::const_(nn("MyList", "cons"), vec![]), tree()),
                head,
            ),
            tail,
        )
    };
    // Minor types depend on each minor's POSITION in the telescope, so the two
    // orders carry different de Bruijn indices for the same judgment.
    let (minors, aux_rules): (Vec<Minor>, [AuxRecursorSpec; 2]) = if arr_first {
        // …node mk nil cons: mk is the 2nd minor, nil/cons the 3rd and 4th.
        let mk_minor_ty = Expr::forall_e(
            n("data"),
            list(),
            Expr::forall_e(
                n("data_ih"),
                Expr::app(bv(2), bv(0)),
                Expr::app(bv(4), mk_app(bv(1))),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        let nil_minor_ty = Expr::app(bv(2), nil_app());
        let cons_minor_ty = Expr::forall_e(
            n("head"),
            tree(),
            Expr::forall_e(
                n("tail"),
                list(),
                Expr::forall_e(
                    n("head_ih"),
                    Expr::app(bv(7), bv(1)),
                    Expr::forall_e(
                        n("tail_ih"),
                        Expr::app(bv(6), bv(1)),
                        Expr::app(bv(7), cons_app(bv(3), bv(2))),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        (
            vec![
                (n("node"), node_minor_ty.clone()),
                (n("mk"), mk_minor_ty),
                (n("nil"), nil_minor_ty),
                (n("cons"), cons_minor_ty),
            ],
            [
                ("rec_1", vec![(nn("MyArr", "mk"), 1)]),
                (
                    "rec_2",
                    vec![(nn("MyList", "nil"), 0), (nn("MyList", "cons"), 2)],
                ),
            ],
        )
    } else {
        // …node nil cons mk: nil/cons are the 2nd and 3rd minors, mk the 4th.
        let nil_minor_ty = Expr::app(bv(2), nil_app());
        let cons_minor_ty = Expr::forall_e(
            n("head"),
            tree(),
            Expr::forall_e(
                n("tail"),
                list(),
                Expr::forall_e(
                    n("head_ih"),
                    Expr::app(bv(6), bv(1)),
                    Expr::forall_e(
                        n("tail_ih"),
                        Expr::app(bv(6), bv(1)),
                        Expr::app(bv(7), cons_app(bv(3), bv(2))),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        let mk_minor_ty = Expr::forall_e(
            n("data"),
            list(),
            Expr::forall_e(
                n("data_ih"),
                Expr::app(bv(5), bv(0)),
                Expr::app(bv(5), mk_app(bv(1))),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        (
            vec![
                (n("node"), node_minor_ty.clone()),
                (n("nil"), nil_minor_ty),
                (n("cons"), cons_minor_ty),
                (n("mk"), mk_minor_ty),
            ],
            [
                (
                    "rec_1",
                    vec![(nn("MyList", "nil"), 0), (nn("MyList", "cons"), 2)],
                ),
                ("rec_2", vec![(nn("MyArr", "mk"), 1)]),
            ],
        )
    };
    let motive_binders = [
        (n("motive_3"), motive_3_ty.clone()),
        (n("motive_2"), motive_2_ty.clone()),
        (n("motive_1"), motive_1_ty.clone()),
    ];
    let telescope = |major_ty: Expr, result_motive_at: u32| {
        let mut body = Expr::forall_e(
            n("t"),
            major_ty,
            Expr::app(bv(result_motive_at), bv(0)),
            BinderInfo::Default,
        );
        for (name, ty) in minors.iter().rev() {
            body = Expr::forall_e(name.clone(), ty.clone(), body, BinderInfo::Default);
        }
        for (name, ty) in &motive_binders {
            body = Expr::forall_e(name.clone(), ty.clone(), body, BinderInfo::Implicit);
        }
        body
    };
    let lam = |body: Expr, field_lams: &[(Name, Expr)]| {
        let mut inner = body;
        for (name, ty) in field_lams.iter().rev() {
            inner = Expr::lam(name.clone(), ty.clone(), inner, BinderInfo::Default);
        }
        for (name, ty) in minors.iter().rev() {
            inner = Expr::lam(name.clone(), ty.clone(), inner, BinderInfo::Default);
        }
        for (name, ty) in &motive_binders {
            inner = Expr::lam(name.clone(), ty.clone(), inner, BinderInfo::Default);
        }
        inner
    };
    let rec_call = |rec: &str, args: &[u32]| {
        let mut app = Expr::const_(nn("MyTree", rec), vec![u.clone()]);
        for a in args {
            app = Expr::app(app, bv(*a));
        }
        app
    };
    // node: … (f1) (f2) => node f1 f2 (rec_1 … f1) (rec_2 … f2). The minor
    // sits at index 5 under both orders (two fields plus three later minors).
    let node_rhs = lam(
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(bv(5), bv(1)), bv(0)),
                rec_call("rec_1", &[8, 7, 6, 5, 4, 3, 2, 1]),
            ),
            rec_call("rec_2", &[8, 7, 6, 5, 4, 3, 2, 0]),
        ),
        &[(f1, aux_1.clone()), (f2, aux_2.clone())],
    );
    // The `MyList` copy's own recursor: `rec_2` when the list is minted second,
    // `rec_1` when it is minted first.
    let list_rec = if arr_first { "rec_2" } else { "rec_1" };
    let (mk_minor_at, nil_minor_at, cons_minor_at) = if arr_first { (3, 1, 2) } else { (1, 2, 3) };
    let mk_rhs = lam(
        Expr::app(
            Expr::app(bv(mk_minor_at), bv(0)),
            rec_call(list_rec, &[7, 6, 5, 4, 3, 2, 1, 0]),
        ),
        &[(n("data"), list())],
    );
    let nil_rhs = lam(bv(nil_minor_at), &[]);
    let cons_rhs = lam(
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(bv(cons_minor_at), bv(1)), bv(0)),
                rec_call("rec", &[8, 7, 6, 5, 4, 3, 2, 1]),
            ),
            rec_call(list_rec, &[8, 7, 6, 5, 4, 3, 2, 0]),
        ),
        &[(n("head"), tree()), (n("tail"), list())],
    );
    let rhs_for = |ctor: &Name| -> Expr {
        if ctor == &nn("MyArr", "mk") {
            mk_rhs.clone()
        } else if ctor == &nn("MyList", "nil") {
            nil_rhs.clone()
        } else {
            cons_rhs.clone()
        }
    };
    let mk_rec = |name: Name, ty: Expr, rules: Vec<RecursorRule>| RecursorVal {
        base: cval(name, vec![n("u")], ty),
        all: vec![n("MyTree")],
        num_params: 0,
        num_indices: 0,
        num_motives: 3,
        num_minors: 4,
        rules,
        k: false,
        is_unsafe: false,
    };
    let mut recursors = vec![mk_rec(
        nn("MyTree", "rec"),
        telescope(tree(), 7),
        vec![RecursorRule {
            ctor: nn("MyTree", "node"),
            nfields: 2,
            rhs: node_rhs,
        }],
    )];
    for (index, (rec_name, rules)) in aux_rules.iter().enumerate() {
        let major = if index == 0 {
            aux_1.clone()
        } else {
            aux_2.clone()
        };
        recursors.push(mk_rec(
            nn("MyTree", rec_name),
            telescope(major, 6 - index as u32),
            rules
                .iter()
                .map(|(ctor, nfields)| RecursorRule {
                    ctor: ctor.clone(),
                    nfields: *nfields,
                    rhs: rhs_for(ctor),
                })
                .collect(),
        ));
    }
    (types, ctors, recursors)
}

/// Step ceiling for admitting the cascading block. Deduplication is what makes
/// the translation terminate at all — without it each minted copy's own
/// self-occurrence mints another copy forever — so the cost covenant is the
/// discriminating, TERMINATING form of that mutant: a run that mints redundant
/// auxiliaries blows this ceiling and reports typed exhaustion instead of the
/// verdict. Pinned at roughly twice the measured cost so ordinary refactors do
/// not trip it. Measured cost at the time of pinning: 151 steps.
const CASCADE_STEP_CAP: u64 = 300;

// ---------------------------------------------------------------------------
// KR-608 property lane (bead franken_lean-8ce). The fixtures above prove the
// shapes I thought of. This proves the ones I did not: random nested shapes,
// each checked against an INDEPENDENT model of the pin's discovery rule —
// occurrences are the applications whose parameter mentions a block type, each
// copy exposes its family's constructor fields instantiated at the occurrence,
// and the worklist closes over what those expose, deduplicated.
//
// Deterministic and replayable: fixed seeds, a dependency-free SplitMix64, and
// every failure prints the seed, the trial, the rendered constructor and the
// exact permutation, so a red run reproduces without re-rolling.
// ---------------------------------------------------------------------------

/// SplitMix64 — the test apparatus obeys D1 too, so the generator is ours.
struct SplitMix64(u64);

impl SplitMix64 {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next_u64() % n as u64) as usize
    }
}

/// The parameterized families the fixture environment declares.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Family {
    List,
    Arr,
}

impl Family {
    fn name(self) -> Name {
        match self {
            Family::List => n("MyList"),
            Family::Arr => n("MyArr"),
        }
    }

    fn label(self) -> &'static str {
        match self {
            Family::List => "MyList",
            Family::Arr => "MyArr",
        }
    }

    /// What a copy of this family exposes: its constructors' field types,
    /// written over the family's own parameter. This is the model's only
    /// knowledge of the environment, and it mirrors the rows `mylist_rows`
    /// and `myarr_rows` declare — `MyList.cons : α → MyList α → MyList α`
    /// (`MyList.nil` has no fields) and `MyArr.mk : MyList α → MyArr α`.
    fn field_shapes(self) -> Vec<ParamShape> {
        match self {
            Family::List => vec![
                ParamShape::Param,
                ParamShape::App(Family::List, Box::new(ParamShape::Param)),
            ],
            Family::Arr => vec![ParamShape::App(Family::List, Box::new(ParamShape::Param))],
        }
    }
}

/// A generated field type: `MyTree`, `MyUnit`, or a family applied to another.
#[derive(Clone, PartialEq, Eq, Debug)]
enum Shape {
    Tree,
    Unit,
    App(Family, Box<Shape>),
}

/// A family's field type, written over its parameter.
enum ParamShape {
    Param,
    App(Family, Box<ParamShape>),
}

impl Shape {
    fn render(&self) -> String {
        match self {
            Shape::Tree => "MyTree".to_string(),
            Shape::Unit => "MyUnit".to_string(),
            Shape::App(f, arg) => format!("({} {})", f.label(), arg.render()),
        }
    }

    fn to_expr(&self) -> Expr {
        match self {
            Shape::Tree => Expr::const_(n("MyTree"), vec![]),
            Shape::Unit => Expr::const_(n("MyUnit"), vec![]),
            Shape::App(f, arg) => Expr::app(Expr::const_(f.name(), vec![]), arg.to_expr()),
        }
    }

    fn mentions_tree(&self) -> bool {
        match self {
            Shape::Tree => true,
            Shape::Unit => false,
            Shape::App(_, arg) => arg.mentions_tree(),
        }
    }

    /// The pin's rule: an application is a nested occurrence exactly when one
    /// of the head's parameters mentions a type of the block being declared.
    /// The parameter is NOT descended into here — it is carried verbatim into
    /// the occurrence key and only translated inside the copy, which is what
    /// makes the worklist necessary.
    fn occurrence(&self) -> Option<(Family, Shape)> {
        match self {
            Shape::App(f, arg) if arg.mentions_tree() => Some((*f, (**arg).clone())),
            _ => None,
        }
    }
}

fn substitute(shape: &ParamShape, arg: &Shape) -> Shape {
    match shape {
        ParamShape::Param => arg.clone(),
        ParamShape::App(f, inner) => Shape::App(*f, Box::new(substitute(inner, arg))),
    }
}

/// The independent model: the deduplicated worklist closure of the auxiliaries
/// a block with these constructor fields must mint, in creation order.
fn expected_auxiliaries(fields: &[Shape]) -> Vec<(Family, Shape)> {
    let mut auxes: Vec<(Family, Shape)> = Vec::new();
    let push = |auxes: &mut Vec<(Family, Shape)>, occurrence: Option<(Family, Shape)>| {
        if let Some(occurrence) = occurrence
            && !auxes.contains(&occurrence)
        {
            auxes.push(occurrence);
        }
    };
    for field in fields {
        push(&mut auxes, field.occurrence());
    }
    let mut next = 0;
    while next < auxes.len() {
        let (family, arg) = auxes[next].clone();
        for field_shape in family.field_shapes() {
            let field = substitute(&field_shape, &arg);
            push(&mut auxes, field.occurrence());
        }
        next += 1;
    }
    auxes
}

/// `MyUnit` — a nullary type, so a generated field can be legitimately
/// NON-nested and the model is tested on what must not be minted too.
fn property_env(arr_first: bool) -> Environment {
    let unit = InductiveVal {
        base: cval(n("MyUnit"), vec![], sort1()),
        num_params: 0,
        num_indices: 0,
        all: vec![n("MyUnit")],
        ctors: vec![nn("MyUnit", "mk")],
        num_nested: 0,
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    };
    let mk = ConstructorVal {
        base: cval(
            nn("MyUnit", "mk"),
            vec![],
            Expr::const_(n("MyUnit"), vec![]),
        ),
        induct: n("MyUnit"),
        cidx: 0,
        num_params: 0,
        num_fields: 0,
        is_unsafe: false,
    };
    cascade_env(arr_first)
        .add_decl(ConstantInfo::Induct(unit))
        .expect("env")
        .add_decl(ConstantInfo::Ctor(mk))
        .expect("env")
}

/// A generated block: `MyTree.node : fields… → MyTree`, declaring no recursors
/// so the translated type count is observable as a typed rejection.
fn generated_block(fields: &[Shape], num_nested: u32) -> Declaration {
    let tree = || Expr::const_(n("MyTree"), vec![]);
    let mut ctor_type = tree();
    for (index, field) in fields.iter().enumerate().rev() {
        ctor_type = Expr::forall_e(
            Name::str(Name::anonymous(), format!("f{index}")),
            field.to_expr(),
            ctor_type,
            BinderInfo::Default,
        );
    }
    let ind = InductiveVal {
        base: cval(n("MyTree"), vec![], sort1()),
        num_params: 0,
        num_indices: 0,
        all: vec![n("MyTree")],
        ctors: vec![nn("MyTree", "node")],
        num_nested,
        is_rec: true,
        is_unsafe: false,
        is_reflexive: false,
    };
    let node = ConstructorVal {
        base: cval(nn("MyTree", "node"), vec![], ctor_type),
        induct: n("MyTree"),
        cidx: 0,
        num_params: 0,
        num_fields: fields.len() as u32,
        is_unsafe: false,
    };
    block_decl(vec![ind], vec![node], vec![])
}

fn random_shape(rng: &mut SplitMix64, depth: usize) -> Shape {
    if depth == 0 {
        return if rng.below(2) == 0 {
            Shape::Tree
        } else {
            Shape::Unit
        };
    }
    match rng.below(4) {
        0 => Shape::Tree,
        1 => Shape::Unit,
        2 => Shape::App(Family::List, Box::new(random_shape(rng, depth - 1))),
        _ => Shape::App(Family::Arr, Box::new(random_shape(rng, depth - 1))),
    }
}

fn render_fields(fields: &[Shape]) -> String {
    let rendered: Vec<String> = fields.iter().map(Shape::render).collect();
    format!("MyTree.node : {} → MyTree", rendered.join(" → "))
}

/// Fixed seeds; every trial is a fresh random block plus a random permutation
/// of its fields, checked against both environment declaration orders.
const PROPERTY_SEEDS: [u64; 4] = [
    0x0000_0000_0000_002a,
    0x5eed_0000_dead_beef,
    0xa5a5_a5a5_5a5a_5a5a,
    0x0123_4567_89ab_cdef,
];
const TRIALS_PER_SEED: usize = 120;

#[test]
fn kr608_random_nested_shapes_agree_with_the_independent_model() {
    // Coverage counters. A property lane that generates only trivial shapes
    // passes while proving nothing, so the corpus has to justify itself: the
    // floors below are asserted after the loop.
    let mut cascading = 0usize;
    let mut multi_aux = 0usize;
    let mut deepest = 0usize;
    for seed in PROPERTY_SEEDS {
        let mut rng = SplitMix64(seed);
        for trial in 0..TRIALS_PER_SEED {
            // Generate until the block actually nests: a block with no nested
            // occurrence takes the ordinary path, which this lane is not about.
            let (fields, auxes) = loop {
                let count = 1 + rng.below(4);
                let fields: Vec<Shape> = (0..count)
                    .map(|_| {
                        let depth = 1 + rng.below(3);
                        random_shape(&mut rng, depth)
                    })
                    .collect();
                let auxes = expected_auxiliaries(&fields);
                if !auxes.is_empty() {
                    break (fields, auxes);
                }
            };
            // A random permutation of the fields (Fisher-Yates, same stream).
            let mut permutation: Vec<usize> = (0..fields.len()).collect();
            for i in (1..permutation.len()).rev() {
                permutation.swap(i, rng.below(i + 1));
            }
            let permuted: Vec<Shape> = permutation.iter().map(|&i| fields[i].clone()).collect();
            // The auxiliary SET is permutation-invariant, so both orders must
            // report the same translated type count — only the order differs.
            let permuted_auxes = expected_auxiliaries(&permuted);
            assert_eq!(
                auxes.len(),
                permuted_auxes.len(),
                "seed {seed:#x} trial {trial}: the model's own auxiliary count \
                 moved under permutation {permutation:?}\n  original: {}\n  permuted: {}",
                render_fields(&fields),
                render_fields(&permuted)
            );
            // An auxiliary the fields do not name directly was discovered
            // inside another copy — the cascade this bead exists for.
            let direct = fields.iter().filter_map(Shape::occurrence).fold(
                Vec::new(),
                |mut seen: Vec<(Family, Shape)>, occurrence| {
                    if !seen.contains(&occurrence) {
                        seen.push(occurrence);
                    }
                    seen
                },
            );
            if auxes.len() > direct.len() {
                cascading += 1;
            }
            if auxes.len() >= 2 {
                multi_aux += 1;
            }
            deepest = deepest.max(auxes.len());
            let expected = format!(
                "block declares 0 recursors, expected {} (main + auxiliary)",
                1 + auxes.len()
            );
            for (label, order) in [("declared", &fields), ("permuted", &permuted)] {
                for arr_first in [true, false] {
                    let verdict = check(
                        &property_env(arr_first),
                        &generated_block(order, auxes.len() as u32),
                        Budget::DEFAULT,
                    );
                    let context = format!(
                        "seed {seed:#x} trial {trial} [{label} order, env arr_first={arr_first}]\n  \
                         permutation: {permutation:?}\n  block: {}\n  model auxiliaries: {}",
                        render_fields(order),
                        auxes
                            .iter()
                            .map(|(f, arg)| format!("{} {}", f.label(), arg.render()))
                            .collect::<Vec<_>>()
                            .join(", ")
                    );
                    match &verdict {
                        Outcome::Complete(Verdict::Rejected { class, message, .. }) => {
                            assert_eq!(
                                *class,
                                RejectClass::BlockMismatch,
                                "{context}\n  expected a block-mismatch rejection, got {class:?}: {message}"
                            );
                            assert!(
                                message.contains(&expected),
                                "{context}\n  expected: {expected}\n  actual:   {message}"
                            );
                        }
                        other => panic!(
                            "{context}\n  expected the recursor-count rejection, got {other:?}"
                        ),
                    }
                }
            }
        }
    }
    let trials = PROPERTY_SEEDS.len() * TRIALS_PER_SEED;
    assert!(
        cascading * 10 >= trials,
        "corpus is too shallow: only {cascading}/{trials} trials needed the \
         worklist to reach an auxiliary no field names directly"
    );
    assert!(
        multi_aux * 4 >= trials,
        "corpus is too shallow: only {multi_aux}/{trials} trials minted two or \
         more auxiliaries"
    );
    assert!(
        deepest >= 3,
        "corpus never reached a three-auxiliary block (deepest was {deepest})"
    );
}

#[test]
fn kr608_same_head_at_two_instantiations_mints_distinct_auxiliaries() {
    // MUTANT ("altered auxiliary names"): the minted names carry a per-copy
    // uniquifier. It is load-bearing ONLY when one head is copied at two
    // different instantiations in a single block — `MyList MyTree` and
    // `MyList (MyList MyTree)` here. Lean.Syntax never does this (each of its
    // heads is nested at one instantiation), so the real Prelude replay cannot
    // see the uniquifier at all; without this fixture, dropping it is a
    // surviving mutant. With the names collapsed, the translated block would
    // declare the same auxiliary type twice and a LEGITIMATE block would be
    // refused `already declared`.
    let tree = || Expr::const_(n("MyTree"), vec![]);
    let list = |arg: Expr| Expr::app(Expr::const_(n("MyList"), vec![]), arg);
    let ind = InductiveVal {
        base: cval(n("MyTree"), vec![], sort1()),
        num_params: 0,
        num_indices: 0,
        all: vec![n("MyTree")],
        ctors: vec![nn("MyTree", "node")],
        num_nested: 2,
        is_rec: true,
        is_unsafe: false,
        is_reflexive: false,
    };
    let node = ConstructorVal {
        base: cval(
            nn("MyTree", "node"),
            vec![],
            Expr::forall_e(
                n("shallow"),
                list(tree()),
                Expr::forall_e(n("deep"), list(list(tree())), tree(), BinderInfo::Default),
                BinderInfo::Default,
            ),
        ),
        induct: n("MyTree"),
        cidx: 0,
        num_params: 0,
        num_fields: 2,
        is_unsafe: false,
    };
    let verdict = check(
        &mylist_env(),
        &block_decl(vec![ind], vec![node], vec![]),
        Budget::DEFAULT,
    );
    // Two DISTINCT auxiliaries were minted from the same head, so the
    // translated block has three types and wants three recursors. The block
    // deliberately declares none, which is how the count becomes observable
    // without hand-building the telescopes; a name collision would instead
    // fail earlier, and differently.
    assert_eq!(reject_class(&verdict), Some(RejectClass::BlockMismatch));
    let message = reject_message(&verdict);
    assert!(
        message.contains("block declares 0 recursors, expected 3"),
        "one head at two instantiations must mint two distinct auxiliaries: {message}"
    );
    assert!(
        !message.contains("already declared"),
        "auxiliary names must stay distinct across instantiations of one head: {message}"
    );
}

#[test]
fn kr608_deduplication_keeps_the_cascade_cost_bounded() {
    // The capped run comes FIRST and is what makes this mutant terminating: a
    // translation that mints a fresh auxiliary per reachability path never
    // finishes (each copy's own self-occurrence mints another), so under a
    // generous budget it would spin instead of failing. Bounded to the
    // ceiling, it stops at typed exhaustion and the assertion below fires.
    let (types, ctors, recursors) = cascaded_mytree_block();
    let capped = check(
        &myarr_env(),
        &block_decl(types, ctors, recursors),
        Budget::DEFAULT.narrowed(CASCADE_STEP_CAP, 4_096),
    );
    assert!(
        capped.is_accepted(),
        "the cascading block must admit within the pinned ceiling of \
         {CASCADE_STEP_CAP} steps; got {capped:?}"
    );
    // Only then measure the real cost, so the ceiling keeps its margin honest.
    let (types, ctors, recursors) = cascaded_mytree_block();
    let measured = match check(
        &myarr_env(),
        &block_decl(types, ctors, recursors),
        Budget::DEFAULT,
    ) {
        Outcome::Complete(Verdict::Accepted { consumption }) => consumption.steps_used,
        other => panic!("the cascading block must admit; got {other:?}"),
    };
    assert!(
        measured <= CASCADE_STEP_CAP,
        "cascade cost {measured} exceeds the pinned ceiling {CASCADE_STEP_CAP}; \
         a redundant auxiliary was minted"
    );
}

#[test]
fn kr608_permutation_arr_first_admits_byte_exact() {
    // Fields (MyArr MyTree, MyList MyTree): auxiliaries are minted
    // [MyArr, MyList], so `rec_1` eliminates the array copy and the minors run
    // node/mk/nil/cons.
    let (types, ctors, recursors) = permuted_block(true);
    let verdict = check(
        &myarr_env(),
        &block_decl(types, ctors, recursors),
        Budget::DEFAULT,
    );
    assert!(
        verdict.is_accepted(),
        "arr-first permutation must admit with its own recursors; got {verdict:?}"
    );
}

#[test]
fn kr608_permutation_list_first_admits_byte_exact() {
    // The mirrored order (MyList MyTree, MyArr MyTree): auxiliaries are minted
    // [MyList, MyArr], `rec_1` eliminates the list copy, and the minors run
    // node/nil/cons/mk. Same judgment, different serialized block.
    let (types, ctors, recursors) = permuted_block(false);
    let verdict = check(
        &myarr_env(),
        &block_decl(types, ctors, recursors),
        Budget::DEFAULT,
    );
    assert!(
        verdict.is_accepted(),
        "list-first permutation must admit with its own recursors; got {verdict:?}"
    );
}

#[test]
fn kr608_permutation_arr_first_recursors_reject_the_list_first_block() {
    // Insertion order is OBSERVABLE, and each order gets its own recursors: a
    // translation that fixed the auxiliary order (by name, by environment
    // position, by set iteration) would admit this cross-feed.
    let (types, ctors) = permuted_rows(false);
    let (_, _, arr_first_recursors) = permuted_block(true);
    let verdict = check(
        &myarr_env(),
        &block_decl(types, ctors, arr_first_recursors),
        Budget::DEFAULT,
    );
    assert_eq!(reject_class(&verdict), Some(RejectClass::BlockMismatch));
    assert!(
        reject_message(&verdict).contains("diverges from regeneration"),
        "arr-first recursors must not satisfy the list-first block: {}",
        reject_message(&verdict)
    );
}

#[test]
fn kr608_permutation_list_first_recursors_reject_the_arr_first_block() {
    // The mirror of the previous test, so neither direction passes by accident.
    let (types, ctors) = permuted_rows(true);
    let (_, _, list_first_recursors) = permuted_block(false);
    let verdict = check(
        &myarr_env(),
        &block_decl(types, ctors, list_first_recursors),
        Budget::DEFAULT,
    );
    assert_eq!(reject_class(&verdict), Some(RejectClass::BlockMismatch));
    assert!(
        reject_message(&verdict).contains("diverges from regeneration"),
        "list-first recursors must not satisfy the arr-first block: {}",
        reject_message(&verdict)
    );
}

#[test]
fn kr608_permutation_environment_declaration_order_is_not_observable() {
    // The other permutation axis: declaring `MyArr` before `MyList` or after
    // must change nothing, because nested heads are resolved by name out of
    // the environment. Both field orders are checked against both environment
    // orders — four runs, one verdict.
    for arr_first_block in [true, false] {
        for arr_first_env in [true, false] {
            let (types, ctors, recursors) = permuted_block(arr_first_block);
            let verdict = check(
                &cascade_env(arr_first_env),
                &block_decl(types, ctors, recursors),
                Budget::DEFAULT,
            );
            assert!(
                verdict.is_accepted(),
                "declaration order must not be observable \
                 (block arr_first={arr_first_block}, env arr_first={arr_first_env}); got {verdict:?}"
            );
        }
    }
}

#[test]
fn kr608_cascade_discovers_the_transitive_auxiliary() {
    // MUTANT ("stops after the direct edge"): `MyList MyTree` occurs in no
    // declared constructor — only inside the MINTED copy of `MyArr`. A
    // translation that replaced occurrences in the declared block and stopped
    // would mint ONE auxiliary and happily accept this `num_nested = 1` row.
    // The pin's worklist keeps translating the auxiliaries it mints, so the
    // block has two, and the decoded count is wrong.
    let (types, ctors) = cascaded_mytree_rows(1, false);
    let verdict = check(
        &myarr_env(),
        &block_decl(types, ctors, vec![]),
        Budget::DEFAULT,
    );
    assert_eq!(reject_class(&verdict), Some(RejectClass::BlockMismatch));
    assert!(
        reject_message(&verdict).contains("vs 2 translated auxiliaries"),
        "the worklist must cascade into the auxiliary it just minted: {}",
        reject_message(&verdict)
    );
}

#[test]
fn kr608_cascade_regenerates_one_recursor_per_translated_type() {
    // With the auxiliary count agreed, the run reaches the recursor
    // cross-check. The expected count is the translated block's type count —
    // main + both auxiliaries — so this pins that the cascade built a
    // THREE-motive block (`MyTree.rec`, `.rec_1`, `.rec_2`) rather than the
    // two-motive block a direct-only translation would produce. Reaching this
    // check at all means the synthesized block already passed the full
    // ordinary ruleset (positivity, universes, regeneration) after the
    // cascade.
    let (types, ctors) = cascaded_mytree_rows(2, false);
    let verdict = check(
        &myarr_env(),
        &block_decl(types, ctors, vec![]),
        Budget::DEFAULT,
    );
    assert_eq!(reject_class(&verdict), Some(RejectClass::BlockMismatch));
    assert!(
        reject_message(&verdict).contains("block declares 0 recursors, expected 3"),
        "one recursor per translated type, auxiliaries included: {}",
        reject_message(&verdict)
    );
}

#[test]
fn kr608_duplicate_reachability_mints_one_auxiliary() {
    // `MyList MyTree` is now reachable TWICE: directly, as `node`'s second
    // field, and transitively through the `MyArr` copy. The pin dedups by the
    // parameter-normalized occurrence key, so the block still carries exactly
    // two auxiliaries — a translation that minted per reachability path would
    // report three.
    let (types, ctors) = cascaded_mytree_rows(3, true);
    let verdict = check(
        &myarr_env(),
        &block_decl(types, ctors, vec![]),
        Budget::DEFAULT,
    );
    assert_eq!(reject_class(&verdict), Some(RejectClass::BlockMismatch));
    assert!(
        reject_message(&verdict).contains("vs 2 translated auxiliaries"),
        "the same occurrence reached twice is ONE auxiliary: {}",
        reject_message(&verdict)
    );

    // …and the deduplicated block is still the three-type block, so the
    // duplicate path did not silently drop the cascade either.
    let (types, ctors) = cascaded_mytree_rows(2, true);
    let verdict = check(
        &myarr_env(),
        &block_decl(types, ctors, vec![]),
        Budget::DEFAULT,
    );
    assert_eq!(reject_class(&verdict), Some(RejectClass::BlockMismatch));
    assert!(
        reject_message(&verdict).contains("block declares 0 recursors, expected 3"),
        "deduplication must not lose the cascaded auxiliary: {}",
        reject_message(&verdict)
    );
}
