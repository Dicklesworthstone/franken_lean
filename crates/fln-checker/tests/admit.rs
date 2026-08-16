#![forbid(unsafe_code)]

//! KR-970 … KR-973 — the declaration-admission preamble.
//!
//! Every rule is covered by its acceptance *and* its refusal, and every refusal
//! is asserted on its **own typed variant** rather than on a generic rejection:
//! `matches!(v, Verdict::Rejected(_))` passes when the wrong law refused, which
//! is how a rule stops being tested without any test going red.

use std::cell::Cell;
use std::path::{Path, PathBuf};

use fln_checker::admit::{
    ADMISSION_SCHEMA, AdmissionBudget, AdmissionDeferred, AdmissionGround, AdmissionPhase,
    AdmissionRejection, AdmissionStop, BlockRejection, BlockVerdict, Quarantine, QuotientRejection,
    QuotientVerdict, Verdict, admit, admit_block, admit_quotient, admit_quotient_with, admit_with,
};
use fln_checker::defeq::{DefEqBudget, QuickDefEqBudget, QuickDefEqLimit, QuickDefEqStop};
use fln_checker::environment::{
    ConstantDeclaration, ConstantEntry, ConstantEnvironment, ConstantKind, ConstantSafety,
    ConstructorDeclaration, DefinitionBody, DefinitionSafety, EnvironmentBudget,
    EnvironmentOutcome, InductiveDeclaration, QuotientKind, ReducibilityHint,
};
use fln_checker::infer::InferenceBudget;
use fln_checker::term::TermBudget;
use fln_checker::whnf::WhnfBudget;
use fln_checker::wire::{
    DecodeBudget, DecodeOutcome, WireExpr, WireName, decode_expr, decode_name,
};
use fln_core::expr::{BinderInfo, Expr, Literal, NatLit};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_hash::canon::Canonical;

fn primary_name(component: impl Into<String>) -> Name {
    Name::str(Name::anonymous(), component)
}

fn checker_name(component: impl Into<String>) -> WireName {
    let name = primary_name(component);
    match decode_name(&name.to_canonical_bytes(), DecodeBudget::unlimited()) {
        DecodeOutcome::Complete(Ok(value)) => value,
        other => panic!("primary-produced name did not decode: {other:?}"),
    }
}

fn checker_qualified(components: &[&str]) -> WireName {
    let name = Name::from_components(components.iter().copied());
    let outcome = decode_name(&name.to_canonical_bytes(), DecodeBudget::unlimited());
    match outcome {
        DecodeOutcome::Complete(Ok(value)) => Some(value),
        _ => None,
    }
    .expect("primary-produced qualified name must decode")
}

fn decoded(expression: &Expr) -> WireExpr {
    match decode_expr(&expression.to_canonical_bytes(), DecodeBudget::unlimited()) {
        DecodeOutcome::Complete(Ok(value)) => value,
        other => panic!("primary-produced expression did not decode: {other:?}"),
    }
}

/// `Sort 0` — a well-formed declared type, since its own type is `Sort 1`.
fn a_type() -> WireExpr {
    decoded(&Expr::sort(Level::zero()))
}

/// A Nat literal — a well-formed TERM whose type is `Nat`, which is not a sort.
/// This is the KR-972 subject: not malformed, just not a type.
fn not_a_type() -> WireExpr {
    decoded(&Expr::lit(Literal::Nat(NatLit::from_u64(7))))
}

fn header(
    level_parameters: Vec<WireName>,
    type_: WireExpr,
    kind: ConstantKind,
    safety: ConstantSafety,
) -> ConstantDeclaration {
    ConstantDeclaration::header(level_parameters, type_, kind, safety)
}

fn axiom(name: &str) -> ConstantEntry {
    ConstantEntry::new(
        checker_name(name),
        header(
            Vec::new(),
            a_type(),
            ConstantKind::Axiom,
            ConstantSafety::Safe,
        ),
    )
}

fn environment_of(entries: Vec<ConstantEntry>) -> ConstantEnvironment {
    match ConstantEnvironment::build(entries, EnvironmentBudget::unlimited()) {
        EnvironmentOutcome::Complete { environment, .. } => environment,
        other => panic!("environment did not build: {other:?}"),
    }
}

/// The `Nat` constant KR-972's negative cell needs, so that inferring a Nat
/// literal's type succeeds and the run reaches the sort check rather than dying
/// earlier on an unknown constant.
fn nat_environment() -> ConstantEnvironment {
    environment_of(vec![ConstantEntry::new(
        checker_name("Nat"),
        header(
            Vec::new(),
            a_type(),
            ConstantKind::Inductive,
            ConstantSafety::Safe,
        ),
    )])
}

/// A conversion budget of zero. Named once rather than repeated, so the two
/// cells that need it cannot drift apart.
fn starved_conversion() -> AdmissionBudget {
    AdmissionBudget::new(
        InferenceBudget::unlimited(),
        WhnfBudget::unlimited(),
        DefEqBudget::new(
            QuickDefEqBudget::new(0, 0),
            0,
            0,
            0,
            0,
            WhnfBudget::new(0, 0, TermBudget::unlimited()),
        ),
    )
}

fn primary_arrow(domain: Expr, codomain: Expr) -> Expr {
    Expr::forall_e(primary_name("a"), domain, codomain, BinderInfo::Default)
}

fn primary_pi(name: &str, info: BinderInfo, type_: Expr, body: Expr) -> Expr {
    Expr::forall_e(primary_name(name), type_, body, info)
}

fn equality_environment(
    extra_constructor: bool,
    malformed_constructor: bool,
) -> ConstantEnvironment {
    let eq = primary_name("Eq");
    let u_name = primary_name("uEq");
    let u = Level::param(u_name.clone());
    let alpha = Expr::bvar(0).expect("packs");
    let alpha1 = Expr::bvar(1).expect("packs");
    let eq_type = primary_pi(
        "α",
        BinderInfo::Implicit,
        Expr::sort(u.clone()),
        primary_arrow(
            alpha.clone(),
            primary_arrow(alpha1, Expr::sort(Level::zero())),
        ),
    );
    let refl_type = if malformed_constructor {
        Expr::sort(Level::zero())
    } else {
        primary_pi(
            "α",
            BinderInfo::Implicit,
            Expr::sort(u.clone()),
            primary_pi(
                "a",
                BinderInfo::Default,
                Expr::bvar(0).expect("packs"),
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(eq.clone(), vec![u]),
                            Expr::bvar(1).expect("packs"),
                        ),
                        Expr::bvar(0).expect("packs"),
                    ),
                    Expr::bvar(0).expect("packs"),
                ),
            ),
        )
    };
    let mut constructors = vec![checker_qualified(&["Eq", "refl"])];
    if extra_constructor {
        constructors.push(checker_qualified(&["Eq", "extra"]));
    }
    let mut entries = vec![
        ConstantEntry::new(
            checker_name("Eq"),
            ConstantDeclaration::inductive(
                vec![checker_name("uEq")],
                decoded(&eq_type),
                ConstantSafety::Safe,
                InductiveDeclaration::new(
                    1,
                    0,
                    vec![checker_name("Eq")],
                    constructors,
                    0,
                    false,
                    true,
                ),
            ),
        ),
        ConstantEntry::new(
            checker_qualified(&["Eq", "refl"]),
            ConstantDeclaration::constructor(
                vec![checker_name("uEq")],
                decoded(&refl_type),
                ConstantSafety::Safe,
                ConstructorDeclaration::new(checker_name("Eq"), 0, 1, 0),
            ),
        ),
    ];
    if extra_constructor {
        entries.push(ConstantEntry::new(
            checker_qualified(&["Eq", "extra"]),
            ConstantDeclaration::constructor(
                vec![checker_name("uEq")],
                a_type(),
                ConstantSafety::Safe,
                ConstructorDeclaration::new(checker_name("Eq"), 1, 1, 0),
            ),
        ));
    }
    environment_of(entries)
}

fn quotient_entries() -> Vec<ConstantEntry> {
    let quot = primary_name("Quot");
    let u_name = primary_name("u");
    let v_name = primary_name("v");
    let u = Level::param(u_name.clone());
    let v = Level::param(v_name.clone());
    let prop = || Expr::sort(Level::zero());
    let bv = |index| Expr::bvar(index).expect("packs");
    let quot_type = primary_pi(
        "α",
        BinderInfo::Implicit,
        Expr::sort(u.clone()),
        primary_arrow(
            primary_arrow(bv(0), primary_arrow(bv(1), prop())),
            Expr::sort(u.clone()),
        ),
    );
    let quot_app = |alpha: Expr, relation: Expr| {
        Expr::app(
            Expr::app(Expr::const_(quot.clone(), vec![u.clone()]), alpha),
            relation,
        )
    };
    let quot_mk_type = primary_pi(
        "α",
        BinderInfo::Implicit,
        Expr::sort(u.clone()),
        primary_pi(
            "r",
            BinderInfo::Default,
            primary_arrow(bv(0), primary_arrow(bv(1), prop())),
            primary_pi("a", BinderInfo::Default, bv(1), quot_app(bv(2), bv(1))),
        ),
    );
    let eq = primary_name("Eq");
    let sanity = primary_pi(
        "a",
        BinderInfo::Default,
        bv(3),
        primary_pi(
            "b",
            BinderInfo::Default,
            bv(4),
            primary_arrow(
                Expr::app(Expr::app(bv(4), bv(1)), bv(0)),
                Expr::app(
                    Expr::app(
                        Expr::app(Expr::const_(eq, vec![v.clone()]), bv(4)),
                        Expr::app(bv(3), bv(2)),
                    ),
                    Expr::app(bv(3), bv(1)),
                ),
            ),
        ),
    );
    let quot_lift_type = primary_pi(
        "α",
        BinderInfo::Implicit,
        Expr::sort(u.clone()),
        primary_pi(
            "r",
            BinderInfo::Implicit,
            primary_arrow(bv(0), primary_arrow(bv(1), prop())),
            primary_pi(
                "β",
                BinderInfo::Implicit,
                Expr::sort(v.clone()),
                primary_pi(
                    "f",
                    BinderInfo::Default,
                    primary_arrow(bv(2), bv(1)),
                    primary_arrow(sanity, primary_arrow(quot_app(bv(4), bv(3)), bv(3))),
                ),
            ),
        ),
    );
    let quot_mk = Name::str(quot.clone(), "mk");
    let quot_ind_type = primary_pi(
        "α",
        BinderInfo::Implicit,
        Expr::sort(u.clone()),
        primary_pi(
            "r",
            BinderInfo::Implicit,
            primary_arrow(bv(0), primary_arrow(bv(1), prop())),
            primary_pi(
                "β",
                BinderInfo::Implicit,
                primary_arrow(quot_app(bv(1), bv(0)), prop()),
                primary_pi(
                    "mk",
                    BinderInfo::Default,
                    primary_pi(
                        "a",
                        BinderInfo::Default,
                        bv(2),
                        Expr::app(
                            bv(1),
                            Expr::app(
                                Expr::app(
                                    Expr::app(Expr::const_(quot_mk, vec![u.clone()]), bv(3)),
                                    bv(2),
                                ),
                                bv(0),
                            ),
                        ),
                    ),
                    primary_pi(
                        "q",
                        BinderInfo::Default,
                        quot_app(bv(3), bv(2)),
                        Expr::app(bv(2), bv(0)),
                    ),
                ),
            ),
        ),
    );
    vec![
        ConstantEntry::new(
            checker_name("Quot"),
            ConstantDeclaration::quotient(
                vec![checker_name("u")],
                decoded(&quot_type),
                QuotientKind::Type,
            ),
        ),
        ConstantEntry::new(
            checker_qualified(&["Quot", "mk"]),
            ConstantDeclaration::quotient(
                vec![checker_name("u")],
                decoded(&quot_mk_type),
                QuotientKind::Constructor,
            ),
        ),
        ConstantEntry::new(
            checker_qualified(&["Quot", "lift"]),
            ConstantDeclaration::quotient(
                vec![checker_name("u"), checker_name("v")],
                decoded(&quot_lift_type),
                QuotientKind::Lift,
            ),
        ),
        ConstantEntry::new(
            checker_qualified(&["Quot", "ind"]),
            ConstantDeclaration::quotient(
                vec![checker_name("u")],
                decoded(&quot_ind_type),
                QuotientKind::Induction,
            ),
        ),
    ]
}

#[test]
fn kr950_954_quotient_initialization_is_reconstructed_independently() {
    let environment = equality_environment(false, false);
    let mut declarations = quotient_entries();
    declarations.rotate_left(2);
    let verdict = admit_quotient(&environment, &declarations, AdmissionBudget::unlimited());
    assert!(
        verdict.is_admitted(),
        "the exact quotient primitive was not admitted: {verdict:?}"
    );
    let QuotientVerdict::Admitted(admission) = verdict else {
        return;
    };
    assert_eq!(admission.members().len(), 4);
    assert_eq!(
        admission.ground(),
        AdmissionGround::QuotientPrimitiveChecked
    );
    assert_eq!(admission.schema(), ADMISSION_SCHEMA);
}

#[test]
fn kr950_quotient_initialization_checks_the_equality_constructor_type() {
    assert!(matches!(
        admit_quotient(
            &equality_environment(false, true),
            &quotient_entries(),
            AdmissionBudget::unlimited(),
        ),
        QuotientVerdict::Rejected(QuotientRejection::EqualityConstructorShape)
    ));
    assert!(
        admit_quotient(
            &equality_environment(false, false),
            &quotient_entries(),
            AdmissionBudget::unlimited(),
        )
        .is_admitted(),
        "the exact equality constructor must clear the same check"
    );
}

#[test]
fn kr950_level_pairs_consume_the_aggregate_quotient_comparison_budget() {
    let budget = AdmissionBudget::new(
        InferenceBudget::unlimited(),
        WhnfBudget::unlimited(),
        DefEqBudget {
            // The Eq type and constructor contain 18 expression pairs. A
            // comparer that forgets their level pairs reaches the empty-unit
            // rejection; the bounded comparer must stop on pair 19 instead.
            quick: QuickDefEqBudget::new(18, u64::MAX),
            ..DefEqBudget::unlimited()
        },
    );
    assert!(matches!(
        admit_quotient(&equality_environment(false, false), &[], budget),
        QuotientVerdict::Inconclusive(QuickDefEqStop::Resource {
            limit: QuickDefEqLimit::Comparisons,
            allowed: 18,
            observed: 19,
            completed_comparisons: 18,
        })
    ));
    assert!(matches!(
        admit_quotient(
            &equality_environment(false, false),
            &[],
            AdmissionBudget::unlimited(),
        ),
        QuotientVerdict::Rejected(QuotientRejection::DeclarationCount { observed: 0 })
    ));
}

#[test]
fn kr950_954_quotient_rejections_and_nonanswers_do_not_collapse() {
    let environment = equality_environment(false, false);
    let mut malformed = quotient_entries();
    malformed[2] = ConstantEntry::new(
        checker_qualified(&["Quot", "lift"]),
        ConstantDeclaration::quotient(
            vec![checker_name("u"), checker_name("v")],
            a_type(),
            QuotientKind::Lift,
        ),
    );
    assert!(matches!(
        admit_quotient(&environment, &malformed, AdmissionBudget::unlimited()),
        QuotientVerdict::Rejected(QuotientRejection::UnexpectedType { ref name })
            if name == &checker_qualified(&["Quot", "lift"])
    ));

    let starved = AdmissionBudget::new(
        InferenceBudget::unlimited(),
        WhnfBudget::unlimited(),
        DefEqBudget {
            quick: QuickDefEqBudget::new(0, u64::MAX),
            ..DefEqBudget::unlimited()
        },
    );
    assert!(matches!(
        admit_quotient(&environment, &quotient_entries(), starved),
        QuotientVerdict::Inconclusive(_)
    ));
    let aggregate = AdmissionBudget::new(
        InferenceBudget::unlimited(),
        WhnfBudget::unlimited(),
        DefEqBudget {
            quick: QuickDefEqBudget::new(100, u64::MAX),
            ..DefEqBudget::unlimited()
        },
    );
    assert!(matches!(
        admit_quotient(&environment, &quotient_entries(), aggregate),
        QuotientVerdict::Inconclusive(_)
    ));
    assert!(matches!(
        admit_quotient_with(
            &environment,
            &quotient_entries(),
            AdmissionBudget::unlimited(),
            || true,
        ),
        QuotientVerdict::Inconclusive(_)
    ));

    assert!(matches!(
        admit_quotient(
            &equality_environment(true, false),
            &quotient_entries(),
            AdmissionBudget::unlimited(),
        ),
        QuotientVerdict::Rejected(QuotientRejection::EqualityTypeShape)
    ));

    let mut repeated = quotient_entries();
    repeated[3] = repeated[0].clone();
    assert!(matches!(
        admit_quotient(&environment, &repeated, AdmissionBudget::unlimited()),
        QuotientVerdict::Rejected(QuotientRejection::DeclarationMissing {
            kind: QuotientKind::Induction,
        })
    ));

    assert!(
        admit_quotient(
            &environment,
            &quotient_entries(),
            AdmissionBudget::unlimited(),
        )
        .is_admitted(),
        "a completed rejection or non-answer must not poison a later exact run"
    );
}

// ---------------------------------------------------------------- KR-970

#[test]
fn kr970_a_name_already_in_the_environment_is_refused_and_named() {
    let environment = environment_of(vec![axiom("A")]);
    let verdict = admit(&environment, &axiom("A"), AdmissionBudget::unlimited());
    match verdict {
        Verdict::Rejected(AdmissionRejection::NameAlreadyDeclared { name }) => {
            assert_eq!(
                name,
                checker_name("A"),
                "KR-970 must NAME the colliding constant, not merely report a collision"
            );
        }
        other => panic!("expected KR-970's own rejection, got {other:?}"),
    }

    // Control: the same environment and the same shape under a fresh name is
    // admitted, so the cell above cannot be passing because admission is broken.
    assert!(
        admit(&environment, &axiom("B"), AdmissionBudget::unlimited()).is_admitted(),
        "a fresh name in the same environment must still be admitted"
    );
}

// ---------------------------------------------------------------- KR-971

#[test]
fn kr971_a_repeated_level_parameter_is_refused_naming_both_positions() {
    // [u, v, u] — the repeat is NOT adjacent, so a check comparing neighbours
    // passes here, and the two positions are 0 and 2 rather than n-1 and n.
    let candidate = ConstantEntry::new(
        checker_name("C"),
        header(
            vec![checker_name("u"), checker_name("v"), checker_name("u")],
            a_type(),
            ConstantKind::Axiom,
            ConstantSafety::Safe,
        ),
    );
    match admit(
        &ConstantEnvironment::empty(),
        &candidate,
        AdmissionBudget::unlimited(),
    ) {
        Verdict::Rejected(AdmissionRejection::DuplicateLevelParameter {
            name,
            parameter,
            first,
            second,
        }) => {
            assert_eq!(name, checker_name("C"));
            assert_eq!(parameter, checker_name("u"), "the DUPLICATE must be named");
            assert_eq!(
                (first, second),
                (0, 2),
                "both positions are carried, and they are the first repeat in \
                 declaration order rather than the last"
            );
        }
        other => panic!("expected KR-971's own rejection, got {other:?}"),
    }

    // Control: distinct parameters over the identical shape are admitted, so the
    // refusal above is about the repeat and not about carrying parameters.
    let distinct = ConstantEntry::new(
        checker_name("C"),
        header(
            vec![checker_name("u"), checker_name("v")],
            a_type(),
            ConstantKind::Axiom,
            ConstantSafety::Safe,
        ),
    );
    assert!(
        admit(
            &ConstantEnvironment::empty(),
            &distinct,
            AdmissionBudget::unlimited()
        )
        .is_admitted(),
        "distinct level parameters must not be refused"
    );
}

#[test]
fn kr971_is_checked_before_the_context_that_would_also_refuse_it() {
    // `InferenceContext::new` refuses a repeated level parameter too, so KR-971
    // could ride on that refusal and look implemented while being absent. It is
    // checked FIRST and deliberately: this cell fails if the rule is ever
    // deleted, because the context's refusal surfaces as an InternalFault
    // (ContextUnbuildable) rather than as KR-971's rejection.
    let candidate = ConstantEntry::new(
        checker_name("C"),
        header(
            vec![checker_name("u"), checker_name("u")],
            a_type(),
            ConstantKind::Axiom,
            ConstantSafety::Safe,
        ),
    );
    let verdict = admit(
        &ConstantEnvironment::empty(),
        &candidate,
        AdmissionBudget::unlimited(),
    );
    assert!(
        matches!(
            verdict,
            Verdict::Rejected(AdmissionRejection::DuplicateLevelParameter { .. })
        ),
        "a repeat must be KR-971's REJECTION, never an internal fault from a \
         context that could not be built: got {verdict:?}"
    );
}

// ---------------------------------------------------------------- KR-972

#[test]
fn kr972_a_declared_type_that_is_not_a_type_is_refused_at_the_declaration() {
    // The declared type is `7`. That is a well-formed term whose type is `Nat`,
    // and `Nat` is not a sort — so this declaration is refused HERE rather than
    // at first use, which is the whole point of the rule.
    let candidate = ConstantEntry::new(
        checker_name("D"),
        header(
            Vec::new(),
            not_a_type(),
            ConstantKind::Axiom,
            ConstantSafety::Safe,
        ),
    );
    match admit(&nat_environment(), &candidate, AdmissionBudget::unlimited()) {
        Verdict::Rejected(AdmissionRejection::DeclaredTypeIsNotASort { name }) => {
            assert_eq!(name, checker_name("D"));
        }
        other => panic!("expected KR-972's own rejection, got {other:?}"),
    }

    // Control: `Sort 0` in the SAME environment is admitted, so the refusal is
    // attributable to the declared type and not to the environment.
    assert!(
        admit(
            &nat_environment(),
            &axiom("D"),
            AdmissionBudget::unlimited()
        )
        .is_admitted(),
        "a declared type that IS a type must be admitted in the same environment"
    );
}

#[test]
fn kr972_a_declared_type_whose_inference_refuses_is_rejected_carrying_that_refusal() {
    // An unknown constant as the declared type. Inference refuses on its own
    // terms, and KR-972 must carry that refusal rather than flatten it.
    let candidate = ConstantEntry::new(
        checker_name("E"),
        header(
            Vec::new(),
            decoded(&Expr::const_(primary_name("Absent"), Vec::new())),
            ConstantKind::Axiom,
            ConstantSafety::Safe,
        ),
    );
    match admit(
        &ConstantEnvironment::empty(),
        &candidate,
        AdmissionBudget::unlimited(),
    ) {
        Verdict::Rejected(AdmissionRejection::DeclaredTypeRefused { name, refusal }) => {
            assert_eq!(name, checker_name("E"));
            // The nested refusal is retained, not summarised into a boolean.
            let rendered = format!("{refusal:?}");
            assert!(
                rendered.contains("UnknownConstant"),
                "the inference refusal must be CARRIED, got {rendered}"
            );
        }
        other => panic!("expected KR-972's refusal-carrying rejection, got {other:?}"),
    }
}

// ---------------------------------------------------------------- KR-973

#[test]
fn kr973_an_axiom_whose_preamble_passes_is_admitted_end_to_end() {
    let verdict = admit(
        &ConstantEnvironment::empty(),
        &axiom("A"),
        AdmissionBudget::unlimited(),
    );
    match verdict {
        Verdict::Admitted(admission) => {
            assert_eq!(admission.name(), &checker_name("A"));
            assert_eq!(admission.ground(), AdmissionGround::AxiomPreamble);
            assert_eq!(admission.schema(), ADMISSION_SCHEMA);
        }
        other => panic!("an axiom with a clean preamble must be ADMITTED, got {other:?}"),
    }
}

#[test]
fn the_inductive_family_still_defers_after_kr974() {
    // KR-974 moved Theorem, Opaque and Definition OUT of this arm. The inductive
    // family stays, and this cell exists in the direction that matters: it fails
    // if a later slice quietly absorbs a kind it has not built the rule for.
    // Inductive, Constructor, Recursor and Quotient do not carry a body, so
    // folding them into the body check would be scope creep wearing a match arm.
    for kind in [
        ConstantKind::Inductive,
        ConstantKind::Constructor,
        ConstantKind::Recursor,
        ConstantKind::Quotient,
    ] {
        let candidate = ConstantEntry::new(
            checker_name("K"),
            header(Vec::new(), a_type(), kind, ConstantSafety::Safe),
        );
        let verdict = admit(
            &ConstantEnvironment::empty(),
            &candidate,
            AdmissionBudget::unlimited(),
        );
        match verdict {
            Verdict::Deferred(AdmissionDeferred::BodyNotChecked {
                name,
                kind: deferred_kind,
            }) => {
                assert_eq!(name, checker_name("K"));
                assert_eq!(
                    deferred_kind, kind,
                    "the deferral must name the KIND it owes"
                );
            }
            other => panic!("{kind:?} must DEFER, not decide: got {other:?}"),
        }
    }
}

#[test]
fn kr975_an_unsafe_declaration_is_admitted_into_the_quarantine_not_deferred() {
    // This cell replaces `an_unsafe_declaration_is_deferred_even_when_its_preamble_
    // is_clean`, which asserted the behaviour KR-975 exists to remove. Before this
    // slice the checker DEFERRED every unsafe declaration before its kind was even
    // examined, so it could say nothing at all about one.
    let candidate = ConstantEntry::new(
        checker_name("U"),
        header(
            Vec::new(),
            a_type(),
            ConstantKind::Axiom,
            ConstantSafety::Unsafe,
        ),
    );
    match admit(
        &ConstantEnvironment::empty(),
        &candidate,
        AdmissionBudget::unlimited(),
    ) {
        Verdict::Admitted(admission) => {
            assert_eq!(admission.name(), &checker_name("U"));
            assert_eq!(
                admission.ground(),
                AdmissionGround::UnsafeQuarantine,
                "an unsafe admission must report the QUARANTINE ground; reusing the \
                 ordinary one would make a council unable to tell them apart"
            );
        }
        other => {
            panic!("an unsafe declaration must be admitted into the quarantine, got {other:?}")
        }
    }

    // Control: the identical declaration marked Safe reports the ORDINARY ground,
    // so the assertion above is about the safety mark and not about every
    // admission reporting a quarantine.
    match admit(
        &ConstantEnvironment::empty(),
        &axiom("U"),
        AdmissionBudget::unlimited(),
    ) {
        Verdict::Admitted(admission) => assert_eq!(
            admission.ground(),
            AdmissionGround::AxiomPreamble,
            "a safe declaration must NOT report a quarantine ground"
        ),
        other => panic!("the safe control must be admitted, got {other:?}"),
    }
}

#[test]
fn kr976_a_partial_body_lands_in_its_own_quarantine_not_the_unsafe_one() {
    // Two different quarantines. One ground for both would leave the verdict
    // unable to say which, which is the whole reason they are separate variants.
    let partial = ConstantEntry::new(
        checker_name("P"),
        ConstantDeclaration::definition(
            Vec::new(),
            a_type(),
            ConstantSafety::Safe,
            DefinitionBody::new(
                nat_constant(),
                ReducibilityHint::Regular(0),
                DefinitionSafety::Partial,
                Vec::new(),
            ),
        ),
    );
    match admit(&nat_environment(), &partial, AdmissionBudget::unlimited()) {
        Verdict::Admitted(admission) => assert_eq!(
            admission.ground(),
            AdmissionGround::PartialQuarantine,
            "a partial body must land in the PARTIAL quarantine, not the unsafe one"
        ),
        other => panic!("a partial definition must be admitted, got {other:?}"),
    }

    // Control: the identical definition with a Safe body reports the ordinary
    // ground, so the quarantine above is attributable to the body's safety mark.
    match admit(
        &nat_environment(),
        &definition("P", a_type(), nat_constant()),
        AdmissionBudget::unlimited(),
    ) {
        Verdict::Admitted(admission) => assert_eq!(
            admission.ground(),
            AdmissionGround::BodyCheckedAgainstDeclaredType,
            "the safe-bodied control must report the ordinary ground"
        ),
        other => panic!("the safe control must be admitted, got {other:?}"),
    }
}

#[test]
fn kr975_a_safe_header_over_an_unsafe_body_lands_in_the_unsafe_quarantine() {
    // THE DECISION gii.25 WAS FILED TO MAKE. The two safety marks disagree, and
    // the quarantine is keyed on the WEAKEST of them.
    //
    // The argument is consistency, not taste, and this cell pins BOTH halves of
    // it so the reasoning cannot rot into a bare choice: `delta_body` already
    // treats such a declaration as non-unfoldable, and inference already refuses
    // references to it. Admission keying on the header alone would be a third
    // behaviour disagreeing with two existing ones, silently.
    let mixed = ConstantEntry::new(
        checker_name("M"),
        ConstantDeclaration::definition(
            Vec::new(),
            a_type(),
            ConstantSafety::Safe, // the HEADER says safe
            DefinitionBody::new(
                nat_constant(),
                ReducibilityHint::Regular(0),
                DefinitionSafety::Unsafe, // the BODY says otherwise
                Vec::new(),
            ),
        ),
    );
    match admit(&nat_environment(), &mixed, AdmissionBudget::unlimited()) {
        Verdict::Admitted(admission) => assert_eq!(
            admission.ground(),
            AdmissionGround::UnsafeQuarantine,
            "a safe header over an unsafe body must be quarantined as UNSAFE"
        ),
        other => panic!("expected an unsafe-quarantined admission, got {other:?}"),
    }

    // The two existing mechanisms this decision is consistent WITH, asserted
    // rather than cited, so the argument above is measured and not remembered.
    assert!(
        !mixed.declaration().is_delta_unfoldable(),
        "delta_body already treats a safe header over an unsafe body as \
         non-unfoldable; if that ever stops being true the argument for this \
         quarantine choice has lost one of its two legs"
    );
}

// ------------------------------------------------------- FL-INV-07 family

#[test]
fn cancellation_at_every_preamble_checkpoint_is_inconclusive_and_names_its_phase() {
    // Sweep the poll count so each checkpoint is reached in turn. Every observed
    // verdict must be Inconclusive and NEVER a decision; the phases actually
    // reached are collected and required to cover the preamble, so a checkpoint
    // that stops being polled fails here rather than silently going unwatched.
    let environment = nat_environment();
    let candidate = axiom("A");
    let mut seen: Vec<AdmissionPhase> = Vec::new();
    let mut nested = 0_u32;

    // Swept well past the run's own poll count: inference consumes an unknown
    // number of polls between the DeclaredType and DeclaredTypeSort checkpoints,
    // so a sweep sized to the preamble alone can never reach the later ones.
    for budgeted_polls in 0..64_u32 {
        let polls = Cell::new(0_u32);
        let verdict = admit_with(
            &environment,
            &candidate,
            AdmissionBudget::unlimited(),
            || {
                let seen_so_far = polls.get();
                polls.set(seen_so_far + 1);
                seen_so_far >= budgeted_polls
            },
        );
        match verdict {
            Verdict::Inconclusive(AdmissionStop::Cancelled { name, phase }) => {
                assert_eq!(name, checker_name("A"));
                if !seen.contains(&phase) {
                    seen.push(phase);
                }
            }
            // Cancellation observed INSIDE a nested engine. The poll is handed
            // to `infer_with` and `whnf_with` rather than only checked between
            // them, so a long declared-type inference is interruptible; these
            // are the outcomes that prove it.
            Verdict::Inconclusive(
                AdmissionStop::DeclaredTypeInference { .. }
                | AdmissionStop::DeclaredTypeSortWhnf { .. },
            ) => nested += 1,
            Verdict::Admitted(_) => {
                // The poll budget outlived the run; the only non-stop outcome
                // permitted here.
            }
            other => panic!(
                "cancellation must be INCONCLUSIVE, never a decision or a fault: \
                 at {budgeted_polls} polls got {other:?}"
            ),
        }
    }

    assert!(
        nested > 0,
        "cancellation was never observed inside a nested engine, so the poll is \
         not actually reaching inference and a long declared-type check would \
         run to completion regardless"
    );

    for required in [
        AdmissionPhase::UniqueName,
        AdmissionPhase::LevelParameters,
        AdmissionPhase::DeclaredType,
        AdmissionPhase::DeclaredTypeSort,
        AdmissionPhase::Terminal,
    ] {
        assert!(
            seen.contains(&required),
            "no cancellation was observed at {required:?}; a checkpoint that is \
             never reached is a checkpoint that is not there. Reached: {seen:?}"
        );
    }
}

#[test]
fn an_exhausted_declared_type_budget_is_inconclusive_never_rejected() {
    // Resource exhaustion is not a verdict. A budget of zero steps must produce
    // the inconclusive arm carrying inference's own stop, not a rejection that
    // a caller would read as "this declaration is bad".
    let starved = AdmissionBudget::new(
        InferenceBudget::new(0, 0, TermBudget::unlimited(), TermBudget::unlimited()),
        WhnfBudget::unlimited(),
        InferenceBudget::unlimited().defeq,
    );
    let verdict = admit(&ConstantEnvironment::empty(), &axiom("A"), starved);
    match verdict {
        Verdict::Inconclusive(AdmissionStop::DeclaredTypeInference { name, .. }) => {
            assert_eq!(name, checker_name("A"));
        }
        other => panic!("an exhausted budget must be INCONCLUSIVE, got {other:?}"),
    }

    // Control: the identical candidate under an unlimited budget is admitted, so
    // the stop above is the budget and not the declaration.
    assert!(
        admit(
            &ConstantEnvironment::empty(),
            &axiom("A"),
            AdmissionBudget::unlimited()
        )
        .is_admitted(),
        "the same candidate must be admitted when the budget allows it"
    );
}

#[test]
fn the_three_non_answers_are_never_reported_as_admitted() {
    // The FL-INV-07 conservation property stated directly: `is_admitted` and
    // `is_inconclusive_family` must never both hold, over every verdict this
    // suite can produce.
    let starved = AdmissionBudget::new(
        InferenceBudget::new(0, 0, TermBudget::unlimited(), TermBudget::unlimited()),
        WhnfBudget::unlimited(),
        InferenceBudget::unlimited().defeq,
    );
    let unsafe_axiom = ConstantEntry::new(
        checker_name("U"),
        header(
            Vec::new(),
            a_type(),
            ConstantKind::Axiom,
            ConstantSafety::Unsafe,
        ),
    );
    let verdicts = vec![
        admit(
            &ConstantEnvironment::empty(),
            &axiom("A"),
            AdmissionBudget::unlimited(),
        ),
        admit(
            &environment_of(vec![axiom("A")]),
            &axiom("A"),
            AdmissionBudget::unlimited(),
        ),
        admit(
            &ConstantEnvironment::empty(),
            &unsafe_axiom,
            AdmissionBudget::unlimited(),
        ),
        admit(&ConstantEnvironment::empty(), &axiom("A"), starved),
        // KR-974's outcomes, so conservation covers the body check and not only
        // the preamble.
        admit(
            &nat_environment(),
            &definition("D", a_type(), nat_constant()),
            AdmissionBudget::unlimited(),
        ),
        admit(
            &nat_environment(),
            &definition("D", a_type(), a_type()),
            AdmissionBudget::unlimited(),
        ),
        admit(
            &nat_environment(),
            &definition("D", a_type(), nat_constant()),
            starved_conversion(),
        ),
    ];
    let mut admitted = 0;
    for verdict in &verdicts {
        assert!(
            !(verdict.is_admitted() && verdict.is_inconclusive_family()),
            "a verdict may not be both admitted and a non-answer: {verdict:?}"
        );
        if verdict.is_admitted() {
            admitted += 1;
        }
    }
    assert_eq!(
        admitted, 3,
        "exactly three of these seven are genuine admissions -- the axiom preamble, \
         the body-checked definition, and (since KR-975) the UNSAFE axiom, which \
         this list previously expected to defer. A cell where nothing is ever \
         admitted satisfies the property above vacuously, and this count moves \
         DELIBERATELY when an outcome changes rather than being loosened to a \
         floor: it caught KR-975 moving one verdict from Deferred to Admitted, \
         which is exactly the event a floor would have hidden"
    );
}

// --------------------------------------------------------------- FL-INV-02

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("the crate sits two levels below the workspace root")
        .to_path_buf()
}

/// Needles assembled from parts so this scanner's OWN source cannot satisfy the
/// scan it performs — the self-exclusion trap this repository has paid for.
fn laundering_needles() -> Vec<String> {
    let from = String::from("impl ") + "From<";
    vec![
        from.clone() + "Admission>",
        from + "Verdict>",
        String::from("-> ") + "ConstantEntry",
        String::from("-> ") + "ConstantDeclaration",
        String::from("#[derive") + "(Clone)]",
    ]
}

/// Strip the `//`-comment tail of a line, so prose *describing* a forbidden
/// shape is not scored as the shape itself.
fn code_only(line: &str) -> &str {
    match line.find("//") {
        Some(at) => &line[..at],
        None => line,
    }
}

fn laundering_hits(source: &str) -> Vec<String> {
    let mut hits = Vec::new();
    for line in source.lines() {
        let code = code_only(line);
        for needle in laundering_needles() {
            if code.contains(&needle) {
                hits.push(format!("{needle} :: {}", code.trim()));
            }
        }
    }
    hits
}

#[test]
fn the_admission_verdict_is_not_a_capability() {
    // FL-INV-02: fln-checker is an evidence seat, never an alternative admission
    // authority. Two independent halves, because either alone is defeatable.

    // HALF 1 -- the structural fact, derived from the real manifest. No type
    // fln-kernel's admission consumes is even nameable here.
    let manifest = std::fs::read_to_string(workspace_root().join("crates/fln-checker/Cargo.toml"))
        .expect("fln-checker's manifest is readable");
    assert!(
        !manifest.contains("fln-kernel"),
        "fln-checker must not depend on fln-kernel, in any dependency table"
    );
    // Anti-vacuity: a manifest this scan could not read, or one that declares
    // nothing, would satisfy the assertion above while proving nothing.
    assert!(
        manifest.contains("fln-core"),
        "the manifest scan found no known dependency, so it is a broken scan \
         rather than a clean result"
    );

    // HALF 2 -- the surface itself carries no way out.
    let admit_source =
        std::fs::read_to_string(workspace_root().join("crates/fln-checker/src/admit.rs"))
            .expect("the admission module is readable");
    let hits = laundering_hits(&admit_source);
    assert!(
        hits.is_empty(),
        "the admission surface must expose no conversion out of a verdict and no \
         Clone on one: {hits:?}"
    );

    // The scan must be shown CAPABLE of firing, or its empty result means
    // nothing. A decoy carrying each forbidden shape is scored by the same
    // function, and every needle must be found.
    let decoy = laundering_needles()
        .iter()
        .map(|needle| format!("    {needle} Admission {{ }}\n"))
        .collect::<String>();
    assert_eq!(
        laundering_hits(&decoy).len(),
        laundering_needles().len(),
        "the laundering scan did not fire on a planted decoy, so its clean \
         result on the real module is vacuous"
    );

    // And prose must NOT be scored, or the guard reddens on its own doc comment.
    let commented = laundering_needles()
        .iter()
        .map(|needle| format!("    // there is no {needle} here\n"))
        .collect::<String>();
    assert!(
        laundering_hits(&commented).is_empty(),
        "a comment describing a forbidden shape must not be scored as one"
    );
}

#[test]
fn an_axiom_cannot_be_constructed_with_a_body() {
    // `admit` deliberately carries NO "an axiom must not have a body" check,
    // because the state is unconstructible and an unreachable branch is one no
    // mutation can kill. That is a claim about `environment.rs`, so it is bound
    // here: the day a constructor lands that could produce the state, this fails
    // and the missing check becomes owed.
    let source =
        std::fs::read_to_string(workspace_root().join("crates/fln-checker/src/environment.rs"))
            .expect("the environment module is readable");
    let declaration_impl = source
        .split_once("impl ConstantDeclaration {")
        .expect("ConstantDeclaration has an impl block")
        .1
        .split_once("\n}\n")
        .expect("that impl block ends")
        .0;
    let constructor_region = declaration_impl
        .split_once("    pub fn level_parameters")
        .expect("constructors precede the declaration accessors")
        .0;
    let constructors: Vec<&str> = constructor_region
        .lines()
        .map(str::trim)
        .filter(|line| line.starts_with("pub fn "))
        .collect();
    assert_eq!(
        constructors.len(),
        8,
        "ConstantDeclaration gained or lost a constructor, so the reachability \
         of an axiom-with-a-body must be re-measured: {constructors:?}"
    );
    assert!(
        constructors
            .iter()
            .any(|line| line.contains("pub fn header(")),
        "expected the header constructor: {constructors:?}"
    );
    assert!(
        constructors
            .iter()
            .any(|line| line.contains("pub fn definition(")),
        "expected the definition constructor: {constructors:?}"
    );
    assert!(
        constructors
            .iter()
            .any(|line| line.contains("pub fn theorem(")),
        "expected the theorem constructor: {constructors:?}"
    );
    assert!(
        constructors
            .iter()
            .any(|line| line.contains("pub fn opaque(")),
        "expected the opaque constructor: {constructors:?}"
    );
    for name in ["inductive", "constructor", "recursor", "quotient"] {
        assert!(
            constructors
                .iter()
                .any(|line| line.contains(&format!("pub fn {name}("))),
            "expected the {name} constructor: {constructors:?}"
        );
    }
    // `header` is the only constructor reachable with `ConstantKind::Axiom`, and
    // it hardcodes an absent body; every body-bearing constructor hardcodes its
    // non-Axiom kind.
    assert!(
        declaration_impl.contains("body: None,"),
        "the header constructor no longer hardcodes an absent body"
    );
    assert!(
        declaration_impl.contains("kind: ConstantKind::Definition,"),
        "the definition constructor no longer hardcodes the Definition kind"
    );
    assert!(
        declaration_impl.contains("kind: ConstantKind::Theorem,"),
        "the theorem constructor no longer hardcodes the Theorem kind"
    );
    assert!(
        declaration_impl.contains("kind: ConstantKind::Opaque,"),
        "the opaque constructor no longer hardcodes the Opaque kind"
    );
}

// ---------------------------------------------------------------- KR-974

/// A definition whose body's type matches its declared type.
///
/// Declared type `Sort 0`; body `Sort 0`... would be circular, so the honest
/// smallest pair is a declared type that IS a type and a body inhabiting it.
/// `Nat : Sort 0` in `nat_environment`, so a definition declared `Sort 0` with
/// body `Nat` type-checks: `Nat`'s inferred type is `Sort 0`, definitionally
/// equal to the declared `Sort 0`.
/// Builds a DEFINITION. It takes no `kind` on purpose: measured,
/// `ConstantDeclaration::definition` hardcodes `ConstantKind::Definition` and
/// ignores any kind you think you are choosing. An earlier version of this
/// helper accepted one, and three cells silently tested a Definition while
/// their names said Theorem and Opaque.
fn definition(name: &str, declared: WireExpr, body: WireExpr) -> ConstantEntry {
    ConstantEntry::new(
        checker_name(name),
        ConstantDeclaration::definition(
            Vec::new(),
            declared,
            ConstantSafety::Safe,
            DefinitionBody::new(
                body,
                ReducibilityHint::Regular(0),
                DefinitionSafety::Safe,
                Vec::new(),
            ),
        ),
    )
}

fn nat_constant() -> WireExpr {
    decoded(&Expr::const_(primary_name("Nat"), Vec::new()))
}

#[test]
fn kr974_a_definition_whose_body_matches_its_declared_type_is_admitted() {
    let candidate = definition("D", a_type(), nat_constant());
    match admit(&nat_environment(), &candidate, AdmissionBudget::unlimited()) {
        Verdict::Admitted(admission) => {
            assert_eq!(admission.name(), &checker_name("D"));
            assert_eq!(
                admission.ground(),
                AdmissionGround::BodyCheckedAgainstDeclaredType,
                "a body-checked admission must NOT report the axiom preamble's ground; \
                 the two are different claims and reusing one variant hides that"
            );
        }
        other => panic!("expected a body-checked admission, got {other:?}"),
    }
}

#[test]
fn kr974_a_body_whose_type_does_not_match_is_rejected_carrying_the_mismatch() {
    // Declared `Sort 0`, body `Sort 0` -- whose type is `Sort 1`. Two sorts at
    // different levels, which conversion DECIDES.
    //
    // The first version of this cell used body `7`, whose type is the constant
    // `Nat`, against a declared `Sort 0`. That is Constant-vs-Sort, and this
    // checker's conversion DEFERS on it rather than deciding -- correctly, since
    // nothing it has implemented rules out `Nat` reducing to a sort. The code
    // returned Deferred and the cell demanded a mismatch. The code was right:
    // a comparison that did not finish is not a disagreement, which is the exact
    // FL-INV-07 line this rule exists to hold. Cell corrected, not the rule.
    let candidate = definition("D", a_type(), a_type());
    match admit(&nat_environment(), &candidate, AdmissionBudget::unlimited()) {
        Verdict::Rejected(AdmissionRejection::BodyTypeMismatch { name, mismatch }) => {
            assert_eq!(name, checker_name("D"));
            // The nested mismatch is CARRIED, not summarised into a boolean --
            // the gii.23 lesson, where flattening was planted as a mutant.
            assert!(
                !format!("{mismatch:?}").is_empty(),
                "the conversion mismatch must be carried"
            );
        }
        other => panic!("expected KR-974's own mismatch rejection, got {other:?}"),
    }

    // Control: the same shape with a matching body IS admitted, so the rejection
    // is about the body and not about body-checking being broken.
    assert!(
        admit(
            &nat_environment(),
            &definition("D", a_type(), nat_constant()),
            AdmissionBudget::unlimited()
        )
        .is_admitted(),
        "the matching control must still be admitted"
    );
}

#[test]
fn kr974b_a_theorem_whose_declared_type_is_not_a_proposition_is_rejected() {
    // `Sort 0`'s own type is `Sort 1`, which does not normalize to zero, so a
    // theorem declared `Sort 0` has a non-Prop statement.
    //
    // The body itself is well-typed for the declaration. This isolates KR-974b:
    // the theorem must be rejected because its statement is not a proposition,
    // before its otherwise-valid body can influence the result.
    let candidate = ConstantEntry::new(
        checker_name("T"),
        ConstantDeclaration::theorem(Vec::new(), a_type(), nat_constant(), Vec::new()),
    );
    match admit(&nat_environment(), &candidate, AdmissionBudget::unlimited()) {
        Verdict::Rejected(AdmissionRejection::TheoremTypeIsNotAProposition { name }) => {
            assert_eq!(name, checker_name("T"));
        }
        other => panic!("expected KR-974b's own rejection, got {other:?}"),
    }

    // Control: the identical shape as a DEFINITION is not refused by KR-974b, so
    // the rejection above is attributable to the theorem rule and not to the
    // declared type. (It is refused for carrying no body, which is a different
    // rule and the point: a different variant, not a different message.)
    let as_definition = ConstantEntry::new(
        checker_name("T"),
        header(
            Vec::new(),
            a_type(),
            ConstantKind::Definition,
            ConstantSafety::Safe,
        ),
    );
    assert!(
        matches!(
            admit(
                &nat_environment(),
                &as_definition,
                AdmissionBudget::unlimited()
            ),
            Verdict::Rejected(AdmissionRejection::DeclarationCarriesNoBody { .. })
        ),
        "the same shape as a Definition must fail the BODY rule, not KR-974b"
    );
}

#[test]
fn kr974b_a_theorem_whose_statement_is_a_proposition_reaches_the_body_check() {
    // `Nat : Sort 0`, so a theorem DECLARED `Nat` has a Prop statement. A Nat
    // literal inhabits that statement in this fixture, making this a completed
    // theorem admission rather than merely proof that one rejection did not fire.
    let candidate = ConstantEntry::new(
        checker_name("T"),
        ConstantDeclaration::theorem(Vec::new(), nat_constant(), not_a_type(), Vec::new()),
    );
    match admit(&nat_environment(), &candidate, AdmissionBudget::unlimited()) {
        Verdict::Admitted(admission) => assert_eq!(
            admission.ground(),
            AdmissionGround::BodyCheckedAgainstDeclaredType
        ),
        other => panic!("expected a body-checked theorem admission, got {other:?}"),
    }
}

#[test]
fn kr974c_a_body_checked_opaque_is_unreachable_by_construction() {
    // The historical name is retained because the verification manifest binds
    // it. The old unreachable condition is now false: this constructs a real
    // body-bearing Opaque, admits it, and proves admission did not make it
    // delta-unfoldable.
    let opaque = ConstantEntry::new(
        checker_name("O"),
        ConstantDeclaration::opaque(
            Vec::new(),
            a_type(),
            ConstantSafety::Safe,
            nat_constant(),
            Vec::new(),
        ),
    );
    assert!(!opaque.declaration().is_delta_unfoldable());
    match admit(&nat_environment(), &opaque, AdmissionBudget::unlimited()) {
        Verdict::Admitted(admission) => assert_eq!(
            admission.ground(),
            AdmissionGround::BodyCheckedAgainstDeclaredType
        ),
        other => panic!("expected a body-checked opaque admission, got {other:?}"),
    }

    let mismatch = ConstantEntry::new(
        checker_name("BadOpaque"),
        ConstantDeclaration::opaque(
            Vec::new(),
            a_type(),
            ConstantSafety::Safe,
            a_type(),
            Vec::new(),
        ),
    );
    assert!(matches!(
        admit(&nat_environment(), &mismatch, AdmissionBudget::unlimited()),
        Verdict::Rejected(AdmissionRejection::BodyTypeMismatch { .. })
    ));

    // Anti-vacuity for the unfoldability assertion above: a Definition WITH a
    // body IS delta-unfoldable, so "not unfoldable" is a real property here and
    // not something true of every declaration.
    assert!(
        definition("O", a_type(), nat_constant())
            .declaration()
            .is_delta_unfoldable(),
        "the definition control must be unfoldable, or opacity is vacuous"
    );
}

#[test]
fn kr974_a_body_carrying_kind_declared_with_no_body_is_rejected_not_faulted() {
    // `ConstantDeclaration::header` accepts any kind and hardcodes an absent
    // body, so a bodyless Definition is CONSTRUCTIBLE caller input -- measured,
    // which is why this is a rejection and not an internal fault. FL-INV-07
    // reserves the fault arm for invariant failures, never user diagnostics.
    for kind in [
        ConstantKind::Definition,
        ConstantKind::Theorem,
        ConstantKind::Opaque,
    ] {
        let declared = if kind == ConstantKind::Theorem {
            nat_constant() // a Prop statement, so KR-974b does not fire first
        } else {
            a_type()
        };
        let candidate = ConstantEntry::new(
            checker_name("B"),
            header(Vec::new(), declared, kind, ConstantSafety::Safe),
        );
        match admit(&nat_environment(), &candidate, AdmissionBudget::unlimited()) {
            Verdict::Rejected(AdmissionRejection::DeclarationCarriesNoBody {
                name,
                kind: rejected,
            }) => {
                assert_eq!(name, checker_name("B"));
                assert_eq!(rejected, kind);
            }
            other => panic!("{kind:?} with no body must be REJECTED, got {other:?}"),
        }
    }
}

#[test]
fn kr974_an_exhausted_conversion_budget_is_inconclusive_never_a_mismatch() {
    // The arm most likely to be got wrong: a body check that could not finish
    // looks exactly like a body check that failed. A starved CONVERSION budget
    // must never be reported as a mismatch.
    let candidate = definition("D", a_type(), nat_constant());
    let verdict = admit(&nat_environment(), &candidate, starved_conversion());
    assert!(
        !matches!(
            verdict,
            Verdict::Rejected(AdmissionRejection::BodyTypeMismatch { .. })
        ),
        "an exhausted conversion budget must NEVER be reported as a mismatch, got {verdict:?}"
    );
    assert!(
        verdict.is_inconclusive_family(),
        "an exhausted conversion budget must be a non-answer, got {verdict:?}"
    );

    // Control: the identical candidate under an unlimited budget is admitted.
    assert!(
        admit(
            &nat_environment(),
            &definition("D", a_type(), nat_constant()),
            AdmissionBudget::unlimited()
        )
        .is_admitted(),
        "the same candidate must be admitted when the budget allows it"
    );
}

#[test]
fn kr975b_the_reference_gate_is_keyed_on_the_header_and_fires_in_both_directions() {
    // The gate `infer.rs` already enforces: a SAFE declaration may not reference
    // an unsafe constant. That half predates this slice and is correct — but
    // nothing asserted it from admission, so a slice that "tightened" the mode
    // would silently make every unsafe declaration unadmittable and no cell
    // would notice. Both directions are pinned here.
    let unsafe_constant = ConstantEntry::new(
        checker_name("Danger"),
        header(
            Vec::new(),
            a_type(),
            ConstantKind::Axiom,
            ConstantSafety::Unsafe,
        ),
    );
    let environment = environment_of(vec![
        unsafe_constant,
        ConstantEntry::new(
            checker_name("Nat"),
            header(
                Vec::new(),
                a_type(),
                ConstantKind::Inductive,
                ConstantSafety::Safe,
            ),
        ),
    ]);
    let referencing_body = decoded(&Expr::const_(primary_name("Danger"), Vec::new()));

    // SAFE header: the gate is ON, and the reference is refused carrying
    // inference's own typed refusal rather than a generic rejection.
    let safe_referrer = ConstantEntry::new(
        checker_name("S"),
        ConstantDeclaration::definition(
            Vec::new(),
            a_type(),
            ConstantSafety::Safe,
            DefinitionBody::new(
                referencing_body.clone(),
                ReducibilityHint::Regular(0),
                DefinitionSafety::Safe,
                Vec::new(),
            ),
        ),
    );
    match admit(&environment, &safe_referrer, AdmissionBudget::unlimited()) {
        Verdict::Rejected(AdmissionRejection::BodyTypeRefused { name, refusal }) => {
            assert_eq!(name, checker_name("S"));
            let rendered = format!("{refusal:?}");
            assert!(
                rendered.contains("UnsafeConstant"),
                "a safe declaration referencing an unsafe constant must be refused \
                 carrying UnsafeConstant, got {rendered}"
            );
        }
        other => panic!("the safe referrer must be refused by the gate, got {other:?}"),
    }

    // UNSAFE header: the gate is OFF, and the SAME reference is permitted. This
    // is the direction that is currently accidental — `admit` keys the mode on
    // the header, so `checks_safe_declaration()` is false here.
    let unsafe_referrer = ConstantEntry::new(
        checker_name("S"),
        ConstantDeclaration::definition(
            Vec::new(),
            a_type(),
            ConstantSafety::Unsafe,
            DefinitionBody::new(
                referencing_body,
                ReducibilityHint::Regular(0),
                DefinitionSafety::Unsafe,
                Vec::new(),
            ),
        ),
    );
    let verdict = admit(&environment, &unsafe_referrer, AdmissionBudget::unlimited());
    assert!(
        !matches!(
            &verdict,
            Verdict::Rejected(AdmissionRejection::BodyTypeRefused { refusal, .. })
                if format!("{refusal:?}").contains("UnsafeConstant")
        ),
        "an UNSAFE declaration must be allowed to reference an unsafe constant; \
         the gate is keyed on the header and this is the direction a mode \
         'tightening' would silently break: got {verdict:?}"
    );

    // THE THIRD COMBINATION, and it is the one that separates keying the gate on
    // the HEADER from keying it on effective safety. A SAFE header over an UNSAFE
    // body: the quarantine says unsafe, but the gate must still be ON, or a
    // caller unlocks unsafe references by marking only the body -- the mark the
    // header does not advertise.
    //
    // Added because a planted mutant that keyed the mode on effective safety
    // SURVIVED the two cases above: both agree under either keying, so the cell
    // was testing the property its own doc comment argues for in exactly the two
    // places where the argument does not bite.
    let mixed_referrer = ConstantEntry::new(
        checker_name("S"),
        ConstantDeclaration::definition(
            Vec::new(),
            a_type(),
            ConstantSafety::Safe, // header: safe, so the gate stays ON
            DefinitionBody::new(
                decoded(&Expr::const_(primary_name("Danger"), Vec::new())),
                ReducibilityHint::Regular(0),
                DefinitionSafety::Unsafe, // body: unsafe, so the QUARANTINE is unsafe
                Vec::new(),
            ),
        ),
    );
    match admit(&environment, &mixed_referrer, AdmissionBudget::unlimited()) {
        Verdict::Rejected(AdmissionRejection::BodyTypeRefused { refusal, .. }) => {
            let rendered = format!("{refusal:?}");
            assert!(
                rendered.contains("UnsafeConstant"),
                "a SAFE-header declaration must not reach an unsafe constant even \
                 when its own body is marked unsafe, got {rendered}"
            );
        }
        other => panic!(
            "a safe header over an unsafe body must still be GATED -- otherwise \
             marking only the body unlocks unsafe references: got {other:?}"
        ),
    }
}

// ---------------------------------------------------------------- KR-977

/// One member of a mutual block: an unsafe definition naming the whole block.
fn member(name: &str, block: &[&str], safety: DefinitionSafety) -> ConstantEntry {
    ConstantEntry::new(
        checker_name(name),
        ConstantDeclaration::definition(
            Vec::new(),
            a_type(),
            ConstantSafety::Safe,
            DefinitionBody::new(
                nat_constant(),
                ReducibilityHint::Regular(0),
                safety,
                block.iter().map(|n| checker_name(*n)).collect(),
            ),
        ),
    )
}

fn unsafe_pair() -> Vec<ConstantEntry> {
    vec![
        member("A", &["A", "B"], DefinitionSafety::Unsafe),
        member("B", &["A", "B"], DefinitionSafety::Unsafe),
    ]
}

#[test]
fn kr977_an_unsafe_mutual_block_is_admitted_into_the_quarantine() {
    match admit_block(
        &nat_environment(),
        &unsafe_pair(),
        AdmissionBudget::unlimited(),
    ) {
        BlockVerdict::Admitted(admission) => {
            assert_eq!(
                admission.members(),
                &[checker_name("A"), checker_name("B")],
                "the admission must cover EVERY member, in the order supplied"
            );
            assert_eq!(
                admission.ground(),
                AdmissionGround::UnsafeQuarantine,
                "KR-977b refuses a safe block, so a mutual admission is a quarantined \
                 one BY RULE and never an ordinary ground"
            );
        }
        other => panic!("an unsafe mutual block must be admitted, got {other:?}"),
    }
}

#[test]
fn kr977b_a_block_of_safe_definitions_is_refused_because_mutual_is_unsafe_only() {
    // The rule the inventory's title names, and the one that makes KR-977 a
    // quarantine rule rather than bookkeeping: mutual recursion is admitted on
    // the strength of the quarantine, never on a check this checker has not run.
    let safe_block = vec![
        member("A", &["A", "B"], DefinitionSafety::Safe),
        member("B", &["A", "B"], DefinitionSafety::Safe),
    ];
    match admit_block(
        &nat_environment(),
        &safe_block,
        AdmissionBudget::unlimited(),
    ) {
        BlockVerdict::Rejected(BlockRejection::SafeBlock { member }) => {
            assert_eq!(member, checker_name("A"));
        }
        other => panic!("a SAFE mutual block must be refused, got {other:?}"),
    }

    // Control: the identical block marked Unsafe IS admitted, so the refusal is
    // attributable to the safety class and not to the block's shape.
    assert!(
        admit_block(
            &nat_environment(),
            &unsafe_pair(),
            AdmissionBudget::unlimited()
        )
        .is_admitted(),
        "the unsafe control must be admitted"
    );
}

#[test]
fn kr977b_a_block_whose_members_disagree_on_safety_is_refused_naming_both_classes() {
    let mixed = vec![
        member("A", &["A", "B"], DefinitionSafety::Unsafe),
        member("B", &["A", "B"], DefinitionSafety::Partial),
    ];
    match admit_block(&nat_environment(), &mixed, AdmissionBudget::unlimited()) {
        BlockVerdict::Rejected(BlockRejection::NonUniformSafety {
            member,
            expected,
            found,
        }) => {
            assert_eq!(member, checker_name("B"));
            assert_eq!(expected, Quarantine::Unsafe);
            assert_eq!(found, Quarantine::Partial);
        }
        other => panic!("a mixed-safety block must be refused naming both, got {other:?}"),
    }
}

#[test]
fn kr977a_each_shape_defect_is_refused_on_its_own_variant() {
    let env = nat_environment();
    let budget = AdmissionBudget::unlimited();

    // Empty: nothing checked, so nothing admitted. Not a degenerate success.
    assert!(
        matches!(
            admit_block(&env, &[], budget),
            BlockVerdict::Rejected(BlockRejection::EmptyBlock)
        ),
        "an empty block must be refused on its own variant"
    );

    // Repeated member, naming BOTH positions.
    let repeated = vec![
        member("A", &["A", "B"], DefinitionSafety::Unsafe),
        member("B", &["A", "B"], DefinitionSafety::Unsafe),
        member("A", &["A", "B"], DefinitionSafety::Unsafe),
    ];
    match admit_block(&env, &repeated, budget) {
        BlockVerdict::Rejected(BlockRejection::RepeatedMember {
            member: name,
            first,
            second,
        }) => {
            assert_eq!(name, checker_name("A"));
            assert_eq!((first, second), (0, 2), "both positions are carried");
        }
        other => panic!("a repeated member must be refused on its own variant, got {other:?}"),
    }

    // Asymmetric membership: B thinks the block is {B, C}, but {A, B} was supplied.
    let asymmetric = vec![
        member("A", &["A", "B"], DefinitionSafety::Unsafe),
        member("B", &["B", "C"], DefinitionSafety::Unsafe),
    ];
    match admit_block(&env, &asymmetric, budget) {
        BlockVerdict::Rejected(BlockRejection::AsymmetricMembership { member: name }) => {
            assert_eq!(name, checker_name("B"));
        }
        other => panic!("asymmetric membership must be refused on its own variant, got {other:?}"),
    }

    // A declaration carrying no mutual list is not part of a block at all.
    let lone = vec![definition("A", a_type(), nat_constant())];
    assert!(
        matches!(
            admit_block(&env, &lone, budget),
            BlockVerdict::Rejected(BlockRejection::MemberDeclaresNoBlock { .. })
        ),
        "a member declaring no block must be refused on its own variant"
    );
}

#[test]
fn kr977a_membership_is_compared_as_a_set_so_a_permutation_is_not_a_defect() {
    // The order a declaration lists its peers in is not a semantic fact, and
    // refusing a permutation would be a wall against a correct block. This is
    // the direction a set-vs-sequence comparison gets wrong silently.
    let permuted = vec![
        member("A", &["B", "A"], DefinitionSafety::Unsafe),
        member("B", &["A", "B"], DefinitionSafety::Unsafe),
    ];
    assert!(
        admit_block(&nat_environment(), &permuted, AdmissionBudget::unlimited()).is_admitted(),
        "a permuted membership list names the same SET and must be admitted"
    );
}

#[test]
fn kr977_a_member_whose_own_admission_fails_carries_its_fl_inv_07_class_up() {
    // The four Member* arms exist so a member that DEFERRED is not reported the
    // same way as one that was REJECTED. This cell fails if they are collapsed.
    let env = nat_environment();

    // A member whose body does not match its declared type: a REJECTION.
    let mismatched = vec![
        ConstantEntry::new(
            checker_name("A"),
            ConstantDeclaration::definition(
                Vec::new(),
                a_type(),
                ConstantSafety::Safe,
                DefinitionBody::new(
                    a_type(), // type is Sort 1, declared is Sort 0
                    ReducibilityHint::Regular(0),
                    DefinitionSafety::Unsafe,
                    vec![checker_name("A"), checker_name("B")],
                ),
            ),
        ),
        member("B", &["A", "B"], DefinitionSafety::Unsafe),
    ];
    match admit_block(&env, &mismatched, AdmissionBudget::unlimited()) {
        BlockVerdict::MemberRejected {
            member: name,
            rejection,
        } => {
            assert_eq!(name, checker_name("A"));
            assert!(
                matches!(*rejection, AdmissionRejection::BodyTypeMismatch { .. }),
                "the member's own rejection must be carried verbatim, got {rejection:?}"
            );
        }
        other => panic!("expected MemberRejected, got {other:?}"),
    }

    // A starved conversion budget: the member is INCONCLUSIVE, and the block must
    // report that class rather than folding it into a rejection.
    let verdict = admit_block(&env, &unsafe_pair(), starved_conversion());
    assert!(
        !matches!(verdict, BlockVerdict::MemberRejected { .. }),
        "an exhausted budget must NEVER surface as a member rejection, got {verdict:?}"
    );
    assert!(
        verdict.is_inconclusive_family(),
        "an exhausted budget must be a non-answer at the block layer too, got {verdict:?}"
    );
}

#[test]
fn kr977_a_refused_block_admits_no_member() {
    // The atomicity property, and an honest note about what asserting it costs.
    //
    // It holds BY CONSTRUCTION rather than by a rollback: `admit_block` takes
    // `&ConstantEnvironment` and returns an observation, so there is no
    // environment mutation anywhere in this module to undo. The value of this
    // cell is therefore PROSPECTIVE -- it fails on the day admission becomes
    // stateful, which is the only day the property could be lost. Recorded that
    // way rather than presented as evidence that a rollback works, because there
    // is no rollback.
    let environment = nat_environment();
    let before = environment.clone();
    let safe_block = vec![
        member("A", &["A", "B"], DefinitionSafety::Safe),
        member("B", &["A", "B"], DefinitionSafety::Safe),
    ];
    let verdict = admit_block(&environment, &safe_block, AdmissionBudget::unlimited());
    assert!(!verdict.is_admitted(), "this block must be refused");
    assert_eq!(
        environment, before,
        "a refused block must leave the environment untouched"
    );
    assert_eq!(
        environment.len(),
        before.len(),
        "and in particular must not have admitted a member"
    );

    // Anti-vacuity: an ADMITTED block leaves it untouched too, so the assertion
    // above is not passing because admission is a no-op for refusals only.
    let ok = admit_block(&environment, &unsafe_pair(), AdmissionBudget::unlimited());
    assert!(ok.is_admitted());
    assert_eq!(
        environment, before,
        "admission produces an OBSERVATION, never an environment -- if this ever \
         fails, the atomicity property above has lost its mechanism"
    );
}

#[test]
fn kr977_the_max_mutual_members_budget_still_binds() {
    // The one part of this machinery that already worked before KR-977: the
    // environment's own meter. A slice that replaced metering with judgement
    // while silently dropping the meter would be a regression nothing else
    // watches, so the meter is asserted here rather than assumed.
    let entries = vec![
        member("A", &["A", "B"], DefinitionSafety::Unsafe),
        member("B", &["A", "B"], DefinitionSafety::Unsafe),
    ];
    // max_block_members = 1, everything else unlimited: the meter is the only
    // variable, so a refusal is attributable to it.
    let starved = EnvironmentBudget::new(u64::MAX, u64::MAX, u64::MAX, 1, u64::MAX, u64::MAX);
    assert!(
        !matches!(
            ConstantEnvironment::build(entries.clone(), starved),
            EnvironmentOutcome::Complete { .. }
        ),
        "max_block_members must still refuse a block that exceeds it"
    );
    // Control: the same entries under an unlimited budget build cleanly, so the
    // refusal above is the meter and not the entries.
    assert!(
        matches!(
            ConstantEnvironment::build(entries, EnvironmentBudget::unlimited()),
            EnvironmentOutcome::Complete { .. }
        ),
        "the same entries must build when the budget allows it"
    );
}

/// A member whose BODY references its peer by name — the defining shape of a
/// mutual block, and the one gii.26 could not admit.
fn recursive_member(name: &str, peer: &str, block: &[&str]) -> ConstantEntry {
    ConstantEntry::new(
        checker_name(name),
        ConstantDeclaration::definition(
            Vec::new(),
            a_type(),
            ConstantSafety::Safe,
            DefinitionBody::new(
                decoded(&Expr::const_(primary_name(peer), Vec::new())),
                ReducibilityHint::Regular(0),
                DefinitionSafety::Unsafe,
                block.iter().map(|n| checker_name(*n)).collect(),
            ),
        ),
    )
}

#[test]
fn kr977_a_genuinely_mutually_recursive_block_is_admitted() {
    // THE CELL THIS BEAD EXISTS FOR. Two members whose bodies each reference the
    // other. Under gii.26 this failed on UnknownConstant for the peer, because
    // members were admitted independently against an environment that did not
    // contain them — so the shape rules gated an admission that could not happen.
    //
    // Each member's declared type is `Sort 0` and each body is the peer constant,
    // whose predeclared type is `Sort 0`, so the bodies type-check against the
    // peers' DECLARED types rather than against their bodies.
    let block = vec![
        recursive_member("A", "B", &["A", "B"]),
        recursive_member("B", "A", &["A", "B"]),
    ];
    match admit_block(&nat_environment(), &block, AdmissionBudget::unlimited()) {
        BlockVerdict::Admitted(admission) => {
            assert_eq!(admission.members(), &[checker_name("A"), checker_name("B")]);
            assert_eq!(admission.ground(), AdmissionGround::UnsafeQuarantine);
        }
        other => panic!(
            "a mutually-recursive block must be ADMITTED once its peers are \
             predeclared; this is the case gii.26 could not reach: {other:?}"
        ),
    }
}

#[test]
fn kr977_predeclaration_leaves_kr970_unweakened_in_both_directions() {
    // Predeclaring the whole block INCLUDING self would put every member in its
    // own environment, and KR-970 would refuse each one for colliding with
    // itself. Excluding self is what keeps the rule intact — and a cell covering
    // only that direction would also pass against an implementation that had
    // simply DELETED KR-970, which is why both directions are here.
    let block = vec![
        recursive_member("A", "B", &["A", "B"]),
        recursive_member("B", "A", &["A", "B"]),
    ];

    // Direction 1: a member is NOT refused for colliding with its own
    // predeclaration.
    assert!(
        admit_block(&nat_environment(), &block, AdmissionBudget::unlimited()).is_admitted(),
        "a member must not collide with its own predeclared header"
    );

    // Direction 2: KR-970 still fires. `A` already exists in the base
    // environment, so the block must be refused naming it.
    let occupied = environment_of(vec![
        ConstantEntry::new(
            checker_name("Nat"),
            header(
                Vec::new(),
                a_type(),
                ConstantKind::Inductive,
                ConstantSafety::Safe,
            ),
        ),
        axiom("A"),
    ]);
    match admit_block(&occupied, &block, AdmissionBudget::unlimited()) {
        BlockVerdict::MemberRejected { member, rejection } => {
            assert_eq!(member, checker_name("A"));
            assert!(
                matches!(*rejection, AdmissionRejection::NameAlreadyDeclared { .. }),
                "KR-970 must still refuse a member whose name is already taken in the \
                 BASE environment, got {rejection:?}"
            );
        }
        other => panic!("KR-970 must still fire through predeclaration, got {other:?}"),
    }
}

#[test]
fn kr977_a_predeclared_peer_carries_no_body_so_it_cannot_be_unfolded() {
    // Predeclaration exposes TYPES, not definitions. A peer is built with
    // `ConstantDeclaration::header`, which hardcodes an absent body, so nothing
    // can delta-unfold a peer while checking against it.
    //
    // Measured through the same predicate the reduction path uses rather than
    // asserted about the code: `is_delta_unfoldable` is `delta_body().is_some()`,
    // and a header-built peer has no body at all.
    let peer = recursive_member("B", "A", &["A", "B"]);
    let declaration = peer.declaration();
    let predeclared = ConstantDeclaration::header(
        declaration.level_parameters().to_vec(),
        declaration.type_().clone(),
        declaration.kind(),
        declaration.safety(),
    );
    assert!(
        predeclared.definition_body().is_none(),
        "a predeclared peer must carry NO body"
    );
    assert!(
        !predeclared.is_delta_unfoldable(),
        "a predeclared peer must not be delta-unfoldable"
    );

    // Anti-vacuity: the ORIGINAL declaration does have a body, so the assertions
    // above are about predeclaration and not about this declaration being empty.
    assert!(
        declaration.definition_body().is_some(),
        "the original member must have a body, or the assertions above are vacuous"
    );
}

#[test]
fn kr977_a_collision_on_any_member_is_kr970_on_that_member_not_a_fault_on_another() {
    // Found by a gut mutant, not by reading. Predeclaring member i's peers puts
    // those names into an environment that already holds the base, so a member
    // colliding with the base created a duplicate while checking a DIFFERENT
    // member — and the collision surfaced as PredeclarationUnbuildable blaming
    // the wrong member: an internal fault for what is plainly untrusted input.
    //
    // The SECOND member is the colliding one deliberately. With the first member
    // colliding, the old code happened to report KR-970 correctly, so a cell
    // built that way would have passed against the defect.
    let occupied = environment_of(vec![
        ConstantEntry::new(
            checker_name("Nat"),
            header(
                Vec::new(),
                a_type(),
                ConstantKind::Inductive,
                ConstantSafety::Safe,
            ),
        ),
        axiom("B"),
    ]);
    let block = vec![
        recursive_member("A", "B", &["A", "B"]),
        recursive_member("B", "A", &["A", "B"]),
    ];
    match admit_block(&occupied, &block, AdmissionBudget::unlimited()) {
        BlockVerdict::MemberRejected { member, rejection } => {
            assert_eq!(
                member,
                checker_name("B"),
                "the rejection must name the member that actually collides"
            );
            assert!(
                matches!(*rejection, AdmissionRejection::NameAlreadyDeclared { .. }),
                "a collision is KR-970, never an internal fault, got {rejection:?}"
            );
        }
        other => panic!("expected KR-970 on the colliding member, got {other:?}"),
    }
}

// ---------------------------------------------------------------- KR-978

#[test]
fn kr978_the_environment_does_not_require_a_verdict() {
    // KR-978, satisfied INVERTED from the kernel's. There, the door is guarded:
    // the environment extends only through `check`. Here there is no door at
    // all, deliberately — FL-INV-02 forbids this crate from being a second
    // admission authority, so `ConstantEnvironment::build` takes declarations and
    // a budget and nothing this module produces.
    //
    // BOTH halves are asserted. A cell showing only that `build` accepts a
    // declaration would pass against a crate where nothing is ever rejected.
    let environment = nat_environment();
    let refused = ConstantEntry::new(
        checker_name("D"),
        header(
            Vec::new(),
            not_a_type(), // `7`, whose type is Nat — not a sort
            ConstantKind::Axiom,
            ConstantSafety::Safe,
        ),
    );

    // Half 1: this checker REJECTS it.
    assert!(
        matches!(
            admit(&environment, &refused, AdmissionBudget::unlimited()),
            Verdict::Rejected(AdmissionRejection::DeclaredTypeIsNotASort { .. })
        ),
        "the declaration must actually be rejected, or half 2 proves nothing"
    );

    // Half 2: an environment containing it builds anyway. The checker is
    // ADVISORY. If this ever fails, `build` has grown a verdict requirement and
    // fln-checker has become an alternative admission authority — which reads
    // like tightening a safety property and is FL-INV-02's exact prohibition.
    match ConstantEnvironment::build(vec![refused], EnvironmentBudget::unlimited()) {
        EnvironmentOutcome::Complete { environment, .. } => {
            assert_eq!(
                environment.len(),
                1,
                "the rejected declaration is in the environment; this crate gates nothing"
            );
        }
        other => panic!(
            "building an environment must not consult a verdict -- if this now \
             refuses, fln-checker has become an admission authority: {other:?}"
        ),
    }
}

/// Needles assembled from parts so this scanner's own source cannot satisfy it.
fn admission_type_needles() -> Vec<String> {
    let prefix = String::from("Admis") + "sion";
    vec![
        prefix.clone(),
        String::from("Ver") + "dict",
        String::from("admit") + "_with",
    ]
}

fn admission_type_hits(source: &str) -> Vec<String> {
    let mut hits = Vec::new();
    for line in source.lines() {
        let code = match line.find("//") {
            Some(at) => &line[..at],
            None => line,
        };
        for needle in admission_type_needles() {
            if code.contains(&needle) {
                hits.push(format!("{needle} :: {}", code.trim()));
            }
        }
    }
    hits
}

#[test]
fn kr978_the_environment_module_names_no_admission_type() {
    // The structural half, derived from the file rather than asserted. If
    // `environment.rs` ever names a verdict type, the separation this crate is
    // shaped around has started to erode, and it will erode by looking like an
    // improvement.
    let source =
        std::fs::read_to_string(workspace_root().join("crates/fln-checker/src/environment.rs"))
            .expect("the environment module is readable");
    let hits = admission_type_hits(&source);
    assert!(
        hits.is_empty(),
        "environment.rs must name no admission type -- FL-INV-02 keeps the \
         environment independent of any verdict: {hits:?}"
    );

    // The scan must be shown CAPABLE of firing, or its empty result is vacuous.
    let decoy = admission_type_needles()
        .iter()
        .map(|needle| format!("    fn gate(v: {needle}) {{}}\n"))
        .collect::<String>();
    assert_eq!(
        admission_type_hits(&decoy).len(),
        admission_type_needles().len(),
        "the scan did not fire on a planted decoy, so its clean result means nothing"
    );

    // And prose must not be scored, or the guard reddens on a doc comment.
    let commented = admission_type_needles()
        .iter()
        .map(|needle| format!("    // this module never mentions {needle}\n"))
        .collect::<String>();
    assert!(
        admission_type_hits(&commented).is_empty(),
        "a comment naming an admission type must not be scored as a use"
    );
}

#[test]
fn kr978_the_module_doc_still_records_why_there_is_no_door() {
    // A property whose reason is unwritten is one the next reader repairs. The
    // inversion -- guarded in K1, absent here, and BOTH correct -- is exactly
    // what will not survive a context restart unless it is held.
    let source = std::fs::read_to_string(workspace_root().join("crates/fln-checker/src/admit.rs"))
        .expect("the admission module is readable");
    for required in [
        "there is no door",
        "would become a second admission authority",
        "satisfies it INVERTED",
    ] {
        assert!(
            source.contains(required),
            "admit.rs's module doc must keep recording WHY there is no gate; \
             missing: {required:?}"
        );
    }
}

#[test]
fn the_admission_module_contains_no_panicking_construct() {
    // Three closed rows CLAIM this -- "src/admit.rs contains zero panicking
    // constructs, counted independently" -- and until now nothing enforced it.
    // A claim counted by hand at close time is a claim with no producer: it
    // cannot fail when it stops being true.
    //
    // FL-INV-07's reason for caring: a panic in this module would be an
    // invariant failure surfacing as a process abort rather than as a typed
    // Inconclusive or InternalFault, which is precisely the outcome the five-arm
    // verdict exists to make impossible.
    let source = std::fs::read_to_string(workspace_root().join("crates/fln-checker/src/admit.rs"))
        .expect("the admission module is readable");
    let mut sites = Vec::new();
    for (number, line) in source.lines().enumerate() {
        // Strip the comment tail: this module's doc comments discuss panics and
        // FL-INV-07 at length, and scoring prose would make the guard redden on
        // its own explanation.
        let code = match line.find("//") {
            Some(at) => &line[..at],
            None => line,
        };
        for needle in [
            "panic!",
            ".unwrap()",
            ".expect(",
            "unreachable!",
            "todo!",
            "unimplemented!",
        ] {
            if code.contains(needle) {
                sites.push(format!("{}:{} {needle}", "src/admit.rs", number + 1));
            }
        }
    }
    assert!(
        sites.is_empty(),
        "the admission module must contain no panicking construct; FL-INV-07 wants a \
         typed Inconclusive or InternalFault, never an abort: {sites:?}"
    );

    // Anti-vacuity: the scan must be shown capable of finding one, or an empty
    // result means nothing. Every needle is planted and every needle must hit.
    let decoy: String = [
        "panic!",
        ".unwrap()",
        ".expect(",
        "unreachable!",
        "todo!",
        "unimplemented!",
    ]
    .iter()
    .map(|n| format!("    let x = y{n};\n"))
    .collect();
    let found = decoy
        .lines()
        .filter(|line| {
            let code = match line.find("//") {
                Some(at) => &line[..at],
                None => line,
            };
            [
                "panic!",
                ".unwrap()",
                ".expect(",
                "unreachable!",
                "todo!",
                "unimplemented!",
            ]
            .iter()
            .any(|n| code.contains(n))
        })
        .count();
    assert_eq!(
        found, 6,
        "the panicking-construct scan did not fire on a planted decoy, so its clean \
         result on the real module is vacuous"
    );
}
