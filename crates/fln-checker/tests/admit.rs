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
    QuotientVerdict, Verdict, admit, admit_block, admit_inductive, admit_inductive_with,
    admit_quotient, admit_quotient_with, admit_with,
};
use fln_checker::defeq::{DefEqBudget, QuickDefEqBudget, QuickDefEqLimit, QuickDefEqStop};
use fln_checker::environment::{
    ConstantDeclaration, ConstantEntry, ConstantEnvironment, ConstantKind, ConstantSafety,
    ConstructorDeclaration, DefinitionBody, DefinitionSafety, EnvironmentBudget,
    EnvironmentOutcome, InductiveDeclaration, QuotientKind, RecursorDeclaration, RecursorRule,
    ReducibilityHint,
};
use fln_checker::infer::InferenceBudget;
use fln_checker::term::{TermBudget, TermOutcome, inspect};
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

fn quotient_entries_with_lift_relation_binder(
    lift_relation_binder: BinderInfo,
) -> Vec<ConstantEntry> {
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
            lift_relation_binder,
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

fn quotient_entries() -> Vec<ConstantEntry> {
    quotient_entries_with_lift_relation_binder(BinderInfo::Implicit)
}

fn enumeration_entries_with_binders(
    recursor_motive_binder: BinderInfo,
    rule_motive_binder: BinderInfo,
) -> Vec<ConstantEntry> {
    let color = primary_name("Color");
    let red = Name::str(color.clone(), "red");
    let blue = Name::str(color.clone(), "blue");
    let u_name = primary_name("u");
    let u = Level::param(u_name.clone());
    let color_expr = || Expr::const_(color.clone(), Vec::new());
    let red_expr = || Expr::const_(red.clone(), Vec::new());
    let blue_expr = || Expr::const_(blue.clone(), Vec::new());
    let bv = |index| Expr::bvar(index).expect("packs");
    let motive_type = primary_pi(
        "t",
        BinderInfo::Default,
        color_expr(),
        Expr::sort(u.clone()),
    );
    let recursor_type = primary_pi(
        "motive",
        recursor_motive_binder,
        motive_type.clone(),
        primary_pi(
            "red",
            BinderInfo::Default,
            Expr::app(bv(0), red_expr()),
            primary_pi(
                "blue",
                BinderInfo::Default,
                Expr::app(bv(1), blue_expr()),
                primary_pi(
                    "t",
                    BinderInfo::Default,
                    color_expr(),
                    Expr::app(bv(3), bv(0)),
                ),
            ),
        ),
    );
    let rule_rhs = |selected: u32| {
        Expr::lam(
            primary_name("motive"),
            motive_type.clone(),
            Expr::lam(
                primary_name("red"),
                Expr::app(bv(0), red_expr()),
                Expr::lam(
                    primary_name("blue"),
                    Expr::app(bv(1), blue_expr()),
                    bv(selected),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            rule_motive_binder,
        )
    };
    vec![
        ConstantEntry::new(
            checker_name("Color"),
            ConstantDeclaration::inductive(
                Vec::new(),
                decoded(&Expr::sort(Level::one())),
                ConstantSafety::Safe,
                InductiveDeclaration::new(
                    0,
                    0,
                    vec![checker_name("Color")],
                    vec![
                        checker_qualified(&["Color", "red"]),
                        checker_qualified(&["Color", "blue"]),
                    ],
                    0,
                    false,
                    false,
                ),
            ),
        ),
        ConstantEntry::new(
            checker_qualified(&["Color", "red"]),
            ConstantDeclaration::constructor(
                Vec::new(),
                decoded(&color_expr()),
                ConstantSafety::Safe,
                ConstructorDeclaration::new(checker_name("Color"), 0, 0, 0),
            ),
        ),
        ConstantEntry::new(
            checker_qualified(&["Color", "blue"]),
            ConstantDeclaration::constructor(
                Vec::new(),
                decoded(&color_expr()),
                ConstantSafety::Safe,
                ConstructorDeclaration::new(checker_name("Color"), 1, 0, 0),
            ),
        ),
        ConstantEntry::new(
            checker_qualified(&["Color", "rec"]),
            ConstantDeclaration::recursor(
                vec![checker_name("u")],
                decoded(&recursor_type),
                ConstantSafety::Safe,
                RecursorDeclaration::new(
                    vec![checker_name("Color")],
                    0,
                    0,
                    1,
                    2,
                    vec![
                        RecursorRule::new(
                            checker_qualified(&["Color", "red"]),
                            0,
                            decoded(&rule_rhs(1)),
                        ),
                        RecursorRule::new(
                            checker_qualified(&["Color", "blue"]),
                            0,
                            decoded(&rule_rhs(0)),
                        ),
                    ],
                    false,
                ),
            ),
        ),
    ]
}

fn enumeration_entries(recursor_motive_binder: BinderInfo) -> Vec<ConstantEntry> {
    enumeration_entries_with_binders(recursor_motive_binder, BinderInfo::Default)
}

fn dependent_field_inductive_entries() -> Vec<ConstantEntry> {
    let witness = primary_name("Witness");
    let make = Name::str(witness.clone(), "mk");
    let u_name = primary_name("u");
    let u = Level::param(u_name.clone());
    let witness_expr = || Expr::const_(witness.clone(), Vec::new());
    let make_expr = || Expr::const_(make.clone(), Vec::new());
    let bv = |index| Expr::bvar(index).expect("packs");
    let constructor_type = primary_pi(
        "proposition",
        BinderInfo::Default,
        Expr::sort(Level::zero()),
        primary_pi("proof", BinderInfo::Default, bv(0), witness_expr()),
    );
    let motive_type = primary_pi(
        "t",
        BinderInfo::Default,
        witness_expr(),
        Expr::sort(u.clone()),
    );
    let minor_type = primary_pi(
        "proposition",
        BinderInfo::Default,
        Expr::sort(Level::zero()),
        primary_pi(
            "proof",
            BinderInfo::Default,
            bv(0),
            Expr::app(bv(2), Expr::app(Expr::app(make_expr(), bv(1)), bv(0))),
        ),
    );
    let recursor_type = primary_pi(
        "motive",
        BinderInfo::Implicit,
        motive_type.clone(),
        primary_pi(
            "minor",
            BinderInfo::Default,
            minor_type.clone(),
            primary_pi(
                "t",
                BinderInfo::Default,
                witness_expr(),
                Expr::app(bv(2), bv(0)),
            ),
        ),
    );
    let rule_rhs = Expr::lam(
        primary_name("motive"),
        motive_type,
        Expr::lam(
            primary_name("minor"),
            minor_type,
            Expr::lam(
                primary_name("proposition"),
                Expr::sort(Level::zero()),
                Expr::lam(
                    primary_name("proof"),
                    bv(0),
                    Expr::app(Expr::app(bv(2), bv(1)), bv(0)),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    vec![
        ConstantEntry::new(
            checker_name("Witness"),
            ConstantDeclaration::inductive(
                Vec::new(),
                decoded(&Expr::sort(Level::one())),
                ConstantSafety::Safe,
                InductiveDeclaration::new(
                    0,
                    0,
                    vec![checker_name("Witness")],
                    vec![checker_qualified(&["Witness", "mk"])],
                    0,
                    false,
                    false,
                ),
            ),
        ),
        ConstantEntry::new(
            checker_qualified(&["Witness", "mk"]),
            ConstantDeclaration::constructor(
                Vec::new(),
                decoded(&constructor_type),
                ConstantSafety::Safe,
                ConstructorDeclaration::new(checker_name("Witness"), 0, 0, 2),
            ),
        ),
        ConstantEntry::new(
            checker_qualified(&["Witness", "rec"]),
            ConstantDeclaration::recursor(
                vec![checker_name("u")],
                decoded(&recursor_type),
                ConstantSafety::Safe,
                RecursorDeclaration::new(
                    vec![checker_name("Witness")],
                    0,
                    0,
                    1,
                    1,
                    vec![RecursorRule::new(
                        checker_qualified(&["Witness", "mk"]),
                        2,
                        decoded(&rule_rhs),
                    )],
                    false,
                ),
            ),
        ),
    ]
}

/// The bounded Init.Nat shape: one nullary constructor and one constructor
/// carrying a direct self field. Its recursor's successor minor contains the
/// induction hypothesis, and its successor rule re-enters `Nat.rec`.
fn nat_entries() -> Vec<ConstantEntry> {
    let nat = checker_name("Nat");
    let zero = checker_qualified(&["Nat", "zero"]);
    let succ = checker_qualified(&["Nat", "succ"]);
    let rec = checker_qualified(&["Nat", "rec"]);
    let u_name = checker_name("u");
    let u = Level::param(primary_name("u"));
    let nat_expr = || Expr::const_(primary_name("Nat"), Vec::new());
    let zero_expr = || Expr::const_(Name::from_components(["Nat", "zero"]), Vec::new());
    let succ_expr = || Expr::const_(Name::from_components(["Nat", "succ"]), Vec::new());
    let bv = |index| Expr::bvar(index).expect("packs");
    let motive_type = primary_pi("t", BinderInfo::Default, nat_expr(), Expr::sort(u.clone()));
    let succ_minor_type = |motive_index: u32| {
        primary_pi(
            "n",
            BinderInfo::Default,
            nat_expr(),
            primary_pi(
                "n_ih",
                BinderInfo::Default,
                Expr::app(bv(motive_index + 1), bv(0)),
                Expr::app(bv(motive_index + 2), Expr::app(succ_expr(), bv(1))),
            ),
        )
    };
    let zero_minor_type = Expr::app(bv(0), zero_expr());
    let recursor_type = primary_pi(
        "motive",
        BinderInfo::Implicit,
        motive_type.clone(),
        primary_pi(
            "zero",
            BinderInfo::Default,
            zero_minor_type.clone(),
            primary_pi(
                "succ",
                BinderInfo::Default,
                succ_minor_type(1),
                primary_pi(
                    "t",
                    BinderInfo::Default,
                    nat_expr(),
                    Expr::app(bv(3), bv(0)),
                ),
            ),
        ),
    );
    let zero_rule_rhs = Expr::lam(
        primary_name("motive"),
        motive_type.clone(),
        Expr::lam(
            primary_name("zero"),
            zero_minor_type,
            Expr::lam(
                primary_name("succ"),
                succ_minor_type(1),
                bv(1),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let successor_rule_rhs = {
        let mut recursive_call = Expr::const_(Name::from_components(["Nat", "rec"]), vec![u]);
        for argument in [bv(3), bv(2), bv(1), bv(0)] {
            recursive_call = Expr::app(recursive_call, argument);
        }
        Expr::lam(
            primary_name("motive"),
            motive_type.clone(),
            Expr::lam(
                primary_name("zero"),
                Expr::app(bv(0), zero_expr()),
                Expr::lam(
                    primary_name("succ"),
                    succ_minor_type(1),
                    Expr::lam(
                        primary_name("n"),
                        nat_expr(),
                        Expr::app(Expr::app(bv(1), bv(0)), recursive_call),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        )
    };
    vec![
        ConstantEntry::new(
            nat.clone(),
            ConstantDeclaration::inductive(
                Vec::new(),
                decoded(&Expr::sort(Level::one())),
                ConstantSafety::Safe,
                InductiveDeclaration::new(
                    0,
                    0,
                    vec![nat.clone()],
                    vec![zero.clone(), succ.clone()],
                    0,
                    true,
                    false,
                ),
            ),
        ),
        ConstantEntry::new(
            zero.clone(),
            ConstantDeclaration::constructor(
                Vec::new(),
                decoded(&nat_expr()),
                ConstantSafety::Safe,
                ConstructorDeclaration::new(nat.clone(), 0, 0, 0),
            ),
        ),
        ConstantEntry::new(
            succ.clone(),
            ConstantDeclaration::constructor(
                Vec::new(),
                decoded(&primary_pi(
                    "n",
                    BinderInfo::Default,
                    nat_expr(),
                    nat_expr(),
                )),
                ConstantSafety::Safe,
                ConstructorDeclaration::new(nat.clone(), 1, 0, 1),
            ),
        ),
        ConstantEntry::new(
            rec,
            ConstantDeclaration::recursor(
                vec![u_name],
                decoded(&recursor_type),
                ConstantSafety::Safe,
                RecursorDeclaration::new(
                    vec![nat],
                    0,
                    0,
                    1,
                    2,
                    vec![
                        RecursorRule::new(zero, 0, decoded(&zero_rule_rhs)),
                        RecursorRule::new(succ, 1, decoded(&successor_rule_rhs)),
                    ],
                    false,
                ),
            ),
        ),
    ]
}

/// The universe-polymorphic `Init.Option` family. This fixture carries both
/// the family universe and the recursor's independent motive universe, so a
/// success requires the checker to reconstruct their distinct roles.
fn init_option_entries() -> Vec<ConstantEntry> {
    let option = checker_name("Option");
    let none = checker_qualified(&["Option", "none"]);
    let some = checker_qualified(&["Option", "some"]);
    let rec = checker_qualified(&["Option", "rec"]);
    let u_name = checker_name("u");
    let v_name = checker_name("v");
    let u = Level::param(primary_name("u"));
    let v = Level::param(primary_name("v"));
    let parameter_type = || Expr::sort(Level::succ(u.clone()).expect("universe successor packs"));
    let option_expr = |parameter: Expr| {
        Expr::app(
            Expr::const_(primary_name("Option"), vec![u.clone()]),
            parameter,
        )
    };
    let none_expr = |parameter: Expr| {
        Expr::app(
            Expr::const_(Name::from_components(["Option", "none"]), vec![u.clone()]),
            parameter,
        )
    };
    let some_expr = |parameter: Expr, value: Expr| {
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_components(["Option", "some"]), vec![u.clone()]),
                parameter,
            ),
            value,
        )
    };
    let bv = |index| Expr::bvar(index).expect("packs");
    let motive_type = || {
        primary_pi(
            "t",
            BinderInfo::Default,
            option_expr(bv(0)),
            Expr::sort(v.clone()),
        )
    };
    let none_minor_type = || Expr::app(bv(0), none_expr(bv(1)));
    let some_minor_type = || {
        primary_pi(
            "value",
            BinderInfo::Default,
            bv(2),
            Expr::app(bv(2), some_expr(bv(3), bv(0))),
        )
    };
    let recursor_type = primary_pi(
        "α",
        BinderInfo::Implicit,
        parameter_type(),
        primary_pi(
            "motive",
            BinderInfo::Implicit,
            motive_type(),
            primary_pi(
                "none",
                BinderInfo::Default,
                none_minor_type(),
                primary_pi(
                    "some",
                    BinderInfo::Default,
                    some_minor_type(),
                    primary_pi(
                        "t",
                        BinderInfo::Default,
                        option_expr(bv(3)),
                        Expr::app(bv(3), bv(0)),
                    ),
                ),
            ),
        ),
    );
    let none_rule_rhs = Expr::lam(
        primary_name("α"),
        parameter_type(),
        Expr::lam(
            primary_name("motive"),
            motive_type(),
            Expr::lam(
                primary_name("none"),
                none_minor_type(),
                Expr::lam(
                    primary_name("some"),
                    some_minor_type(),
                    bv(1),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let some_rule_rhs = Expr::lam(
        primary_name("α"),
        parameter_type(),
        Expr::lam(
            primary_name("motive"),
            motive_type(),
            Expr::lam(
                primary_name("none"),
                none_minor_type(),
                Expr::lam(
                    primary_name("some"),
                    some_minor_type(),
                    Expr::lam(
                        primary_name("value"),
                        bv(2),
                        Expr::app(bv(1), bv(0)),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    vec![
        ConstantEntry::new(
            option.clone(),
            ConstantDeclaration::inductive(
                vec![u_name.clone()],
                decoded(&primary_pi(
                    "α",
                    BinderInfo::Default,
                    parameter_type(),
                    parameter_type(),
                )),
                ConstantSafety::Safe,
                InductiveDeclaration::new(
                    1,
                    0,
                    vec![option.clone()],
                    vec![none.clone(), some.clone()],
                    0,
                    false,
                    false,
                ),
            ),
        ),
        ConstantEntry::new(
            none.clone(),
            ConstantDeclaration::constructor(
                vec![u_name.clone()],
                decoded(&primary_pi(
                    "α",
                    BinderInfo::Default,
                    parameter_type(),
                    option_expr(bv(0)),
                )),
                ConstantSafety::Safe,
                ConstructorDeclaration::new(option.clone(), 0, 1, 0),
            ),
        ),
        ConstantEntry::new(
            some.clone(),
            ConstantDeclaration::constructor(
                vec![u_name.clone()],
                decoded(&primary_pi(
                    "α",
                    BinderInfo::Default,
                    parameter_type(),
                    primary_pi("value", BinderInfo::Default, bv(0), option_expr(bv(1))),
                )),
                ConstantSafety::Safe,
                ConstructorDeclaration::new(option.clone(), 1, 1, 1),
            ),
        ),
        ConstantEntry::new(
            rec,
            ConstantDeclaration::recursor(
                vec![v_name, u_name],
                decoded(&recursor_type),
                ConstantSafety::Safe,
                RecursorDeclaration::new(
                    vec![option],
                    1,
                    0,
                    1,
                    2,
                    vec![
                        RecursorRule::new(none, 0, decoded(&none_rule_rhs)),
                        RecursorRule::new(some, 1, decoded(&some_rule_rhs)),
                    ],
                    false,
                ),
            ),
        ),
    ]
}

/// `Init.List.{u}` exercises a recursive, universe-polymorphic parameterized
/// family. The `cons` minor premise must carry the recursive hypothesis and
/// the second rule must rebuild the recursive recursor call.
fn init_list_entries() -> Vec<ConstantEntry> {
    let list = checker_name("List");
    let nil = checker_qualified(&["List", "nil"]);
    let cons = checker_qualified(&["List", "cons"]);
    let rec = checker_qualified(&["List", "rec"]);
    let u_name = checker_name("u");
    let v_name = checker_name("v");
    let u = Level::param(primary_name("u"));
    let v = Level::param(primary_name("v"));
    let parameter_type = || Expr::sort(Level::succ(u.clone()).expect("universe successor packs"));
    let list_expr = |parameter: Expr| {
        Expr::app(
            Expr::const_(primary_name("List"), vec![u.clone()]),
            parameter,
        )
    };
    let nil_expr = |parameter: Expr| {
        Expr::app(
            Expr::const_(Name::from_components(["List", "nil"]), vec![u.clone()]),
            parameter,
        )
    };
    let cons_expr = |parameter: Expr, head: Expr, tail: Expr| {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_components(["List", "cons"]), vec![u.clone()]),
                    parameter,
                ),
                head,
            ),
            tail,
        )
    };
    let bv = |index| Expr::bvar(index).expect("packs");
    let motive_type = || {
        primary_pi(
            "t",
            BinderInfo::Default,
            list_expr(bv(0)),
            Expr::sort(v.clone()),
        )
    };
    let nil_minor_type = || Expr::app(bv(0), nil_expr(bv(1)));
    let cons_minor_type = || {
        primary_pi(
            "head",
            BinderInfo::Default,
            bv(2),
            primary_pi(
                "tail",
                BinderInfo::Default,
                list_expr(bv(3)),
                primary_pi(
                    "tail_ih",
                    BinderInfo::Default,
                    Expr::app(bv(3), bv(0)),
                    Expr::app(bv(4), cons_expr(bv(5), bv(2), bv(1))),
                ),
            ),
        )
    };
    let recursor_type = primary_pi(
        "α",
        BinderInfo::Implicit,
        parameter_type(),
        primary_pi(
            "motive",
            BinderInfo::Implicit,
            motive_type(),
            primary_pi(
                "nil",
                BinderInfo::Default,
                nil_minor_type(),
                primary_pi(
                    "cons",
                    BinderInfo::Default,
                    cons_minor_type(),
                    primary_pi(
                        "t",
                        BinderInfo::Default,
                        list_expr(bv(3)),
                        Expr::app(bv(3), bv(0)),
                    ),
                ),
            ),
        ),
    );
    let nil_rule_rhs = Expr::lam(
        primary_name("α"),
        parameter_type(),
        Expr::lam(
            primary_name("motive"),
            motive_type(),
            Expr::lam(
                primary_name("nil"),
                nil_minor_type(),
                Expr::lam(
                    primary_name("cons"),
                    cons_minor_type(),
                    bv(1),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let recursive_call = {
        let recursor = Expr::const_(
            Name::from_components(["List", "rec"]),
            vec![v.clone(), u.clone()],
        );
        [bv(5), bv(4), bv(3), bv(2), bv(0)]
            .into_iter()
            .fold(recursor, Expr::app)
    };
    let cons_rule_rhs = Expr::lam(
        primary_name("α"),
        parameter_type(),
        Expr::lam(
            primary_name("motive"),
            motive_type(),
            Expr::lam(
                primary_name("nil"),
                nil_minor_type(),
                Expr::lam(
                    primary_name("cons"),
                    cons_minor_type(),
                    Expr::lam(
                        primary_name("head"),
                        bv(3),
                        Expr::lam(
                            primary_name("tail"),
                            list_expr(bv(4)),
                            Expr::app(
                                Expr::app(Expr::app(bv(2), bv(1)), bv(0)),
                                recursive_call,
                            ),
                            BinderInfo::Default,
                        ),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    vec![
        ConstantEntry::new(
            list.clone(),
            ConstantDeclaration::inductive(
                vec![u_name.clone()],
                decoded(&primary_pi(
                    "α",
                    BinderInfo::Default,
                    parameter_type(),
                    parameter_type(),
                )),
                ConstantSafety::Safe,
                InductiveDeclaration::new(
                    1,
                    0,
                    vec![list.clone()],
                    vec![nil.clone(), cons.clone()],
                    0,
                    true,
                    false,
                ),
            ),
        ),
        ConstantEntry::new(
            nil.clone(),
            ConstantDeclaration::constructor(
                vec![u_name.clone()],
                decoded(&primary_pi(
                    "α",
                    BinderInfo::Default,
                    parameter_type(),
                    list_expr(bv(0)),
                )),
                ConstantSafety::Safe,
                ConstructorDeclaration::new(list.clone(), 0, 1, 0),
            ),
        ),
        ConstantEntry::new(
            cons.clone(),
            ConstantDeclaration::constructor(
                vec![u_name.clone()],
                decoded(&primary_pi(
                    "α",
                    BinderInfo::Default,
                    parameter_type(),
                    primary_pi(
                        "head",
                        BinderInfo::Default,
                        bv(0),
                        primary_pi(
                            "tail",
                            BinderInfo::Default,
                            list_expr(bv(1)),
                            list_expr(bv(2)),
                        ),
                    ),
                )),
                ConstantSafety::Safe,
                ConstructorDeclaration::new(list.clone(), 1, 1, 2),
            ),
        ),
        ConstantEntry::new(
            rec,
            ConstantDeclaration::recursor(
                vec![v_name, u_name],
                decoded(&recursor_type),
                ConstantSafety::Safe,
                RecursorDeclaration::new(
                    vec![list],
                    1,
                    0,
                    1,
                    2,
                    vec![
                        RecursorRule::new(nil, 0, decoded(&nil_rule_rhs)),
                        RecursorRule::new(cons, 2, decoded(&cons_rule_rhs)),
                    ],
                    false,
                ),
            ),
        ),
    ]
}

/// `Init.Empty` has no constructor rows, but its recursor still must be
/// reconstructed rather than treated as an empty success.
fn init_empty_entries() -> Vec<ConstantEntry> {
    let empty = checker_name("Empty");
    let rec = checker_qualified(&["Empty", "rec"]);
    let u_name = checker_name("u");
    let u = Level::param(primary_name("u"));
    let empty_expr = || Expr::const_(primary_name("Empty"), Vec::new());
    let bv = |index| Expr::bvar(index).expect("packs");
    let motive_type = primary_pi("t", BinderInfo::Default, empty_expr(), Expr::sort(u));
    let recursor_type = primary_pi(
        "motive",
        BinderInfo::Implicit,
        motive_type.clone(),
        primary_pi(
            "t",
            BinderInfo::Default,
            empty_expr(),
            Expr::app(bv(1), bv(0)),
        ),
    );
    vec![
        ConstantEntry::new(
            empty.clone(),
            ConstantDeclaration::inductive(
                Vec::new(),
                decoded(&Expr::sort(Level::one())),
                ConstantSafety::Safe,
                InductiveDeclaration::new(0, 0, vec![empty.clone()], Vec::new(), 0, false, false),
            ),
        ),
        ConstantEntry::new(
            rec,
            ConstantDeclaration::recursor(
                vec![u_name],
                decoded(&recursor_type),
                ConstantSafety::Safe,
                RecursorDeclaration::new(vec![empty], 0, 0, 1, 0, Vec::new(), false),
            ),
        ),
    ]
}

fn init_false_entries() -> Vec<ConstantEntry> {
    let false_name = checker_name("False");
    let rec = checker_qualified(&["False", "rec"]);
    let u_name = checker_name("u");
    let u = Level::param(primary_name("u"));
    let false_expr = || Expr::const_(primary_name("False"), Vec::new());
    let bv = |index| Expr::bvar(index).expect("packs");
    let motive = primary_pi("t", BinderInfo::Default, false_expr(), Expr::sort(u));
    let rec_type = primary_pi("motive", BinderInfo::Implicit, motive, primary_pi(
        "t", BinderInfo::Default, false_expr(), Expr::app(bv(1), bv(0)),
    ));
    vec![
        ConstantEntry::new(false_name.clone(), ConstantDeclaration::inductive(
            Vec::new(), decoded(&Expr::sort(Level::zero())), ConstantSafety::Safe,
            InductiveDeclaration::new(0, 0, vec![false_name.clone()], Vec::new(), 0, false, false),
        )),
        ConstantEntry::new(rec, ConstantDeclaration::recursor(
            vec![u_name], decoded(&rec_type), ConstantSafety::Safe,
            RecursorDeclaration::new(vec![false_name], 0, 0, 1, 0, Vec::new(), false),
        )),
    ]
}

/// `Init.PEmpty.{u}` keeps its family universe and eliminator universe
/// separate. The exact recursor is what prevents an empty row set from being a
/// vacuous admission.
fn init_pempty_entries() -> Vec<ConstantEntry> {
    let pempty = checker_name("PEmpty");
    let rec = checker_qualified(&["PEmpty", "rec"]);
    let u_name = checker_name("u");
    let v_name = checker_name("v");
    let u = Level::param(primary_name("u"));
    let v = Level::param(primary_name("v"));
    let pempty_expr = || Expr::const_(primary_name("PEmpty"), vec![u.clone()]);
    let bv = |index| Expr::bvar(index).expect("packs");
    let motive_type = primary_pi("t", BinderInfo::Default, pempty_expr(), Expr::sort(v));
    let recursor_type = primary_pi(
        "motive",
        BinderInfo::Implicit,
        motive_type.clone(),
        primary_pi(
            "t",
            BinderInfo::Default,
            pempty_expr(),
            Expr::app(bv(1), bv(0)),
        ),
    );
    vec![
        ConstantEntry::new(
            pempty.clone(),
            ConstantDeclaration::inductive(
                vec![u_name.clone()],
                decoded(&Expr::sort(u)),
                ConstantSafety::Safe,
                InductiveDeclaration::new(0, 0, vec![pempty.clone()], Vec::new(), 0, false, false),
            ),
        ),
        ConstantEntry::new(
            rec,
            ConstantDeclaration::recursor(
                vec![v_name, u_name],
                decoded(&recursor_type),
                ConstantSafety::Safe,
                RecursorDeclaration::new(vec![pempty], 0, 0, 1, 0, Vec::new(), false),
            ),
        ),
    ]
}

/// `Init.Or` is proposition-only, so its recursor has no universe parameters
/// and each branch carries exactly the proposition it introduces.
fn init_or_entries() -> Vec<ConstantEntry> {
    let or_name = checker_name("Or");
    let inl = checker_qualified(&["Or", "inl"]);
    let inr = checker_qualified(&["Or", "inr"]);
    let rec = checker_qualified(&["Or", "rec"]);
    let proposition = || Expr::sort(Level::zero());
    let or_expr = |left: Expr, right: Expr| {
        Expr::app(
            Expr::app(Expr::const_(primary_name("Or"), Vec::new()), left),
            right,
        )
    };
    let inl_expr = |left: Expr, right: Expr, proof: Expr| {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_components(["Or", "inl"]), Vec::new()),
                    left,
                ),
                right,
            ),
            proof,
        )
    };
    let inr_expr = |left: Expr, right: Expr, proof: Expr| {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_components(["Or", "inr"]), Vec::new()),
                    left,
                ),
                right,
            ),
            proof,
        )
    };
    let bv = |index| Expr::bvar(index).expect("packs");
    let motive_type = || {
        primary_pi(
            "t",
            BinderInfo::Default,
            or_expr(bv(1), bv(0)),
            proposition(),
        )
    };
    let inl_minor_type = || {
        primary_pi(
            "h",
            BinderInfo::Default,
            bv(2),
            Expr::app(bv(1), inl_expr(bv(3), bv(2), bv(0))),
        )
    };
    let inr_minor_type = || {
        primary_pi(
            "h",
            BinderInfo::Default,
            bv(2),
            Expr::app(bv(2), inr_expr(bv(4), bv(3), bv(0))),
        )
    };
    let recursor_type = primary_pi(
        "a",
        BinderInfo::Implicit,
        proposition(),
        primary_pi(
            "b",
            BinderInfo::Implicit,
            proposition(),
            primary_pi(
                "motive",
                BinderInfo::Implicit,
                motive_type(),
                primary_pi(
                    "inl",
                    BinderInfo::Default,
                    inl_minor_type(),
                    primary_pi(
                        "inr",
                        BinderInfo::Default,
                        inr_minor_type(),
                        primary_pi(
                            "t",
                            BinderInfo::Default,
                            or_expr(bv(4), bv(3)),
                            Expr::app(bv(3), bv(0)),
                        ),
                    ),
                ),
            ),
        ),
    );
    let inl_rule_rhs = Expr::lam(
        primary_name("a"),
        proposition(),
        Expr::lam(
            primary_name("b"),
            proposition(),
            Expr::lam(
                primary_name("motive"),
                motive_type(),
                Expr::lam(
                    primary_name("inl"),
                    inl_minor_type(),
                    Expr::lam(
                        primary_name("inr"),
                        inr_minor_type(),
                        Expr::lam(
                            primary_name("h"),
                            bv(4),
                            Expr::app(bv(2), bv(0)),
                            BinderInfo::Default,
                        ),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let inr_rule_rhs = Expr::lam(
        primary_name("a"),
        proposition(),
        Expr::lam(
            primary_name("b"),
            proposition(),
            Expr::lam(
                primary_name("motive"),
                motive_type(),
                Expr::lam(
                    primary_name("inl"),
                    inl_minor_type(),
                    Expr::lam(
                        primary_name("inr"),
                        inr_minor_type(),
                        Expr::lam(
                            primary_name("h"),
                            bv(3),
                            Expr::app(bv(1), bv(0)),
                            BinderInfo::Default,
                        ),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    vec![
        ConstantEntry::new(
            or_name.clone(),
            ConstantDeclaration::inductive(
                Vec::new(),
                decoded(&primary_pi(
                    "a",
                    BinderInfo::Default,
                    proposition(),
                    primary_pi("b", BinderInfo::Default, proposition(), proposition()),
                )),
                ConstantSafety::Safe,
                InductiveDeclaration::new(
                    2,
                    0,
                    vec![or_name.clone()],
                    vec![inl.clone(), inr.clone()],
                    0,
                    false,
                    false,
                ),
            ),
        ),
        ConstantEntry::new(
            inl.clone(),
            ConstantDeclaration::constructor(
                Vec::new(),
                decoded(&primary_pi(
                    "a",
                    BinderInfo::Default,
                    proposition(),
                    primary_pi(
                        "b",
                        BinderInfo::Default,
                        proposition(),
                        primary_pi("h", BinderInfo::Default, bv(1), or_expr(bv(2), bv(1))),
                    ),
                )),
                ConstantSafety::Safe,
                ConstructorDeclaration::new(or_name.clone(), 0, 2, 1),
            ),
        ),
        ConstantEntry::new(
            inr.clone(),
            ConstantDeclaration::constructor(
                Vec::new(),
                decoded(&primary_pi(
                    "a",
                    BinderInfo::Default,
                    proposition(),
                    primary_pi(
                        "b",
                        BinderInfo::Default,
                        proposition(),
                        primary_pi("h", BinderInfo::Default, bv(0), or_expr(bv(2), bv(1))),
                    ),
                )),
                ConstantSafety::Safe,
                ConstructorDeclaration::new(or_name.clone(), 1, 2, 1),
            ),
        ),
        ConstantEntry::new(
            rec,
            ConstantDeclaration::recursor(
                Vec::new(),
                decoded(&recursor_type),
                ConstantSafety::Safe,
                RecursorDeclaration::new(
                    vec![or_name],
                    2,
                    0,
                    1,
                    2,
                    vec![
                        RecursorRule::new(inl, 1, decoded(&inl_rule_rhs)),
                        RecursorRule::new(inr, 1, decoded(&inr_rule_rhs)),
                    ],
                    false,
                ),
            ),
        ),
    ]
}

fn init_and_entries() -> Vec<ConstantEntry> {
    let and = checker_name("And");
    let intro = checker_qualified(&["And", "intro"]);
    let rec = checker_qualified(&["And", "rec"]);
    let u_name = checker_name("u");
    let u = Level::param(primary_name("u"));
    let prop = || Expr::sort(Level::zero());
    let and_expr = |a: Expr, b: Expr| {
        Expr::app(Expr::app(Expr::const_(primary_name("And"), Vec::new()), a), b)
    };
    let intro_expr = |a: Expr, b: Expr, left: Expr, right: Expr| {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(Expr::const_(Name::from_components(["And", "intro"]), Vec::new()), a),
                    b,
                ),
                left,
            ),
            right,
        )
    };
    let bv = |index| Expr::bvar(index).expect("packs");
    let motive = || primary_pi("t", BinderInfo::Default, and_expr(bv(1), bv(0)), Expr::sort(u.clone()));
    let minor = || primary_pi(
        "left", BinderInfo::Default, bv(2),
        primary_pi(
            "right", BinderInfo::Default, bv(2),
            Expr::app(bv(2), intro_expr(bv(4), bv(3), bv(1), bv(0))),
        ),
    );
    let rec_type = primary_pi("a", BinderInfo::Implicit, prop(), primary_pi(
        "b", BinderInfo::Implicit, prop(), primary_pi(
            "motive", BinderInfo::Implicit, motive(), primary_pi(
                "intro", BinderInfo::Default, minor(), primary_pi(
                    "t", BinderInfo::Default, and_expr(bv(3), bv(2)), Expr::app(bv(2), bv(0)),
                ),
            ),
        ),
    ));
    let rhs = Expr::lam(primary_name("a"), prop(), Expr::lam(
        primary_name("b"), prop(), Expr::lam(
            primary_name("motive"), motive(), Expr::lam(
                primary_name("intro"), minor(), Expr::lam(
                    primary_name("left"), bv(3), Expr::lam(
                        primary_name("right"), bv(3),
                        Expr::app(Expr::app(bv(2), bv(1)), bv(0)), BinderInfo::Default,
                    ), BinderInfo::Default,
                ), BinderInfo::Default,
            ), BinderInfo::Default,
        ), BinderInfo::Default,
    ), BinderInfo::Default);
    vec![
        ConstantEntry::new(and.clone(), ConstantDeclaration::inductive(
            Vec::new(), decoded(&primary_pi("a", BinderInfo::Default, prop(), primary_pi("b", BinderInfo::Default, prop(), prop()))), ConstantSafety::Safe,
            InductiveDeclaration::new(2, 0, vec![and.clone()], vec![intro.clone()], 0, false, false),
        )),
        ConstantEntry::new(intro.clone(), ConstantDeclaration::constructor(
            Vec::new(), decoded(&primary_pi("a", BinderInfo::Default, prop(), primary_pi(
                "b", BinderInfo::Default, prop(), primary_pi(
                    "left", BinderInfo::Default, bv(1), primary_pi(
                        "right", BinderInfo::Default, bv(1), and_expr(bv(3), bv(2)),
                    ),
                ),
            ))), ConstantSafety::Safe, ConstructorDeclaration::new(and.clone(), 0, 2, 2),
        )),
        ConstantEntry::new(rec, ConstantDeclaration::recursor(
            vec![u_name], decoded(&rec_type), ConstantSafety::Safe,
            RecursorDeclaration::new(vec![and], 2, 0, 1, 1, vec![RecursorRule::new(intro, 2, decoded(&rhs))], false),
        )),
    ]
}

fn init_bool_entries() -> Vec<ConstantEntry> {
    let bool_name = checker_name("Bool");
    let false_name = checker_qualified(&["Bool", "false"]);
    let true_name = checker_qualified(&["Bool", "true"]);
    let rec = checker_qualified(&["Bool", "rec"]);
    let u_name = checker_name("u");
    let u = Level::param(primary_name("u"));
    let bool_expr = || Expr::const_(primary_name("Bool"), Vec::new());
    let false_expr = || Expr::const_(Name::from_components(["Bool", "false"]), Vec::new());
    let true_expr = || Expr::const_(Name::from_components(["Bool", "true"]), Vec::new());
    let bv = |index| Expr::bvar(index).expect("packs");
    let motive = || primary_pi("t", BinderInfo::Default, bool_expr(), Expr::sort(u.clone()));
    let false_minor = || Expr::app(bv(0), false_expr());
    let true_minor = || Expr::app(bv(1), true_expr());
    let rec_type = primary_pi("motive", BinderInfo::Implicit, motive(), primary_pi(
        "false", BinderInfo::Default, false_minor(), primary_pi(
            "true", BinderInfo::Default, true_minor(), primary_pi(
                "t", BinderInfo::Default, bool_expr(), Expr::app(bv(3), bv(0)),
            ),
        ),
    ));
    let false_rhs = Expr::lam(primary_name("motive"), motive(), Expr::lam(
        primary_name("false"), false_minor(), Expr::lam(
            primary_name("true"), true_minor(), bv(1), BinderInfo::Default,
        ), BinderInfo::Default,
    ), BinderInfo::Default);
    let true_rhs = Expr::lam(primary_name("motive"), motive(), Expr::lam(
        primary_name("false"), false_minor(), Expr::lam(
            primary_name("true"), true_minor(), bv(0), BinderInfo::Default,
        ), BinderInfo::Default,
    ), BinderInfo::Default);
    vec![
        ConstantEntry::new(bool_name.clone(), ConstantDeclaration::inductive(
            Vec::new(), decoded(&Expr::sort(Level::one())), ConstantSafety::Safe,
            InductiveDeclaration::new(0, 0, vec![bool_name.clone()], vec![false_name.clone(), true_name.clone()], 0, false, false),
        )),
        ConstantEntry::new(false_name.clone(), ConstantDeclaration::constructor(
            Vec::new(), decoded(&bool_expr()), ConstantSafety::Safe,
            ConstructorDeclaration::new(bool_name.clone(), 0, 0, 0),
        )),
        ConstantEntry::new(true_name.clone(), ConstantDeclaration::constructor(
            Vec::new(), decoded(&bool_expr()), ConstantSafety::Safe,
            ConstructorDeclaration::new(bool_name.clone(), 1, 0, 0),
        )),
        ConstantEntry::new(rec, ConstantDeclaration::recursor(
            vec![u_name], decoded(&rec_type), ConstantSafety::Safe,
            RecursorDeclaration::new(vec![bool_name], 0, 0, 1, 2, vec![
                RecursorRule::new(false_name, 0, decoded(&false_rhs)),
                RecursorRule::new(true_name, 0, decoded(&true_rhs)),
            ], false),
        )),
    ]
}

fn init_punit_entries() -> Vec<ConstantEntry> {
    let punit = checker_name("PUnit");
    let unit = checker_qualified(&["PUnit", "unit"]);
    let rec = checker_qualified(&["PUnit", "rec"]);
    let u_name = checker_name("u");
    let v_name = checker_name("v");
    let u = Level::param(primary_name("u"));
    let v = Level::param(primary_name("v"));
    let punit_expr = || Expr::const_(primary_name("PUnit"), vec![u.clone()]);
    let unit_expr = || Expr::const_(Name::from_components(["PUnit", "unit"]), vec![u.clone()]);
    let bv = |index| Expr::bvar(index).expect("packs");
    let motive = || primary_pi("t", BinderInfo::Default, punit_expr(), Expr::sort(v.clone()));
    let minor = || Expr::app(bv(0), unit_expr());
    let rec_type = primary_pi("motive", BinderInfo::Implicit, motive(), primary_pi(
        "unit", BinderInfo::Default, minor(), primary_pi(
            "t", BinderInfo::Default, punit_expr(), Expr::app(bv(2), bv(0)),
        ),
    ));
    let rhs = Expr::lam(primary_name("motive"), motive(), Expr::lam(
        primary_name("unit"), minor(), bv(0), BinderInfo::Default,
    ), BinderInfo::Default);
    vec![
        ConstantEntry::new(punit.clone(), ConstantDeclaration::inductive(
            vec![u_name.clone()], decoded(&Expr::sort(u.clone())), ConstantSafety::Safe,
            InductiveDeclaration::new(0, 0, vec![punit.clone()], vec![unit.clone()], 0, false, false),
        )),
        ConstantEntry::new(unit.clone(), ConstantDeclaration::constructor(
            vec![u_name.clone()], decoded(&punit_expr()), ConstantSafety::Safe,
            ConstructorDeclaration::new(punit.clone(), 0, 0, 0),
        )),
        ConstantEntry::new(rec, ConstantDeclaration::recursor(
            vec![v_name, u_name], decoded(&rec_type), ConstantSafety::Safe,
            RecursorDeclaration::new(vec![punit], 0, 0, 1, 1, vec![RecursorRule::new(unit, 0, decoded(&rhs))], false),
        )),
    ]
}

fn init_unit_entries() -> Vec<ConstantEntry> {
    let unit = checker_name("Unit");
    let unit_ctor = checker_qualified(&["Unit", "unit"]);
    let rec = checker_qualified(&["Unit", "rec"]);
    let v_name = checker_name("v");
    let v = Level::param(primary_name("v"));
    let unit_expr = || Expr::const_(primary_name("Unit"), Vec::new());
    let unit_ctor_expr = || Expr::const_(Name::from_components(["Unit", "unit"]), Vec::new());
    let bv = |index| Expr::bvar(index).expect("packs");
    let motive = || primary_pi("t", BinderInfo::Default, unit_expr(), Expr::sort(v.clone()));
    let minor = || Expr::app(bv(0), unit_ctor_expr());
    let rec_type = primary_pi("motive", BinderInfo::Implicit, motive(), primary_pi(
        "unit", BinderInfo::Default, minor(), primary_pi(
            "t", BinderInfo::Default, unit_expr(), Expr::app(bv(2), bv(0)),
        ),
    ));
    let rhs = Expr::lam(primary_name("motive"), motive(), Expr::lam(
        primary_name("unit"), minor(), bv(0), BinderInfo::Default,
    ), BinderInfo::Default);
    vec![
        ConstantEntry::new(unit.clone(), ConstantDeclaration::inductive(
            Vec::new(), decoded(&Expr::sort(Level::one())), ConstantSafety::Safe,
            InductiveDeclaration::new(0, 0, vec![unit.clone()], vec![unit_ctor.clone()], 0, false, false),
        )),
        ConstantEntry::new(unit_ctor.clone(), ConstantDeclaration::constructor(
            Vec::new(), decoded(&unit_expr()), ConstantSafety::Safe,
            ConstructorDeclaration::new(unit.clone(), 0, 0, 0),
        )),
        ConstantEntry::new(rec, ConstantDeclaration::recursor(
            vec![v_name], decoded(&rec_type), ConstantSafety::Safe,
            RecursorDeclaration::new(vec![unit], 0, 0, 1, 1, vec![RecursorRule::new(unit_ctor, 0, decoded(&rhs))], false),
        )),
    ]
}

fn init_sum_entries() -> Vec<ConstantEntry> {
    let sum = checker_name("Sum");
    let inl = checker_qualified(&["Sum", "inl"]);
    let inr = checker_qualified(&["Sum", "inr"]);
    let rec = checker_qualified(&["Sum", "rec"]);
    let u_name = checker_name("u");
    let v_name = checker_name("v");
    let w_name = checker_name("w");
    let u = Level::param(primary_name("u"));
    let v = Level::param(primary_name("v"));
    let w = Level::param(primary_name("w"));
    let left_type = || Expr::sort(Level::succ(u.clone()).expect("universe successor packs"));
    let right_type = || Expr::sort(Level::succ(v.clone()).expect("universe successor packs"));
    let sum_type = || Expr::sort(Level::succ(Level::max(u.clone(), v.clone()).expect("universe maximum packs")).expect("universe successor packs"));
    let sum_expr = |left: Expr, right: Expr| {
        Expr::app(
            Expr::app(Expr::const_(primary_name("Sum"), vec![u.clone(), v.clone()]), left),
            right,
        )
    };
    let inl_expr = |left: Expr, right: Expr, value: Expr| {
        Expr::app(
            Expr::app(
                Expr::app(Expr::const_(Name::from_components(["Sum", "inl"]), vec![u.clone(), v.clone()]), left),
                right,
            ),
            value,
        )
    };
    let inr_expr = |left: Expr, right: Expr, value: Expr| {
        Expr::app(
            Expr::app(
                Expr::app(Expr::const_(Name::from_components(["Sum", "inr"]), vec![u.clone(), v.clone()]), left),
                right,
            ),
            value,
        )
    };
    let bv = |index| Expr::bvar(index).expect("packs");
    let motive = || primary_pi("t", BinderInfo::Default, sum_expr(bv(1), bv(0)), Expr::sort(w.clone()));
    let inl_minor = || primary_pi("value", BinderInfo::Default, bv(2), Expr::app(bv(1), inl_expr(bv(3), bv(2), bv(0))));
    let inr_minor = || primary_pi("value", BinderInfo::Default, bv(2), Expr::app(bv(2), inr_expr(bv(4), bv(3), bv(0))));
    let rec_type = primary_pi("α", BinderInfo::Implicit, left_type(), primary_pi(
        "β", BinderInfo::Implicit, right_type(), primary_pi(
            "motive", BinderInfo::Implicit, motive(), primary_pi(
                "inl", BinderInfo::Default, inl_minor(), primary_pi(
                    "inr", BinderInfo::Default, inr_minor(), primary_pi(
                        "t", BinderInfo::Default, sum_expr(bv(4), bv(3)), Expr::app(bv(3), bv(0)),
                    ),
                ),
            ),
        ),
    ));
    let inl_rhs = Expr::lam(primary_name("α"), left_type(), Expr::lam(
        primary_name("β"), right_type(), Expr::lam(
            primary_name("motive"), motive(), Expr::lam(
                primary_name("inl"), inl_minor(), Expr::lam(
                    primary_name("inr"), inr_minor(), Expr::lam(
                        primary_name("value"), bv(4), Expr::app(bv(2), bv(0)), BinderInfo::Default,
                    ), BinderInfo::Default,
                ), BinderInfo::Default,
            ), BinderInfo::Default,
        ), BinderInfo::Default,
    ), BinderInfo::Default);
    let inr_rhs = Expr::lam(primary_name("α"), left_type(), Expr::lam(
        primary_name("β"), right_type(), Expr::lam(
            primary_name("motive"), motive(), Expr::lam(
                primary_name("inl"), inl_minor(), Expr::lam(
                    primary_name("inr"), inr_minor(), Expr::lam(
                        primary_name("value"), bv(3), Expr::app(bv(1), bv(0)), BinderInfo::Default,
                    ), BinderInfo::Default,
                ), BinderInfo::Default,
            ), BinderInfo::Default,
        ), BinderInfo::Default,
    ), BinderInfo::Default);
    let inductive_type = primary_pi(
        "α",
        BinderInfo::Default,
        left_type(),
        primary_pi("β", BinderInfo::Default, right_type(), sum_type()),
    );
    let inl_type = primary_pi(
        "α",
        BinderInfo::Default,
        left_type(),
        primary_pi(
            "β",
            BinderInfo::Default,
            right_type(),
            primary_pi("value", BinderInfo::Default, bv(1), sum_expr(bv(2), bv(1))),
        ),
    );
    let inr_type = primary_pi(
        "α",
        BinderInfo::Default,
        left_type(),
        primary_pi(
            "β",
            BinderInfo::Default,
            right_type(),
            primary_pi("value", BinderInfo::Default, bv(0), sum_expr(bv(2), bv(1))),
        ),
    );
    vec![
        ConstantEntry::new(sum.clone(), ConstantDeclaration::inductive(
            vec![u_name.clone(), v_name.clone()],
            decoded(&inductive_type),
            ConstantSafety::Safe,
            InductiveDeclaration::new(2, 0, vec![sum.clone()], vec![inl.clone(), inr.clone()], 0, false, false),
        )),
        ConstantEntry::new(inl.clone(), ConstantDeclaration::constructor(
            vec![u_name.clone(), v_name.clone()],
            decoded(&inl_type),
            ConstantSafety::Safe,
            ConstructorDeclaration::new(sum.clone(), 0, 2, 1),
        )),
        ConstantEntry::new(inr.clone(), ConstantDeclaration::constructor(
            vec![u_name.clone(), v_name.clone()],
            decoded(&inr_type),
            ConstantSafety::Safe,
            ConstructorDeclaration::new(sum.clone(), 1, 2, 1),
        )),
        ConstantEntry::new(rec, ConstantDeclaration::recursor(
            vec![w_name, u_name, v_name], decoded(&rec_type), ConstantSafety::Safe,
            RecursorDeclaration::new(vec![sum], 2, 0, 1, 2, vec![
                RecursorRule::new(inl, 1, decoded(&inl_rhs)),
                RecursorRule::new(inr, 1, decoded(&inr_rhs)),
            ], false),
        )),
    ]
}

fn init_prod_entries() -> Vec<ConstantEntry> {
    let prod = checker_name("Prod");
    let mk = checker_qualified(&["Prod", "mk"]);
    let rec = checker_qualified(&["Prod", "rec"]);
    let u_name = checker_name("u");
    let v_name = checker_name("v");
    let w_name = checker_name("w");
    let u = Level::param(primary_name("u"));
    let v = Level::param(primary_name("v"));
    let w = Level::param(primary_name("w"));
    let left_type = || Expr::sort(Level::succ(u.clone()).expect("universe successor packs"));
    let right_type = || Expr::sort(Level::succ(v.clone()).expect("universe successor packs"));
    let prod_type = || Expr::sort(Level::succ(Level::max(u.clone(), v.clone()).expect("universe maximum packs")).expect("universe successor packs"));
    let prod_expr = |left: Expr, right: Expr| Expr::app(Expr::app(Expr::const_(primary_name("Prod"), vec![u.clone(), v.clone()]), left), right);
    let mk_expr = |left: Expr, right: Expr, first: Expr, second: Expr| Expr::app(Expr::app(Expr::app(Expr::app(Expr::const_(Name::from_components(["Prod", "mk"]), vec![u.clone(), v.clone()]), left), right), first), second);
    let bv = |index| Expr::bvar(index).expect("packs");
    let motive = || primary_pi("t", BinderInfo::Default, prod_expr(bv(1), bv(0)), Expr::sort(w.clone()));
    let minor = || primary_pi("fst", BinderInfo::Default, bv(2), primary_pi("snd", BinderInfo::Default, bv(2), Expr::app(bv(2), mk_expr(bv(4), bv(3), bv(1), bv(0)))));
    let rec_type = primary_pi("α", BinderInfo::Implicit, left_type(), primary_pi(
        "β", BinderInfo::Implicit, right_type(), primary_pi(
            "motive", BinderInfo::Implicit, motive(), primary_pi(
                "mk", BinderInfo::Default, minor(), primary_pi(
                    "t", BinderInfo::Default, prod_expr(bv(3), bv(2)), Expr::app(bv(2), bv(0)),
                ),
            ),
        ),
    ));
    let minor_applied = Expr::app(Expr::app(bv(2), bv(1)), bv(0));
    let rhs = Expr::lam(primary_name("α"), left_type(), Expr::lam(
        primary_name("β"), right_type(), Expr::lam(
            primary_name("motive"), motive(), Expr::lam(
                primary_name("mk"), minor(), Expr::lam(
                    primary_name("fst"), bv(3), Expr::lam(
                        primary_name("snd"), bv(3), minor_applied, BinderInfo::Default,
                    ), BinderInfo::Default,
                ), BinderInfo::Default,
            ), BinderInfo::Default,
        ), BinderInfo::Default,
    ), BinderInfo::Default);
    let inductive_type = primary_pi(
        "α", BinderInfo::Default, left_type(), primary_pi("β", BinderInfo::Default, right_type(), prod_type()),
    );
    let constructor_type = primary_pi("α", BinderInfo::Default, left_type(), primary_pi(
        "β", BinderInfo::Default, right_type(), primary_pi(
            "fst", BinderInfo::Default, bv(1), primary_pi("snd", BinderInfo::Default, bv(1), prod_expr(bv(3), bv(2))),
        ),
    ));
    vec![
        ConstantEntry::new(prod.clone(), ConstantDeclaration::inductive(vec![u_name.clone(), v_name.clone()], decoded(&inductive_type), ConstantSafety::Safe, InductiveDeclaration::new(2, 0, vec![prod.clone()], vec![mk.clone()], 0, false, false))),
        ConstantEntry::new(mk.clone(), ConstantDeclaration::constructor(vec![u_name.clone(), v_name.clone()], decoded(&constructor_type), ConstantSafety::Safe, ConstructorDeclaration::new(prod.clone(), 0, 2, 2))),
        ConstantEntry::new(rec, ConstantDeclaration::recursor(vec![w_name, u_name, v_name], decoded(&rec_type), ConstantSafety::Safe, RecursorDeclaration::new(vec![prod], 2, 0, 1, 1, vec![RecursorRule::new(mk, 2, decoded(&rhs))], false))),
    ]
}

fn init_except_constructor_entries() -> Vec<ConstantEntry> {
    let except = checker_name("Except");
    let error = checker_qualified(&["Except", "error"]);
    let ok = checker_qualified(&["Except", "ok"]);
    let u_name = checker_name("u");
    let v_name = checker_name("v");
    let u = Level::param(primary_name("u"));
    let v = Level::param(primary_name("v"));
    let error_type = || Expr::sort(Level::succ(u.clone()).expect("universe successor packs"));
    let ok_type = || Expr::sort(Level::succ(v.clone()).expect("universe successor packs"));
    let except_expr = |error: Expr, ok: Expr| Expr::app(
        Expr::app(Expr::const_(primary_name("Except"), vec![u.clone(), v.clone()]), error), ok,
    );
    let bv = |index| Expr::bvar(index).expect("packs");
    let error_ctor_type = primary_pi("ε", BinderInfo::Default, error_type(), primary_pi(
        "α", BinderInfo::Default, ok_type(), primary_pi("value", BinderInfo::Default, bv(1), except_expr(bv(2), bv(1))),
    ));
    let ok_ctor_type = primary_pi("ε", BinderInfo::Default, error_type(), primary_pi(
        "α", BinderInfo::Default, ok_type(), primary_pi("value", BinderInfo::Default, bv(0), except_expr(bv(2), bv(1))),
    ));
    vec![
        ConstantEntry::new(error, ConstantDeclaration::constructor(vec![u_name.clone(), v_name.clone()], decoded(&error_ctor_type), ConstantSafety::Safe, ConstructorDeclaration::new(except.clone(), 0, 2, 1))),
        ConstantEntry::new(ok, ConstantDeclaration::constructor(vec![u_name, v_name], decoded(&ok_ctor_type), ConstantSafety::Safe, ConstructorDeclaration::new(except, 1, 2, 1))),
    ]
}

#[test]
fn kr600_803_init_and_parameters_fields_and_rule_are_reconstructed() {
    let entries = init_and_entries();
    let verdict = admit_inductive(&ConstantEnvironment::empty(), &entries, AdmissionBudget::unlimited(), EnvironmentBudget::unlimited());
    assert!(verdict.is_admitted(), "exact Init.And block: {verdict:?}");
    let fln_checker::admit::InductiveVerdict::Admitted(admission) = verdict else {
        return;
    };
    assert_eq!(admission.members().len(), 3);
}

#[test]
fn kr600_803_init_and_refuses_a_forged_iota_rule() {
    let mut entries = init_and_entries();
    let declaration = entries[2].declaration();
    let metadata = declaration.recursor_metadata().expect("fixture recursor metadata");
    entries[2] = ConstantEntry::new(checker_qualified(&["And", "rec"]), ConstantDeclaration::recursor(
        declaration.level_parameters().to_vec(), declaration.type_().clone(), declaration.safety(),
        RecursorDeclaration::new(metadata.mutual().to_vec(), metadata.num_parameters(), metadata.num_indices(), metadata.num_motives(), metadata.num_minors(), vec![RecursorRule::new(checker_qualified(&["And", "intro"]), 2, decoded(&Expr::bvar(0).expect("packs")))], metadata.k()),
    ));
    assert!(matches!(admit_inductive(&ConstantEnvironment::empty(), &entries, AdmissionBudget::unlimited(), EnvironmentBudget::unlimited()), fln_checker::admit::InductiveVerdict::Rejected(fln_checker::admit::InductiveRejection::RecursorShape { .. })));
}

#[test]
fn kr600_803_init_and_refuses_a_forged_num_motives_count() {
    let mut entries = init_and_entries();
    let declaration = entries[2].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[2] = ConstantEntry::new(
        checker_qualified(&["And", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives() + 1,
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_and_refuses_a_forged_num_minors_count() {
    let mut entries = init_and_entries();
    let declaration = entries[2].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[2] = ConstantEntry::new(
        checker_qualified(&["And", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors() + 1,
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_and_refuses_a_forged_num_rules_count() {
    let mut entries = init_and_entries();
    let declaration = entries[2].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    let mut rules = metadata.rules().to_vec();
    rules.push(metadata.rules()[0].clone());
    entries[2] = ConstantEntry::new(
        checker_qualified(&["And", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                rules,
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_and_refuses_a_forged_num_parameters_count() {
    let mut entries = init_and_entries();
    let declaration = entries[2].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[2] = ConstantEntry::new(
        checker_qualified(&["And", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters() + 1,
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_and_refuses_a_forged_num_indices_count() {
    let mut entries = init_and_entries();
    let declaration = entries[2].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[2] = ConstantEntry::new(
        checker_qualified(&["And", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices() + 1,
                metadata.num_motives(),
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_and_refuses_a_forged_extra_recursor_rule() {
    let mut entries = init_and_entries();
    let declaration = entries[2].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    let mut rules = metadata.rules().to_vec();
    rules.push(RecursorRule::new(
        checker_qualified(&["And", "forged"]),
        0,
        decoded(&Expr::bvar(0).expect("packs")),
    ));
    entries[2] = ConstantEntry::new(
        checker_qualified(&["And", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                rules,
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_and_refuses_a_forged_constructor_field_count() {
    let mut entries = init_and_entries();
    let constructor = entries[1].declaration();
    entries[1] = ConstantEntry::new(
        checker_qualified(&["And", "intro"]),
        ConstantDeclaration::constructor(
            constructor.level_parameters().to_vec(),
            constructor.type_().clone(),
            constructor.safety(),
            ConstructorDeclaration::new(checker_name("And"), 0, 2, 3),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::ConstructorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_and_fixture_pins_recursor_levels_motives_minors_and_rules() {
    let entries = init_and_entries();
    let recursor = entries[2].declaration();
    let metadata = recursor.recursor_metadata().expect("fixture recursor metadata");
    assert_eq!(recursor.level_parameters().len(), 1);
    assert_eq!(metadata.num_parameters(), 2);
    assert_eq!(metadata.num_indices(), 0);
    assert_eq!(metadata.num_motives(), 1);
    assert_eq!(metadata.num_minors(), 1);
    assert_eq!(metadata.rules().len(), 1);
    assert_eq!(metadata.rules()[0].constructor(), &checker_qualified(&["And", "intro"]));
    assert_eq!(metadata.rules()[0].num_fields(), 2);
}

#[test]
fn kr600_803_init_and_fixture_pins_recursor_mutual_family_and_k() {
    let entries = init_and_entries();
    let metadata = entries[2]
        .declaration()
        .recursor_metadata()
        .expect("fixture recursor metadata");
    assert_eq!(metadata.mutual(), &[checker_name("And")]);
    assert!(!metadata.k());
}

#[test]
fn kr600_803_init_and_fixture_pins_constructor_and_iota_rule() {
    let entries = init_and_entries();
    let constructor = entries[1].declaration();
    let constructor_metadata = constructor.constructor_metadata().expect("fixture constructor metadata");
    assert_eq!(constructor_metadata.inductive(), &checker_name("And"));
    assert_eq!(constructor_metadata.index(), 0);
    assert_eq!(constructor_metadata.num_parameters(), 2);
    assert_eq!(constructor_metadata.num_fields(), 2);
    assert!(constructor.level_parameters().is_empty());
    let recursor = entries[2].declaration().recursor_metadata().expect("fixture recursor metadata");
    assert_eq!(recursor.rules()[0].constructor(), entries[1].name());
    assert_eq!(recursor.rules()[0].num_fields(), 2);
}

#[test]
fn kr600_803_init_and_fixture_pins_iota_rhs_closure() {
    let entries = init_and_entries();
    let rule = &entries[2]
        .declaration()
        .recursor_metadata()
        .expect("fixture recursor metadata")
        .rules()[0];
    let facts = match inspect(rule.rhs(), TermBudget::unlimited()) {
        TermOutcome::Complete(facts) => facts,
        other => panic!("fixture iota inspection must complete: {other:?}"),
    };
    assert_eq!(facts.external_bound_span, 0);
}

#[test]
fn kr600_803_init_bool_constructors_recursor_and_iota_are_reconstructed() {
    let entries = init_bool_entries();
    let verdict = admit_inductive(&ConstantEnvironment::empty(), &entries, AdmissionBudget::unlimited(), EnvironmentBudget::unlimited());
    assert!(verdict.is_admitted(), "exact Init.Bool block: {verdict:?}");
}

#[test]
fn kr600_803_init_bool_refuses_a_forged_true_iota_rule() {
    let mut entries = init_bool_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration.recursor_metadata().expect("fixture recursor metadata");
    entries[3] = ConstantEntry::new(checker_qualified(&["Bool", "rec"]), ConstantDeclaration::recursor(
        declaration.level_parameters().to_vec(), declaration.type_().clone(), declaration.safety(),
        RecursorDeclaration::new(metadata.mutual().to_vec(), metadata.num_parameters(), metadata.num_indices(), metadata.num_motives(), metadata.num_minors(), vec![
            metadata.rules()[0].clone(),
            RecursorRule::new(checker_qualified(&["Bool", "true"]), 0, decoded(&Expr::bvar(0).expect("packs"))),
        ], metadata.k()),
    ));
    assert!(matches!(admit_inductive(&ConstantEnvironment::empty(), &entries, AdmissionBudget::unlimited(), EnvironmentBudget::unlimited()), fln_checker::admit::InductiveVerdict::Rejected(fln_checker::admit::InductiveRejection::RecursorShape { .. })));
}

#[test]
fn kr600_803_init_bool_refuses_a_forged_num_parameters_count() {
    let mut entries = init_bool_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Bool", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters() + 1,
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_bool_refuses_a_forged_num_motives_count() {
    let mut entries = init_bool_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Bool", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives() + 1,
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_bool_refuses_a_forged_num_minors_count() {
    let mut entries = init_bool_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Bool", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors() + 1,
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_bool_refuses_a_forged_num_rules_count() {
    let mut entries = init_bool_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    let mut rules = metadata.rules().to_vec();
    rules.push(metadata.rules()[1].clone());
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Bool", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                rules,
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_bool_refuses_a_forged_extra_recursor_rule() {
    let mut entries = init_bool_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    let mut rules = metadata.rules().to_vec();
    rules.push(RecursorRule::new(
        checker_qualified(&["Bool", "forged"]),
        0,
        decoded(&Expr::bvar(0).expect("packs")),
    ));
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Bool", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                rules,
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_bool_refuses_a_forged_constructor_field_count() {
    let mut entries = init_bool_entries();
    let constructor = entries[1].declaration();
    entries[1] = ConstantEntry::new(
        checker_qualified(&["Bool", "false"]),
        ConstantDeclaration::constructor(
            constructor.level_parameters().to_vec(),
            constructor.type_().clone(),
            constructor.safety(),
            ConstructorDeclaration::new(checker_name("Bool"), 0, 0, 1),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::ConstructorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_bool_refuses_a_forged_constructor_index() {
    let mut entries = init_bool_entries();
    let constructor = entries[1].declaration();
    entries[1] = ConstantEntry::new(
        checker_qualified(&["Bool", "false"]),
        ConstantDeclaration::constructor(
            constructor.level_parameters().to_vec(),
            constructor.type_().clone(),
            constructor.safety(),
            ConstructorDeclaration::new(checker_name("Bool"), 1, 0, 0),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::ConstructorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_bool_refuses_a_forged_num_indices_count() {
    let mut entries = init_bool_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Bool", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices() + 1,
                metadata.num_motives(),
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_bool_fixture_pins_recursor_levels_motives_minors_and_rules() {
    let entries = init_bool_entries();
    let recursor = entries[3].declaration();
    let metadata = recursor.recursor_metadata().expect("fixture recursor metadata");
    assert_eq!(recursor.level_parameters().len(), 1);
    assert_eq!(metadata.num_parameters(), 0);
    assert_eq!(metadata.num_indices(), 0);
    assert_eq!(metadata.num_motives(), 1);
    assert_eq!(metadata.num_minors(), 2);
    assert_eq!(metadata.rules().len(), 2);
    assert_eq!(metadata.rules()[0].constructor(), &checker_qualified(&["Bool", "false"]));
    assert_eq!(metadata.rules()[0].num_fields(), 0);
    assert_eq!(metadata.rules()[1].constructor(), &checker_qualified(&["Bool", "true"]));
    assert_eq!(metadata.rules()[1].num_fields(), 0);
}

#[test]
fn kr600_803_init_bool_fixture_pins_recursor_mutual_family_and_k() {
    let entries = init_bool_entries();
    let metadata = entries[3]
        .declaration()
        .recursor_metadata()
        .expect("fixture recursor metadata");
    assert_eq!(metadata.mutual(), &[checker_name("Bool")]);
    assert!(!metadata.k());
}

#[test]
fn kr600_803_init_bool_fixture_pins_constructor_indices_parameters_and_fields() {
    let entries = init_bool_entries();
    for (entry, expected_index) in [(&entries[1], 0), (&entries[2], 1)] {
        let metadata = entry
            .declaration()
            .constructor_metadata()
            .expect("fixture constructor metadata");
        assert_eq!(metadata.inductive(), &checker_name("Bool"));
        assert_eq!(metadata.index(), expected_index);
        assert_eq!(metadata.num_parameters(), 0);
        assert_eq!(metadata.num_fields(), 0);
        assert_eq!(entry.declaration().level_parameters().len(), 0);
    }
}

#[test]
fn kr600_803_init_bool_fixture_pins_iota_rule_constructors_and_fields() {
    let entries = init_bool_entries();
    let metadata = entries[3]
        .declaration()
        .recursor_metadata()
        .expect("fixture recursor metadata");
    for (rule, constructor) in [
        (&metadata.rules()[0], entries[1].name()),
        (&metadata.rules()[1], entries[2].name()),
    ] {
        assert_eq!(rule.constructor(), constructor);
        assert_eq!(rule.num_fields(), 0);
    }
}

#[test]
fn kr600_803_init_bool_fixture_pins_iota_rhs_closure() {
    let entries = init_bool_entries();
    let metadata = entries[3]
        .declaration()
        .recursor_metadata()
        .expect("fixture recursor metadata");
    for rule in metadata.rules() {
        let facts = match inspect(rule.rhs(), TermBudget::unlimited()) {
            TermOutcome::Complete(facts) => facts,
            other => panic!("fixture iota inspection must complete: {other:?}"),
        };
        assert_eq!(facts.external_bound_span, 0);
    }
}

#[test]
fn kr600_803_init_punit_universes_constructor_and_iota_are_reconstructed() {
    let entries = init_punit_entries();
    let verdict = admit_inductive(&ConstantEnvironment::empty(), &entries, AdmissionBudget::unlimited(), EnvironmentBudget::unlimited());
    assert!(verdict.is_admitted(), "exact Init.PUnit block: {verdict:?}");
}

#[test]
fn kr600_803_init_punit_refuses_a_forged_iota_rule() {
    let mut entries = init_punit_entries();
    let declaration = entries[2].declaration();
    let metadata = declaration.recursor_metadata().expect("fixture recursor metadata");
    entries[2] = ConstantEntry::new(checker_qualified(&["PUnit", "rec"]), ConstantDeclaration::recursor(
        declaration.level_parameters().to_vec(), declaration.type_().clone(), declaration.safety(),
        RecursorDeclaration::new(metadata.mutual().to_vec(), metadata.num_parameters(), metadata.num_indices(), metadata.num_motives(), metadata.num_minors(), vec![RecursorRule::new(checker_qualified(&["PUnit", "unit"]), 0, decoded(&Expr::bvar(0).expect("packs")))], metadata.k()),
    ));
    assert!(matches!(admit_inductive(&ConstantEnvironment::empty(), &entries, AdmissionBudget::unlimited(), EnvironmentBudget::unlimited()), fln_checker::admit::InductiveVerdict::Rejected(fln_checker::admit::InductiveRejection::RecursorShape { .. })));
}

#[test]
fn kr600_803_init_punit_refuses_a_forged_extra_recursor_rule() {
    let mut entries = init_punit_entries();
    let declaration = entries[2].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    let mut rules = metadata.rules().to_vec();
    rules.push(RecursorRule::new(
        checker_qualified(&["PUnit", "forged"]),
        0,
        decoded(&Expr::bvar(0).expect("packs")),
    ));
    entries[2] = ConstantEntry::new(
        checker_qualified(&["PUnit", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                rules,
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_punit_refuses_a_forged_constructor_index() {
    let mut entries = init_punit_entries();
    let constructor = entries[1].declaration();
    entries[1] = ConstantEntry::new(
        checker_qualified(&["PUnit", "unit"]),
        ConstantDeclaration::constructor(
            constructor.level_parameters().to_vec(),
            constructor.type_().clone(),
            constructor.safety(),
            ConstructorDeclaration::new(checker_name("PUnit"), 1, 0, 0),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::ConstructorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_punit_refuses_a_forged_constructor_field_count() {
    let mut entries = init_punit_entries();
    let constructor = entries[1].declaration();
    entries[1] = ConstantEntry::new(
        checker_qualified(&["PUnit", "unit"]),
        ConstantDeclaration::constructor(
            constructor.level_parameters().to_vec(),
            constructor.type_().clone(),
            constructor.safety(),
            ConstructorDeclaration::new(checker_name("PUnit"), 0, 0, 1),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::ConstructorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_punit_refuses_a_forged_num_rules_count() {
    let mut entries = init_punit_entries();
    let declaration = entries[2].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    let mut rules = metadata.rules().to_vec();
    rules.push(metadata.rules()[0].clone());
    entries[2] = ConstantEntry::new(
        checker_qualified(&["PUnit", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                rules,
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_punit_refuses_a_forged_num_indices_count() {
    let mut entries = init_punit_entries();
    let declaration = entries[2].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[2] = ConstantEntry::new(
        checker_qualified(&["PUnit", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices() + 1,
                metadata.num_motives(),
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_punit_refuses_a_forged_num_motives_count() {
    let mut entries = init_punit_entries();
    let declaration = entries[2].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[2] = ConstantEntry::new(
        checker_qualified(&["PUnit", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives() + 1,
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_punit_refuses_a_forged_num_minors_count() {
    let mut entries = init_punit_entries();
    let declaration = entries[2].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[2] = ConstantEntry::new(
        checker_qualified(&["PUnit", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors() + 1,
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_punit_refuses_a_forged_num_parameters_count() {
    let mut entries = init_punit_entries();
    let declaration = entries[2].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[2] = ConstantEntry::new(
        checker_qualified(&["PUnit", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters() + 1,
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_punit_fixture_pins_recursor_levels_motives_minors_and_rules() {
    let entries = init_punit_entries();
    let recursor = entries[2].declaration();
    let metadata = recursor.recursor_metadata().expect("fixture recursor metadata");
    assert_eq!(recursor.level_parameters().len(), 2);
    assert_eq!(metadata.num_parameters(), 0);
    assert_eq!(metadata.num_indices(), 0);
    assert_eq!(metadata.num_motives(), 1);
    assert_eq!(metadata.num_minors(), 1);
    assert_eq!(metadata.rules().len(), 1);
    assert_eq!(metadata.rules()[0].constructor(), &checker_qualified(&["PUnit", "unit"]));
    assert_eq!(metadata.rules()[0].num_fields(), 0);
}

#[test]
fn kr600_803_init_punit_fixture_pins_recursor_mutual_family_and_k() {
    let entries = init_punit_entries();
    let metadata = entries[2]
        .declaration()
        .recursor_metadata()
        .expect("fixture recursor metadata");
    assert_eq!(metadata.mutual(), &[checker_name("PUnit")]);
    assert!(!metadata.k());
}

#[test]
fn kr600_803_init_punit_fixture_pins_constructor_and_iota_rule() {
    let entries = init_punit_entries();
    let constructor = entries[1].declaration();
    let constructor_metadata = constructor.constructor_metadata().expect("fixture constructor metadata");
    assert_eq!(constructor_metadata.inductive(), &checker_name("PUnit"));
    assert_eq!(constructor_metadata.index(), 0);
    assert_eq!(constructor_metadata.num_parameters(), 0);
    assert_eq!(constructor_metadata.num_fields(), 0);
    assert_eq!(constructor.level_parameters().len(), 1);
    let recursor = entries[2].declaration().recursor_metadata().expect("fixture recursor metadata");
    assert_eq!(recursor.rules()[0].constructor(), entries[1].name());
    assert_eq!(recursor.rules()[0].num_fields(), 0);
}

#[test]
fn kr600_803_init_punit_fixture_pins_iota_rhs_closure() {
    let entries = init_punit_entries();
    let rule = &entries[2]
        .declaration()
        .recursor_metadata()
        .expect("fixture recursor metadata")
        .rules()[0];
    let facts = match inspect(rule.rhs(), TermBudget::unlimited()) {
        TermOutcome::Complete(facts) => facts,
        other => panic!("fixture iota inspection must complete: {other:?}"),
    };
    assert_eq!(facts.external_bound_span, 0);
}

#[test]
fn kr600_803_init_unit_constructor_recursor_and_iota_are_reconstructed() {
    let entries = init_unit_entries();
    let verdict = admit_inductive(
        &ConstantEnvironment::empty(),
        &entries,
        AdmissionBudget::unlimited(),
        EnvironmentBudget::unlimited(),
    );
    assert!(verdict.is_admitted(), "exact Init.Unit block: {verdict:?}");
}

#[test]
fn kr600_803_init_unit_refuses_a_forged_iota_rule() {
    let mut entries = init_unit_entries();
    let declaration = entries[2].declaration();
    let metadata = declaration.recursor_metadata().expect("fixture recursor metadata");
    entries[2] = ConstantEntry::new(checker_qualified(&["Unit", "rec"]), ConstantDeclaration::recursor(
        declaration.level_parameters().to_vec(), declaration.type_().clone(), declaration.safety(),
        RecursorDeclaration::new(metadata.mutual().to_vec(), metadata.num_parameters(), metadata.num_indices(), metadata.num_motives(), metadata.num_minors(), vec![RecursorRule::new(checker_qualified(&["Unit", "unit"]), 0, decoded(&Expr::bvar(0).expect("packs")))], metadata.k()),
    ));
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_unit_refuses_a_forged_extra_recursor_rule() {
    let mut entries = init_unit_entries();
    let declaration = entries[2].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    let mut rules = metadata.rules().to_vec();
    rules.push(RecursorRule::new(
        checker_qualified(&["Unit", "forged"]),
        0,
        decoded(&Expr::bvar(0).expect("packs")),
    ));
    entries[2] = ConstantEntry::new(
        checker_qualified(&["Unit", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                rules,
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_unit_refuses_a_forged_constructor_field_count() {
    let mut entries = init_unit_entries();
    let constructor = entries[1].declaration();
    entries[1] = ConstantEntry::new(
        checker_qualified(&["Unit", "unit"]),
        ConstantDeclaration::constructor(
            constructor.level_parameters().to_vec(),
            constructor.type_().clone(),
            constructor.safety(),
            ConstructorDeclaration::new(checker_name("Unit"), 0, 0, 1),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::ConstructorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_unit_refuses_a_forged_constructor_index() {
    let mut entries = init_unit_entries();
    let constructor = entries[1].declaration();
    entries[1] = ConstantEntry::new(
        checker_qualified(&["Unit", "unit"]),
        ConstantDeclaration::constructor(
            constructor.level_parameters().to_vec(),
            constructor.type_().clone(),
            constructor.safety(),
            ConstructorDeclaration::new(checker_name("Unit"), 1, 0, 0),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::ConstructorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_unit_refuses_a_forged_num_rules_count() {
    let mut entries = init_unit_entries();
    let declaration = entries[2].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    let mut rules = metadata.rules().to_vec();
    rules.push(metadata.rules()[0].clone());
    entries[2] = ConstantEntry::new(
        checker_qualified(&["Unit", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                rules,
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_unit_refuses_a_forged_num_indices_count() {
    let mut entries = init_unit_entries();
    let declaration = entries[2].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[2] = ConstantEntry::new(
        checker_qualified(&["Unit", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices() + 1,
                metadata.num_motives(),
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_unit_refuses_a_forged_num_motives_count() {
    let mut entries = init_unit_entries();
    let declaration = entries[2].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[2] = ConstantEntry::new(
        checker_qualified(&["Unit", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives() + 1,
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_unit_refuses_a_forged_num_minors_count() {
    let mut entries = init_unit_entries();
    let declaration = entries[2].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[2] = ConstantEntry::new(
        checker_qualified(&["Unit", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors() + 1,
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_unit_refuses_a_forged_num_parameters_count() {
    let mut entries = init_unit_entries();
    let declaration = entries[2].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[2] = ConstantEntry::new(
        checker_qualified(&["Unit", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters() + 1,
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_unit_fixture_pins_constructor_and_iota_rule() {
    let entries = init_unit_entries();
    let constructor = entries[1].declaration();
    let constructor_metadata = constructor.constructor_metadata().expect("fixture constructor metadata");
    assert_eq!(constructor_metadata.inductive(), &checker_name("Unit"));
    assert_eq!(constructor_metadata.index(), 0);
    assert_eq!(constructor_metadata.num_parameters(), 0);
    assert_eq!(constructor_metadata.num_fields(), 0);
    assert!(constructor.level_parameters().is_empty());
    let recursor = entries[2].declaration().recursor_metadata().expect("fixture recursor metadata");
    assert_eq!(recursor.rules()[0].constructor(), entries[1].name());
    assert_eq!(recursor.rules()[0].num_fields(), 0);
}

#[test]
fn kr600_803_init_unit_fixture_pins_recursor_mutual_family_and_k() {
    let entries = init_unit_entries();
    let metadata = entries[2]
        .declaration()
        .recursor_metadata()
        .expect("fixture recursor metadata");
    assert_eq!(metadata.mutual(), &[checker_name("Unit")]);
    assert!(!metadata.k());
}

#[test]
fn kr600_803_init_unit_fixture_pins_iota_rhs_closure() {
    let entries = init_unit_entries();
    let rule = &entries[2]
        .declaration()
        .recursor_metadata()
        .expect("fixture recursor metadata")
        .rules()[0];
    let facts = match inspect(rule.rhs(), TermBudget::unlimited()) {
        TermOutcome::Complete(facts) => facts,
        other => panic!("fixture iota inspection must complete: {other:?}"),
    };
    assert_eq!(facts.external_bound_span, 0);
}

#[test]
fn kr600_803_init_sum_branches_recursor_and_iota_are_reconstructed() {
    let entries = init_sum_entries();
    let verdict = admit_inductive(
        &ConstantEnvironment::empty(),
        &entries,
        AdmissionBudget::unlimited(),
        EnvironmentBudget::unlimited(),
    );
    assert!(verdict.is_admitted(), "exact Init.Sum block: {verdict:?}");
}

#[test]
fn kr600_803_init_sum_fixture_pins_recursor_mutual_family_and_k() {
    let entries = init_sum_entries();
    let metadata = entries[3]
        .declaration()
        .recursor_metadata()
        .expect("fixture recursor metadata");
    assert_eq!(metadata.mutual(), &[checker_name("Sum")]);
    assert!(!metadata.k());
}

#[test]
fn kr600_803_init_sum_refuses_a_forged_inr_iota_rule() {
    let mut entries = init_sum_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration.recursor_metadata().expect("fixture recursor metadata");
    entries[3] = ConstantEntry::new(checker_qualified(&["Sum", "rec"]), ConstantDeclaration::recursor(
        declaration.level_parameters().to_vec(), declaration.type_().clone(), declaration.safety(),
        RecursorDeclaration::new(metadata.mutual().to_vec(), metadata.num_parameters(), metadata.num_indices(), metadata.num_motives(), metadata.num_minors(), vec![
            metadata.rules()[0].clone(),
            RecursorRule::new(checker_qualified(&["Sum", "inr"]), 1, decoded(&Expr::bvar(0).expect("packs"))),
        ], metadata.k()),
    ));
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_sum_refuses_a_forged_num_motives_count() {
    let mut entries = init_sum_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Sum", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives() + 1,
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_sum_refuses_a_forged_num_minors_count() {
    let mut entries = init_sum_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Sum", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors() + 1,
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_sum_refuses_a_forged_num_rules_count() {
    let mut entries = init_sum_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    let mut rules = metadata.rules().to_vec();
    rules.push(metadata.rules()[1].clone());
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Sum", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                rules,
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_sum_refuses_a_forged_extra_recursor_rule() {
    let mut entries = init_sum_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    let mut rules = metadata.rules().to_vec();
    rules.push(RecursorRule::new(
        checker_qualified(&["Sum", "forged"]),
        0,
        decoded(&Expr::bvar(0).expect("packs")),
    ));
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Sum", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                rules,
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_sum_inl_refuses_a_forged_constructor_index() {
    let mut entries = init_sum_entries();
    let constructor = entries[1].declaration();
    entries[1] = ConstantEntry::new(
        checker_qualified(&["Sum", "inl"]),
        ConstantDeclaration::constructor(
            constructor.level_parameters().to_vec(),
            constructor.type_().clone(),
            constructor.safety(),
            ConstructorDeclaration::new(checker_name("Sum"), 1, 2, 1),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::ConstructorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_sum_inr_refuses_a_forged_constructor_index() {
    let mut entries = init_sum_entries();
    let constructor = entries[2].declaration();
    entries[2] = ConstantEntry::new(
        checker_qualified(&["Sum", "inr"]),
        ConstantDeclaration::constructor(
            constructor.level_parameters().to_vec(),
            constructor.type_().clone(),
            constructor.safety(),
            ConstructorDeclaration::new(checker_name("Sum"), 0, 2, 1),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::ConstructorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_sum_refuses_a_forged_num_parameters_count() {
    let mut entries = init_sum_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Sum", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters() + 1,
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_sum_refuses_a_forged_num_indices_count() {
    let mut entries = init_sum_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Sum", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices() + 1,
                metadata.num_motives(),
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_prod_pair_recursor_and_iota_are_reconstructed() {
    let entries = init_prod_entries();
    let verdict = admit_inductive(&ConstantEnvironment::empty(), &entries, AdmissionBudget::unlimited(), EnvironmentBudget::unlimited());
    assert!(verdict.is_admitted(), "exact Init.Prod block: {verdict:?}");
}

#[test]
fn kr600_803_init_prod_fixture_pins_recursor_levels_motives_minors_and_metadata() {
    let entries = init_prod_entries();
    let recursor = entries[2].declaration();
    let metadata = recursor.recursor_metadata().expect("fixture recursor metadata");
    assert_eq!(recursor.level_parameters().len(), 3);
    assert_eq!(metadata.mutual(), &[checker_name("Prod")]);
    assert_eq!(metadata.num_parameters(), 2);
    assert_eq!(metadata.num_indices(), 0);
    assert_eq!(metadata.num_motives(), 1);
    assert_eq!(metadata.num_minors(), 1);
    assert_eq!(metadata.rules().len(), 1);
    assert!(!metadata.k());
}

#[test]
fn kr600_803_init_prod_refuses_a_forged_iota_rule() {
    let mut entries = init_prod_entries();
    let declaration = entries[2].declaration();
    let metadata = declaration.recursor_metadata().expect("fixture recursor metadata");
    entries[2] = ConstantEntry::new(checker_qualified(&["Prod", "rec"]), ConstantDeclaration::recursor(
        declaration.level_parameters().to_vec(), declaration.type_().clone(), declaration.safety(),
        RecursorDeclaration::new(metadata.mutual().to_vec(), metadata.num_parameters(), metadata.num_indices(), metadata.num_motives(), metadata.num_minors(), vec![RecursorRule::new(checker_qualified(&["Prod", "mk"]), 2, decoded(&Expr::bvar(0).expect("packs")))], metadata.k()),
    ));
    assert!(matches!(admit_inductive(&ConstantEnvironment::empty(), &entries, AdmissionBudget::unlimited(), EnvironmentBudget::unlimited()), fln_checker::admit::InductiveVerdict::Rejected(fln_checker::admit::InductiveRejection::RecursorShape { .. })));
}

#[test]
fn kr600_803_init_prod_refuses_a_forged_num_motives_count() {
    let mut entries = init_prod_entries();
    let declaration = entries[2].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[2] = ConstantEntry::new(
        checker_qualified(&["Prod", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives() + 1,
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_prod_refuses_a_forged_num_minors_count() {
    let mut entries = init_prod_entries();
    let declaration = entries[2].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[2] = ConstantEntry::new(
        checker_qualified(&["Prod", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors() + 1,
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_prod_refuses_a_forged_num_parameters_count() {
    let mut entries = init_prod_entries();
    let declaration = entries[2].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[2] = ConstantEntry::new(
        checker_qualified(&["Prod", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters() + 1,
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_prod_refuses_a_forged_num_rules_count() {
    let mut entries = init_prod_entries();
    let declaration = entries[2].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    let mut rules = metadata.rules().to_vec();
    rules.push(metadata.rules()[0].clone());
    entries[2] = ConstantEntry::new(
        checker_qualified(&["Prod", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                rules,
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_prod_refuses_a_forged_extra_recursor_rule() {
    let mut entries = init_prod_entries();
    let declaration = entries[2].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    let mut rules = metadata.rules().to_vec();
    rules.push(RecursorRule::new(
        checker_qualified(&["Prod", "forged"]),
        0,
        decoded(&Expr::bvar(0).expect("packs")),
    ));
    entries[2] = ConstantEntry::new(
        checker_qualified(&["Prod", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                rules,
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_prod_mk_refuses_a_forged_constructor_index() {
    let mut entries = init_prod_entries();
    let constructor = entries[1].declaration();
    entries[1] = ConstantEntry::new(
        checker_qualified(&["Prod", "mk"]),
        ConstantDeclaration::constructor(
            constructor.level_parameters().to_vec(),
            constructor.type_().clone(),
            constructor.safety(),
            ConstructorDeclaration::new(checker_name("Prod"), 1, 2, 2),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::ConstructorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_prod_mk_refuses_a_forged_constructor_field_count() {
    let mut entries = init_prod_entries();
    let constructor = entries[1].declaration();
    entries[1] = ConstantEntry::new(
        checker_qualified(&["Prod", "mk"]),
        ConstantDeclaration::constructor(
            constructor.level_parameters().to_vec(),
            constructor.type_().clone(),
            constructor.safety(),
            ConstructorDeclaration::new(checker_name("Prod"), 0, 2, 3),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::ConstructorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_prod_refuses_a_forged_num_indices_count() {
    let mut entries = init_prod_entries();
    let declaration = entries[2].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[2] = ConstantEntry::new(
        checker_qualified(&["Prod", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices() + 1,
                metadata.num_motives(),
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_sum_fixture_pins_constructor_indices_parameters_and_fields() {
    let entries = init_sum_entries();
    for (entry, expected_index) in [(&entries[1], 0), (&entries[2], 1)] {
        let metadata = entry
            .declaration()
            .constructor_metadata()
            .expect("fixture constructor metadata");
        assert_eq!(metadata.inductive(), &checker_name("Sum"));
        assert_eq!(metadata.index(), expected_index);
        assert_eq!(metadata.num_parameters(), 2);
        assert_eq!(metadata.num_fields(), 1);
        assert_eq!(entry.declaration().level_parameters().len(), 2);
    }
}

#[test]
fn kr600_803_init_sum_fixture_pins_iota_rule_constructors_and_fields() {
    let entries = init_sum_entries();
    let metadata = entries[3]
        .declaration()
        .recursor_metadata()
        .expect("fixture recursor metadata");
    for (rule, constructor) in [
        (&metadata.rules()[0], entries[1].name()),
        (&metadata.rules()[1], entries[2].name()),
    ] {
        assert_eq!(rule.constructor(), constructor);
        assert_eq!(rule.num_fields(), 1);
    }
}

#[test]
fn kr600_803_init_prod_fixture_pins_constructor_index_parameters_and_fields() {
    let entries = init_prod_entries();
    let constructor = entries[1].declaration();
    let metadata = constructor
        .constructor_metadata()
        .expect("fixture constructor metadata");
    assert_eq!(metadata.inductive(), &checker_name("Prod"));
    assert_eq!(metadata.index(), 0);
    assert_eq!(metadata.num_parameters(), 2);
    assert_eq!(metadata.num_fields(), 2);
    assert_eq!(constructor.level_parameters().len(), 2);
}

#[test]
fn kr600_803_init_prod_fixture_pins_iota_rule_constructor_and_fields() {
    let entries = init_prod_entries();
    let metadata = entries[2]
        .declaration()
        .recursor_metadata()
        .expect("fixture recursor metadata");
    assert_eq!(metadata.rules()[0].constructor(), entries[1].name());
    assert_eq!(metadata.rules()[0].num_fields(), 2);
}

#[test]
fn kr600_803_init_except_fixture_pins_constructor_indices_parameters_and_fields() {
    let entries = init_except_constructor_entries();
    for (entry, expected_index) in [(&entries[0], 0), (&entries[1], 1)] {
        let metadata = entry.declaration().constructor_metadata().expect("fixture constructor metadata");
        assert_eq!(metadata.inductive(), &checker_name("Except"));
        assert_eq!(metadata.index(), expected_index);
        assert_eq!(metadata.num_parameters(), 2);
        assert_eq!(metadata.num_fields(), 1);
        assert_eq!(entry.declaration().level_parameters().len(), 2);
    }
}

#[test]
fn kr600_803_sum_and_prod_recursor_major_premises_close_the_bvar_span() {
    for recursor in [init_sum_entries().remove(3), init_prod_entries().remove(2)] {
        let facts = match inspect(recursor.declaration().type_(), TermBudget::unlimited()) {
            TermOutcome::Complete(facts) => facts,
            other => panic!("fixture recursor inspection must complete: {other:?}"),
        };
        assert_eq!(facts.external_bound_span, 0, "{:?} recursor leaks a major-premise binder", recursor.name());
    }
}

#[test]
fn kr600_803_sum_and_prod_iota_rhs_close_the_bvar_span() {
    for recursor in [init_sum_entries().remove(3), init_prod_entries().remove(2)] {
        let metadata = recursor.declaration().recursor_metadata().expect("fixture recursor metadata");
        for rule in metadata.rules() {
            let facts = match inspect(rule.rhs(), TermBudget::unlimited()) {
                TermOutcome::Complete(facts) => facts,
                other => panic!("fixture iota inspection must complete: {other:?}"),
            };
            assert_eq!(facts.external_bound_span, 0, "{:?} iota RHS leaks a binder", rule.constructor());
        }
    }
}

#[test]
fn kr600_803_nullary_type_enumeration_is_reconstructed_independently() {
    let entries = enumeration_entries(BinderInfo::Implicit);
    let verdict = admit_inductive(
        &ConstantEnvironment::empty(),
        &entries,
        AdmissionBudget::unlimited(),
        EnvironmentBudget::unlimited(),
    );
    assert!(verdict.is_admitted(), "exact Color block: {verdict:?}");
    let fln_checker::admit::InductiveVerdict::Admitted(admission) = verdict else {
        return;
    };
    assert_eq!(admission.members().len(), 4);
    assert_eq!(
        admission.ground(),
        AdmissionGround::InductiveNonrecursiveChecked
    );
}

#[test]
fn kr600_803_color_fixture_pins_recursor_mutual_family_and_k() {
    let entries = enumeration_entries(BinderInfo::Implicit);
    let metadata = entries[3]
        .declaration()
        .recursor_metadata()
        .expect("fixture recursor metadata");
    assert_eq!(metadata.mutual(), &[checker_name("Color")]);
    assert!(!metadata.k());
}

#[test]
fn kr600_803_color_fixture_pins_recursor_levels_motives_minors_and_rules() {
    let entries = enumeration_entries(BinderInfo::Implicit);
    let recursor = entries[3].declaration();
    let metadata = recursor
        .recursor_metadata()
        .expect("fixture recursor metadata");
    assert_eq!(recursor.level_parameters().len(), 1);
    assert_eq!(metadata.num_parameters(), 0);
    assert_eq!(metadata.num_indices(), 0);
    assert_eq!(metadata.num_motives(), 1);
    assert_eq!(metadata.num_minors(), 2);
    assert_eq!(metadata.rules().len(), 2);
}

#[test]
fn kr600_803_color_refuses_a_forged_blue_iota_rule() {
    let mut entries = enumeration_entries(BinderInfo::Implicit);
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Color", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                vec![
                    metadata.rules()[0].clone(),
                    RecursorRule::new(
                        checker_qualified(&["Color", "blue"]),
                        0,
                        decoded(&Expr::bvar(0).expect("packs")),
                    ),
                ],
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_color_refuses_a_forged_num_parameters_count() {
    let mut entries = enumeration_entries(BinderInfo::Implicit);
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Color", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters() + 1,
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_color_refuses_a_forged_num_motives_count() {
    let mut entries = enumeration_entries(BinderInfo::Implicit);
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Color", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives() + 1,
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_color_refuses_a_forged_num_minors_count() {
    let mut entries = enumeration_entries(BinderInfo::Implicit);
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Color", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors() + 1,
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_color_refuses_a_forged_num_rules_count() {
    let mut entries = enumeration_entries(BinderInfo::Implicit);
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    let mut rules = metadata.rules().to_vec();
    rules.push(metadata.rules()[1].clone());
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Color", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                rules,
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_color_refuses_a_forged_extra_recursor_rule() {
    let mut entries = enumeration_entries(BinderInfo::Implicit);
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    let mut rules = metadata.rules().to_vec();
    rules.push(RecursorRule::new(
        checker_qualified(&["Color", "forged"]),
        0,
        decoded(&Expr::bvar(0).expect("packs")),
    ));
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Color", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                rules,
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_color_refuses_a_forged_constructor_field_count() {
    let mut entries = enumeration_entries(BinderInfo::Implicit);
    let constructor = entries[1].declaration();
    entries[1] = ConstantEntry::new(
        checker_qualified(&["Color", "red"]),
        ConstantDeclaration::constructor(
            constructor.level_parameters().to_vec(),
            constructor.type_().clone(),
            constructor.safety(),
            ConstructorDeclaration::new(checker_name("Color"), 0, 0, 1),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::ConstructorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_color_refuses_a_forged_constructor_index() {
    let mut entries = enumeration_entries(BinderInfo::Implicit);
    let constructor = entries[1].declaration();
    entries[1] = ConstantEntry::new(
        checker_qualified(&["Color", "red"]),
        ConstantDeclaration::constructor(
            constructor.level_parameters().to_vec(),
            constructor.type_().clone(),
            constructor.safety(),
            ConstructorDeclaration::new(checker_name("Color"), 1, 0, 0),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::ConstructorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_color_refuses_a_forged_num_indices_count() {
    let mut entries = enumeration_entries(BinderInfo::Implicit);
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Color", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices() + 1,
                metadata.num_motives(),
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_color_fixture_pins_constructor_indices_parameters_and_fields() {
    let entries = enumeration_entries(BinderInfo::Implicit);
    for (entry, expected_index) in [(&entries[1], 0), (&entries[2], 1)] {
        let metadata = entry
            .declaration()
            .constructor_metadata()
            .expect("fixture constructor metadata");
        assert_eq!(metadata.inductive(), &checker_name("Color"));
        assert_eq!(metadata.index(), expected_index);
        assert_eq!(metadata.num_parameters(), 0);
        assert_eq!(metadata.num_fields(), 0);
        assert!(entry.declaration().level_parameters().is_empty());
    }
}

#[test]
fn kr600_803_color_fixture_pins_iota_rule_constructors_and_fields() {
    let entries = enumeration_entries(BinderInfo::Implicit);
    let metadata = entries[3]
        .declaration()
        .recursor_metadata()
        .expect("fixture recursor metadata");
    for (rule, constructor) in [
        (&metadata.rules()[0], entries[1].name()),
        (&metadata.rules()[1], entries[2].name()),
    ] {
        assert_eq!(rule.constructor(), constructor);
        assert_eq!(rule.num_fields(), 0);
    }
}

#[test]
fn kr600_803_color_fixture_pins_iota_rhs_closure() {
    let entries = enumeration_entries(BinderInfo::Implicit);
    let metadata = entries[3]
        .declaration()
        .recursor_metadata()
        .expect("fixture recursor metadata");
    for rule in metadata.rules() {
        let facts = match inspect(rule.rhs(), TermBudget::unlimited()) {
            TermOutcome::Complete(facts) => facts,
            other => panic!("fixture iota inspection must complete: {other:?}"),
        };
        assert_eq!(facts.external_bound_span, 0);
    }
}

#[test]
fn kr600_803_dependent_nonrecursive_fields_are_reconstructed_independently() {
    let entries = dependent_field_inductive_entries();
    let verdict = admit_inductive(
        &ConstantEnvironment::empty(),
        &entries,
        AdmissionBudget::unlimited(),
        EnvironmentBudget::unlimited(),
    );
    assert!(verdict.is_admitted(), "exact Witness block: {verdict:?}");
    let fln_checker::admit::InductiveVerdict::Admitted(admission) = verdict else {
        return;
    };
    assert_eq!(admission.members().len(), 3);
    assert_eq!(
        admission.ground(),
        AdmissionGround::InductiveNonrecursiveChecked
    );
}

#[test]
fn kr600_803_witness_fixture_pins_recursor_mutual_family_and_k() {
    let entries = dependent_field_inductive_entries();
    let metadata = entries[2]
        .declaration()
        .recursor_metadata()
        .expect("fixture recursor metadata");
    assert_eq!(metadata.mutual(), &[checker_name("Witness")]);
    assert!(!metadata.k());
}

#[test]
fn kr600_803_witness_fixture_pins_recursor_levels_motives_minors_and_rules() {
    let entries = dependent_field_inductive_entries();
    let recursor = entries[2].declaration();
    let metadata = recursor
        .recursor_metadata()
        .expect("fixture recursor metadata");
    assert_eq!(recursor.level_parameters().len(), 1);
    assert_eq!(metadata.num_parameters(), 0);
    assert_eq!(metadata.num_indices(), 0);
    assert_eq!(metadata.num_motives(), 1);
    assert_eq!(metadata.num_minors(), 1);
    assert_eq!(metadata.rules().len(), 1);
}

#[test]
fn kr600_803_witness_refuses_a_forged_mk_iota_rule() {
    let mut entries = dependent_field_inductive_entries();
    let declaration = entries[2].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[2] = ConstantEntry::new(
        checker_qualified(&["Witness", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                vec![RecursorRule::new(
                    checker_qualified(&["Witness", "mk"]),
                    2,
                    decoded(&Expr::bvar(0).expect("packs")),
                )],
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_witness_refuses_a_forged_num_parameters_count() {
    let mut entries = dependent_field_inductive_entries();
    let declaration = entries[2].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[2] = ConstantEntry::new(
        checker_qualified(&["Witness", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters() + 1,
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_witness_refuses_a_forged_num_motives_count() {
    let mut entries = dependent_field_inductive_entries();
    let declaration = entries[2].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[2] = ConstantEntry::new(
        checker_qualified(&["Witness", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives() + 1,
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_witness_refuses_a_forged_num_minors_count() {
    let mut entries = dependent_field_inductive_entries();
    let declaration = entries[2].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[2] = ConstantEntry::new(
        checker_qualified(&["Witness", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors() + 1,
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_witness_refuses_a_forged_num_rules_count() {
    let mut entries = dependent_field_inductive_entries();
    let declaration = entries[2].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    let mut rules = metadata.rules().to_vec();
    rules.push(metadata.rules()[0].clone());
    entries[2] = ConstantEntry::new(
        checker_qualified(&["Witness", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                rules,
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_witness_refuses_a_forged_extra_recursor_rule() {
    let mut entries = dependent_field_inductive_entries();
    let declaration = entries[2].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    let mut rules = metadata.rules().to_vec();
    rules.push(RecursorRule::new(
        checker_qualified(&["Witness", "forged"]),
        0,
        decoded(&Expr::bvar(0).expect("packs")),
    ));
    entries[2] = ConstantEntry::new(
        checker_qualified(&["Witness", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                rules,
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_witness_refuses_a_forged_num_indices_count() {
    let mut entries = dependent_field_inductive_entries();
    let declaration = entries[2].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[2] = ConstantEntry::new(
        checker_qualified(&["Witness", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices() + 1,
                metadata.num_motives(),
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_witness_fixture_pins_constructor_index_parameters_and_fields() {
    let entries = dependent_field_inductive_entries();
    let constructor = entries[1].declaration();
    let metadata = constructor
        .constructor_metadata()
        .expect("fixture constructor metadata");
    assert_eq!(metadata.inductive(), &checker_name("Witness"));
    assert_eq!(metadata.index(), 0);
    assert_eq!(metadata.num_parameters(), 0);
    assert_eq!(metadata.num_fields(), 2);
    assert!(constructor.level_parameters().is_empty());
}

#[test]
fn kr600_803_witness_fixture_pins_iota_rule_constructor_and_fields() {
    let entries = dependent_field_inductive_entries();
    let metadata = entries[2]
        .declaration()
        .recursor_metadata()
        .expect("fixture recursor metadata");
    assert_eq!(metadata.rules()[0].constructor(), entries[1].name());
    assert_eq!(metadata.rules()[0].num_fields(), 2);
}

#[test]
fn kr600_803_witness_fixture_pins_iota_rhs_closure() {
    let entries = dependent_field_inductive_entries();
    let rule = &entries[2]
        .declaration()
        .recursor_metadata()
        .expect("fixture recursor metadata")
        .rules()[0];
    let facts = match inspect(rule.rhs(), TermBudget::unlimited()) {
        TermOutcome::Complete(facts) => facts,
        other => panic!("fixture iota inspection must complete: {other:?}"),
    };
    assert_eq!(facts.external_bound_span, 0);
}

#[test]
fn kr600_803_direct_self_recursion_is_reconstructed_independently() {
    let entries = nat_entries();
    let verdict = admit_inductive(
        &ConstantEnvironment::empty(),
        &entries,
        AdmissionBudget::unlimited(),
        EnvironmentBudget::unlimited(),
    );
    assert!(verdict.is_admitted(), "exact Nat block: {verdict:?}");
    let fln_checker::admit::InductiveVerdict::Admitted(admission) = verdict else {
        return;
    };
    assert_eq!(admission.members().len(), 4);
}

#[test]
fn kr600_803_init_nat_refuses_a_forged_succ_iota_rule() {
    let mut entries = nat_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Nat", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                vec![
                    metadata.rules()[0].clone(),
                    RecursorRule::new(
                        checker_qualified(&["Nat", "succ"]),
                        1,
                        decoded(&Expr::bvar(0).expect("packs")),
                    ),
                ],
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_nat_refuses_a_forged_num_motives_count() {
    let mut entries = nat_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Nat", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives() + 1,
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_nat_refuses_a_forged_num_minors_count() {
    let mut entries = nat_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Nat", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors() + 1,
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_nat_refuses_a_forged_num_rules_count() {
    let mut entries = nat_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    let mut rules = metadata.rules().to_vec();
    rules.push(metadata.rules()[1].clone());
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Nat", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                rules,
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_nat_refuses_a_forged_extra_recursor_rule() {
    let mut entries = nat_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    let mut rules = metadata.rules().to_vec();
    rules.push(RecursorRule::new(
        checker_qualified(&["Nat", "forged"]),
        0,
        decoded(&Expr::bvar(0).expect("packs")),
    ));
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Nat", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                rules,
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_nat_zero_refuses_a_forged_constructor_field_count() {
    let mut entries = nat_entries();
    let constructor = entries[1].declaration();
    entries[1] = ConstantEntry::new(
        checker_qualified(&["Nat", "zero"]),
        ConstantDeclaration::constructor(
            constructor.level_parameters().to_vec(),
            constructor.type_().clone(),
            constructor.safety(),
            ConstructorDeclaration::new(checker_name("Nat"), 0, 0, 1),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::ConstructorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_nat_succ_refuses_a_forged_constructor_field_count() {
    let mut entries = nat_entries();
    let constructor = entries[2].declaration();
    entries[2] = ConstantEntry::new(
        checker_qualified(&["Nat", "succ"]),
        ConstantDeclaration::constructor(
            constructor.level_parameters().to_vec(),
            constructor.type_().clone(),
            constructor.safety(),
            ConstructorDeclaration::new(checker_name("Nat"), 1, 0, 2),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::ConstructorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_nat_succ_refuses_a_forged_constructor_index() {
    let mut entries = nat_entries();
    let constructor = entries[2].declaration();
    entries[2] = ConstantEntry::new(
        checker_qualified(&["Nat", "succ"]),
        ConstantDeclaration::constructor(
            constructor.level_parameters().to_vec(),
            constructor.type_().clone(),
            constructor.safety(),
            ConstructorDeclaration::new(checker_name("Nat"), 0, 0, 1),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::ConstructorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_nat_refuses_a_forged_num_parameters_count() {
    let mut entries = nat_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Nat", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters() + 1,
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_nat_refuses_a_forged_num_indices_count() {
    let mut entries = nat_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Nat", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices() + 1,
                metadata.num_motives(),
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_nat_fixture_pins_recursor_levels_motives_minors_and_rules() {
    let entries = nat_entries();
    let recursor = entries[3].declaration();
    let metadata = recursor.recursor_metadata().expect("fixture recursor metadata");
    assert_eq!(recursor.level_parameters().len(), 1);
    assert_eq!(metadata.num_parameters(), 0);
    assert_eq!(metadata.num_indices(), 0);
    assert_eq!(metadata.num_motives(), 1);
    assert_eq!(metadata.num_minors(), 2);
    assert_eq!(metadata.rules().len(), 2);
    assert_eq!(metadata.rules()[0].constructor(), &checker_qualified(&["Nat", "zero"]));
    assert_eq!(metadata.rules()[0].num_fields(), 0);
    assert_eq!(metadata.rules()[1].constructor(), &checker_qualified(&["Nat", "succ"]));
    assert_eq!(metadata.rules()[1].num_fields(), 1);
}

#[test]
fn kr600_803_init_nat_fixture_pins_recursor_mutual_family_and_k() {
    let entries = nat_entries();
    let metadata = entries[3]
        .declaration()
        .recursor_metadata()
        .expect("fixture recursor metadata");
    assert_eq!(metadata.mutual(), &[checker_name("Nat")]);
    assert!(!metadata.k());
}

#[test]
fn kr600_803_init_nat_fixture_pins_constructor_indices_parameters_and_fields() {
    let entries = nat_entries();
    for (entry, expected_index, expected_fields) in [(&entries[1], 0, 0), (&entries[2], 1, 1)] {
        let metadata = entry.declaration().constructor_metadata().expect("fixture constructor metadata");
        assert_eq!(metadata.inductive(), &checker_name("Nat"));
        assert_eq!(metadata.index(), expected_index);
        assert_eq!(metadata.num_parameters(), 0);
        assert_eq!(metadata.num_fields(), expected_fields);
        assert!(entry.declaration().level_parameters().is_empty());
    }
}

#[test]
fn kr600_803_init_nat_fixture_pins_iota_rule_constructors_and_fields() {
    let entries = nat_entries();
    let metadata = entries[3]
        .declaration()
        .recursor_metadata()
        .expect("fixture recursor metadata");
    for (rule, constructor, expected_fields) in [
        (&metadata.rules()[0], entries[1].name(), 0),
        (&metadata.rules()[1], entries[2].name(), 1),
    ] {
        assert_eq!(rule.constructor(), constructor);
        assert_eq!(rule.num_fields(), expected_fields);
    }
}

#[test]
fn kr600_803_init_nat_fixture_pins_iota_rhs_closure() {
    let entries = nat_entries();
    let metadata = entries[3]
        .declaration()
        .recursor_metadata()
        .expect("fixture recursor metadata");
    for rule in metadata.rules() {
        let facts = match inspect(rule.rhs(), TermBudget::unlimited()) {
            TermOutcome::Complete(facts) => facts,
            other => panic!("fixture iota inspection must complete: {other:?}"),
        };
        assert_eq!(facts.external_bound_span, 0);
    }
}

#[test]
fn kr600_803_init_option_universes_parameters_and_rules_are_reconstructed() {
    let entries = init_option_entries();
    let verdict = admit_inductive(
        &ConstantEnvironment::empty(),
        &entries,
        AdmissionBudget::unlimited(),
        EnvironmentBudget::unlimited(),
    );
    assert!(
        verdict.is_admitted(),
        "exact Init.Option block: {verdict:?}"
    );
    let fln_checker::admit::InductiveVerdict::Admitted(admission) = verdict else {
        return;
    };
    assert_eq!(admission.members().len(), 4);
}

#[test]
fn kr600_803_init_option_refuses_a_forged_some_iota_rule() {
    let mut entries = init_option_entries();
    let recursor = entries[3].declaration();
    let metadata = recursor
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Option", "rec"]),
        ConstantDeclaration::recursor(
            recursor.level_parameters().to_vec(),
            recursor.type_().clone(),
            recursor.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                vec![
                    metadata.rules()[0].clone(),
                    RecursorRule::new(
                        checker_qualified(&["Option", "some"]),
                        1,
                        decoded(&Expr::bvar(0).expect("packs")),
                    ),
                ],
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_option_refuses_a_forged_num_rules_count() {
    let mut entries = init_option_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    let mut rules = metadata.rules().to_vec();
    rules.push(metadata.rules()[1].clone());
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Option", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                rules,
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_option_refuses_a_forged_num_motives_count() {
    let mut entries = init_option_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Option", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives() + 1,
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_option_refuses_a_forged_num_minors_count() {
    let mut entries = init_option_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Option", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors() + 1,
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_option_refuses_a_forged_num_indices_count() {
    let mut entries = init_option_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Option", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices() + 1,
                metadata.num_motives(),
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_option_refuses_a_forged_extra_recursor_rule() {
    let mut entries = init_option_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    let mut rules = metadata.rules().to_vec();
    rules.push(RecursorRule::new(
        checker_qualified(&["Option", "forged"]),
        0,
        decoded(&Expr::bvar(0).expect("packs")),
    ));
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Option", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                rules,
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_option_refuses_a_forged_num_parameters_count() {
    let mut entries = init_option_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Option", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters() + 1,
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_option_fixture_pins_recursor_levels_motives_minors_and_rules() {
    let entries = init_option_entries();
    let recursor = entries[3].declaration();
    let metadata = recursor.recursor_metadata().expect("fixture recursor metadata");
    assert_eq!(recursor.level_parameters().len(), 2);
    assert_eq!(metadata.num_parameters(), 1);
    assert_eq!(metadata.num_indices(), 0);
    assert_eq!(metadata.num_motives(), 1);
    assert_eq!(metadata.num_minors(), 2);
    assert_eq!(metadata.rules().len(), 2);
    assert_eq!(metadata.rules()[0].constructor(), &checker_qualified(&["Option", "none"]));
    assert_eq!(metadata.rules()[0].num_fields(), 0);
    assert_eq!(metadata.rules()[1].constructor(), &checker_qualified(&["Option", "some"]));
    assert_eq!(metadata.rules()[1].num_fields(), 1);
}

#[test]
fn kr600_803_init_option_fixture_pins_recursor_mutual_family_and_k() {
    let entries = init_option_entries();
    let metadata = entries[3]
        .declaration()
        .recursor_metadata()
        .expect("fixture recursor metadata");
    assert_eq!(metadata.mutual(), &[checker_name("Option")]);
    assert!(!metadata.k());
}

#[test]
fn kr600_803_init_option_fixture_pins_constructor_indices_parameters_and_fields() {
    let entries = init_option_entries();
    for (entry, expected_index, expected_fields) in [(&entries[1], 0, 0), (&entries[2], 1, 1)] {
        let metadata = entry
            .declaration()
            .constructor_metadata()
            .expect("fixture constructor metadata");
        assert_eq!(metadata.inductive(), &checker_name("Option"));
        assert_eq!(metadata.index(), expected_index);
        assert_eq!(metadata.num_parameters(), 1);
        assert_eq!(metadata.num_fields(), expected_fields);
        assert_eq!(entry.declaration().level_parameters().len(), 1);
    }
}

#[test]
fn kr600_803_init_option_fixture_pins_iota_rule_constructors_and_fields() {
    let entries = init_option_entries();
    let metadata = entries[3]
        .declaration()
        .recursor_metadata()
        .expect("fixture recursor metadata");
    for (rule, constructor, expected_fields) in [
        (&metadata.rules()[0], entries[1].name(), 0),
        (&metadata.rules()[1], entries[2].name(), 1),
    ] {
        assert_eq!(rule.constructor(), constructor);
        assert_eq!(rule.num_fields(), expected_fields);
    }
}

#[test]
fn kr600_803_init_option_fixture_pins_iota_rhs_closure() {
    let entries = init_option_entries();
    let metadata = entries[3]
        .declaration()
        .recursor_metadata()
        .expect("fixture recursor metadata");
    for rule in metadata.rules() {
        let facts = match inspect(rule.rhs(), TermBudget::unlimited()) {
            TermOutcome::Complete(facts) => facts,
            other => panic!("fixture iota inspection must complete: {other:?}"),
        };
        assert_eq!(facts.external_bound_span, 0);
    }
}

#[test]
fn kr600_803_init_list_recursive_parameter_and_iota_rules_are_reconstructed() {
    let entries = init_list_entries();
    let verdict = admit_inductive(
        &ConstantEnvironment::empty(),
        &entries,
        AdmissionBudget::unlimited(),
        EnvironmentBudget::unlimited(),
    );
    assert!(verdict.is_admitted(), "exact Init.List block: {verdict:?}");
    let fln_checker::admit::InductiveVerdict::Admitted(admission) = verdict else {
        return;
    };
    assert_eq!(admission.members().len(), 4);
}

#[test]
fn kr600_803_init_list_refuses_a_forged_cons_iota_rule() {
    let mut entries = init_list_entries();
    let recursor = entries[3].declaration();
    let metadata = recursor
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[3] = ConstantEntry::new(
        checker_qualified(&["List", "rec"]),
        ConstantDeclaration::recursor(
            recursor.level_parameters().to_vec(),
            recursor.type_().clone(),
            recursor.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                vec![
                    metadata.rules()[0].clone(),
                    RecursorRule::new(
                        checker_qualified(&["List", "cons"]),
                        2,
                        decoded(&Expr::bvar(0).expect("packs")),
                    ),
                ],
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_list_refuses_a_forged_num_motives_count() {
    let mut entries = init_list_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[3] = ConstantEntry::new(
        checker_qualified(&["List", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives() + 1,
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_list_refuses_a_forged_num_minors_count() {
    let mut entries = init_list_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[3] = ConstantEntry::new(
        checker_qualified(&["List", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors() + 1,
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_list_refuses_a_forged_num_rules_count() {
    let mut entries = init_list_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    let mut rules = metadata.rules().to_vec();
    rules.push(metadata.rules()[1].clone());
    entries[3] = ConstantEntry::new(
        checker_qualified(&["List", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                rules,
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_list_refuses_a_forged_extra_recursor_rule() {
    let mut entries = init_list_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    let mut rules = metadata.rules().to_vec();
    rules.push(RecursorRule::new(
        checker_qualified(&["List", "forged"]),
        0,
        decoded(&Expr::bvar(0).expect("packs")),
    ));
    entries[3] = ConstantEntry::new(
        checker_qualified(&["List", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                rules,
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_list_refuses_a_forged_num_indices_count() {
    let mut entries = init_list_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[3] = ConstantEntry::new(
        checker_qualified(&["List", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices() + 1,
                metadata.num_motives(),
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_list_refuses_a_forged_num_parameters_count() {
    let mut entries = init_list_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[3] = ConstantEntry::new(
        checker_qualified(&["List", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters() + 1,
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_list_fixture_pins_recursor_levels_motives_minors_and_rules() {
    let entries = init_list_entries();
    let recursor = entries[3].declaration();
    let metadata = recursor.recursor_metadata().expect("fixture recursor metadata");
    assert_eq!(recursor.level_parameters().len(), 2);
    assert_eq!(metadata.num_parameters(), 1);
    assert_eq!(metadata.num_indices(), 0);
    assert_eq!(metadata.num_motives(), 1);
    assert_eq!(metadata.num_minors(), 2);
    assert_eq!(metadata.rules().len(), 2);
    assert_eq!(metadata.rules()[0].constructor(), &checker_qualified(&["List", "nil"]));
    assert_eq!(metadata.rules()[0].num_fields(), 0);
    assert_eq!(metadata.rules()[1].constructor(), &checker_qualified(&["List", "cons"]));
    assert_eq!(metadata.rules()[1].num_fields(), 2);
}

#[test]
fn kr600_803_init_list_fixture_pins_recursor_mutual_family_and_k() {
    let entries = init_list_entries();
    let metadata = entries[3]
        .declaration()
        .recursor_metadata()
        .expect("fixture recursor metadata");
    assert_eq!(metadata.mutual(), &[checker_name("List")]);
    assert!(!metadata.k());
}

#[test]
fn kr600_803_init_list_fixture_pins_constructor_indices_parameters_and_fields() {
    let entries = init_list_entries();
    for (entry, expected_index, expected_fields) in
        [(&entries[1], 0, 0), (&entries[2], 1, 2)]
    {
        let metadata = entry
            .declaration()
            .constructor_metadata()
            .expect("fixture constructor metadata");
        assert_eq!(metadata.inductive(), &checker_name("List"));
        assert_eq!(metadata.index(), expected_index);
        assert_eq!(metadata.num_parameters(), 1);
        assert_eq!(metadata.num_fields(), expected_fields);
        assert_eq!(entry.declaration().level_parameters().len(), 1);
    }
}

#[test]
fn kr600_803_init_list_fixture_pins_iota_rule_constructors_and_fields() {
    let entries = init_list_entries();
    let metadata = entries[3]
        .declaration()
        .recursor_metadata()
        .expect("fixture recursor metadata");
    for (rule, constructor, expected_fields) in [
        (&metadata.rules()[0], entries[1].name(), 0),
        (&metadata.rules()[1], entries[2].name(), 2),
    ] {
        assert_eq!(rule.constructor(), constructor);
        assert_eq!(rule.num_fields(), expected_fields);
    }
}

#[test]
fn kr600_803_init_list_fixture_pins_iota_rhs_closure() {
    let entries = init_list_entries();
    let metadata = entries[3]
        .declaration()
        .recursor_metadata()
        .expect("fixture recursor metadata");
    for rule in metadata.rules() {
        let facts = match inspect(rule.rhs(), TermBudget::unlimited()) {
            TermOutcome::Complete(facts) => facts,
            other => panic!("fixture iota inspection must complete: {other:?}"),
        };
        assert_eq!(facts.external_bound_span, 0);
    }
}

#[test]
fn kr600_803_init_empty_eliminator_is_reconstructed_independently() {
    let entries = init_empty_entries();
    let verdict = admit_inductive(
        &ConstantEnvironment::empty(),
        &entries,
        AdmissionBudget::unlimited(),
        EnvironmentBudget::unlimited(),
    );
    assert!(verdict.is_admitted(), "exact Init.Empty block: {verdict:?}");
    let fln_checker::admit::InductiveVerdict::Admitted(admission) = verdict else {
        return;
    };
    assert_eq!(admission.members().len(), 2);
}

#[test]
fn kr600_803_init_empty_refuses_a_forged_recursor_rule() {
    let mut entries = init_empty_entries();
    let recursor = entries[1].declaration();
    let metadata = recursor
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[1] = ConstantEntry::new(
        checker_qualified(&["Empty", "rec"]),
        ConstantDeclaration::recursor(
            recursor.level_parameters().to_vec(),
            recursor.type_().clone(),
            recursor.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                vec![RecursorRule::new(
                    checker_qualified(&["Empty", "forged"]),
                    0,
                    decoded(&Expr::bvar(0).expect("packs")),
                )],
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_empty_refuses_a_forged_num_motives_count() {
    let mut entries = init_empty_entries();
    let declaration = entries[1].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[1] = ConstantEntry::new(
        checker_qualified(&["Empty", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives() + 1,
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_empty_refuses_a_forged_num_minors_count() {
    let mut entries = init_empty_entries();
    let declaration = entries[1].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[1] = ConstantEntry::new(
        checker_qualified(&["Empty", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors() + 1,
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_empty_refuses_a_forged_num_parameters_count() {
    let mut entries = init_empty_entries();
    let declaration = entries[1].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[1] = ConstantEntry::new(
        checker_qualified(&["Empty", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters() + 1,
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_empty_fixture_pins_recursor_levels_motives_minors_and_rules() {
    let entries = init_empty_entries();
    let recursor = entries[1].declaration();
    let metadata = recursor.recursor_metadata().expect("fixture recursor metadata");
    assert_eq!(recursor.level_parameters().len(), 1);
    assert_eq!(metadata.num_parameters(), 0);
    assert_eq!(metadata.num_indices(), 0);
    assert_eq!(metadata.num_motives(), 1);
    assert_eq!(metadata.num_minors(), 0);
    assert!(metadata.rules().is_empty());
}

#[test]
fn kr600_803_init_empty_fixture_pins_recursor_mutual_family_and_k() {
    let entries = init_empty_entries();
    let metadata = entries[1]
        .declaration()
        .recursor_metadata()
        .expect("fixture recursor metadata");
    assert_eq!(metadata.mutual(), &[checker_name("Empty")]);
    assert!(!metadata.k());
}

#[test]
fn kr600_803_init_empty_fixture_pins_eliminator_bvar_closure() {
    let entries = init_empty_entries();
    let facts = match inspect(entries[1].declaration().type_(), TermBudget::unlimited()) {
        TermOutcome::Complete(facts) => facts,
        other => panic!("fixture eliminator inspection must complete: {other:?}"),
    };
    assert_eq!(facts.external_bound_span, 0);
}

#[test]
fn kr600_803_init_false_eliminator_is_reconstructed_independently() {
    let entries = init_false_entries();
    let verdict = admit_inductive(&ConstantEnvironment::empty(), &entries, AdmissionBudget::unlimited(), EnvironmentBudget::unlimited());
    assert!(verdict.is_admitted(), "exact Init.False block: {verdict:?}");
}

#[test]
fn kr600_803_init_false_refuses_a_forged_recursor_rule() {
    let mut entries = init_false_entries();
    let declaration = entries[1].declaration();
    let metadata = declaration.recursor_metadata().expect("fixture recursor metadata");
    entries[1] = ConstantEntry::new(checker_qualified(&["False", "rec"]), ConstantDeclaration::recursor(
        declaration.level_parameters().to_vec(), declaration.type_().clone(), declaration.safety(),
        RecursorDeclaration::new(metadata.mutual().to_vec(), metadata.num_parameters(), metadata.num_indices(), metadata.num_motives(), metadata.num_minors(), vec![RecursorRule::new(checker_qualified(&["False", "forged"]), 0, decoded(&Expr::bvar(0).expect("packs")))], metadata.k()),
    ));
    assert!(matches!(admit_inductive(&ConstantEnvironment::empty(), &entries, AdmissionBudget::unlimited(), EnvironmentBudget::unlimited()), fln_checker::admit::InductiveVerdict::Rejected(fln_checker::admit::InductiveRejection::RecursorShape { .. })));
}

#[test]
fn kr600_803_init_false_fixture_pins_recursor_levels_motives_minors_and_rules() {
    let entries = init_false_entries();
    let recursor = entries[1].declaration();
    let metadata = recursor.recursor_metadata().expect("fixture recursor metadata");
    assert_eq!(recursor.level_parameters().len(), 1);
    assert_eq!(metadata.num_parameters(), 0);
    assert_eq!(metadata.num_indices(), 0);
    assert_eq!(metadata.num_motives(), 1);
    assert_eq!(metadata.num_minors(), 0);
    assert!(metadata.rules().is_empty());
}

#[test]
fn kr600_803_init_false_fixture_pins_recursor_mutual_family_and_k() {
    let entries = init_false_entries();
    let metadata = entries[1]
        .declaration()
        .recursor_metadata()
        .expect("fixture recursor metadata");
    assert_eq!(metadata.mutual(), &[checker_name("False")]);
    assert!(!metadata.k());
}

#[test]
fn kr600_803_init_false_fixture_pins_eliminator_bvar_closure() {
    let entries = init_false_entries();
    let facts = match inspect(entries[1].declaration().type_(), TermBudget::unlimited()) {
        TermOutcome::Complete(facts) => facts,
        other => panic!("fixture eliminator inspection must complete: {other:?}"),
    };
    assert_eq!(facts.external_bound_span, 0);
}

#[test]
fn kr600_803_init_pempty_universes_and_eliminator_are_reconstructed() {
    let entries = init_pempty_entries();
    let verdict = admit_inductive(
        &ConstantEnvironment::empty(),
        &entries,
        AdmissionBudget::unlimited(),
        EnvironmentBudget::unlimited(),
    );
    assert!(
        verdict.is_admitted(),
        "exact Init.PEmpty block: {verdict:?}"
    );
    let fln_checker::admit::InductiveVerdict::Admitted(admission) = verdict else {
        return;
    };
    assert_eq!(admission.members().len(), 2);
}

#[test]
fn kr600_803_init_pempty_refuses_a_forged_recursor_rule() {
    let mut entries = init_pempty_entries();
    let recursor = entries[1].declaration();
    let metadata = recursor
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[1] = ConstantEntry::new(
        checker_qualified(&["PEmpty", "rec"]),
        ConstantDeclaration::recursor(
            recursor.level_parameters().to_vec(),
            recursor.type_().clone(),
            recursor.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                vec![RecursorRule::new(
                    checker_qualified(&["PEmpty", "forged"]),
                    0,
                    decoded(&Expr::bvar(0).expect("packs")),
                )],
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_pempty_refuses_a_forged_num_parameters_count() {
    let mut entries = init_pempty_entries();
    let declaration = entries[1].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[1] = ConstantEntry::new(
        checker_qualified(&["PEmpty", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters() + 1,
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_pempty_fixture_pins_recursor_levels_motives_minors_and_rules() {
    let entries = init_pempty_entries();
    let recursor = entries[1].declaration();
    let metadata = recursor.recursor_metadata().expect("fixture recursor metadata");
    assert_eq!(recursor.level_parameters().len(), 2);
    assert_eq!(metadata.num_parameters(), 0);
    assert_eq!(metadata.num_indices(), 0);
    assert_eq!(metadata.num_motives(), 1);
    assert_eq!(metadata.num_minors(), 0);
    assert!(metadata.rules().is_empty());
}

#[test]
fn kr600_803_init_pempty_fixture_pins_recursor_mutual_family_and_k() {
    let entries = init_pempty_entries();
    let metadata = entries[1]
        .declaration()
        .recursor_metadata()
        .expect("fixture recursor metadata");
    assert_eq!(metadata.mutual(), &[checker_name("PEmpty")]);
    assert!(!metadata.k());
}

#[test]
fn kr600_803_init_pempty_fixture_pins_eliminator_bvar_closure() {
    let entries = init_pempty_entries();
    let facts = match inspect(entries[1].declaration().type_(), TermBudget::unlimited()) {
        TermOutcome::Complete(facts) => facts,
        other => panic!("fixture eliminator inspection must complete: {other:?}"),
    };
    assert_eq!(facts.external_bound_span, 0);
}

#[test]
fn kr600_803_init_or_proposition_branches_are_reconstructed() {
    let entries = init_or_entries();
    let verdict = admit_inductive(
        &ConstantEnvironment::empty(),
        &entries,
        AdmissionBudget::unlimited(),
        EnvironmentBudget::unlimited(),
    );
    assert!(verdict.is_admitted(), "exact Init.Or block: {verdict:?}");
    let fln_checker::admit::InductiveVerdict::Admitted(admission) = verdict else {
        return;
    };
    assert_eq!(admission.members().len(), 4);
}

#[test]
fn kr600_803_init_or_refuses_a_forged_inr_iota_rule() {
    let mut entries = init_or_entries();
    let recursor = entries[3].declaration();
    let metadata = recursor
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Or", "rec"]),
        ConstantDeclaration::recursor(
            recursor.level_parameters().to_vec(),
            recursor.type_().clone(),
            recursor.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                vec![
                    metadata.rules()[0].clone(),
                    RecursorRule::new(
                        checker_qualified(&["Or", "inr"]),
                        1,
                        decoded(&Expr::bvar(0).expect("packs")),
                    ),
                ],
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_or_refuses_a_forged_num_motives_count() {
    let mut entries = init_or_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Or", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives() + 1,
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_or_refuses_a_forged_num_minors_count() {
    let mut entries = init_or_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Or", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors() + 1,
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_or_refuses_a_forged_num_parameters_count() {
    let mut entries = init_or_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Or", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters() + 1,
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_or_refuses_a_forged_num_indices_count() {
    let mut entries = init_or_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Or", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices() + 1,
                metadata.num_motives(),
                metadata.num_minors(),
                metadata.rules().to_vec(),
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_or_refuses_a_forged_extra_recursor_rule() {
    let mut entries = init_or_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    let mut rules = metadata.rules().to_vec();
    rules.push(RecursorRule::new(
        checker_qualified(&["Or", "forged"]),
        0,
        decoded(&Expr::bvar(0).expect("packs")),
    ));
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Or", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                rules,
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_or_inl_refuses_a_forged_constructor_index() {
    let mut entries = init_or_entries();
    let constructor = entries[1].declaration();
    entries[1] = ConstantEntry::new(
        checker_qualified(&["Or", "inl"]),
        ConstantDeclaration::constructor(
            constructor.level_parameters().to_vec(),
            constructor.type_().clone(),
            constructor.safety(),
            ConstructorDeclaration::new(checker_name("Or"), 1, 2, 1),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::ConstructorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_or_inl_refuses_a_forged_constructor_field_count() {
    let mut entries = init_or_entries();
    let constructor = entries[1].declaration();
    entries[1] = ConstantEntry::new(
        checker_qualified(&["Or", "inl"]),
        ConstantDeclaration::constructor(
            constructor.level_parameters().to_vec(),
            constructor.type_().clone(),
            constructor.safety(),
            ConstructorDeclaration::new(checker_name("Or"), 0, 2, 2),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::ConstructorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_or_inr_refuses_a_forged_constructor_index() {
    let mut entries = init_or_entries();
    let constructor = entries[2].declaration();
    entries[2] = ConstantEntry::new(
        checker_qualified(&["Or", "inr"]),
        ConstantDeclaration::constructor(
            constructor.level_parameters().to_vec(),
            constructor.type_().clone(),
            constructor.safety(),
            ConstructorDeclaration::new(checker_name("Or"), 0, 2, 1),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::ConstructorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_or_refuses_a_forged_num_rules_count() {
    let mut entries = init_or_entries();
    let declaration = entries[3].declaration();
    let metadata = declaration
        .recursor_metadata()
        .expect("fixture recursor metadata");
    let mut rules = metadata.rules().to_vec();
    rules.push(metadata.rules()[1].clone());
    entries[3] = ConstantEntry::new(
        checker_qualified(&["Or", "rec"]),
        ConstantDeclaration::recursor(
            declaration.level_parameters().to_vec(),
            declaration.type_().clone(),
            declaration.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                rules,
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
}

#[test]
fn kr600_803_init_or_fixture_pins_recursor_levels_motives_minors_and_rules() {
    let entries = init_or_entries();
    let recursor = entries[3].declaration();
    let metadata = recursor.recursor_metadata().expect("fixture recursor metadata");
    assert!(recursor.level_parameters().is_empty());
    assert_eq!(metadata.num_parameters(), 2);
    assert_eq!(metadata.num_indices(), 0);
    assert_eq!(metadata.num_motives(), 1);
    assert_eq!(metadata.num_minors(), 2);
    assert_eq!(metadata.rules().len(), 2);
    assert_eq!(metadata.rules()[0].constructor(), &checker_qualified(&["Or", "inl"]));
    assert_eq!(metadata.rules()[0].num_fields(), 1);
    assert_eq!(metadata.rules()[1].constructor(), &checker_qualified(&["Or", "inr"]));
    assert_eq!(metadata.rules()[1].num_fields(), 1);
}

#[test]
fn kr600_803_init_or_fixture_pins_recursor_mutual_family_and_k() {
    let entries = init_or_entries();
    let metadata = entries[3]
        .declaration()
        .recursor_metadata()
        .expect("fixture recursor metadata");
    assert_eq!(metadata.mutual(), &[checker_name("Or")]);
    assert!(!metadata.k());
}

#[test]
fn kr600_803_init_or_fixture_pins_constructor_indices_parameters_and_fields() {
    let entries = init_or_entries();
    for (entry, expected_index) in [(&entries[1], 0), (&entries[2], 1)] {
        let metadata = entry
            .declaration()
            .constructor_metadata()
            .expect("fixture constructor metadata");
        assert_eq!(metadata.inductive(), &checker_name("Or"));
        assert_eq!(metadata.index(), expected_index);
        assert_eq!(metadata.num_parameters(), 2);
        assert_eq!(metadata.num_fields(), 1);
        assert!(entry.declaration().level_parameters().is_empty());
    }
}

#[test]
fn kr600_803_init_or_fixture_pins_iota_rule_constructors_and_fields() {
    let entries = init_or_entries();
    let metadata = entries[3]
        .declaration()
        .recursor_metadata()
        .expect("fixture recursor metadata");
    for (rule, constructor) in [
        (&metadata.rules()[0], entries[1].name()),
        (&metadata.rules()[1], entries[2].name()),
    ] {
        assert_eq!(rule.constructor(), constructor);
        assert_eq!(rule.num_fields(), 1);
    }
}

#[test]
fn kr600_803_init_or_fixture_pins_iota_rhs_closure() {
    let entries = init_or_entries();
    let metadata = entries[3]
        .declaration()
        .recursor_metadata()
        .expect("fixture recursor metadata");
    for rule in metadata.rules() {
        let facts = match inspect(rule.rhs(), TermBudget::unlimited()) {
            TermOutcome::Complete(facts) => facts,
            other => panic!("fixture iota inspection must complete: {other:?}"),
        };
        assert_eq!(facts.external_bound_span, 0);
    }
}

#[test]
fn kr600_803_direct_recursion_reconstructs_iota_and_defers_indirect_fields() {
    let mut forged_rule = nat_entries();
    let recursor = forged_rule[3].declaration();
    let metadata = recursor
        .recursor_metadata()
        .expect("fixture recursor metadata");
    forged_rule[3] = ConstantEntry::new(
        checker_qualified(&["Nat", "rec"]),
        ConstantDeclaration::recursor(
            recursor.level_parameters().to_vec(),
            recursor.type_().clone(),
            recursor.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                vec![
                    metadata.rules()[0].clone(),
                    RecursorRule::new(
                        checker_qualified(&["Nat", "succ"]),
                        1,
                        decoded(&Expr::bvar(0).expect("packs")),
                    ),
                ],
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &forged_rule,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));

    let mut indirect = nat_entries();
    let indirect_field = primary_pi(
        "f",
        BinderInfo::Default,
        Expr::const_(primary_name("Nat"), Vec::new()),
        Expr::const_(primary_name("Nat"), Vec::new()),
    );
    indirect[2] = ConstantEntry::new(
        checker_qualified(&["Nat", "succ"]),
        ConstantDeclaration::constructor(
            Vec::new(),
            decoded(&primary_pi(
                "step",
                BinderInfo::Default,
                indirect_field,
                Expr::const_(primary_name("Nat"), Vec::new()),
            )),
            ConstantSafety::Safe,
            ConstructorDeclaration::new(checker_name("Nat"), 1, 0, 1),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &indirect,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Deferred(
            fln_checker::admit::InductiveSupportLimit::Recursive
        )
    ));
}

#[test]
fn kr600_803_field_metadata_recursion_and_rule_forgery_are_refused() {
    let mut wrong_count = dependent_field_inductive_entries();
    let constructor = wrong_count[1].declaration();
    wrong_count[1] = ConstantEntry::new(
        checker_qualified(&["Witness", "mk"]),
        ConstantDeclaration::constructor(
            constructor.level_parameters().to_vec(),
            constructor.type_().clone(),
            constructor.safety(),
            ConstructorDeclaration::new(checker_name("Witness"), 0, 0, 1),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &wrong_count,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::ConstructorShape { .. }
        )
    ));

    let mut recursive_field = dependent_field_inductive_entries();
    let recursive_type = primary_pi(
        "recursive",
        BinderInfo::Default,
        Expr::const_(primary_name("Witness"), Vec::new()),
        Expr::const_(primary_name("Witness"), Vec::new()),
    );
    recursive_field[1] = ConstantEntry::new(
        checker_qualified(&["Witness", "mk"]),
        ConstantDeclaration::constructor(
            Vec::new(),
            decoded(&recursive_type),
            ConstantSafety::Safe,
            ConstructorDeclaration::new(checker_name("Witness"), 0, 0, 1),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &recursive_field,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::ConstructorShape { .. }
        )
    ));

    let mut bad_rule = dependent_field_inductive_entries();
    let recursor = bad_rule[2].declaration();
    let metadata = recursor
        .recursor_metadata()
        .expect("fixture recursor metadata");
    bad_rule[2] = ConstantEntry::new(
        checker_qualified(&["Witness", "rec"]),
        ConstantDeclaration::recursor(
            recursor.level_parameters().to_vec(),
            recursor.type_().clone(),
            recursor.safety(),
            RecursorDeclaration::new(
                metadata.mutual().to_vec(),
                metadata.num_parameters(),
                metadata.num_indices(),
                metadata.num_motives(),
                metadata.num_minors(),
                vec![RecursorRule::new(
                    checker_qualified(&["Witness", "mk"]),
                    2,
                    decoded(&Expr::bvar(0).expect("packs")),
                )],
                metadata.k(),
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &bad_rule,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));

    assert!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &dependent_field_inductive_entries(),
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        )
        .is_admitted()
    );
}

#[test]
fn kr600_803_field_environment_exhaustion_is_a_nonanswer() {
    let entries = dependent_field_inductive_entries();
    let zero_environment = EnvironmentBudget::new(0, 0, 0, 0, 0, 0);
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            zero_environment,
        ),
        fln_checker::admit::InductiveVerdict::Inconclusive(
            fln_checker::admit::InductiveStop::Environment { .. }
        )
    ));
    assert!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        )
        .is_admitted()
    );
}

#[test]
fn kr600_803_enumeration_rejects_constructor_and_recursor_forgery() {
    let mut bad_constructor = enumeration_entries(BinderInfo::Implicit);
    bad_constructor[1] = ConstantEntry::new(
        checker_qualified(&["Color", "red"]),
        ConstantDeclaration::constructor(
            Vec::new(),
            a_type(),
            ConstantSafety::Safe,
            ConstructorDeclaration::new(checker_name("Color"), 0, 0, 0),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &bad_constructor,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::ConstructorShape { .. }
        )
    ));

    let bad_recursor = enumeration_entries(BinderInfo::Default);
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &bad_recursor,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
    let bad_rule = enumeration_entries_with_binders(BinderInfo::Implicit, BinderInfo::Implicit);
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &bad_rule,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Rejected(
            fln_checker::admit::InductiveRejection::RecursorShape { .. }
        )
    ));
    assert!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &enumeration_entries(BinderInfo::Implicit),
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        )
        .is_admitted(),
        "the exact block must remain the positive control"
    );
}

#[test]
fn kr600_803_enumeration_resource_and_cancellation_are_nonanswers() {
    let entries = enumeration_entries(BinderInfo::Implicit);
    let oversized = vec![entries[0].clone(); 35];
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &oversized,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Deferred(
            fln_checker::admit::InductiveSupportLimit::DeclarationRows {
                observed: 35,
                limit: 34,
            }
        )
    ));
    let budget = AdmissionBudget::new(
        InferenceBudget::unlimited(),
        WhnfBudget::unlimited(),
        DefEqBudget {
            quick: QuickDefEqBudget::new(0, u64::MAX),
            ..DefEqBudget::unlimited()
        },
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &entries,
            budget,
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Inconclusive(_)
    ));
    assert!(matches!(
        admit_inductive_with(
            &ConstantEnvironment::empty(),
            &entries,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
            || true,
        ),
        fln_checker::admit::InductiveVerdict::Inconclusive(_)
    ));

    let mut recursive = enumeration_entries(BinderInfo::Implicit);
    recursive[0] = ConstantEntry::new(
        checker_name("Color"),
        ConstantDeclaration::inductive(
            Vec::new(),
            decoded(&Expr::sort(Level::one())),
            ConstantSafety::Safe,
            InductiveDeclaration::new(
                0,
                0,
                vec![checker_name("Color")],
                vec![
                    checker_qualified(&["Color", "red"]),
                    checker_qualified(&["Color", "blue"]),
                ],
                0,
                true,
                false,
            ),
        ),
    );
    assert!(matches!(
        admit_inductive(
            &ConstantEnvironment::empty(),
            &recursive,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
        ),
        fln_checker::admit::InductiveVerdict::Deferred(
            fln_checker::admit::InductiveSupportLimit::Recursive
        )
    ));
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
fn kr950_954_quotient_initialization_ignores_kernel_irrelevant_binder_styles() {
    let environment = equality_environment(false, false);
    let declarations = quotient_entries_with_lift_relation_binder(BinderInfo::Default);
    assert!(
        admit_quotient(&environment, &declarations, AdmissionBudget::unlimited()).is_admitted(),
        "the pinned quotient equality ignores binder annotations"
    );
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
