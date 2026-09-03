#![forbid(unsafe_code)]

use fln_checker::admit::{AdmissionBudget, InductiveRejection, InductiveVerdict, admit_inductive};
use fln_checker::environment::{
    ConstantDeclaration, ConstantEntry, ConstantEnvironment, ConstantSafety,
    ConstructorDeclaration, EnvironmentBudget, InductiveDeclaration, RecursorDeclaration,
    RecursorRule,
};
use fln_checker::wire::{
    DecodeBudget, DecodeOutcome, WireExpr, WireName, decode_expr, decode_name,
};
use fln_core::expr::{BinderInfo, Expr};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_hash::canon::Canonical;

fn name(component: &str) -> Name {
    Name::str(Name::anonymous(), component)
}

fn qualified(components: &[&str]) -> Name {
    Name::from_components(components.iter().copied())
}

fn wire_name(value: &Name) -> WireName {
    match decode_name(&value.to_canonical_bytes(), DecodeBudget::unlimited()) {
        DecodeOutcome::Complete(Ok(value)) => value,
        other => panic!("primary-produced name did not decode: {other:?}"),
    }
}

fn wire_expr(value: &Expr) -> WireExpr {
    match decode_expr(&value.to_canonical_bytes(), DecodeBudget::unlimited()) {
        DecodeOutcome::Complete(Ok(value)) => value,
        other => panic!("primary-produced expression did not decode: {other:?}"),
    }
}

fn pi(label: &str, info: BinderInfo, domain: Expr, body: Expr) -> Expr {
    Expr::forall_e(name(label), domain, body, info)
}

fn app(function: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(function, Expr::app)
}

fn bvar(index: u32) -> Expr {
    Expr::bvar(index).expect("fixture index is in range")
}

fn nat() -> Expr {
    Expr::const_(name("Nat"), Vec::new())
}

fn zero() -> Expr {
    Expr::const_(qualified(&["Nat", "zero"]), Vec::new())
}

fn succ(value: Expr) -> Expr {
    Expr::app(Expr::const_(qualified(&["Nat", "succ"]), Vec::new()), value)
}

fn nat_entries(recursive: bool, recursive_rule_call: bool) -> Vec<ConstantEntry> {
    let nat_name = wire_name(&name("Nat"));
    let zero_name = wire_name(&qualified(&["Nat", "zero"]));
    let succ_name = wire_name(&qualified(&["Nat", "succ"]));
    let rec_name = wire_name(&qualified(&["Nat", "rec"]));
    let u_name = wire_name(&name("u"));
    let u = Level::param(name("u"));

    let inductive_type = Expr::sort(Level::one());
    let zero_type = nat();
    let succ_type = pi("n", BinderInfo::Default, nat(), nat());

    let motive_type = pi("t", BinderInfo::Default, nat(), Expr::sort(u.clone()));
    let zero_minor = Expr::app(bvar(0), zero());
    let succ_minor = pi(
        "n",
        BinderInfo::Default,
        nat(),
        pi(
            "ih",
            BinderInfo::Default,
            Expr::app(bvar(2), bvar(0)),
            Expr::app(bvar(3), succ(bvar(1))),
        ),
    );
    let recursor_type = pi(
        "motive",
        BinderInfo::Implicit,
        motive_type.clone(),
        pi(
            "zero",
            BinderInfo::Default,
            zero_minor.clone(),
            pi(
                "succ",
                BinderInfo::Default,
                succ_minor.clone(),
                pi("t", BinderInfo::Default, nat(), Expr::app(bvar(3), bvar(0))),
            ),
        ),
    );

    let zero_rule = Expr::lam(
        name("motive"),
        motive_type.clone(),
        Expr::lam(
            name("zero"),
            zero_minor.clone(),
            Expr::lam(
                name("succ"),
                succ_minor.clone(),
                bvar(1),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );

    let recursive_call = if recursive_rule_call {
        app(
            Expr::const_(qualified(&["Nat", "rec"]), vec![u.clone()]),
            [bvar(3), bvar(2), bvar(1), bvar(0)],
        )
    } else {
        // Deliberately pass `n` where the induction hypothesis belongs. The
        // recursor-rule comparison must reject this before it can be confused
        // with Nat.rec's recursive iota law.
        bvar(0)
    };
    let succ_body = app(bvar(1), [bvar(0), recursive_call]);
    let succ_rule = Expr::lam(
        name("motive"),
        motive_type,
        Expr::lam(
            name("zero"),
            zero_minor,
            Expr::lam(
                name("succ"),
                succ_minor,
                Expr::lam(name("n"), nat(), succ_body, BinderInfo::Default),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );

    vec![
        ConstantEntry::new(
            nat_name.clone(),
            ConstantDeclaration::inductive(
                Vec::new(),
                wire_expr(&inductive_type),
                ConstantSafety::Safe,
                InductiveDeclaration::new(
                    0,
                    0,
                    vec![nat_name.clone()],
                    vec![zero_name.clone(), succ_name.clone()],
                    0,
                    recursive,
                    false,
                ),
            ),
        ),
        ConstantEntry::new(
            zero_name.clone(),
            ConstantDeclaration::constructor(
                Vec::new(),
                wire_expr(&zero_type),
                ConstantSafety::Safe,
                ConstructorDeclaration::new(nat_name.clone(), 0, 0, 0),
            ),
        ),
        ConstantEntry::new(
            succ_name.clone(),
            ConstantDeclaration::constructor(
                Vec::new(),
                wire_expr(&succ_type),
                ConstantSafety::Safe,
                ConstructorDeclaration::new(nat_name.clone(), 1, 0, 1),
            ),
        ),
        ConstantEntry::new(
            rec_name,
            ConstantDeclaration::recursor(
                vec![u_name],
                wire_expr(&recursor_type),
                ConstantSafety::Safe,
                RecursorDeclaration::new(
                    vec![nat_name],
                    0,
                    0,
                    1,
                    2,
                    vec![
                        RecursorRule::new(zero_name, 0, wire_expr(&zero_rule)),
                        RecursorRule::new(succ_name, 1, wire_expr(&succ_rule)),
                    ],
                    false,
                ),
            ),
        ),
    ]
}

#[test]
fn kr600_803_init_nat_block_is_reconstructed_with_its_recursive_iota_rule() {
    let entries = nat_entries(true, true);
    let verdict = admit_inductive(
        &ConstantEnvironment::empty(),
        &entries,
        AdmissionBudget::unlimited(),
        EnvironmentBudget::unlimited(),
    );
    assert!(verdict.is_admitted(), "exact Init.Nat block: {verdict:?}");
    let InductiveVerdict::Admitted(admission) = verdict else {
        return;
    };
    assert_eq!(
        admission.members(),
        &[
            wire_name(&name("Nat")),
            wire_name(&qualified(&["Nat", "zero"])),
            wire_name(&qualified(&["Nat", "succ"])),
            wire_name(&qualified(&["Nat", "rec"])),
        ]
    );
}

#[test]
fn kr600_803_init_nat_refuses_a_forged_nonrecursive_flag() {
    let entries = nat_entries(false, true);
    let verdict = admit_inductive(
        &ConstantEnvironment::empty(),
        &entries,
        AdmissionBudget::unlimited(),
        EnvironmentBudget::unlimited(),
    );
    let succ_name = wire_name(&qualified(&["Nat", "succ"]));
    assert!(
        matches!(
            &verdict,
            InductiveVerdict::Rejected(InductiveRejection::ConstructorShape { name })
                if name == &succ_name
        ),
        "Nat.succ mentions Nat, so a nonrecursive metadata flag must fail at the constructor: {verdict:?}"
    );
}

#[test]
fn kr600_803_init_nat_refuses_a_succ_rule_without_the_recursive_call() {
    let entries = nat_entries(true, false);
    let verdict = admit_inductive(
        &ConstantEnvironment::empty(),
        &entries,
        AdmissionBudget::unlimited(),
        EnvironmentBudget::unlimited(),
    );
    let rec_name = wire_name(&qualified(&["Nat", "rec"]));
    assert!(
        matches!(
            &verdict,
            InductiveVerdict::Rejected(InductiveRejection::RecursorShape { name })
                if name == &rec_name
        ),
        "a successor rule without the recursive call must fail at Nat.rec: {verdict:?}"
    );
}
