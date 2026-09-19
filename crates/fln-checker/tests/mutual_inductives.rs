//! Mutual-family admission through the independent checker, with hand-built
//! recursors and adversarial controls that cannot consult its reconstruction.
#![forbid(unsafe_code)]
#[path = "support/mutual.rs"]
mod fixtures;
use fixtures::{Fixture, Mutation, fixture};
use fln_checker::admit::{
    AdmissionBudget, InductiveRejection, InductiveSupportLimit, InductiveVerdict, admit_inductive,
    admit_inductive_with,
};
use fln_checker::environment::{
    ConstantDeclaration, ConstantEntry, ConstantEnvironment, ConstantSafety,
    ConstructorDeclaration, EnvironmentBudget, EnvironmentOutcome, InductiveDeclaration,
    RecursorDeclaration, RecursorRule,
};
use fln_checker::wire::{
    DecodeBudget, DecodeOutcome, WireExpr, WireName, decode_expr, decode_name,
};
use fln_core::{expr::Expr, name::Name};
use fln_hash::canon::Canonical;
fn wn(name: &Name) -> WireName {
    match decode_name(&name.to_canonical_bytes(), DecodeBudget::unlimited()) {
        DecodeOutcome::Complete(Ok(value)) => value,
        other => panic!("name decode {other:?}"),
    }
}
fn we(expr: &Expr) -> WireExpr {
    match decode_expr(&expr.to_canonical_bytes(), DecodeBudget::unlimited()) {
        DecodeOutcome::Complete(Ok(value)) => value,
        other => panic!("term decode {other:?}"),
    }
}
fn rows(f: &Fixture) -> Vec<ConstantEntry> {
    let levels: Vec<_> = f.levels.iter().map(wn).collect();
    let all: Vec<_> = f.names.iter().map(wn).collect();
    let mut rows = Vec::new();
    for t in &f.types {
        rows.push(ConstantEntry::new(
            wn(&t.name),
            ConstantDeclaration::inductive(
                levels.clone(),
                we(&t.ty),
                ConstantSafety::Safe,
                InductiveDeclaration::new(
                    f.parameters as u32,
                    t.indices as u32,
                    all.clone(),
                    t.ctors.iter().map(wn).collect(),
                    0,
                    f.recursive,
                    f.reflexive,
                ),
            ),
        ));
    }
    for c in &f.ctors {
        rows.push(ConstantEntry::new(
            wn(&c.name),
            ConstantDeclaration::constructor(
                levels.clone(),
                we(&c.ty),
                ConstantSafety::Safe,
                ConstructorDeclaration::new(
                    wn(&f.names[c.family]),
                    c.index as u32,
                    f.parameters as u32,
                    c.fields as u32,
                ),
            ),
        ));
    }
    for r in &f.recs {
        rows.push(ConstantEntry::new(
            wn(&r.name),
            ConstantDeclaration::recursor(
                f.rec_levels.iter().map(wn).collect(),
                we(&r.ty),
                ConstantSafety::Safe,
                RecursorDeclaration::new(
                    all.clone(),
                    f.parameters as u32,
                    r.indices as u32,
                    all.len() as u32,
                    f.ctors.len() as u32,
                    r.rules
                        .iter()
                        .map(|rule| {
                            RecursorRule::new(wn(&rule.ctor), rule.fields as u32, we(&rule.rhs))
                        })
                        .collect(),
                    false,
                ),
            ),
        ));
    }
    rows
}
fn empty() -> ConstantEnvironment {
    match ConstantEnvironment::build(vec![], EnvironmentBudget::unlimited()) {
        EnvironmentOutcome::Complete { environment, .. } => environment,
        other => panic!("environment {other:?}"),
    }
}
fn verdict(rows: &[ConstantEntry]) -> InductiveVerdict {
    admit_inductive(
        &empty(),
        rows,
        AdmissionBudget::unlimited(),
        EnvironmentBudget::unlimited(),
    )
}
fn accepts(f: &Fixture) {
    let rs = rows(f);
    let result = verdict(&rs);
    let InductiveVerdict::Admitted(admitted) = result else {
        panic!("mutual admission: {result:?}");
    };
    assert_eq!(admitted.members().len(), rs.len());
    assert!(
        admitted
            .members()
            .iter()
            .all(|n| rs.iter().any(|r| r.name() == n))
    );
}
#[test]
fn mutually_recursive_families_reconstruct_all_motives_and_minors() {
    for n in [2, 3, 8] {
        accepts(&fixture(false, false, false, n, Mutation::None));
    }
}
#[test]
fn shared_dependent_parameters_and_polymorphic_recursors_are_checked() {
    accepts(&fixture(true, false, false, 2, Mutation::None));
}
#[test]
fn different_dependent_index_telescopes_follow_each_childs_family() {
    accepts(&fixture(true, true, false, 2, Mutation::None));
}
#[test]
fn function_valued_mutual_children_preserve_their_dependent_argument_telescopes() {
    accepts(&fixture(true, false, true, 3, Mutation::None));
    accepts(&fixture(true, true, true, 2, Mutation::None));
}
#[test]
fn decoded_row_order_cannot_change_the_declared_mutual_order() {
    let rs = rows(&fixture(true, true, true, 2, Mutation::None));
    for start in 0..rs.len() {
        let mut reordered = rs.clone();
        reordered.rotate_left(start);
        assert!(verdict(&reordered).is_admitted());
        reordered.reverse();
        assert!(verdict(&reordered).is_admitted());
    }
}
#[test]
fn forged_cross_family_calls_motives_minors_and_induction_hypotheses_are_vetoed() {
    for mutation in [
        Mutation::WrongCallFamily,
        Mutation::SwapMotives,
        Mutation::SwapMinors,
        Mutation::MissingInductionHypothesis,
        Mutation::MissingArgumentLambda,
        Mutation::WrongChildIndex,
    ] {
        assert!(matches!(
            verdict(&rows(&fixture(true, true, true, 2, mutation))),
            InductiveVerdict::Rejected(InductiveRejection::RecursorShape { .. })
        ));
    }
}
#[test]
fn negative_cross_family_occurrences_and_false_recursivity_metadata_are_vetoed() {
    for mutation in [Mutation::FalseRecursive, Mutation::FalseReflexive] {
        let result = verdict(&rows(&fixture(true, true, true, 2, mutation)));
        assert!(
            matches!(result, InductiveVerdict::Rejected(_)),
            "{mutation:?}: {result:?}"
        );
    }
    let negative = verdict(&rows(&fixture(
        true,
        false,
        true,
        2,
        Mutation::NegativeCrossFamily,
    )));
    assert!(
        matches!(
            negative,
            InductiveVerdict::Rejected(InductiveRejection::ConstructorShape { .. })
        ),
        "{negative:?}"
    );
    assert!(matches!(
        verdict(&rows(&fixture(
            false,
            false,
            false,
            2,
            Mutation::WrongResultFamily
        ))),
        InductiveVerdict::Rejected(_)
    ));
    assert!(
        !verdict(&rows(&fixture(
            true,
            false,
            false,
            2,
            Mutation::NonuniformParameter
        )))
        .is_admitted()
    );
}
#[test]
fn all_block_members_and_recursor_rules_are_required() {
    let f = fixture(false, false, false, 2, Mutation::None);
    let rs = rows(&f);
    for missing in 0..rs.len() {
        let remaining: Vec<_> = rs
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != missing)
            .map(|(_, r)| r.clone())
            .collect();
        assert!(!verdict(&remaining).is_admitted(), "missing {missing}");
    }
    let mut duplicate = rs.clone();
    duplicate.push(rs[0].clone());
    assert!(!verdict(&duplicate).is_admitted());
    let mut missing_rule = f.clone();
    missing_rule.recs[1].rules.clear();
    assert!(!verdict(&rows(&missing_rule)).is_admitted());
    let mut extra_rule = f;
    let copied_rule = extra_rule.recs[0].rules[0].clone();
    extra_rule.recs[1].rules.push(copied_rule);
    assert!(!verdict(&rows(&extra_rule)).is_admitted());
}
#[test]
fn wider_mutual_blocks_remain_explicit_support_nonanswers() {
    assert!(matches!(
        verdict(&rows(&fixture(false, false, false, 9, Mutation::None))),
        InductiveVerdict::Deferred(InductiveSupportLimit::MultipleTypes { observed: 9 })
    ));
}
#[test]
fn cancellation_and_resource_stops_never_publish_a_prefix_and_allow_recovery() {
    let rs = rows(&fixture(true, true, true, 2, Mutation::None));
    let base = empty();
    let mut polls = 0;
    let result = admit_inductive_with(
        &base,
        &rs,
        AdmissionBudget::unlimited(),
        EnvironmentBudget::unlimited(),
        || {
            polls += 1;
            false
        },
    );
    assert!(result.is_admitted());
    assert!(polls > 100);
    for cut in [1, 10, polls / 2, polls - 1, polls] {
        let mut at = 0;
        let result = admit_inductive_with(
            &base,
            &rs,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
            || {
                at += 1;
                at >= cut
            },
        );
        assert!(
            matches!(result, InductiveVerdict::Inconclusive(_)),
            "cut {cut}: {result:?}"
        );
        assert!(base.find(rs[0].name()).is_none());
    }
    for limit in [0, 1, 20, 100] {
        let mut budget = AdmissionBudget::unlimited();
        budget.conversion.quick.max_comparisons = limit;
        assert!(matches!(
            admit_inductive(&base, &rs, budget, EnvironmentBudget::unlimited()),
            InductiveVerdict::Inconclusive(_)
        ));
    }
    assert!(verdict(&rs).is_admitted());
}
