//! Mutual-family admission through the independent checker, with hand-built
//! recursors and adversarial controls that cannot consult its reconstruction.
#![forbid(unsafe_code)]
#[path = "support/mutual.rs"]
mod fixtures;
#[path = "support/safety.rs"]
mod safety;
use fixtures::{Fixture, Mutation, fixture, proposition_fixture};
use fln_checker::admit::{
    AdmissionBudget, InductiveRejection, InductiveStop, InductiveSupportLimit, InductiveVerdict,
    admit_inductive, admit_inductive_with,
};
use fln_checker::defeq::DefEqBudget;
use fln_checker::environment::{
    ConstantDeclaration, ConstantEntry, ConstantEnvironment, ConstantSafety,
    ConstructorDeclaration, EnvironmentBudget, EnvironmentOutcome, InductiveDeclaration,
    RecursorDeclaration, RecursorRule,
};
use fln_checker::wire::{
    DecodeBudget, DecodeOutcome, WireExpr, WireName, decode_expr, decode_name,
};
use fln_checker::{infer::InferenceBudget, term::TermBudget, whnf::WhnfBudget};
use fln_core::{
    expr::{BinderInfo, Expr, ExprNode},
    level::Level,
    name::Name,
};
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

fn map_parameter_domain(type_: &Expr, parameter: usize, map: impl FnOnce(&Expr) -> Expr) -> Expr {
    let ExprNode::ForallE {
        binder_name,
        binder_type,
        body,
        binder_info,
    } = type_.node()
    else {
        panic!("fixture parameter missing");
    };
    let (domain, body) = if parameter == 0 {
        (map(binder_type), body.clone())
    } else {
        (
            binder_type.clone(),
            map_parameter_domain(body, parameter - 1, map),
        )
    };
    Expr::forall_e(binder_name.clone(), domain, body, *binder_info)
}

/// Keep the second parameter dependent on the first, but make its written
/// domain a beta redex. The pin opens both domains with the first family's
/// locals before converting them (`inductive.cpp:234,430`).
fn convertible_parameter(type_: &Expr) -> Expr {
    map_parameter_domain(type_, 1, |domain| {
        let type_of_domain = Expr::sort(
            Level::succ(Level::succ(Level::param(fixtures::name("u"))).unwrap()).unwrap(),
        );
        Expr::app(
            Expr::lam(
                fixtures::name("type_alias"),
                type_of_domain,
                Expr::bvar(0).unwrap(),
                BinderInfo::Default,
            ),
            domain.clone(),
        )
    })
}

fn convertible_mutual_parameters(family: bool, constructor: bool) -> Fixture {
    let mut f = fixture(true, true, true, 2, Mutation::None);
    if family {
        f.types[1].ty = convertible_parameter(&f.types[1].ty);
    }
    if constructor {
        f.ctors[0].ty = convertible_parameter(&f.ctors[0].ty);
    }
    f
}

#[test]
fn mutually_defined_families_convert_their_shared_dependent_parameter_domains() {
    accepts(&convertible_mutual_parameters(true, false));
}

#[test]
fn mutual_constructors_convert_their_shared_dependent_parameter_domains() {
    accepts(&convertible_mutual_parameters(false, true));
    accepts(&convertible_mutual_parameters(true, true));
}

#[test]
fn mutual_parameter_conversion_stops_stay_nonanswers_and_allow_recovery() {
    let unlimited = InferenceBudget::unlimited().defeq;
    let budget = AdmissionBudget::new(
        InferenceBudget::unlimited(),
        WhnfBudget::unlimited(),
        DefEqBudget::new(
            unlimited.quick,
            0,
            0,
            u64::MAX,
            u64::MAX,
            WhnfBudget::new(0, 0, TermBudget::unlimited()),
        ),
    );
    for (family, constructor) in [(true, false), (false, true)] {
        let rs = rows(&convertible_mutual_parameters(family, constructor));
        let base = empty();
        let stopped = admit_inductive(&base, &rs, budget, EnvironmentBudget::unlimited());
        assert!(
            matches!(
                stopped,
                InductiveVerdict::Inconclusive(InductiveStop::ParameterConversion {
                    parameter: 1,
                    ..
                })
            ),
            "family={family} constructor={constructor}: {stopped:?}"
        );
        assert!(base.find(rs[0].name()).is_none());
        let mut polls = 0;
        let complete = admit_inductive_with(
            &base,
            &rs,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
            || {
                polls += 1;
                false
            },
        );
        assert!(complete.is_admitted(), "{complete:?}");
        for cut in [1, polls / 2, polls - 1] {
            let mut observed = 0;
            let cancelled = admit_inductive_with(
                &base,
                &rs,
                AdmissionBudget::unlimited(),
                EnvironmentBudget::unlimited(),
                || {
                    observed += 1;
                    observed >= cut
                },
            );
            assert!(
                matches!(cancelled, InductiveVerdict::Inconclusive(_)),
                "cut {cut}: {cancelled:?}"
            );
        }
        assert!(verdict(&rs).is_admitted());
    }
}

#[test]
fn unequal_mutual_parameter_domains_and_forged_recursors_are_not_admitted() {
    let mut f = convertible_mutual_parameters(true, true);
    f.types[1].ty = map_parameter_domain(&f.types[1].ty, 0, |_| {
        Expr::sort(Level::succ(Level::succ(Level::param(fixtures::name("u"))).unwrap()).unwrap())
    });
    let result = verdict(&rows(&f));
    assert!(
        matches!(
            result,
            InductiveVerdict::Rejected(InductiveRejection::ConstructorShape { ref name })
                if *name == wn(&f.names[1])
        ),
        "{result:?}"
    );

    let mut f = convertible_mutual_parameters(true, true);
    f.recs[1].rules[0].rhs = f.recs[0].rules[0].rhs.clone();
    let result = verdict(&rows(&f));
    assert!(
        matches!(
            result,
            InductiveVerdict::Rejected(InductiveRejection::RecursorShape { .. })
        ),
        "{result:?}"
    );
}

/// Two empty data families with every declared universe used in the family's
/// result sort and every family occurrence instantiated at the full list.
/// Their recursor types are written here independently of reconstruction.
fn many_universe_mutual_fixture(count: usize) -> Fixture {
    assert!(count > 0);
    let levels: Vec<_> = (0..count)
        .map(|i| fixtures::name(&format!("v{i}")))
        .collect();
    let actual_levels: Vec<_> = levels.iter().cloned().map(Level::param).collect();
    let maximum = actual_levels
        .iter()
        .cloned()
        .reduce(|a, b| Level::max(a, b).unwrap())
        .unwrap();
    let result_sort = Expr::sort(Level::succ(maximum).unwrap());
    let motive_level = fixtures::name("motive_universe");
    let names = vec![
        fixtures::name("ManyUniverse0"),
        fixtures::name("ManyUniverse1"),
    ];
    let family_terms: Vec<_> = names
        .iter()
        .map(|name| Expr::const_(name.clone(), actual_levels.clone()))
        .collect();
    let motives: Vec<_> = family_terms
        .iter()
        .map(|family| {
            Expr::forall_e(
                fixtures::name("major"),
                family.clone(),
                Expr::sort(Level::param(motive_level.clone())),
                BinderInfo::Default,
            )
        })
        .collect();
    let mut f = Fixture {
        names: names.clone(),
        levels,
        rec_levels: vec![motive_level],
        parameters: 0,
        types: Vec::new(),
        ctors: Vec::new(),
        recs: Vec::new(),
        recursive: false,
        reflexive: false,
    };
    f.rec_levels.extend(f.levels.iter().cloned());
    for family in 0..2 {
        f.types.push(fixtures::Type {
            name: names[family].clone(),
            ty: result_sort.clone(),
            indices: 0,
            ctors: Vec::new(),
        });
        let mut type_ = Expr::forall_e(
            fixtures::name("major"),
            family_terms[family].clone(),
            Expr::app(
                Expr::bvar((2 - family) as u32).unwrap(),
                Expr::bvar(0).unwrap(),
            ),
            BinderInfo::Default,
        );
        for (index, motive) in motives.iter().enumerate().rev() {
            type_ = Expr::forall_e(
                fixtures::name(&format!("motive_{index}")),
                motive.clone(),
                type_,
                BinderInfo::Default,
            );
        }
        f.recs.push(fixtures::Rec {
            name: fixtures::name(&format!("ManyUniverse{family}.rec")),
            ty: type_,
            indices: 0,
            rules: Vec::new(),
        });
    }
    f
}

#[test]
fn mutual_families_support_more_than_eight_universe_parameters() {
    for count in [1, 8, 9, 16] {
        accepts(&many_universe_mutual_fixture(count));
    }
}

#[test]
fn wide_mutual_universe_telescopes_still_require_distinct_and_matching_parameters() {
    let mut duplicated = many_universe_mutual_fixture(9);
    duplicated.levels[8] = duplicated.levels[0].clone();
    let result = verdict(&rows(&duplicated));
    assert!(
        matches!(result, InductiveVerdict::Rejected(_)),
        "{result:?}"
    );

    let mut inconsistent = many_universe_mutual_fixture(9);
    inconsistent.rec_levels.swap(1, 2);
    let result = verdict(&rows(&inconsistent));
    assert!(
        matches!(
            result,
            InductiveVerdict::Rejected(InductiveRejection::RecursorShape { .. })
        ),
        "{result:?}"
    );
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
/// The stdlib's widest block, `Lean.Meta.Grind.Arith.Cutsat.EqCnstr`, is 21
/// families with its auxiliaries; `Lean.Doc.Block` is 9.
#[test]
fn wide_mutual_blocks_are_admitted_up_to_the_limit() {
    accepts(&fixture(false, false, false, 9, Mutation::None));
    accepts(&fixture(false, false, false, 21, Mutation::None));
}

#[test]
fn wider_mutual_blocks_remain_explicit_support_nonanswers() {
    assert!(matches!(
        verdict(&rows(&fixture(false, false, false, 33, Mutation::None))),
        InductiveVerdict::Deferred(InductiveSupportLimit::MultipleTypes { observed: 33 })
    ));
}

/// `Std.Http.Status` has 64 constructors and `Std.Http.Method` 40.
#[test]
fn enumerations_are_admitted_up_to_the_constructor_limit() {
    accepts(&fixtures::enumeration(64));
    assert!(matches!(
        verdict(&rows(&fixtures::enumeration(129))),
        InductiveVerdict::Deferred(_)
    ));
}

/// `Std.DHashMap.Raw.WF.below` has 144 fields over 15 constructors.
#[test]
fn wide_blocks_are_admitted_up_to_the_field_limit() {
    accepts(&fixtures::wide_structure(144));
    assert!(matches!(
        verdict(&rows(&fixtures::wide_structure(257))),
        InductiveVerdict::Deferred(_)
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

#[test]
fn interleaved_recursive_fields_have_distinct_family_targets_and_induction_hypotheses() {
    for (generic, indexed, higher, families) in [
        (false, false, false, 3),
        (true, false, false, 3),
        (true, true, false, 2),
        (true, false, true, 3),
        (true, true, true, 2),
    ] {
        accepts(&fixture(
            generic,
            indexed,
            higher,
            families,
            Mutation::MultipleChildren,
        ));
    }
}

#[test]
fn cyclic_family_signatures_cannot_use_private_staging_to_justify_themselves() {
    use fln_core::expr::BinderInfo;
    use fln_core::level::Level;
    let mut f = fixture(false, false, false, 2, Mutation::None);
    f.parameters = 1;
    // Both declared types have a syntactically valid final Sort. Validation
    // must still reject their shared parameter type, which names a sibling
    // unavailable in the predecessor environment.
    for ty in &mut f.types {
        ty.ty = Expr::forall_e(
            fixtures::name("x"),
            Expr::const_(fixtures::name("Mutual1"), vec![]),
            Expr::sort(Level::one()),
            BinderInfo::Default,
        );
    }
    assert!(matches!(verdict(&rows(&f)), InductiveVerdict::Rejected(_)));
}

#[test]
fn inconsistent_sorts_and_universe_telescopes_cannot_gain_mutual_admission() {
    use fln_core::level::Level;
    let mut f = fixture(false, false, false, 2, Mutation::None);
    f.types[1].ty = Expr::sort(Level::succ(Level::one()).unwrap());
    assert!(matches!(verdict(&rows(&f)), InductiveVerdict::Rejected(_)));
    // A Prop family beside a Type family: the pin requires one sort per block.
    f.types[1].ty = Expr::sort(Level::zero());
    assert!(matches!(verdict(&rows(&f)), InductiveVerdict::Rejected(_)));
    // A block in `Sort u` is Prop at u = 0 and data above it; it stays deferred.
    let mut f = fixture(false, false, false, 2, Mutation::None);
    f.levels = vec![fixtures::name("u")];
    for t in &mut f.types {
        t.ty = Expr::sort(Level::param(fixtures::name("u")));
    }
    assert!(matches!(
        verdict(&rows(&f)),
        InductiveVerdict::Deferred(InductiveSupportLimit::ResultUniverse)
    ));
    let mut f = fixture(true, false, false, 2, Mutation::None);
    f.levels.push(fixtures::name("u"));
    assert!(matches!(verdict(&rows(&f)), InductiveVerdict::Rejected(_)));
    let mut f = fixture(true, false, false, 2, Mutation::None);
    f.rec_levels[0] = fixtures::name("u");
    assert!(matches!(verdict(&rows(&f)), InductiveVerdict::Rejected(_)));
}

#[test]
fn mutual_predicates_eliminate_only_into_prop_with_fields_in_any_universe() {
    // The generic blocks have fields in `Type` (their parameters' universe),
    // above the predicates' `Prop`.
    for (generic, indexed, higher, families, mutation) in [
        (false, false, false, 2, Mutation::None),
        (false, false, false, 3, Mutation::None),
        (true, false, false, 2, Mutation::None),
        (true, true, false, 2, Mutation::None),
        (true, false, true, 3, Mutation::None),
        (true, true, true, 2, Mutation::MultipleChildren),
    ] {
        accepts(&proposition_fixture(
            generic, indexed, higher, families, mutation,
        ));
    }
}

#[test]
fn a_mutual_predicate_cannot_claim_a_large_eliminator_nor_data_a_small_one() {
    for (generic, indexed) in [(false, false), (true, true)] {
        let data = fixture(generic, indexed, false, 2, Mutation::None);
        let predicate = proposition_fixture(generic, indexed, false, 2, Mutation::None);
        // Data recursors (an extra universe, motives in `Sort u`) over families in Prop.
        let mut large = data.clone();
        large.types = predicate.types.clone();
        // The predicate's own recursors, declared with one extra, unused universe.
        let mut widened = predicate.clone();
        widened.rec_levels.insert(0, fixtures::name("v"));
        // The predicate's recursors over families in `Type`.
        let mut small = predicate.clone();
        small.types = data.types.clone();
        for (label, f) in [("large", large), ("widened", widened), ("small", small)] {
            let result = verdict(&rows(&f));
            assert!(
                matches!(
                    result,
                    InductiveVerdict::Rejected(InductiveRejection::RecursorShape { .. })
                ),
                "{label} generic={generic}: {result:?}"
            );
        }
    }
}

#[test]
fn unsafe_mutual_blocks_support_parameters_indices_and_negative_function_domains() {
    for f in [
        fixture(false, false, false, 3, Mutation::None),
        fixture(true, true, false, 2, Mutation::None),
        fixture(true, true, true, 2, Mutation::None),
        fixture(true, false, true, 3, Mutation::NegativeCrossFamily),
    ] {
        let rs = safety::unsafe_rows(&rows(&f));
        let result = verdict(&rs);
        assert!(result.is_admitted(), "{result:?}");
        let mut reversed = rs;
        reversed.reverse();
        assert!(verdict(&reversed).is_admitted());
    }
    assert!(matches!(
        verdict(&rows(&fixture(
            true,
            false,
            true,
            3,
            Mutation::NegativeCrossFamily
        ))),
        InductiveVerdict::Rejected(InductiveRejection::ConstructorShape { .. })
    ));
}

#[test]
fn unsafe_mutual_blocks_reject_mixed_safety_and_forged_recursors() {
    let rs = safety::unsafe_rows(&rows(&fixture(
        true,
        false,
        true,
        3,
        Mutation::NegativeCrossFamily,
    )));
    for i in 0..rs.len() {
        let mut changed = rs.clone();
        changed[i] = safety::retag(&changed[i], ConstantSafety::Safe);
        let result = verdict(&changed);
        assert!(
            matches!(result, InductiveVerdict::Rejected(_)),
            "row {i}: {result:?}"
        );
    }
    for mutation in [
        Mutation::WrongCallFamily,
        Mutation::SwapMotives,
        Mutation::SwapMinors,
        Mutation::MissingInductionHypothesis,
        Mutation::MissingArgumentLambda,
        Mutation::WrongChildIndex,
        Mutation::FalseRecursive,
        Mutation::FalseReflexive,
    ] {
        let result = verdict(&safety::unsafe_rows(&rows(&fixture(
            true, true, true, 2, mutation,
        ))));
        assert!(
            matches!(result, InductiveVerdict::Rejected(_)),
            "{mutation:?}: {result:?}"
        );
    }
}

#[test]
fn unsafe_mutual_admission_stops_atomically_and_retries() {
    let rs = safety::unsafe_rows(&rows(&fixture(
        true,
        false,
        true,
        2,
        Mutation::NegativeCrossFamily,
    )));
    let base = empty();
    let before = base.clone();
    let mut polls = 0;
    assert!(
        admit_inductive_with(
            &base,
            &rs,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
            || {
                polls += 1;
                false
            }
        )
        .is_admitted()
    );
    for stop in [1, 10, polls / 2, polls - 1, polls] {
        let mut calls = 0;
        let result = admit_inductive_with(
            &base,
            &rs,
            AdmissionBudget::unlimited(),
            EnvironmentBudget::unlimited(),
            || {
                calls += 1;
                calls >= stop
            },
        );
        assert!(
            matches!(result, InductiveVerdict::Inconclusive(_)),
            "{result:?}"
        );
    }
    let mut budget = AdmissionBudget::unlimited();
    budget.conversion.quick.max_comparisons = 1;
    assert!(matches!(
        admit_inductive(&base, &rs, budget, EnvironmentBudget::unlimited()),
        InductiveVerdict::Inconclusive(_)
    ));
    assert_eq!(base, before);
    assert!(verdict(&rs).is_admitted());
}
