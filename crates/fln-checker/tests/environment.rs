#![forbid(unsafe_code)]

use std::process::Command;

use fln_checker::environment::{
    ConstantDeclaration, ConstantEntry, ConstantEnvironment, ConstantKind, ConstantSafety,
    ConstructorDeclaration, DefinitionBody, DefinitionSafety, EnvironmentBudget, EnvironmentField,
    EnvironmentLimit, EnvironmentOutcome, EnvironmentProgress, EnvironmentRefusal, EnvironmentStop,
    InductiveDeclaration, QuotientKind, RecursorDeclaration, RecursorRule, ReducibilityHint,
};
use fln_checker::wire::{
    DecodeBudget, DecodeOutcome, NamePart, WireExpr, WireName, decode_expr, decode_name,
};
use fln_core::expr::{Expr, Literal, NatLit};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_hash::canon::{CanonWriter, Canonical, SCHEMA_EXPR};

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

fn decoded(expression: &Expr) -> WireExpr {
    match decode_expr(&expression.to_canonical_bytes(), DecodeBudget::unlimited()) {
        DecodeOutcome::Complete(Ok(value)) => value,
        other => panic!("primary-produced expression did not decode: {other:?}"),
    }
}

fn leaf(value: u64) -> WireExpr {
    decoded(&Expr::lit(Literal::Nat(NatLit::from_u64(value))))
}

fn entry(
    name: &str,
    level_parameters: Vec<WireName>,
    type_: WireExpr,
    value: WireExpr,
    hint: ReducibilityHint,
    safety: DefinitionSafety,
    mutual: Vec<WireName>,
) -> ConstantEntry {
    let constant_safety = if safety == DefinitionSafety::Unsafe {
        ConstantSafety::Unsafe
    } else {
        ConstantSafety::Safe
    };
    ConstantEntry::new(
        checker_name(name),
        ConstantDeclaration::definition(
            level_parameters,
            type_,
            constant_safety,
            DefinitionBody::new(value, hint, safety, mutual),
        ),
    )
}

fn header_entry(
    name: &str,
    level_parameters: Vec<WireName>,
    type_: WireExpr,
    kind: ConstantKind,
    safety: ConstantSafety,
) -> ConstantEntry {
    ConstantEntry::new(
        checker_name(name),
        ConstantDeclaration::header(level_parameters, type_, kind, safety),
    )
}

fn simple_entry(name: &str, value: u64) -> ConstantEntry {
    entry(
        name,
        Vec::new(),
        leaf(0),
        leaf(value),
        ReducibilityHint::Regular(value as u32),
        DefinitionSafety::Safe,
        vec![checker_name(name)],
    )
}

fn complete(outcome: EnvironmentOutcome) -> (ConstantEnvironment, EnvironmentProgress) {
    match outcome {
        EnvironmentOutcome::Complete {
            environment,
            progress,
        } => (environment, progress),
        EnvironmentOutcome::Refused { refusal, .. } => {
            panic!("unexpected environment refusal: {refusal:?}")
        }
        EnvironmentOutcome::Inconclusive(stop) => {
            panic!("unexpected environment non-answer: {stop:?}")
        }
        EnvironmentOutcome::InternalFault { fault, .. } => {
            panic!("unexpected environment fault: {fault:?}")
        }
    }
}

fn display_name(name: &WireName) -> String {
    match name.parts().last() {
        Some(NamePart::Text(text)) => text.clone(),
        Some(NamePart::Numeric { value, overflowed }) => {
            format!("{value}:overflow={overflowed}")
        }
        None => String::new(),
    }
}

#[test]
fn constant_schema_retains_common_headers_and_optional_definition_bodies() {
    let mut rows = vec![
        entry(
            "abbrev_safe",
            vec![checker_name("u")],
            decoded(&Expr::sort(Level::param(primary_name("u")))),
            leaf(1),
            ReducibilityHint::Abbrev,
            DefinitionSafety::Safe,
            vec![checker_name("abbrev_safe"), checker_name("regular_unsafe")],
        ),
        entry(
            "partial_definition",
            Vec::new(),
            leaf(2),
            leaf(3),
            ReducibilityHint::Opaque,
            DefinitionSafety::Partial,
            vec![checker_name("partial_definition")],
        ),
        entry(
            "regular_unsafe",
            Vec::new(),
            leaf(4),
            leaf(5),
            ReducibilityHint::Regular(17),
            DefinitionSafety::Unsafe,
            vec![checker_name("abbrev_safe"), checker_name("regular_unsafe")],
        ),
        ConstantEntry::new(
            checker_name("body_theorem"),
            ConstantDeclaration::theorem(
                Vec::new(),
                leaf(6),
                leaf(7),
                vec![checker_name("body_theorem")],
            ),
        ),
        ConstantEntry::new(
            checker_name("body_opaque"),
            ConstantDeclaration::opaque(
                Vec::new(),
                leaf(8),
                ConstantSafety::Unsafe,
                leaf(9),
                vec![checker_name("body_opaque")],
            ),
        ),
    ];
    let header_kinds = [
        ("axiom", ConstantKind::Axiom),
        ("theorem", ConstantKind::Theorem),
        ("opaque", ConstantKind::Opaque),
        ("header_definition", ConstantKind::Definition),
        ("inductive", ConstantKind::Inductive),
        ("constructor", ConstantKind::Constructor),
        ("recursor", ConstantKind::Recursor),
        ("quotient", ConstantKind::Quotient),
    ];
    rows.extend(
        header_kinds
            .iter()
            .enumerate()
            .map(|(index, (name, kind))| {
                header_entry(
                    name,
                    vec![checker_name(format!("u_{index}"))],
                    leaf(10 + index as u64),
                    *kind,
                    if index & 1 == 0 {
                        ConstantSafety::Safe
                    } else {
                        ConstantSafety::Unsafe
                    },
                )
            }),
    );
    let (environment, _) = complete(ConstantEnvironment::build(
        rows,
        EnvironmentBudget::unlimited(),
    ));

    let abbrev = environment
        .find(&checker_name("abbrev_safe"))
        .expect("abbreviation remains addressable");
    assert_eq!(abbrev.kind(), ConstantKind::Definition);
    assert_eq!(abbrev.safety(), ConstantSafety::Safe);
    assert!(abbrev.is_delta_unfoldable());
    assert_eq!(abbrev.level_parameters(), &[checker_name("u")]);
    let abbrev_body = abbrev
        .definition_body()
        .expect("definition body is retained");
    assert_eq!(abbrev_body.hint(), ReducibilityHint::Abbrev);
    assert_eq!(abbrev_body.hint().delta_height(), u32::MAX);
    assert_eq!(abbrev_body.safety(), DefinitionSafety::Safe);
    assert_eq!(abbrev_body.mutual().len(), 2);

    let partial = environment
        .find(&checker_name("partial_definition"))
        .expect("partial definition remains addressable");
    let partial_body = partial
        .definition_body()
        .expect("partial definition body is retained");
    assert_eq!(partial_body.hint(), ReducibilityHint::Opaque);
    assert_eq!(partial_body.hint().delta_height(), 0);
    assert_eq!(partial_body.safety(), DefinitionSafety::Partial);
    assert!(!partial.is_delta_unfoldable());

    let regular = environment
        .find(&checker_name("regular_unsafe"))
        .expect("regular definition remains addressable");
    let regular_body = regular
        .definition_body()
        .expect("unsafe definition body is retained");
    assert_eq!(regular.safety(), ConstantSafety::Unsafe);
    assert_eq!(regular_body.hint(), ReducibilityHint::Regular(17));
    assert_eq!(regular_body.hint().delta_height(), 17);
    assert_eq!(regular_body.safety(), DefinitionSafety::Unsafe);
    assert_eq!(regular.type_(), &leaf(4));
    assert_eq!(regular_body.value(), &leaf(5));
    assert!(regular.delta_body().is_none());

    let theorem = environment
        .find(&checker_name("body_theorem"))
        .expect("body-bearing theorem remains addressable");
    assert_eq!(theorem.kind(), ConstantKind::Theorem);
    assert_eq!(theorem.safety(), ConstantSafety::Safe);
    assert_eq!(theorem.body_value(), Some(&leaf(7)));
    assert!(theorem.definition_body().is_none());
    assert!(!theorem.is_delta_unfoldable());

    let opaque = environment
        .find(&checker_name("body_opaque"))
        .expect("body-bearing opaque remains addressable");
    assert_eq!(opaque.kind(), ConstantKind::Opaque);
    assert_eq!(opaque.safety(), ConstantSafety::Unsafe);
    assert_eq!(opaque.body_value(), Some(&leaf(9)));
    assert!(opaque.definition_body().is_none());
    assert!(!opaque.is_delta_unfoldable());

    for (index, (name, kind)) in header_kinds.iter().enumerate() {
        let header = environment
            .find(&checker_name(*name))
            .expect("header-only constant remains addressable");
        assert_eq!(header.kind(), *kind);
        assert_eq!(
            header.level_parameters(),
            &[checker_name(format!("u_{index}"))]
        );
        assert_eq!(header.type_(), &leaf(10 + index as u64));
        assert_eq!(
            header.safety(),
            if index & 1 == 0 {
                ConstantSafety::Safe
            } else {
                ConstantSafety::Unsafe
            }
        );
        assert!(header.definition_body().is_none());
        assert!(header.body_value().is_none());
        assert!(header.delta_body().is_none());
    }
}

#[test]
fn block_schema_retains_and_resources_every_inductive_family_field() {
    let inductive = checker_name("Tree");
    let constructor = checker_name("Tree.node");
    let recursor = checker_name("Tree.rec");
    let rows = vec![
        ConstantEntry::new(
            inductive.clone(),
            ConstantDeclaration::inductive(
                vec![checker_name("u")],
                leaf(1),
                ConstantSafety::Safe,
                InductiveDeclaration::new(
                    1,
                    2,
                    vec![inductive.clone()],
                    vec![constructor.clone()],
                    3,
                    true,
                    false,
                ),
            ),
        ),
        ConstantEntry::new(
            constructor.clone(),
            ConstantDeclaration::constructor(
                vec![checker_name("u")],
                leaf(2),
                ConstantSafety::Safe,
                ConstructorDeclaration::new(inductive.clone(), 4, 1, 5),
            ),
        ),
        ConstantEntry::new(
            recursor.clone(),
            ConstantDeclaration::recursor(
                vec![checker_name("u")],
                leaf(3),
                ConstantSafety::Safe,
                RecursorDeclaration::new(
                    vec![recursor.clone()],
                    1,
                    2,
                    1,
                    1,
                    vec![RecursorRule::new(constructor.clone(), 5, leaf(4))],
                    true,
                ),
            ),
        ),
        ConstantEntry::new(
            checker_name("Quot"),
            ConstantDeclaration::quotient(Vec::new(), leaf(5), QuotientKind::Type),
        ),
    ];
    let (environment, progress) = complete(ConstantEnvironment::build(
        rows.clone(),
        EnvironmentBudget::unlimited(),
    ));
    assert_eq!(progress.block_members, 5);
    let tree = environment.find(&inductive).expect("inductive retained");
    let tree_metadata = tree
        .inductive_metadata()
        .expect("inductive metadata retained");
    assert_eq!(tree_metadata.num_parameters(), 1);
    assert_eq!(tree_metadata.num_indices(), 2);
    assert_eq!(tree_metadata.mutual(), std::slice::from_ref(&inductive));
    assert_eq!(
        tree_metadata.constructors(),
        std::slice::from_ref(&constructor)
    );
    assert_eq!(tree_metadata.num_nested(), 3);
    assert!(tree_metadata.is_recursive());
    assert!(!tree_metadata.is_reflexive());
    let ctor = environment
        .find(&constructor)
        .expect("constructor retained")
        .constructor_metadata()
        .expect("constructor metadata retained");
    assert_eq!(ctor.inductive(), &inductive);
    assert_eq!(
        (ctor.index(), ctor.num_parameters(), ctor.num_fields()),
        (4, 1, 5)
    );
    let rec = environment
        .find(&recursor)
        .expect("recursor retained")
        .recursor_metadata()
        .expect("recursor metadata retained");
    assert_eq!((rec.num_parameters(), rec.num_indices()), (1, 2));
    assert_eq!((rec.num_motives(), rec.num_minors()), (1, 1));
    assert!(rec.k());
    assert_eq!(rec.rules()[0].constructor(), &constructor);
    assert_eq!(rec.rules()[0].num_fields(), 5);
    assert_eq!(rec.rules()[0].rhs(), &leaf(4));
    assert_eq!(
        environment
            .find(&checker_name("Quot"))
            .expect("quotient retained")
            .quotient_kind(),
        Some(QuotientKind::Type)
    );

    let one_less = EnvironmentBudget {
        max_block_members: progress.block_members - 1,
        ..EnvironmentBudget::unlimited()
    };
    assert!(matches!(
        ConstantEnvironment::build(rows, one_less),
        EnvironmentOutcome::Inconclusive(EnvironmentStop::Resource {
            limit: EnvironmentLimit::BlockMembers,
            ..
        })
    ));
}

#[test]
fn header_only_rows_never_charge_or_traverse_a_definition_value() {
    let parameter = checker_name("u");
    let header = header_entry(
        "shared",
        vec![parameter.clone()],
        leaf(0),
        ConstantKind::Axiom,
        ConstantSafety::Safe,
    );
    let definition = entry(
        "shared",
        vec![parameter],
        leaf(0),
        leaf(1),
        ReducibilityHint::Regular(1),
        DefinitionSafety::Safe,
        vec![checker_name("shared")],
    );
    let (_, header_progress) = complete(ConstantEnvironment::build(
        vec![header.clone()],
        EnvironmentBudget::unlimited(),
    ));
    let (_, definition_progress) = complete(ConstantEnvironment::build(
        vec![definition.clone()],
        EnvironmentBudget::unlimited(),
    ));

    assert_eq!(header_progress.constants, definition_progress.constants);
    assert_eq!(
        header_progress.level_parameters,
        definition_progress.level_parameters
    );
    assert_eq!(header_progress.block_members, 0);
    assert_eq!(definition_progress.block_members, 1);
    assert!(definition_progress.arena_nodes > header_progress.arena_nodes);
    assert!(definition_progress.owned_units > header_progress.owned_units);
    complete(ConstantEnvironment::build(
        vec![header],
        exact_budget(header_progress),
    ));

    assert!(matches!(
        ConstantEnvironment::build(
            vec![definition.clone()],
            EnvironmentBudget {
                max_block_members: 0,
                ..exact_budget(definition_progress)
            },
        ),
        EnvironmentOutcome::Inconclusive(EnvironmentStop::Resource {
            limit: EnvironmentLimit::BlockMembers,
            at,
            ..
        }) if at.field == EnvironmentField::MutualMember
    ));
    assert!(matches!(
        ConstantEnvironment::build(
            vec![definition],
            EnvironmentBudget {
                max_arena_nodes: header_progress.arena_nodes,
                ..exact_budget(definition_progress)
            },
        ),
        EnvironmentOutcome::Inconclusive(EnvironmentStop::Resource {
            limit: EnvironmentLimit::ArenaNodes,
            at,
            ..
        }) if at.field == EnvironmentField::ValueExpression
    ));
}

#[test]
fn permutation_independent_builds_compare_equal_and_iterate_canonically() {
    let rows = vec![
        simple_entry("zeta", 1),
        simple_entry("alpha", 2),
        simple_entry("middle", 3),
    ];
    let mut reversed = rows.clone();
    reversed.reverse();
    let (forward, forward_progress) = complete(ConstantEnvironment::build(
        rows,
        EnvironmentBudget::unlimited(),
    ));
    let (backward, backward_progress) = complete(ConstantEnvironment::build(
        reversed,
        EnvironmentBudget::unlimited(),
    ));
    assert_eq!(forward, backward);
    assert_eq!(forward_progress, backward_progress);
    assert_eq!(
        forward
            .constants()
            .map(|(name, _)| display_name(name))
            .collect::<Vec<_>>(),
        ["alpha", "middle", "zeta"]
    );
}

#[test]
fn persistent_extension_charges_only_the_candidate_and_preserves_both_snapshots() {
    let (base, _) = complete(ConstantEnvironment::build(
        vec![simple_entry("alpha", 1), simple_entry("middle", 2)],
        EnvironmentBudget::unlimited(),
    ));
    let candidate = simple_entry("zeta", 3);
    let (_, candidate_progress) = complete(ConstantEnvironment::build(
        vec![candidate.clone()],
        EnvironmentBudget::unlimited(),
    ));
    let (extended, extension_progress) =
        complete(base.extend(candidate.clone(), exact_budget(candidate_progress)));

    assert_eq!(extension_progress, candidate_progress);
    assert_eq!(base.len(), 2, "extension cannot mutate the base snapshot");
    assert!(base.find(&checker_name("zeta")).is_none());
    assert_eq!(extended.len(), 3);
    assert_eq!(
        extended
            .constants()
            .map(|(name, _)| display_name(name))
            .collect::<Vec<_>>(),
        ["alpha", "middle", "zeta"]
    );

    assert!(matches!(
        base.extend(
            candidate.clone(),
            EnvironmentBudget {
                max_constants: 0,
                ..exact_budget(candidate_progress)
            }
        ),
        EnvironmentOutcome::Inconclusive(EnvironmentStop::Resource {
            limit: EnvironmentLimit::Constants,
            allowed: 0,
            observed: 1,
            ..
        })
    ));
    assert_eq!(base.len(), 2);

    assert!(matches!(
        extended.extend(candidate, exact_budget(candidate_progress)),
        EnvironmentOutcome::Refused {
            refusal: EnvironmentRefusal::DuplicateConstant { name },
            ..
        } if name == checker_name("zeta")
    ));
    assert_eq!(extended.len(), 3);
}

#[test]
fn duplicate_names_and_level_parameters_refuse_deterministically_then_recover() {
    let duplicate_a = entry(
        "duplicate",
        Vec::new(),
        leaf(0),
        leaf(1),
        ReducibilityHint::Regular(1),
        DefinitionSafety::Safe,
        Vec::new(),
    );
    let duplicate_b = header_entry(
        "duplicate",
        Vec::new(),
        leaf(2),
        ConstantKind::Axiom,
        ConstantSafety::Safe,
    );
    for rows in [
        vec![duplicate_a.clone(), duplicate_b.clone()],
        vec![duplicate_b, duplicate_a],
    ] {
        assert!(matches!(
            ConstantEnvironment::build(rows, EnvironmentBudget::unlimited()),
            EnvironmentOutcome::Refused {
                refusal: EnvironmentRefusal::DuplicateConstant { ref name },
                ..
            } if name == &checker_name("duplicate")
        ));
    }

    let duplicate_parameter = entry(
        "parameters",
        vec![checker_name("u"), checker_name("u")],
        leaf(0),
        leaf(1),
        ReducibilityHint::Opaque,
        DefinitionSafety::Safe,
        Vec::new(),
    );
    assert!(matches!(
        ConstantEnvironment::build(vec![duplicate_parameter], EnvironmentBudget::unlimited()),
        EnvironmentOutcome::Refused {
            refusal: EnvironmentRefusal::DuplicateLevelParameter {
                constant: 0,
                first: 0,
                second: 1,
            },
            ..
        }
    ));

    let (recovered, _) = complete(ConstantEnvironment::build(
        vec![simple_entry("recovered", 9)],
        EnvironmentBudget::unlimited(),
    ));
    assert!(recovered.find(&checker_name("recovered")).is_some());
}

fn bounded_fixture() -> Vec<ConstantEntry> {
    vec![
        entry(
            "alpha",
            vec![checker_name("u")],
            decoded(&Expr::sort(Level::param(primary_name("u")))),
            leaf(1),
            ReducibilityHint::Regular(1),
            DefinitionSafety::Safe,
            vec![checker_name("alpha"), checker_name("beta")],
        ),
        entry(
            "beta",
            vec![checker_name("v")],
            decoded(&Expr::sort(Level::param(primary_name("v")))),
            decoded(&Expr::app(
                Expr::const_(primary_name("f"), Vec::new()),
                Expr::lit(Literal::Nat(NatLit::from_u64(2))),
            )),
            ReducibilityHint::Abbrev,
            DefinitionSafety::Partial,
            vec![checker_name("alpha"), checker_name("beta")],
        ),
        header_entry(
            "gamma",
            vec![checker_name("w")],
            decoded(&Expr::sort(Level::param(primary_name("w")))),
            ConstantKind::Axiom,
            ConstantSafety::Unsafe,
        ),
    ]
}

fn exact_budget(progress: EnvironmentProgress) -> EnvironmentBudget {
    EnvironmentBudget::new(
        progress.steps,
        progress.constants,
        progress.level_parameters,
        progress.block_members,
        progress.arena_nodes,
        progress.owned_units,
    )
}

fn expect_limit(budget: EnvironmentBudget, expected: EnvironmentLimit) {
    assert!(matches!(
        ConstantEnvironment::build(bounded_fixture(), budget),
        EnvironmentOutcome::Inconclusive(EnvironmentStop::Resource {
            limit,
            ..
        }) if limit == expected
    ));
}

#[test]
fn exact_aggregate_resource_boundaries_pass_and_each_one_less_stops_typed() {
    let (_, progress) = complete(ConstantEnvironment::build(
        bounded_fixture(),
        EnvironmentBudget::unlimited(),
    ));
    let exact = exact_budget(progress);
    let (_, exact_progress) = complete(ConstantEnvironment::build(bounded_fixture(), exact));
    assert_eq!(exact_progress, progress);

    expect_limit(
        EnvironmentBudget {
            max_steps: exact.max_steps - 1,
            ..exact
        },
        EnvironmentLimit::Steps,
    );
    expect_limit(
        EnvironmentBudget {
            max_constants: exact.max_constants - 1,
            ..exact
        },
        EnvironmentLimit::Constants,
    );
    expect_limit(
        EnvironmentBudget {
            max_level_parameters: exact.max_level_parameters - 1,
            ..exact
        },
        EnvironmentLimit::LevelParameters,
    );
    expect_limit(
        EnvironmentBudget {
            max_block_members: exact.max_block_members - 1,
            ..exact
        },
        EnvironmentLimit::BlockMembers,
    );
    expect_limit(
        EnvironmentBudget {
            max_arena_nodes: exact.max_arena_nodes - 1,
            ..exact
        },
        EnvironmentLimit::ArenaNodes,
    );
    expect_limit(
        EnvironmentBudget {
            max_owned_units: exact.max_owned_units - 1,
            ..exact
        },
        EnvironmentLimit::OwnedUnits,
    );
}

#[test]
fn generated_permutations_preserve_environment_identity_and_schema() {
    let base = (0usize..11)
        .map(|index| {
            let hint = match index % 3 {
                0 => ReducibilityHint::Opaque,
                1 => ReducibilityHint::Abbrev,
                _ => ReducibilityHint::Regular(index as u32),
            };
            let safety = match index % 3 {
                0 => DefinitionSafety::Unsafe,
                1 => DefinitionSafety::Safe,
                _ => DefinitionSafety::Partial,
            };
            let name = format!("generated_{index:02}");
            if index % 4 == 0 {
                header_entry(
                    &name,
                    vec![checker_name(format!("u_{index}"))],
                    leaf(index as u64),
                    [
                        ConstantKind::Axiom,
                        ConstantKind::Inductive,
                        ConstantKind::Recursor,
                    ][index / 4],
                    if index & 1 == 0 {
                        ConstantSafety::Safe
                    } else {
                        ConstantSafety::Unsafe
                    },
                )
            } else {
                entry(
                    &name,
                    vec![checker_name(format!("u_{index}"))],
                    leaf(index as u64),
                    leaf((index + 1) as u64),
                    hint,
                    safety,
                    vec![checker_name(&name)],
                )
            }
        })
        .collect::<Vec<_>>();
    let (expected, expected_progress) = complete(ConstantEnvironment::build(
        base.clone(),
        EnvironmentBudget::unlimited(),
    ));

    for seed in 0..128usize {
        let mut rows = base.clone();
        let length = rows.len();
        rows.rotate_left(seed % length);
        if seed & 1 == 1 {
            rows.reverse();
        }
        let (actual, progress) = complete(ConstantEnvironment::build(
            rows,
            EnvironmentBudget::unlimited(),
        ));
        assert_eq!(actual, expected, "permutation seed {seed}");
        assert_eq!(progress, expected_progress, "progress seed {seed}");
    }
}

#[test]
fn cancellation_is_a_failure_atomic_nonanswer_and_the_next_build_recovers() {
    let mut polls = 0u64;
    let stopped =
        ConstantEnvironment::build_with(bounded_fixture(), EnvironmentBudget::unlimited(), || {
            polls = polls.saturating_add(1);
            polls == 5
        });
    assert!(matches!(
        stopped,
        EnvironmentOutcome::Inconclusive(EnvironmentStop::Cancelled { .. })
    ));
    let (recovered, _) = complete(ConstantEnvironment::build(
        bounded_fixture(),
        EnvironmentBudget::unlimited(),
    ));
    assert_eq!(recovered.len(), 3);
}

fn deep_application() -> Result<WireExpr, String> {
    const DEPTH: usize = 50_000;
    let mut writer = CanonWriter::new();
    writer.schema(SCHEMA_EXPR);
    for _ in 0..DEPTH {
        writer.u8(5);
    }
    writer.u8(0);
    writer.u32(0);
    for _ in 0..DEPTH {
        writer.u8(0);
        writer.u32(1);
    }
    match decode_expr(&writer.into_bytes(), DecodeBudget::unlimited()) {
        DecodeOutcome::Complete(Ok(value)) => Ok(value),
        other => Err(format!("deep application did not decode: {other:?}")),
    }
}

fn deep_environment_child() -> Result<(), String> {
    const CONSTANTS: usize = 50_000;
    let type_ = leaf(0);
    let value = leaf(1);
    let deep = deep_application()?;
    let mut rows = Vec::with_capacity(CONSTANTS);
    for index in 0..CONSTANTS {
        let name = checker_name(format!("large_{index:05}"));
        rows.push(ConstantEntry::new(
            name.clone(),
            ConstantDeclaration::definition(
                Vec::new(),
                type_.clone(),
                ConstantSafety::Safe,
                DefinitionBody::new(
                    if index == 0 {
                        deep.clone()
                    } else {
                        value.clone()
                    },
                    ReducibilityHint::Regular(index as u32),
                    DefinitionSafety::Safe,
                    vec![name],
                ),
            ),
        ));
    }
    let (environment, progress) = complete(ConstantEnvironment::build(
        rows,
        EnvironmentBudget::unlimited(),
    ));
    if environment.len() != CONSTANTS {
        return Err(format!(
            "large environment retained {} constants",
            environment.len()
        ));
    }
    if progress.constants != CONSTANTS as u64 {
        return Err(format!(
            "large environment counted {} constants",
            progress.constants
        ));
    }
    if progress.arena_nodes < 150_000 {
        return Err(format!(
            "deep arena coverage was unexpectedly small: {}",
            progress.arena_nodes
        ));
    }
    Ok(())
}

#[test]
fn fifty_thousand_definitions_and_a_deep_payload_fit_a_64k_stack() {
    const CHILD_ENV: &str = "FLN_CHECKER_ENVIRONMENT_DEEP_CHILD";
    if std::env::var_os(CHILD_ENV).is_some() {
        let result = std::thread::Builder::new()
            .name("fln-checker-environment-deep".to_owned())
            .stack_size(64 * 1024)
            .spawn(deep_environment_child)
            .expect("spawn bounded-stack environment thread")
            .join()
            .expect("bounded-stack environment thread did not panic");
        result.expect("bounded-stack environment build");
        return;
    }

    let executable = std::env::current_exe().expect("current test executable");
    let output = Command::new(executable)
        .env(CHILD_ENV, "1")
        .args([
            "--exact",
            "fifty_thousand_constants_and_a_deep_definition_body_fit_a_64k_stack",
            "--nocapture",
        ])
        .output()
        .expect("run bounded-stack environment child");
    assert!(
        output.status.success(),
        "bounded-stack environment child failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn environment_production_code_has_no_primary_semantic_path() {
    let source = include_str!("../src/environment.rs");
    for forbidden in [
        "fln_env::",
        "fln_kernel::",
        "fln_core::expr",
        "from_canonical_bytes(",
        "from_canonical_bytes_budgeted(",
        "is_equiv(",
        "loose_bvar_range(",
    ] {
        assert!(
            !source.contains(forbidden),
            "checker environment reached a forbidden primary semantic path: {forbidden}"
        );
    }
}
