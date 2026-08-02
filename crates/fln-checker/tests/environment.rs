#![forbid(unsafe_code)]

use std::process::Command;

use fln_checker::environment::{
    Definition, DefinitionEntry, DefinitionEnvironment, DefinitionSafety, EnvironmentBudget,
    EnvironmentLimit, EnvironmentOutcome, EnvironmentProgress, EnvironmentRefusal, EnvironmentStop,
    ReducibilityHint,
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
) -> DefinitionEntry {
    DefinitionEntry::new(
        checker_name(name),
        Definition::new(level_parameters, type_, value, hint, safety, mutual),
    )
}

fn simple_entry(name: &str, value: u64) -> DefinitionEntry {
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

fn complete(outcome: EnvironmentOutcome) -> (DefinitionEnvironment, EnvironmentProgress) {
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
fn definition_schema_retains_hints_safety_types_values_and_mutual_membership() {
    let rows = vec![
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
            "opaque_partial",
            Vec::new(),
            leaf(2),
            leaf(3),
            ReducibilityHint::Opaque,
            DefinitionSafety::Partial,
            vec![checker_name("opaque_partial")],
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
    ];
    let (environment, _) = complete(DefinitionEnvironment::build(
        rows,
        EnvironmentBudget::unlimited(),
    ));

    let abbrev = environment
        .find(&checker_name("abbrev_safe"))
        .expect("abbreviation remains addressable");
    assert_eq!(abbrev.hint(), ReducibilityHint::Abbrev);
    assert_eq!(abbrev.hint().delta_height(), u32::MAX);
    assert_eq!(abbrev.safety(), DefinitionSafety::Safe);
    assert!(abbrev.is_delta_unfoldable());
    assert_eq!(abbrev.level_parameters(), &[checker_name("u")]);
    assert_eq!(abbrev.mutual().len(), 2);

    let opaque = environment
        .find(&checker_name("opaque_partial"))
        .expect("opaque-hint definition remains addressable");
    assert_eq!(opaque.hint(), ReducibilityHint::Opaque);
    assert_eq!(opaque.hint().delta_height(), 0);
    assert_eq!(opaque.safety(), DefinitionSafety::Partial);
    assert!(!opaque.is_delta_unfoldable());

    let regular = environment
        .find(&checker_name("regular_unsafe"))
        .expect("regular definition remains addressable");
    assert_eq!(regular.hint(), ReducibilityHint::Regular(17));
    assert_eq!(regular.hint().delta_height(), 17);
    assert_eq!(regular.safety(), DefinitionSafety::Unsafe);
    assert_eq!(regular.type_(), &leaf(4));
    assert_eq!(regular.value(), &leaf(5));
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
    let (forward, forward_progress) = complete(DefinitionEnvironment::build(
        rows,
        EnvironmentBudget::unlimited(),
    ));
    let (backward, backward_progress) = complete(DefinitionEnvironment::build(
        reversed,
        EnvironmentBudget::unlimited(),
    ));
    assert_eq!(forward, backward);
    assert_eq!(forward_progress, backward_progress);
    assert_eq!(
        forward
            .definitions()
            .map(|(name, _)| display_name(name))
            .collect::<Vec<_>>(),
        ["alpha", "middle", "zeta"]
    );
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
    let duplicate_b = entry(
        "duplicate",
        Vec::new(),
        leaf(2),
        leaf(3),
        ReducibilityHint::Abbrev,
        DefinitionSafety::Partial,
        Vec::new(),
    );
    for rows in [
        vec![duplicate_a.clone(), duplicate_b.clone()],
        vec![duplicate_b, duplicate_a],
    ] {
        assert!(matches!(
            DefinitionEnvironment::build(rows, EnvironmentBudget::unlimited()),
            EnvironmentOutcome::Refused {
                refusal: EnvironmentRefusal::DuplicateDefinition { ref name },
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
        DefinitionEnvironment::build(vec![duplicate_parameter], EnvironmentBudget::unlimited()),
        EnvironmentOutcome::Refused {
            refusal: EnvironmentRefusal::DuplicateLevelParameter {
                definition: 0,
                first: 0,
                second: 1,
            },
            ..
        }
    ));

    let (recovered, _) = complete(DefinitionEnvironment::build(
        vec![simple_entry("recovered", 9)],
        EnvironmentBudget::unlimited(),
    ));
    assert!(recovered.find(&checker_name("recovered")).is_some());
}

fn bounded_fixture() -> Vec<DefinitionEntry> {
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
    ]
}

fn exact_budget(progress: EnvironmentProgress) -> EnvironmentBudget {
    EnvironmentBudget::new(
        progress.steps,
        progress.definitions,
        progress.level_parameters,
        progress.mutual_members,
        progress.arena_nodes,
        progress.owned_units,
    )
}

fn expect_limit(budget: EnvironmentBudget, expected: EnvironmentLimit) {
    assert!(matches!(
        DefinitionEnvironment::build(bounded_fixture(), budget),
        EnvironmentOutcome::Inconclusive(EnvironmentStop::Resource {
            limit,
            ..
        }) if limit == expected
    ));
}

#[test]
fn exact_aggregate_resource_boundaries_pass_and_each_one_less_stops_typed() {
    let (_, progress) = complete(DefinitionEnvironment::build(
        bounded_fixture(),
        EnvironmentBudget::unlimited(),
    ));
    let exact = exact_budget(progress);
    let (_, exact_progress) = complete(DefinitionEnvironment::build(bounded_fixture(), exact));
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
            max_definitions: exact.max_definitions - 1,
            ..exact
        },
        EnvironmentLimit::Definitions,
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
            max_mutual_members: exact.max_mutual_members - 1,
            ..exact
        },
        EnvironmentLimit::MutualMembers,
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
    let base = (0..11)
        .map(|index| {
            let hint = match index % 3 {
                0 => ReducibilityHint::Opaque,
                1 => ReducibilityHint::Abbrev,
                _ => ReducibilityHint::Regular(index),
            };
            let safety = match index % 3 {
                0 => DefinitionSafety::Unsafe,
                1 => DefinitionSafety::Safe,
                _ => DefinitionSafety::Partial,
            };
            let name = format!("generated_{index:02}");
            entry(
                &name,
                vec![checker_name(format!("u_{index}"))],
                leaf(index as u64),
                leaf((index + 1) as u64),
                hint,
                safety,
                vec![checker_name(&name)],
            )
        })
        .collect::<Vec<_>>();
    let (expected, expected_progress) = complete(DefinitionEnvironment::build(
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
        let (actual, progress) = complete(DefinitionEnvironment::build(
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
    let stopped = DefinitionEnvironment::build_with(
        bounded_fixture(),
        EnvironmentBudget::unlimited(),
        || {
            polls = polls.saturating_add(1);
            polls == 5
        },
    );
    assert!(matches!(
        stopped,
        EnvironmentOutcome::Inconclusive(EnvironmentStop::Cancelled { .. })
    ));
    let (recovered, _) = complete(DefinitionEnvironment::build(
        bounded_fixture(),
        EnvironmentBudget::unlimited(),
    ));
    assert_eq!(recovered.len(), 2);
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
    const DEFINITIONS: usize = 50_000;
    let type_ = leaf(0);
    let value = leaf(1);
    let deep = deep_application()?;
    let mut rows = Vec::with_capacity(DEFINITIONS);
    for index in 0..DEFINITIONS {
        let name = checker_name(format!("large_{index:05}"));
        rows.push(DefinitionEntry::new(
            name.clone(),
            Definition::new(
                Vec::new(),
                type_.clone(),
                if index == 0 {
                    deep.clone()
                } else {
                    value.clone()
                },
                ReducibilityHint::Regular(index as u32),
                DefinitionSafety::Safe,
                vec![name],
            ),
        ));
    }
    let (environment, progress) = complete(DefinitionEnvironment::build(
        rows,
        EnvironmentBudget::unlimited(),
    ));
    if environment.len() != DEFINITIONS {
        return Err(format!(
            "large environment retained {} definitions",
            environment.len()
        ));
    }
    if progress.definitions != DEFINITIONS as u64 {
        return Err(format!(
            "large environment counted {} definitions",
            progress.definitions
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
            "fifty_thousand_definitions_and_a_deep_payload_fit_a_64k_stack",
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
