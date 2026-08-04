#![forbid(unsafe_code)]

use std::process::Command;

use fln_checker::defeq::{DefEqBudget, DefEqOutcome, DefEqStop, def_eq, def_eq_with};
use fln_checker::environment::{
    ConstantDeclaration, ConstantEntry, ConstantEnvironment, ConstantSafety, DefinitionBody,
    DefinitionSafety, EnvironmentBudget, EnvironmentOutcome, ReducibilityHint,
};
use fln_checker::nat_reduce::{
    NatNotReduced, NatReductionBudget, NatReductionInput, NatReductionLimit, NatReductionOperation,
    NatReductionOutcome, NatReductionStop, reduce_nat, reduce_nat_with,
};
use fln_checker::numeric::NatBudget;
use fln_checker::term::TermBudget;
use fln_checker::whnf::{WhnfBudget, WhnfContext};
use fln_checker::wire::{
    DecodeBudget, DecodeOutcome, ExprNode, NamePart, WireExpr, WireName, decode_expr, decode_name,
};
use fln_core::expr::{Expr, FVarId, Literal, NatLit};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_hash::canon::Canonical;

fn qualified(namespace: &str, leaf: &str) -> Name {
    Name::str(Name::str(Name::anonymous(), namespace), leaf)
}

fn checker_name(name: &Name) -> WireName {
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

fn literal(value: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(value)))
}

fn literal_limbs(limbs_le: Vec<u64>) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_limbs_le(limbs_le)))
}

fn literal_u128(value: u128) -> Expr {
    let low = value as u64;
    let high = (value >> 64) as u64;
    literal_limbs(if high == 0 {
        if low == 0 { Vec::new() } else { vec![low] }
    } else {
        vec![low, high]
    })
}

fn nat_constant(leaf: &str) -> Expr {
    Expr::const_(qualified("Nat", leaf), Vec::new())
}

fn unary(leaf: &str, value: Expr) -> Expr {
    Expr::app(nat_constant(leaf), value)
}

fn binary(leaf: &str, left: Expr, right: Expr) -> Expr {
    Expr::app(Expr::app(nat_constant(leaf), left), right)
}

fn companion() -> WireExpr {
    decoded(&literal(0))
}

fn reduced(
    expression: &Expr,
    context: &WhnfContext,
) -> fln_checker::nat_reduce::NatReductionResult {
    match reduce_nat(
        &decoded(expression),
        &companion(),
        context,
        NatReductionBudget::unlimited(),
    ) {
        NatReductionOutcome::Reduced(result) => result,
        other => panic!("Nat expression did not reduce: {other:?}"),
    }
}

fn output_nat(term: &WireExpr) -> Vec<u64> {
    match term.node(term.root()) {
        Some(ExprNode::NatLiteral { limbs_le }) => limbs_le.clone(),
        other => panic!("expected Nat literal output, got {other:?}"),
    }
}

fn output_u128(term: &WireExpr) -> u128 {
    let limbs = output_nat(term);
    assert!(limbs.len() <= 2, "bounded model escaped u128");
    u128::from(limbs.first().copied().unwrap_or(0))
        | (u128::from(limbs.get(1).copied().unwrap_or(0)) << 64)
}

fn output_bool(term: &WireExpr) -> bool {
    let Some(ExprNode::Constant { name, levels }) = term.node(term.root()) else {
        panic!("expected Bool constant output");
    };
    assert!(levels.is_empty());
    match name.parts() {
        [NamePart::Text(namespace), NamePart::Text(leaf)] if namespace == "Bool" => {
            match leaf.as_str() {
                "true" => true,
                "false" => false,
                other => panic!("unexpected Bool leaf {other}"),
            }
        }
        other => panic!("unexpected Bool name {other:?}"),
    }
}

fn constant_environment(entries: Vec<ConstantEntry>) -> ConstantEnvironment {
    match ConstantEnvironment::build(entries, EnvironmentBudget::unlimited()) {
        EnvironmentOutcome::Complete { environment, .. } => environment,
        other => panic!("constant environment did not build: {other:?}"),
    }
}

fn definition_context(name: &Name, value: Expr) -> WhnfContext {
    let entry = ConstantEntry::new(
        checker_name(name),
        ConstantDeclaration::definition(
            Vec::new(),
            decoded(&Expr::sort(Level::zero())),
            ConstantSafety::Safe,
            DefinitionBody::new(
                decoded(&value),
                ReducibilityHint::Regular(3),
                DefinitionSafety::Safe,
                Vec::new(),
            ),
        ),
    );
    WhnfContext::new(Vec::new(), Vec::new(), constant_environment(vec![entry]))
}

#[test]
fn exact_pinned_operation_table_materializes_nat_and_bool_results() {
    let context = WhnfContext::default();
    for (operation, expression, expected) in [
        (
            NatReductionOperation::Successor,
            unary("succ", literal(7)),
            8,
        ),
        (
            NatReductionOperation::Add,
            binary("add", literal(17), literal(5)),
            22,
        ),
        (
            NatReductionOperation::Subtract,
            binary("sub", literal(5), literal(17)),
            0,
        ),
        (
            NatReductionOperation::Multiply,
            binary("mul", literal(17), literal(5)),
            85,
        ),
        (
            NatReductionOperation::Divide,
            binary("div", literal(17), literal(5)),
            3,
        ),
        (
            NatReductionOperation::Modulo,
            binary("mod", literal(17), literal(5)),
            2,
        ),
        (
            NatReductionOperation::Gcd,
            binary("gcd", literal(18), literal(12)),
            6,
        ),
        (
            NatReductionOperation::Power,
            binary("pow", literal(3), literal(4)),
            81,
        ),
        (
            NatReductionOperation::BitAnd,
            binary("land", literal(12), literal(10)),
            8,
        ),
        (
            NatReductionOperation::BitOr,
            binary("lor", literal(12), literal(10)),
            14,
        ),
        (
            NatReductionOperation::BitXor,
            binary("xor", literal(12), literal(10)),
            6,
        ),
        (
            NatReductionOperation::ShiftLeft,
            binary("shiftLeft", literal(3), literal(5)),
            96,
        ),
        (
            NatReductionOperation::ShiftRight,
            binary("shiftRight", literal(96), literal(5)),
            3,
        ),
    ] {
        let result = reduced(&expression, &context);
        assert_eq!(result.operation, operation);
        assert_eq!(
            output_nat(&result.term),
            NatLit::from_u64(expected).limbs_le()
        );
    }

    for (leaf, left, right, expected) in [
        ("beq", 5, 5, true),
        ("beq", 5, 6, false),
        ("ble", 5, 6, true),
        ("ble", 6, 5, false),
    ] {
        let result = reduced(&binary(leaf, literal(left), literal(right)), &context);
        assert_eq!(output_bool(&result.term), expected);
    }

    assert_eq!(
        output_nat(&reduced(&binary("div", literal(7), nat_constant("zero")), &context,).term),
        Vec::<u64>::new()
    );
    assert_eq!(
        output_nat(&reduced(&binary("mod", literal(7), nat_constant("zero")), &context,).term),
        vec![7]
    );
}

#[test]
fn head_arity_level_cap_and_closed_pair_gates_are_exact() {
    let context = WhnfContext::default();
    let wrong_arity = decoded(&unary("add", literal(1)));
    assert!(matches!(
        reduce_nat(
            &wrong_arity,
            &companion(),
            &context,
            NatReductionBudget::unlimited(),
        ),
        NatReductionOutcome::NotReduced {
            reason: NatNotReduced::Arity {
                operation: NatReductionOperation::Add,
                expected: 2,
                actual: 1,
            },
            ..
        }
    ));

    let blt = decoded(&binary("blt", literal(1), literal(2)));
    assert!(matches!(
        reduce_nat(
            &blt,
            &companion(),
            &context,
            NatReductionBudget::unlimited(),
        ),
        NatReductionOutcome::NotReduced {
            reason: NatNotReduced::UnknownHead,
            ..
        }
    ));

    let levelled = Expr::app(
        Expr::app(
            Expr::const_(qualified("Nat", "add"), vec![Level::zero()]),
            literal(1),
        ),
        literal(2),
    );
    assert!(matches!(
        reduce_nat(
            &decoded(&levelled),
            &companion(),
            &context,
            NatReductionBudget::unlimited(),
        ),
        NatReductionOutcome::NotReduced {
            reason: NatNotReduced::HeadHasLevels,
            ..
        }
    ));

    let open = Expr::fvar(FVarId(qualified("test", "x")));
    assert!(matches!(
        reduce_nat(
            &decoded(&binary("add", open.clone(), literal(2))),
            &companion(),
            &context,
            NatReductionBudget::unlimited(),
        ),
        NatReductionOutcome::NotReduced {
            reason: NatNotReduced::OpenPair {
                input: NatReductionInput::Candidate,
            },
            ..
        }
    ));
    assert!(matches!(
        reduce_nat(
            &decoded(&binary("add", literal(1), literal(2))),
            &decoded(&open),
            &context,
            NatReductionBudget::unlimited(),
        ),
        NatReductionOutcome::NotReduced {
            reason: NatNotReduced::OpenPair {
                input: NatReductionInput::Companion,
            },
            ..
        }
    ));

    assert!(matches!(
        reduce_nat(
            &decoded(&binary(
                "pow",
                literal(1),
                literal(fln_checker::numeric::REDUCE_POW_MAX_EXP + 1),
            )),
            &companion(),
            &context,
            NatReductionBudget::unlimited(),
        ),
        NatReductionOutcome::NotReduced {
            reason: NatNotReduced::PowExponentAbovePinCap { .. },
            ..
        }
    ));

    let nested_over_cap = binary(
        "add",
        binary(
            "pow",
            literal(1),
            literal(fln_checker::numeric::REDUCE_POW_MAX_EXP + 1),
        ),
        literal(1),
    );
    assert!(matches!(
        reduce_nat(
            &decoded(&nested_over_cap),
            &companion(),
            &context,
            NatReductionBudget::unlimited(),
        ),
        NatReductionOutcome::NotReduced {
            reason: NatNotReduced::PowExponentAbovePinCap { .. },
            ..
        }
    ));
}

#[test]
fn nested_numeric_and_checker_definition_whnf_feed_operands() {
    let nested = binary(
        "mul",
        binary("add", literal(2), literal(3)),
        binary("add", literal(4), literal(5)),
    );
    assert_eq!(
        output_nat(&reduced(&nested, &WhnfContext::default()).term),
        vec![45]
    );

    let alias = qualified("Fixture", "seven");
    let context = definition_context(&alias, literal(7));
    let exposed = binary("add", Expr::const_(alias, Vec::new()), literal(5));
    let result = reduced(&exposed, &context);
    assert_eq!(output_nat(&result.term), vec![12]);
    assert!(result.progress.delta_unfolds >= 1);

    let nested_alias = qualified("Fixture", "nested");
    let context = definition_context(&nested_alias, binary("mul", literal(6), literal(7)));
    let result = reduced(
        &binary("add", Expr::const_(nested_alias, Vec::new()), literal(1)),
        &context,
    );
    assert_eq!(output_nat(&result.term), vec![43]);
    assert!(result.progress.numeric_reductions >= 2);
}

#[test]
fn generated_bounded_model_covers_every_expression_operation_independently() {
    fn gcd(mut left: u128, mut right: u128) -> u128 {
        while right != 0 {
            (left, right) = (right, left % right);
        }
        left
    }

    let context = WhnfContext::default();
    for left in 0_u128..=12 {
        let successor = reduced(&unary("succ", literal_u128(left)), &context);
        assert_eq!(output_u128(&successor.term), left + 1);

        for right in 0_u128..=8 {
            for (leaf, expected) in [
                ("add", left + right),
                ("sub", left.saturating_sub(right)),
                ("mul", left * right),
                ("div", left.checked_div(right).unwrap_or(0)),
                ("mod", left.checked_rem(right).unwrap_or(left)),
                ("gcd", gcd(left, right)),
                ("pow", left.pow(right as u32)),
                ("land", left & right),
                ("lor", left | right),
                ("xor", left ^ right),
                ("shiftLeft", left << (right as u32)),
                ("shiftRight", left >> (right as u32)),
            ] {
                let result = reduced(
                    &binary(leaf, literal_u128(left), literal_u128(right)),
                    &context,
                );
                assert_eq!(
                    output_u128(&result.term),
                    expected,
                    "Nat.{leaf} drifted for ({left}, {right})"
                );
            }

            for (leaf, expected) in [("beq", left == right), ("ble", left <= right)] {
                let result = reduced(
                    &binary(leaf, literal_u128(left), literal_u128(right)),
                    &context,
                );
                assert_eq!(
                    output_bool(&result.term),
                    expected,
                    "Nat.{leaf} drifted for ({left}, {right})"
                );
            }
        }
    }
}

#[test]
fn arbitrary_precision_shift_and_limb_carry_survive_expression_materialization() {
    let shifted = reduced(
        &binary("shiftLeft", literal(3), literal(65)),
        &WhnfContext::default(),
    );
    assert_eq!(output_nat(&shifted.term), vec![0, 6]);

    let all_two = literal_limbs(vec![u64::MAX, u64::MAX]);
    let carried = reduced(&binary("add", all_two, literal(1)), &WhnfContext::default());
    assert_eq!(output_nat(&carried.term), vec![0, 0, 1]);
}

#[test]
fn exact_one_less_limits_cancellation_and_recovery_are_typed() {
    let expression = decoded(&binary(
        "mul",
        literal_limbs(vec![u64::MAX, 9]),
        literal_limbs(vec![u64::MAX, 13]),
    ));
    let exact = match reduce_nat(
        &expression,
        &companion(),
        &WhnfContext::default(),
        NatReductionBudget::unlimited(),
    ) {
        NatReductionOutcome::Reduced(result) => result,
        other => panic!("exact reduction failed: {other:?}"),
    };
    assert!(exact.progress.steps > 1);
    assert!(exact.progress.numeric_steps > 1);

    let mut step_budget = NatReductionBudget::unlimited();
    step_budget.max_steps = exact.progress.steps - 1;
    assert!(matches!(
        reduce_nat(
            &expression,
            &companion(),
            &WhnfContext::default(),
            step_budget,
        ),
        NatReductionOutcome::Inconclusive(NatReductionStop::Resource {
            limit: NatReductionLimit::Steps,
            allowed,
            observed,
            ..
        }) if observed == allowed + 1
    ));

    let mut numeric_budget = NatReductionBudget::unlimited();
    numeric_budget.numeric = NatBudget::new(
        exact.progress.numeric_steps - 1,
        exact.progress.numeric_materialized_limbs,
    );
    assert!(matches!(
        reduce_nat(
            &expression,
            &companion(),
            &WhnfContext::default(),
            numeric_budget,
        ),
        NatReductionOutcome::Inconclusive(NatReductionStop::Numeric { .. })
    ));

    let mut saw_inner_cancellation = false;
    for cancel_at in 1_u64..=512 {
        let mut polls = 0_u64;
        let outcome = reduce_nat_with(
            &expression,
            &companion(),
            &WhnfContext::default(),
            NatReductionBudget::unlimited(),
            || {
                polls = polls.saturating_add(1);
                polls >= cancel_at
            },
        );
        if matches!(
            outcome,
            NatReductionOutcome::Inconclusive(NatReductionStop::Numeric { .. })
        ) {
            saw_inner_cancellation = true;
            break;
        }
    }
    assert!(saw_inner_cancellation);
    assert_eq!(
        output_nat(
            &match reduce_nat(
                &expression,
                &companion(),
                &WhnfContext::default(),
                NatReductionBudget::unlimited(),
            ) {
                NatReductionOutcome::Reduced(result) => result,
                other => panic!("recovery reduction failed: {other:?}"),
            }
            .term
        ),
        output_nat(&exact.term)
    );
}

#[test]
fn every_aggregate_reducer_limit_has_an_exact_and_one_less_boundary() {
    let alias = qualified("Fixture", "sevenForLimits");
    let context = definition_context(&alias, literal(7));
    let expression = decoded(&binary(
        "add",
        Expr::const_(alias, Vec::new()),
        literal_limbs(vec![u64::MAX, 3]),
    ));
    let companion = companion();
    let baseline = match reduce_nat(
        &expression,
        &companion,
        &context,
        NatReductionBudget::unlimited(),
    ) {
        NatReductionOutcome::Reduced(result) => result,
        other => panic!("aggregate baseline did not reduce: {other:?}"),
    };
    let progress = baseline.progress;
    assert!(progress.steps > 0);
    assert!(progress.work_items > 0);
    assert!(progress.generated_arenas > 0);
    assert!(progress.materialized_arena_nodes > 0);
    assert!(progress.materialized_owned_units > 0);
    assert!(progress.output_units > 0);
    assert!(progress.whnf_steps > 0);
    assert!(progress.whnf_reductions > 0);
    assert!(progress.numeric_steps > 0);
    assert!(progress.numeric_materialized_limbs > 0);

    let mut exact = NatReductionBudget::unlimited();
    exact.max_steps = progress.steps;
    exact.max_work_items = progress.work_items;
    exact.max_generated_arenas = progress.generated_arenas;
    exact.max_materialized_arena_nodes = progress.materialized_arena_nodes;
    exact.max_materialized_owned_units = progress.materialized_owned_units;
    exact.max_output_units = progress.output_units;
    exact.whnf.max_steps = progress.whnf_steps;
    exact.whnf.max_reductions = progress.whnf_reductions;
    exact.numeric = NatBudget::new(progress.numeric_steps, progress.numeric_materialized_limbs);
    let exact_outcome = reduce_nat(&expression, &companion, &context, exact);
    assert!(
        matches!(exact_outcome, NatReductionOutcome::Reduced(_)),
        "exact aggregate budget did not pass: {exact_outcome:?}"
    );

    let mut one_less_cases = Vec::new();
    let mut budget = exact;
    budget.max_steps -= 1;
    one_less_cases.push((NatReductionLimit::Steps, budget));
    let mut budget = exact;
    budget.max_work_items -= 1;
    one_less_cases.push((NatReductionLimit::WorkItems, budget));
    let mut budget = exact;
    budget.max_generated_arenas -= 1;
    one_less_cases.push((NatReductionLimit::GeneratedArenas, budget));
    let mut budget = exact;
    budget.max_materialized_arena_nodes -= 1;
    one_less_cases.push((NatReductionLimit::MaterializedArenaNodes, budget));
    let mut budget = exact;
    budget.max_materialized_owned_units -= 1;
    one_less_cases.push((NatReductionLimit::MaterializedOwnedUnits, budget));
    let mut budget = exact;
    budget.max_output_units -= 1;
    one_less_cases.push((NatReductionLimit::OutputUnits, budget));

    for (limit, budget) in one_less_cases {
        assert!(matches!(
            reduce_nat(&expression, &companion, &context, budget),
            NatReductionOutcome::Inconclusive(NatReductionStop::Resource {
                limit: actual,
                allowed,
                observed,
                ..
            }) if actual == limit && observed == allowed + 1
        ));
    }

    let mut one_less_whnf = exact;
    one_less_whnf.whnf.max_steps -= 1;
    assert!(matches!(
        reduce_nat(&expression, &companion, &context, one_less_whnf),
        NatReductionOutcome::Inconclusive(NatReductionStop::Whnf { .. })
    ));

    let mut one_less_numeric_steps = exact;
    one_less_numeric_steps.numeric.max_steps -= 1;
    assert!(matches!(
        reduce_nat(&expression, &companion, &context, one_less_numeric_steps,),
        NatReductionOutcome::Inconclusive(NatReductionStop::Numeric { .. })
    ));

    let mut one_less_numeric_limbs = exact;
    one_less_numeric_limbs.numeric.max_materialized_limbs -= 1;
    assert!(matches!(
        reduce_nat(&expression, &companion, &context, one_less_numeric_limbs,),
        NatReductionOutcome::Inconclusive(NatReductionStop::Numeric { .. })
    ));

    assert_eq!(
        output_nat(
            &match reduce_nat(
                &expression,
                &companion,
                &context,
                NatReductionBudget::unlimited(),
            ) {
                NatReductionOutcome::Reduced(result) => result,
                other => panic!("aggregate recovery did not reduce: {other:?}"),
            }
            .term
        ),
        output_nat(&baseline.term)
    );
}

fn deep_child() -> Result<(), String> {
    const DEPTH: usize = 50_000;
    let mut expression = nat_constant("zero");
    for _ in 0..DEPTH {
        expression = unary("succ", expression);
    }
    let result = match reduce_nat(
        &decoded(&expression),
        &companion(),
        &WhnfContext::default(),
        NatReductionBudget::unlimited(),
    ) {
        NatReductionOutcome::Reduced(result) => result,
        other => return Err(format!("deep reduction did not complete: {other:?}")),
    };
    if output_nat(&result.term) != vec![DEPTH as u64] {
        return Err(format!(
            "deep reduction produced {:?}",
            output_nat(&result.term)
        ));
    }
    Ok(())
}

#[test]
fn fifty_thousand_nested_successors_fit_a_64k_stack() {
    const CHILD_ENV: &str = "FLN_CHECKER_NAT_REDUCE_DEEP_CHILD";
    if std::env::var_os(CHILD_ENV).is_some() {
        let result = std::thread::Builder::new()
            .name("fln-checker-nat-reduce-deep".to_owned())
            .stack_size(64 * 1024)
            .spawn(deep_child)
            .expect("spawn bounded-stack Nat reduction thread")
            .join()
            .expect("bounded-stack Nat reduction thread did not panic");
        result.expect("bounded-stack Nat reduction");
        return;
    }

    let executable = std::env::current_exe().expect("current test executable");
    let output = Command::new(executable)
        .env(CHILD_ENV, "1")
        .args([
            "--exact",
            "fifty_thousand_nested_successors_fit_a_64k_stack",
            "--nocapture",
        ])
        .output()
        .expect("run bounded-stack Nat reduction child process");
    assert!(
        output.status.success(),
        "bounded-stack Nat reduction child failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn production_reducer_has_no_primary_or_shared_arithmetic_path() {
    let source = include_str!("../src/nat_reduce.rs");
    for forbidden in [
        "fln_core::",
        "fln_kernel::",
        "fln_bignum",
        "BigNat",
        "nat_add(",
        "nat_mul(",
    ] {
        assert!(
            !source.contains(forbidden),
            "checker Nat reducer shares forbidden semantic path `{forbidden}`"
        );
    }
}

#[test]
fn explicit_small_budgets_remain_constructible_without_hidden_defaults() {
    let budget = NatReductionBudget::new(
        10,
        20,
        3,
        8,
        16,
        4,
        WhnfBudget::new(5, 2, TermBudget::new(10, 10)),
        NatBudget::new(7, 4),
    );
    assert_eq!(budget.max_steps, 10);
    assert_eq!(budget.max_work_items, 20);
}

#[test]
fn conversion_dispatch_reduces_closed_nat_and_bool_pairs_after_core_and_delta_whnf() {
    let context = WhnfContext::default();
    let arithmetic = decoded(&binary(
        "mul",
        binary("add", literal(2), literal(3)),
        literal(9),
    ));
    let expected = decoded(&literal(45));
    let progress = match def_eq(&arithmetic, &expected, &context, DefEqBudget::unlimited()) {
        DefEqOutcome::Equal(progress) => progress,
        other => panic!("closed arithmetic conversion did not reduce: {other:?}"),
    };
    assert!(progress.nat_reductions >= 2);
    assert!(progress.nat_reduction_steps > 0);

    let boolean = decoded(&binary("beq", literal(7), literal(7)));
    let true_constant = decoded(&Expr::const_(qualified("Bool", "true"), Vec::new()));
    let progress = match def_eq(&boolean, &true_constant, &context, DefEqBudget::unlimited()) {
        DefEqOutcome::Equal(progress) => progress,
        other => panic!("closed Nat predicate conversion did not reduce: {other:?}"),
    };
    assert!(progress.nat_reductions >= 1);

    let alias = qualified("Fixture", "closedComputation");
    let context = definition_context(&alias, binary("add", literal(2), literal(3)));
    let alias = decoded(&Expr::const_(alias, Vec::new()));
    let expected = decoded(&literal(5));
    let progress = match def_eq(&alias, &expected, &context, DefEqBudget::unlimited()) {
        DefEqOutcome::Equal(progress) => progress,
        other => panic!("delta-exposed Nat conversion did not reduce: {other:?}"),
    };
    assert!(progress.delta_unfolds >= 1);
    assert!(progress.nat_reductions >= 1);
}

#[test]
fn conversion_dispatch_preserves_joint_closedness_caps_and_typed_stops() {
    let context = WhnfContext::default();
    let arithmetic = decoded(&binary("add", literal(17), literal(5)));
    let expected = decoded(&literal(22));
    let exact = match def_eq(&arithmetic, &expected, &context, DefEqBudget::unlimited()) {
        DefEqOutcome::Equal(progress) => progress,
        other => panic!("baseline Nat conversion did not reduce: {other:?}"),
    };
    assert!(exact.nat_reduction_steps > 1);

    let open = decoded(&Expr::fvar(FVarId(qualified("Fixture", "x"))));
    match def_eq(&arithmetic, &open, &context, DefEqBudget::unlimited()) {
        DefEqOutcome::Deferred { progress, .. } => {
            assert_eq!(progress.nat_reductions, 0);
        }
        other => panic!("open companion was not deferred: {other:?}"),
    }

    let over_cap = decoded(&binary(
        "pow",
        literal(1),
        literal(fln_checker::numeric::REDUCE_POW_MAX_EXP + 1),
    ));
    assert!(matches!(
        def_eq(
            &over_cap,
            &decoded(&literal(1)),
            &context,
            DefEqBudget::unlimited(),
        ),
        DefEqOutcome::Deferred { .. }
    ));

    let mut one_less = NatReductionBudget::unlimited();
    one_less.max_steps = exact.nat_reduction_steps - 1;
    assert!(matches!(
        def_eq(
            &arithmetic,
            &expected,
            &context,
            DefEqBudget::unlimited().with_nat(one_less),
        ),
        DefEqOutcome::Inconclusive(DefEqStop::NatReduction {
            stop: NatReductionStop::Resource {
                limit: NatReductionLimit::Steps,
                allowed,
                observed,
                ..
            },
            ..
        }) if observed == allowed + 1
    ));

    let mut saw_nat_cancellation = false;
    for cancel_at in 1_u64..=512 {
        let mut polls = 0_u64;
        let outcome = def_eq_with(
            &arithmetic,
            &expected,
            &context,
            DefEqBudget::unlimited(),
            || {
                polls = polls.saturating_add(1);
                polls >= cancel_at
            },
        );
        if matches!(
            outcome,
            DefEqOutcome::Inconclusive(DefEqStop::NatReduction { .. })
        ) {
            saw_nat_cancellation = true;
            break;
        }
    }
    assert!(saw_nat_cancellation);

    assert!(matches!(
        def_eq(&arithmetic, &expected, &context, DefEqBudget::unlimited(),),
        DefEqOutcome::Equal(_)
    ));
}
