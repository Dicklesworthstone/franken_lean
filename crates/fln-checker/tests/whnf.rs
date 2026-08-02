#![forbid(unsafe_code)]

use std::process::Command;

use fln_checker::term::{TermBudget, TermLimit, TermStop};
use fln_checker::whnf::{
    FreeBinding, ProjectionRule, WhnfBudget, WhnfContext, WhnfLimit, WhnfOutcome, WhnfPhase,
    WhnfRefusal, WhnfResult, WhnfStop, whnf, whnf_with,
};
use fln_checker::wire::{
    DecodeBudget, DecodeOutcome, ExprId, ExprNode, NamePart, WireExpr, WireName, decode_expr,
    decode_name,
};
use fln_core::expr::{BinderInfo, Expr, FVarId};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_hash::canon::{CanonWriter, Canonical, SCHEMA_EXPR};

fn primary_name(component: impl Into<String>) -> Name {
    Name::str(Name::anonymous(), component)
}

fn constant(component: impl Into<String>) -> Expr {
    Expr::const_(primary_name(component), Vec::new())
}

fn decoded(expression: &Expr) -> WireExpr {
    match decode_expr(&expression.to_canonical_bytes(), DecodeBudget::unlimited()) {
        DecodeOutcome::Complete(Ok(value)) => value,
        other => panic!("primary-produced expression did not decode: {other:?}"),
    }
}

fn checker_name(component: impl Into<String>) -> WireName {
    let name = primary_name(component);
    match decode_name(&name.to_canonical_bytes(), DecodeBudget::unlimited()) {
        DecodeOutcome::Complete(Ok(value)) => value,
        other => panic!("primary-produced name did not decode: {other:?}"),
    }
}

fn complete(outcome: WhnfOutcome) -> WhnfResult {
    match outcome {
        WhnfOutcome::Complete(result) => result,
        WhnfOutcome::Refused(refusal) => panic!("unexpected refusal: {refusal:?}"),
        WhnfOutcome::Inconclusive(stop) => panic!("unexpected non-answer: {stop:?}"),
        WhnfOutcome::InternalFault(fault) => panic!("unexpected internal fault: {fault:?}"),
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Frozen {
    Bound(u32),
    Free(String),
    Meta(String),
    Sort,
    Constant(String),
    Apply(Box<Frozen>, Box<Frozen>),
    Lambda(Box<Frozen>, Box<Frozen>),
    Forall(Box<Frozen>, Box<Frozen>),
    Let {
        type_: Box<Frozen>,
        value: Box<Frozen>,
        body: Box<Frozen>,
        non_dependent: bool,
    },
    Nat(Vec<u64>),
    String(String),
    Metadata(Box<Frozen>),
    Projection {
        structure: String,
        index: u64,
        expression: Box<Frozen>,
    },
}

fn model_name(name: &WireName) -> String {
    match name.parts().last() {
        Some(NamePart::Text(value)) => value.clone(),
        Some(NamePart::Numeric { value, overflowed }) => {
            format!("{value}:overflow={overflowed}")
        }
        None => String::new(),
    }
}

fn frozen(term: &WireExpr, root: ExprId) -> Frozen {
    match term.node(root).expect("well-formed checker expression") {
        ExprNode::Bound { index } => Frozen::Bound(*index),
        ExprNode::Free { name } => Frozen::Free(model_name(name)),
        ExprNode::Meta { name } => Frozen::Meta(model_name(name)),
        ExprNode::Sort { .. } => Frozen::Sort,
        ExprNode::Constant { name, .. } => Frozen::Constant(model_name(name)),
        ExprNode::Apply { function, argument } => Frozen::Apply(
            Box::new(frozen(term, *function)),
            Box::new(frozen(term, *argument)),
        ),
        ExprNode::Lambda {
            binder_type, body, ..
        } => Frozen::Lambda(
            Box::new(frozen(term, *binder_type)),
            Box::new(frozen(term, *body)),
        ),
        ExprNode::Forall {
            binder_type, body, ..
        } => Frozen::Forall(
            Box::new(frozen(term, *binder_type)),
            Box::new(frozen(term, *body)),
        ),
        ExprNode::Let {
            type_,
            value,
            body,
            non_dependent,
            ..
        } => Frozen::Let {
            type_: Box::new(frozen(term, *type_)),
            value: Box::new(frozen(term, *value)),
            body: Box::new(frozen(term, *body)),
            non_dependent: *non_dependent,
        },
        ExprNode::NatLiteral { limbs_le } => Frozen::Nat(limbs_le.clone()),
        ExprNode::StringLiteral(value) => Frozen::String(value.clone()),
        ExprNode::Metadata { expression, .. } => {
            Frozen::Metadata(Box::new(frozen(term, *expression)))
        }
        ExprNode::Projection {
            structure_name,
            index,
            expression,
        } => Frozen::Projection {
            structure: model_name(structure_name),
            index: *index,
            expression: Box::new(frozen(term, *expression)),
        },
    }
}

fn output_model(result: &WhnfResult) -> Frozen {
    frozen(&result.term, result.term.root())
}

fn apply(function: Frozen, argument: Frozen) -> Frozen {
    Frozen::Apply(Box::new(function), Box::new(argument))
}

fn identity() -> Expr {
    Expr::lam(
        Name::anonymous(),
        Expr::sort(Level::zero()),
        Expr::bvar(0).expect("identity bound variable packs"),
        BinderInfo::Default,
    )
}

fn binary_function() -> Expr {
    let body = Expr::app(
        Expr::bvar(1).expect("outer bound variable packs"),
        Expr::bvar(0).expect("inner bound variable packs"),
    );
    Expr::lam(
        primary_name("left"),
        Expr::sort(Level::zero()),
        Expr::lam(
            primary_name("right"),
            Expr::sort(Level::zero()),
            body,
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    )
}

fn projection_context(parameter_count: usize) -> WhnfContext {
    WhnfContext::new(
        Vec::new(),
        vec![ProjectionRule::new(
            checker_name("GeneratedStructure"),
            checker_name("GeneratedConstructor"),
            parameter_count,
        )],
    )
}

fn constructor(arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments
        .into_iter()
        .fold(constant("GeneratedConstructor"), Expr::app)
}

#[test]
fn generated_eager_whnf_matches_the_frozen_model() {
    const CASES: usize = 336;
    let context = WhnfContext::new(
        vec![FreeBinding::new(
            checker_name("generated_free"),
            decoded(&constant("generated_free_value")),
        )],
        projection_context(1).projection_rules().to_vec(),
    );
    for index in 0..CASES {
        let left_name = format!("left_{index}");
        let right_name = format!("right_{index}");
        let left = constant(left_name.clone());
        let right = constant(right_name.clone());
        let left_model = Frozen::Constant(left_name);
        let right_model = Frozen::Constant(right_name);
        let (input, expected) = match index % 8 {
            0 => (Expr::mdata(KVMap::new(), left), left_model),
            1 => (
                Expr::let_e(
                    primary_name("value"),
                    Expr::sort(Level::zero()),
                    left,
                    Expr::bvar(0).expect("let-bound variable packs"),
                    false,
                ),
                left_model,
            ),
            2 => (Expr::app(identity(), left), left_model),
            3 => (
                Expr::app(Expr::app(binary_function(), left), right),
                apply(left_model, right_model),
            ),
            4 => (
                Expr::app(Expr::app(identity(), left), right),
                apply(left_model, right_model),
            ),
            5 => (Expr::app(left, right), apply(left_model, right_model)),
            6 => (
                Expr::proj(
                    primary_name("GeneratedStructure"),
                    0,
                    constructor([left, right]),
                ),
                right_model,
            ),
            7 => (
                Expr::fvar(FVarId(primary_name("generated_free"))),
                Frozen::Constant("generated_free_value".to_owned()),
            ),
            _ => unreachable!("modulo eight"),
        };
        let result = complete(whnf(&decoded(&input), &context, WhnfBudget::unlimited()));
        assert_eq!(
            output_model(&result),
            expected,
            "frozen weak-head drift at generated case {index}"
        );
    }
}

#[test]
fn batched_beta_and_residual_reapplication_are_exact() {
    let left = constant("left");
    let right = constant("right");
    let tail = constant("tail");
    let expected_pair = apply(
        Frozen::Constant("left".to_owned()),
        Frozen::Constant("right".to_owned()),
    );

    let exact = complete(whnf(
        &decoded(&Expr::app(
            Expr::app(binary_function(), left.clone()),
            right.clone(),
        )),
        &WhnfContext::default(),
        WhnfBudget::unlimited(),
    ));
    assert_eq!(output_model(&exact), expected_pair);
    assert_eq!(
        exact.reductions, 1,
        "a contiguous beta batch is one weak-head reduction"
    );

    let residual = complete(whnf(
        &decoded(&Expr::app(
            Expr::app(Expr::app(binary_function(), left), right),
            tail,
        )),
        &WhnfContext::default(),
        WhnfBudget::unlimited(),
    ));
    assert_eq!(
        output_model(&residual),
        apply(expected_pair, Frozen::Constant("tail".to_owned()))
    );
    assert_eq!(
        residual.reductions, 1,
        "residual reapplication must not invent a second beta batch"
    );
}

#[test]
fn metadata_and_zeta_wrapping_do_not_change_the_weak_head() {
    let payload = constant("payload");
    let wrapped_value = Expr::mdata(KVMap::new(), payload);
    let wrapped_body = Expr::mdata(
        KVMap::new(),
        Expr::bvar(0).expect("let-bound variable packs"),
    );
    let input = Expr::mdata(
        KVMap::new(),
        Expr::let_e(
            primary_name("wrapped"),
            Expr::sort(Level::zero()),
            wrapped_value,
            wrapped_body,
            false,
        ),
    );
    let result = complete(whnf(
        &decoded(&input),
        &WhnfContext::default(),
        WhnfBudget::unlimited(),
    ));
    assert_eq!(
        output_model(&result),
        Frozen::Constant("payload".to_owned())
    );
    assert_eq!(
        result.reductions, 4,
        "outer metadata, zeta, body metadata, and value metadata are all live"
    );
}

#[test]
fn projection_parameter_offsets_are_exact() {
    let context = projection_context(2);
    let scrutinee = constructor([
        constant("parameter_0"),
        constant("parameter_1"),
        constant("field_0"),
        constant("field_1"),
    ]);
    for (index, expected) in [(0, "field_0"), (1, "field_1")] {
        let result = complete(whnf(
            &decoded(&Expr::proj(
                primary_name("GeneratedStructure"),
                index,
                scrutinee.clone(),
            )),
            &context,
            WhnfBudget::unlimited(),
        ));
        assert_eq!(
            output_model(&result),
            Frozen::Constant(expected.to_owned()),
            "projection {index} ignored the constructor parameter offset"
        );
        assert_eq!(result.reductions, 1);
    }

    let reapplied = complete(whnf(
        &decoded(&Expr::app(
            Expr::proj(primary_name("GeneratedStructure"), 0, scrutinee.clone()),
            constant("tail"),
        )),
        &context,
        WhnfBudget::unlimited(),
    ));
    assert_eq!(
        output_model(&reapplied),
        apply(
            Frozen::Constant("field_0".to_owned()),
            Frozen::Constant("tail".to_owned()),
        )
    );

    let absent = complete(whnf(
        &decoded(&Expr::proj(
            primary_name("GeneratedStructure"),
            2,
            scrutinee,
        )),
        &context,
        WhnfBudget::unlimited(),
    ));
    assert!(
        matches!(
            output_model(&absent),
            Frozen::Projection {
                structure,
                index: 2,
                ..
            } if structure == "GeneratedStructure"
        ),
        "an absent field stays stuck instead of being guessed"
    );
    assert_eq!(absent.reductions, 0);

    let overflow_context = projection_context(usize::MAX);
    assert_eq!(
        whnf(
            &decoded(&Expr::proj(
                primary_name("GeneratedStructure"),
                1,
                constructor(Vec::new()),
            )),
            &overflow_context,
            WhnfBudget::unlimited(),
        ),
        WhnfOutcome::Refused(WhnfRefusal::ProjectionIndexOverflow {
            rule: 0,
            parameter_count: usize::MAX,
            field_index: 1,
        })
    );
}

#[test]
fn stuck_constants_never_delta_unfold() {
    let constant_term = decoded(&constant("opaque"));
    let context = WhnfContext::new(
        vec![FreeBinding::new(
            checker_name("opaque"),
            decoded(&constant("wrong_delta_result")),
        )],
        Vec::new(),
    );
    let result = complete(whnf(&constant_term, &context, WhnfBudget::unlimited()));
    assert_eq!(output_model(&result), Frozen::Constant("opaque".to_owned()));
    assert_eq!(result.reductions, 0);

    let unmatched = complete(whnf(
        &decoded(&Expr::fvar(FVarId(primary_name("unmatched")))),
        &context,
        WhnfBudget::unlimited(),
    ));
    assert_eq!(
        output_model(&unmatched),
        Frozen::Free("unmatched".to_owned())
    );
    assert_eq!(unmatched.reductions, 0);
}

#[test]
fn duplicate_context_rows_and_free_cycles_are_refused() {
    let input = decoded(&constant("input"));
    let duplicate_free = WhnfContext::new(
        vec![
            FreeBinding::new(checker_name("x"), decoded(&constant("first"))),
            FreeBinding::new(checker_name("x"), decoded(&constant("second"))),
        ],
        Vec::new(),
    );
    assert_eq!(
        whnf(&input, &duplicate_free, WhnfBudget::unlimited()),
        WhnfOutcome::Refused(WhnfRefusal::DuplicateFreeBinding {
            first: 0,
            second: 1,
        })
    );

    let duplicate_projection = WhnfContext::new(
        Vec::new(),
        vec![
            ProjectionRule::new(checker_name("S"), checker_name("MkS"), 0),
            ProjectionRule::new(checker_name("S"), checker_name("OtherMkS"), 2),
        ],
    );
    assert_eq!(
        whnf(&input, &duplicate_projection, WhnfBudget::unlimited()),
        WhnfOutcome::Refused(WhnfRefusal::DuplicateProjectionRule {
            first: 0,
            second: 1,
        })
    );

    let cycle = WhnfContext::new(
        vec![
            FreeBinding::new(
                checker_name("x"),
                decoded(&Expr::fvar(FVarId(primary_name("y")))),
            ),
            FreeBinding::new(
                checker_name("y"),
                decoded(&Expr::fvar(FVarId(primary_name("x")))),
            ),
        ],
        Vec::new(),
    );
    let free_x = decoded(&Expr::fvar(FVarId(primary_name("x"))));
    assert_eq!(
        whnf(&free_x, &cycle, WhnfBudget::unlimited()),
        WhnfOutcome::Refused(WhnfRefusal::FreeBindingCycle { binding: 0 })
    );
}

#[test]
fn resource_and_cancellation_are_typed_nonanswers_with_exact_recovery() {
    let simple = decoded(&constant("simple"));
    assert!(matches!(
        whnf(
            &simple,
            &WhnfContext::default(),
            WhnfBudget::new(0, u64::MAX, TermBudget::unlimited()),
        ),
        WhnfOutcome::Inconclusive(WhnfStop::Resource {
            limit: WhnfLimit::Steps,
            allowed: 0,
            observed: 1,
            completed_steps: 0,
            completed_reductions: 0,
            ..
        })
    ));

    let metadata = decoded(&Expr::mdata(KVMap::new(), constant("payload")));
    assert!(matches!(
        whnf(
            &metadata,
            &WhnfContext::default(),
            WhnfBudget::new(u64::MAX, 0, TermBudget::unlimited()),
        ),
        WhnfOutcome::Inconclusive(WhnfStop::Resource {
            limit: WhnfLimit::Reductions,
            allowed: 0,
            observed: 1,
            completed_reductions: 0,
            ..
        })
    ));

    assert!(matches!(
        whnf(
            &simple,
            &WhnfContext::default(),
            WhnfBudget::new(u64::MAX, u64::MAX, TermBudget::new(0, u64::MAX),),
        ),
        WhnfOutcome::Inconclusive(WhnfStop::Materialization {
            phase: WhnfPhase::Initial,
            stop: TermStop::Resource {
                limit: TermLimit::Steps,
                allowed: 0,
                observed: 1,
                completed_steps: 0,
                ..
            },
            completed_steps: 1,
            completed_reductions: 0,
        })
    ));

    let stuck_application = decoded(&Expr::app(constant("function"), constant("argument")));
    assert!(matches!(
        whnf(
            &stuck_application,
            &WhnfContext::default(),
            WhnfBudget::new(
                u64::MAX,
                u64::MAX,
                TermBudget::unlimited().with_max_arena_nodes(3),
            ),
        ),
        WhnfOutcome::Inconclusive(WhnfStop::Materialization {
            phase: WhnfPhase::RebuildApplication,
            stop: TermStop::Resource {
                limit: TermLimit::ArenaNodes,
                allowed: 3,
                observed: 4,
                ..
            },
            completed_steps,
            completed_reductions: 0,
        }) if completed_steps > 0
    ));

    assert!(matches!(
        whnf_with(
            &metadata,
            &WhnfContext::default(),
            WhnfBudget::unlimited(),
            || true,
        ),
        WhnfOutcome::Inconclusive(WhnfStop::Cancelled {
            polls: 1,
            completed_steps: 0,
            completed_reductions: 0,
            ..
        })
    ));

    let expected = whnf(&metadata, &WhnfContext::default(), WhnfBudget::unlimited());
    let mut polls = 0_u64;
    let interrupted = whnf_with(
        &metadata,
        &WhnfContext::default(),
        WhnfBudget::unlimited(),
        || {
            polls = polls.saturating_add(1);
            polls >= 2
        },
    );
    assert!(matches!(
        interrupted,
        WhnfOutcome::Inconclusive(WhnfStop::Materialization {
            phase: WhnfPhase::Initial,
            stop: TermStop::Cancelled { .. },
            completed_steps: 1,
            completed_reductions: 0,
        })
    ));
    assert_eq!(
        whnf(&metadata, &WhnfContext::default(), WhnfBudget::unlimited(),),
        expected,
        "a typed non-answer cannot mutate the source or poison exact recovery"
    );
}

fn deep_child() -> Result<(), String> {
    const DEPTH: usize = 50_000;
    let mut writer = CanonWriter::new();
    writer.schema(SCHEMA_EXPR);
    for _ in 0..DEPTH {
        writer.u8(11);
        writer.u64(0);
    }
    writer.u8(0);
    writer.u32(0);
    let term = match decode_expr(&writer.into_bytes(), DecodeBudget::unlimited()) {
        DecodeOutcome::Complete(Ok(value)) => value,
        _ => return Err("deep primary-shaped metadata chain did not decode".to_owned()),
    };
    let result = match whnf(&term, &WhnfContext::default(), WhnfBudget::unlimited()) {
        WhnfOutcome::Complete(value) => value,
        _ => return Err("deep metadata reduction did not complete".to_owned()),
    };
    if result.reductions != DEPTH as u64 {
        return Err(format!(
            "deep reduction count drifted: {}",
            result.reductions
        ));
    }
    if result.term.nodes().len() != 1
        || !matches!(
            result.term.node(result.term.root()),
            Some(ExprNode::Bound { index: 0 })
        )
    {
        return Err("deep weak head was not the terminal bound variable".to_owned());
    }
    Ok(())
}

#[test]
fn deep_wrapper_reduction_fits_a_64k_stack() {
    const CHILD_ENV: &str = "FLN_CHECKER_WHNF_DEEP_CHILD";
    if std::env::var_os(CHILD_ENV).is_some() {
        let result = std::thread::Builder::new()
            .name("fln-checker-whnf-deep".to_owned())
            .stack_size(64 * 1024)
            .spawn(deep_child)
            .expect("spawn bounded-stack child thread")
            .join()
            .expect("bounded-stack child thread did not panic");
        result.expect("bounded-stack weak-head reduction");
        return;
    }

    let executable = std::env::current_exe().expect("current test executable");
    let output = Command::new(executable)
        .env(CHILD_ENV, "1")
        .args([
            "--exact",
            "deep_wrapper_reduction_fits_a_64k_stack",
            "--nocapture",
        ])
        .output()
        .expect("run bounded-stack child process");
    assert!(
        output.status.success(),
        "bounded-stack child failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn whnf_production_code_has_no_primary_semantic_path() {
    let source = include_str!("../src/whnf.rs");
    for forbidden in [
        "fln_core::",
        "TypeChecker",
        "Expr::whnf",
        "Expr::instantiate",
        "fln_kernel",
    ] {
        assert!(
            !source.contains(forbidden),
            "checker WHNF source shares forbidden semantic path `{forbidden}`"
        );
    }
}
