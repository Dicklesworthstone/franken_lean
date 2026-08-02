#![forbid(unsafe_code)]

use std::process::Command;

use fln_checker::defeq::{
    DefEqBudget, DefEqLimit, DefEqMismatch, DefEqOutcome, DefEqSide, DefEqStop, ExpressionClass,
    QuickDefEqBudget, QuickDefEqDeferred, QuickDefEqLimit, QuickDefEqMismatch, QuickDefEqOutcome,
    QuickDefEqResult, QuickDefEqStop, def_eq, def_eq_with, quick_def_eq, quick_def_eq_with,
};
use fln_checker::term::TermBudget;
use fln_checker::whnf::{
    FreeBinding, ProjectionRule, WhnfBudget, WhnfContext, WhnfLimit, WhnfRefusal, WhnfStop,
};
use fln_checker::wire::{
    DecodeBudget, DecodeOutcome, WireExpr, WireName, decode_expr, decode_name,
};
use fln_core::expr::{BinderInfo, Expr, FVarId, Literal, NatLit};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_hash::canon::{CanonWriter, Canonical, SCHEMA_EXPR};

fn name(component: impl Into<String>) -> Name {
    Name::str(Name::anonymous(), component)
}

fn constant(component: impl Into<String>) -> Expr {
    Expr::const_(name(component), Vec::new())
}

fn decoded(expression: &Expr) -> WireExpr {
    match decode_expr(&expression.to_canonical_bytes(), DecodeBudget::unlimited()) {
        DecodeOutcome::Complete(Ok(value)) => value,
        other => panic!("primary-produced expression did not decode: {other:?}"),
    }
}

fn checker_name(component: impl Into<String>) -> WireName {
    let value = name(component);
    match decode_name(&value.to_canonical_bytes(), DecodeBudget::unlimited()) {
        DecodeOutcome::Complete(Ok(value)) => value,
        other => panic!("primary-produced name did not decode: {other:?}"),
    }
}

fn identity() -> Expr {
    Expr::lam(
        Name::anonymous(),
        Expr::sort(Level::zero()),
        Expr::bvar(0).expect("identity bound variable"),
        BinderInfo::Default,
    )
}

fn slow_equal(
    left: &WireExpr,
    right: &WireExpr,
    context: &WhnfContext,
) -> fln_checker::defeq::DefEqProgress {
    match def_eq(left, right, context, DefEqBudget::unlimited()) {
        DefEqOutcome::Equal(progress) => progress,
        other => panic!("expected pure definitional equality, got {other:?}"),
    }
}

fn equal(left: &WireExpr, right: &WireExpr) -> QuickDefEqResult {
    match quick_def_eq(left, right, QuickDefEqBudget::unlimited()) {
        QuickDefEqOutcome::Equal(result) => result,
        other => panic!("expected quick equality, got {other:?}"),
    }
}

fn parameter(component: &str) -> Level {
    Level::param(name(component))
}

#[test]
fn generated_quick_congruence_is_alpha_and_metadata_insensitive() {
    const CASES: usize = 384;
    for index in 0..CASES {
        let universe = parameter(&format!("u{}", index % 7));
        let equivalent = Level::max(universe.clone(), Level::zero()).expect("shallow level");
        let left_constant = Expr::const_(name(format!("C{}", index % 13)), vec![universe]);
        let right_constant = Expr::const_(name(format!("C{}", index % 13)), vec![equivalent]);
        let left_body = Expr::app(
            Expr::bvar(0).expect("generated bound variable"),
            left_constant,
        );
        let right_body = Expr::mdata(
            KVMap::new(),
            Expr::app(
                Expr::bvar(0).expect("generated bound variable"),
                right_constant,
            ),
        );
        let left = Expr::lam(
            name(format!("left_{index}")),
            Expr::sort(Level::zero()),
            left_body,
            BinderInfo::Default,
        );
        let right = Expr::lam(
            name(format!("right_{index}")),
            Expr::sort(Level::zero()),
            right_body,
            BinderInfo::Implicit,
        );
        let result = equal(&decoded(&left), &decoded(&right));
        assert!(
            result.comparisons >= 5,
            "generated case {index} skipped a live congruence edge"
        );
    }
}

#[test]
fn rigid_sort_and_literal_mismatches_are_exact_non_equal_answers() {
    let universe = parameter("u");
    let collapsed = Level::imax(Level::one(), universe.clone()).expect("shallow level");
    assert_eq!(
        equal(
            &decoded(&Expr::sort(collapsed)),
            &decoded(&Expr::sort(universe)),
        )
        .comparisons,
        1,
        "KR-303 must use one-pass universe equivalence, not raw level shape"
    );

    let sort_zero = decoded(&Expr::sort(Level::zero()));
    let sort_one = decoded(&Expr::sort(Level::one()));
    assert!(matches!(
        quick_def_eq(&sort_zero, &sort_one, QuickDefEqBudget::unlimited()),
        QuickDefEqOutcome::NotEqual {
            mismatch: QuickDefEqMismatch::SortLevels { .. },
            completed_comparisons: 1,
        }
    ));

    let one = decoded(&Expr::lit(Literal::Nat(NatLit::from_u64(1))));
    let two = decoded(&Expr::lit(Literal::Nat(NatLit::from_u64(2))));
    assert!(matches!(
        quick_def_eq(&one, &two, QuickDefEqBudget::unlimited()),
        QuickDefEqOutcome::NotEqual {
            mismatch: QuickDefEqMismatch::NatLiterals { .. },
            completed_comparisons: 1,
        }
    ));

    let left = decoded(&Expr::lit(Literal::Str("left".to_owned())));
    let right = decoded(&Expr::lit(Literal::Str("right".to_owned())));
    assert!(matches!(
        quick_def_eq(&left, &right, QuickDefEqBudget::unlimited()),
        QuickDefEqOutcome::NotEqual {
            mismatch: QuickDefEqMismatch::StringLiterals { .. },
            completed_comparisons: 1,
        }
    ));
}

#[test]
fn slow_or_environment_sensitive_cases_defer_instead_of_rejecting() {
    let left = decoded(&Expr::const_(name("C"), vec![Level::zero()]));
    let right = decoded(&Expr::const_(name("C"), vec![Level::one()]));
    assert!(matches!(
        quick_def_eq(&left, &right, QuickDefEqBudget::unlimited()),
        QuickDefEqOutcome::Deferred {
            need: QuickDefEqDeferred {
                left_class: ExpressionClass::Constant,
                right_class: ExpressionClass::Constant,
                ..
            },
            ..
        }
    ));

    let beta = decoded(&Expr::app(
        Expr::lam(
            Name::anonymous(),
            Expr::sort(Level::zero()),
            Expr::bvar(0).expect("identity body"),
            BinderInfo::Default,
        ),
        constant("payload"),
    ));
    let payload = decoded(&constant("payload"));
    assert!(matches!(
        quick_def_eq(&beta, &payload, QuickDefEqBudget::unlimited()),
        QuickDefEqOutcome::Deferred {
            need: QuickDefEqDeferred {
                left_class: ExpressionClass::Apply,
                right_class: ExpressionClass::Constant,
                ..
            },
            ..
        }
    ));
}

#[test]
fn pure_conversion_preserves_pending_siblings_across_beta_reduction() {
    let function = constant("function");
    let argument = constant("argument");
    let left = decoded(&Expr::app(
        Expr::app(identity(), function.clone()),
        Expr::app(identity(), argument.clone()),
    ));
    let right = decoded(&Expr::app(function, argument));
    let progress = slow_equal(&left, &right, &WhnfContext::default());
    assert_eq!(progress.quick_comparisons, 2);
    assert_eq!(progress.slow_comparisons, 5);
    assert_eq!(progress.normalizations, 4);
    assert_eq!(progress.whnf_reductions, 2);
    assert_eq!(progress.materialized_arena_nodes, 4);
}

#[test]
fn pure_conversion_closes_zeta_free_binding_and_registered_projection() {
    let payload = constant("payload");
    let zeta = Expr::let_e(
        name("x"),
        Expr::sort(Level::zero()),
        Expr::mdata(KVMap::new(), payload.clone()),
        Expr::mdata(KVMap::new(), Expr::bvar(0).expect("let-bound variable")),
        false,
    );
    assert!(
        slow_equal(&decoded(&zeta), &decoded(&payload), &WhnfContext::default(),).whnf_reductions
            >= 1
    );

    let free_name = name("bound_free");
    let free = decoded(&Expr::fvar(FVarId(free_name)));
    let free_value = decoded(&constant("free_value"));
    let free_context = WhnfContext::new(
        vec![FreeBinding::new(
            checker_name("bound_free"),
            free_value.clone(),
        )],
        Vec::new(),
    );
    let free_progress = slow_equal(&free, &free_value, &free_context);
    assert_eq!(free_progress.whnf_reductions, 1);

    let constructor = Expr::app(
        Expr::app(constant("MkS"), constant("parameter")),
        constant("field"),
    );
    let projection = decoded(&Expr::proj(name("S"), 0, constructor));
    let field = decoded(&constant("field"));
    let projection_context = WhnfContext::new(
        Vec::new(),
        vec![ProjectionRule::new(
            checker_name("S"),
            checker_name("MkS"),
            1,
        )],
    );
    let projection_progress = slow_equal(&projection, &field, &projection_context);
    assert_eq!(projection_progress.whnf_reductions, 1);
}

#[test]
fn generated_pure_reductions_match_their_frozen_targets() {
    const CASES: usize = 320;
    for index in 0..CASES {
        let payload = constant(format!("payload_{index}"));
        let (left, context) = match index % 4 {
            0 => (
                Expr::app(identity(), payload.clone()),
                WhnfContext::default(),
            ),
            1 => (
                Expr::let_e(
                    name(format!("x_{index}")),
                    Expr::sort(Level::zero()),
                    payload.clone(),
                    Expr::bvar(0).expect("generated let-bound variable"),
                    false,
                ),
                WhnfContext::default(),
            ),
            2 => {
                let free_component = format!("free_{index}");
                (
                    Expr::fvar(FVarId(name(free_component.clone()))),
                    WhnfContext::new(
                        vec![FreeBinding::new(
                            checker_name(free_component),
                            decoded(&payload),
                        )],
                        Vec::new(),
                    ),
                )
            }
            3 => (
                Expr::proj(
                    name("GeneratedStructure"),
                    0,
                    Expr::app(
                        Expr::app(
                            constant("GeneratedConstructor"),
                            constant(format!("parameter_{index}")),
                        ),
                        payload.clone(),
                    ),
                ),
                WhnfContext::new(
                    Vec::new(),
                    vec![ProjectionRule::new(
                        checker_name("GeneratedStructure"),
                        checker_name("GeneratedConstructor"),
                        1,
                    )],
                ),
            ),
            _ => unreachable!("modulo four"),
        };
        let progress = slow_equal(&decoded(&left), &decoded(&payload), &context);
        assert!(
            progress.whnf_reductions >= 1,
            "generated case {index} reached its target without exercising reduction"
        );
    }
}

#[test]
fn stable_environment_sensitive_pairs_remain_deferred_after_pure_whnf() {
    let left = decoded(&Expr::const_(name("C"), vec![Level::zero()]));
    let right = decoded(&Expr::const_(name("C"), vec![Level::one()]));
    assert!(matches!(
        def_eq(
            &left,
            &right,
            &WhnfContext::default(),
            DefEqBudget::unlimited(),
        ),
        DefEqOutcome::Deferred {
            need: fln_checker::defeq::DefEqDeferred {
                left_class: ExpressionClass::Constant,
                right_class: ExpressionClass::Constant,
                ..
            },
            progress: fln_checker::defeq::DefEqProgress {
                normalizations: 2,
                whnf_reductions: 0,
                ..
            },
        }
    ));

    let projection = decoded(&Expr::proj(
        name("UnknownStructure"),
        0,
        constant("scrutinee"),
    ));
    let field = decoded(&constant("field"));
    assert!(matches!(
        def_eq(
            &projection,
            &field,
            &WhnfContext::default(),
            DefEqBudget::unlimited(),
        ),
        DefEqOutcome::Deferred {
            need: fln_checker::defeq::DefEqDeferred {
                left_class: ExpressionClass::Projection,
                right_class: ExpressionClass::Constant,
                ..
            },
            ..
        }
    ));
}

#[test]
fn rigid_negative_can_be_discovered_after_pure_reduction() {
    let one = Expr::lit(Literal::Nat(NatLit::from_u64(1)));
    let two = Expr::lit(Literal::Nat(NatLit::from_u64(2)));
    let reduced_one = decoded(&Expr::app(
        Expr::lam(
            Name::anonymous(),
            Expr::sort(Level::zero()),
            one,
            BinderInfo::Default,
        ),
        constant("ignored"),
    ));
    assert!(matches!(
        def_eq(
            &reduced_one,
            &decoded(&two),
            &WhnfContext::default(),
            DefEqBudget::unlimited(),
        ),
        DefEqOutcome::NotEqual {
            mismatch: DefEqMismatch::NatLiterals { .. },
            progress: fln_checker::defeq::DefEqProgress {
                whnf_reductions: 1,
                ..
            },
        }
    ));
}

#[test]
fn slow_resources_refusals_and_cancellation_are_typed_and_recoverable() {
    let payload = constant("payload");
    let beta = decoded(&Expr::app(identity(), payload.clone()));
    let value = decoded(&payload);

    let no_comparisons = DefEqBudget::new(
        QuickDefEqBudget::unlimited(),
        0,
        u64::MAX,
        u64::MAX,
        u64::MAX,
        WhnfBudget::unlimited(),
    );
    assert!(matches!(
        def_eq(&beta, &value, &WhnfContext::default(), no_comparisons,),
        DefEqOutcome::Inconclusive(DefEqStop::Resource {
            limit: DefEqLimit::SlowComparisons,
            allowed: 0,
            observed: 1,
            ..
        })
    ));

    let identical = decoded(&constant("identical"));
    assert!(matches!(
        def_eq(
            &identical,
            &identical,
            &WhnfContext::default(),
            no_comparisons,
        ),
        DefEqOutcome::Equal(fln_checker::defeq::DefEqProgress {
            quick_comparisons: 1,
            slow_comparisons: 0,
            normalizations: 0,
            ..
        })
    ));

    let no_normalizations = DefEqBudget::new(
        QuickDefEqBudget::unlimited(),
        u64::MAX,
        0,
        u64::MAX,
        u64::MAX,
        WhnfBudget::unlimited(),
    );
    assert!(matches!(
        def_eq(&beta, &value, &WhnfContext::default(), no_normalizations,),
        DefEqOutcome::Inconclusive(DefEqStop::Resource {
            limit: DefEqLimit::Normalizations,
            allowed: 0,
            observed: 1,
            ..
        })
    ));

    let no_materialized_nodes = DefEqBudget::new(
        QuickDefEqBudget::unlimited(),
        u64::MAX,
        u64::MAX,
        0,
        u64::MAX,
        WhnfBudget::unlimited(),
    );
    assert!(matches!(
        def_eq(
            &beta,
            &value,
            &WhnfContext::default(),
            no_materialized_nodes,
        ),
        DefEqOutcome::Inconclusive(DefEqStop::Resource {
            limit: DefEqLimit::MaterializedArenaNodes,
            allowed: 0,
            observed: 1,
            ..
        })
    ));

    let no_materialized_units = DefEqBudget::new(
        QuickDefEqBudget::unlimited(),
        u64::MAX,
        u64::MAX,
        u64::MAX,
        0,
        WhnfBudget::unlimited(),
    );
    assert!(matches!(
        def_eq(
            &beta,
            &value,
            &WhnfContext::default(),
            no_materialized_units,
        ),
        DefEqOutcome::Inconclusive(DefEqStop::Resource {
            limit: DefEqLimit::MaterializedOwnedUnits,
            allowed: 0,
            observed,
            ..
        }) if observed > 0
    ));

    let nested_left = decoded(&Expr::app(
        Expr::app(identity(), constant("function")),
        Expr::app(identity(), constant("argument")),
    ));
    let nested_right = decoded(&Expr::app(constant("function"), constant("argument")));
    let one_reduction = DefEqBudget::new(
        QuickDefEqBudget::unlimited(),
        u64::MAX,
        u64::MAX,
        u64::MAX,
        u64::MAX,
        WhnfBudget::new(u64::MAX, 1, TermBudget::unlimited()),
    );
    assert!(matches!(
        def_eq(
            &nested_left,
            &nested_right,
            &WhnfContext::default(),
            one_reduction,
        ),
        DefEqOutcome::Inconclusive(DefEqStop::Whnf {
            side: DefEqSide::Left,
            stop: WhnfStop::Resource {
                limit: WhnfLimit::Reductions,
                allowed: 0,
                observed: 1,
                ..
            },
            ..
        })
    ));

    let duplicate_context = WhnfContext::new(
        vec![
            FreeBinding::new(checker_name("x"), decoded(&constant("first"))),
            FreeBinding::new(checker_name("x"), decoded(&constant("second"))),
        ],
        Vec::new(),
    );
    let free = decoded(&Expr::fvar(FVarId(name("x"))));
    assert!(matches!(
        def_eq(
            &free,
            &decoded(&constant("first")),
            &duplicate_context,
            DefEqBudget::unlimited(),
        ),
        DefEqOutcome::Refused {
            side: DefEqSide::Left,
            refusal: WhnfRefusal::DuplicateFreeBinding {
                first: 0,
                second: 1,
            },
            ..
        }
    ));

    let mut polls = 0_u64;
    assert!(matches!(
        def_eq_with(
            &beta,
            &value,
            &WhnfContext::default(),
            DefEqBudget::unlimited(),
            || {
                polls = polls.saturating_add(1);
                polls >= 3
            },
        ),
        DefEqOutcome::Inconclusive(DefEqStop::Cancelled {
            polls: 1,
            progress: fln_checker::defeq::DefEqProgress {
                quick_comparisons: 1,
                slow_comparisons: 0,
                ..
            },
        })
    ));

    assert!(matches!(
        def_eq(
            &beta,
            &value,
            &WhnfContext::default(),
            DefEqBudget::unlimited(),
        ),
        DefEqOutcome::Equal(_)
    ));
}

#[test]
fn resource_and_cancellation_are_typed_nonanswers_with_exact_recovery() {
    let simple = decoded(&constant("simple"));
    assert_eq!(
        quick_def_eq(&simple, &simple, QuickDefEqBudget::new(0, u64::MAX)),
        QuickDefEqOutcome::Inconclusive(QuickDefEqStop::Resource {
            limit: QuickDefEqLimit::Comparisons,
            allowed: 0,
            observed: 1,
            completed_comparisons: 0,
        })
    );

    let sort = decoded(&Expr::sort(Level::zero()));
    assert_eq!(
        quick_def_eq(&sort, &sort, QuickDefEqBudget::new(u64::MAX, 1)),
        QuickDefEqOutcome::Inconclusive(QuickDefEqStop::Resource {
            limit: QuickDefEqLimit::LevelArenaNodes,
            allowed: 1,
            observed: 2,
            completed_comparisons: 0,
        })
    );

    assert_eq!(
        quick_def_eq_with(&simple, &simple, QuickDefEqBudget::unlimited(), || true,),
        QuickDefEqOutcome::Inconclusive(QuickDefEqStop::Cancelled {
            polls: 1,
            completed_comparisons: 0,
        })
    );
    let expected = quick_def_eq(&simple, &simple, QuickDefEqBudget::unlimited());
    let mut polls = 0_u64;
    let interrupted = quick_def_eq_with(&simple, &simple, QuickDefEqBudget::unlimited(), || {
        polls = polls.saturating_add(1);
        polls >= 2
    });
    assert_eq!(
        interrupted,
        QuickDefEqOutcome::Inconclusive(QuickDefEqStop::Cancelled {
            polls: 2,
            completed_comparisons: 0,
        })
    );
    assert_eq!(
        quick_def_eq(&simple, &simple, QuickDefEqBudget::unlimited()),
        expected,
        "a typed non-answer cannot mutate either source or poison recovery"
    );
}

fn deep_application(depth: usize) -> Result<WireExpr, String> {
    let mut writer = CanonWriter::new();
    writer.schema(SCHEMA_EXPR);
    for _ in 0..depth {
        writer.u8(5);
    }
    writer.u8(0);
    writer.u32(0);
    for _ in 0..depth {
        writer.u8(0);
        writer.u32(1);
    }
    let bytes = writer.into_bytes();
    match decode_expr(&bytes, DecodeBudget::unlimited()) {
        DecodeOutcome::Complete(Ok(value)) => Ok(value),
        other => Err(format!("deep expression did not decode: {other:?}")),
    }
}

fn deep_child() -> Result<(), String> {
    const DEPTH: usize = 50_000;
    let left = deep_application(DEPTH)?;
    let right = deep_application(DEPTH)?;
    match quick_def_eq(&left, &right, QuickDefEqBudget::unlimited()) {
        QuickDefEqOutcome::Equal(QuickDefEqResult { comparisons })
            if comparisons == DEPTH.saturating_mul(2).saturating_add(1) as u64 =>
        {
            Ok(())
        }
        other => Err(format!("deep quick equality drifted: {other:?}")),
    }
}

#[test]
fn deep_quick_equality_fits_a_64k_stack() {
    const CHILD_ENV: &str = "FLN_CHECKER_DEFEQ_DEEP_CHILD";
    if std::env::var_os(CHILD_ENV).is_some() {
        let result = std::thread::Builder::new()
            .name("fln-checker-defeq-deep".to_owned())
            .stack_size(64 * 1024)
            .spawn(deep_child)
            .expect("spawn bounded-stack child thread")
            .join()
            .expect("bounded-stack child thread did not panic");
        result.expect("bounded-stack quick equality");
        return;
    }

    let executable = std::env::current_exe().expect("current test executable");
    let output = Command::new(executable)
        .env(CHILD_ENV, "1")
        .args([
            "--exact",
            "deep_quick_equality_fits_a_64k_stack",
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

fn deep_slow_child() -> Result<(), String> {
    const DEPTH: usize = 50_000;
    let binding_value = deep_application(DEPTH)?;
    let right = deep_application(DEPTH)?;
    let left = decoded(&Expr::fvar(FVarId(name("deep_free"))));
    let context = WhnfContext::new(
        vec![FreeBinding::new(checker_name("deep_free"), binding_value)],
        Vec::new(),
    );
    match def_eq(&left, &right, &context, DefEqBudget::unlimited()) {
        DefEqOutcome::Equal(progress)
            if progress.quick_comparisons == 1
                && progress.slow_comparisons
                    == DEPTH.saturating_mul(2).saturating_add(2) as u64
                && progress.normalizations == 2
                && progress.whnf_reductions == 1
                && progress.materialized_arena_nodes
                    == DEPTH.saturating_mul(4).saturating_add(2) as u64 =>
        {
            Ok(())
        }
        other => Err(format!("deep pure conversion drifted: {other:?}")),
    }
}

#[test]
fn deep_pure_conversion_fits_a_64k_stack() {
    const CHILD_ENV: &str = "FLN_CHECKER_SLOW_DEFEQ_DEEP_CHILD";
    if std::env::var_os(CHILD_ENV).is_some() {
        let result = std::thread::Builder::new()
            .name("fln-checker-slow-defeq-deep".to_owned())
            .stack_size(64 * 1024)
            .spawn(deep_slow_child)
            .expect("spawn bounded-stack child thread")
            .join()
            .expect("bounded-stack child thread did not panic");
        result.expect("bounded-stack pure conversion");
        return;
    }

    let executable = std::env::current_exe().expect("current test executable");
    let output = Command::new(executable)
        .env(CHILD_ENV, "1")
        .args([
            "--exact",
            "deep_pure_conversion_fits_a_64k_stack",
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
fn defeq_production_code_has_no_primary_semantic_path() {
    let source = include_str!("../src/defeq.rs");
    for forbidden in [
        "fln_core::",
        "TypeChecker",
        "Expr::is_def_eq",
        "Level::is_equiv",
        "fln_kernel",
    ] {
        assert!(
            !source.contains(forbidden),
            "checker quick-defeq source shares forbidden semantic path `{forbidden}`"
        );
    }
}
