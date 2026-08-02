#![forbid(unsafe_code)]

use std::process::Command;

use fln_checker::defeq::{
    ExpressionClass, QuickDefEqBudget, QuickDefEqDeferred, QuickDefEqLimit, QuickDefEqMismatch,
    QuickDefEqOutcome, QuickDefEqResult, QuickDefEqStop, quick_def_eq, quick_def_eq_with,
};
use fln_checker::wire::{DecodeBudget, DecodeOutcome, WireExpr, decode_expr};
use fln_core::expr::{BinderInfo, Expr, Literal, NatLit};
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

fn deep_child() -> Result<(), String> {
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
    let bytes = writer.into_bytes();
    let decode = || match decode_expr(&bytes, DecodeBudget::unlimited()) {
        DecodeOutcome::Complete(Ok(value)) => Ok(value),
        other => Err(format!("deep expression did not decode: {other:?}")),
    };
    let left = decode()?;
    let right = decode()?;
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
