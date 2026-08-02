#![forbid(unsafe_code)]

use std::process::Command;

use fln_checker::defeq::{
    DefEqBudget, DefEqLimit, DefEqMismatch, DefEqOutcome, DefEqSide, DefEqStop, ExpressionClass,
    QuickDefEqBudget, QuickDefEqDeferred, QuickDefEqLimit, QuickDefEqMismatch, QuickDefEqOutcome,
    QuickDefEqResult, QuickDefEqStop, def_eq, def_eq_with, quick_def_eq, quick_def_eq_with,
};
use fln_checker::environment::{
    Definition, DefinitionEntry, DefinitionEnvironment, DefinitionSafety, EnvironmentBudget,
    EnvironmentOutcome, ReducibilityHint,
};
use fln_checker::term::TermBudget;
use fln_checker::whnf::{
    FreeBinding, ProjectionRule, WhnfBudget, WhnfContext, WhnfLimit, WhnfRefusal, WhnfStop,
};
use fln_checker::wire::{
    DecodeBudget, DecodeOutcome, WireExpr, WireName, decode_expr, decode_name,
};
use fln_core::expr::{BinderInfo, Expr, FVarId, Literal, MVarId, NatLit};
use fln_core::level::{LMVarId, Level};
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_hash::canon::{CanonWriter, Canonical, SCHEMA_EXPR};

fn name(component: impl Into<String>) -> Name {
    Name::str(Name::anonymous(), component)
}

fn constant(component: impl Into<String>) -> Expr {
    Expr::const_(name(component), Vec::new())
}

fn qualified(namespace: &str, leaf: &str) -> Name {
    Name::str(Name::str(Name::anonymous(), namespace), leaf)
}

fn nat_zero() -> Expr {
    Expr::const_(qualified("Nat", "zero"), Vec::new())
}

fn nat_succ(value: Expr) -> Expr {
    Expr::app(Expr::const_(qualified("Nat", "succ"), Vec::new()), value)
}

fn nat_literal(value: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(value)))
}

fn nat_limbs(limbs_le: Vec<u64>) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_limbs_le(limbs_le)))
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

fn eta(function: Expr) -> Expr {
    Expr::lam(
        name("eta"),
        Expr::sort(Level::zero()),
        Expr::app(function, Expr::bvar(0).expect("eta argument")),
        BinderInfo::Default,
    )
}

fn eta_all_wire_variants() -> Expr {
    let binder = name("eta_all_variants");
    let type_ = Expr::sort(Level::param(name("eta_type_level")));
    let locals = Expr::app(
        Expr::app(
            Expr::bvar(0).expect("nested bound variable"),
            Expr::fvar(FVarId(name("eta_free"))),
        ),
        Expr::mvar(MVarId(name("eta_meta"))),
    );
    let constants = Expr::app(
        Expr::const_(
            name("EtaConstant"),
            vec![
                Level::param(name("eta_constant_level")),
                Level::mvar(LMVarId(name("eta_level_meta"))),
            ],
        ),
        Expr::lit(Literal::Nat(NatLit::from_limbs_le(vec![3, 5]))),
    );
    let body = Expr::app(
        Expr::app(constants, locals),
        Expr::lit(Literal::Str("eta-string".to_owned())),
    );
    let lambda = Expr::lam(
        binder.clone(),
        type_.clone(),
        body,
        BinderInfo::StrictImplicit,
    );
    let forall = Expr::forall_e(
        binder.clone(),
        type_.clone(),
        lambda,
        BinderInfo::InstImplicit,
    );
    let let_expression = Expr::let_e(binder.clone(), type_, nat_literal(1), forall, true);
    Expr::app(
        constant("EtaOpaqueHolder"),
        Expr::mdata(
            KVMap::new(),
            Expr::proj(name("EtaStructure"), 7, let_expression),
        ),
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

fn definition_entry(
    definition_name: impl Into<String>,
    value: WireExpr,
    hint: ReducibilityHint,
    safety: DefinitionSafety,
) -> DefinitionEntry {
    DefinitionEntry::new(
        checker_name(definition_name),
        Definition::new(
            Vec::new(),
            decoded(&Expr::sort(Level::zero())),
            value,
            hint,
            safety,
            Vec::new(),
        ),
    )
}

fn definition_context(entries: Vec<DefinitionEntry>) -> WhnfContext {
    let environment = match DefinitionEnvironment::build(entries, EnvironmentBudget::unlimited()) {
        EnvironmentOutcome::Complete { environment, .. } => environment,
        other => panic!("definition environment did not build: {other:?}"),
    };
    WhnfContext::new(Vec::new(), Vec::new(), environment)
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
    assert_eq!(progress.slow_comparisons, 9);
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
        DefinitionEnvironment::empty(),
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
        DefinitionEnvironment::empty(),
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
                        DefinitionEnvironment::empty(),
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
                    DefinitionEnvironment::empty(),
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
fn eager_safe_definition_delta_is_visible_to_slow_conversion() {
    let type_ = decoded(&Expr::sort(Level::zero()));
    let entries = vec![
        DefinitionEntry::new(
            checker_name("safe_alias"),
            Definition::new(
                Vec::new(),
                type_.clone(),
                decoded(&constant("target")),
                ReducibilityHint::Opaque,
                DefinitionSafety::Safe,
                Vec::new(),
            ),
        ),
        DefinitionEntry::new(
            checker_name("unsafe_alias"),
            Definition::new(
                Vec::new(),
                type_,
                decoded(&constant("target")),
                ReducibilityHint::Abbrev,
                DefinitionSafety::Unsafe,
                Vec::new(),
            ),
        ),
    ];
    let environment = match DefinitionEnvironment::build(entries, EnvironmentBudget::unlimited()) {
        EnvironmentOutcome::Complete { environment, .. } => environment,
        other => panic!("definition environment did not build: {other:?}"),
    };
    let context = WhnfContext::new(Vec::new(), Vec::new(), environment);

    let progress = slow_equal(
        &decoded(&constant("safe_alias")),
        &decoded(&constant("target")),
        &context,
    );
    assert_eq!(progress.whnf_reductions, 1);
    assert!(progress.normalizations >= 1);

    assert!(matches!(
        def_eq(
            &decoded(&constant("unsafe_alias")),
            &decoded(&constant("target")),
            &context,
            DefEqBudget::unlimited(),
        ),
        DefEqOutcome::Deferred {
            need: fln_checker::defeq::DefEqDeferred {
                left_class: ExpressionClass::Constant,
                right_class: ExpressionClass::Constant,
                ..
            },
            progress: fln_checker::defeq::DefEqProgress {
                whnf_reductions: 0,
                ..
            },
        }
    ));
}

#[test]
fn lazy_delta_orders_by_height_and_unfolds_both_sides_only_on_a_tie() {
    let context = definition_context(vec![
        definition_entry(
            "short",
            decoded(&constant("terminal")),
            ReducibilityHint::Regular(1),
            DefinitionSafety::Safe,
        ),
        definition_entry(
            "tall",
            decoded(&constant("short")),
            ReducibilityHint::Regular(10),
            DefinitionSafety::Safe,
        ),
        definition_entry(
            "equal_left",
            decoded(&constant("terminal")),
            ReducibilityHint::Regular(4),
            DefinitionSafety::Safe,
        ),
        definition_entry(
            "equal_right",
            decoded(&constant("terminal")),
            ReducibilityHint::Regular(4),
            DefinitionSafety::Safe,
        ),
        definition_entry(
            "opaque",
            decoded(&constant("terminal")),
            ReducibilityHint::Opaque,
            DefinitionSafety::Safe,
        ),
        definition_entry(
            "regular_to_opaque",
            decoded(&constant("opaque")),
            ReducibilityHint::Regular(9),
            DefinitionSafety::Safe,
        ),
        definition_entry(
            "abbrev_to_short",
            decoded(&constant("short")),
            ReducibilityHint::Abbrev,
            DefinitionSafety::Safe,
        ),
    ]);

    for (left, right) in [
        ("tall", "short"),
        ("regular_to_opaque", "opaque"),
        ("abbrev_to_short", "short"),
    ] {
        let progress = slow_equal(
            &decoded(&constant(left)),
            &decoded(&constant(right)),
            &context,
        );
        assert_eq!(
            progress.delta_unfolds, 1,
            "the greater-height side must close {left} against {right} in one delta step"
        );
    }

    let tied = slow_equal(
        &decoded(&constant("equal_left")),
        &decoded(&constant("equal_right")),
        &context,
    );
    assert_eq!(
        tied.delta_unfolds, 2,
        "equal heights must unfold both safe definition heads"
    );
}

#[test]
fn generated_height_permutations_close_by_unfolding_only_the_taller_alias() {
    const CASES: usize = 320;
    let mut entries = Vec::new();
    for index in 0..CASES {
        let lower = format!("generated_lower_{index}");
        let higher = format!("generated_higher_{index}");
        let terminal = format!("generated_terminal_{index}");
        let lower_height = (index % 23) as u32;
        entries.push(definition_entry(
            lower.clone(),
            decoded(&constant(terminal)),
            ReducibilityHint::Regular(lower_height),
            DefinitionSafety::Safe,
        ));
        entries.push(definition_entry(
            higher,
            decoded(&constant(lower)),
            if index % 7 == 0 {
                ReducibilityHint::Abbrev
            } else {
                ReducibilityHint::Regular(lower_height.saturating_add(1))
            },
            DefinitionSafety::Safe,
        ));
    }
    let context = definition_context(entries);
    for index in 0..CASES {
        let progress = slow_equal(
            &decoded(&constant(format!("generated_higher_{index}"))),
            &decoded(&constant(format!("generated_lower_{index}"))),
            &context,
        );
        assert_eq!(
            progress.delta_unfolds, 1,
            "generated height ordering drifted at case {index}"
        );
    }
}

#[test]
fn lazy_delta_finds_safe_definition_heads_under_application_spines() {
    let context = definition_context(vec![definition_entry(
        "apply_identity",
        decoded(&identity()),
        ReducibilityHint::Opaque,
        DefinitionSafety::Safe,
    )]);
    let payload = decoded(&constant("application_payload"));
    let application = decoded(&Expr::app(
        constant("apply_identity"),
        constant("application_payload"),
    ));
    let progress = slow_equal(&application, &payload, &context);
    assert_eq!(progress.delta_unfolds, 1);
    assert!(
        progress.whnf_reductions >= 2,
        "one delta step must continue through the exposed beta redex"
    );
}

#[test]
fn lazy_delta_resources_cancellation_and_recursion_are_typed_and_recoverable() {
    let context = definition_context(vec![
        definition_entry(
            "loop",
            decoded(&constant("loop")),
            ReducibilityHint::Regular(5),
            DefinitionSafety::Safe,
        ),
        definition_entry(
            "short",
            decoded(&constant("terminal")),
            ReducibilityHint::Regular(1),
            DefinitionSafety::Safe,
        ),
        definition_entry(
            "tall",
            decoded(&constant("short")),
            ReducibilityHint::Regular(10),
            DefinitionSafety::Safe,
        ),
    ]);
    let loop_term = decoded(&constant("loop"));
    let terminal = decoded(&constant("terminal"));
    assert!(matches!(
        def_eq(
            &loop_term,
            &terminal,
            &context,
            DefEqBudget::new(
                QuickDefEqBudget::unlimited(),
                u64::MAX,
                8,
                u64::MAX,
                u64::MAX,
                WhnfBudget::unlimited(),
            ),
        ),
        DefEqOutcome::Inconclusive(DefEqStop::Resource {
            limit: DefEqLimit::Normalizations,
            allowed: 8,
            observed: 9,
            progress: fln_checker::defeq::DefEqProgress {
                delta_unfolds: 2,
                ..
            },
        })
    ));

    let tall = decoded(&constant("tall"));
    let short = decoded(&constant("short"));
    let mut saw_delta_cancellation = false;
    for cancel_at in 1_u64..=128 {
        let mut polls = 0_u64;
        let interrupted = def_eq_with(&tall, &short, &context, DefEqBudget::unlimited(), || {
            polls = polls.saturating_add(1);
            polls >= cancel_at
        });
        if matches!(
            interrupted,
            DefEqOutcome::Inconclusive(DefEqStop::Whnf {
                stop: WhnfStop::DefinitionInstantiation {
                    stop: fln_checker::term::TermStop::Cancelled { .. },
                    ..
                },
                ..
            })
        ) {
            saw_delta_cancellation = true;
            break;
        }
    }
    assert!(
        saw_delta_cancellation,
        "cancellation must be observable inside a selected lazy-delta step"
    );

    let recovered = slow_equal(&tall, &short, &context);
    assert_eq!(recovered.delta_unfolds, 1);
}

#[test]
fn exact_function_eta_is_symmetric_and_shifts_outer_bounds() {
    let function = decoded(&constant("eta_function"));
    let contracted = decoded(&eta(constant("eta_function")));
    let left_progress = slow_equal(&contracted, &function, &WhnfContext::default());
    let right_progress = slow_equal(&function, &contracted, &WhnfContext::default());
    assert_eq!(left_progress, right_progress);
    assert!(left_progress.slow_comparisons > 0);
    assert_eq!(left_progress.delta_unfolds, 0);

    let shifted = decoded(&Expr::lam(
        name("shifted"),
        Expr::sort(Level::zero()),
        Expr::app(
            Expr::bvar(1).expect("outer variable under eta binder"),
            Expr::bvar(0).expect("eta argument"),
        ),
        BinderInfo::Default,
    ));
    let outside = decoded(&Expr::bvar(0).expect("outer variable"));
    assert!(matches!(
        def_eq(
            &shifted,
            &outside,
            &WhnfContext::default(),
            DefEqBudget::unlimited(),
        ),
        DefEqOutcome::Equal(_)
    ));
}

#[test]
fn eta_virtual_binder_tracks_nested_scope_names_styles_and_universes() {
    let universe = parameter("eta_u");
    let equivalent = Level::max(universe.clone(), Level::zero()).expect("shallow equivalent level");
    let inside_nested = Expr::lam(
        name("inside_name"),
        Expr::sort(universe.clone()),
        Expr::app(
            Expr::bvar(0).expect("nested local"),
            Expr::bvar(2).expect("outer variable beyond eta binder"),
        ),
        BinderInfo::Default,
    );
    let outside_nested = Expr::lam(
        name("outside_name"),
        Expr::sort(equivalent.clone()),
        Expr::app(
            Expr::bvar(0).expect("nested local"),
            Expr::bvar(1).expect("outer variable"),
        ),
        BinderInfo::Implicit,
    );
    let inside_function = Expr::app(Expr::const_(name("EtaWrap"), vec![universe]), inside_nested);
    let outside_function = Expr::app(
        Expr::const_(name("EtaWrap"), vec![equivalent]),
        outside_nested,
    );
    let progress = slow_equal(
        &decoded(&eta(inside_function)),
        &decoded(&outside_function),
        &WhnfContext::default(),
    );
    assert!(progress.slow_comparisons > 10);

    let dependent_function = Expr::app(
        constant("EtaWrap"),
        Expr::lam(
            name("nested"),
            Expr::sort(Level::zero()),
            Expr::bvar(1).expect("consumed eta binder"),
            BinderInfo::Default,
        ),
    );
    let independent_function = Expr::app(
        constant("EtaWrap"),
        Expr::lam(
            name("nested"),
            Expr::sort(Level::zero()),
            Expr::bvar(0).expect("nested local"),
            BinderInfo::Default,
        ),
    );
    assert!(matches!(
        def_eq(
            &decoded(&eta(dependent_function)),
            &decoded(&independent_function),
            &WhnfContext::default(),
            DefEqBudget::unlimited(),
        ),
        DefEqOutcome::Deferred {
            need: fln_checker::defeq::DefEqDeferred {
                left_class: ExpressionClass::Lambda,
                right_class: ExpressionClass::Apply,
                ..
            },
            ..
        }
    ));
}

#[test]
fn eta_virtual_binder_covers_every_checker_wire_constructor() {
    let function = eta_all_wire_variants();
    let progress = slow_equal(
        &decoded(&eta(function.clone())),
        &decoded(&function),
        &WhnfContext::default(),
    );
    assert!(progress.slow_comparisons > 20);
    assert_eq!(progress.delta_unfolds, 0);
}

#[test]
fn eta_gate_misses_and_structural_mismatches_remain_deferred() {
    let function = constant("eta_gate_function");
    let cases = [
        (
            Expr::lam(
                name("wrong_body"),
                Expr::sort(Level::zero()),
                function.clone(),
                BinderInfo::Default,
            ),
            function.clone(),
        ),
        (
            Expr::lam(
                name("wrong_argument"),
                Expr::sort(Level::zero()),
                Expr::app(function.clone(), Expr::bvar(1).expect("non-eta argument")),
                BinderInfo::Default,
            ),
            function.clone(),
        ),
        (
            Expr::lam(
                name("metadata_argument"),
                Expr::sort(Level::zero()),
                Expr::app(
                    function.clone(),
                    Expr::mdata(
                        KVMap::new(),
                        Expr::bvar(0).expect("metadata-wrapped eta argument"),
                    ),
                ),
                BinderInfo::Default,
            ),
            function.clone(),
        ),
        (eta(function), constant("different_function")),
    ];

    for (index, (left, right)) in cases.into_iter().enumerate() {
        assert!(
            matches!(
                def_eq(
                    &decoded(&left),
                    &decoded(&right),
                    &WhnfContext::default(),
                    DefEqBudget::unlimited(),
                ),
                DefEqOutcome::Deferred { .. }
            ),
            "eta gate miss {index} became decisive"
        );
    }
}

#[test]
fn eta_comparison_limits_cancellation_and_recovery_are_exact() {
    let mut function = constant("eta_budget_head");
    for index in 0..64 {
        function = Expr::app(function, constant(format!("eta_budget_{index}")));
    }
    let contracted = decoded(&eta(function.clone()));
    let outside = decoded(&function);
    let full = slow_equal(&contracted, &outside, &WhnfContext::default());

    let wrong_argument = decoded(&Expr::lam(
        name("wrong_argument"),
        Expr::sort(Level::zero()),
        Expr::app(
            function,
            Expr::bvar(1).expect("non-eta argument for comparison floor"),
        ),
        BinderInfo::Default,
    ));
    let prefix = match def_eq(
        &wrong_argument,
        &outside,
        &WhnfContext::default(),
        DefEqBudget::unlimited(),
    ) {
        DefEqOutcome::Deferred { progress, .. } => progress,
        other => panic!("wrong eta argument did not defer: {other:?}"),
    };
    assert!(full.slow_comparisons > prefix.slow_comparisons);

    let budget = |max_slow_comparisons| {
        DefEqBudget::new(
            QuickDefEqBudget::unlimited(),
            max_slow_comparisons,
            u64::MAX,
            u64::MAX,
            u64::MAX,
            WhnfBudget::unlimited(),
        )
    };
    let allowed = full.slow_comparisons - 1;
    assert!(matches!(
        def_eq(
            &contracted,
            &outside,
            &WhnfContext::default(),
            budget(allowed),
        ),
        DefEqOutcome::Inconclusive(DefEqStop::Resource {
            limit: DefEqLimit::SlowComparisons,
            allowed: actual_allowed,
            observed,
            progress,
        }) if actual_allowed == allowed
            && observed == allowed + 1
            && progress.slow_comparisons == allowed
    ));
    assert_eq!(
        match def_eq(
            &contracted,
            &outside,
            &WhnfContext::default(),
            budget(full.slow_comparisons),
        ) {
            DefEqOutcome::Equal(progress) => progress,
            other => panic!("exact eta comparison budget did not pass: {other:?}"),
        },
        full
    );

    let mut saw_eta_cancellation = false;
    for cancel_at in 1_u64..=4_096 {
        let mut polls = 0_u64;
        let interrupted = def_eq_with(
            &contracted,
            &outside,
            &WhnfContext::default(),
            DefEqBudget::unlimited(),
            || {
                polls = polls.saturating_add(1);
                polls >= cancel_at
            },
        );
        if matches!(
            interrupted,
            DefEqOutcome::Inconclusive(DefEqStop::Cancelled { progress, .. })
                if progress.slow_comparisons > prefix.slow_comparisons
                    && progress.slow_comparisons < full.slow_comparisons
        ) {
            saw_eta_cancellation = true;
            break;
        }
    }
    assert!(
        saw_eta_cancellation,
        "cancellation never reached the virtual-binder comparison"
    );
    assert_eq!(
        slow_equal(&contracted, &outside, &WhnfContext::default()),
        full
    );
}

#[test]
fn eta_virtual_bound_index_has_an_exact_intrinsic_boundary() {
    const MAX_INDEX: u32 = (1 << 20) - 2;
    let contracted = decoded(&eta(
        Expr::bvar(MAX_INDEX).expect("last checker-owned bound index")
    ));
    let exact_outside =
        decoded(&Expr::bvar(MAX_INDEX - 1).expect("last shiftable checker-owned bound index"));
    assert!(matches!(
        def_eq(
            &contracted,
            &exact_outside,
            &WhnfContext::default(),
            DefEqBudget::unlimited(),
        ),
        DefEqOutcome::Equal(_)
    ));

    let overflowing_outside =
        decoded(&Expr::bvar(MAX_INDEX).expect("last checker-owned bound index"));
    assert!(matches!(
        def_eq(
            &contracted,
            &overflowing_outside,
            &WhnfContext::default(),
            DefEqBudget::unlimited(),
        ),
        DefEqOutcome::Inconclusive(DefEqStop::Resource {
            limit: DefEqLimit::BoundIndex,
            allowed,
            observed,
            ..
        }) if allowed == u64::from(MAX_INDEX) && observed == allowed + 1
    ));
}

#[test]
fn nat_offsets_close_zero_successors_and_a_terminal_mismatch_exactly() {
    let context = WhnfContext::default();
    let zero = decoded(&nat_zero());
    let literal_zero = decoded(&nat_literal(0));
    let zero_progress = slow_equal(&zero, &literal_zero, &context);
    assert_eq!(zero_progress.nat_offset_steps, 0);
    assert_eq!(zero_progress.materialized_arena_nodes, 0);

    for (left, right) in [
        (nat_literal(1), nat_succ(nat_zero())),
        (nat_succ(nat_zero()), nat_literal(1)),
        (nat_succ(nat_literal(4)), nat_literal(5)),
        (nat_literal(5), nat_succ(nat_literal(4))),
    ] {
        let progress = slow_equal(&decoded(&left), &decoded(&right), &context);
        assert_eq!(progress.nat_offset_steps, 1);
        assert_eq!(progress.materialized_arena_nodes, 1);
    }

    assert!(matches!(
        def_eq(
            &decoded(&nat_literal(2)),
            &decoded(&nat_succ(nat_zero())),
            &context,
            DefEqBudget::unlimited(),
        ),
        DefEqOutcome::NotEqual {
            mismatch: DefEqMismatch::NatOffsets { .. },
            progress: fln_checker::defeq::DefEqProgress {
                nat_offset_steps: 1,
                ..
            },
        }
    ));
    assert!(matches!(
        def_eq(
            &decoded(&nat_zero()),
            &decoded(&nat_succ(constant("arbitrary_predecessor"))),
            &context,
            DefEqBudget::unlimited(),
        ),
        DefEqOutcome::Deferred { .. }
    ));
}

#[test]
fn generated_nat_offset_orientations_match_their_direct_predecessors() {
    const CASES: usize = 320;
    for index in 0..CASES {
        let predecessor = (index as u64).saturating_mul(1_000_003).saturating_add(17);
        let literal = nat_literal(predecessor.saturating_add(1));
        let successor = nat_succ(nat_literal(predecessor));
        let (left, right) = if index % 2 == 0 {
            (literal, successor)
        } else {
            (successor, literal)
        };
        let progress = slow_equal(&decoded(&left), &decoded(&right), &WhnfContext::default());
        assert_eq!(
            progress.nat_offset_steps, 1,
            "generated offset orientation drifted at case {index}"
        );
    }
}

#[test]
fn nat_offset_large_limbs_are_direct_and_shape_guards_do_not_fire() {
    let huge = nat_limbs(vec![0, 1]);
    let huge_predecessor = nat_limbs(vec![u64::MAX]);
    let progress = slow_equal(
        &decoded(&huge),
        &decoded(&nat_succ(huge_predecessor)),
        &WhnfContext::default(),
    );
    assert_eq!(progress.nat_offset_steps, 1);
    assert_eq!(progress.nat_offset_limb_steps, 3);
    assert_eq!(progress.materialized_arena_nodes, 1);
    assert_eq!(progress.materialized_owned_units, 2);

    let zero_with_level = Expr::const_(qualified("Nat", "zero"), vec![Level::zero()]);
    let succ_with_level = Expr::app(
        Expr::const_(qualified("Nat", "succ"), vec![Level::zero()]),
        nat_zero(),
    );
    let over_applied = Expr::app(nat_succ(nat_zero()), constant("extra"));
    for guarded in [
        zero_with_level,
        succ_with_level,
        over_applied,
        constant("Nat.zero"),
    ] {
        assert!(matches!(
            def_eq(
                &decoded(&guarded),
                &decoded(&nat_literal(0)),
                &WhnfContext::default(),
                DefEqBudget::unlimited(),
            ),
            DefEqOutcome::Deferred { .. }
        ));
    }
}

#[test]
fn delta_exposed_nat_offsets_rerun_before_the_next_definition_step() {
    let context = definition_context(vec![
        definition_entry(
            "two",
            decoded(&nat_literal(2)),
            ReducibilityHint::Regular(8),
            DefinitionSafety::Safe,
        ),
        definition_entry(
            "zero_alias",
            decoded(&nat_literal(0)),
            ReducibilityHint::Abbrev,
            DefinitionSafety::Safe,
        ),
    ]);

    let two = slow_equal(
        &decoded(&constant("two")),
        &decoded(&nat_succ(nat_succ(nat_zero()))),
        &context,
    );
    assert_eq!(two.delta_unfolds, 1);
    assert_eq!(two.nat_offset_steps, 2);

    let zero = slow_equal(
        &decoded(&constant("zero_alias")),
        &decoded(&nat_zero()),
        &context,
    );
    assert_eq!(zero.delta_unfolds, 1);
    assert_eq!(zero.nat_offset_steps, 0);
}

#[test]
fn nat_offset_materialization_resources_cancellation_and_recovery_are_exact() {
    const LIMBS: usize = 64;
    let mut value_limbs = vec![0; LIMBS];
    value_limbs[LIMBS - 1] = 1;
    let predecessor_limbs = vec![u64::MAX; LIMBS - 1];
    let value = decoded(&nat_limbs(value_limbs));
    let successor = decoded(&nat_succ(nat_limbs(predecessor_limbs)));

    let budget = |nodes, owned| {
        DefEqBudget::new(
            QuickDefEqBudget::unlimited(),
            u64::MAX,
            u64::MAX,
            nodes,
            owned,
            WhnfBudget::unlimited(),
        )
    };
    assert!(matches!(
        def_eq(
            &value,
            &successor,
            &WhnfContext::default(),
            budget(0, u64::MAX),
        ),
        DefEqOutcome::Inconclusive(DefEqStop::Resource {
            limit: DefEqLimit::MaterializedArenaNodes,
            allowed: 0,
            observed: 1,
            progress: fln_checker::defeq::DefEqProgress {
                materialized_arena_nodes: 0,
                materialized_owned_units: 0,
                ..
            },
        })
    ));
    assert!(matches!(
        def_eq(
            &value,
            &successor,
            &WhnfContext::default(),
            budget(u64::MAX, LIMBS as u64 - 1),
        ),
        DefEqOutcome::Inconclusive(DefEqStop::Resource {
            limit: DefEqLimit::MaterializedOwnedUnits,
            allowed,
            observed,
            progress: fln_checker::defeq::DefEqProgress {
                materialized_arena_nodes: 0,
                materialized_owned_units: 0,
                ..
            },
        }) if allowed == LIMBS as u64 - 1 && observed == LIMBS as u64
    ));

    let exact = match def_eq(
        &value,
        &successor,
        &WhnfContext::default(),
        budget(1, LIMBS as u64),
    ) {
        DefEqOutcome::Equal(progress) => progress,
        other => panic!("exact Nat offset materialization budget did not pass: {other:?}"),
    };
    assert_eq!(exact.materialized_arena_nodes, 1);
    assert_eq!(exact.materialized_owned_units, LIMBS as u64);

    let mut saw_copy_cancellation = false;
    for cancel_at in 1_u64..=512 {
        let mut polls = 0_u64;
        let interrupted = def_eq_with(
            &value,
            &successor,
            &WhnfContext::default(),
            DefEqBudget::unlimited(),
            || {
                polls = polls.saturating_add(1);
                polls >= cancel_at
            },
        );
        if matches!(
            interrupted,
            DefEqOutcome::Inconclusive(DefEqStop::Cancelled {
                progress: fln_checker::defeq::DefEqProgress {
                    nat_offset_limb_steps,
                    materialized_arena_nodes: 0,
                    materialized_owned_units: 0,
                    ..
                },
                ..
            }) if nat_offset_limb_steps > LIMBS as u64
        ) {
            saw_copy_cancellation = true;
            break;
        }
    }
    assert!(
        saw_copy_cancellation,
        "cancellation must be observable after predecessor copying begins"
    );
    let recovered = slow_equal(&value, &successor, &WhnfContext::default());
    assert_eq!(recovered.materialized_arena_nodes, 1);
    assert_eq!(recovered.materialized_owned_units, LIMBS as u64);
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
        DefinitionEnvironment::empty(),
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

fn write_sort_zero(writer: &mut CanonWriter) {
    writer.u8(3);
    writer.u8(0);
}

fn write_anonymous_lambda_prefix(writer: &mut CanonWriter) {
    writer.u8(6);
    writer.u64(0);
    write_sort_zero(writer);
}

fn write_simple_constant(writer: &mut CanonWriter, component: &str) {
    writer.u8(4);
    writer.u64(1);
    writer.u8(1);
    writer.str(component);
    writer.u64(0);
}

fn write_deep_eta_function(writer: &mut CanonWriter, depth: usize) {
    writer.u8(5);
    write_simple_constant(writer, "DeepEtaWrap");
    for _ in 0..depth {
        write_anonymous_lambda_prefix(writer);
    }
    writer.u8(0);
    writer.u32(0);
    for _ in 0..depth {
        writer.u8(0);
    }
}

fn deep_eta_terms(depth: usize) -> Result<(WireExpr, WireExpr), String> {
    let mut contracted = CanonWriter::new();
    contracted.schema(SCHEMA_EXPR);
    write_anonymous_lambda_prefix(&mut contracted);
    contracted.u8(5);
    write_deep_eta_function(&mut contracted, depth);
    contracted.u8(0);
    contracted.u32(0);
    contracted.u8(0);

    let mut outside = CanonWriter::new();
    outside.schema(SCHEMA_EXPR);
    write_deep_eta_function(&mut outside, depth);

    let decode = |bytes: Vec<u8>| match decode_expr(&bytes, DecodeBudget::unlimited()) {
        DecodeOutcome::Complete(Ok(value)) => Ok(value),
        other => Err(format!("deep eta expression did not decode: {other:?}")),
    };
    Ok((
        decode(contracted.into_bytes())?,
        decode(outside.into_bytes())?,
    ))
}

fn deep_eta_child() -> Result<(), String> {
    const DEPTH: usize = 50_000;
    let (contracted, outside) = deep_eta_terms(DEPTH)?;
    match def_eq(
        &contracted,
        &outside,
        &WhnfContext::default(),
        DefEqBudget::unlimited(),
    ) {
        DefEqOutcome::Equal(progress)
            if progress.quick_comparisons == 1
                && progress.slow_comparisons >= DEPTH.saturating_mul(2) as u64
                && progress.delta_unfolds == 0 =>
        {
            Ok(())
        }
        other => Err(format!("deep eta conversion drifted: {other:?}")),
    }
}

#[test]
fn deep_exact_function_eta_fits_a_64k_stack() {
    const CHILD_ENV: &str = "FLN_CHECKER_EXACT_ETA_DEEP_CHILD";
    if std::env::var_os(CHILD_ENV).is_some() {
        let result = std::thread::Builder::new()
            .name("fln-checker-exact-eta-deep".to_owned())
            .stack_size(64 * 1024)
            .spawn(deep_eta_child)
            .expect("spawn bounded-stack eta child thread")
            .join()
            .expect("bounded-stack eta child thread did not panic");
        result.expect("bounded-stack exact eta conversion");
        return;
    }

    let executable = std::env::current_exe().expect("current test executable");
    let output = Command::new(executable)
        .env(CHILD_ENV, "1")
        .args([
            "--exact",
            "deep_exact_function_eta_fits_a_64k_stack",
            "--nocapture",
        ])
        .output()
        .expect("run bounded-stack eta child process");
    assert!(
        output.status.success(),
        "bounded-stack eta child failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
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
        DefinitionEnvironment::empty(),
    );
    match def_eq(&left, &right, &context, DefEqBudget::unlimited()) {
        DefEqOutcome::Equal(progress)
            if progress.quick_comparisons == 1
                && progress.slow_comparisons
                    == DEPTH.saturating_mul(2).saturating_add(4) as u64
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

fn deep_lazy_delta_child() -> Result<(), String> {
    const DEPTH: usize = 50_000;
    let names: Vec<_> = (0..=DEPTH)
        .map(|index| format!("deep_lazy_definition_{index}"))
        .collect();
    let type_ = decoded(&Expr::sort(Level::zero()));
    let entries = (0..DEPTH)
        .map(|index| {
            DefinitionEntry::new(
                checker_name(names[index].clone()),
                Definition::new(
                    Vec::new(),
                    type_.clone(),
                    decoded(&constant(names[index + 1].clone())),
                    ReducibilityHint::Regular(
                        u32::try_from(DEPTH - index).expect("depth fits u32"),
                    ),
                    DefinitionSafety::Safe,
                    Vec::new(),
                ),
            )
        })
        .collect();
    let context = definition_context(entries);
    let left = decoded(&constant(names[0].clone()));
    let right = decoded(&constant(names[DEPTH].clone()));
    match def_eq(&left, &right, &context, DefEqBudget::unlimited()) {
        DefEqOutcome::Equal(progress)
            if progress.quick_comparisons == 1
                && progress.slow_comparisons
                    == DEPTH.saturating_mul(5).saturating_add(1) as u64
                && progress.normalizations == DEPTH.saturating_mul(3) as u64
                && progress.whnf_reductions == DEPTH as u64
                && progress.delta_unfolds == DEPTH as u64
                && progress.materialized_arena_nodes == DEPTH.saturating_mul(3) as u64 =>
        {
            Ok(())
        }
        other => Err(format!("deep lazy-delta conversion drifted: {other:?}")),
    }
}

#[test]
fn deep_lazy_delta_conversion_fits_a_64k_stack() {
    const CHILD_ENV: &str = "FLN_CHECKER_LAZY_DELTA_DEEP_CHILD";
    if std::env::var_os(CHILD_ENV).is_some() {
        let result = std::thread::Builder::new()
            .name("fln-checker-lazy-delta-deep".to_owned())
            .stack_size(64 * 1024)
            .spawn(deep_lazy_delta_child)
            .expect("spawn bounded-stack lazy-delta child thread")
            .join()
            .expect("bounded-stack lazy-delta child thread did not panic");
        result.expect("bounded-stack lazy-delta conversion");
        return;
    }

    let executable = std::env::current_exe().expect("current test executable");
    let output = Command::new(executable)
        .env(CHILD_ENV, "1")
        .args([
            "--exact",
            "deep_lazy_delta_conversion_fits_a_64k_stack",
            "--nocapture",
        ])
        .output()
        .expect("run bounded-stack lazy-delta child process");
    assert!(
        output.status.success(),
        "bounded-stack lazy-delta child failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn write_nat_constant(writer: &mut CanonWriter, leaf: &str) {
    writer.u8(4);
    writer.u64(2);
    writer.u8(1);
    writer.str("Nat");
    writer.u8(1);
    writer.str(leaf);
    writer.u64(0);
}

fn deep_nat_successors(depth: usize) -> Result<WireExpr, String> {
    let mut writer = CanonWriter::new();
    writer.schema(SCHEMA_EXPR);
    for _ in 0..depth {
        writer.u8(5);
        write_nat_constant(&mut writer, "succ");
    }
    write_nat_constant(&mut writer, "zero");
    match decode_expr(&writer.into_bytes(), DecodeBudget::unlimited()) {
        DecodeOutcome::Complete(Ok(value)) => Ok(value),
        other => Err(format!(
            "deep Nat successor expression did not decode: {other:?}"
        )),
    }
}

fn deep_nat_offset_child() -> Result<(), String> {
    const DEPTH: usize = 50_000;
    let left = deep_nat_successors(DEPTH)?;
    let right = decoded(&nat_literal(DEPTH as u64));
    match def_eq(
        &left,
        &right,
        &WhnfContext::default(),
        DefEqBudget::unlimited(),
    ) {
        DefEqOutcome::Equal(progress)
            if progress.quick_comparisons == 1
                && progress.slow_comparisons
                    == DEPTH.saturating_mul(5).saturating_add(2) as u64
                && progress.normalizations == 0
                && progress.whnf_steps == 0
                && progress.whnf_reductions == 0
                && progress.delta_unfolds == 0
                && progress.nat_offset_steps == DEPTH as u64
                && progress.nat_offset_limb_steps
                    == DEPTH.saturating_mul(2).saturating_sub(1) as u64
                && progress.materialized_arena_nodes == DEPTH as u64
                && progress.materialized_owned_units
                    == DEPTH.saturating_mul(2).saturating_sub(1) as u64 =>
        {
            Ok(())
        }
        other => Err(format!("deep Nat offset conversion drifted: {other:?}")),
    }
}

#[test]
fn deep_nat_offset_conversion_fits_a_64k_stack() {
    const CHILD_ENV: &str = "FLN_CHECKER_NAT_OFFSET_DEEP_CHILD";
    if std::env::var_os(CHILD_ENV).is_some() {
        let result = std::thread::Builder::new()
            .name("fln-checker-nat-offset-deep".to_owned())
            .stack_size(64 * 1024)
            .spawn(deep_nat_offset_child)
            .expect("spawn bounded-stack Nat offset child thread")
            .join()
            .expect("bounded-stack Nat offset child thread did not panic");
        result.expect("bounded-stack Nat offset conversion");
        return;
    }

    let executable = std::env::current_exe().expect("current test executable");
    let output = Command::new(executable)
        .env(CHILD_ENV, "1")
        .args([
            "--exact",
            "deep_nat_offset_conversion_fits_a_64k_stack",
            "--nocapture",
        ])
        .output()
        .expect("run bounded-stack Nat offset child process");
    assert!(
        output.status.success(),
        "bounded-stack Nat offset child failed\nstdout:\n{}\nstderr:\n{}",
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
