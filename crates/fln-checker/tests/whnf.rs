#![forbid(unsafe_code)]

use std::process::Command;

use fln_checker::environment::{
    ConstantDeclaration, ConstantEntry, ConstantEnvironment, ConstantKind, ConstantSafety,
    DefinitionBody, DefinitionSafety, EnvironmentBudget, EnvironmentOutcome, ReducibilityHint,
};
use fln_checker::instantiate::InstantiationRefusal;
use fln_checker::term::{TermBudget, TermLimit, TermStop};
use fln_checker::whnf::{
    FreeBinding, ProjectionRule, WhnfBudget, WhnfContext, WhnfLimit, WhnfOutcome, WhnfPhase,
    WhnfRefusal, WhnfResult, WhnfStop, whnf, whnf_with,
};
use fln_checker::wire::{
    DecodeBudget, DecodeOutcome, ExprId, ExprNode, LevelNode, NamePart, WireExpr, WireName,
    decode_expr, decode_name,
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
        ConstantEnvironment::empty(),
    )
}

fn definition_entry_with_constant_safety(
    name: impl Into<String>,
    level_parameters: Vec<WireName>,
    value: WireExpr,
    hint: ReducibilityHint,
    constant_safety: ConstantSafety,
    safety: DefinitionSafety,
) -> ConstantEntry {
    ConstantEntry::new(
        checker_name(name),
        ConstantDeclaration::definition(
            level_parameters,
            decoded(&Expr::sort(Level::zero())),
            constant_safety,
            DefinitionBody::new(value, hint, safety, Vec::new()),
        ),
    )
}

fn definition_entry(
    name: impl Into<String>,
    level_parameters: Vec<WireName>,
    value: WireExpr,
    hint: ReducibilityHint,
    safety: DefinitionSafety,
) -> ConstantEntry {
    definition_entry_with_constant_safety(
        name,
        level_parameters,
        value,
        hint,
        if safety == DefinitionSafety::Unsafe {
            ConstantSafety::Unsafe
        } else {
            ConstantSafety::Safe
        },
        safety,
    )
}

fn header_entry(
    name: impl Into<String>,
    kind: ConstantKind,
    safety: ConstantSafety,
) -> ConstantEntry {
    ConstantEntry::new(
        checker_name(name),
        ConstantDeclaration::header(
            Vec::new(),
            decoded(&Expr::sort(Level::zero())),
            kind,
            safety,
        ),
    )
}

fn constant_environment(entries: Vec<ConstantEntry>) -> ConstantEnvironment {
    match ConstantEnvironment::build(entries, EnvironmentBudget::unlimited()) {
        EnvironmentOutcome::Complete { environment, .. } => environment,
        other => panic!("test constant environment did not build: {other:?}"),
    }
}

fn definition_context(entries: Vec<ConstantEntry>) -> WhnfContext {
    WhnfContext::new(Vec::new(), Vec::new(), constant_environment(entries))
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
        ConstantEnvironment::empty(),
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
        ConstantEnvironment::empty(),
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
fn only_safe_definition_bodies_unfold_while_every_header_only_kind_stays_stuck() {
    let context = definition_context(vec![
        definition_entry(
            "safe_opaque",
            Vec::new(),
            decoded(&constant("opaque_target")),
            ReducibilityHint::Opaque,
            DefinitionSafety::Safe,
        ),
        definition_entry(
            "safe_abbrev",
            Vec::new(),
            decoded(&constant("abbrev_target")),
            ReducibilityHint::Abbrev,
            DefinitionSafety::Safe,
        ),
        definition_entry(
            "safe_regular",
            Vec::new(),
            decoded(&constant("regular_target")),
            ReducibilityHint::Regular(41),
            DefinitionSafety::Safe,
        ),
        definition_entry(
            "unsafe_row",
            Vec::new(),
            decoded(&constant("must_not_escape")),
            ReducibilityHint::Regular(7),
            DefinitionSafety::Unsafe,
        ),
        definition_entry(
            "partial_row",
            Vec::new(),
            decoded(&constant("must_not_escape")),
            ReducibilityHint::Abbrev,
            DefinitionSafety::Partial,
        ),
        definition_entry_with_constant_safety(
            "unsafe_constant_safe_body",
            Vec::new(),
            decoded(&constant("must_not_escape")),
            ReducibilityHint::Regular(9),
            ConstantSafety::Unsafe,
            DefinitionSafety::Safe,
        ),
        header_entry("axiom", ConstantKind::Axiom, ConstantSafety::Safe),
        header_entry("theorem", ConstantKind::Theorem, ConstantSafety::Safe),
        header_entry("opaque", ConstantKind::Opaque, ConstantSafety::Safe),
        header_entry(
            "header_definition",
            ConstantKind::Definition,
            ConstantSafety::Safe,
        ),
        header_entry("inductive", ConstantKind::Inductive, ConstantSafety::Safe),
        header_entry(
            "constructor",
            ConstantKind::Constructor,
            ConstantSafety::Safe,
        ),
        header_entry("recursor", ConstantKind::Recursor, ConstantSafety::Safe),
        header_entry("quotient", ConstantKind::Quotient, ConstantSafety::Unsafe),
    ]);

    for (name, expected) in [
        ("safe_opaque", "opaque_target"),
        ("safe_abbrev", "abbrev_target"),
        ("safe_regular", "regular_target"),
    ] {
        let result = complete(whnf(
            &decoded(&constant(name)),
            &context,
            WhnfBudget::unlimited(),
        ));
        assert_eq!(output_model(&result), Frozen::Constant(expected.to_owned()));
        assert_eq!(result.reductions, 1);
    }

    for name in [
        "unsafe_row",
        "partial_row",
        "unsafe_constant_safe_body",
        "axiom",
        "theorem",
        "opaque",
        "header_definition",
        "inductive",
        "constructor",
        "recursor",
        "quotient",
        "absent_row",
    ] {
        let result = complete(whnf(
            &decoded(&constant(name)),
            &context,
            WhnfBudget::unlimited(),
        ));
        assert_eq!(output_model(&result), Frozen::Constant(name.to_owned()));
        assert_eq!(result.reductions, 0);
    }
}

#[test]
fn polymorphic_delta_instantiates_ordered_universe_parameters_exactly() {
    let u = checker_name("u");
    let v = checker_name("v");
    let value = decoded(&Expr::const_(
        primary_name("UniverseWitness"),
        vec![
            Level::param(primary_name("u")),
            Level::param(primary_name("v")),
        ],
    ));
    let context = definition_context(vec![definition_entry(
        "poly",
        vec![u, v],
        value,
        ReducibilityHint::Regular(3),
        DefinitionSafety::Safe,
    )]);
    let input = decoded(&Expr::const_(
        primary_name("poly"),
        vec![Level::one(), Level::zero()],
    ));
    let result = complete(whnf(&input, &context, WhnfBudget::unlimited()));
    let ExprNode::Constant { name, levels } = result
        .term
        .node(result.term.root())
        .expect("delta result root exists")
    else {
        panic!("polymorphic definition did not expose its constant body");
    };
    assert_eq!(model_name(name), "UniverseWitness");
    assert_eq!(levels.len(), 2);
    let LevelNode::Succ(zero) = result.term.level(levels[0]).expect("first level exists") else {
        panic!("the first universe parameter did not receive Level::one");
    };
    assert!(matches!(result.term.level(*zero), Some(LevelNode::Zero)));
    assert!(matches!(
        result.term.level(levels[1]),
        Some(LevelNode::Zero)
    ));
    assert_eq!(result.reductions, 1);

    assert!(matches!(
        whnf(
            &decoded(&constant("poly")),
            &context,
            WhnfBudget::unlimited(),
        ),
        WhnfOutcome::Refused(WhnfRefusal::DefinitionInstantiation {
            refusal: InstantiationRefusal::ArityMismatch {
                parameters: 2,
                values: 0,
            },
            ..
        })
    ));
}

#[test]
fn delta_preserves_application_order_and_continues_beta_and_projection() {
    let choose_left = Expr::lam(
        primary_name("left"),
        Expr::sort(Level::zero()),
        Expr::lam(
            primary_name("right"),
            Expr::sort(Level::zero()),
            Expr::bvar(1).expect("outer binder is in scope"),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let environment = constant_environment(vec![
        definition_entry(
            "choose_left",
            Vec::new(),
            decoded(&choose_left),
            ReducibilityHint::Regular(2),
            DefinitionSafety::Safe,
        ),
        definition_entry(
            "packed",
            Vec::new(),
            decoded(&constructor([
                constant("parameter"),
                constant("selected_field"),
            ])),
            ReducibilityHint::Opaque,
            DefinitionSafety::Safe,
        ),
    ]);
    let context = WhnfContext::new(
        Vec::new(),
        vec![ProjectionRule::new(
            checker_name("GeneratedStructure"),
            checker_name("GeneratedConstructor"),
            1,
        )],
        environment,
    );

    let application = Expr::app(
        Expr::app(constant("choose_left"), constant("left_argument")),
        constant("right_argument"),
    );
    let application_result = complete(whnf(
        &decoded(&application),
        &context,
        WhnfBudget::unlimited(),
    ));
    assert_eq!(
        output_model(&application_result),
        Frozen::Constant("left_argument".to_owned())
    );
    assert_eq!(application_result.reductions, 2);

    let projection = Expr::proj(primary_name("GeneratedStructure"), 0, constant("packed"));
    let projection_result = complete(whnf(
        &decoded(&projection),
        &context,
        WhnfBudget::unlimited(),
    ));
    assert_eq!(
        output_model(&projection_result),
        Frozen::Constant("selected_field".to_owned())
    );
    assert_eq!(projection_result.reductions, 2);
}

#[test]
fn generated_safe_definition_delta_matches_frozen_targets() {
    const CASES: usize = 320;
    let entries = (0..CASES)
        .map(|index| {
            definition_entry(
                format!("generated_definition_{index}"),
                Vec::new(),
                decoded(&constant(format!("generated_target_{index}"))),
                match index % 3 {
                    0 => ReducibilityHint::Opaque,
                    1 => ReducibilityHint::Abbrev,
                    _ => ReducibilityHint::Regular(index as u32),
                },
                DefinitionSafety::Safe,
            )
        })
        .collect();
    let context = definition_context(entries);
    for index in 0..CASES {
        let result = complete(whnf(
            &decoded(&constant(format!("generated_definition_{index}"))),
            &context,
            WhnfBudget::unlimited(),
        ));
        assert_eq!(
            output_model(&result),
            Frozen::Constant(format!("generated_target_{index}"))
        );
        assert_eq!(result.reductions, 1);
    }
}

#[test]
fn delta_resources_cancellation_and_recursion_are_typed_and_recoverable() {
    let large_value = decoded(&Expr::app(
        constant("materialized_target"),
        constant("materialized_argument"),
    ));
    let context = definition_context(vec![
        definition_entry(
            "large",
            Vec::new(),
            large_value,
            ReducibilityHint::Regular(1),
            DefinitionSafety::Safe,
        ),
        definition_entry(
            "loop",
            Vec::new(),
            decoded(&constant("loop")),
            ReducibilityHint::Regular(1),
            DefinitionSafety::Safe,
        ),
    ]);
    let large = decoded(&constant("large"));

    assert!(matches!(
        whnf(
            &large,
            &context,
            WhnfBudget::new(
                u64::MAX,
                u64::MAX,
                TermBudget::unlimited().with_max_arena_nodes(1),
            ),
        ),
        WhnfOutcome::Inconclusive(WhnfStop::DefinitionInstantiation {
            stop: TermStop::Resource {
                limit: TermLimit::ArenaNodes,
                allowed: 1,
                observed: 2,
                ..
            },
            completed_reductions: 1,
            ..
        })
    ));

    let mut saw_delta_cancellation = false;
    for cancel_at in 1_u64..=64 {
        let mut polls = 0_u64;
        let interrupted = whnf_with(&large, &context, WhnfBudget::unlimited(), || {
            polls = polls.saturating_add(1);
            polls >= cancel_at
        });
        if matches!(
            interrupted,
            WhnfOutcome::Inconclusive(WhnfStop::DefinitionInstantiation {
                stop: TermStop::Cancelled { .. },
                ..
            })
        ) {
            saw_delta_cancellation = true;
            break;
        }
    }
    assert!(
        saw_delta_cancellation,
        "a cancellation poll must be observable inside definition instantiation"
    );

    let recovered = complete(whnf(&large, &context, WhnfBudget::unlimited()));
    assert_eq!(
        output_model(&recovered),
        apply(
            Frozen::Constant("materialized_target".to_owned()),
            Frozen::Constant("materialized_argument".to_owned()),
        )
    );

    assert!(matches!(
        whnf(
            &decoded(&constant("loop")),
            &context,
            WhnfBudget::new(100, 7, TermBudget::unlimited()),
        ),
        WhnfOutcome::Inconclusive(WhnfStop::Resource {
            limit: WhnfLimit::Reductions,
            allowed: 7,
            observed: 8,
            completed_reductions: 7,
            ..
        })
    ));
    assert_eq!(
        whnf(&large, &context, WhnfBudget::unlimited()),
        WhnfOutcome::Complete(recovered),
        "a recursive resource stop cannot poison the immutable environment"
    );
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
        ConstantEnvironment::empty(),
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
        ConstantEnvironment::empty(),
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
        ConstantEnvironment::empty(),
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
    let compact = whnf(
        &stuck_application,
        &WhnfContext::default(),
        WhnfBudget::new(
            u64::MAX,
            u64::MAX,
            TermBudget::unlimited().with_max_arena_nodes(3),
        ),
    );
    assert!(matches!(
        compact,
        WhnfOutcome::Complete(WhnfResult {
            reductions: 0,
            ref term,
            ..
        }) if term.nodes().len() == 3
    ));
    assert!(matches!(
        whnf(
            &stuck_application,
            &WhnfContext::default(),
            WhnfBudget::new(
                u64::MAX,
                u64::MAX,
                TermBudget::unlimited().with_max_arena_nodes(2),
            ),
        ),
        WhnfOutcome::Inconclusive(WhnfStop::Materialization {
            phase: WhnfPhase::Initial,
            stop: TermStop::Resource {
                limit: TermLimit::ArenaNodes,
                allowed: 2,
                observed: 3,
                ..
            },
            completed_reductions: 0,
            ..
        })
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
    let term = match decode_expr(&writer.into_bytes(), DecodeBudget::unlimited()) {
        DecodeOutcome::Complete(Ok(value)) => value,
        _ => return Err("deep primary-shaped application spine did not decode".to_owned()),
    };
    let result = match whnf(&term, &WhnfContext::default(), WhnfBudget::unlimited()) {
        WhnfOutcome::Complete(value) => value,
        _ => return Err("deep stuck application did not complete".to_owned()),
    };
    if result.reductions != 0 {
        return Err(format!(
            "stuck application reduction count drifted: {}",
            result.reductions
        ));
    }
    if result.term.nodes().len() != DEPTH.saturating_mul(2).saturating_add(1)
        || !matches!(
            result.term.node(result.term.root()),
            Some(ExprNode::Apply { .. })
        )
    {
        return Err("deep stuck application was not rebuilt compactly".to_owned());
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

fn deep_delta_child() -> Result<(), String> {
    const DEPTH: usize = 50_000;
    let names: Vec<_> = (0..=DEPTH)
        .map(|index| format!("deep_definition_{index}"))
        .collect();
    let type_ = decoded(&Expr::sort(Level::zero()));
    let entries = (0..DEPTH)
        .map(|index| {
            ConstantEntry::new(
                checker_name(names[index].clone()),
                ConstantDeclaration::definition(
                    Vec::new(),
                    type_.clone(),
                    ConstantSafety::Safe,
                    DefinitionBody::new(
                        decoded(&constant(names[index + 1].clone())),
                        ReducibilityHint::Regular(index as u32),
                        DefinitionSafety::Safe,
                        Vec::new(),
                    ),
                ),
            )
        })
        .collect();
    let environment = match ConstantEnvironment::build(entries, EnvironmentBudget::unlimited()) {
        EnvironmentOutcome::Complete { environment, .. } => environment,
        other => return Err(format!("deep constant environment failed: {other:?}")),
    };
    let context = WhnfContext::new(Vec::new(), Vec::new(), environment);
    let result = match whnf(
        &decoded(&constant(names[0].clone())),
        &context,
        WhnfBudget::unlimited(),
    ) {
        WhnfOutcome::Complete(result) => result,
        other => return Err(format!("deep definition chain did not complete: {other:?}")),
    };
    if result.reductions != DEPTH as u64 {
        return Err(format!(
            "deep delta reduction count drifted: {}",
            result.reductions
        ));
    }
    let Some(ExprNode::Constant { name, levels }) = result.term.node(result.term.root()) else {
        return Err("deep delta result is not a constant".to_owned());
    };
    if model_name(name) != names[DEPTH] || !levels.is_empty() {
        return Err("deep delta result is not the terminal definition name".to_owned());
    }
    Ok(())
}

#[test]
fn deep_safe_definition_chain_fits_a_64k_stack() {
    const CHILD_ENV: &str = "FLN_CHECKER_DELTA_DEEP_CHILD";
    if std::env::var_os(CHILD_ENV).is_some() {
        let result = std::thread::Builder::new()
            .name("fln-checker-delta-deep".to_owned())
            .stack_size(64 * 1024)
            .spawn(deep_delta_child)
            .expect("spawn bounded-stack delta child thread")
            .join()
            .expect("bounded-stack delta child thread did not panic");
        result.expect("bounded-stack safe-definition delta reduction");
        return;
    }

    let executable = std::env::current_exe().expect("current test executable");
    let output = Command::new(executable)
        .env(CHILD_ENV, "1")
        .args([
            "--exact",
            "deep_safe_definition_chain_fits_a_64k_stack",
            "--nocapture",
        ])
        .output()
        .expect("run bounded-stack delta child process");
    assert!(
        output.status.success(),
        "bounded-stack delta child failed\nstdout:\n{}\nstderr:\n{}",
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
