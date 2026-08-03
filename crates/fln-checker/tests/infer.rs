#![forbid(unsafe_code)]

use std::process::Command;

use fln_checker::environment::{
    ConstantDeclaration, ConstantEntry, ConstantEnvironment, ConstantKind, ConstantSafety,
    DefinitionBody, DefinitionSafety, EnvironmentBudget, EnvironmentOutcome, ReducibilityHint,
};
use fln_checker::infer::{
    InferenceBudget, InferenceContext, InferenceContextRefusal, InferenceDeferred, InferenceFault,
    InferenceLimit, InferenceMode, InferenceOutcome, InferencePhase, InferenceRefusal,
    InferenceResult, InferenceStop, LocalDeclaration, infer, infer_with,
};
use fln_checker::term::{TermBudget, TermLimit, TermStop};
use fln_checker::wire::{
    DecodeBudget, DecodeOutcome, ExprNode, LevelId, LevelNode, WireExpr, WireName, decode_expr,
    decode_name,
};
use fln_core::expr::{BinderInfo, Expr, FVarId, Literal, MVarId, NatLit};
use fln_core::level::{LMVarId, Level};
use fln_core::name::Name;
use fln_core::options::KVMap;
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

fn sort(level: Level) -> WireExpr {
    decoded(&Expr::sort(level))
}

fn header(
    name: &str,
    parameters: Vec<WireName>,
    type_: WireExpr,
    kind: ConstantKind,
    safety: ConstantSafety,
) -> ConstantEntry {
    ConstantEntry::new(
        checker_name(name),
        ConstantDeclaration::header(parameters, type_, kind, safety),
    )
}

fn definition(
    name: &str,
    type_: WireExpr,
    safety: ConstantSafety,
    body_safety: DefinitionSafety,
) -> ConstantEntry {
    ConstantEntry::new(
        checker_name(name),
        ConstantDeclaration::definition(
            Vec::new(),
            type_,
            safety,
            DefinitionBody::new(
                decoded(&Expr::lit(Literal::Nat(NatLit::from_u64(0)))),
                ReducibilityHint::Regular(0),
                body_safety,
                Vec::new(),
            ),
        ),
    )
}

fn environment(entries: Vec<ConstantEntry>) -> ConstantEnvironment {
    match ConstantEnvironment::build(entries, EnvironmentBudget::unlimited()) {
        EnvironmentOutcome::Complete { environment, .. } => environment,
        other => panic!("checker environment did not build: {other:?}"),
    }
}

fn built_context(
    locals: Vec<LocalDeclaration>,
    parameters: Vec<WireName>,
    entries: Vec<ConstantEntry>,
) -> InferenceContext {
    InferenceContext::new(locals, parameters, environment(entries))
        .expect("unique checker inference context")
}

fn complete(outcome: InferenceOutcome) -> InferenceResult {
    match outcome {
        InferenceOutcome::Complete(result) => result,
        other => panic!("unexpected inference non-success: {other:?}"),
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum LevelModel {
    Zero,
    Succ(Box<LevelModel>),
    Max(Box<LevelModel>, Box<LevelModel>),
    IMax(Box<LevelModel>, Box<LevelModel>),
    Parameter(WireName),
    Meta(WireName),
}

fn level_model(term: &WireExpr, root: LevelId) -> LevelModel {
    match term.level(root).expect("inferred type has a valid level") {
        LevelNode::Zero => LevelModel::Zero,
        LevelNode::Succ(child) => LevelModel::Succ(Box::new(level_model(term, *child))),
        LevelNode::Max(left, right) => LevelModel::Max(
            Box::new(level_model(term, *left)),
            Box::new(level_model(term, *right)),
        ),
        LevelNode::IMax(left, right) => LevelModel::IMax(
            Box::new(level_model(term, *left)),
            Box::new(level_model(term, *right)),
        ),
        LevelNode::Parameter(name) => LevelModel::Parameter(name.clone()),
        LevelNode::Meta(name) => LevelModel::Meta(name.clone()),
    }
}

fn sort_model(term: &WireExpr) -> LevelModel {
    match term.node(term.root()).expect("inferred type has a root") {
        ExprNode::Sort { level } => level_model(term, *level),
        other => panic!("inferred type was not a sort: {other:?}"),
    }
}

#[test]
fn leaf_dispatch_and_metadata_transparency_are_exact() {
    let x = checker_name("x");
    let u = checker_name("u");
    let local_type = sort(Level::zero());
    let local_value = decoded(&Expr::lit(Literal::Nat(NatLit::from_u64(7))));
    let local = LocalDeclaration::definition(x.clone(), local_type.clone(), local_value.clone());
    let context = built_context(
        vec![local],
        Vec::new(),
        vec![header(
            "C",
            vec![u.clone()],
            sort(Level::param(primary_name("u"))),
            ConstantKind::Axiom,
            ConstantSafety::Safe,
        )],
    );
    assert_eq!(context.locals()[0].value(), Some(&local_value));

    let free = decoded(&Expr::fvar(FVarId(primary_name("x"))));
    let free_result = complete(infer(
        &free,
        &context,
        InferenceMode::InferOnly,
        InferenceBudget::unlimited(),
    ));
    assert_eq!(free_result.type_, local_type);

    let wrapped = decoded(&Expr::mdata(
        KVMap::new(),
        Expr::mdata(KVMap::new(), Expr::fvar(FVarId(primary_name("x")))),
    ));
    let wrapped_result = complete(infer(
        &wrapped,
        &context,
        InferenceMode::InferOnly,
        InferenceBudget::unlimited(),
    ));
    assert_eq!(wrapped_result.type_, local_type);
    assert_eq!(wrapped_result.progress.metadata_layers, 2);

    assert!(matches!(
        infer(
            &decoded(&Expr::mvar(MVarId(primary_name("m")))),
            &context,
            InferenceMode::InferOnly,
            InferenceBudget::unlimited(),
        ),
        InferenceOutcome::Refused {
            refusal: InferenceRefusal::ExpressionMetavariable,
            ..
        }
    ));
    for index in [0, 3] {
        assert!(matches!(
            infer(
                &decoded(&Expr::bvar(index).expect("bound index packs")),
                &context,
                InferenceMode::InferOnly,
                InferenceBudget::unlimited(),
            ),
            InferenceOutcome::InternalFault {
                fault: InferenceFault::LooseBoundVariables {
                    external_bound_span: span
                },
                ..
            } if span == index + 1
        ));
    }

    let sort_result = complete(infer(
        &sort(Level::zero()),
        &context,
        InferenceMode::InferOnly,
        InferenceBudget::unlimited(),
    ));
    assert_eq!(
        sort_model(&sort_result.type_),
        LevelModel::Succ(Box::new(LevelModel::Zero))
    );

    let constant_result = complete(infer(
        &decoded(&Expr::const_(primary_name("C"), vec![Level::one()])),
        &context,
        InferenceMode::InferOnly,
        InferenceBudget::unlimited(),
    ));
    assert_eq!(
        sort_model(&constant_result.type_),
        LevelModel::Succ(Box::new(LevelModel::Zero))
    );

    assert!(matches!(
        infer(
            &decoded(&Expr::fvar(FVarId(primary_name("missing")))),
            &context,
            InferenceMode::InferOnly,
            InferenceBudget::unlimited(),
        ),
        InferenceOutcome::Refused {
            refusal: InferenceRefusal::UnknownFreeVariable { .. },
            ..
        }
    ));
    assert!(matches!(
        infer(
            &decoded(&Expr::const_(primary_name("Missing"), Vec::new())),
            &context,
            InferenceMode::InferOnly,
            InferenceBudget::unlimited(),
        ),
        InferenceOutcome::Refused {
            refusal: InferenceRefusal::UnknownConstant { .. },
            ..
        }
    ));
}

#[test]
fn local_context_duplicates_refuse_without_a_partial_context_and_recover() {
    let x = checker_name("x");
    let type_ = sort(Level::zero());
    assert!(matches!(
        InferenceContext::new(
            vec![
                LocalDeclaration::assumption(x.clone(), type_.clone()),
                LocalDeclaration::definition(
                    x.clone(),
                    type_.clone(),
                    decoded(&Expr::lit(Literal::Nat(NatLit::from_u64(1)))),
                ),
            ],
            Vec::new(),
            ConstantEnvironment::empty(),
        ),
        Err(InferenceContextRefusal::DuplicateLocal {
            first: 0,
            second: 1,
            ..
        })
    ));

    let u = checker_name("u");
    assert!(matches!(
        InferenceContext::new(
            Vec::new(),
            vec![u.clone(), u.clone()],
            ConstantEnvironment::empty(),
        ),
        Err(InferenceContextRefusal::DuplicateLevelParameter {
            first: 0,
            second: 1,
            ..
        })
    ));

    let recovered = InferenceContext::new(
        vec![LocalDeclaration::assumption(x, type_)],
        vec![u],
        ConstantEnvironment::empty(),
    )
    .expect("clean context recovers exactly");
    assert_eq!(recovered.locals().len(), 1);
    assert!(recovered.locals()[0].value().is_none());
    assert_eq!(recovered.level_parameters().len(), 1);
}

#[test]
fn constant_arity_universe_and_safety_quarantines_are_mode_exact() {
    let u = checker_name("u");
    let p = checker_name("p");
    let entries = vec![
        header(
            "C",
            vec![u],
            sort(Level::param(primary_name("u"))),
            ConstantKind::Axiom,
            ConstantSafety::Safe,
        ),
        header(
            "UnsafeC",
            Vec::new(),
            sort(Level::zero()),
            ConstantKind::Axiom,
            ConstantSafety::Unsafe,
        ),
        definition(
            "PartialC",
            sort(Level::zero()),
            ConstantSafety::Safe,
            DefinitionSafety::Partial,
        ),
    ];
    let constants = environment(entries);
    let context = InferenceContext::new(Vec::new(), vec![p.clone()], constants)
        .expect("unique checking context");
    let safe_mode = InferenceMode::Checking {
        declaration_safety: ConstantSafety::Safe,
    };
    let unsafe_mode = InferenceMode::Checking {
        declaration_safety: ConstantSafety::Unsafe,
    };

    for (levels, actual) in [(Vec::new(), 0), (vec![Level::zero(), Level::one()], 2)] {
        assert!(matches!(
            infer(
                &decoded(&Expr::const_(primary_name("C"), levels)),
                &context,
                InferenceMode::InferOnly,
                InferenceBudget::unlimited(),
            ),
            InferenceOutcome::Refused {
                refusal: InferenceRefusal::ConstantUniverseArity {
                    expected: 1,
                    actual: seen,
                    ..
                },
                ..
            } if seen == actual
        ));
    }

    let declared = decoded(&Expr::const_(
        primary_name("C"),
        vec![Level::param(primary_name("p"))],
    ));
    assert!(matches!(
        infer(&declared, &context, safe_mode, InferenceBudget::unlimited()),
        InferenceOutcome::Complete(_)
    ));

    let undeclared = decoded(&Expr::const_(
        primary_name("C"),
        vec![Level::param(primary_name("q"))],
    ));
    assert!(matches!(
        infer(
            &undeclared,
            &context,
            safe_mode,
            InferenceBudget::unlimited()
        ),
        InferenceOutcome::Refused {
            refusal: InferenceRefusal::UndeclaredUniverseParameter { .. },
            ..
        }
    ));
    assert!(matches!(
        infer(
            &undeclared,
            &context,
            InferenceMode::InferOnly,
            InferenceBudget::unlimited()
        ),
        InferenceOutcome::Complete(_)
    ));

    let universe_meta = decoded(&Expr::const_(
        primary_name("C"),
        vec![Level::mvar(LMVarId(primary_name("m")))],
    ));
    assert!(matches!(
        infer(
            &universe_meta,
            &context,
            safe_mode,
            InferenceBudget::unlimited()
        ),
        InferenceOutcome::Refused {
            refusal: InferenceRefusal::UniverseMetavariable { .. },
            ..
        }
    ));
    assert!(matches!(
        infer(
            &universe_meta,
            &context,
            InferenceMode::InferOnly,
            InferenceBudget::unlimited()
        ),
        InferenceOutcome::Complete(_)
    ));

    let undeclared_sort = sort(Level::param(primary_name("q")));
    assert!(matches!(
        infer(
            &undeclared_sort,
            &context,
            safe_mode,
            InferenceBudget::unlimited()
        ),
        InferenceOutcome::Refused {
            refusal: InferenceRefusal::UndeclaredUniverseParameter { .. },
            ..
        }
    ));
    let meta_sort = sort(Level::mvar(LMVarId(primary_name("m"))));
    assert!(matches!(
        infer(
            &meta_sort,
            &context,
            safe_mode,
            InferenceBudget::unlimited()
        ),
        InferenceOutcome::Refused {
            refusal: InferenceRefusal::UniverseMetavariable { .. },
            ..
        }
    ));
    assert!(matches!(
        infer(
            &meta_sort,
            &context,
            InferenceMode::InferOnly,
            InferenceBudget::unlimited()
        ),
        InferenceOutcome::Complete(_)
    ));

    let unsafe_constant = decoded(&Expr::const_(primary_name("UnsafeC"), Vec::new()));
    assert!(matches!(
        infer(
            &unsafe_constant,
            &context,
            safe_mode,
            InferenceBudget::unlimited()
        ),
        InferenceOutcome::Refused {
            refusal: InferenceRefusal::UnsafeConstant { .. },
            ..
        }
    ));
    assert!(matches!(
        infer(
            &unsafe_constant,
            &context,
            unsafe_mode,
            InferenceBudget::unlimited()
        ),
        InferenceOutcome::Complete(_)
    ));

    let partial_constant = decoded(&Expr::const_(primary_name("PartialC"), Vec::new()));
    assert!(matches!(
        infer(
            &partial_constant,
            &context,
            safe_mode,
            InferenceBudget::unlimited()
        ),
        InferenceOutcome::Refused {
            refusal: InferenceRefusal::PartialConstant { .. },
            ..
        }
    ));
    assert!(matches!(
        infer(
            &partial_constant,
            &context,
            unsafe_mode,
            InferenceBudget::unlimited()
        ),
        InferenceOutcome::Complete(_)
    ));
}

#[test]
fn generated_level_constructors_preserve_sort_successor_and_constant_instantiation() {
    let p = primary_name("p");
    let m = primary_name("m");
    let parameter = Level::param(p.clone());
    let levels = [
        Level::zero(),
        Level::one(),
        parameter.clone(),
        Level::max(parameter.clone(), Level::one()).expect("shallow max"),
        Level::imax(parameter.clone(), Level::one()).expect("shallow imax"),
        Level::mvar(LMVarId(m)),
    ];
    let context = built_context(
        Vec::new(),
        vec![checker_name("p")],
        vec![header(
            "C",
            vec![checker_name("u")],
            sort(Level::param(primary_name("u"))),
            ConstantKind::Axiom,
            ConstantSafety::Safe,
        )],
    );

    for (index, level) in levels.iter().enumerate() {
        let source = sort(level.clone());
        let source_model = match source.node(source.root()).expect("sort root") {
            ExprNode::Sort { level } => level_model(&source, *level),
            other => panic!("generated source was not a sort: {other:?}"),
        };
        let inferred_sort = complete(infer(
            &source,
            &context,
            InferenceMode::InferOnly,
            InferenceBudget::unlimited(),
        ));
        assert_eq!(
            sort_model(&inferred_sort.type_),
            LevelModel::Succ(Box::new(source_model.clone())),
            "Sort successor drift at generated level {index}"
        );

        let constant = decoded(&Expr::const_(primary_name("C"), vec![level.clone()]));
        let inferred_constant = complete(infer(
            &constant,
            &context,
            InferenceMode::InferOnly,
            InferenceBudget::unlimited(),
        ));
        assert_eq!(
            sort_model(&inferred_constant.type_),
            source_model,
            "constant instantiation drift at generated level {index}"
        );

        let checking = InferenceMode::Checking {
            declaration_safety: ConstantSafety::Safe,
        };
        if index + 1 == levels.len() {
            for candidate in [&source, &constant] {
                assert!(matches!(
                    infer(candidate, &context, checking, InferenceBudget::unlimited(),),
                    InferenceOutcome::Refused {
                        refusal: InferenceRefusal::UniverseMetavariable { .. },
                        ..
                    }
                ));
            }
        } else {
            assert!(matches!(
                infer(&source, &context, checking, InferenceBudget::unlimited(),),
                InferenceOutcome::Complete(_)
            ));
            assert!(matches!(
                infer(&constant, &context, checking, InferenceBudget::unlimited(),),
                InferenceOutcome::Complete(_)
            ));
        }
    }
}

#[test]
fn unsupported_rule_families_are_deferred_and_metadata_does_not_change_the_requirement() {
    let sort_zero = Expr::sort(Level::zero());
    let cases = vec![
        (
            Expr::app(sort_zero.clone(), sort_zero.clone()),
            InferenceDeferred::Application,
        ),
        (
            Expr::lam(
                Name::anonymous(),
                sort_zero.clone(),
                sort_zero.clone(),
                BinderInfo::Default,
            ),
            InferenceDeferred::Lambda,
        ),
        (
            Expr::forall_e(
                Name::anonymous(),
                sort_zero.clone(),
                sort_zero.clone(),
                BinderInfo::Implicit,
            ),
            InferenceDeferred::Forall,
        ),
        (
            Expr::let_e(
                Name::anonymous(),
                sort_zero.clone(),
                sort_zero.clone(),
                sort_zero.clone(),
                false,
            ),
            InferenceDeferred::Let,
        ),
        (
            Expr::lit(Literal::Nat(NatLit::from_u64(11))),
            InferenceDeferred::NatLiteral,
        ),
        (
            Expr::lit(Literal::Str("deferred".to_owned())),
            InferenceDeferred::StringLiteral,
        ),
        (
            Expr::proj(primary_name("S"), 0, sort_zero.clone()),
            InferenceDeferred::Projection,
        ),
    ];
    let context = InferenceContext::empty(ConstantEnvironment::empty());
    for (expression, requirement) in cases {
        for candidate in [expression.clone(), Expr::mdata(KVMap::new(), expression)] {
            assert!(matches!(
                infer(
                    &decoded(&candidate),
                    &context,
                    InferenceMode::InferOnly,
                    InferenceBudget::unlimited(),
                ),
                InferenceOutcome::Deferred {
                    requirement: seen,
                    ..
                } if seen == requirement
            ));
        }
    }
}

#[test]
fn every_resource_boundary_is_typed_and_the_exact_budget_recovers() {
    let context = InferenceContext::empty(ConstantEnvironment::empty());
    let zero_sort = sort(Level::zero());

    let outer_stop = infer(
        &zero_sort,
        &context,
        InferenceMode::InferOnly,
        InferenceBudget::new(
            0,
            u64::MAX,
            TermBudget::unlimited(),
            TermBudget::unlimited(),
        ),
    );
    assert!(matches!(
        outer_stop,
        InferenceOutcome::Inconclusive(InferenceStop::Resource {
            limit: InferenceLimit::Steps,
            allowed: 0,
            observed: 1,
            phase: InferencePhase::Precondition,
            ..
        })
    ));

    assert!(matches!(
        infer(
            &zero_sort,
            &context,
            InferenceMode::InferOnly,
            InferenceBudget::new(
                u64::MAX,
                u64::MAX,
                TermBudget::new(0, u64::MAX),
                TermBudget::unlimited(),
            ),
        ),
        InferenceOutcome::Inconclusive(InferenceStop::Inspection {
            stop: TermStop::Resource {
                limit: TermLimit::Steps,
                allowed: 0,
                observed: 1,
                ..
            },
            ..
        })
    ));

    let materialization_steps = |allowed| {
        infer(
            &zero_sort,
            &context,
            InferenceMode::InferOnly,
            InferenceBudget::new(
                u64::MAX,
                u64::MAX,
                TermBudget::unlimited(),
                TermBudget::new(allowed, u64::MAX),
            ),
        )
    };
    assert!(matches!(
        materialization_steps(2),
        InferenceOutcome::Inconclusive(InferenceStop::Materialization {
            phase: InferencePhase::SortType,
            stop: TermStop::Resource {
                limit: TermLimit::Steps,
                allowed: 2,
                observed: 3,
                ..
            },
            ..
        })
    ));
    assert!(matches!(
        materialization_steps(3),
        InferenceOutcome::Complete(_)
    ));

    let arena_budget = |allowed| {
        infer(
            &zero_sort,
            &context,
            InferenceMode::InferOnly,
            InferenceBudget::new(
                u64::MAX,
                u64::MAX,
                TermBudget::unlimited(),
                TermBudget::unlimited().with_max_arena_nodes(allowed),
            ),
        )
    };
    assert!(matches!(
        arena_budget(2),
        InferenceOutcome::Inconclusive(InferenceStop::Materialization {
            phase: InferencePhase::SortType,
            stop: TermStop::Resource {
                limit: TermLimit::ArenaNodes,
                allowed: 2,
                observed: 3,
                ..
            },
            ..
        })
    ));
    assert!(matches!(arena_budget(3), InferenceOutcome::Complete(_)));

    let parameter_sort = sort(Level::param(primary_name("payload")));
    let output_budget = |allowed| {
        infer(
            &parameter_sort,
            &context,
            InferenceMode::InferOnly,
            InferenceBudget::new(
                u64::MAX,
                u64::MAX,
                TermBudget::unlimited(),
                TermBudget::new(u64::MAX, allowed),
            ),
        )
    };
    let mut exact_output = 0;
    loop {
        match output_budget(exact_output) {
            InferenceOutcome::Inconclusive(InferenceStop::Materialization {
                phase: InferencePhase::SortType,
                stop:
                    TermStop::Resource {
                        limit: TermLimit::OutputUnits,
                        allowed,
                        observed,
                        ..
                    },
                ..
            }) => {
                assert_eq!(allowed, exact_output);
                assert!(observed > allowed);
                exact_output = observed;
            }
            InferenceOutcome::Complete(_) => break,
            other => panic!("output boundary search changed outcome class: {other:?}"),
        }
    }
    assert!(exact_output > 0);
    assert!(matches!(
        output_budget(exact_output - 1),
        InferenceOutcome::Inconclusive(InferenceStop::Materialization {
            phase: InferencePhase::SortType,
            stop: TermStop::Resource {
                limit: TermLimit::OutputUnits,
                allowed,
                observed,
                ..
            },
            ..
        }) if allowed + 1 == observed && observed == exact_output
    ));
    assert!(matches!(
        output_budget(exact_output),
        InferenceOutcome::Complete(_)
    ));

    let local_context = InferenceContext::new(
        vec![LocalDeclaration::assumption(
            checker_name("x"),
            sort(Level::zero()),
        )],
        Vec::new(),
        ConstantEnvironment::empty(),
    )
    .expect("unique local context");
    let free = decoded(&Expr::fvar(FVarId(primary_name("x"))));
    assert!(matches!(
        infer(
            &free,
            &local_context,
            InferenceMode::InferOnly,
            InferenceBudget::new(
                u64::MAX,
                u64::MAX,
                TermBudget::unlimited(),
                TermBudget::new(0, u64::MAX),
            ),
        ),
        InferenceOutcome::Inconclusive(InferenceStop::Materialization {
            phase: InferencePhase::LocalType,
            stop: TermStop::Resource {
                limit: TermLimit::Steps,
                allowed: 0,
                observed: 1,
                ..
            },
            ..
        })
    ));
    assert!(matches!(
        infer(
            &free,
            &local_context,
            InferenceMode::InferOnly,
            InferenceBudget::unlimited(),
        ),
        InferenceOutcome::Complete(_)
    ));

    let constant_context = built_context(
        Vec::new(),
        Vec::new(),
        vec![header(
            "C",
            vec![checker_name("u")],
            sort(Level::param(primary_name("u"))),
            ConstantKind::Axiom,
            ConstantSafety::Safe,
        )],
    );
    let constant = decoded(&Expr::const_(primary_name("C"), vec![Level::zero()]));
    assert!(matches!(
        infer(
            &constant,
            &constant_context,
            InferenceMode::InferOnly,
            InferenceBudget::new(
                u64::MAX,
                u64::MAX,
                TermBudget::unlimited(),
                TermBudget::new(0, u64::MAX),
            ),
        ),
        InferenceOutcome::Inconclusive(InferenceStop::Materialization {
            phase: InferencePhase::ConstantType,
            stop: TermStop::Resource {
                limit: TermLimit::Steps,
                allowed: 0,
                observed: 1,
                ..
            },
            ..
        })
    ));
    assert!(matches!(
        infer(
            &constant,
            &constant_context,
            InferenceMode::InferOnly,
            InferenceBudget::unlimited(),
        ),
        InferenceOutcome::Complete(_)
    ));

    let p = primary_name("p");
    let q = primary_name("q");
    let checking_sort =
        sort(Level::max(Level::param(p.clone()), Level::param(q.clone())).expect("shallow max"));
    let checking_context = InferenceContext::new(
        Vec::new(),
        vec![checker_name("p"), checker_name("q")],
        ConstantEnvironment::empty(),
    )
    .expect("unique level context");
    let checking_mode = InferenceMode::Checking {
        declaration_safety: ConstantSafety::Safe,
    };
    let baseline = complete(infer(
        &checking_sort,
        &checking_context,
        checking_mode,
        InferenceBudget::unlimited(),
    ));
    assert!(baseline.progress.level_nodes > 1);
    let exact_nodes = baseline.progress.level_nodes;
    assert!(matches!(
        infer(
            &checking_sort,
            &checking_context,
            checking_mode,
            InferenceBudget::new(
                u64::MAX,
                exact_nodes - 1,
                TermBudget::unlimited(),
                TermBudget::unlimited(),
            ),
        ),
        InferenceOutcome::Inconclusive(InferenceStop::Resource {
            limit: InferenceLimit::LevelNodes,
            allowed,
            observed,
            ..
        }) if allowed + 1 == observed && observed == exact_nodes
    ));
    assert!(matches!(
        infer(
            &checking_sort,
            &checking_context,
            checking_mode,
            InferenceBudget::new(
                u64::MAX,
                exact_nodes,
                TermBudget::unlimited(),
                TermBudget::unlimited(),
            ),
        ),
        InferenceOutcome::Complete(_)
    ));
}

#[test]
fn cancellation_reaches_each_phase_without_partial_output_and_cleanly_recovers() {
    let wrapped = decoded(&Expr::mdata(
        KVMap::new(),
        Expr::sort(
            Level::max(
                Level::param(primary_name("p")),
                Level::param(primary_name("q")),
            )
            .expect("shallow max"),
        ),
    ));
    let context = InferenceContext::new(
        Vec::new(),
        vec![checker_name("p"), checker_name("q")],
        ConstantEnvironment::empty(),
    )
    .expect("unique level context");
    let mode = InferenceMode::Checking {
        declaration_safety: ConstantSafety::Safe,
    };
    let baseline = complete(infer(
        &wrapped,
        &context,
        mode,
        InferenceBudget::unlimited(),
    ));

    let mut saw_precondition = false;
    let mut saw_inspection = false;
    let mut saw_metadata = false;
    let mut saw_dispatch = false;
    let mut saw_universe = false;
    let mut saw_materialization = false;
    for cancellation_poll in 1..128 {
        let mut polls = 0usize;
        let outcome = infer_with(
            &wrapped,
            &context,
            mode,
            InferenceBudget::unlimited(),
            || {
                polls += 1;
                polls == cancellation_poll
            },
        );
        match outcome {
            InferenceOutcome::Inconclusive(InferenceStop::Cancelled { phase, .. }) => match phase {
                InferencePhase::Precondition => saw_precondition = true,
                InferencePhase::Metadata => saw_metadata = true,
                InferencePhase::Dispatch => saw_dispatch = true,
                InferencePhase::UniverseValidation => saw_universe = true,
                InferencePhase::LocalType
                | InferencePhase::SortType
                | InferencePhase::ConstantType => {
                    panic!("nested work surfaced as an outer cancellation phase")
                }
            },
            InferenceOutcome::Inconclusive(InferenceStop::Inspection {
                stop: TermStop::Cancelled { .. },
                ..
            }) => saw_inspection = true,
            InferenceOutcome::Inconclusive(InferenceStop::Materialization {
                stop: TermStop::Cancelled { .. },
                ..
            }) => saw_materialization = true,
            InferenceOutcome::Complete(result) => {
                assert_eq!(result.type_, baseline.type_);
                break;
            }
            other => panic!("cancellation became a semantic answer: {other:?}"),
        }
    }
    assert!(saw_precondition);
    assert!(saw_inspection);
    assert!(saw_metadata);
    assert!(saw_dispatch);
    assert!(saw_universe);
    assert!(saw_materialization);
    assert_eq!(
        complete(infer(
            &wrapped,
            &context,
            mode,
            InferenceBudget::unlimited(),
        ))
        .type_,
        baseline.type_
    );
}

fn deep_metadata_child() -> Result<(), String> {
    const DEPTH: usize = 50_000;
    let mut writer = CanonWriter::new();
    writer.schema(SCHEMA_EXPR);
    for _ in 0..DEPTH {
        writer.u8(11);
        writer.u64(0);
    }
    writer.u8(3);
    writer.u8(0);
    let term = match decode_expr(&writer.into_bytes(), DecodeBudget::unlimited()) {
        DecodeOutcome::Complete(Ok(value)) => value,
        other => return Err(format!("deep metadata bytes did not decode: {other:?}")),
    };
    let result = match infer(
        &term,
        &InferenceContext::empty(ConstantEnvironment::empty()),
        InferenceMode::InferOnly,
        InferenceBudget::unlimited(),
    ) {
        InferenceOutcome::Complete(result) => result,
        other => return Err(format!("deep metadata inference failed: {other:?}")),
    };
    if result.progress.metadata_layers != DEPTH as u64 {
        return Err(format!(
            "metadata layer count drifted: {}",
            result.progress.metadata_layers
        ));
    }
    if sort_model(&result.type_) != LevelModel::Succ(Box::new(LevelModel::Zero)) {
        return Err("deep metadata inferred the wrong successor sort".to_owned());
    }
    Ok(())
}

#[test]
fn deep_metadata_transparency_fits_a_64k_stack() {
    const CHILD_ENV: &str = "FLN_CHECKER_INFER_DEEP_CHILD";
    if std::env::var_os(CHILD_ENV).is_some() {
        let result = std::thread::Builder::new()
            .name("fln-checker-infer-deep".to_owned())
            .stack_size(64 * 1024)
            .spawn(deep_metadata_child)
            .expect("spawn bounded-stack inference child")
            .join()
            .expect("bounded-stack inference child did not panic");
        result.expect("bounded-stack inference work");
        return;
    }

    let executable = std::env::current_exe().expect("current test executable");
    let output = Command::new(executable)
        .env(CHILD_ENV, "1")
        .args([
            "--exact",
            "deep_metadata_transparency_fits_a_64k_stack",
            "--nocapture",
        ])
        .output()
        .expect("run bounded-stack inference child process");
    assert!(
        output.status.success(),
        "bounded-stack inference child failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn inference_production_code_has_no_primary_semantic_path() {
    let source = include_str!("../src/infer.rs");
    for forbidden in [
        "fln_env::",
        "fln_kernel::",
        "fln_core::expr",
        "TypeChecker",
        "from_canonical_bytes(",
        "loose_bvar_range(",
        "has_expr_mvar(",
        "is_equiv(",
    ] {
        assert!(
            !source.contains(forbidden),
            "checker inference reached a forbidden primary semantic path: {forbidden}"
        );
    }
}
