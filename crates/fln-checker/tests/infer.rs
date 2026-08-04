#![forbid(unsafe_code)]

use std::process::Command;

use fln_checker::defeq::{
    DefEqBudget, DefEqOutcome, DefEqStop, QuickDefEqBudget, QuickDefEqStop, def_eq,
};
use fln_checker::environment::{
    ConstantDeclaration, ConstantEntry, ConstantEnvironment, ConstantKind, ConstantSafety,
    DefinitionBody, DefinitionSafety, EnvironmentBudget, EnvironmentOutcome, ReducibilityHint,
};
use fln_checker::infer::{
    InferenceBudget, InferenceContext, InferenceContextRefusal, InferenceDeferred, InferenceFault,
    InferenceLimit, InferenceMode, InferenceOutcome, InferencePhase, InferenceRefusal,
    InferenceResult, InferenceSortSite, InferenceStop, LocalDeclaration, infer, infer_with,
};
use fln_checker::term::{TermBudget, TermLimit, TermStop};
use fln_checker::whnf::{ProjectionRule, WhnfBudget, WhnfContext, WhnfStop};
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
    checker_name_value(&name)
}

fn checker_name_value(name: &Name) -> WireName {
    match decode_name(&name.to_canonical_bytes(), DecodeBudget::unlimited()) {
        DecodeOutcome::Complete(Ok(value)) => value,
        other => panic!("primary-produced name did not decode: {other:?}"),
    }
}

fn checker_local_candidate(index: u64) -> (Name, WireName) {
    let name = Name::num(primary_name("_fln_checker_local"), index);
    let wire = checker_name_value(&name);
    (name, wire)
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
    definition_with_body(
        name,
        type_,
        decoded(&Expr::lit(Literal::Nat(NatLit::from_u64(0)))),
        safety,
        body_safety,
        0,
    )
}

fn definition_with_body(
    name: &str,
    type_: WireExpr,
    body: WireExpr,
    safety: ConstantSafety,
    body_safety: DefinitionSafety,
    height: u32,
) -> ConstantEntry {
    ConstantEntry::new(
        checker_name(name),
        ConstantDeclaration::definition(
            Vec::new(),
            type_,
            safety,
            DefinitionBody::new(
                body,
                ReducibilityHint::Regular(height),
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
fn forall_telescope_infers_dependent_imax_in_both_modes_and_ignores_binder_style() {
    let universe_name = primary_name("u");
    let universe = Level::param(universe_name.clone());
    let expected = LevelModel::IMax(
        Box::new(LevelModel::Succ(Box::new(LevelModel::Parameter(
            checker_name("u"),
        )))),
        Box::new(LevelModel::IMax(
            Box::new(LevelModel::Parameter(checker_name("u"))),
            Box::new(LevelModel::Parameter(checker_name("u"))),
        )),
    );
    let context = built_context(Vec::new(), vec![checker_name("u")], Vec::new());
    let modes = [
        InferenceMode::InferOnly,
        InferenceMode::Checking {
            declaration_safety: ConstantSafety::Safe,
        },
    ];
    let styles = [
        BinderInfo::Default,
        BinderInfo::Implicit,
        BinderInfo::StrictImplicit,
        BinderInfo::InstImplicit,
    ];

    for style in styles {
        let forall = Expr::forall_e(
            primary_name("A"),
            Expr::sort(universe.clone()),
            Expr::forall_e(
                primary_name("x"),
                Expr::bvar(0).expect("outer Forall binder"),
                Expr::bvar(1).expect("outer Forall binder under x"),
                style,
            ),
            style,
        );
        for mode in modes {
            let result = complete(infer(
                &decoded(&forall),
                &context,
                mode,
                InferenceBudget::unlimited(),
            ));
            assert_eq!(sort_model(&result.type_), expected);
            assert_eq!(result.progress.forall_telescope_nodes, 2);
            assert_eq!(result.progress.forall_binders, 2);
            assert_eq!(result.progress.forall_domain_queries, 2);
            assert_eq!(result.progress.forall_body_queries, 1);
            assert_eq!(result.progress.forall_sort_checks, 3);
            assert_eq!(result.progress.forall_imax_nodes, 2);
            assert_eq!(result.progress.lambda_binders, 0);
        }
    }
}

#[test]
fn forall_prop_impredicativity_uses_the_checker_universe_relation() {
    let prop = Expr::sort(Level::zero());
    let forall = Expr::forall_e(
        primary_name("p"),
        prop.clone(),
        Expr::bvar(0).expect("Forall proposition binder"),
        BinderInfo::Default,
    );
    let result = complete(infer(
        &decoded(&forall),
        &InferenceContext::empty(ConstantEnvironment::empty()),
        InferenceMode::InferOnly,
        InferenceBudget::unlimited(),
    ));
    assert_eq!(
        sort_model(&result.type_),
        LevelModel::IMax(
            Box::new(LevelModel::Succ(Box::new(LevelModel::Zero))),
            Box::new(LevelModel::Zero),
        )
    );
    assert!(matches!(
        def_eq(
            &result.type_,
            &decoded(&prop),
            &WhnfContext::default(),
            DefEqBudget::unlimited(),
        ),
        DefEqOutcome::Equal(_)
    ));
}

#[test]
fn forall_domain_and_codomain_sort_validation_is_mode_exact_and_reducible() {
    let prop = Expr::sort(Level::zero());
    let type_one = Expr::sort(Level::one());
    let a = Expr::fvar(FVarId(primary_name("A")));
    let datum = Expr::fvar(FVarId(primary_name("datum")));
    let context = built_context(
        vec![
            LocalDeclaration::assumption(checker_name("A"), decoded(&prop)),
            LocalDeclaration::assumption(checker_name("datum"), decoded(&a)),
        ],
        Vec::new(),
        Vec::new(),
    );
    let bad_domain = Expr::forall_e(
        primary_name("x"),
        datum.clone(),
        a.clone(),
        BinderInfo::Default,
    );
    let bad_codomain = Expr::forall_e(primary_name("x"), a, datum, BinderInfo::Default);
    let modes = [
        InferenceMode::InferOnly,
        InferenceMode::Checking {
            declaration_safety: ConstantSafety::Safe,
        },
    ];
    for mode in modes {
        assert!(matches!(
            infer(
                &decoded(&bad_domain),
                &context,
                mode,
                InferenceBudget::unlimited(),
            ),
            InferenceOutcome::Refused {
                refusal: InferenceRefusal::SortExpected {
                    site: InferenceSortSite::ForallBinder { binder: 0 },
                },
                ..
            }
        ));
        assert!(matches!(
            infer(
                &decoded(&bad_codomain),
                &context,
                mode,
                InferenceBudget::unlimited(),
            ),
            InferenceOutcome::Refused {
                refusal: InferenceRefusal::SortExpected {
                    site: InferenceSortSite::ForallCodomain { binders: 1 },
                },
                ..
            }
        ));
    }

    let sort_alias = Expr::const_(primary_name("SortAlias"), Vec::new());
    let domain = Expr::const_(primary_name("T"), Vec::new());
    let codomain = Expr::const_(primary_name("U"), Vec::new());
    let reducible_context = built_context(
        Vec::new(),
        Vec::new(),
        vec![
            definition_with_body(
                "SortAlias",
                decoded(&type_one),
                decoded(&prop),
                ConstantSafety::Safe,
                DefinitionSafety::Safe,
                0,
            ),
            header(
                "T",
                Vec::new(),
                decoded(&sort_alias),
                ConstantKind::Axiom,
                ConstantSafety::Safe,
            ),
            header(
                "U",
                Vec::new(),
                decoded(&sort_alias),
                ConstantKind::Axiom,
                ConstantSafety::Safe,
            ),
        ],
    );
    let reducible = Expr::forall_e(primary_name("x"), domain, codomain, BinderInfo::Default);
    let result = complete(infer(
        &decoded(&reducible),
        &reducible_context,
        InferenceMode::Checking {
            declaration_safety: ConstantSafety::Safe,
        },
        InferenceBudget::unlimited(),
    ));
    assert_eq!(
        sort_model(&result.type_),
        LevelModel::IMax(Box::new(LevelModel::Zero), Box::new(LevelModel::Zero))
    );
    assert_eq!(result.progress.forall_sort_checks, 2);
    assert_eq!(result.progress.whnf_queries, 2);
}

#[test]
fn forall_locals_avoid_context_and_constant_free_names_with_repeated_display_names() {
    let (candidate_zero, candidate_zero_wire) = checker_local_candidate(0);
    let (candidate_one, _) = checker_local_candidate(1);
    let prop = Expr::sort(Level::zero());
    let type_one = Expr::sort(Level::one());
    let context = built_context(
        vec![LocalDeclaration::assumption(
            candidate_zero_wire,
            decoded(&prop),
        )],
        Vec::new(),
        vec![header(
            "CarriesFreeName",
            Vec::new(),
            decoded(&Expr::fvar(FVarId(candidate_one))),
            ConstantKind::Axiom,
            ConstantSafety::Safe,
        )],
    );
    let repeated = primary_name("same");
    let forall = Expr::forall_e(
        repeated.clone(),
        type_one,
        Expr::forall_e(
            repeated,
            Expr::bvar(0).expect("outer repeated-name Forall binder"),
            Expr::bvar(1).expect("outer repeated-name binder below inner Forall"),
            BinderInfo::Implicit,
        ),
        BinderInfo::Default,
    );
    let result = complete(infer(
        &decoded(&forall),
        &context,
        InferenceMode::InferOnly,
        InferenceBudget::unlimited(),
    ));
    assert_eq!(
        sort_model(&result.type_),
        LevelModel::IMax(
            Box::new(LevelModel::Succ(Box::new(LevelModel::Succ(Box::new(
                LevelModel::Zero,
            ))))),
            Box::new(LevelModel::IMax(
                Box::new(LevelModel::Succ(Box::new(LevelModel::Zero))),
                Box::new(LevelModel::Succ(Box::new(LevelModel::Zero))),
            )),
        )
    );
    assert!(result.progress.local_identity_candidates >= 4);
    assert_eq!(result.progress.forall_binders, 2);
}

#[test]
fn forall_composes_inside_lambda_and_application_continuations() {
    let prop = Expr::sort(Level::zero());
    let proposition = Expr::forall_e(
        primary_name("p"),
        prop.clone(),
        Expr::bvar(0).expect("proposition Forall binder"),
        BinderInfo::Default,
    );
    let identity = Expr::lam(
        primary_name("Q"),
        prop.clone(),
        Expr::bvar(0).expect("proposition identity binder"),
        BinderInfo::Default,
    );
    let nested = Expr::lam(
        primary_name("unused"),
        prop.clone(),
        Expr::app(identity, proposition),
        BinderInfo::Implicit,
    );
    let result = complete(infer(
        &decoded(&nested),
        &InferenceContext::empty(ConstantEnvironment::empty()),
        InferenceMode::Checking {
            declaration_safety: ConstantSafety::Safe,
        },
        InferenceBudget::unlimited(),
    ));
    assert_eq!(
        result.type_,
        decoded(&Expr::forall_e(
            primary_name("unused"),
            prop.clone(),
            prop,
            BinderInfo::Implicit,
        ))
    );
    assert_eq!(result.progress.forall_binders, 1);
    assert_eq!(result.progress.lambda_binders, 2);
    assert_eq!(result.progress.application_arguments, 1);
    assert_eq!(result.progress.defeq_queries, 1);
}

#[test]
fn lambda_telescope_infers_dependent_types_and_preserves_every_binder_style() {
    let sort_zero = Expr::sort(Level::zero());
    let sort_one = Expr::sort(Level::one());
    let styles = [
        BinderInfo::Default,
        BinderInfo::Implicit,
        BinderInfo::StrictImplicit,
        BinderInfo::InstImplicit,
    ];
    for style in styles {
        let lambda = Expr::lam(
            primary_name("A"),
            sort_one.clone(),
            Expr::lam(
                primary_name("x"),
                Expr::bvar(0).expect("outer lambda binder"),
                Expr::bvar(0).expect("inner lambda binder"),
                style,
            ),
            style,
        );
        let expected = Expr::forall_e(
            primary_name("A"),
            sort_one.clone(),
            Expr::forall_e(
                primary_name("x"),
                Expr::bvar(0).expect("outer forall binder"),
                Expr::bvar(1).expect("outer binder below inner forall"),
                style,
            ),
            style,
        );
        for mode in [
            InferenceMode::InferOnly,
            InferenceMode::Checking {
                declaration_safety: ConstantSafety::Safe,
            },
        ] {
            let checking = matches!(mode, InferenceMode::Checking { .. });
            let result = complete(infer(
                &decoded(&lambda),
                &InferenceContext::empty(ConstantEnvironment::empty()),
                mode,
                InferenceBudget::unlimited(),
            ));
            assert_eq!(result.type_, decoded(&expected));
            assert_eq!(result.progress.lambda_binders, 2);
            assert_eq!(result.progress.lambda_body_queries, 1);
            assert_eq!(
                result.progress.lambda_domain_queries,
                u64::from(checking) * 2
            );
            assert_eq!(result.progress.binder_sort_checks, u64::from(checking) * 2);
        }
    }

    let nondependent = Expr::lam(
        primary_name("x"),
        sort_zero.clone(),
        sort_zero.clone(),
        BinderInfo::Default,
    );
    let expected = Expr::forall_e(
        primary_name("x"),
        sort_zero.clone(),
        Expr::sort(Level::one()),
        BinderInfo::Default,
    );
    assert_eq!(
        complete(infer(
            &decoded(&nondependent),
            &InferenceContext::empty(ConstantEnvironment::empty()),
            InferenceMode::InferOnly,
            InferenceBudget::unlimited(),
        ))
        .type_,
        decoded(&expected)
    );
}

#[test]
fn lambda_locals_avoid_context_and_constant_free_names_with_repeated_display_names() {
    let (candidate_zero, candidate_zero_wire) = checker_local_candidate(0);
    let (candidate_one, _) = checker_local_candidate(1);
    let sort_zero = Expr::sort(Level::zero());
    let sort_one = Expr::sort(Level::one());
    let context = built_context(
        vec![LocalDeclaration::assumption(
            candidate_zero_wire,
            decoded(&sort_zero),
        )],
        Vec::new(),
        vec![header(
            "CarriesFreeName",
            Vec::new(),
            decoded(&Expr::fvar(FVarId(candidate_one))),
            ConstantKind::Axiom,
            ConstantSafety::Safe,
        )],
    );
    let repeated = primary_name("same");
    let lambda = Expr::lam(
        repeated.clone(),
        sort_one.clone(),
        Expr::lam(
            repeated.clone(),
            Expr::bvar(0).expect("outer repeated-name binder"),
            Expr::bvar(0).expect("inner repeated-name binder"),
            BinderInfo::Implicit,
        ),
        BinderInfo::Default,
    );
    let expected = Expr::forall_e(
        repeated.clone(),
        sort_one,
        Expr::forall_e(
            repeated,
            Expr::bvar(0).expect("outer repeated-name forall"),
            Expr::bvar(1).expect("outer repeated-name body type"),
            BinderInfo::Implicit,
        ),
        BinderInfo::Default,
    );
    let result = complete(infer(
        &decoded(&lambda),
        &context,
        InferenceMode::InferOnly,
        InferenceBudget::unlimited(),
    ));
    assert_eq!(result.type_, decoded(&expected));
    assert_eq!(
        result.progress.local_identity_candidates, 4,
        "two adversarially reserved candidates must be skipped before allocating two locals"
    );
    assert_eq!(result.progress.lambda_binders, 2);
    assert_ne!(candidate_zero, primary_name("same"));
}

#[test]
fn lambda_domain_validation_is_mode_exact_and_uses_checker_whnf() {
    let sort_zero = Expr::sort(Level::zero());
    let sort_one = Expr::sort(Level::one());
    let missing = Expr::fvar(FVarId(primary_name("missingDomain")));
    let missing_lambda = Expr::lam(
        primary_name("x"),
        missing.clone(),
        Expr::bvar(0).expect("missing-domain binder"),
        BinderInfo::Default,
    );
    let empty = InferenceContext::empty(ConstantEnvironment::empty());
    assert!(matches!(
        infer(
            &decoded(&missing_lambda),
            &empty,
            InferenceMode::Checking {
                declaration_safety: ConstantSafety::Safe,
            },
            InferenceBudget::unlimited(),
        ),
        InferenceOutcome::Refused {
            refusal: InferenceRefusal::UnknownFreeVariable { name },
            ..
        } if name == checker_name("missingDomain")
    ));
    let skipped = complete(infer(
        &decoded(&missing_lambda),
        &empty,
        InferenceMode::InferOnly,
        InferenceBudget::unlimited(),
    ));
    assert_eq!(
        skipped.type_,
        decoded(&Expr::forall_e(
            primary_name("x"),
            missing.clone(),
            missing,
            BinderInfo::Default,
        ))
    );
    assert_eq!(skipped.progress.lambda_domain_queries, 0);
    assert_eq!(skipped.progress.binder_sort_checks, 0);

    let a = Expr::fvar(FVarId(primary_name("A")));
    let datum = Expr::fvar(FVarId(primary_name("datum")));
    let invalid_context = built_context(
        vec![
            LocalDeclaration::assumption(checker_name("A"), decoded(&sort_zero)),
            LocalDeclaration::assumption(checker_name("datum"), decoded(&a)),
        ],
        Vec::new(),
        Vec::new(),
    );
    let invalid = Expr::lam(
        primary_name("x"),
        datum,
        Expr::bvar(0).expect("invalid-domain binder"),
        BinderInfo::Default,
    );
    assert!(matches!(
        infer(
            &decoded(&invalid),
            &invalid_context,
            InferenceMode::Checking {
                declaration_safety: ConstantSafety::Safe,
            },
            InferenceBudget::unlimited(),
        ),
        InferenceOutcome::Refused {
            refusal: InferenceRefusal::SortExpected {
                site: InferenceSortSite::LambdaBinder { binder: 0 },
            },
            ..
        }
    ));

    let sort_alias = Expr::const_(primary_name("SortAlias"), Vec::new());
    let type_constant = Expr::const_(primary_name("T"), Vec::new());
    let reducible_context = built_context(
        Vec::new(),
        Vec::new(),
        vec![
            definition_with_body(
                "SortAlias",
                decoded(&sort_one),
                decoded(&sort_zero),
                ConstantSafety::Safe,
                DefinitionSafety::Safe,
                0,
            ),
            header(
                "T",
                Vec::new(),
                decoded(&sort_alias),
                ConstantKind::Axiom,
                ConstantSafety::Safe,
            ),
        ],
    );
    let reducible = Expr::lam(
        primary_name("x"),
        type_constant.clone(),
        Expr::bvar(0).expect("reducible-domain binder"),
        BinderInfo::Default,
    );
    let reduced = complete(infer(
        &decoded(&reducible),
        &reducible_context,
        InferenceMode::Checking {
            declaration_safety: ConstantSafety::Safe,
        },
        InferenceBudget::unlimited(),
    ));
    assert_eq!(
        reduced.type_,
        decoded(&Expr::forall_e(
            primary_name("x"),
            type_constant.clone(),
            type_constant,
            BinderInfo::Default,
        ))
    );
    assert_eq!(reduced.progress.binder_sort_checks, 1);

    let structure_name = primary_name("OverflowStructure");
    let constructor_name = primary_name("OverflowConstructor");
    let overflow_type = Expr::proj(
        structure_name.clone(),
        u64::MAX,
        Expr::app(
            Expr::const_(constructor_name.clone(), Vec::new()),
            sort_zero.clone(),
        ),
    );
    let overflow_context = InferenceContext::new_with_projection_rules(
        Vec::new(),
        Vec::new(),
        vec![ProjectionRule::new(
            checker_name_value(&structure_name),
            checker_name_value(&constructor_name),
            usize::MAX,
        )],
        environment(vec![header(
            "OverflowType",
            Vec::new(),
            decoded(&overflow_type),
            ConstantKind::Axiom,
            ConstantSafety::Safe,
        )]),
    )
    .expect("unique overflow projection context");
    let overflow = Expr::lam(
        primary_name("x"),
        Expr::const_(primary_name("OverflowType"), Vec::new()),
        Expr::bvar(0).expect("overflow-domain binder"),
        BinderInfo::Default,
    );
    assert!(matches!(
        infer(
            &decoded(&overflow),
            &overflow_context,
            InferenceMode::Checking {
                declaration_safety: ConstantSafety::Safe,
            },
            InferenceBudget::unlimited(),
        ),
        InferenceOutcome::Refused {
            refusal: InferenceRefusal::SortReductionRefusal {
                site: InferenceSortSite::LambdaBinder { binder: 0 },
                refusal: fln_checker::whnf::WhnfRefusal::ProjectionIndexOverflow { .. },
            },
            ..
        }
    ));
}

#[test]
fn lambda_cheap_head_beta_fires_only_for_the_two_exact_safe_shapes() {
    let sort_zero = Expr::sort(Level::zero());
    let sort_one = Expr::sort(Level::one());
    let f = Expr::fvar(FVarId(primary_name("f")));
    let a = Expr::fvar(FVarId(primary_name("A")));
    let function_type = Expr::forall_e(
        Name::anonymous(),
        sort_one.clone(),
        sort_one.clone(),
        BinderInfo::Default,
    );
    let direct_binder = Expr::app(
        Expr::lam(
            primary_name("z"),
            sort_one.clone(),
            Expr::bvar(0).expect("cheap-beta direct binder"),
            BinderInfo::Default,
        ),
        sort_zero.clone(),
    );
    let closed_residual = Expr::app(
        Expr::lam(
            primary_name("z"),
            sort_one.clone(),
            sort_zero.clone(),
            BinderInfo::Default,
        ),
        sort_one.clone(),
    );
    let over_applied = Expr::app(
        Expr::app(
            Expr::lam(
                primary_name("h"),
                function_type.clone(),
                Expr::bvar(0).expect("cheap-beta function binder"),
                BinderInfo::Default,
            ),
            f.clone(),
        ),
        a.clone(),
    );
    let complex_residual = Expr::app(
        Expr::lam(
            primary_name("z"),
            sort_one.clone(),
            Expr::app(f.clone(), Expr::bvar(0).expect("complex residual binder")),
            BinderInfo::Default,
        ),
        a.clone(),
    );
    let non_lambda_head = Expr::app(f.clone(), a.clone());
    let cases = [
        ("direct binder", direct_binder, sort_zero.clone()),
        ("closed residual", closed_residual, sort_zero.clone()),
        (
            "over application",
            over_applied,
            Expr::app(f.clone(), a.clone()),
        ),
        (
            "complex loose residual",
            complex_residual.clone(),
            complex_residual,
        ),
        ("non-lambda head", non_lambda_head.clone(), non_lambda_head),
    ];

    for (label, body_type, expected_body_type) in cases {
        let context = built_context(
            vec![
                LocalDeclaration::assumption(checker_name("y"), decoded(&body_type)),
                LocalDeclaration::assumption(checker_name("f"), decoded(&function_type)),
                LocalDeclaration::assumption(checker_name("A"), decoded(&sort_one)),
            ],
            Vec::new(),
            Vec::new(),
        );
        let lambda = Expr::lam(
            primary_name("outer"),
            sort_zero.clone(),
            Expr::fvar(FVarId(primary_name("y"))),
            BinderInfo::Default,
        );
        let result = complete(infer(
            &decoded(&lambda),
            &context,
            InferenceMode::InferOnly,
            InferenceBudget::unlimited(),
        ));
        assert_eq!(
            result.type_,
            decoded(&Expr::forall_e(
                primary_name("outer"),
                sort_zero.clone(),
                expected_body_type,
                BinderInfo::Default,
            )),
            "cheap-beta result drifted for {label}"
        );
        assert!(result.progress.cheap_beta_steps > 0);
    }
}

#[test]
fn lambda_heads_compose_with_nested_application_continuations() {
    let sort_zero = Expr::sort(Level::zero());
    let sort_one = Expr::sort(Level::one());
    let identity = Expr::lam(
        primary_name("A"),
        sort_one.clone(),
        Expr::lam(
            primary_name("x"),
            Expr::bvar(0).expect("application outer lambda binder"),
            Expr::bvar(0).expect("application inner lambda binder"),
            BinderInfo::Default,
        ),
        BinderInfo::Implicit,
    );
    let application = Expr::app(
        Expr::app(identity, sort_zero.clone()),
        Expr::fvar(FVarId(primary_name("proof"))),
    );
    let context = built_context(
        vec![LocalDeclaration::assumption(
            checker_name("proof"),
            decoded(&sort_zero),
        )],
        Vec::new(),
        Vec::new(),
    );
    let result = complete(infer(
        &decoded(&application),
        &context,
        InferenceMode::Checking {
            declaration_safety: ConstantSafety::Safe,
        },
        InferenceBudget::unlimited(),
    ));
    assert_eq!(sort_model(&result.type_), LevelModel::Zero);
    assert_eq!(result.progress.lambda_binders, 2);
    assert_eq!(result.progress.application_arguments, 2);
    assert_eq!(result.progress.defeq_queries, 2);
}

#[test]
fn lambda_resources_cancellation_and_recovery_remain_typed_and_failure_atomic() {
    let sort_zero = Expr::sort(Level::zero());
    let sort_one = Expr::sort(Level::one());
    let body_type = Expr::app(
        Expr::lam(
            primary_name("z"),
            sort_one.clone(),
            Expr::bvar(0).expect("resource cheap-beta binder"),
            BinderInfo::Default,
        ),
        sort_zero.clone(),
    );
    let context = built_context(
        vec![LocalDeclaration::assumption(
            checker_name("body"),
            decoded(&body_type),
        )],
        Vec::new(),
        Vec::new(),
    );
    let lambda = decoded(&Expr::lam(
        primary_name("A"),
        sort_one,
        Expr::lam(
            primary_name("x"),
            Expr::bvar(0).expect("resource outer binder"),
            Expr::fvar(FVarId(primary_name("body"))),
            BinderInfo::Implicit,
        ),
        BinderInfo::Default,
    ));
    let mode = InferenceMode::Checking {
        declaration_safety: ConstantSafety::Safe,
    };
    let baseline = complete(infer(&lambda, &context, mode, InferenceBudget::unlimited()));
    let exact_steps = baseline.progress.steps;
    assert!(exact_steps > 1);
    assert!(matches!(
        infer(
            &lambda,
            &context,
            mode,
            InferenceBudget::new(
                exact_steps - 1,
                u64::MAX,
                TermBudget::unlimited(),
                TermBudget::unlimited(),
            ),
        ),
        InferenceOutcome::Inconclusive(InferenceStop::Resource {
            limit: InferenceLimit::Steps,
            allowed,
            observed,
            phase: InferencePhase::CheapBeta | InferencePhase::LambdaBody,
            ..
        }) if observed == allowed + 1 && observed == exact_steps
    ));
    assert_eq!(
        complete(infer(
            &lambda,
            &context,
            mode,
            InferenceBudget::new(
                exact_steps,
                u64::MAX,
                TermBudget::unlimited(),
                TermBudget::unlimited(),
            ),
        ))
        .type_,
        baseline.type_
    );

    let mut materialization_limited = InferenceBudget::unlimited();
    materialization_limited.materialization =
        TermBudget::new(0, u64::MAX).with_max_arena_nodes(u64::MAX);
    assert!(matches!(
        infer(&lambda, &context, mode, materialization_limited,),
        InferenceOutcome::Inconclusive(InferenceStop::Materialization {
            phase: InferencePhase::LambdaDomain,
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
            &lambda,
            &context,
            mode,
            InferenceBudget::unlimited().with_whnf(WhnfBudget::new(
                0,
                u64::MAX,
                TermBudget::unlimited(),
            )),
        ),
        InferenceOutcome::Inconclusive(InferenceStop::SortWhnf {
            site: InferenceSortSite::LambdaBinder { binder: 0 },
            stop,
            ..
        }) if matches!(
            *stop,
            WhnfStop::Resource {
                allowed: 0,
                observed: 1,
                ..
            }
        )
    ));

    let mut saw_local_identity = false;
    let mut saw_telescope = false;
    let mut saw_domain = false;
    let mut saw_binder_sort = false;
    let mut saw_body = false;
    let mut saw_cheap_beta = false;
    let mut saw_nested_inspection = false;
    let mut saw_nested_binder_whnf = false;
    let mut saw_pi_materialization = false;
    let mut completed = false;
    for cancellation_poll in 1..2048 {
        let mut polls = 0usize;
        let outcome = infer_with(
            &lambda,
            &context,
            mode,
            InferenceBudget::unlimited(),
            || {
                polls = polls.saturating_add(1);
                polls == cancellation_poll
            },
        );
        match outcome {
            InferenceOutcome::Inconclusive(InferenceStop::Cancelled { phase, .. }) => match phase {
                InferencePhase::LocalIdentity => saw_local_identity = true,
                InferencePhase::LambdaTelescope => saw_telescope = true,
                InferencePhase::LambdaDomain => saw_domain = true,
                InferencePhase::BinderSort => saw_binder_sort = true,
                InferencePhase::LambdaBody => saw_body = true,
                InferencePhase::CheapBeta => saw_cheap_beta = true,
                _ => {}
            },
            InferenceOutcome::Inconclusive(InferenceStop::Inspection {
                stop: TermStop::Cancelled { .. },
                ..
            }) => saw_nested_inspection = true,
            InferenceOutcome::Inconclusive(InferenceStop::SortWhnf {
                site: InferenceSortSite::LambdaBinder { .. },
                stop,
                ..
            }) if matches!(*stop, WhnfStop::Cancelled { .. }) => {
                saw_nested_binder_whnf = true;
            }
            InferenceOutcome::Inconclusive(InferenceStop::Materialization {
                phase: InferencePhase::PiAbstraction,
                stop: TermStop::Cancelled { .. },
                ..
            }) => saw_pi_materialization = true,
            InferenceOutcome::Inconclusive(_) => {}
            InferenceOutcome::Complete(result) => {
                assert_eq!(result.type_, baseline.type_);
                completed = true;
                break;
            }
            other => panic!("lambda cancellation became a semantic answer: {other:?}"),
        }
    }
    assert!(completed);
    assert!(saw_local_identity);
    assert!(saw_telescope);
    assert!(saw_domain);
    assert!(saw_binder_sort);
    assert!(saw_body);
    assert!(saw_cheap_beta);
    assert!(saw_nested_inspection);
    assert!(saw_nested_binder_whnf);
    assert!(saw_pi_materialization);
    assert_eq!(
        complete(infer(&lambda, &context, mode, InferenceBudget::unlimited(),)).type_,
        baseline.type_
    );
}

#[test]
fn application_checking_instantiates_dependent_and_nondependent_codomains() {
    let sort_zero = Expr::sort(Level::zero());
    let sort_one = Expr::sort(Level::one());
    let type_term = Expr::fvar(FVarId(primary_name("A")));
    let value_term = Expr::fvar(FVarId(primary_name("x")));
    let dependent_type = Expr::forall_e(
        primary_name("A"),
        sort_one.clone(),
        Expr::forall_e(
            primary_name("x"),
            Expr::bvar(0).expect("outer binder"),
            Expr::bvar(1).expect("outer binder below inner binder"),
            BinderInfo::Default,
        ),
        BinderInfo::Implicit,
    );
    let nondependent_type = Expr::forall_e(
        Name::anonymous(),
        sort_zero.clone(),
        sort_one.clone(),
        BinderInfo::Default,
    );
    let context = built_context(
        vec![
            LocalDeclaration::assumption(checker_name("A"), decoded(&sort_one)),
            LocalDeclaration::assumption(checker_name("x"), decoded(&type_term)),
            LocalDeclaration::assumption(checker_name("p"), decoded(&sort_zero)),
            LocalDeclaration::assumption(checker_name("dependent"), decoded(&dependent_type)),
            LocalDeclaration::assumption(checker_name("nondependent"), decoded(&nondependent_type)),
        ],
        Vec::new(),
        Vec::new(),
    );
    let mode = InferenceMode::Checking {
        declaration_safety: ConstantSafety::Safe,
    };

    let dependent_application = decoded(&Expr::app(
        Expr::app(
            Expr::fvar(FVarId(primary_name("dependent"))),
            type_term.clone(),
        ),
        value_term,
    ));
    let dependent = complete(infer(
        &dependent_application,
        &context,
        mode,
        InferenceBudget::unlimited(),
    ));
    assert_eq!(dependent.type_, decoded(&type_term));
    assert_eq!(dependent.progress.application_spine_nodes, 2);
    assert_eq!(dependent.progress.application_arguments, 2);
    assert_eq!(dependent.progress.defeq_queries, 2);

    let nondependent = complete(infer(
        &decoded(&Expr::app(
            Expr::fvar(FVarId(primary_name("nondependent"))),
            Expr::fvar(FVarId(primary_name("p"))),
        )),
        &context,
        mode,
        InferenceBudget::unlimited(),
    ));
    assert_eq!(
        sort_model(&nondependent.type_),
        LevelModel::Succ(Box::new(LevelModel::Zero))
    );
}

#[test]
fn infer_only_peels_the_spine_without_inferring_or_converting_arguments() {
    let sort_one = Expr::sort(Level::one());
    let dependent_type = Expr::forall_e(
        primary_name("A"),
        sort_one,
        Expr::forall_e(
            primary_name("x"),
            Expr::bvar(0).expect("outer binder"),
            Expr::bvar(1).expect("outer binder below inner binder"),
            BinderInfo::Default,
        ),
        BinderInfo::Implicit,
    );
    let context = built_context(
        vec![LocalDeclaration::assumption(
            checker_name("dependent"),
            decoded(&dependent_type),
        )],
        Vec::new(),
        Vec::new(),
    );
    let skipped_meta = Expr::mvar(MVarId(primary_name("skippedType")));
    let application = decoded(&Expr::app(
        Expr::app(
            Expr::fvar(FVarId(primary_name("dependent"))),
            skipped_meta.clone(),
        ),
        Expr::fvar(FVarId(primary_name("missingArgument"))),
    ));

    let result = complete(infer(
        &application,
        &context,
        InferenceMode::InferOnly,
        InferenceBudget::unlimited(),
    ));
    assert_eq!(result.type_, decoded(&skipped_meta));
    assert_eq!(result.progress.application_arguments, 2);
    assert_eq!(result.progress.defeq_queries, 0);
    assert_eq!(result.progress.whnf_queries, 0);
    assert!(matches!(
        infer(
            &application,
            &context,
            InferenceMode::Checking {
                declaration_safety: ConstantSafety::Safe,
            },
            InferenceBudget::unlimited(),
        ),
        InferenceOutcome::Refused {
            refusal: InferenceRefusal::ExpressionMetavariable,
            ..
        }
    ));
}

#[test]
fn application_outcomes_separate_function_mismatch_conversion_and_nested_rules() {
    let sort_zero = Expr::sort(Level::zero());
    let sort_one = Expr::sort(Level::one());
    let mode = InferenceMode::Checking {
        declaration_safety: ConstantSafety::Safe,
    };

    let nonfunction_context = built_context(
        vec![LocalDeclaration::assumption(
            checker_name("x"),
            decoded(&sort_zero),
        )],
        Vec::new(),
        Vec::new(),
    );
    assert!(matches!(
        infer(
            &decoded(&Expr::app(
                Expr::fvar(FVarId(primary_name("x"))),
                Expr::fvar(FVarId(primary_name("x"))),
            )),
            &nonfunction_context,
            mode,
            InferenceBudget::unlimited(),
        ),
        InferenceOutcome::Refused {
            refusal: InferenceRefusal::FunctionExpected { argument: 0 },
            ..
        }
    ));
    assert!(matches!(
        infer(
            &decoded(&Expr::app(
                Expr::fvar(FVarId(primary_name("x"))),
                Expr::fvar(FVarId(primary_name("x"))),
            )),
            &nonfunction_context,
            InferenceMode::InferOnly,
            InferenceBudget::unlimited(),
        ),
        InferenceOutcome::Refused {
            refusal: InferenceRefusal::FunctionExpected { argument: 0 },
            ..
        }
    ));

    let function_type = Expr::forall_e(
        Name::anonymous(),
        sort_zero.clone(),
        sort_zero.clone(),
        BinderInfo::Default,
    );
    let mismatch_context = built_context(
        vec![
            LocalDeclaration::assumption(checker_name("f"), decoded(&function_type)),
            LocalDeclaration::assumption(checker_name("A"), decoded(&sort_one)),
        ],
        Vec::new(),
        Vec::new(),
    );
    assert!(matches!(
        infer(
            &decoded(&Expr::app(
                Expr::fvar(FVarId(primary_name("f"))),
                Expr::fvar(FVarId(primary_name("A"))),
            )),
            &mismatch_context,
            mode,
            InferenceBudget::unlimited(),
        ),
        InferenceOutcome::Refused {
            refusal: InferenceRefusal::ApplicationTypeMismatch { argument: 0, .. },
            ..
        }
    ));

    let expected = Expr::fvar(FVarId(primary_name("Expected")));
    let actual = Expr::fvar(FVarId(primary_name("Actual")));
    let deferred_function_type = Expr::forall_e(
        Name::anonymous(),
        expected.clone(),
        expected,
        BinderInfo::Default,
    );
    let deferred_context = built_context(
        vec![
            LocalDeclaration::assumption(checker_name("Expected"), decoded(&sort_zero)),
            LocalDeclaration::assumption(checker_name("Actual"), decoded(&sort_zero)),
            LocalDeclaration::assumption(checker_name("value"), decoded(&actual)),
            LocalDeclaration::assumption(
                checker_name("deferredFunction"),
                decoded(&deferred_function_type),
            ),
        ],
        Vec::new(),
        Vec::new(),
    );
    assert!(matches!(
        infer(
            &decoded(&Expr::app(
                Expr::fvar(FVarId(primary_name("deferredFunction"))),
                Expr::fvar(FVarId(primary_name("value"))),
            )),
            &deferred_context,
            mode,
            InferenceBudget::unlimited(),
        ),
        InferenceOutcome::Deferred {
            requirement: InferenceDeferred::ApplicationConversion { argument: 0, .. },
            ..
        }
    ));

    let nested_lambda = Expr::lam(
        Name::anonymous(),
        sort_zero.clone(),
        Expr::bvar(0).expect("lambda binder"),
        BinderInfo::Default,
    );
    let nested_outcome = infer(
        &decoded(&Expr::app(
            Expr::fvar(FVarId(primary_name("f"))),
            nested_lambda,
        )),
        &mismatch_context,
        mode,
        InferenceBudget::unlimited(),
    );
    assert!(
        matches!(
            nested_outcome,
            InferenceOutcome::Deferred {
                requirement: InferenceDeferred::ApplicationConversion { argument: 0, .. },
                ..
            }
        ),
        "nested lambda outcome drifted: {nested_outcome:?}"
    );
}

#[test]
fn application_whnf_uses_safe_definitions_shared_lets_and_validated_projections() {
    let sort_zero = Expr::sort(Level::zero());
    let sort_one = Expr::sort(Level::one());
    let function_type = Expr::forall_e(
        Name::anonymous(),
        sort_zero.clone(),
        sort_zero.clone(),
        BinderInfo::Default,
    );
    let mode = InferenceMode::Checking {
        declaration_safety: ConstantSafety::Safe,
    };
    let definition_context = built_context(
        vec![LocalDeclaration::assumption(
            checker_name("x"),
            decoded(&sort_zero),
        )],
        Vec::new(),
        vec![
            definition_with_body(
                "FunctionAlias",
                decoded(&sort_one),
                decoded(&function_type),
                ConstantSafety::Safe,
                DefinitionSafety::Safe,
                1,
            ),
            header(
                "aliasedFunction",
                Vec::new(),
                decoded(&Expr::const_(primary_name("FunctionAlias"), Vec::new())),
                ConstantKind::Axiom,
                ConstantSafety::Safe,
            ),
        ],
    );
    let definition_result = complete(infer(
        &decoded(&Expr::app(
            Expr::const_(primary_name("aliasedFunction"), Vec::new()),
            Expr::fvar(FVarId(primary_name("x"))),
        )),
        &definition_context,
        mode,
        InferenceBudget::unlimited(),
    ));
    assert_eq!(sort_model(&definition_result.type_), LevelModel::Zero);
    assert_eq!(definition_result.progress.whnf_queries, 1);

    let local_alias = Expr::fvar(FVarId(primary_name("LocalFunctionAlias")));
    let local_context = built_context(
        vec![
            LocalDeclaration::definition(
                checker_name("LocalFunctionAlias"),
                decoded(&sort_one),
                decoded(&function_type),
            ),
            LocalDeclaration::assumption(checker_name("localFunction"), decoded(&local_alias)),
            LocalDeclaration::assumption(checker_name("x"), decoded(&sort_zero)),
        ],
        Vec::new(),
        Vec::new(),
    );
    let local_result = complete(infer(
        &decoded(&Expr::app(
            Expr::fvar(FVarId(primary_name("localFunction"))),
            Expr::fvar(FVarId(primary_name("x"))),
        )),
        &local_context,
        mode,
        InferenceBudget::unlimited(),
    ));
    assert_eq!(sort_model(&local_result.type_), LevelModel::Zero);
    assert_eq!(local_result.progress.whnf_queries, 1);

    let local_infer_only = complete(infer(
        &decoded(&Expr::app(
            Expr::fvar(FVarId(primary_name("localFunction"))),
            Expr::mvar(MVarId(primary_name("skippedArgument"))),
        )),
        &local_context,
        InferenceMode::InferOnly,
        InferenceBudget::unlimited(),
    ));
    assert_eq!(sort_model(&local_infer_only.type_), LevelModel::Zero);
    assert_eq!(local_infer_only.progress.whnf_queries, 1);
    assert_eq!(local_infer_only.progress.defeq_queries, 0);

    let first = ProjectionRule::new(checker_name("S"), checker_name("MkS"), 0);
    let second = ProjectionRule::new(checker_name("S"), checker_name("OtherMkS"), 2);
    assert_eq!(
        InferenceContext::new_with_projection_rules(
            Vec::new(),
            Vec::new(),
            vec![first.clone(), second],
            ConstantEnvironment::empty(),
        ),
        Err(InferenceContextRefusal::DuplicateProjectionRule {
            structure_name: checker_name("S"),
            first: 0,
            second: 1,
        })
    );
    let recovered = InferenceContext::new_with_projection_rules(
        Vec::new(),
        Vec::new(),
        vec![first],
        ConstantEnvironment::empty(),
    )
    .expect("a unique projection context recovers after refusal");
    assert_eq!(recovered.projection_rules().len(), 1);
}

#[test]
fn eager_reduce_recognition_is_exact_and_query_local() {
    let sort_zero = Expr::sort(Level::zero());
    let sort_one = Expr::sort(Level::one());
    let type_term = Expr::fvar(FVarId(primary_name("A")));
    let identity_type = Expr::forall_e(
        primary_name("A"),
        sort_one.clone(),
        Expr::forall_e(
            primary_name("x"),
            Expr::bvar(0).expect("outer binder"),
            Expr::bvar(1).expect("outer binder below inner binder"),
            BinderInfo::Default,
        ),
        BinderInfo::Implicit,
    );
    let instantiated_identity_type = Expr::forall_e(
        primary_name("x"),
        type_term.clone(),
        type_term.clone(),
        BinderInfo::Default,
    );
    let accept_type = Expr::forall_e(
        primary_name("x"),
        type_term.clone(),
        type_term.clone(),
        BinderInfo::Default,
    );
    let accept_function_type = Expr::forall_e(
        primary_name("f"),
        instantiated_identity_type,
        sort_zero,
        BinderInfo::Default,
    );
    let context = built_context(
        vec![
            LocalDeclaration::assumption(checker_name("A"), decoded(&sort_one)),
            LocalDeclaration::assumption(checker_name("x"), decoded(&type_term)),
            LocalDeclaration::assumption(checker_name("accept"), decoded(&accept_type)),
            LocalDeclaration::assumption(
                checker_name("acceptFunction"),
                decoded(&accept_function_type),
            ),
        ],
        Vec::new(),
        vec![header(
            "eagerReduce",
            Vec::new(),
            decoded(&identity_type),
            ConstantKind::Axiom,
            ConstantSafety::Safe,
        )],
    );
    let mode = InferenceMode::Checking {
        declaration_safety: ConstantSafety::Safe,
    };
    let eager_argument = Expr::app(
        Expr::app(
            Expr::const_(primary_name("eagerReduce"), Vec::new()),
            type_term.clone(),
        ),
        Expr::fvar(FVarId(primary_name("x"))),
    );

    let eager = complete(infer(
        &decoded(&Expr::app(
            Expr::fvar(FVarId(primary_name("accept"))),
            eager_argument.clone(),
        )),
        &context,
        mode,
        InferenceBudget::unlimited(),
    ));
    assert_eq!(eager.progress.eager_argument_checks, 1);

    let next_plain_query = complete(infer(
        &decoded(&Expr::app(
            Expr::fvar(FVarId(primary_name("accept"))),
            Expr::fvar(FVarId(primary_name("x"))),
        )),
        &context,
        mode,
        InferenceBudget::unlimited(),
    ));
    assert_eq!(next_plain_query.progress.eager_argument_checks, 0);

    let one_argument_near_miss = complete(infer(
        &decoded(&Expr::app(
            Expr::fvar(FVarId(primary_name("acceptFunction"))),
            Expr::app(
                Expr::const_(primary_name("eagerReduce"), Vec::new()),
                type_term.clone(),
            ),
        )),
        &context,
        mode,
        InferenceBudget::unlimited(),
    ));
    assert_eq!(one_argument_near_miss.progress.eager_argument_checks, 0);

    let metadata_near_miss = complete(infer(
        &decoded(&Expr::app(
            Expr::fvar(FVarId(primary_name("accept"))),
            Expr::mdata(KVMap::new(), eager_argument),
        )),
        &context,
        mode,
        InferenceBudget::unlimited(),
    ));
    assert_eq!(metadata_near_miss.progress.eager_argument_checks, 0);
}

#[test]
fn nested_applications_use_heap_continuations() {
    let sort_zero = Expr::sort(Level::zero());
    let function_type = Expr::forall_e(
        Name::anonymous(),
        sort_zero.clone(),
        sort_zero.clone(),
        BinderInfo::Default,
    );
    let context = built_context(
        vec![
            LocalDeclaration::assumption(checker_name("f"), decoded(&function_type)),
            LocalDeclaration::assumption(checker_name("g"), decoded(&function_type)),
            LocalDeclaration::assumption(checker_name("x"), decoded(&sort_zero)),
        ],
        Vec::new(),
        Vec::new(),
    );
    let result = complete(infer(
        &decoded(&Expr::app(
            Expr::fvar(FVarId(primary_name("f"))),
            Expr::app(
                Expr::fvar(FVarId(primary_name("g"))),
                Expr::fvar(FVarId(primary_name("x"))),
            ),
        )),
        &context,
        InferenceMode::Checking {
            declaration_safety: ConstantSafety::Safe,
        },
        InferenceBudget::unlimited(),
    ));
    assert_eq!(sort_model(&result.type_), LevelModel::Zero);
    assert_eq!(result.progress.application_spine_nodes, 2);
    assert_eq!(result.progress.application_arguments, 2);
    assert_eq!(result.progress.defeq_queries, 2);
}

#[test]
fn application_nested_resources_and_cancellation_are_typed_and_recover_cleanly() {
    let sort_zero = Expr::sort(Level::zero());
    let sort_one = Expr::sort(Level::one());
    let function_type = Expr::forall_e(
        Name::anonymous(),
        sort_zero.clone(),
        sort_zero.clone(),
        BinderInfo::Default,
    );
    let alias = Expr::fvar(FVarId(primary_name("FunctionAlias")));
    let context = built_context(
        vec![
            LocalDeclaration::definition(
                checker_name("FunctionAlias"),
                decoded(&sort_one),
                decoded(&function_type),
            ),
            LocalDeclaration::assumption(checker_name("f"), decoded(&alias)),
            LocalDeclaration::assumption(checker_name("x"), decoded(&sort_zero)),
        ],
        Vec::new(),
        Vec::new(),
    );
    let application = decoded(&Expr::app(
        Expr::fvar(FVarId(primary_name("f"))),
        Expr::fvar(FVarId(primary_name("x"))),
    ));
    let mode = InferenceMode::Checking {
        declaration_safety: ConstantSafety::Safe,
    };
    let baseline = complete(infer(
        &application,
        &context,
        mode,
        InferenceBudget::unlimited(),
    ));

    assert!(matches!(
        infer(
            &application,
            &context,
            mode,
            InferenceBudget::new(
                u64::MAX,
                u64::MAX,
                TermBudget::unlimited(),
                TermBudget::new(0, u64::MAX),
            ),
        ),
        InferenceOutcome::Inconclusive(InferenceStop::Materialization {
            phase: InferencePhase::ApplicationTerm,
            stop: TermStop::Resource { .. },
            ..
        })
    ));

    let whnf_stop = infer(
        &application,
        &context,
        mode,
        InferenceBudget::unlimited().with_whnf(WhnfBudget::new(
            0,
            u64::MAX,
            TermBudget::unlimited(),
        )),
    );
    assert!(matches!(
        whnf_stop,
        InferenceOutcome::Inconclusive(InferenceStop::Whnf {
            argument: 0,
            stop,
            ..
        }) if matches!(stop.as_ref(), WhnfStop::Resource { .. })
    ));

    let defeq_stop = infer(
        &application,
        &context,
        mode,
        InferenceBudget::unlimited().with_defeq(DefEqBudget::new(
            QuickDefEqBudget::new(0, u64::MAX),
            u64::MAX,
            u64::MAX,
            u64::MAX,
            u64::MAX,
            WhnfBudget::unlimited(),
        )),
    );
    assert!(matches!(
        defeq_stop,
        InferenceOutcome::Inconclusive(InferenceStop::DefEq {
            argument: 0,
            stop,
            ..
        }) if matches!(
            stop.as_ref(),
            DefEqStop::Quick(QuickDefEqStop::Resource { .. })
        )
    ));

    let mut saw_application_phase = false;
    let mut saw_inspection = false;
    let mut saw_materialization = false;
    let mut saw_whnf = false;
    let mut saw_defeq = false;
    for cancellation_poll in 1..512 {
        let mut polls = 0usize;
        let outcome = infer_with(
            &application,
            &context,
            mode,
            InferenceBudget::unlimited(),
            || {
                polls += 1;
                polls == cancellation_poll
            },
        );
        match outcome {
            InferenceOutcome::Inconclusive(InferenceStop::Cancelled { phase, .. }) => {
                saw_application_phase |= matches!(
                    phase,
                    InferencePhase::ApplicationTerm
                        | InferencePhase::ApplicationSpine
                        | InferencePhase::FunctionType
                        | InferencePhase::ApplicationDomain
                        | InferencePhase::ArgumentType
                        | InferencePhase::DomainComparison
                        | InferencePhase::Codomain
                );
            }
            InferenceOutcome::Inconclusive(InferenceStop::Inspection {
                stop: TermStop::Cancelled { .. },
                ..
            }) => saw_inspection = true,
            InferenceOutcome::Inconclusive(InferenceStop::Materialization {
                stop: TermStop::Cancelled { .. },
                ..
            }) => saw_materialization = true,
            InferenceOutcome::Inconclusive(InferenceStop::Whnf { .. }) => saw_whnf = true,
            InferenceOutcome::Inconclusive(InferenceStop::DefEq { .. }) => saw_defeq = true,
            InferenceOutcome::Complete(result) => {
                assert_eq!(result.type_, baseline.type_);
                break;
            }
            other => panic!("application cancellation became a semantic answer: {other:?}"),
        }
    }
    assert!(saw_application_phase);
    assert!(saw_inspection);
    assert!(saw_materialization);
    assert!(saw_whnf);
    assert!(saw_defeq);
    assert_eq!(
        complete(infer(
            &application,
            &context,
            mode,
            InferenceBudget::unlimited(),
        ))
        .type_,
        baseline.type_
    );
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
                | InferencePhase::ConstantType
                | InferencePhase::ApplicationTerm
                | InferencePhase::ApplicationSpine
                | InferencePhase::FunctionType
                | InferencePhase::ApplicationDomain
                | InferencePhase::ArgumentType
                | InferencePhase::DomainComparison
                | InferencePhase::Codomain
                | InferencePhase::LocalIdentity
                | InferencePhase::LambdaTelescope
                | InferencePhase::LambdaDomain
                | InferencePhase::BinderSort
                | InferencePhase::LambdaBody
                | InferencePhase::CheapBeta
                | InferencePhase::PiAbstraction
                | InferencePhase::ForallTelescope
                | InferencePhase::ForallDomain
                | InferencePhase::ForallDomainSort
                | InferencePhase::ForallBody
                | InferencePhase::ForallCodomainSort
                | InferencePhase::ForallUniverse => {
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

fn deep_lambda_telescope_child() -> Result<(), String> {
    const BINDERS: usize = 50_000;
    let mut writer = CanonWriter::new();
    writer.schema(SCHEMA_EXPR);
    for _ in 0..BINDERS {
        writer.u8(6);
        writer.u64(0);
        writer.u8(3);
        writer.u8(0);
    }
    writer.u8(0);
    writer.u32(0);
    for _ in 0..BINDERS {
        writer.u8(0);
    }
    let term = match decode_expr(&writer.into_bytes(), DecodeBudget::unlimited()) {
        DecodeOutcome::Complete(Ok(value)) => value,
        other => return Err(format!("deep lambda bytes did not decode: {other:?}")),
    };
    let result = match infer(
        &term,
        &InferenceContext::empty(ConstantEnvironment::empty()),
        InferenceMode::InferOnly,
        InferenceBudget::unlimited(),
    ) {
        InferenceOutcome::Complete(result) => result,
        other => return Err(format!("deep lambda inference failed: {other:?}")),
    };
    if result.progress.lambda_binders != BINDERS as u64
        || result.progress.lambda_domain_queries != 0
        || result.progress.lambda_body_queries != 1
    {
        return Err(format!(
            "deep lambda progress drifted: binders={}, domains={}, bodies={}",
            result.progress.lambda_binders,
            result.progress.lambda_domain_queries,
            result.progress.lambda_body_queries
        ));
    }
    if result
        .type_
        .nodes()
        .iter()
        .any(|node| matches!(node, ExprNode::Free { .. }))
    {
        return Err("deep lambda result leaked a query-local free name".to_owned());
    }
    let mut cursor = result.type_.root();
    let mut forall_count = 0usize;
    loop {
        match result.type_.node(cursor) {
            Some(ExprNode::Forall {
                binder_name,
                binder_type,
                body,
                style,
            }) => {
                if !binder_name.is_anonymous()
                    || *style != fln_checker::wire::BinderStyle::Default
                    || !matches!(result.type_.node(*binder_type), Some(ExprNode::Sort { .. }))
                {
                    return Err(format!("deep lambda forall drifted at {forall_count}"));
                }
                forall_count = forall_count.saturating_add(1);
                cursor = *body;
            }
            Some(ExprNode::Sort { .. }) => break,
            Some(_) => return Err(format!("deep lambda terminal drifted at {forall_count}")),
            None => return Err(format!("deep lambda body missing at {forall_count}")),
        }
    }
    if forall_count != BINDERS {
        return Err(format!(
            "deep lambda forall count drifted: expected {BINDERS}, got {forall_count}"
        ));
    }
    Ok(())
}

#[test]
fn fifty_thousand_binder_lambda_telescope_fits_a_64k_stack() {
    const CHILD_ENV: &str = "FLN_CHECKER_INFER_DEEP_LAMBDA_CHILD";
    if std::env::var_os(CHILD_ENV).is_some() {
        let result = std::thread::Builder::new()
            .name("fln-checker-infer-lambda-deep".to_owned())
            .stack_size(64 * 1024)
            .spawn(deep_lambda_telescope_child)
            .expect("spawn bounded-stack lambda child")
            .join()
            .expect("bounded-stack lambda child did not panic");
        result.expect("bounded-stack lambda work");
        return;
    }

    let executable = std::env::current_exe().expect("current test executable");
    let output = Command::new(executable)
        .env(CHILD_ENV, "1")
        .args([
            "--exact",
            "fifty_thousand_binder_lambda_telescope_fits_a_64k_stack",
            "--nocapture",
        ])
        .output()
        .expect("run bounded-stack lambda child process");
    assert!(
        output.status.success(),
        "bounded-stack lambda child failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
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

fn deep_application_child() -> Result<(), String> {
    const ARGUMENTS: usize = 50_000;
    let sort_zero = Expr::sort(Level::zero());
    let mut function_type = sort_zero.clone();
    for _ in 0..ARGUMENTS {
        function_type = Expr::forall_e(
            Name::anonymous(),
            sort_zero.clone(),
            function_type,
            BinderInfo::Default,
        );
    }

    let argument = Expr::fvar(FVarId(primary_name("x")));
    let mut application = Expr::fvar(FVarId(primary_name("f")));
    for _ in 0..ARGUMENTS {
        application = Expr::app(application, argument.clone());
    }
    let context = built_context(
        vec![
            LocalDeclaration::assumption(checker_name("f"), decoded(&function_type)),
            LocalDeclaration::assumption(checker_name("x"), decoded(&sort_zero)),
        ],
        Vec::new(),
        Vec::new(),
    );
    let result = match infer(
        &decoded(&application),
        &context,
        InferenceMode::InferOnly,
        InferenceBudget::unlimited(),
    ) {
        InferenceOutcome::Complete(result) => result,
        other => return Err(format!("deep application inference failed: {other:?}")),
    };
    if result.progress.application_spine_nodes != ARGUMENTS as u64
        || result.progress.application_arguments != ARGUMENTS as u64
    {
        return Err(format!(
            "application progress drifted: spine={}, arguments={}",
            result.progress.application_spine_nodes, result.progress.application_arguments
        ));
    }
    if result.progress.defeq_queries != 0 {
        return Err("infer-only deep application ran domain conversion".to_owned());
    }
    if sort_model(&result.type_) != LevelModel::Zero {
        return Err("deep application inferred the wrong codomain".to_owned());
    }
    Ok(())
}

#[test]
fn fifty_thousand_argument_spine_fits_a_64k_stack() {
    const CHILD_ENV: &str = "FLN_CHECKER_INFER_DEEP_APPLICATION_CHILD";
    if std::env::var_os(CHILD_ENV).is_some() {
        let result = std::thread::Builder::new()
            .name("fln-checker-infer-application-deep".to_owned())
            .stack_size(64 * 1024)
            .spawn(deep_application_child)
            .expect("spawn bounded-stack application child")
            .join()
            .expect("bounded-stack application child did not panic");
        result.expect("bounded-stack application work");
        return;
    }

    let executable = std::env::current_exe().expect("current test executable");
    let output = Command::new(executable)
        .env(CHILD_ENV, "1")
        .args([
            "--exact",
            "fifty_thousand_argument_spine_fits_a_64k_stack",
            "--nocapture",
        ])
        .output()
        .expect("run bounded-stack application child process");
    assert!(
        output.status.success(),
        "bounded-stack application child failed\nstdout:\n{}\nstderr:\n{}",
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
