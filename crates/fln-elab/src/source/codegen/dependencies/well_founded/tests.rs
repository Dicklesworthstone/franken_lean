//! Raw selector models exercise classification only; no model below is executed
//! or published. The facade and CLI tests separately use real source admission.
use super::*;
use fln_env::constants::{AxiomVal, DefinitionVal, RecursorVal, ReducibilityHints, TheoremVal};

fn c(text: &str) -> Expr {
    Expr::const_(n(text), vec![])
}

fn seven() -> Expr {
    Expr::lit(fln_core::expr::Literal::Nat(
        fln_core::expr::NatLit::from_u64(7),
    ))
}

fn definition(label: &str) -> ConstantInfo {
    ConstantInfo::Defn(DefinitionVal {
        base: ConstantVal {
            name: n(label),
            level_params: vec![],
            type_: c("Nat"),
        },
        value: seven(),
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![n(label)],
    })
}

fn equation(source: &str, target: &str, label: &str) -> TheoremVal {
    TheoremVal {
        base: ConstantVal {
            name: n(label),
            level_params: vec![],
            type_: [c("Nat"), c(source), c(target)]
                .into_iter()
                .fold(Expr::const_(n("Eq"), vec![Level::one()]), Expr::app),
        },
        value: [c("Nat"), c(source)]
            .into_iter()
            .fold(Expr::const_(n("Eq.refl"), vec![Level::one()]), Expr::app),
        all: vec![n(label)],
    }
}

fn environment(omit: Option<&str>) -> Environment {
    let mut environment = crate::seed::bootstrap_nat_environment(Budget::DEFAULT).unwrap();
    let Declaration::Inductive(equality) = crate::seed::eq_seed_declaration() else {
        unreachable!();
    };
    for info in equality
        .types
        .into_iter()
        .map(ConstantInfo::Induct)
        .chain(equality.ctors.into_iter().map(ConstantInfo::Ctor))
        .chain(equality.recursors.into_iter().map(ConstantInfo::Rec))
    {
        environment = environment.add_decl(info).unwrap();
    }
    for (source, target, label) in EQUATIONS {
        // The primitive Rec alternative is a matcher-only model. The actual
        // Acc telescope is exercised through the pinned CLI regression.
        let source_info = if source == "Acc.rec" {
            ConstantInfo::Rec(RecursorVal {
                base: ConstantVal {
                    name: n(source),
                    level_params: vec![],
                    type_: c("Nat"),
                },
                all: vec![n("Acc")],
                num_params: 0,
                num_indices: 0,
                num_motives: 0,
                num_minors: 0,
                rules: vec![],
                k: false,
                is_unsafe: false,
            })
        } else {
            definition(source)
        };
        environment = environment.add_decl(source_info).unwrap();
        environment = environment.add_decl(definition(target)).unwrap();
        if omit != Some(label) {
            environment = environment
                .add_decl(ConstantInfo::Thm(equation(source, target, label)))
                .unwrap();
        }
        environment = crate::noncomputable::register(&environment, &n(source)).unwrap();
    }
    environment.add_decl(definition("other")).unwrap()
}

fn changed(environment: &Environment, label: &Name, replacement: ConstantInfo) -> Environment {
    assert_eq!(replacement.name(), label);
    let mut result = Environment::new();
    for (candidate, _) in environment.constants() {
        if candidate != label {
            result = result
                .with_entry(environment.entry(candidate).unwrap())
                .unwrap();
        }
    }
    result = result.add_decl(replacement).unwrap();
    for (journal, state) in environment.extensions() {
        result = result.register_extension(state.descriptor.clone()).unwrap();
        for entry in state.entries() {
            result = result
                .push_extension_entry(journal, entry.payload.clone())
                .unwrap();
        }
    }
    result
}

fn compiled(
    environment: &Environment,
    label: &str,
    section: bool,
) -> Result<bool, NatDefinitionElabError> {
    let mut context = Context::new(environment, Budget::DEFAULT);
    context.source_scope.noncomputable_section = section;
    let locals = context.txn.lctx.clone();
    let result = context.check_definition_codegen(&Typed {
        type_: c("Nat"),
        value: c(label),
    });
    assert_eq!(context.txn.lctx, locals);
    assert_eq!(&context.txn.env, environment);
    result
}

fn noncomputable(error: Result<bool, NatDefinitionElabError>, expected: &str) {
    assert!(matches!(error,
        Err(NatDefinitionElabError::Inference(SourceInferenceError::NoncomputableDependency(label)))
        if label == n(expected)));
}

#[test]
fn production_dependency_walk_selects_each_equation_without_changing_logical_declarations() {
    let environment = environment(None);
    for (source, _, _) in EQUATIONS {
        for section in [false, true] {
            assert_eq!(
                compiled(&environment, source, section),
                Ok(false),
                "{source}"
            );
        }
        assert!(
            crate::noncomputable::read(&environment)
                .unwrap()
                .contains(&n(source))
        );
    }
}

#[test]
fn missing_equations_and_noncomputable_targets_do_not_gain_executable_authority() {
    for (source, target, label) in EQUATIONS {
        let absent = environment(Some(label));
        noncomputable(compiled(&absent, source, false), source);
        assert_eq!(compiled(&absent, source, true), Ok(true));
        let unusable = crate::noncomputable::register(&environment(None), &n(target)).unwrap();
        noncomputable(compiled(&unusable, source, false), target);
        let mut context = Context::new(&unusable, Budget::DEFAULT);
        let mut dependencies = Dependencies::read(&mut context).unwrap();
        assert!(
            dependencies
                .check_compiled(&mut context, &n(source))
                .is_err()
        );
        assert!(
            dependencies
                .well_founded
                .equations
                .iter()
                .all(Option::is_none)
        );
        assert!(!dependencies.well_founded.equality_checked);
    }
}

#[test]
fn counterfeit_equations_cannot_be_suppressed_by_a_noncomputable_section() {
    let environment = environment(None);
    for (source, target, label) in EQUATIONS {
        let original = equation(source, target, label);
        let mut reversed = original.clone();
        reversed.base.type_ = equation(target, source, label).base.type_;
        let mut non_equality = original.clone();
        non_equality.base.type_ = c("Nat");
        for replacement in [
            ConstantInfo::Axiom(AxiomVal {
                base: original.base.clone(),
                is_unsafe: false,
            }),
            ConstantInfo::Thm(reversed),
            ConstantInfo::Thm(non_equality),
        ] {
            let invalid = changed(&environment, &n(label), replacement);
            for section in [false, true] {
                assert!(matches!(
                    compiled(&invalid, source, section),
                    Err(NatDefinitionElabError::Inference(
                        SourceInferenceError::NoncomputableJournal(
                            crate::noncomputable::NoncomputableError::CompilerEquation { .. }
                        )
                    ))
                ));
            }
        }
    }
}

#[test]
fn a_validated_equation_cannot_authorize_a_different_equation_or_environment() {
    let base = environment(Some("Acc.ndrec_eq_ndrecC"));
    let mut context = Context::new(&base, Budget::DEFAULT);
    let mut dependencies = Dependencies::read(&mut context).unwrap();
    dependencies
        .check_compiled(&mut context, &n("WellFounded.fix"))
        .unwrap();
    assert_eq!(dependencies.well_founded.equations[0], Some(true));
    assert!(
        dependencies.well_founded.equations[1..]
            .iter()
            .all(Option::is_none)
    );
    assert!(
        dependencies
            .check_compiled(&mut context, &n("Acc.ndrec"))
            .is_err()
    );
    assert_eq!(dependencies.well_founded.equations[2], None);
    let missing = environment(Some("WellFounded.fix_eq_fixC"));
    noncomputable(
        compiled(&missing, "WellFounded.fix", false),
        "WellFounded.fix",
    );
}

#[test]
fn explicit_implementations_externs_and_companions_keep_their_precedence() {
    let base = environment(None);
    let overridden =
        crate::implemented_by::register(&base, &n("WellFounded.fix"), &n("other")).unwrap();
    assert_eq!(compiled(&overridden, "WellFounded.fix", false), Ok(false));
    let bodyless = crate::externs::register(
        &base,
        &n("WellFounded.fix"),
        vec![crate::externs::ExternEntry::Opaque],
    )
    .unwrap();
    assert_eq!(compiled(&bodyless, "WellFounded.fix", false), Ok(false));
    let paired = base
        .add_decl(definition("WellFounded.fix._unsafe_rec"))
        .unwrap();
    noncomputable(
        compiled(&paired, "WellFounded.fix", false),
        "WellFounded.fix",
    );
    let target_companion = base
        .add_decl(definition("WellFounded.fixC._unsafe_rec"))
        .unwrap();
    let target_companion =
        crate::noncomputable::register(&target_companion, &n("WellFounded.fixC._unsafe_rec"))
            .unwrap();
    noncomputable(
        compiled(&target_companion, "WellFounded.fix", false),
        "WellFounded.fixC",
    );
}

#[test]
fn mixed_equation_attribute_cycles_publish_no_cache_and_are_never_suppressed() {
    let base = environment(None);
    let first =
        crate::implemented_by::register(&base, &n("WellFounded.fixC"), &n("WellFounded.fixF"))
            .unwrap();
    assert_eq!(compiled(&first, "WellFounded.fix", false), Ok(false));
    let cycle =
        crate::implemented_by::register(&first, &n("WellFounded.fixFC"), &n("WellFounded.fix"))
            .unwrap();
    for section in [false, true] {
        assert!(matches!(
            compiled(&cycle, "WellFounded.fix", section),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::NoncomputableJournal(
                    crate::noncomputable::NoncomputableError::CompilerEquation {
                        reason: "cyclic executable replacement chain",
                        ..
                    }
                )
            ))
        ));
    }
    let mut context = Context::new(&cycle, Budget::DEFAULT);
    let mut dependencies = Dependencies::read(&mut context).unwrap();
    assert!(
        dependencies
            .check_compiled(&mut context, &n("WellFounded.fix"))
            .is_err()
    );
    assert!(
        dependencies
            .well_founded
            .equations
            .iter()
            .all(Option::is_none)
    );
    assert!(!dependencies.well_founded.equality_checked);
}

#[test]
fn malformed_journals_and_a_corrupt_equality_family_still_refuse() {
    let base = environment(None);
    let malformed = base
        .push_extension_entry(&crate::noncomputable::journal_name(), b"broken".to_vec())
        .unwrap();
    assert!(matches!(
        compiled(&malformed, "WellFounded.fix", true),
        Err(NatDefinitionElabError::Inference(
            SourceInferenceError::NoncomputableJournal(_)
        ))
    ));
    let mut equality = base.find(&n("Eq.rec")).unwrap().clone();
    let ConstantInfo::Rec(ref mut recursor) = equality else {
        unreachable!();
    };
    recursor.rules[0].rhs = seven();
    let invalid = changed(&base, &n("Eq.rec"), equality);
    assert!(matches!(
        compiled(&invalid, "WellFounded.fix", true),
        Err(NatDefinitionElabError::Inference(
            SourceInferenceError::NoncomputableJournal(
                crate::noncomputable::NoncomputableError::CompilerEquation { .. }
            )
        ))
    ));
}

#[test]
fn every_selector_budget_stop_is_typed_and_preserves_locals_and_successful_cache_state() {
    let environment = environment(None);
    let mut full_context = Context::new(&environment, Budget::DEFAULT);
    let mut full = Dependencies::read(&mut full_context).unwrap();
    let before = full_context.txn.budget.heartbeats_consumed;
    full.check_compiled(&mut full_context, &n("WellFounded.fix"))
        .unwrap();
    let required = full_context.txn.budget.heartbeats_consumed - before;
    assert!(required > 1);
    for allowance in 1..required {
        let mut context = Context::new(&environment, Budget::DEFAULT);
        let mut dependencies = Dependencies::read(&mut context).unwrap();
        let locals = context.txn.lctx.clone();
        context.txn.budget.max_heartbeats = context.txn.budget.heartbeats_consumed + allowance;
        assert!(
            matches!(
                dependencies.check_compiled(&mut context, &n("WellFounded.fix")),
                Err(NatDefinitionElabError::Inference(
                    SourceInferenceError::ResourceLimit
                ))
            ),
            "allowance {allowance}"
        );
        assert_eq!(context.txn.lctx, locals);
        assert_eq!(context.txn.env, environment);
        assert!(
            dependencies
                .well_founded
                .equations
                .iter()
                .all(Option::is_none)
        );
        assert!(!dependencies.well_founded.equality_checked);
    }
    let mut retry_context = Context::new(&environment, Budget::DEFAULT);
    let mut retry = Dependencies::read(&mut retry_context).unwrap();
    let before = retry_context.txn.budget.heartbeats_consumed;
    retry
        .check_compiled(&mut retry_context, &n("WellFounded.fix"))
        .unwrap();
    assert_eq!(
        retry_context.txn.budget.heartbeats_consumed - before,
        required
    );
}

#[test]
fn universe_substitution_is_parametric_and_rejects_repeated_or_closed_endpoints() {
    let source = n("WellFounded.fixF");
    let target = n("WellFounded.fixFC");
    let theorem = n("WellFounded.fixF_eq_fixFC");
    let mut base = environment(None);
    let parameter = n("u");
    let universe = Level::param(parameter.clone());
    let signature = Expr::forall_e(
        n("A"),
        Expr::sort(universe.clone()),
        Expr::forall_e(
            n("x"),
            Expr::bvar(0).unwrap(),
            Expr::bvar(1).unwrap(),
            BinderInfo::Default,
        ),
        BinderInfo::Implicit,
    );
    for endpoint in [&source, &target] {
        let definition = ConstantInfo::Defn(DefinitionVal {
            base: ConstantVal {
                name: endpoint.clone(),
                level_params: vec![parameter.clone()],
                type_: signature.clone(),
            },
            value: Expr::lam(
                n("A"),
                Expr::sort(universe.clone()),
                Expr::lam(
                    n("x"),
                    Expr::bvar(0).unwrap(),
                    Expr::bvar(0).unwrap(),
                    BinderInfo::Default,
                ),
                BinderInfo::Implicit,
            ),
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: vec![endpoint.clone()],
        });
        base = changed(&base, endpoint, definition);
    }
    let equation = |levels: Vec<Level>, params: Vec<Name>| ConstantVal {
        name: theorem.clone(),
        level_params: params,
        type_: [
            signature.clone(),
            Expr::const_(source.clone(), levels.clone()),
            Expr::const_(target.clone(), levels),
        ]
        .into_iter()
        .fold(
            Expr::const_(n("Eq"), vec![universe.clone().succ().unwrap()]),
            Expr::app,
        ),
    };
    let valid = equation(vec![universe.clone()], vec![parameter.clone()]);
    validate_equation(
        &mut Context::new(&base, Budget::DEFAULT),
        &base,
        &source,
        &target,
        &valid,
    )
    .unwrap();
    for invalid in [
        equation(vec![Level::one()], vec![parameter.clone()]),
        equation(
            vec![universe.clone(), universe.clone()],
            vec![parameter.clone(), parameter.clone()],
        ),
        equation(vec![universe.clone()], vec![]),
    ] {
        assert!(matches!(
            validate_equation(
                &mut Context::new(&base, Budget::DEFAULT),
                &base,
                &source,
                &target,
                &invalid
            ),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::NoncomputableJournal(
                    crate::noncomputable::NoncomputableError::CompilerEquation { .. }
                )
            ))
        ));
    }
}

#[test]
fn unsupported_target_safety_and_mismatched_interfaces_never_authorize_selection() {
    let base = environment(None);
    for (source, target, _) in EQUATIONS {
        for safety in [DefinitionSafety::Unsafe, DefinitionSafety::Partial] {
            let ConstantInfo::Defn(mut replacement) = definition(target) else {
                unreachable!();
            };
            replacement.safety = safety;
            let altered = changed(&base, &n(target), ConstantInfo::Defn(replacement));
            assert!(matches!(
                compiled(&altered, source, true),
                Err(NatDefinitionElabError::Inference(
                    SourceInferenceError::NoncomputableJournal(
                        crate::noncomputable::NoncomputableError::CompilerEquation { .. }
                    )
                ))
            ));
        }
        let ConstantInfo::Defn(mut replacement) = definition(target) else {
            unreachable!();
        };
        replacement.base.type_ = Expr::sort(Level::one());
        let altered = changed(&base, &n(target), ConstantInfo::Defn(replacement));
        assert!(matches!(
            compiled(&altered, source, true),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::NoncomputableJournal(
                    crate::noncomputable::NoncomputableError::CompilerEquation { .. }
                )
            ))
        ));
    }
}
