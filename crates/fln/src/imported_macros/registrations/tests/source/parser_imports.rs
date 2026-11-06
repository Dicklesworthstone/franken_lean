//! Artifact-only syntax reaches imported macro execution and ordinary admission.
//! These constructed, fully checked library inputs are integration witnesses,
//! not claims of Reference corpus parity. Consumers declare no local syntax.
use super::modules::{check, succeeded};
use super::*;
use crate::imported_parsers::{ParserRegistrationError, ParserRegistryLimits};
use crate::source_check::modules::imported::SourceOleanImport;
use fln_core::expr::BinderInfo;

// Share the codec's mechanically extracted wire contract across artifact tests.
use crate::imported_parsers::test_wire as wire;

mod commands;

#[derive(Clone, Copy, Debug)]
enum Fault {
    None,
    MalformedSuffix,
    UnsupportedSuffix,
    UnsupportedScopedSuffix,
    TokenBudgetSuffix,
}

pub(super) fn constant(label: &str) -> Expr {
    Expr::const_(name(label), vec![])
}

pub(super) fn apply(label: &str, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(constant(label), Expr::app)
}

pub(super) fn string(text: &str) -> Expr {
    Expr::lit(Literal::Str(text.into()))
}

pub(super) fn natural(value: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(value)))
}

pub(super) fn literal_name(label: &str) -> Expr {
    label
        .split('.')
        .fold(constant("Lean.Name.anonymous"), |prefix, part| {
            apply("Lean.Name.str", [prefix, string(part)])
        })
}

pub(super) fn definition(label: &str, type_: Expr, value: Expr) -> ConstantInfo {
    ConstantInfo::Defn(DefinitionVal {
        base: ConstantVal {
            name: name(label),
            level_params: vec![],
            type_,
        },
        value,
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![name(label)],
    })
}

fn descriptor(kind: &str, token: &str, unsupported: bool) -> Expr {
    let body = if unsupported {
        apply(
            "Lean.ParserDescr.const",
            [literal_name("unimplementedAlias")],
        )
    } else {
        apply(
            "Lean.ParserDescr.binary",
            [
                literal_name("andthen"),
                apply("Lean.ParserDescr.symbol", [string(token)]),
                apply(
                    "Lean.ParserDescr.cat",
                    [literal_name("term"), natural(1024)],
                ),
            ],
        )
    };
    apply(
        "Lean.ParserDescr.node",
        [literal_name(kind), natural(1022), body],
    )
}

fn bounded_descriptor(kind: &str, token: &str, precedence: u32) -> Expr {
    let sequence = |left, right| {
        apply(
            "Lean.ParserDescr.binary",
            [literal_name("andthen"), left, right],
        )
    };
    apply(
        "Lean.ParserDescr.node",
        [
            literal_name(kind),
            natural(1022),
            sequence(
                apply("Lean.ParserDescr.symbol", [string(token)]),
                sequence(
                    apply(
                        "Lean.ParserDescr.cat",
                        [literal_name("term"), natural(u64::from(precedence))],
                    ),
                    apply("Lean.ParserDescr.symbol", [string("done!")]),
                ),
            ),
        ],
    )
}

pub(super) fn scope(row: Obj, namespace: Option<&str>) -> Obj {
    match namespace {
        None => Obj::mk_ctor(wire::SCOPE_GLOBAL, vec![row], &[]),
        Some(namespace) => Obj::mk_ctor(
            wire::SCOPE_SCOPED,
            vec![inject_name(&name(namespace)), row],
            &[],
        ),
    }
}

fn parser_rows(kind: &str, declaration: &str, token: &str, namespace: Option<&str>) -> Vec<Obj> {
    vec![
        scope(
            Obj::mk_ctor(wire::PARSER_ENTRY_TOKEN, vec![Obj::mk_string(token)], &[]),
            namespace,
        ),
        // The pin exports a scoped parser's syntax kind globally.
        scope(
            Obj::mk_ctor(wire::PARSER_ENTRY_KIND, vec![inject_name(&name(kind))], &[]),
            None,
        ),
        scope(
            Obj::mk_ctor(
                wire::PARSER_ENTRY_PARSER,
                vec![
                    inject_name(&name("term")),
                    inject_name(&name(declaration)),
                    Obj::mk_nat(1000),
                ],
                &[],
            ),
            namespace,
        ),
    ]
}

fn fixture(fault: Fault) -> (SourceOleanImport, Vec<IrModule>) {
    let (mut imported, code) = unselected_fixture(fault);
    if matches!(fault, Fault::None) {
        imported
            .enable_imported_syntax(&[name("SourceLibrary")], ParserRegistryLimits::default())
            .unwrap();
    }
    (imported, code)
}

fn unselected_fixture(fault: Fault) -> (SourceOleanImport, Vec<IrModule>) {
    unselected_fixture_with_dependency(fault, false)
}

fn unselected_fixture_with_dependency(
    fault: Fault,
    with_dependency: bool,
) -> (SourceOleanImport, Vec<IrModule>) {
    unselected_fixture_with_operand(fault, with_dependency, None)
}

fn unselected_fixture_with_operand(
    fault: Fault,
    with_dependency: bool,
    operand_precedence: Option<u32>,
) -> (SourceOleanImport, Vec<IrModule>) {
    let mut constants = Vec::new();
    for declaration in crate::imported_parsers::fixture_declarations() {
        match declaration {
            crate::Declaration::Inductive(block) => {
                constants.extend(block.types.into_iter().map(ConstantInfo::Induct));
                constants.extend(block.ctors.into_iter().map(ConstantInfo::Ctor));
                constants.extend(block.recursors.into_iter().map(ConstantInfo::Rec));
            }
            crate::Declaration::Defn(value) => constants.push(ConstantInfo::Defn(value)),
            _ => panic!("parser fixture must contain genuine data families and aliases"),
        }
    }
    let mut dependency_constants = if with_dependency {
        std::mem::take(&mut constants)
    } else {
        Vec::new()
    };
    let dependency_rows = if with_dependency {
        dependency_constants.push(definition(
            "ParserPrelude.unsupportedParser",
            constant(wire::PARSER_DESCR_TYPE),
            descriptor("ParserPrelude.unsupportedKind", "unsupportedSyntax!", true),
        ));
        parser_rows(
            "ParserPrelude.unsupportedKind",
            "ParserPrelude.unsupportedParser",
            "unsupportedSyntax!",
            None,
        )
    } else {
        Vec::new()
    };
    constants.extend([
        definition(
            "SourceLibrary.chooseParser",
            constant(wire::PARSER_DESCR_TYPE),
            operand_precedence.map_or_else(
                || descriptor("SourceLibrary.choose", "choose!", false),
                |precedence| bounded_descriptor("SourceLibrary.choose", "choose!", precedence),
            ),
        ),
        definition(
            "SourceLibrary.scopedParser",
            constant(wire::PARSER_DESCR_TYPE),
            descriptor("SourceLibrary.scopedChoice", "scopedChoice!", false),
        ),
    ]);
    let mut macro_body = natural(0);
    for binder in ["state", "context", "syntax"] {
        macro_body = Expr::lam(
            name(binder),
            constant("Nat"),
            macro_body,
            BinderInfo::Default,
        );
    }
    constants.push(definition(
        "SourceLibrary.chooseMacro",
        constant("Lean.Macro"),
        macro_body,
    ));
    let mut rows = parser_rows(
        "SourceLibrary.choose",
        "SourceLibrary.chooseParser",
        "choose!",
        None,
    );
    if operand_precedence.is_some() {
        rows.push(scope(
            Obj::mk_ctor(wire::PARSER_ENTRY_TOKEN, vec![Obj::mk_string("done!")], &[]),
            None,
        ));
    }
    rows.extend(parser_rows(
        "SourceLibrary.scopedChoice",
        "SourceLibrary.scopedParser",
        "scopedChoice!",
        Some("SourceScoped"),
    ));
    match fault {
        Fault::None => {}
        Fault::MalformedSuffix => rows.push(Obj::mk_nat(0)),
        Fault::TokenBudgetSuffix => rows.push(scope(
            Obj::mk_ctor(
                wire::PARSER_ENTRY_TOKEN,
                vec![Obj::mk_string(&"k".repeat(4097))],
                &[],
            ),
            None,
        )),
        Fault::UnsupportedSuffix | Fault::UnsupportedScopedSuffix => {
            constants.push(definition(
                "SourceLibrary.unsupportedParser",
                constant(wire::PARSER_DESCR_TYPE),
                descriptor("SourceLibrary.unsupportedKind", "unsupportedSyntax!", true),
            ));
            rows.extend(parser_rows(
                "SourceLibrary.unsupportedKind",
                "SourceLibrary.unsupportedParser",
                "unsupportedSyntax!",
                matches!(fault, Fault::UnsupportedScopedSuffix).then_some("Dormant"),
            ));
        }
    }
    batches::artifact_import_fixture_with_parser_dependency(
        &[
            ("SourceLibrary.choose", "SourceLibrary.chooseMacro", None),
            (
                "SourceLibrary.scopedChoice",
                "SourceLibrary.chooseMacro",
                Some("SourceScoped"),
            ),
        ],
        &constants,
        &rows,
        &[selecting_function("SourceLibrary.chooseMacro", 1)],
        with_dependency.then_some(("ParserPrelude", &dependency_constants, &dependency_rows)),
    )
}

fn execute_graph(
    imported: &SourceOleanImport,
    compilation: MacroCompilationInputs,
    entries: &[(&str, &str)],
    limits: crate::source_check::modules::execution::SourceProgramLimits,
    registry_limits: MacroRegistryLimits,
    cancellation: Option<&dyn fln_vm::interpreter::CancellationProbe>,
) -> crate::source_check::modules::SourceMacroProgramExecution {
    let names: Vec<_> = entries.iter().map(|(module, _)| name(module)).collect();
    let modules: Vec<_> = names
        .iter()
        .zip(entries)
        .map(|(name, (_, source))| crate::SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    imported.execute_source_modules_with_deferred_imported_macros(
        &modules,
        &names[0],
        &KVMap::new(),
        limits,
        crate::source_check::modules::SourceModuleDeferredMacroInputs {
            compilation,
            registry_limits,
            context: context(),
            state: MacroState {
                macro_scope: 17,
                ..MacroState::default()
            },
            limits: MacroTreeLimits::default(),
        },
        cancellation,
        crate::EvaluationPresentation::Raw,
    )
}

#[test]
fn artifact_syntax_without_local_declaration_expands_and_kernel_checks_values_and_proofs() {
    let (imported, code) = fixture(Fault::None);
    let before = imported.engine.logical_root(&KVMap::new());
    let report = check(
        &imported,
        &code,
        &[(
            "Main",
            "prelude\nimport SourceLibrary\ndef chosen : Nat := choose! 42\ntheorem chosen_ok : chosen = 42 := by rfl",
        )],
        MacroTreeLimits::default(),
        None,
    );
    let checked = succeeded(&report);
    assert_declared_value(&checked.checked.engine, "chosen", 42);
    assert!(
        checked
            .checked
            .engine
            .environment()
            .contains(&name("chosen_ok"))
    );
    assert_eq!(report.attempts.len(), 1);
    // The chosen_ok proof also enters evalTactic's unconditional fresh scope
    // (pin Tactic/Basic.lean:194), although rfl has no imported macro candidate.
    assert_eq!(
        report.states.as_ref().unwrap()[&name("Main")].macro_scope,
        17 + 1 + 1
    );
    assert!(
        imported.checked.modules[0]
            .declarations
            .iter()
            .any(|row| row.name == name("Lean.ParserDescr"))
    );
    assert!(
        imported.checked.modules[0]
            .declarations
            .iter()
            .any(|row| row.name == name("SourceLibrary.chooseParser"))
    );
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
    assert!(!imported.engine.environment().contains(&name("chosen")));

    let false_proof = check(
        &imported,
        &code,
        &[(
            "Main",
            "prelude\nimport SourceLibrary\ndef chosen : Nat := choose! 42\ntheorem wrong : chosen = 43 := by rfl",
        )],
        MacroTreeLimits::default(),
        None,
    );
    assert!(
        matches!(false_proof.outcome, Outcome::Complete(Err(_))),
        "{false_proof:?}"
    );
    assert_eq!(false_proof.attempts.len(), 1);
    assert!(false_proof.states.is_none());
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
}

#[test]
fn artifact_operand_precedence_survives_codec_admission_reexport_and_macro_expansion() {
    for precedence in [65, 66] {
        let (mut imported, code) =
            unselected_fixture_with_operand(Fault::None, false, Some(precedence));
        imported
            .enable_imported_syntax(&[name("SourceLibrary")], ParserRegistryLimits::default())
            .unwrap();
        let before = imported.engine.logical_root(&KVMap::new());
        let source = if precedence == 65 {
            "prelude\nimport Forward\n\
             def chosen : Nat := choose! 7 + 42 done!\n\
             theorem chosen_ok : chosen = 42 := by rfl"
        } else {
            "prelude\nimport Forward\n\
             def chosen : Nat := choose! (7 + 42) done!\n\
             theorem chosen_ok : chosen = 42 := by rfl"
        };
        let report = check(
            &imported,
            &code,
            &[
                ("Main", source),
                ("Forward", "prelude\nimport SourceLibrary"),
            ],
            MacroTreeLimits::default(),
            None,
        );
        // This fixture's independently registered '+' macro selects its right
        // operand. Reaching 42 witnesses both expansion layers and the checked
        // proof, rather than treating the parser's output as an admitted term.
        let checked = succeeded(&report);
        assert_declared_value(&checked.checked.engine, "chosen", 42);
        assert!(
            checked
                .checked
                .engine
                .environment()
                .contains(&name("chosen_ok"))
        );
        assert_eq!(imported.engine.logical_root(&KVMap::new()), before);

        if precedence == 66 {
            let rejected = check(
                &imported,
                &code,
                &[(
                    "Main",
                    "prelude\nimport SourceLibrary\ndef prefix : Nat := 7\n\
                     def bad : Nat := choose! 7 + 42 done!",
                )],
                MacroTreeLimits::default(),
                None,
            );
            assert!(
                matches!(rejected.outcome, Outcome::Complete(Err(_))),
                "{rejected:?}"
            );
            assert!(rejected.states.is_none());
            assert!(!imported.engine.environment().contains(&name("prefix")));
            assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
        }
    }
}

#[test]
fn imported_artifact_syntax_executes_evaluations_and_keeps_program_failures_transactional() {
    fn execute(
        imported: &SourceOleanImport,
        code: &[IrModule],
        source: &str,
    ) -> crate::source_check::modules::SourceMacroProgramExecution {
        let module = name("Main");
        imported.execute_source_modules_with_imported_macros(
            &[crate::SourceModuleInput {
                name: &module,
                source: source.as_bytes(),
            }],
            &module,
            &KVMap::new(),
            crate::source_check::modules::execution::SourceProgramLimits::new(execution_limits()),
            crate::source_check::modules::SourceModuleMacroInputs {
                code,
                partition: &VerifiedPartition::user_fixture(),
                user_declarations: &users(code),
                registry_limits: MacroRegistryLimits::default(),
                context: context(),
                state: MacroState {
                    macro_scope: 17,
                    ..MacroState::default()
                },
                limits: MacroTreeLimits::default(),
            },
            None,
            crate::EvaluationPresentation::Raw,
        )
    }

    let source = "prelude\nimport SourceLibrary\n\
                  def chosen : Nat := choose! 42\n\
                  theorem chosen_ok : chosen = 42 := by rfl\n\
                  #eval choose! 42\n#eval chosen";
    let (imported, code) = fixture(Fault::None);
    let before = imported.engine.logical_root(&KVMap::new());
    let report = execute(&imported, &code, source);
    let Outcome::Complete(Ok(program)) = &report.outcome else {
        panic!("{report:?}");
    };
    assert_eq!(program.modules.len(), 1);
    let batch = &program.modules[0].commands.batch;
    assert_eq!(batch.source_evaluation_indices.len(), 2);
    for index in &batch.source_evaluation_indices {
        assert_eq!(
            crate::closed_vm_value(&batch.executions[*index].exit)
                .unwrap()
                .unwrap(),
            crate::ClosedVmValue::Scalar(42)
        );
    }
    assert_declared_value(&batch.engine, "chosen", 42);
    assert!(batch.engine.environment().contains(&name("chosen_ok")));
    assert_eq!(report.attempts.len(), 2, "each custom syntax expands once");
    // Two choose! expansions and chosen_ok's native rfl each allocate a scope.
    assert_eq!(
        report.states.as_ref().unwrap()[&name("Main")].macro_scope,
        17 + 2 + 1
    );
    assert!(report.completed_vm_usage.steps > 0);

    let false_proof = execute(
        &imported,
        &code,
        "prelude\nimport SourceLibrary\n\
         def chosen : Nat := choose! 42\n#eval choose! 42\n\
         theorem wrong : chosen = 43 := by rfl",
    );
    assert!(
        matches!(false_proof.outcome, Outcome::Complete(Err(_))),
        "{false_proof:?}"
    );
    assert!(!false_proof.attempts.is_empty());
    assert!(false_proof.states.is_none());
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
    assert!(!imported.engine.environment().contains(&name("chosen")));

    let (mut malformed, code) = fixture(Fault::MalformedSuffix);
    let before = malformed.engine.logical_root(&KVMap::new());
    assert!(matches!(
        malformed.enable_imported_syntax(&[name("SourceLibrary")], ParserRegistryLimits::default()),
        Err(ParserRegistrationError::Decode { .. })
    ));
    let stopped = execute(&malformed, &code, source);
    assert!(
        matches!(stopped.outcome, Outcome::Complete(Err(_))),
        "{stopped:?}"
    );
    assert!(stopped.states.is_none());
    assert!(stopped.attempts.is_empty());
    assert_eq!(malformed.engine.logical_root(&KVMap::new()), before);
    assert!(!malformed.engine.environment().contains(&name("chosen")));
}

#[test]
fn imported_artifact_syntax_reaches_deferred_program_execution_without_publishing_failed_state() {
    let (imported, mut code) = fixture(Fault::None);
    let before = imported.engine.logical_root(&KVMap::new());
    // The complete journal still owns this unused macro. Only the demanded
    // choose! closure should compile, so unrelated missing IR cannot block it.
    for module in &mut code {
        module
            .decls
            .retain(|declaration| declaration.name() != &name("SourceLibrary.diagnostic"));
    }
    let declarations = users(&code);
    let compilation =
        MacroCompilationInputs::new(code, VerifiedPartition::user_fixture(), declarations);
    let run = |source: &str| {
        let module = name("Main");
        imported.execute_source_modules_with_deferred_imported_macros(
            &[crate::SourceModuleInput {
                name: &module,
                source: source.as_bytes(),
            }],
            &module,
            &KVMap::new(),
            crate::source_check::modules::execution::SourceProgramLimits::new(execution_limits()),
            crate::source_check::modules::SourceModuleDeferredMacroInputs {
                compilation: compilation.clone(),
                registry_limits: MacroRegistryLimits::default(),
                context: context(),
                state: MacroState {
                    macro_scope: 17,
                    ..MacroState::default()
                },
                limits: MacroTreeLimits::default(),
            },
            None,
            crate::EvaluationPresentation::Raw,
        )
    };
    let complete = run("prelude\nimport SourceLibrary\n\
         def chosen : Nat := choose! 42\n\
         theorem chosen_ok : chosen = 42 := by rfl\n\
         #eval choose! 42\n#eval chosen");
    let Outcome::Complete(Ok(program)) = &complete.outcome else {
        panic!("{complete:?}");
    };
    assert_eq!(program.modules.len(), 1);
    let batch = &program.modules[0].commands.batch;
    assert_eq!(batch.source_evaluation_indices.len(), 2);
    for index in &batch.source_evaluation_indices {
        assert_eq!(
            crate::closed_vm_value(&batch.executions[*index].exit)
                .unwrap()
                .unwrap(),
            crate::ClosedVmValue::Scalar(42)
        );
    }
    assert_declared_value(&batch.engine, "chosen", 42);
    assert!(batch.engine.environment().contains(&name("chosen_ok")));
    assert_eq!(complete.attempts.len(), 2);
    // Deferred execution retains the same two macro scopes and native rfl scope.
    assert_eq!(
        complete.states.as_ref().unwrap()[&name("Main")].macro_scope,
        17 + 2 + 1
    );
    assert!(complete.completed_vm_usage.steps > 0);

    let stopped = run("prelude\nimport SourceLibrary\n\
         def chosen : Nat := choose! 42\n#eval choose! 42\n\
         theorem wrong : chosen = 43 := by rfl");
    assert!(
        matches!(stopped.outcome, Outcome::Complete(Err(_))),
        "{stopped:?}"
    );
    assert!(!stopped.attempts.is_empty());
    assert!(stopped.states.is_none());
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
    assert!(!imported.engine.environment().contains(&name("chosen")));
}

#[test]
fn imported_scoped_parser_activation_stays_within_sections_and_source_modules() {
    let (imported, code) = fixture(Fault::None);
    let before = imported.engine.logical_root(&KVMap::new());
    let report = check(
        &imported,
        &code,
        &[
            (
                "Main",
                "prelude\nimport ScopedLib\ndef next : Nat := choose! 23\ntheorem scoped_value : inScope = 17 := by rfl",
            ),
            (
                "ScopedLib",
                "prelude\nimport SourceLibrary\nsection\nopen scoped SourceScoped\ndef inScope : Nat := scopedChoice! 17\nend\ndef afterScope : Nat := choose! 19",
            ),
        ],
        MacroTreeLimits::default(),
        None,
    );
    let checked = succeeded(&report);
    for (declaration, value) in [("inScope", 17), ("afterScope", 19), ("next", 23)] {
        assert_declared_value(&checked.checked.engine, declaration, value);
    }
    for source in [
        "prelude\nimport SourceLibrary\ndef unavailable : Nat := scopedChoice! 17",
        "prelude\nimport SourceLibrary\nsection\nopen scoped SourceScoped\ndef inside : Nat := scopedChoice! 17\nend\ndef unavailable : Nat := scopedChoice! 19",
    ] {
        let failed = check(
            &imported,
            &code,
            &[("Main", source)],
            MacroTreeLimits::default(),
            None,
        );
        assert!(
            matches!(failed.outcome, Outcome::Complete(Err(_))),
            "{failed:?}"
        );
        assert!(failed.states.is_none());
    }
    let isolated = check(
        &imported,
        &code,
        &[
            (
                "Main",
                "prelude\nimport ScopedLib\ndef unavailable : Nat := scopedChoice! 23",
            ),
            (
                "ScopedLib",
                "prelude\nimport SourceLibrary\nopen scoped SourceScoped\ndef inScope : Nat := scopedChoice! 17",
            ),
        ],
        MacroTreeLimits::default(),
        None,
    );
    assert!(
        matches!(isolated.outcome, Outcome::Complete(Err(_))),
        "{isolated:?}"
    );
    assert_eq!(
        isolated.attempts.len(),
        1,
        "only the dependency activated its namespace"
    );
    assert!(isolated.states.is_none());
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
}

#[test]
fn artifact_parser_follows_transitive_public_imports_and_private_forwarding_boundaries() {
    let (imported, code) = fixture(Fault::None);
    let before = imported.engine.logical_root(&KVMap::new());
    let report = check(
        &imported,
        &code,
        &[
            (
                "Main",
                "prelude\nimport Middle\ndef chosen : Nat := choose! 42\ntheorem inherited_ok : fromApi = 7 := by rfl",
            ),
            ("Middle", "module\nprelude\npublic import Api"),
            (
                "Api",
                "module\nprelude\npublic import SourceLibrary\n@[expose] public def fromApi : Nat := choose! 7",
            ),
        ],
        MacroTreeLimits::default(),
        None,
    );
    let checked = succeeded(&report);
    assert_declared_value(&checked.checked.engine, "chosen", 42);
    assert_declared_value(&checked.checked.engine, "fromApi", 7);
    assert_eq!(report.attempts.len(), 2);

    let private = check(
        &imported,
        &code,
        &[
            (
                "Main",
                "prelude\nimport Api\ndef unavailable : Nat := choose! 42",
            ),
            (
                "Api",
                "module\nprelude\nimport SourceLibrary\n@[expose] public def fromApi : Nat := choose! 7",
            ),
        ],
        MacroTreeLimits::default(),
        None,
    );
    assert!(
        matches!(private.outcome, Outcome::Complete(Err(_))),
        "{private:?}"
    );
    assert_eq!(
        private.attempts.len(),
        1,
        "the private dependency remains usable inside Api"
    );
    assert!(private.states.is_none());
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
}

#[test]
fn malformed_or_unsupported_later_parser_rows_cannot_publish_a_working_prefix() {
    for fault in [Fault::MalformedSuffix, Fault::UnsupportedSuffix] {
        let (mut imported, code) = fixture(fault);
        let before = imported.engine.logical_root(&KVMap::new());
        if matches!(fault, Fault::MalformedSuffix) {
            assert!(matches!(
                imported.prepare_imported_parsers(ParserRegistryLimits::default()),
                Err(ParserRegistrationError::Decode { .. })
            ));
        }
        let error = imported
            .enable_imported_syntax(&[name("SourceLibrary")], ParserRegistryLimits::default())
            .unwrap_err();
        assert!(!error.is_resource(), "{fault:?}: {error}");
        let report = check(
            &imported,
            &code,
            &[(
                "Main",
                "prelude\nimport SourceLibrary\ndef prefix : Nat := choose! 42",
            )],
            MacroTreeLimits::default(),
            None,
        );
        assert!(
            matches!(report.outcome, Outcome::Complete(Err(_))),
            "{fault:?}: {report:?}"
        );
        assert!(report.states.is_none());
        assert!(
            report.attempts.is_empty(),
            "{fault:?}: grammar preparation must finish before source execution"
        );
        assert!(!imported.engine.environment().contains(&name("prefix")));
        assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
    }
}

#[test]
fn inactive_unsupported_parser_rows_refuse_selection_even_for_empty_forwarding_modules() {
    let (mut imported, code) = fixture(Fault::UnsupportedScopedSuffix);
    let before = imported.engine.logical_root(&KVMap::new());
    // Closed data reconstruction succeeds; grammar capability validation must
    // still examine the complete selected journal, including inactive scopes.
    imported
        .prepare_imported_parsers(ParserRegistryLimits::default())
        .unwrap();
    let error = imported
        .enable_imported_syntax(&[name("SourceLibrary")], ParserRegistryLimits::default())
        .unwrap_err();
    assert!(matches!(error, ParserRegistrationError::Description { .. }));
    assert!(!error.is_resource(), "{error}");
    let source = "prelude\nimport SourceLibrary";
    let checked = check(
        &imported,
        &code,
        &[("Main", source)],
        MacroTreeLimits::default(),
        None,
    );
    assert!(
        matches!(checked.outcome, Outcome::Complete(Ok(_))),
        "{checked:?}"
    );
    assert!(checked.attempts.is_empty());
    assert!(checked.states.is_some());

    let declarations = users(&code);
    let executed = execute_graph(
        &imported,
        MacroCompilationInputs::new(code, VerifiedPartition::user_fixture(), declarations),
        &[("Main", source)],
        crate::source_check::modules::execution::SourceProgramLimits::new(execution_limits()),
        MacroRegistryLimits::default(),
        None,
    );
    assert!(
        matches!(executed.outcome, Outcome::Complete(Ok(_))),
        "{executed:?}"
    );
    assert!(executed.attempts.is_empty());
    assert_eq!(executed.completed_vm_usage.steps, 0);
    assert!(executed.states.is_some());
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
}

#[test]
fn imported_parser_installation_exhaustion_refuses_selection_before_empty_source_modules() {
    let (mut imported, code) = fixture(Fault::TokenBudgetSuffix);
    let before = imported.engine.logical_root(&KVMap::new());
    // The retained metadata and checked descriptions fit their own allowances.
    // Only the native grammar's independent token-byte allowance is exhausted.
    imported
        .prepare_imported_parsers(ParserRegistryLimits::default())
        .unwrap();
    let error = imported
        .enable_imported_syntax(&[name("SourceLibrary")], ParserRegistryLimits::default())
        .unwrap_err();
    assert!(matches!(error, ParserRegistrationError::Limit(_)));
    assert!(error.is_resource(), "{error}");
    // Selection failed before source execution. The unchanged empty selection
    // still permits macro-only forwarding; no parser prefix was installed.
    let source = "prelude\nimport SourceLibrary";
    let checked = check(
        &imported,
        &code,
        &[("Main", source)],
        MacroTreeLimits::default(),
        None,
    );
    assert!(
        matches!(checked.outcome, Outcome::Complete(Ok(_))),
        "{checked:?}"
    );
    assert!(checked.attempts.is_empty());
    assert!(checked.states.is_some());

    let declarations = users(&code);
    let executed = execute_graph(
        &imported,
        MacroCompilationInputs::new(code, VerifiedPartition::user_fixture(), declarations),
        &[("Main", source)],
        crate::source_check::modules::execution::SourceProgramLimits::new(execution_limits()),
        MacroRegistryLimits::default(),
        None,
    );
    assert!(
        matches!(executed.outcome, Outcome::Complete(Ok(_))),
        "{executed:?}"
    );
    assert!(executed.attempts.is_empty());
    assert_eq!(executed.completed_vm_usage.steps, 0);
    assert!(executed.states.is_some());
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
}

#[test]
fn parser_preparation_exhaustion_is_resource_typed_and_keeps_the_import_receipt_unchanged() {
    let (imported, _) = fixture(Fault::None);
    let before = imported.engine.logical_root(&KVMap::new());
    let error = imported
        .prepare_imported_parsers(ParserRegistryLimits {
            max_description_nodes: 0,
            ..ParserRegistryLimits::default()
        })
        .unwrap_err();
    assert!(error.is_resource(), "{error}");
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
    imported
        .prepare_imported_parsers(ParserRegistryLimits::default())
        .unwrap();
}

#[test]
fn imported_parser_preflight_checks_the_whole_graph_before_macro_or_program_execution() {
    use crate::source_check::modules::SourceModuleCheckError;
    use crate::source_check::modules::execution::{
        SourceProgramExecutionError, SourceProgramLimits,
    };

    let (imported, code) = fixture(Fault::None);
    let before = imported.engine.logical_root(&KVMap::new());
    let declarations = users(&code);
    let compilation =
        MacroCompilationInputs::new(code, VerifiedPartition::user_fixture(), declarations);
    let early = "prelude\nimport SourceLibrary\ndef first : Nat := choose! 41\n#eval choose! 42";
    let complete = execute_graph(
        &imported,
        compilation.clone(),
        &[
            (
                "Main",
                "prelude\nimport Early\ndef chosen : Nat := choose! 43",
            ),
            ("Early", early),
        ],
        SourceProgramLimits::new(execution_limits()),
        MacroRegistryLimits::default(),
        None,
    );
    let Outcome::Complete(Ok(program)) = &complete.outcome else {
        panic!("{complete:?}");
    };
    assert_eq!(program.modules.len(), 2);
    assert_declared_value(&program.modules[1].commands.batch.engine, "chosen", 43);
    assert_eq!(complete.attempts.len(), 3);
    assert_eq!(complete.states.as_ref().unwrap().len(), 2);

    let malformed = execute_graph(
        &imported,
        compilation.clone(),
        &[
            (
                "Main",
                "prelude\nimport Early\ndef broken : Nat := choose! (",
            ),
            ("Early", early),
        ],
        SourceProgramLimits::new(execution_limits()),
        MacroRegistryLimits::default(),
        None,
    );
    assert!(
        matches!(
            &malformed.outcome,
            Outcome::Complete(Err(SourceProgramExecutionError::Source(
                SourceModuleCheckError::Source { module, .. }
            ))) if module == &name("Main")
        ),
        "{malformed:?}"
    );
    assert!(malformed.attempts.is_empty());
    assert_eq!(malformed.completed_vm_usage.steps, 0);
    assert!(malformed.states.is_none());

    let mut limits = SourceProgramLimits::new(execution_limits());
    limits.modules.source.max_commands = 2;
    let limited = execute_graph(
        &imported,
        compilation,
        &[
            (
                "Main",
                "prelude\nimport Early\ndef chosen : Nat := choose! 43",
            ),
            ("Early", early),
        ],
        limits,
        MacroRegistryLimits::default(),
        None,
    );
    assert!(
        matches!(
            &limited.outcome,
            Outcome::Complete(Err(SourceProgramExecutionError::Source(
                SourceModuleCheckError::Limit {
                    resource: "source commands",
                    limit: 2
                }
            )))
        ),
        "{limited:?}"
    );
    assert!(limited.attempts.is_empty());
    assert_eq!(limited.completed_vm_usage.steps, 0);
    assert!(limited.states.is_none());
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
    assert!(!imported.engine.environment().contains(&name("first")));
    assert!(!imported.engine.environment().contains(&name("chosen")));
}

#[test]
fn imported_parser_resource_stops_and_cancellation_are_inconclusive_in_source_apis() {
    use crate::source_check::modules::{
        SourceModuleCheckLimits, SourceModuleDeferredMacroInputs, execution::SourceProgramLimits,
    };

    struct Cancel;
    impl fln_vm::interpreter::CancellationProbe for Cancel {
        fn is_cancelled(&self) -> bool {
            true
        }
    }

    let (imported, code) = fixture(Fault::None);
    let before = imported.engine.logical_root(&KVMap::new());
    let declarations = users(&code);
    let compilation =
        MacroCompilationInputs::new(code, VerifiedPartition::user_fixture(), declarations);
    let module = name("Main");
    let source = "prelude\nimport SourceLibrary\ndef chosen : Nat := choose! 42";
    for cancelled in [false, true] {
        let mut registry_limits = MacroRegistryLimits::default();
        if !cancelled {
            registry_limits.metadata.max_entries = 0;
        }
        let probe = Cancel;
        let cancellation =
            cancelled.then_some(&probe as &dyn fln_vm::interpreter::CancellationProbe);
        let checked = imported.check_source_modules_with_deferred_imported_macros(
            &[crate::SourceModuleInput {
                name: &module,
                source: source.as_bytes(),
            }],
            &module,
            &KVMap::new(),
            SourceModuleCheckLimits::new(crate::source_check::SourceCheckLimits::new(admission())),
            SourceModuleDeferredMacroInputs {
                compilation: compilation.clone(),
                registry_limits,
                context: context(),
                state: MacroState::default(),
                limits: MacroTreeLimits::default(),
            },
            cancellation,
        );
        assert!(
            matches!(checked.outcome, Outcome::Inconclusive(_)),
            "{checked:?}"
        );
        assert!(checked.attempts.is_empty());
        assert_eq!(checked.completed_vm_usage.steps, 0);
        assert!(checked.states.is_none());

        let executed = execute_graph(
            &imported,
            compilation.clone(),
            &[("Main", source)],
            SourceProgramLimits::new(execution_limits()),
            registry_limits,
            cancellation,
        );
        assert!(
            matches!(executed.outcome, Outcome::Inconclusive(_)),
            "{executed:?}"
        );
        assert!(executed.attempts.is_empty());
        assert_eq!(executed.completed_vm_usage.steps, 0);
        assert!(executed.states.is_none());
    }
    let recovered = execute_graph(
        &imported,
        compilation,
        &[("Main", source)],
        SourceProgramLimits::new(execution_limits()),
        MacroRegistryLimits::default(),
        None,
    );
    let Outcome::Complete(Ok(program)) = &recovered.outcome else {
        panic!("{recovered:?}");
    };
    assert_declared_value(&program.modules[0].commands.batch.engine, "chosen", 42);
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
}

#[test]
fn editing_public_checked_owner_metadata_cannot_replace_retained_parser_authority() {
    let (mut imported, code) = fixture(Fault::None);
    let before = imported.engine.logical_root(&KVMap::new());
    let constants = &mut imported.checked.modules[0].decoded.constants;
    let owner = constants
        .iter()
        .position(|owner| owner.name() == &name("SourceLibrary.chooseParser"))
        .unwrap();
    constants.remove(owner);
    let error = imported
        .prepare_imported_parsers(ParserRegistryLimits::default())
        .unwrap_err();
    assert!(!error.is_resource(), "{error}");
    let report = check(
        &imported,
        &code,
        &[(
            "Main",
            "prelude\nimport SourceLibrary\ndef prefix : Nat := choose! 42",
        )],
        MacroTreeLimits::default(),
        None,
    );
    assert!(
        matches!(report.outcome, Outcome::Complete(Err(_))),
        "{report:?}"
    );
    assert!(report.states.is_none());
    assert!(report.attempts.is_empty());
    assert!(!imported.engine.environment().contains(&name("prefix")));
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
}

#[test]
fn imported_parser_selection_is_explicit_atomic_and_reversible() {
    let (mut imported, code) = unselected_fixture(Fault::None);
    let before = imported.engine.logical_root(&KVMap::new());
    let source = "prelude\nimport SourceLibrary\n\
                  def chosen : Nat := choose! 42\n\
                  theorem chosen_ok : chosen = 42 := by rfl";
    let run = |imported: &SourceOleanImport| {
        check(
            imported,
            &code,
            &[("Main", source)],
            MacroTreeLimits::default(),
            None,
        )
    };
    let ordinary_error = |imported: &SourceOleanImport| {
        let module = name("Main");
        imported
            .check_source_modules(
                &[crate::SourceModuleInput {
                    name: &module,
                    source: source.as_bytes(),
                }],
                &module,
                &KVMap::new(),
                crate::source_check::modules::SourceModuleCheckLimits::new(
                    crate::source_check::SourceCheckLimits::new(admission()),
                ),
                None,
            )
            .unwrap_err()
    };
    let ordinary_before = format!("{:?}", ordinary_error(&imported));
    let unselected = run(&imported);
    assert!(matches!(unselected.outcome, Outcome::Complete(Err(_))));
    assert!(unselected.attempts.is_empty());
    assert!(unselected.states.is_none());

    imported
        .enable_imported_syntax(&[name("SourceLibrary")], ParserRegistryLimits::default())
        .unwrap();
    let selected = run(&imported);
    assert_declared_value(&succeeded(&selected).checked.engine, "chosen", 42);
    assert_eq!(selected.attempts.len(), 1);
    assert_eq!(
        format!("{:?}", ordinary_error(&imported)),
        ordinary_before,
        "selection only activates syntax on explicit imported-macro adapters"
    );

    for (modules, limits, resource) in [
        (
            vec![name("SourceLibrary"), name("MissingArtifact")],
            ParserRegistryLimits::default(),
            false,
        ),
        (
            vec![name("SourceLibrary"), name("SourceLibrary")],
            ParserRegistryLimits::default(),
            false,
        ),
        (
            vec![name("SourceLibrary")],
            ParserRegistryLimits {
                max_steps: 0,
                ..ParserRegistryLimits::default()
            },
            true,
        ),
    ] {
        let error = imported
            .enable_imported_syntax(&modules, limits)
            .unwrap_err();
        assert_eq!(error.is_resource(), resource, "{error}");
        let retained = run(&imported);
        assert_declared_value(&succeeded(&retained).checked.engine, "chosen", 42);
        assert_eq!(retained.attempts.len(), 1);
    }

    imported
        .enable_imported_syntax(&[], ParserRegistryLimits::default())
        .unwrap();
    let cleared = run(&imported);
    assert!(matches!(cleared.outcome, Outcome::Complete(Err(_))));
    assert!(cleared.attempts.is_empty());
    assert!(cleared.states.is_none());
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
    assert!(!imported.engine.environment().contains(&name("chosen")));
}

#[test]
fn unselected_parser_journals_cannot_block_existing_imported_macros() {
    for fault in [
        Fault::MalformedSuffix,
        Fault::UnsupportedSuffix,
        Fault::TokenBudgetSuffix,
    ] {
        let (mut imported, code) = unselected_fixture(fault);
        let before = imported.engine.logical_root(&KVMap::new());
        let ordinary = |imported: &SourceOleanImport| {
            check(
                imported,
                &code,
                &[(
                    "Main",
                    "prelude\nimport SourceLibrary\n\
                     def ordinary : Nat := 11 + 29\n\
                     theorem ordinary_ok : ordinary = 29 := by rfl",
                )],
                MacroTreeLimits::default(),
                None,
            )
        };
        let before_selection = ordinary(&imported);
        assert_declared_value(&succeeded(&before_selection).checked.engine, "ordinary", 29);
        assert!(!before_selection.attempts.is_empty());

        let error = imported
            .enable_imported_syntax(&[name("SourceLibrary")], ParserRegistryLimits::default())
            .unwrap_err();
        assert_eq!(
            error.is_resource(),
            matches!(fault, Fault::TokenBudgetSuffix),
            "{fault:?}: {error}"
        );
        if matches!(fault, Fault::TokenBudgetSuffix) {
            assert!(matches!(error, ParserRegistrationError::Limit(_)));
        }
        let after_refusal = ordinary(&imported);
        assert_declared_value(&succeeded(&after_refusal).checked.engine, "ordinary", 29);

        // A supported prefix in a selected journal must not survive a bad
        // later row, even when the source would never demand that later parser.
        let prefix = check(
            &imported,
            &code,
            &[(
                "Main",
                "prelude\nimport SourceLibrary\ndef prefix : Nat := choose! 42",
            )],
            MacroTreeLimits::default(),
            None,
        );
        assert!(matches!(prefix.outcome, Outcome::Complete(Err(_))));
        assert!(prefix.attempts.is_empty());
        assert!(prefix.states.is_none());
        assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
        assert!(!imported.engine.environment().contains(&name("ordinary")));
        assert!(!imported.engine.environment().contains(&name("prefix")));
    }
}

#[test]
fn selecting_user_syntax_retains_checked_helpers_without_selecting_ancestor_parsers() {
    let (mut imported, code) = unselected_fixture_with_dependency(Fault::None, true);
    let before = imported.engine.logical_root(&KVMap::new());
    let ancestor = imported
        .checked
        .modules
        .iter()
        .find(|module| module.name == name("ParserPrelude"))
        .unwrap();
    assert!(
        ancestor
            .declarations
            .iter()
            .any(|row| row.name == name("Lean.ParserDescr"))
    );
    assert!(
        ancestor
            .declarations
            .iter()
            .any(|row| row.name == name("ParserPrelude.unsupportedParser"))
    );
    imported
        .enable_imported_syntax(&[name("SourceLibrary")], ParserRegistryLimits::default())
        .unwrap();
    let run = |imported: &SourceOleanImport| {
        check(
            imported,
            &code,
            &[
                (
                    "Main",
                    "prelude\nimport Forward\n\
                     def chosen : Nat := choose! 42\n\
                     theorem chosen_ok : chosen = 42 := by rfl",
                ),
                ("Forward", "prelude\nimport SourceLibrary"),
            ],
            MacroTreeLimits::default(),
            None,
        )
    };
    let selected = run(&imported);
    assert_declared_value(&succeeded(&selected).checked.engine, "chosen", 42);
    assert_eq!(selected.attempts.len(), 1);
    assert_eq!(
        selected.states.as_ref().unwrap()[&name("Forward")].macro_scope,
        17,
        "the empty forwarder validates the same selected dependency product"
    );

    let error = imported
        .enable_imported_syntax(
            &[name("ParserPrelude"), name("SourceLibrary")],
            ParserRegistryLimits::default(),
        )
        .unwrap_err();
    assert!(matches!(error, ParserRegistrationError::Description { .. }));
    assert!(!error.is_resource(), "{error}");
    let retained = run(&imported);
    assert_declared_value(&succeeded(&retained).checked.engine, "chosen", 42);
    assert_eq!(retained.attempts.len(), 1);
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
    assert!(!imported.engine.environment().contains(&name("chosen")));
}
