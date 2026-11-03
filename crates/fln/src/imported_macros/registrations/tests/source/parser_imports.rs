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

#[derive(Clone, Copy, Debug)]
enum Fault {
    None,
    MalformedSuffix,
    UnsupportedSuffix,
}

fn constant(label: &str) -> Expr {
    Expr::const_(name(label), vec![])
}

fn apply(label: &str, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(constant(label), Expr::app)
}

fn string(text: &str) -> Expr {
    Expr::lit(Literal::Str(text.into()))
}

fn natural(value: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(value)))
}

fn literal_name(label: &str) -> Expr {
    label
        .split('.')
        .fold(constant("Lean.Name.anonymous"), |prefix, part| {
            apply("Lean.Name.str", [prefix, string(part)])
        })
}

fn definition(label: &str, type_: Expr, value: Expr) -> ConstantInfo {
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

fn scope(row: Obj, namespace: Option<&str>) -> Obj {
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
    constants.extend([
        definition(
            "SourceLibrary.chooseParser",
            constant(wire::PARSER_DESCR_TYPE),
            descriptor("SourceLibrary.choose", "choose!", false),
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
    rows.extend(parser_rows(
        "SourceLibrary.scopedChoice",
        "SourceLibrary.scopedParser",
        "scopedChoice!",
        Some("SourceScoped"),
    ));
    match fault {
        Fault::None => {}
        Fault::MalformedSuffix => rows.push(Obj::mk_nat(0)),
        Fault::UnsupportedSuffix => {
            constants.push(definition(
                "SourceLibrary.unsupportedParser",
                constant(wire::PARSER_DESCR_TYPE),
                descriptor("SourceLibrary.unsupportedKind", "unsupportedSyntax!", true),
            ));
            rows.extend(parser_rows(
                "SourceLibrary.unsupportedKind",
                "SourceLibrary.unsupportedParser",
                "unsupportedSyntax!",
                None,
            ));
        }
    }
    batches::artifact_import_fixture_with_parser_metadata(
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
    assert_eq!(
        report.states.as_ref().unwrap()[&name("Main")].macro_scope,
        18
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
    assert_eq!(
        report.states.as_ref().unwrap()[&name("Main")].macro_scope,
        19
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

    let (malformed, code) = fixture(Fault::MalformedSuffix);
    let before = malformed.engine.logical_root(&KVMap::new());
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
    assert_eq!(
        complete.states.as_ref().unwrap()[&name("Main")].macro_scope,
        19
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
        let (imported, code) = fixture(fault);
        let before = imported.engine.logical_root(&KVMap::new());
        if matches!(fault, Fault::MalformedSuffix) {
            assert!(matches!(
                imported.prepare_imported_parsers(ParserRegistryLimits::default()),
                Err(ParserRegistrationError::Decode { .. })
            ));
        }
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
