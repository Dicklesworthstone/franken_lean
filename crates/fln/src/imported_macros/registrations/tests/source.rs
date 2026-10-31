//! Source behavior through the real Engine elaborator and dual-check path.
//! Ownership fixtures below are synthetic caller inputs, as in the parent
//! registration tests. The live cell additionally compiles actual Lean macros;
//! neither fixture substitutes for production artifact admission.
use super::*;
use crate::imported_macros::source::{
    SourceMacroAdmission, SourceMacroCheck, SourceMacroError, SourceMacroEvaluation,
    SourceMacroEvaluationResult, SourceMacroInvocation,
};
use crate::{Engine, EngineAdmissionLimits};
use std::sync::Arc;

fn admission() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(crate::Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn bound_engine(module: &CheckedOleanModule) -> Engine {
    let seed = Engine::with_source_seed(admission())
        .unwrap()
        .into_complete()
        .unwrap();
    let environment = module
        .decoded
        .constants
        .iter()
        .fold(seed.environment().clone(), |environment, owner| {
            environment.add_decl(owner.clone()).unwrap()
        });
    // Only test fixtures can supply this ownership marker directly. The public
    // Engine adapter requires the production artifact import path to supply it.
    let mut engine = Engine::from_environment(environment);
    engine.imported_modules = Arc::new(BTreeSet::from([module.name.clone()]));
    engine
}

fn fixture() -> (Engine, RegisteredMacros, CheckedOleanModule) {
    let module = checked(
        "SourceLibrary",
        &[
            owner("SourceLibrary.right"),
            owner("SourceLibrary.skip"),
            owner("SourceLibrary.diagnostic"),
            owner("SourceLibrary.left"),
        ],
        &[],
    );
    let rows = journal(&[
        ("term_+_", "SourceLibrary.right", None),
        ("term_+_", "SourceLibrary.skip", None),
        ("term_-_", "SourceLibrary.diagnostic", None),
        ("term_+_", "SourceLibrary.left", Some("SourceScoped")),
    ]);
    let code = code(vec![
        selecting_function("SourceLibrary.right", 2),
        function("SourceLibrary.skip", Behavior::Unsupported),
        function("SourceLibrary.diagnostic", Behavior::Diagnostic),
        selecting_function("SourceLibrary.left", 0),
    ]);
    let registry = prepare(
        &[MacroRegistrationModule {
            checked: &module,
            extensions: &rows,
        }],
        &code,
    );
    (bound_engine(&module), registry, module)
}

fn run(
    engine: &Engine,
    registry: &RegisteredMacros,
    source: &[u8],
    limits: MacroTreeLimits,
    cancellation: Option<&dyn CancellationProbe>,
) -> SourceMacroCheck {
    engine.check_source_command_with_imported_macros(
        source,
        &KVMap::new(),
        admission(),
        SourceMacroInvocation {
            registry,
            context: &context(),
            state: MacroState {
                macro_scope: 17,
                ..MacroState::default()
            },
            lookup: None,
            limits,
            cancellation,
        },
    )
}

fn evaluate(
    engine: &Engine,
    registry: &RegisteredMacros,
    source: &[u8],
    limits: MacroTreeLimits,
    execution: crate::EngineExecutionLimits,
    cancellation: Option<&dyn CancellationProbe>,
) -> SourceMacroEvaluation {
    engine.evaluate_source_command_with_imported_macros(
        source,
        &KVMap::new(),
        execution,
        SourceMacroInvocation {
            registry,
            context: &context(),
            state: MacroState {
                macro_scope: 17,
                ..MacroState::default()
            },
            lookup: None,
            limits,
            cancellation,
        },
    )
}

fn execution_limits() -> crate::EngineExecutionLimits {
    crate::EngineExecutionLimits::new(crate::Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn admit(
    engine: &Engine,
    registry: &RegisteredMacros,
    source: &[u8],
    limits: MacroTreeLimits,
    admission_limits: EngineAdmissionLimits,
    cancellation: Option<&dyn CancellationProbe>,
) -> SourceMacroAdmission {
    engine.admit_source_declaration_with_imported_macros(
        source,
        &KVMap::new(),
        admission_limits,
        SourceMacroInvocation {
            registry,
            context: &context(),
            state: MacroState {
                macro_scope: 17,
                ..MacroState::default()
            },
            lookup: None,
            limits,
            cancellation,
        },
    )
}

fn admitted(
    report: &SourceMacroAdmission,
) -> &crate::imported_macros::source::SourceMacroAdmissionResult {
    let Outcome::Complete(Ok(result)) = &report.outcome else {
        panic!("{report:?}")
    };
    assert_eq!(
        result.admission.checker.ground,
        crate::CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
    );
    assert!(report.state.is_some());
    result
}

fn assert_declared_value(engine: &Engine, declaration: &str, expected: u64) {
    let source = format!("#eval {declaration}");
    let batch = engine
        .execute_source_commands_with_checks(source.as_bytes(), &KVMap::new(), execution_limits())
        .unwrap()
        .into_complete()
        .unwrap();
    let fln_vm::interpreter::VmExit::Returned(result) = &batch.batch.executions[0].exit else {
        panic!("{batch:?}")
    };
    assert!(result.value.is_scalar());
    assert_eq!(result.value.unbox() as u64, expected);
}

#[test]
fn imported_macros_admit_named_values_and_proofs_through_the_ordinary_authority() {
    let (engine, registry, _) = fixture();
    let before = engine.logical_root(&KVMap::new());
    let source = "-- λ🦀\r\ndef macroChosen : Nat := (7 + 11)\r\n".as_bytes();
    let report = admit(
        &engine,
        &registry,
        source,
        MacroTreeLimits::default(),
        admission(),
        None,
    );
    let result = admitted(&report);
    assert_eq!(result.parsed.reconstruct_original(), source);
    assert_eq!(result.admission.base_logical_root, before);
    assert_ne!(result.admission.result_logical_root, before);
    assert_eq!(report.attempts.len(), 2);
    assert_eq!(report.state.as_ref().unwrap().macro_scope, 19);
    assert_declared_value(&result.admission.engine, "macroChosen", 11);
    assert!(!engine.environment().contains(&name("macroChosen")));

    let proof_source = b"@[simp] theorem macroChosen_eq : macroChosen = 11 := by rfl";
    let proof = admit(
        &result.admission.engine,
        &registry,
        proof_source,
        MacroTreeLimits::default(),
        admission(),
        None,
    );
    let proof = admitted(&proof);
    assert!(matches!(
        proof.admission.declaration,
        crate::Declaration::Thm(_)
    ));
    let simple = proof
        .admission
        .engine
        .admit_source_declaration(
            b"theorem usingMacroChosen : macroChosen = 11 := by simp",
            &KVMap::new(),
            admission(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(
        matches!(simple.declaration, crate::Declaration::Thm(_)),
        "the macro path must install the theorem's simp attribute"
    );
    let false_proof = admit(
        &result.admission.engine,
        &registry,
        b"theorem falseMacroChosen : macroChosen = 18 := by rfl",
        MacroTreeLimits::default(),
        admission(),
        None,
    );
    assert!(matches!(
        false_proof.outcome,
        Outcome::Complete(Err(SourceMacroError::Frontend(_)))
    ));
    assert!(false_proof.state.is_none());
    assert!(
        !result
            .admission
            .engine
            .environment()
            .contains(&name("falseMacroChosen"))
    );

    let scoped = registry.activate_scoped(&name("SourceScoped")).unwrap();
    let left = admit(
        &engine,
        &scoped,
        b"def scopedMacroChosen : Nat := 7 + 11",
        MacroTreeLimits::default(),
        admission(),
        None,
    );
    assert_declared_value(&admitted(&left).admission.engine, "scopedMacroChosen", 7);
    let replay = admit(
        &engine,
        &registry,
        source,
        MacroTreeLimits::default(),
        admission(),
        None,
    );
    assert_eq!(
        admitted(&replay).admission.result_logical_root,
        result.admission.result_logical_root
    );
    assert_eq!(engine.logical_root(&KVMap::new()), before);
}

#[test]
fn macro_admission_keeps_local_helper_receipts_and_drops_failed_successors() {
    let (engine, registry, _) = fixture();
    let before = engine.logical_root(&KVMap::new());
    let report = admit(
        &engine,
        &registry,
        b"def macroHelper (n : Nat) : Nat := let helper (x : Nat) : Nat := x + 11; helper n",
        MacroTreeLimits::default(),
        admission(),
        None,
    );
    let result = admitted(&report);
    assert!(
        result.admission.admissions.len() >= 2,
        "the local helper must retain a separate admission receipt"
    );
    assert!(
        result
            .admission
            .admissions
            .iter()
            .all(|receipt| receipt.checker.ground
                == crate::CheckerAdmissionGround::BodyCheckedAgainstDeclaredType)
    );
    assert_declared_value(&result.admission.engine, "macroHelper 7", 11);
    for source in [
        b"def badMacro : Bool := 7 + 11".as_slice(),
        b"def badMacro : Nat := 7 - 11",
        b"def badMacro : Nat := let unused (x : Nat) : Bool := x; 7 + 11",
        b"#eval 7 + 11",
        b"#check Nat",
        b"def badMacro := 7\ndef alsoBad := 11",
        b"\xef\xbb\xbfdef badMacro := 7 + 11",
    ] {
        let failed = admit(
            &engine,
            &registry,
            source,
            MacroTreeLimits::default(),
            admission(),
            None,
        );
        assert!(
            matches!(failed.outcome, Outcome::Complete(Err(_))),
            "{failed:?}"
        );
        assert!(failed.state.is_none());
        assert!(!engine.environment().contains(&name("badMacro")));
    }
    struct Cancelled;
    impl CancellationProbe for Cancelled {
        fn is_cancelled(&self) -> bool {
            true
        }
    }
    let mut no_macro_work = MacroTreeLimits::default();
    no_macro_work.dispatch.execution.vm.max_steps = 0;
    for (limits, cancellation) in [
        (no_macro_work, None),
        (
            MacroTreeLimits::default(),
            Some(&Cancelled as &dyn CancellationProbe),
        ),
    ] {
        let failed = admit(
            &engine,
            &registry,
            b"def limitedMacro : Nat := 7 + 11",
            limits,
            admission(),
            cancellation,
        );
        assert!(
            matches!(failed.outcome, Outcome::Inconclusive(_)),
            "{failed:?}"
        );
        assert!(failed.state.is_none());
    }
    let term = fln_checker::term::TermBudget::new(0, 0).with_max_arena_nodes(0);
    let whnf = fln_checker::whnf::WhnfBudget::new(0, 0, term);
    let inference = fln_checker::infer::InferenceBudget::new(0, 0, term, term).with_whnf(whnf);
    let mut constrained = admission();
    constrained.checker.admission =
        crate::CheckerAdmissionBudget::new(inference, whnf, inference.defeq);
    let stopped = admit(
        &engine,
        &registry,
        b"def limitedMacro : Nat := 7 + 11",
        MacroTreeLimits::default(),
        constrained,
        None,
    );
    assert!(
        matches!(&stopped.outcome, Outcome::Complete(Err(SourceMacroError::Frontend(error))) if matches!(error.as_ref(), crate::EngineExecutionError::CouncilNoAnswer { summary } if summary.contains("fln-checker"))),
        "{stopped:?}"
    );
    assert!(stopped.state.is_none());
    assert!(!engine.environment().contains(&name("limitedMacro")));
    assert_eq!(engine.logical_root(&KVMap::new()), before);
}

#[test]
fn macro_admission_validates_import_binding_and_keeps_the_declaration_boundary() {
    let (engine, registry, _) = fixture();
    let mut ambient = engine.clone();
    ambient.imported_modules = Arc::new(BTreeSet::new());
    let failed = admit(
        &ambient,
        &registry,
        b"def ambientMacro : Nat := 7 + 11",
        MacroTreeLimits::default(),
        admission(),
        None,
    );
    assert!(matches!(
        failed.outcome,
        Outcome::Complete(Err(SourceMacroError::Binding(_)))
    ));
    assert!(failed.attempts.is_empty());
    assert!(failed.state.is_none());

    let module = checked("CommandBoundary", &[owner("CommandBoundary.unwrap")], &[]);
    let rows = journal(&[(
        "Lean.Parser.Command.declaration",
        "CommandBoundary.unwrap",
        None,
    )]);
    let code = code(vec![selecting_function("CommandBoundary.unwrap", 0)]);
    let registry = prepare(
        &[MacroRegistrationModule {
            checked: &module,
            extensions: &rows,
        }],
        &code,
    );
    let engine = bound_engine(&module);
    let before = engine.logical_root(&KVMap::new());
    let failed = admit(
        &engine,
        &registry,
        b"def escapedMacro : Nat := 11",
        MacroTreeLimits::default(),
        admission(),
        None,
    );
    assert!(
        matches!(
            failed.outcome,
            Outcome::Complete(Err(SourceMacroError::DeclarationRequired))
        ),
        "{failed:?}"
    );
    assert_eq!(failed.attempts.len(), 1);
    assert!(failed.state.is_none());
    assert!(!engine.environment().contains(&name("escapedMacro")));
    assert_eq!(engine.logical_root(&KVMap::new()), before);
}

fn evaluated_nat(report: &SourceMacroEvaluation, expected: u64) -> &SourceMacroEvaluationResult {
    let Outcome::Complete(Ok(result)) = &report.outcome else {
        panic!("{report:?}")
    };
    assert_eq!(result.execution.checker.schema, "fln.checker-admission/1");
    // Like ordinary #eval, the pin compiles an unsafe auxiliary. Its checker
    // receipt must record quarantine, never a proof of a safe logical body.
    assert_eq!(
        result.execution.checker.ground,
        crate::CheckerAdmissionGround::UnsafeQuarantine
    );
    assert!(
        matches!(result.execution.runtime_type.node(), ExprNode::Const { name: result, .. } if result == &name("Nat"))
    );
    assert!(matches!(
        &result.execution.declaration,
        crate::Declaration::Defn(declaration) if declaration.safety == DefinitionSafety::Unsafe
    ));
    let fln_vm::interpreter::VmExit::Returned(returned) = &result.execution.exit else {
        panic!("{report:?}")
    };
    assert!(returned.value.is_scalar());
    assert_eq!(returned.value.unbox() as u64, expected);
    assert!(!result.execution.flbc_artifact.is_empty());
    assert_ne!(
        result.execution.base_logical_root,
        result.execution.result_logical_root
    );
    assert!(report.state.is_some());
    result
}

#[test]
fn imported_source_macros_change_checked_vm_values_and_scoped_replays() {
    let (engine, registry, _) = fixture();
    let before = engine.logical_root(&KVMap::new());
    let source = "-- λ🦀\r\n#eval (7 + 11)\r\n".as_bytes();
    let ordinary = engine
        .execute_source_commands_with_checks(source, &KVMap::new(), execution_limits())
        .unwrap()
        .into_complete()
        .unwrap();
    let fln_vm::interpreter::VmExit::Returned(returned) = &ordinary.batch.executions[0].exit else {
        panic!("{ordinary:?}")
    };
    assert_eq!(returned.value.unbox(), 18);
    let run = |registry, source| {
        evaluate(
            &engine,
            registry,
            source,
            MacroTreeLimits::default(),
            execution_limits(),
            None,
        )
    };
    let report = run(&registry, source);
    let result = evaluated_nat(&report, 11);
    let crate::Declaration::Defn(evaluation) = &result.execution.declaration else {
        unreachable!()
    };
    let mut laundering = evaluation.clone();
    laundering.base.name = name("SourceLibrary.safeEvaluationLeak");
    laundering.value = Expr::const_(evaluation.base.name.clone(), Vec::new());
    laundering.safety = DefinitionSafety::Safe;
    let refused = result.execution.engine.admit_declaration(
        crate::Declaration::Defn(laundering),
        &KVMap::new(),
        admission(),
    );
    assert!(
        matches!(
            refused,
            Err(crate::EngineAdmissionError::KernelRejected { .. })
        ),
        "an evaluated unsafe declaration must not enter a safe body: {refused:?}"
    );
    assert_eq!(result.parsed.reconstruct_original(), source);
    assert_eq!(result.parsed.query_term_normalized(), Some("(7 + 11)"));
    assert_eq!(report.attempts.len(), 2);
    assert_eq!(report.state.as_ref().unwrap().macro_scope, 19);
    let replay = run(&registry, source);
    assert_eq!(
        evaluated_nat(&replay, 11).execution.flbc_artifact,
        result.execution.flbc_artifact
    );
    let scoped = registry.activate_scoped(&name("SourceScoped")).unwrap();
    let scoped_report = run(&scoped, source);
    evaluated_nat(&scoped_report, 7);
    assert_eq!(scoped_report.attempts.len(), 1);
    evaluated_nat(&run(&registry, source), 11);
    evaluated_nat(&run(&registry, b"#eval 7 + (11 + 13)"), 13);
    let plain = run(&registry, b"#eval 9");
    evaluated_nat(&plain, 9);
    assert!(plain.attempts.is_empty());
    assert_eq!(plain.state.as_ref().unwrap().macro_scope, 17);
    assert_eq!(engine.logical_root(&KVMap::new()), before);
}

#[test]
fn source_macro_evaluation_stops_preserve_state_and_recover() {
    let (engine, registry, _) = fixture();
    let before = engine.logical_root(&KVMap::new());
    for source in [
        b"#eval 7 - 11".as_slice(),
        b"#eval 7 + Missing",
        b"#eval Nat + Bool",
    ] {
        let report = evaluate(
            &engine,
            &registry,
            source,
            MacroTreeLimits::default(),
            execution_limits(),
            None,
        );
        assert!(
            matches!(report.outcome, Outcome::Complete(Err(_))),
            "{report:?}"
        );
        assert!(report.state.is_none());
        assert!(!report.attempts.is_empty());
    }
    let sorry = evaluate(
        &engine,
        &registry,
        b"#eval 0 + (sorry : Nat)",
        MacroTreeLimits::default(),
        execution_limits(),
        None,
    );
    // The small seed deliberately omits sorryAx. It refuses labeled `sorry`
    // during elaboration, before the later evaluation dependency guard.
    assert!(!engine.environment().contains(&name("sorryAx")));
    let Outcome::Complete(Err(SourceMacroError::Frontend(error))) = &sorry.outcome else {
        panic!("{sorry:?}");
    };
    assert!(
        matches!(error.as_ref(), crate::EngineExecutionError::Frontend(
            crate::DefinitionFrontendError::Elaborate(fln_elab::NatDefinitionElabError::Inference(
                fln_elab::source::SourceInferenceError::UnknownConstant(missing)
            ))
        ) if missing == &name("sorryAx")),
        "{sorry:?}"
    );
    assert!(sorry.state.is_none());
    for source in [
        b"#check 7".as_slice(),
        b"#guard true",
        b"def x := 7",
        b"#eval 7\n#eval 11",
    ] {
        let report = evaluate(
            &engine,
            &registry,
            source,
            MacroTreeLimits::default(),
            execution_limits(),
            None,
        );
        assert!(
            matches!(report.outcome, Outcome::Complete(Err(_))),
            "{report:?}"
        );
        assert!(report.state.is_none());
        assert!(report.attempts.is_empty());
    }
    let mut macro_limits = MacroTreeLimits::default();
    macro_limits.dispatch.execution.vm.max_steps = 0;
    let mut vm_limits = execution_limits();
    vm_limits.vm.max_steps = 0;
    struct Cancelled;
    impl CancellationProbe for Cancelled {
        fn is_cancelled(&self) -> bool {
            true
        }
    }
    for (macros, execution, cancellation) in [
        (macro_limits, execution_limits(), None),
        (MacroTreeLimits::default(), vm_limits, None),
        (
            MacroTreeLimits::default(),
            execution_limits(),
            Some(&Cancelled as &dyn CancellationProbe),
        ),
    ] {
        let report = evaluate(
            &engine,
            &registry,
            b"#eval 7 + 11",
            macros,
            execution,
            cancellation,
        );
        assert!(
            matches!(report.outcome, Outcome::Inconclusive(_)),
            "{report:?}"
        );
        assert!(report.state.is_none());
    }
    evaluated_nat(
        &evaluate(
            &engine,
            &registry,
            b"#eval 7 + 11",
            MacroTreeLimits::default(),
            execution_limits(),
            None,
        ),
        11,
    );
    assert_eq!(engine.logical_root(&KVMap::new()), before);
}

#[test]
fn expanded_evaluations_refuse_actual_sorry_dependencies_before_execution() {
    let (engine, registry, _) = fixture();
    // Admit the pin's actual polymorphic axiom telescope from source through
    // both checkers. Explicit application exercises the dependency guard
    // without requiring Lean.Name constructors to label the `sorry` syntax.
    let admitted = engine
        .admit_source_declaration(
            b"axiom sorryAx.{u} (a : Sort u) (synthetic : Bool) : a",
            &KVMap::new(),
            admission(),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    // The pin also marks sorryAx as extern lean_sorry. Without that metadata
    // ordinary source elaboration correctly rejects the bare axiom as
    // noncomputable before reaching the evaluation dependency check.
    let environment = fln_elab::externs::register(
        admitted.environment(),
        &name("sorryAx"),
        vec![fln_elab::externs::ExternEntry::Standard {
            backend: name("all"),
            symbol: "lean_sorry".to_owned(),
        }],
    )
    .unwrap();
    let mut engine = Engine::from_environment(environment);
    engine.imported_modules = Arc::clone(&admitted.imported_modules);
    let before = engine.logical_root(&KVMap::new());
    let ordinary = engine
        .execute_source_commands_with_checks(
            b"#eval sorryAx Nat false",
            &KVMap::new(),
            execution_limits(),
        )
        .unwrap_err();
    assert!(
        matches!(&ordinary, crate::EngineExecutionError::BatchCommand { error, .. }
            if matches!(error.as_ref(), crate::EngineExecutionError::EvaluationDependsOnSorry)),
        "{ordinary:?}"
    );
    let report = evaluate(
        &engine,
        &registry,
        b"#eval 0 + (sorryAx Nat false)",
        MacroTreeLimits::default(),
        execution_limits(),
        None,
    );
    assert!(
        matches!(&report.outcome, Outcome::Complete(Err(SourceMacroError::Frontend(error)))
            if matches!(error.as_ref(), crate::EngineExecutionError::EvaluationDependsOnSorry)),
        "{report:?}"
    );
    assert_eq!(report.attempts.len(), 2);
    assert!(report.state.is_none());
    assert_eq!(engine.logical_root(&KVMap::new()), before);
}

fn checked_constant<'a>(report: &'a SourceMacroCheck, expected: &str) -> &'a crate::SourceCheck {
    let Outcome::Complete(Ok(checked)) = &report.outcome else {
        panic!("{report:?}")
    };
    assert_eq!(
        checked.checker.ground,
        crate::CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
    );
    assert!(
        matches!(checked.checked_type.node(), ExprNode::Sort { level }
        if level.to_nat() == Some(1))
    );
    let crate::Declaration::Defn(declaration) = &checked.declaration else {
        panic!("a source check must validate a scratch definition")
    };
    assert!(
        matches!(declaration.value.node(), ExprNode::Const { name: value, .. }
        if value == &name(expected))
    );
    checked
}

#[test]
fn imported_ir_changes_a_real_source_query_and_preserves_original_coordinates() {
    let (engine, registry, _) = fixture();
    let options = KVMap::new();
    let before = engine.logical_root(&options);
    let source = "-- λ🦀\r\n#check (Nat + Bool)\r\n".as_bytes();
    assert!(
        engine
            .check_source_command(source, &options, admission())
            .is_err(),
        "the unchanged standalone path cannot add two types"
    );
    let report = run(&engine, &registry, source, MacroTreeLimits::default(), None);
    let checked = checked_constant(&report, "Bool");
    assert_eq!(checked.environment_root, before);
    assert_eq!(checked.parsed.reconstruct_original(), source);
    assert_eq!(checked.parsed.query_term_normalized(), Some("(Nat + Bool)"));
    assert!(!checked.parsed.query_is_identifier());
    assert_eq!(report.attempts.len(), 2);
    assert_eq!(report.attempts[0].declaration, name("SourceLibrary.skip"));
    assert_eq!(report.attempts[1].declaration, name("SourceLibrary.right"));
    let state = report.state.as_ref().unwrap();
    assert_eq!(state.macro_scope, 19);
    assert_eq!(
        state.expanded_macro_declarations,
        [name("SourceLibrary.right")]
    );
    assert!(report.completed_vm_usage.steps > 0);
    assert_eq!(engine.logical_root(&options), before);

    let scoped = registry.activate_scoped(&name("SourceScoped")).unwrap();
    let scoped_report = run(
        &engine,
        &scoped,
        b"#check Nat + Bool",
        MacroTreeLimits::default(),
        None,
    );
    checked_constant(&scoped_report, "Nat");
    assert_eq!(scoped_report.attempts.len(), 1);
    assert_eq!(
        scoped_report.attempts[0].declaration,
        name("SourceLibrary.left")
    );
    checked_constant(
        &run(
            &engine,
            &registry,
            b"#check Nat + Bool",
            MacroTreeLimits::default(),
            None,
        ),
        "Bool",
    );
    assert_eq!(engine.logical_root(&options), before);
}

#[test]
fn source_bom_refusal_precedes_imported_macro_execution() {
    let (engine, registry, _) = fixture();
    let options = KVMap::new();
    let before = engine.logical_root(&options);
    // The pinned Reference rejects U+FEFF as an unexpected token at byte zero;
    // SourceView preserves it rather than treating it as whitespace. Keep that
    // lexical refusal even when imported macros could change the later term.
    let source = b"\xef\xbb\xbf#check (Nat + Bool)\r\n";
    let report = run(&engine, &registry, source, MacroTreeLimits::default(), None);
    let Outcome::Complete(Err(SourceMacroError::Frontend(error))) = &report.outcome else {
        panic!("{report:?}");
    };
    let crate::EngineExecutionError::Frontend(crate::DefinitionFrontendError::Parse(
        fln_parse::NatDefinitionParseError::Lexical { diagnostics },
    )) = error.as_ref()
    else {
        panic!("{error:?}");
    };
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].at, fln_parse::BytePos(0));
    assert!(report.attempts.is_empty());
    assert!(report.state.is_none());
    assert_eq!(report.completed_vm_usage.steps, 0);
    assert_eq!(engine.logical_root(&options), before);
}

#[test]
fn source_binding_rejects_ambient_foreign_and_changed_owners_before_execution() {
    let (engine, registry, module) = fixture();
    let mut foreign = engine.clone();
    foreign.imported_modules = Arc::new(BTreeSet::from([name("OtherLibrary")]));
    let ambient = Engine::from_environment(engine.environment().clone());
    let mut changed = module.decoded.constants.clone();
    let ConstantInfo::Defn(owner) = &mut changed[0] else {
        unreachable!()
    };
    owner.value = Expr::lit(Literal::Nat(NatLit::from_u64(99)));
    let changed = checked("SourceLibrary", &changed, &[]);
    let changed = bound_engine(&changed);
    let inactive = registry.activate_scoped(&name("UnusedNamespace")).unwrap();
    for engine in [&foreign, &ambient, &changed] {
        for registry in [&registry, &inactive] {
            let before = engine.logical_root(&KVMap::new());
            let report = run(
                engine,
                registry,
                b"#check Nat + Bool",
                MacroTreeLimits::default(),
                None,
            );
            assert!(matches!(
                report.outcome,
                Outcome::Complete(Err(SourceMacroError::Binding(_)))
            ));
            assert!(report.attempts.is_empty());
            assert!(report.state.is_none());
            assert_eq!(report.completed_vm_usage.steps, 0);
            assert_eq!(engine.logical_root(&KVMap::new()), before);
        }
    }
}

#[test]
fn source_diagnostics_and_budgets_publish_neither_checks_nor_partial_state() {
    let (engine, registry, _) = fixture();
    let before = engine.logical_root(&KVMap::new());
    let diagnostic = run(
        &engine,
        &registry,
        b"#check Nat - Bool",
        MacroTreeLimits::default(),
        None,
    );
    assert!(matches!(
        &diagnostic.outcome,
        Outcome::Complete(Err(SourceMacroError::Diagnostic {
            declaration, reference, message, ..
        })) if declaration == &name("SourceLibrary.diagnostic")
            && reference.kind() == Some(&name("term_-_"))
            && message == "λ\0diagnostic"
    ));
    assert_eq!(diagnostic.attempts.len(), 1);
    assert!(diagnostic.state.is_none());

    let baseline = run(
        &engine,
        &registry,
        b"#check Nat + Bool",
        MacroTreeLimits::default(),
        None,
    );
    checked_constant(&baseline, "Bool");
    let mut exact = MacroTreeLimits::default();
    exact.dispatch.execution.vm.max_steps = baseline.completed_vm_usage.steps;
    checked_constant(
        &run(&engine, &registry, b"#check Nat + Bool", exact, None),
        "Bool",
    );
    let mut short_steps = exact;
    short_steps.dispatch.execution.vm.max_steps -= 1;
    let mut short_attempts = MacroTreeLimits::default();
    short_attempts.dispatch.max_attempts = 1;
    let short_visits = MacroTreeLimits {
        max_visits: 0,
        ..MacroTreeLimits::default()
    };
    let mut short_source = MacroTreeLimits::default();
    short_source.dispatch.execution.syntax.max_bytes = 1;
    for limits in [short_steps, short_attempts, short_visits, short_source] {
        let report = run(&engine, &registry, b"#check Nat + Bool", limits, None);
        assert!(
            matches!(report.outcome, Outcome::Inconclusive(_)),
            "{report:?}"
        );
        assert!(report.state.is_none());
        assert_eq!(engine.logical_root(&KVMap::new()), before);
    }
    struct Cancelled;
    impl CancellationProbe for Cancelled {
        fn is_cancelled(&self) -> bool {
            true
        }
    }
    let cancelled = run(
        &engine,
        &registry,
        b"#check Nat + Bool",
        MacroTreeLimits::default(),
        Some(&Cancelled),
    );
    assert!(matches!(cancelled.outcome, Outcome::Inconclusive(_)));
    assert!(cancelled.attempts.is_empty());
    assert!(cancelled.state.is_none());
    checked_constant(
        &run(
            &engine,
            &registry,
            b"#check Nat + Bool",
            MacroTreeLimits::default(),
            None,
        ),
        "Bool",
    );
    assert_eq!(engine.logical_root(&KVMap::new()), before);
}

#[test]
fn source_shortcut_preserves_global_queries_and_refuses_unhandled_atomic_macros() {
    let module = checked("AtomicLibrary", &[owner("AtomicLibrary.fail")], &[]);
    let rows = journal(&[("ident", "AtomicLibrary.fail", None)]);
    let code = code(vec![function("AtomicLibrary.fail", Behavior::Diagnostic)]);
    let registry = prepare(
        &[MacroRegistrationModule {
            checked: &module,
            extensions: &rows,
        }],
        &code,
    );
    let engine = bound_engine(&module);
    let mut no_execution = MacroTreeLimits::default();
    no_execution.dispatch.max_attempts = 0;
    no_execution.dispatch.execution.vm.max_steps = 0;
    let global = run(&engine, &registry, b"#check Nat", no_execution, None);
    assert!(
        checked_constant(&global, "Nat")
            .parsed
            .query_is_identifier()
    );
    assert!(global.attempts.is_empty());
    assert_eq!(global.state.unwrap().macro_scope, 17);
    let evaluation = evaluate(
        &engine,
        &registry,
        b"#eval true",
        MacroTreeLimits::default(),
        execution_limits(),
        None,
    );
    assert!(matches!(
        evaluation.outcome,
        Outcome::Complete(Err(SourceMacroError::AtomicExpansion { .. }))
    ));
    assert!(
        evaluation.state.is_none(),
        "#eval must not take the #check existing-global shortcut"
    );
    let unknown = run(
        &engine,
        &registry,
        b"#check Missing",
        MacroTreeLimits::default(),
        None,
    );
    assert!(matches!(
        unknown.outcome,
        Outcome::Complete(Err(SourceMacroError::AtomicExpansion { kind }))
            if kind == name("ident")
    ));
    assert!(unknown.state.is_none());

    for source in [b"#eval 1".as_slice(), b"#synth Nat".as_slice()] {
        let wrong_command = run(&engine, &registry, source, MacroTreeLimits::default(), None);
        assert!(matches!(
            wrong_command.outcome,
            Outcome::Complete(Err(SourceMacroError::Frontend(error)))
                if matches!(*error, crate::EngineExecutionError::StandaloneCheckRequired)
        ));
        assert!(wrong_command.attempts.is_empty());
    }
}

#[test]
fn source_refuses_imported_tactics_left_for_the_tactic_evaluator() {
    let module = checked("TacticLibrary", &[owner("TacticLibrary.fail")], &[]);
    let rows = journal(&[("Lean.Parser.Tactic.tacticRfl", "TacticLibrary.fail", None)]);
    let code = code(vec![function("TacticLibrary.fail", Behavior::Diagnostic)]);
    let registry = prepare(
        &[MacroRegistrationModule {
            checked: &module,
            extensions: &rows,
        }],
        &code,
    );
    let engine = bound_engine(&module);
    let report = run(
        &engine,
        &registry,
        b"#check (by rfl : Nat = Nat)",
        MacroTreeLimits::default(),
        None,
    );
    assert!(
        matches!(
            &report.outcome,
            Outcome::Complete(Err(SourceMacroError::TacticExpansion { kind }))
                if kind == &name("Lean.Parser.Tactic.tacticRfl")
        ),
        "{report:?}"
    );
    assert!(report.attempts.is_empty());
    assert!(report.state.is_none());
}

#[test]
fn source_lookup_capability_defaults_to_the_engine_snapshot_and_allows_explicit_override() {
    use crate::imported_macros::lookup::EnvironmentMacroLookup;

    let module = checked(
        "SourceCapability",
        &[
            owner("SourceCapability.choose"),
            owner("SourceCapability.skip"),
        ],
        &[],
    );
    let rows = journal(&[
        ("term_+_", "SourceCapability.choose", None),
        ("term_+_", "SourceCapability.skip", None),
    ]);
    let code = code(vec![
        super::lookup::has_decl_selector("SourceCapability.choose"),
        function("SourceCapability.skip", Behavior::Unsupported),
    ]);
    let registry = prepare(
        &[MacroRegistrationModule {
            checked: &module,
            extensions: &rows,
        }],
        &code,
    );
    let engine = bound_engine(&module);
    let before = engine.logical_root(&KVMap::new());
    let source = b"#check Nat + (Nat + Bool)";

    // No embedding-supplied capability is necessary on the production source
    // path. The Engine binds its own immutable environment snapshot.
    let missing = run(&engine, &registry, source, MacroTreeLimits::default(), None);
    checked_constant(&missing, "Bool");
    assert_eq!(missing.attempts.len(), 4);
    assert!(missing.attempts.iter().any(|attempt| {
        attempt
            .native_functions
            .iter()
            .any(|id| id == "mirror:Lean.Macro.hasDecl")
    }));

    let successor = engine
        .admit_source_declaration(b"def available : Nat := 0", &KVMap::new(), admission())
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let after = successor.logical_root(&KVMap::new());
    let available = run(
        &successor,
        &registry,
        source,
        MacroTreeLimits::default(),
        None,
    );
    checked_constant(&available, "Nat");
    assert_eq!(available.attempts.len(), 2);

    // An explicit provider remains an invocation-local override. Supplying the
    // predecessor snapshot to the successor must not be silently replaced by
    // ambient authority from the newer Engine.
    let module_name = name("SourceQuery");
    let namespace = Name::anonymous();
    let stale_lookup = EnvironmentMacroLookup::new(engine.environment(), &module_name, &namespace);
    let stale = successor.check_source_command_with_imported_macros(
        source,
        &KVMap::new(),
        admission(),
        SourceMacroInvocation {
            registry: &registry,
            context: &context(),
            state: MacroState::default(),
            lookup: Some(&stale_lookup),
            limits: MacroTreeLimits::default(),
            cancellation: None,
        },
    );
    checked_constant(&stale, "Bool");

    checked_constant(
        &run(&engine, &registry, source, MacroTreeLimits::default(), None),
        "Bool",
    );
    assert_eq!(engine.logical_root(&KVMap::new()), before);
    assert_eq!(successor.logical_root(&KVMap::new()), after);
}

#[test]
fn source_expansion_does_not_bypass_the_independent_checker() {
    let (engine, registry, _) = fixture();
    let before = engine.logical_root(&KVMap::new());
    let term = fln_checker::term::TermBudget::new(0, 0).with_max_arena_nodes(0);
    let whnf = fln_checker::whnf::WhnfBudget::new(0, 0, term);
    let inference = fln_checker::infer::InferenceBudget::new(0, 0, term, term).with_whnf(whnf);
    let mut constrained = admission();
    constrained.checker.admission =
        crate::CheckerAdmissionBudget::new(inference, whnf, inference.defeq);
    let report = engine.check_source_command_with_imported_macros(
        b"#check Nat + Bool",
        &KVMap::new(),
        constrained,
        SourceMacroInvocation {
            registry: &registry,
            context: &context(),
            state: MacroState::default(),
            lookup: None,
            limits: MacroTreeLimits::default(),
            cancellation: None,
        },
    );
    assert!(
        matches!(
            &report.outcome,
            Outcome::Complete(Err(SourceMacroError::Frontend(error)))
                if matches!(error.as_ref(), crate::EngineExecutionError::CouncilNoAnswer { summary }
                    if summary.contains("fln-checker"))
        ),
        "{report:?}"
    );
    assert_eq!(report.attempts.len(), 2);
    assert!(report.state.is_none());
    assert_eq!(engine.logical_root(&KVMap::new()), before);
}

#[path = "source/reference.rs"]
mod reference;
