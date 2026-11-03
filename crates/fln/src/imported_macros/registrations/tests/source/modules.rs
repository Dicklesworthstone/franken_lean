//! Module-aware macro execution over actual admitted artifact journals. These
//! constructed compiler inputs test native integration, not Reference parity.
use super::*;
use crate::SourceModuleInput;
use crate::source_check::modules::imported::SourceOleanImport;
use crate::source_check::modules::{
    SourceMacroModuleCheck, SourceModuleCheck, SourceModuleCheckError, SourceModuleCheckLimits,
    SourceModuleMacroInputs,
};
use crate::source_check::{SourceCheckError, SourceCheckLimits};
use std::cell::Cell;

pub(super) fn check(
    imported: &SourceOleanImport,
    code: &[IrModule],
    files: &[(&str, &str)],
    limits: MacroTreeLimits,
    cancellation: Option<&dyn CancellationProbe>,
) -> SourceMacroModuleCheck {
    let names: Vec<_> = files.iter().map(|(label, _)| name(label)).collect();
    let inputs: Vec<_> = files
        .iter()
        .zip(&names)
        .map(|((_, source), name)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    imported.check_source_modules_with_imported_macros(
        &inputs,
        &name("Main"),
        &KVMap::new(),
        SourceModuleCheckLimits::new(SourceCheckLimits::new(admission())),
        SourceModuleMacroInputs {
            code,
            partition: &VerifiedPartition::user_fixture(),
            user_declarations: &users(code),
            registry_limits: MacroRegistryLimits::default(),
            context: context(),
            state: MacroState {
                macro_scope: 17,
                ..MacroState::default()
            },
            limits,
        },
        cancellation,
    )
}

pub(super) fn succeeded(report: &SourceMacroModuleCheck) -> &SourceModuleCheck {
    let Outcome::Complete(Ok(checked)) = &report.outcome else {
        panic!("{report:?}")
    };
    assert!(report.states.is_some());
    checked
}

/// Keep the input identifier's source metadata while selecting the quotation
/// context Name from the actual Macro.Context supplied by the module driver.
fn quotation_context_function() -> IrDecl {
    let mut declaration = function("SourceLibrary.preresolved", Behavior::Identity);
    let IrDecl::Function { body, .. } = &mut declaration else {
        unreachable!()
    };
    body.stmts = vec![
        bind(3, IrExpr::Lit(IrLit::Num(IrNat::Small(0)))),
        bind(
            4,
            IrExpr::Fap {
                function: name("Lean.Syntax.getArg"),
                args: vec![IrArg::Var(0), IrArg::Var(3)],
            },
        ),
        bind(5, IrExpr::Proj { i: 0, x: 4 }),
        bind(6, IrExpr::Proj { i: 1, x: 4 }),
        bind(
            7,
            IrExpr::Proj {
                i: layout::MACRO_CONTEXT_QUOTATION_FIELD as u64,
                x: 1,
            },
        ),
        bind(
            8,
            ctor(layout::SYNTAX_IDENT, "Lean.Syntax.ident", &[5, 6, 7, 3]),
        ),
        bind(9, ctor(layout::RESULT_OK, "EStateM.Result.ok", &[8, 2])),
    ];
    *body.terminal = IrTerminal::Ret(IrArg::Var(9));
    declaration
}

#[test]
fn module_macro_contexts_name_the_current_source_module() {
    let (imported, mut code) = batches::artifact_import_fixture();
    let declaration = code
        .iter_mut()
        .flat_map(|module| &mut module.decls)
        .find(|declaration| declaration.name() == &name("SourceLibrary.preresolved"))
        .unwrap();
    *declaration = quotation_context_function();
    let report = check(
        &imported,
        &code,
        &[
            (
                "Main",
                "prelude\nimport Lib\ndef Main : Nat := 41\n\
                 def fromMain : Nat := placeholder / 0\n\
                 theorem mainContext : fromMain = 41 := by rfl",
            ),
            (
                "Lib",
                "prelude\nimport SourceLibrary\ndef Lib : Nat := 31\n\
                 def fromLib : Nat := placeholder / 0\n\
                 theorem libContext : fromLib = 31 := by rfl",
            ),
        ],
        MacroTreeLimits::default(),
        None,
    );
    let checked = succeeded(&report);
    assert_eq!(checked.checked.theorems, 2);
    assert_eq!(report.attempts.len(), 2);
    for module in ["Lib", "Main"] {
        assert_eq!(
            report.states.as_ref().unwrap()[&name(module)].macro_scope,
            18
        );
    }
}

#[test]
fn module_macros_follow_import_closures_and_never_borrow_a_siblings_lookup_world() {
    let (imported, code) = batches::artifact_import_fixture();
    let before = imported.engine.logical_root(&KVMap::new());
    let files = [
        (
            "Main",
            "prelude\nimport A\nimport B\nimport C\n\
             def transitive : Nat := 7 + 11\n\
             def joinedLookup : Nat := 7 * 11\n\
             theorem aChecked : fromA = 11 := by rfl\n\
             theorem bChecked : ordinary = 18 := by rfl\n\
             theorem cChecked : isolatedLookup = 11 := by rfl",
        ),
        (
            "A",
            "prelude\nimport SourceLibrary\n\
             def available : Nat := 13\ndef fromA : Nat := 7 + 11",
        ),
        ("B", "prelude\ndef ordinary : Nat := 7 + 11"),
        (
            "C",
            "prelude\nimport SourceLibrary\ndef isolatedLookup : Nat := 7 * 11",
        ),
    ];
    let report = check(&imported, &code, &files, MacroTreeLimits::default(), None);
    let checked = succeeded(&report);
    assert_eq!(
        checked.module_order,
        [name("A"), name("B"), name("C"), name("Main")]
    );
    assert_eq!(checked.checked.files, 4);
    assert_eq!(checked.checked.theorems, 3);
    for (declaration, expected) in [
        ("fromA", 11),
        ("ordinary", 18),
        ("isolatedLookup", 11),
        ("transitive", 11),
        ("joinedLookup", 7),
    ] {
        assert_declared_value(&checked.checked.engine, declaration, expected);
    }
    assert_eq!(report.attempts.len(), 6);
    let states = report.states.as_ref().unwrap();
    for (module, scope) in [("A", 19), ("B", 17), ("C", 18), ("Main", 20)] {
        assert_eq!(states[&name(module)].macro_scope, scope, "{module}");
    }
    assert!(states[&name("B")].expanded_macro_declarations.is_empty());
    assert_eq!(
        states[&name("C")].expanded_macro_declarations,
        [name("SourceLibrary.hasDecl")]
    );
    let reordered = [files[3], files[1], files[0], files[2]];
    let repeated = check(
        &imported,
        &code,
        &reordered,
        MacroTreeLimits::default(),
        None,
    );
    assert_eq!(
        succeeded(&repeated).checked.result_logical_root,
        checked.checked.result_logical_root
    );
    assert_eq!(repeated.states, report.states);
    assert_eq!(repeated.completed_vm_usage, report.completed_vm_usage);
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
    assert!(!imported.engine.environment().contains(&name("available")));
}

#[test]
fn module_macros_restore_lexical_activation_and_restart_each_modules_state() {
    let (imported, code) = batches::artifact_import_fixture();
    let report = check(
        &imported,
        &code,
        &[
            (
                "Main",
                "prelude\nimport Lib\ndef nextModule : Nat := 7 + 11",
            ),
            (
                "Lib",
                "prelude\nimport SourceLibrary\n\
                 section\nopen scoped SourceScoped\n\
                 def inSection : Nat := 7 + 11\nend\n\
                 def restored : Nat := 7 + 11\n\
                 open scoped SourceScoped in\ndef once : Nat := 7 + 11\n\
                 def afterIn : Nat := 7 + 11\n\
                 open scoped SourceScoped\ndef finalScoped : Nat := 7 + 11",
            ),
        ],
        MacroTreeLimits::default(),
        None,
    );
    let checked = succeeded(&report);
    for (declaration, expected) in [
        ("inSection", 7),
        ("restored", 11),
        ("once", 7),
        ("afterIn", 11),
        ("finalScoped", 7),
        ("nextModule", 11),
    ] {
        assert_declared_value(&checked.checked.engine, declaration, expected);
    }
    assert_eq!(report.attempts.len(), 9);
    let states = report.states.as_ref().unwrap();
    assert_eq!(states[&name("Lib")].macro_scope, 24);
    assert_eq!(states[&name("Main")].macro_scope, 19);
    assert_eq!(
        states[&name("Main")].expanded_macro_declarations,
        [name("SourceLibrary.right")]
    );
    assert_eq!(checked.checked.scope.source_module, Some(name("Main")));
}

#[test]
fn module_macro_failures_preserve_original_header_offsets_and_publish_no_prefix() {
    let (imported, code) = batches::artifact_import_fixture();
    let before = imported.engine.logical_root(&KVMap::new());
    let library = "prelude\nimport SourceLibrary\ndef checkedPrefix : Nat := 7 + 11";
    let false_proof = check(
        &imported,
        &code,
        &[
            ("Lib", library),
            (
                "Main",
                "prelude\nimport Lib\ntheorem wrong : checkedPrefix = 18 := by rfl",
            ),
        ],
        MacroTreeLimits::default(),
        None,
    );
    assert!(
        matches!(&false_proof.outcome,
            Outcome::Complete(Err(SourceModuleCheckError::Source { module, error: SourceCheckError::Command { .. } }))
                if module == &name("Main")),
        "{false_proof:?}"
    );
    assert_eq!(false_proof.attempts.len(), 2);
    assert!(false_proof.states.is_none());

    let source = "-- λ🦀\r\nprelude\r\nimport Lib\r\n\
                  def good : Nat := checkedPrefix\r\n\
                  def bad : Nat := 7 - 11\r\n";
    let diagnostic = check(
        &imported,
        &code,
        &[("Main", source), ("Lib", library)],
        MacroTreeLimits::default(),
        None,
    );
    let Outcome::Complete(Err(SourceModuleCheckError::Source {
        module,
        error: SourceCheckError::ImportedMacro { offset, error, .. },
    })) = &diagnostic.outcome
    else {
        panic!("{diagnostic:?}")
    };
    assert_eq!(module, &name("Main"));
    assert_eq!(*offset, source.find("def bad").unwrap());
    let SourceMacroError::Diagnostic {
        reference, message, ..
    } = error.as_ref()
    else {
        panic!("{error:?}")
    };
    assert_eq!(message, "λ\0diagnostic");
    assert_eq!(reference.kind(), Some(&name("term_-_")));
    // Syntax retains its command-local normalized coordinates; the module error
    // carries the original file offset, including header bytes and CRLF pairs.
    let command = &source.as_bytes()[source.find("def bad").unwrap()..];
    let parsed = fln_parse::parse_source_command(command).unwrap();
    assert_eq!(parsed.reconstruct_original(), command);
    let mut pending = vec![parsed.syntax()];
    let expected = loop {
        let syntax = pending.pop().expect("the parsed subtraction node");
        if syntax.kind() == Some(&name("term_-_")) {
            break syntax;
        }
        if let Syntax::Node { args, .. } = syntax {
            pending.extend(args.iter().rev());
        }
    };
    assert_eq!(reference.as_ref(), expected);
    assert_eq!(diagnostic.attempts.len(), 3);
    assert!(diagnostic.states.is_none());
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
    assert!(
        !imported
            .engine
            .environment()
            .contains(&name("checkedPrefix"))
    );
    let recovered = check(
        &imported,
        &code,
        &[
            ("Lib", library),
            (
                "Main",
                "prelude\nimport Lib\ntheorem correct : checkedPrefix = 11 := by rfl",
            ),
        ],
        MacroTreeLimits::default(),
        None,
    );
    assert!(
        succeeded(&recovered)
            .checked
            .engine
            .environment()
            .contains(&name("correct"))
    );
}

#[test]
fn module_macros_share_attempt_instruction_visit_and_generation_budgets() {
    let (imported, code) = batches::artifact_import_fixture();
    let before = imported.engine.logical_root(&KVMap::new());
    let files = [
        ("Main", "prelude\nimport Lib\ndef second : Nat := 13 + 17"),
        (
            "Lib",
            "prelude\nimport SourceLibrary\ndef first : Nat := 7 + 11",
        ),
    ];
    let complete = check(&imported, &code, &files, MacroTreeLimits::default(), None);
    let expected = succeeded(&complete).checked.result_logical_root;
    assert_eq!(complete.attempts.len(), 4);
    let mut exact = MacroTreeLimits::default();
    exact.dispatch.max_attempts = complete.attempts.len() as u64;
    exact.dispatch.execution.vm.max_steps = complete.completed_vm_usage.steps;
    exact.max_visits = complete.tree_usage.visits;
    exact.generation.max_nodes = complete.tree_usage.generated_nodes;
    exact.generation.max_bytes = complete.tree_usage.generated_bytes;
    let repeated = check(&imported, &code, &files, exact, None);
    assert_eq!(succeeded(&repeated).checked.result_logical_root, expected);
    for resource in ["attempts", "steps", "visits", "nodes", "bytes"] {
        let mut limits = exact;
        match resource {
            "attempts" => limits.dispatch.max_attempts -= 1,
            "steps" => limits.dispatch.execution.vm.max_steps -= 1,
            "visits" => limits.max_visits -= 1,
            "nodes" => limits.generation.max_nodes -= 1,
            "bytes" => limits.generation.max_bytes -= 1,
            _ => unreachable!(),
        }
        let stopped = check(&imported, &code, &files, limits, None);
        assert!(
            matches!(stopped.outcome, Outcome::Inconclusive(_)),
            "{resource}: {stopped:?}"
        );
        assert!(stopped.states.is_none(), "{resource}");
        assert!(
            stopped.attempts.len() >= 2,
            "{resource}: the dependency executed"
        );
        assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
    }
}

#[test]
fn cancellation_after_module_macro_work_discards_all_successful_module_states() {
    struct Polls {
        count: Cell<usize>,
        stop_at: usize,
    }
    impl CancellationProbe for Polls {
        fn is_cancelled(&self) -> bool {
            let count = self.count.get() + 1;
            self.count.set(count);
            count >= self.stop_at
        }
    }
    let (imported, code) = batches::artifact_import_fixture();
    let before = imported.engine.logical_root(&KVMap::new());
    let files = [
        (
            "Main",
            "prelude\nimport Lib\ndef second : Nat := 13 + 17\n\
             theorem accepted : first = 11 := by rfl",
        ),
        (
            "Lib",
            "prelude\nimport SourceLibrary\ndef first : Nat := 7 + 11",
        ),
    ];
    let counter = Polls {
        count: Cell::new(0),
        stop_at: usize::MAX,
    };
    let complete = check(
        &imported,
        &code,
        &files,
        MacroTreeLimits::default(),
        Some(&counter),
    );
    let expected = succeeded(&complete).checked.result_logical_root;
    assert!(counter.count.get() > 2);
    let cancellation = Polls {
        count: Cell::new(0),
        stop_at: counter.count.get() - 2,
    };
    let stopped = check(
        &imported,
        &code,
        &files,
        MacroTreeLimits::default(),
        Some(&cancellation),
    );
    assert!(
        matches!(stopped.outcome, Outcome::Inconclusive(_)),
        "{stopped:?}"
    );
    assert!(stopped.attempts.len() >= 2);
    assert!(stopped.completed_vm_usage.steps > 0);
    assert!(stopped.states.is_none());
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
    assert!(!imported.engine.environment().contains(&name("first")));
    let recovered = check(&imported, &code, &files, MacroTreeLimits::default(), None);
    assert_eq!(succeeded(&recovered).checked.result_logical_root, expected);
}


fn execute_program(
    imported: &SourceOleanImport,
    code: &[IrModule],
    files: &[(&str, &str)],
    limits: MacroTreeLimits,
    cancellation: Option<&dyn CancellationProbe>,
) -> crate::source_check::modules::SourceMacroProgramExecution {
    let names: Vec<_> = files.iter().map(|(label, _)| name(label)).collect();
    let inputs: Vec<_> = files
        .iter()
        .zip(&names)
        .map(|((_, source), name)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    imported.execute_source_modules_with_imported_macros(
        &inputs,
        &name("Main"),
        &KVMap::new(),
        crate::source_check::modules::execution::SourceProgramLimits::new(execution_limits()),
        SourceModuleMacroInputs {
            code,
            partition: &VerifiedPartition::user_fixture(),
            user_declarations: &users(code),
            registry_limits: MacroRegistryLimits::default(),
            context: context(),
            state: MacroState {
                macro_scope: 17,
                ..MacroState::default()
            },
            limits,
        },
        cancellation,
        crate::EvaluationPresentation::Raw,
    )
}

fn executed(
    report: &crate::source_check::modules::SourceMacroProgramExecution,
) -> &crate::source_check::modules::execution::SourceProgramExecution {
    let Outcome::Complete(Ok(program)) = &report.outcome else {
        panic!("{report:?}")
    };
    assert!(report.states.is_some());
    program
}

fn program_values(
    program: &crate::source_check::modules::execution::SourceProgramExecution,
    module: &str,
) -> Vec<crate::ClosedVmValue> {
    let commands = &program
        .modules
        .iter()
        .find(|run| run.module == name(module))
        .unwrap()
        .commands;
    commands
        .batch
        .source_evaluation_indices
        .iter()
        .map(|index| {
            crate::closed_vm_value(&commands.batch.executions[*index].exit)
                .unwrap()
                .unwrap()
        })
        .collect()
}

#[test]
fn imported_macro_programs_execute_expansions_in_exact_module_and_scope_worlds() {
    let (imported, code) = batches::artifact_import_fixture();
    let before = imported.engine.logical_root(&KVMap::new());
    let files = [
        (
            "Main",
            "prelude\nimport A\nimport B\nimport Empty\n\
             #check unavailable + Nat\n\
             #eval fromA\n#eval ordinary\n#eval 7 + 11\n\
             open scoped SourceScoped in\n#eval 7 + 11\n\
             #eval 7 + 11",
        ),
        (
            "A",
            "prelude\nimport SourceLibrary\ndef fromA : Nat := 7 + 11",
        ),
        ("B", "prelude\ndef ordinary : Nat := 7 + 11"),
        ("Empty", "prelude"),
    ];
    let report = execute_program(&imported, &code, &files, MacroTreeLimits::default(), None);
    let program = executed(&report);
    assert_eq!(
        program
            .modules
            .iter()
            .map(|run| run.module.clone())
            .collect::<Vec<_>>(),
        vec![name("A"), name("B"), name("Empty"), name("Main")]
    );
    assert_eq!(
        program_values(program, "Main"),
        [11, 18, 11, 7, 11]
            .into_iter()
            .map(crate::ClosedVmValue::Scalar)
            .collect::<Vec<_>>()
    );
    let commands = &program.modules.last().unwrap().commands;
    assert_eq!(commands.checks.len(), 1);
    assert!(matches!(
        commands.checks[0].checked_type.node(),
        ExprNode::Sort { level } if level.to_nat() == Some(1)
    ));
    assert_declared_value(&commands.batch.engine, "fromA", 11);
    assert_declared_value(&commands.batch.engine, "ordinary", 18);
    assert_eq!(report.states.as_ref().unwrap()[&name("B")].macro_scope, 17);
    assert_eq!(report.states.as_ref().unwrap()[&name("Empty")].macro_scope, 17);
    assert!(report.completed_vm_usage.steps > 0);
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
    assert!(!imported.engine.environment().contains(&name("fromA")));
}

#[test]
fn imported_macro_programs_keep_expanded_public_and_mutual_admission_trees() {
    let (imported, code) = batches::artifact_import_fixture();
    let report = execute_program(
        &imported,
        &code,
        &[
            (
                "Main",
                "prelude\nimport Api\n\
                 mutual\n  def first : Nat := 7 + 11\n  def second : Nat := first\nend\n\
                 example : exposed = 11 := by exact correct\n\
                 #eval exposed\n#eval second",
            ),
            (
                "Api",
                "module\nprelude\npublic import SourceLibrary\n\
                 @[expose] public def exposed : Nat := 7 + 11\n\
                 public theorem correct : exposed = 11 := by rfl",
            ),
        ],
        MacroTreeLimits::default(),
        None,
    );
    let program = executed(&report);
    assert_eq!(
        program_values(program, "Main"),
        vec![crate::ClosedVmValue::Scalar(11), crate::ClosedVmValue::Scalar(11)]
    );
    assert_eq!(report.attempts.len(), 4, "each source macro runs once");
    let result = &program.modules.last().unwrap().commands.batch.engine;
    assert_declared_value(result, "exposed", 11);
    assert_declared_value(result, "first", 11);
    assert!(result.environment().contains(&name("correct")));
}

#[test]
fn imported_macro_program_failures_keep_source_positions_and_publish_no_prefix() {
    use crate::source_check::modules::execution::SourceProgramExecutionError;
    let (imported, code) = batches::artifact_import_fixture();
    let before = imported.engine.logical_root(&KVMap::new());
    let library = "prelude\nimport SourceLibrary\ndef checkedPrefix : Nat := 7 + 11";
    let source = "-- λ🦀\r\nprelude\r\nimport Lib\r\n#eval checkedPrefix\r\n#eval 7 - 11";
    let diagnostic = execute_program(
        &imported,
        &code,
        &[("Main", source), ("Lib", library)],
        MacroTreeLimits::default(),
        None,
    );
    let Outcome::Complete(Err(SourceProgramExecutionError::Source(
        SourceModuleCheckError::Source {
            module,
            error: SourceCheckError::Command { offset, error, .. },
        },
    ))) = &diagnostic.outcome else {
        panic!("{diagnostic:?}")
    };
    assert_eq!(module, &name("Main"));
    assert_eq!(*offset, source.find("#eval 7").unwrap());
    assert!(matches!(
        error.as_ref(),
        crate::EngineExecutionError::ImportedMacro {
            disposition: ("macro", false, 1),
            message,
        } if message.contains("diagnostic")
    ));
    assert_eq!(diagnostic.attempts.len(), 3);
    assert!(diagnostic.states.is_none());
    let bad_proof = execute_program(
        &imported,
        &code,
        &[
            ("Lib", library),
            ("Main", "prelude\nimport Lib\ntheorem wrong : checkedPrefix = 18 := by rfl"),
        ],
        MacroTreeLimits::default(),
        None,
    );
    assert!(matches!(bad_proof.outcome, Outcome::Complete(Err(_))), "{bad_proof:?}");
    assert!(bad_proof.states.is_none());
    assert_eq!(bad_proof.attempts.len(), 2);
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
    assert!(!imported.engine.environment().contains(&name("checkedPrefix")));
    let recovered = execute_program(
        &imported,
        &code,
        &[("Lib", library), ("Main", "prelude\nimport Lib\n#eval checkedPrefix")],
        MacroTreeLimits::default(),
        None,
    );
    assert_eq!(
        program_values(executed(&recovered), "Main"),
        vec![crate::ClosedVmValue::Scalar(11)]
    );
}

#[test]
fn imported_macro_programs_share_budgets_across_definition_and_evaluation_work() {
    let (imported, code) = batches::artifact_import_fixture();
    let files = [
        ("Main", "prelude\nimport Lib\n#eval 13 + 17"),
        ("Lib", "prelude\nimport SourceLibrary\ndef first : Nat := 7 + 11"),
    ];
    let complete = execute_program(&imported, &code, &files, MacroTreeLimits::default(), None);
    assert_eq!(
        program_values(executed(&complete), "Main"),
        vec![crate::ClosedVmValue::Scalar(17)]
    );
    assert_eq!(complete.attempts.len(), 4);
    let mut exact = MacroTreeLimits::default();
    exact.dispatch.max_attempts = complete.attempts.len() as u64;
    exact.dispatch.execution.vm.max_steps = complete.completed_vm_usage.steps;
    exact.max_visits = complete.tree_usage.visits;
    exact.generation.max_nodes = complete.tree_usage.generated_nodes;
    exact.generation.max_bytes = complete.tree_usage.generated_bytes;
    let repeated = execute_program(&imported, &code, &files, exact, None);
    assert_eq!(
        program_values(executed(&repeated), "Main"),
        vec![crate::ClosedVmValue::Scalar(17)]
    );
    assert_eq!(repeated.states, complete.states);
    for resource in ["attempts", "steps", "visits", "nodes", "bytes"] {
        let mut limits = exact;
        match resource {
            "attempts" => limits.dispatch.max_attempts -= 1,
            "steps" => limits.dispatch.execution.vm.max_steps -= 1,
            "visits" => limits.max_visits -= 1,
            "nodes" => limits.generation.max_nodes -= 1,
            "bytes" => limits.generation.max_bytes -= 1,
            _ => unreachable!(),
        }
        let stopped = execute_program(&imported, &code, &files, limits, None);
        assert!(matches!(stopped.outcome, Outcome::Inconclusive(_)), "{resource}: {stopped:?}");
        assert!(stopped.states.is_none());
        assert!(stopped.attempts.len() >= 2, "{resource}: dependency expansion ran");
    }
}

#[test]
fn imported_macro_programs_preserve_control_dispatch_and_template_refusals() {
    for (kind, source) in [
        ("Lean.Parser.Command.openScoped", "open scoped SourceScoped in\n#eval 7 + 11"),
        ("Lean.Parser.Command.in", "open scoped SourceScoped in\n#eval 7 + 11"),
        ("Lean.Parser.Command.section", "open scoped SourceScoped in\n#eval 7 + 11"),
        ("num", "set_option maxRecDepth 1024 in\n#eval 7 + 11"),
        ("Lean.Parser.Command.check", "#check 7 + 11"),
    ] {
        let (imported, code) = batches::artifact_import_fixture_with_extra_rows(&[
            (kind, "SourceLibrary.diagnostic", None),
        ]);
        let source = format!("prelude\nimport SourceLibrary\n{source}");
        let stopped = execute_program(
            &imported, &code, &[("Main", &source)], MacroTreeLimits::default(), None,
        );
        assert!(matches!(stopped.outcome, Outcome::Complete(Err(_))), "{kind}: {stopped:?}");
        assert!(stopped.attempts.is_empty(), "{kind}");
        assert!(stopped.states.is_none());
    }
    let (imported, code) = batches::artifact_import_fixture();
    let source = "prelude\nimport SourceLibrary\nnotation \"seven\" => 7\n#eval seven";
    let stopped = execute_program(
        &imported, &code, &[("Main", source)], MacroTreeLimits::default(), None,
    );
    assert!(matches!(stopped.outcome, Outcome::Complete(Err(_))), "{stopped:?}");
    assert!(stopped.states.is_none());
}

#[test]
fn imported_macro_program_validation_stops_successors_and_withholds_macro_states() {
    use crate::source_check::modules::execution::{
        SourceProgramExecutionError, SourceProgramLimits,
    };
    let (imported, code) = batches::artifact_import_fixture();
    let names = [name("Lib"), name("Main")];
    let inputs = [
        SourceModuleInput {
            name: &names[0],
            source: b"prelude\nimport SourceLibrary\n#eval 7 + 11",
        },
        SourceModuleInput {
            name: &names[1],
            source: b"prelude\nimport Lib\n#eval 13 + 17",
        },
    ];
    let mut visited = Vec::new();
    let stopped = imported.execute_lean_source_modules_with_imported_macros_and_validation(
        &inputs,
        &names[1],
        &KVMap::new(),
        SourceProgramLimits::new(execution_limits()),
        SourceModuleMacroInputs {
            code: &code,
            partition: &VerifiedPartition::user_fixture(),
            user_declarations: &users(&code),
            registry_limits: MacroRegistryLimits::default(),
            context: context(),
            state: MacroState::default(),
            limits: MacroTreeLimits::default(),
        },
        None,
        crate::EvaluationPresentation::Raw,
        &mut |module, commands| {
            visited.push(module.clone());
            assert_eq!(commands.batch.source_evaluation_indices.len(), 1);
            Err("reject this module")
        },
    );
    assert!(matches!(&stopped.outcome,
        Outcome::Complete(Err(SourceProgramExecutionError::Validation { module, error }))
            if module == &names[0] && *error == "reject this module"
    ), "{stopped:?}");
    assert_eq!(visited, vec![name("Lib")]);
    assert_eq!(stopped.attempts.len(), 2);
    assert!(stopped.states.is_none());
}

#[test]
fn cancellation_after_macro_program_execution_withholds_successful_module_states() {
    struct Polls {
        count: Cell<usize>,
        stop_at: usize,
    }
    impl CancellationProbe for Polls {
        fn is_cancelled(&self) -> bool {
            let count = self.count.get() + 1;
            self.count.set(count);
            count >= self.stop_at
        }
    }
    let (imported, code) = batches::artifact_import_fixture();
    let files = [
        ("Main", "prelude\nimport Lib\n#eval 13 + 17"),
        ("Lib", "prelude\nimport SourceLibrary\ndef first : Nat := 7 + 11"),
    ];
    let counter = Polls { count: Cell::new(0), stop_at: usize::MAX };
    let complete = execute_program(
        &imported, &code, &files, MacroTreeLimits::default(), Some(&counter),
    );
    executed(&complete);
    let cancel = Polls { count: Cell::new(0), stop_at: counter.count.get() - 1 };
    let stopped = execute_program(
        &imported, &code, &files, MacroTreeLimits::default(), Some(&cancel),
    );
    assert!(matches!(stopped.outcome, Outcome::Inconclusive(_)), "{stopped:?}");
    assert!(stopped.attempts.len() >= 2);
    assert!(stopped.completed_vm_usage.steps > 0);
    assert!(stopped.states.is_none());
}
