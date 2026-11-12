//! Module-aware macro execution over actual admitted artifact journals. These
//! constructed compiler inputs test native integration, not Reference parity.
use super::*;
use crate::SourceModuleInput;
use crate::source_check::modules::imported::SourceOleanImport;
use crate::source_check::modules::{
    SourceMacroModuleCheck, SourceModuleCheck, SourceModuleCheckError, SourceModuleCheckLimits,
    SourceModuleDeferredMacroInputs, SourceModuleMacroInputs,
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
        // Each module runs one macro and one native rfl; evalTactic always
        // allocates its fresh scope (pin Tactic/Basic.lean:194).
        assert_eq!(
            report.states.as_ref().unwrap()[&name(module)].macro_scope,
            17 + 1 + 1
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
    // Only Main has native tactic calls: its three rfl proofs each allocate
    // evalTactic's fresh scope in addition to the three macro attempts.
    for (module, scope) in [("A", 19), ("B", 17), ("C", 18), ("Main", 20 + 3)] {
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
    execute_program_with_presentation(
        imported,
        code,
        files,
        limits,
        cancellation,
        crate::EvaluationPresentation::Raw,
    )
}

fn execute_program_with_presentation(
    imported: &SourceOleanImport,
    code: &[IrModule],
    files: &[(&str, &str)],
    limits: MacroTreeLimits,
    cancellation: Option<&dyn CancellationProbe>,
    presentation: crate::EvaluationPresentation,
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
        presentation,
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
    assert_eq!(
        report.states.as_ref().unwrap()[&name("Empty")].macro_scope,
        17
    );
    assert!(report.completed_vm_usage.steps > 0);
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
    assert!(!imported.engine.environment().contains(&name("fromA")));
}

#[test]
fn imported_macro_queries_expand_reduction_and_instance_terms() {
    let (imported, code) = batches::artifact_import_fixture();
    let before = imported.engine.logical_root(&KVMap::new());
    let source = "prelude\nimport SourceLibrary\n\
        class QueryClass where\n  value : Nat\n\
        instance queryInstance : QueryClass := QueryClass.mk 42\n\
        def available : Nat := 19\n\
        #reduce (types := false) (proofs := false) 7 + 11\n\
        open scoped SourceScoped in\n#reduce 7 + 11\n\
        #reduce unavailable / 0\n\
        #synth Missing + QueryClass\n";
    let report = execute_program(
        &imported,
        &code,
        &[("Main", source)],
        MacroTreeLimits::default(),
        None,
    );
    let program = executed(&report);
    let commands = &program.modules.last().unwrap().commands;
    assert_eq!(commands.checks.len(), 4);
    assert!(commands.batch.source_evaluation_indices.is_empty());
    for (checked, expected) in commands.checks[..2].iter().zip([11, 7]) {
        let crate::Declaration::Defn(declaration) = &checked.declaration else {
            panic!("a reduction query checks a scratch definition");
        };
        assert_eq!(
            declaration.value,
            Expr::lit(Literal::Nat(NatLit::from_u64(expected)))
        );
        assert_eq!(
            checked.parsed.syntax().kind(),
            Some(&name("Lean.reduceCmd"))
        );
        assert_eq!(checked.parsed.query_term_normalized(), Some("7 + 11"));
    }
    let fln_syntax::tree::Syntax::Node { args, .. } = commands.checks[0].parsed.syntax() else {
        panic!("canonical reduction command");
    };
    assert_eq!(args.len(), 3);
    assert_eq!(args[1].kind(), Some(&name("Lean.reduceConfig")));
    let crate::Declaration::Defn(hygienic) = &commands.checks[2].declaration else {
        panic!("a reduction query checks a scratch definition");
    };
    assert_eq!(
        hygienic.value,
        Expr::lit(Literal::Nat(NatLit::from_u64(19)))
    );
    assert!(matches!(
        commands.checks[2].parsed.query_term_syntax(),
        Some(fln_syntax::tree::Syntax::Ident { val, preresolved, .. })
            if val == &name("unavailable") && !preresolved.is_empty()
    ));
    assert_eq!(
        commands.checks[2].parsed.query_term_normalized(),
        Some("unavailable / 0")
    );
    let instance = &commands.checks[3];
    let crate::Declaration::Defn(synthesized) = &instance.declaration else {
        panic!("instance synthesis checks a scratch definition");
    };
    assert_eq!(
        instance.checked_type,
        Expr::const_(name("QueryClass"), vec![])
    );
    assert_eq!(
        synthesized.value,
        Expr::const_(name("queryInstance"), vec![])
    );
    assert_eq!(
        instance.parsed.syntax().kind(),
        Some(&name("Lean.Parser.Command.synth"))
    );
    assert_eq!(
        instance.parsed.query_term_normalized(),
        Some("Missing + QueryClass")
    );
    let final_root = commands.batch.engine.logical_root(&KVMap::new());
    assert!(
        commands
            .checks
            .iter()
            .all(|checked| checked.environment_root == final_root)
    );
    assert!(report.completed_vm_usage.steps > 0);
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
    assert!(!imported.engine.environment().contains(&name("QueryClass")));
}

#[test]
fn imported_macro_queries_preserve_guard_presentation_and_scoped_boolean_results() {
    // The prelude-only library lacks Init.Guard. Admit its syntax-availability
    // declaration through the same checked artifact path as the macro owners.
    let guard = ConstantInfo::Defn(DefinitionVal {
        base: ConstantVal {
            name: name("Lean.Parser.Command.guardCmd"),
            level_params: vec![],
            type_: Expr::const_(name("Nat"), vec![]),
        },
        value: Expr::lit(Literal::Nat(NatLit::from_u64(0))),
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![name("Lean.Parser.Command.guardCmd")],
    });
    let (imported, code) =
        batches::artifact_import_fixture_with_parser_metadata(&[], &[guard], &[], &[]);
    let before = imported.engine.logical_root(&KVMap::new());
    let source = "prelude\nimport SourceLibrary\n\
        #guard false + true\n\
        open scoped SourceScoped in\n#guard false + true\n\
        #guard false + true\n";
    let report = execute_program_with_presentation(
        &imported,
        &code,
        &[("Main", source)],
        MacroTreeLimits::default(),
        None,
        crate::EvaluationPresentation::Lean,
    );
    let program = executed(&report);
    assert_eq!(
        program_values(program, "Main"),
        vec![
            crate::ClosedVmValue::Scalar(1),
            crate::ClosedVmValue::Scalar(0),
            crate::ClosedVmValue::Scalar(1),
        ]
    );
    let commands = &program.modules.last().unwrap().commands;
    for &index in &commands.batch.source_evaluation_indices {
        // The CLI uses this marker to require true and keep guards silent.
        // A false guard must not become an ordinary successful #eval result.
        assert_eq!(
            commands.batch.executions[index].evaluation_presentation(),
            Some(crate::EvaluationResultPresentation::Guard)
        );
    }
    let rejected = execute_program_with_presentation(
        &imported,
        &code,
        &[("Main", "prelude\nimport SourceLibrary\n#guard 7 + 11")],
        MacroTreeLimits::default(),
        None,
        crate::EvaluationPresentation::Lean,
    );
    assert!(
        matches!(rejected.outcome, Outcome::Complete(Err(_))),
        "{rejected:?}"
    );
    assert!(!rejected.attempts.is_empty());
    assert!(rejected.states.is_none());
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
}

#[test]
fn imported_macro_queries_do_not_bypass_atomic_macros_for_existing_globals() {
    let (imported, code) = batches::artifact_import_fixture_with_extra_rows(&[(
        "ident",
        "SourceLibrary.diagnostic",
        None,
    )]);
    let checked = execute_program(
        &imported,
        &code,
        &[("Main", "prelude\nimport SourceLibrary\n#check Nat")],
        MacroTreeLimits::default(),
        None,
    );
    assert_eq!(
        executed(&checked)
            .modules
            .last()
            .unwrap()
            .commands
            .checks
            .len(),
        1
    );
    assert!(checked.attempts.is_empty());
    for command in ["#reduce Nat", "#synth Nat"] {
        let source = format!("prelude\nimport SourceLibrary\n{command}");
        let rejected = execute_program(
            &imported,
            &code,
            &[("Main", &source)],
            MacroTreeLimits::default(),
            None,
        );
        assert!(
            matches!(rejected.outcome, Outcome::Complete(Err(_))),
            "{command}: {rejected:?}"
        );
        assert!(rejected.states.is_none());
        assert!(
            rejected
                .attempts
                .iter()
                .any(|attempt| attempt.declaration == name("SourceLibrary.diagnostic")),
            "{command}: {rejected:?}"
        );
    }
}

#[test]
fn imported_macro_queries_share_limits_and_withhold_partial_states() {
    let (imported, code) = batches::artifact_import_fixture();
    let source = "prelude\nimport SourceLibrary\n#reduce 7 + 11\n#reduce 13 + 17";
    let files = [("Main", source)];
    let complete = execute_program(&imported, &code, &files, MacroTreeLimits::default(), None);
    assert_eq!(
        executed(&complete)
            .modules
            .last()
            .unwrap()
            .commands
            .checks
            .len(),
        2
    );
    assert_eq!(complete.attempts.len(), 4);
    let mut limits = MacroTreeLimits::default();
    limits.dispatch.max_attempts = 3;
    let stopped = execute_program(&imported, &code, &files, limits, None);
    assert!(
        matches!(stopped.outcome, Outcome::Inconclusive(_)),
        "{stopped:?}"
    );
    assert_eq!(stopped.attempts.len(), 3);
    assert!(stopped.states.is_none());
    let recovered = execute_program(&imported, &code, &files, MacroTreeLimits::default(), None);
    assert_eq!(recovered.states, complete.states);
    assert_eq!(recovered.completed_vm_usage, complete.completed_vm_usage);
}

#[test]
fn mixed_macro_programs_replay_native_templates_through_source_imports() {
    let (imported, code) = batches::artifact_import_fixture();
    let before = imported.engine.logical_root(&KVMap::new());
    let files = [
        (
            "Main",
            "prelude\nimport Forward\n\
             def throughBoth : Nat := 0 + libraryValue\n\
             #eval throughBoth\n#eval sourceToImported\n#eval 0 + libraryPick[2]\n\
             #eval 0 + libraryValue\n\
             section\nlocal macro_rules | `(libraryValue) => `(23)\n\
             #eval 0 + libraryValue\nend\n\
             #eval 0 + libraryValue",
        ),
        ("Forward", "prelude\nimport NativeLibrary\n"),
        (
            "NativeLibrary",
            "prelude\nimport SourceLibrary\n\
             macro \"libraryValue\" : term => `(17)\n\
             macro \"importedResult\" : term => `(7 + 11)\n\
             syntax \"libraryPick[\" num \"]\" : term\n\
             macro_rules | `(libraryPick[1]) => `(11) | `(libraryPick[2]) => `(22)\n\
             macro_rules | `(libraryPick[3]) => `(33)\n\
             def sourceToImported : Nat := importedResult",
        ),
    ];
    let report = execute_program(&imported, &code, &files, MacroTreeLimits::default(), None);
    let program = executed(&report);
    assert_eq!(
        program_values(program, "Main"),
        [17, 11, 22, 17, 23, 17]
            .into_iter()
            .map(crate::ClosedVmValue::Scalar)
            .collect::<Vec<_>>()
    );
    assert_eq!(
        report.states.as_ref().unwrap()[&name("Main")].macro_scope,
        33
    );
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
    assert!(!imported.engine.environment().contains(&name("throughBoth")));
}

#[test]
fn mixed_macro_module_checks_forward_templates_through_empty_modules() {
    let (imported, code) = batches::artifact_import_fixture();
    let report = check(
        &imported,
        &code,
        &[
            (
                "Main",
                "prelude\nimport Forward\n\
                 def fromImported : Nat := 0 + libraryValue\n\
                 theorem checkedBoth : fromImported = fromNative := by rfl",
            ),
            ("Forward", "prelude\nimport NativeLibrary\n"),
            (
                "NativeLibrary",
                "prelude\nimport SourceLibrary\n\
                 macro \"libraryValue\" : term => `(11)\n\
                 macro \"nativeToImported\" : term => `(7 + 11)\n\
                 def fromNative : Nat := nativeToImported",
            ),
        ],
        MacroTreeLimits::default(),
        None,
    );
    let checked = succeeded(&report);
    assert_eq!(checked.checked.theorems, 1);
    assert_declared_value(&checked.checked.engine, "fromImported", 11);
    assert_declared_value(&checked.checked.engine, "fromNative", 11);
    assert_eq!(report.attempts.len(), 6);
    let states = report.states.as_ref().unwrap();
    assert_eq!(states[&name("NativeLibrary")].macro_scope, 20);
    assert_eq!(states[&name("Forward")].macro_scope, 17);
    assert_eq!(states[&name("Main")].macro_scope, 21);
}

#[test]
fn mixed_dependent_application_guards_observe_actual_argument_expansions() {
    let (imported, code) = batches::artifact_import_fixture();
    let before = imported.engine.logical_root(&KVMap::new());
    let files = [(
        "Main",
        "prelude\nimport SourceLibrary\n\
         inductive W (P : Nat -> Type) : (n : Nat) -> P n -> Type where\n  | mk (n : Nat) (v : P n) : W P n v\n\
         section\nlocal macro_rules | `(true) => `(_)\n\
         def direct : W (fun _ => Bool) 3 Bool.true := W.mk 3 true\n\
         def tactic : W (fun _ => Bool) 3 Bool.true := by exact W.mk 3 true\n\
         end\nsection\n\
         local macro_rules | `(1) => `(5 + 2)\n\
         local macro_rules | `(2) => `(3)\n\
         local macro_rules | `(true) => `(_)\n\
         def chained : W (fun _ => Bool) 3 Bool.true := W.mk 1 true\n\
         end\n\
         theorem directChecked : Eq direct (@W.mk (fun _ => Bool) 3 Bool.true) := Eq.refl direct\n\
         theorem tacticChecked : Eq tactic direct := Eq.refl direct\n\
         theorem chainedChecked : Eq chained direct := Eq.refl direct",
    )];
    let report = check(&imported, &code, &files, MacroTreeLimits::default(), None);
    let checked = succeeded(&report);
    assert_eq!(checked.checked.theorems, 3);
    assert_eq!(
        report
            .attempts
            .iter()
            .filter(|attempt| attempt.declaration == name("SourceLibrary.right"))
            .count(),
        1,
        "the argument chain runs its admitted artifact macro once"
    );
    let repeated = check(&imported, &code, &files, MacroTreeLimits::default(), None);
    assert_eq!(
        succeeded(&repeated).checked.result_logical_root,
        checked.checked.result_logical_root
    );
    assert_eq!(repeated.states, report.states);
    assert_eq!(repeated.completed_vm_usage, report.completed_vm_usage);
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
}

#[test]
fn mixed_dependent_application_guards_reject_expanded_rigid_arguments() {
    use fln_elab::{NatDefinitionElabError, source::SourceInferenceError};

    let (imported, code) = batches::artifact_import_fixture();
    let before = imported.engine.logical_root(&KVMap::new());
    for body in ["W.mk 3 magic", "by exact W.mk 3 magic"] {
        let source = format!(
            "prelude\nimport SourceLibrary\n\
             inductive W (P : Nat -> Type) : (n : Nat) -> P n -> Type where\n  | mk (n : Nat) (v : P n) : W P n v\n\
             macro_rules | `(magic) => `(true)\n\
             def rejected : W (fun _ => Bool) 3 Bool.true := {body}"
        );
        let report = check(
            &imported,
            &code,
            &[("Main", source.as_str())],
            MacroTreeLimits::default(),
            None,
        );
        let Outcome::Complete(Err(SourceModuleCheckError::Source {
            module,
            error: SourceCheckError::Command { error, .. },
        })) = &report.outcome
        else {
            panic!("expanded dependent argument bypassed the guard: {report:?}")
        };
        assert_eq!(module, &name("Main"));
        assert!(
            matches!(
                error.as_ref(),
                crate::EngineExecutionError::Frontend(
                    crate::NatDefinitionFrontendError::Elaborate(
                        NatDefinitionElabError::Inference(
                            SourceInferenceError::TypeMismatch { .. }
                        )
                    )
                )
            ),
            "{body}: {error:?}"
        );
        assert!(!report.attempts.is_empty());
        assert!(report.states.is_none());
        assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
        assert!(!imported.engine.environment().contains(&name("rejected")));
    }
}

#[test]
fn mixed_dependent_application_guard_failures_allow_tactic_backtracking() {
    let (imported, code) = batches::artifact_import_fixture();
    let files = [(
        "Main",
        "prelude\nimport SourceLibrary\n\
         inductive W (P : Nat -> Type) : (n : Nat) -> P n -> Type where\n  | mk (n : Nat) (v : P n) : W P n v\n\
         section\nlocal macro_rules | `(magic) => `(true)\n\
         def recovered : W (fun _ => Bool) 3 Bool.true := by\n  first\n  | exact W.mk 3 magic\n  | exact W.mk (P := fun _ => Bool) 3 Bool.true\n\
         end\n\
         theorem recoveredChecked : Eq recovered (@W.mk (fun _ => Bool) 3 Bool.true) := Eq.refl recovered",
    )];
    let report = check(&imported, &code, &files, MacroTreeLimits::default(), None);
    let checked = succeeded(&report);
    assert_eq!(checked.checked.theorems, 1);
    assert!(
        report
            .attempts
            .iter()
            .any(|attempt| attempt.declaration.parent() == name("_fln.sourceTemplate.ident")),
        "the failed tactic candidate retains its macro work"
    );
    let repeated = check(&imported, &code, &files, MacroTreeLimits::default(), None);
    assert_eq!(
        succeeded(&repeated).checked.result_logical_root,
        checked.checked.result_logical_root
    );
    assert_eq!(repeated.states, report.states);
    assert_eq!(repeated.attempts.len(), report.attempts.len());
}

#[test]
fn mixed_program_grammar_declarations_do_not_bypass_active_atomic_macros() {
    let (imported, code) = batches::artifact_import_fixture_with_extra_rows(&[(
        "ident",
        "SourceLibrary.diagnostic",
        Some("SourceAtoms"),
    )]);
    let before = imported.engine.logical_root(&KVMap::new());
    let report = execute_program(
        &imported,
        &code,
        &[(
            "Main",
            "prelude\nimport SourceLibrary\n\
             macro \"existingValue\" : term => `(11)\n\
             def checkedPrefix : Nat := 0 + existingValue\n\
             open scoped SourceAtoms\n\
             macro \"blockedValue\" : term => `(11)",
        )],
        MacroTreeLimits::default(),
        None,
    );
    let Outcome::Complete(Err(error)) = &report.outcome else {
        panic!("native grammar declaration bypassed an active atomic macro");
    };
    assert!(
        format!("{error:?}").contains("generated-reference macro dispatch"),
        "{error:?}"
    );
    assert_eq!(report.attempts.len(), 3);
    assert!(report.states.is_none());
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
    assert!(
        !imported
            .engine
            .environment()
            .contains(&name("checkedPrefix"))
    );
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
        vec![
            crate::ClosedVmValue::Scalar(11),
            crate::ClosedVmValue::Scalar(11)
        ]
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
    ))) = &diagnostic.outcome
    else {
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
            (
                "Main",
                "prelude\nimport Lib\ntheorem wrong : checkedPrefix = 18 := by rfl",
            ),
        ],
        MacroTreeLimits::default(),
        None,
    );
    assert!(
        matches!(bad_proof.outcome, Outcome::Complete(Err(_))),
        "{bad_proof:?}"
    );
    assert!(bad_proof.states.is_none());
    assert_eq!(bad_proof.attempts.len(), 2);
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
    assert!(
        !imported
            .engine
            .environment()
            .contains(&name("checkedPrefix"))
    );
    let recovered = execute_program(
        &imported,
        &code,
        &[
            ("Lib", library),
            ("Main", "prelude\nimport Lib\n#eval checkedPrefix"),
        ],
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
        (
            "Lib",
            "prelude\nimport SourceLibrary\ndef first : Nat := 7 + 11",
        ),
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
        assert!(
            matches!(stopped.outcome, Outcome::Inconclusive(_)),
            "{resource}: {stopped:?}"
        );
        assert!(stopped.states.is_none());
        assert!(
            stopped.attempts.len() >= 2,
            "{resource}: dependency expansion ran"
        );
    }
}

#[test]
fn mixed_macro_programs_preserve_control_dispatch_and_accept_source_templates() {
    for (kind, source) in [
        (
            "Lean.Parser.Command.openScoped",
            "open scoped SourceScoped in\n#eval 7 + 11",
        ),
        (
            "Lean.Parser.Command.in",
            "open scoped SourceScoped in\n#eval 7 + 11",
        ),
        (
            "Lean.Parser.Command.section",
            "open scoped SourceScoped in\n#eval 7 + 11",
        ),
        ("num", "set_option maxRecDepth 1024 in\n#eval 7 + 11"),
        ("Lean.Parser.Command.check", "#check 7 + 11"),
        ("Lean.Parser.Command.synth", "#synth Nat + Bool"),
        ("Lean.reduceCmd", "#reduce (types := false) 7 + 11"),
        ("Lean.Parser.Command.guardCmd", "#guard false + true"),
    ] {
        let (imported, code) = batches::artifact_import_fixture_with_extra_rows(&[(
            kind,
            "SourceLibrary.diagnostic",
            None,
        )]);
        let source = format!("prelude\nimport SourceLibrary\n{source}");
        let stopped = execute_program(
            &imported,
            &code,
            &[("Main", &source)],
            MacroTreeLimits::default(),
            None,
        );
        assert!(
            matches!(stopped.outcome, Outcome::Complete(Err(_))),
            "{kind}: {stopped:?}"
        );
        assert!(stopped.attempts.is_empty(), "{kind}");
        assert!(stopped.states.is_none());
    }
    let (imported, code) = batches::artifact_import_fixture();
    let source = "prelude\nimport SourceLibrary\nnotation \"seven\" => 7\n#eval seven";
    let report = execute_program(
        &imported,
        &code,
        &[("Main", source)],
        MacroTreeLimits::default(),
        None,
    );
    assert_eq!(
        program_values(executed(&report), "Main"),
        vec![crate::ClosedVmValue::Scalar(7)]
    );
    assert_eq!(report.attempts.len(), 1);
    assert_eq!(
        report.states.as_ref().unwrap()[&name("Main")].macro_scope,
        18
    );
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
    assert!(
        matches!(&stopped.outcome,
            Outcome::Complete(Err(SourceProgramExecutionError::Validation { module, error }))
                if module == &names[0] && *error == "reject this module"
        ),
        "{stopped:?}"
    );
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
        (
            "Lib",
            "prelude\nimport SourceLibrary\ndef first : Nat := 7 + 11",
        ),
    ];
    let counter = Polls {
        count: Cell::new(0),
        stop_at: usize::MAX,
    };
    let complete = execute_program(
        &imported,
        &code,
        &files,
        MacroTreeLimits::default(),
        Some(&counter),
    );
    executed(&complete);
    let cancel = Polls {
        count: Cell::new(0),
        stop_at: counter.count.get() - 1,
    };
    let stopped = execute_program(
        &imported,
        &code,
        &files,
        MacroTreeLimits::default(),
        Some(&cancel),
    );
    assert!(
        matches!(stopped.outcome, Outcome::Inconclusive(_)),
        "{stopped:?}"
    );
    assert!(stopped.attempts.len() >= 2);
    assert!(stopped.completed_vm_usage.steps > 0);
    assert!(stopped.states.is_none());
}

#[test]
fn runtime_vm_limits_withhold_macro_program_states_and_retain_macro_work() {
    let (imported, code) = batches::artifact_import_fixture();
    let main = name("Main");
    let inputs = [SourceModuleInput {
        name: &main,
        source: b"prelude\nimport SourceLibrary\n#eval 7 + 11",
    }];
    let mut execution = execution_limits();
    execution.vm.max_steps = 0;
    let stopped = imported.execute_source_modules_with_imported_macros(
        &inputs,
        &main,
        &KVMap::new(),
        crate::source_check::modules::execution::SourceProgramLimits::new(execution),
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
    );
    assert!(
        matches!(stopped.outcome, Outcome::Inconclusive(_)),
        "{stopped:?}"
    );
    assert_eq!(stopped.attempts.len(), 2);
    assert!(stopped.completed_vm_usage.steps > 0);
    assert!(stopped.states.is_none());
}

#[test]
fn later_module_parse_refusal_precedes_earlier_module_runtime_work() {
    use crate::source_check::modules::execution::SourceProgramExecutionError;
    let (imported, code) = batches::artifact_import_fixture();
    let before = imported.engine.logical_root(&KVMap::new());
    let compilation = MacroCompilationInputs::new(
        code.clone(),
        VerifiedPartition::user_fixture(),
        users(&code),
    );
    let mut execution = execution_limits();
    execution.vm.max_steps = 0;
    let prefix = "prelude\nimport SourceLibrary\n#eval 7 + 11\n";
    let valid = [
        ("Main", "prelude\nimport Lib\ndef checked : Nat := 1\n"),
        ("Lib", prefix),
    ];
    let control = execute_deferred_program(
        &imported,
        compilation.clone(),
        &valid,
        MacroRegistryLimits::default(),
        execution,
        None,
    );
    assert!(
        matches!(control.outcome, Outcome::Inconclusive(_)),
        "{control:?}"
    );
    assert!(
        !control.attempts.is_empty(),
        "the valid graph must reach the earlier module: {control:?}"
    );
    assert!(control.states.is_none());
    let malformed = [
        ("Main", "prelude\nimport Lib\ndef broken : Nat := (\n"),
        ("Lib", prefix),
    ];
    let stopped = execute_deferred_program(
        &imported,
        compilation,
        &malformed,
        MacroRegistryLimits::default(),
        execution,
        None,
    );
    let Outcome::Complete(Err(SourceProgramExecutionError::Source(error))) = &stopped.outcome
    else {
        panic!("later syntax must be refused before any earlier evaluation: {stopped:?}")
    };
    assert!(
        matches!(error, SourceModuleCheckError::Source { module, .. } if *module == name("Main")),
        "{error:?}"
    );
    assert_eq!(error.disposition(), ("input", false, 1));
    assert!(stopped.attempts.is_empty(), "{stopped:?}");
    assert_eq!(stopped.completed_vm_usage.steps, 0);
    assert!(stopped.states.is_none());
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
}

fn check_deferred(
    imported: &SourceOleanImport,
    compilation: MacroCompilationInputs,
    files: &[(&str, &str)],
    registry_limits: MacroRegistryLimits,
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
    imported.check_source_modules_with_deferred_imported_macros(
        &inputs,
        &name("Main"),
        &KVMap::new(),
        SourceModuleCheckLimits::new(SourceCheckLimits::new(admission())),
        SourceModuleDeferredMacroInputs {
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
    )
}

#[test]
fn deferred_module_macros_leave_unused_code_uncompiled_and_keep_exact_import_worlds() {
    let (imported, mut code) = batches::artifact_import_fixture();
    let before = imported.engine.logical_root(&KVMap::new());
    // Both the unused global diagnostic and an inactive scoped macro lack IR.
    // Their complete checked owners remain in the receipt and its journals.
    for module in &mut code {
        module.decls.retain(|declaration| {
            declaration.name() != &name("SourceLibrary.diagnostic")
                && declaration.name() != &name("SourceLibrary.left")
        });
    }
    assert!(matches!(
        imported.prepare_imported_macros(
            &code,
            &VerifiedPartition::user_fixture(),
            &users(&code),
            MacroRegistryLimits::default(),
        ),
        Err(MacroRegistrationError::Compile { .. })
    ));
    let declarations = users(&code);
    let compilation =
        MacroCompilationInputs::new(code, VerifiedPartition::user_fixture(), declarations);
    let files = [
        (
            "Main",
            "prelude\nimport Lib\nimport Plain\ndef fromMain : Nat := 13 + 17",
        ),
        (
            "Lib",
            "prelude\nimport SourceLibrary\ndef fromLib : Nat := 7 + 11",
        ),
        ("Plain", "prelude\ndef ordinary : Nat := 7 + 11"),
    ];
    let report = check_deferred(
        &imported,
        compilation.clone(),
        &files,
        MacroRegistryLimits::default(),
        None,
    );
    let checked = succeeded(&report);
    for (declaration, expected) in [("fromLib", 11), ("ordinary", 18), ("fromMain", 17)] {
        assert_declared_value(&checked.checked.engine, declaration, expected);
    }
    let states = report.states.as_ref().unwrap();
    assert_eq!(states[&name("Lib")].macro_scope, 19);
    assert_eq!(states[&name("Plain")].macro_scope, 17);
    assert_eq!(states[&name("Main")].macro_scope, 19);
    assert_eq!(report.attempts.len(), 4);
    for source in [
        "prelude\nimport Lib\ndef blocked : Nat := 7 - 11",
        "prelude\nimport Lib\nopen scoped SourceScoped\ndef blocked : Nat := 7 + 11",
    ] {
        let failed = check_deferred(
            &imported,
            compilation.clone(),
            &[files[1], ("Main", source)],
            MacroRegistryLimits::default(),
            None,
        );
        assert!(
            matches!(
                &failed.outcome,
                Outcome::Complete(Err(SourceModuleCheckError::Source {
                    module,
                    error: SourceCheckError::ImportedMacro { .. },
                })) if module == &name("Main")
            ),
            "{failed:?}"
        );
        assert_eq!(failed.attempts.len(), 3);
        assert!(failed.completed_vm_usage.steps > 0);
        assert!(failed.states.is_none());
        assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
        assert!(!imported.engine.environment().contains(&name("fromLib")));
        assert!(!imported.engine.environment().contains(&name("blocked")));
    }
}

#[test]
fn deferred_module_compilation_stops_and_cancellation_publish_no_module_states() {
    struct Cancel;
    impl CancellationProbe for Cancel {
        fn is_cancelled(&self) -> bool {
            true
        }
    }

    let (imported, code) = batches::artifact_import_fixture();
    let before = imported.engine.logical_root(&KVMap::new());
    let declarations = users(&code);
    let compilation =
        MacroCompilationInputs::new(code, VerifiedPartition::user_fixture(), declarations);
    let files = [
        ("Main", "prelude\nimport Lib\ndef blocked : Nat := 7 + 11"),
        (
            "Lib",
            "prelude\nimport SourceLibrary\ndef checkedPrefix : Nat := 5",
        ),
    ];
    let mut limits = MacroRegistryLimits::default();
    limits.compilation.ir.max_work = 0;
    let stopped = check_deferred(&imported, compilation.clone(), &files, limits, None);
    assert!(matches!(stopped.outcome, Outcome::Inconclusive(_)));
    assert_eq!(stopped.attempts.len(), 1);
    assert_eq!(stopped.completed_vm_usage.steps, 0);
    assert!(stopped.states.is_none());
    assert!(
        !imported
            .engine
            .environment()
            .contains(&name("checkedPrefix"))
    );
    assert!(!imported.engine.environment().contains(&name("blocked")));
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);

    let cancelled = check_deferred(
        &imported,
        compilation.clone(),
        &files,
        MacroRegistryLimits::default(),
        Some(&Cancel),
    );
    assert!(matches!(cancelled.outcome, Outcome::Inconclusive(_)));
    assert!(cancelled.attempts.is_empty());
    assert!(cancelled.states.is_none());
    let recovered = check_deferred(
        &imported,
        compilation,
        &files,
        MacroRegistryLimits::default(),
        None,
    );
    assert_declared_value(&succeeded(&recovered).checked.engine, "blocked", 11);
    assert_eq!(recovered.states.as_ref().unwrap().len(), 2);
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
}

fn execute_deferred_program(
    imported: &SourceOleanImport,
    compilation: MacroCompilationInputs,
    files: &[(&str, &str)],
    registry_limits: MacroRegistryLimits,
    execution: crate::EngineExecutionLimits,
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
    imported.execute_source_modules_with_deferred_imported_macros(
        &inputs,
        &name("Main"),
        &KVMap::new(),
        crate::source_check::modules::execution::SourceProgramLimits::new(execution),
        SourceModuleDeferredMacroInputs {
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
fn deferred_macro_programs_execute_with_unused_missing_code_and_refuse_demand_atomically() {
    use crate::source_check::modules::execution::SourceProgramExecutionError;

    let (imported, mut code) = batches::artifact_import_fixture();
    let before = imported.engine.logical_root(&KVMap::new());
    for module in &mut code {
        module.decls.retain(|declaration| {
            declaration.name() != &name("SourceLibrary.diagnostic")
                && declaration.name() != &name("SourceLibrary.left")
        });
    }
    let files = [
        (
            "Main",
            "prelude\nimport Lib\nimport Plain\n#eval fromLib\n#eval ordinary\n#eval 13 + 17",
        ),
        (
            "Lib",
            "prelude\nimport SourceLibrary\ndef fromLib : Nat := 7 + 11",
        ),
        ("Plain", "prelude\ndef ordinary : Nat := 7 + 11"),
    ];
    let eager = execute_program(&imported, &code, &files, MacroTreeLimits::default(), None);
    assert!(matches!(eager.outcome, Outcome::Complete(Err(_))));
    assert!(eager.attempts.is_empty());
    assert!(eager.states.is_none());
    let declarations = users(&code);
    let compilation =
        MacroCompilationInputs::new(code, VerifiedPartition::user_fixture(), declarations);
    let complete = execute_deferred_program(
        &imported,
        compilation.clone(),
        &files,
        MacroRegistryLimits::default(),
        execution_limits(),
        None,
    );
    assert_eq!(
        program_values(executed(&complete), "Main"),
        vec![
            crate::ClosedVmValue::Scalar(11),
            crate::ClosedVmValue::Scalar(18),
            crate::ClosedVmValue::Scalar(17),
        ]
    );
    let states = complete.states.as_ref().unwrap();
    assert_eq!(states[&name("Lib")].macro_scope, 19);
    assert_eq!(states[&name("Plain")].macro_scope, 17);
    assert_eq!(states[&name("Main")].macro_scope, 19);
    assert_eq!(complete.attempts.len(), 4);
    for (source, selected) in [
        (
            "prelude\nimport Lib\n#eval fromLib\n#eval 7 - 11",
            "SourceLibrary.diagnostic",
        ),
        (
            "prelude\nimport Lib\n#eval fromLib\nopen scoped SourceScoped\n#eval 7 + 11",
            "SourceLibrary.left",
        ),
    ] {
        let failed = execute_deferred_program(
            &imported,
            compilation.clone(),
            &[files[1], ("Main", source)],
            MacroRegistryLimits::default(),
            execution_limits(),
            None,
        );
        assert!(
            matches!(
                &failed.outcome,
                Outcome::Complete(Err(SourceProgramExecutionError::Source(
                    SourceModuleCheckError::Source { module, .. }
                ))) if module == &name("Main")
            ),
            "{failed:?}"
        );
        assert_eq!(failed.attempts.len(), 3);
        assert_eq!(failed.attempts.last().unwrap().declaration, name(selected));
        assert!(failed.completed_vm_usage.steps > 0);
        assert!(failed.states.is_none());
        assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
        assert!(!imported.engine.environment().contains(&name("fromLib")));
        assert!(!imported.engine.environment().contains(&name("ordinary")));
    }
}

#[test]
fn deferred_macro_program_limits_and_cancellation_withhold_successful_prefixes() {
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
    let declarations = users(&code);
    let compilation =
        MacroCompilationInputs::new(code, VerifiedPartition::user_fixture(), declarations);
    let files = [
        (
            "Main",
            "prelude\nimport Lib\n#eval checkedPrefix\n#eval 7 + 11",
        ),
        (
            "Lib",
            "prelude\nimport SourceLibrary\ndef checkedPrefix : Nat := 5",
        ),
    ];
    let mut limits = MacroRegistryLimits::default();
    limits.compilation.ir.max_work = 0;
    let stopped = execute_deferred_program(
        &imported,
        compilation.clone(),
        &files,
        limits,
        execution_limits(),
        None,
    );
    assert!(matches!(stopped.outcome, Outcome::Inconclusive(_)));
    assert_eq!(stopped.attempts.len(), 1);
    assert_eq!(stopped.completed_vm_usage.steps, 0);
    assert!(stopped.states.is_none());

    let mut execution = execution_limits();
    execution.vm.max_steps = 0;
    let runtime_stop = execute_deferred_program(
        &imported,
        compilation.clone(),
        &[("Main", "prelude\nimport SourceLibrary\n#eval 7 + 11")],
        MacroRegistryLimits::default(),
        execution,
        None,
    );
    assert!(matches!(runtime_stop.outcome, Outcome::Inconclusive(_)));
    assert_eq!(runtime_stop.attempts.len(), 2);
    assert!(runtime_stop.completed_vm_usage.steps > 0);
    assert!(runtime_stop.states.is_none());

    let cancel_before = Polls {
        count: Cell::new(0),
        stop_at: 1,
    };
    let cancelled = execute_deferred_program(
        &imported,
        compilation.clone(),
        &files,
        MacroRegistryLimits::default(),
        execution_limits(),
        Some(&cancel_before),
    );
    assert!(matches!(cancelled.outcome, Outcome::Inconclusive(_)));
    assert!(cancelled.attempts.is_empty());
    assert!(cancelled.states.is_none());

    let counter = Polls {
        count: Cell::new(0),
        stop_at: usize::MAX,
    };
    let recovered = execute_deferred_program(
        &imported,
        compilation.clone(),
        &files,
        MacroRegistryLimits::default(),
        execution_limits(),
        Some(&counter),
    );
    assert_eq!(
        program_values(executed(&recovered), "Main"),
        vec![
            crate::ClosedVmValue::Scalar(5),
            crate::ClosedVmValue::Scalar(11)
        ]
    );
    assert!(counter.count.get() > 1);
    let cancel_after = Polls {
        count: Cell::new(0),
        stop_at: counter.count.get() - 1,
    };
    let cancelled = execute_deferred_program(
        &imported,
        compilation,
        &files,
        MacroRegistryLimits::default(),
        execution_limits(),
        Some(&cancel_after),
    );
    assert!(matches!(cancelled.outcome, Outcome::Inconclusive(_)));
    assert_eq!(cancelled.attempts.len(), 2);
    assert!(cancelled.completed_vm_usage.steps > 0);
    assert!(cancelled.states.is_none());
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
    assert!(
        !imported
            .engine
            .environment()
            .contains(&name("checkedPrefix"))
    );
}

#[test]
fn deferred_lean_macro_validation_stops_successors_without_module_states() {
    use crate::source_check::modules::execution::{
        SourceProgramExecutionError, SourceProgramLimits,
    };

    let (imported, code) = batches::artifact_import_fixture();
    let before = imported.engine.logical_root(&KVMap::new());
    let declarations = users(&code);
    let compilation =
        MacroCompilationInputs::new(code, VerifiedPartition::user_fixture(), declarations);
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
    let stopped = imported
        .execute_lean_source_modules_with_deferred_imported_macros_and_validation(
            &inputs,
            &names[1],
            &KVMap::new(),
            SourceProgramLimits::new(execution_limits()),
            SourceModuleDeferredMacroInputs {
                compilation,
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
                let index = commands.batch.source_evaluation_indices[0];
                assert_eq!(
                    crate::closed_vm_value(&commands.batch.executions[index].exit)
                        .unwrap()
                        .unwrap(),
                    crate::ClosedVmValue::Scalar(11)
                );
                Err("reject this module")
            },
        );
    assert!(
        matches!(
            &stopped.outcome,
            Outcome::Complete(Err(SourceProgramExecutionError::Validation { module, error }))
                if module == &names[0] && *error == "reject this module"
        ),
        "{stopped:?}"
    );
    assert_eq!(visited, vec![name("Lib")]);
    assert_eq!(stopped.attempts.len(), 2);
    assert!(stopped.completed_vm_usage.steps > 0);
    assert!(stopped.states.is_none());
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
}

#[test]
fn deferred_program_dispatch_budget_accumulates_across_source_modules() {
    use crate::source_check::modules::execution::SourceProgramLimits;

    let (imported, code) = batches::artifact_import_fixture();
    let before = imported.engine.logical_root(&KVMap::new());
    let declarations = users(&code);
    let compilation =
        MacroCompilationInputs::new(code, VerifiedPartition::user_fixture(), declarations);
    let names = [name("Main"), name("Lib")];
    let inputs = [
        SourceModuleInput {
            name: &names[0],
            source: b"prelude\nimport Lib\n#eval 13 + 17",
        },
        SourceModuleInput {
            name: &names[1],
            source: b"prelude\nimport SourceLibrary\ndef fromLib : Nat := 7 + 11",
        },
    ];
    let run = |limits| {
        imported.execute_source_modules_with_deferred_imported_macros(
            &inputs,
            &names[0],
            &KVMap::new(),
            SourceProgramLimits::new(execution_limits()),
            SourceModuleDeferredMacroInputs {
                compilation: compilation.clone(),
                registry_limits: MacroRegistryLimits::default(),
                context: context(),
                state: MacroState::default(),
                limits,
            },
            None,
            crate::EvaluationPresentation::Raw,
        )
    };
    let complete = run(MacroTreeLimits::default());
    assert_eq!(
        program_values(executed(&complete), "Main"),
        vec![crate::ClosedVmValue::Scalar(17)]
    );
    assert_eq!(complete.attempts.len(), 4);

    let mut limits = MacroTreeLimits::default();
    limits.dispatch.max_attempts = 3;
    let stopped = run(limits);
    assert!(
        matches!(stopped.outcome, Outcome::Inconclusive(_)),
        "{stopped:?}"
    );
    assert_eq!(stopped.attempts.len(), 3);
    assert_eq!(
        stopped.attempts.last().unwrap().declaration,
        name("SourceLibrary.skip")
    );
    assert!(stopped.completed_vm_usage.steps > 0);
    assert!(stopped.states.is_none());
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
    assert!(!imported.engine.environment().contains(&name("fromLib")));

    // Previously compiled closures still cost an attempt in each source module.
    limits.dispatch.max_attempts = 4;
    let exact = run(limits);
    assert_eq!(
        program_values(executed(&exact), "Main"),
        vec![crate::ClosedVmValue::Scalar(17)]
    );
    assert_eq!(exact.states, complete.states);
    assert_eq!(exact.completed_vm_usage, complete.completed_vm_usage);
}

#[test]
fn deferred_lean_programs_keep_implicit_init_edges_and_stop_at_module_validation() {
    use crate::source_check::modules::execution::{
        SourceProgramExecutionError, SourceProgramLimits,
    };

    let (imported, code) = batches::artifact_import_fixture();
    let before = imported.engine.logical_root(&KVMap::new());
    let declarations = users(&code);
    let compilation =
        MacroCompilationInputs::new(code, VerifiedPartition::user_fixture(), declarations);
    let names = [name("Main"), name("Init"), name("Lib")];
    let inputs = [
        SourceModuleInput {
            name: &names[0],
            source: b"import Lib\n#eval 13 + 17",
        },
        SourceModuleInput {
            name: &names[1],
            source: b"prelude",
        },
        SourceModuleInput {
            name: &names[2],
            source: b"prelude\nimport SourceLibrary\n#eval 7 + 11",
        },
    ];
    let mut visited = Vec::new();
    let stopped = imported
        .execute_lean_source_modules_with_deferred_imported_macros_and_validation(
            &inputs,
            &names[0],
            &KVMap::new(),
            SourceProgramLimits::new(execution_limits()),
            SourceModuleDeferredMacroInputs {
                compilation,
                registry_limits: MacroRegistryLimits::default(),
                context: context(),
                state: MacroState::default(),
                limits: MacroTreeLimits::default(),
            },
            None,
            crate::EvaluationPresentation::Raw,
            &mut |module, commands| {
                visited.push(module.clone());
                if module == &names[2] {
                    assert_eq!(commands.batch.source_evaluation_indices.len(), 1);
                    let index = commands.batch.source_evaluation_indices[0];
                    assert_eq!(
                        crate::closed_vm_value(&commands.batch.executions[index].exit)
                            .unwrap()
                            .unwrap(),
                        crate::ClosedVmValue::Scalar(11)
                    );
                    Err("reject this module")
                } else {
                    assert_eq!(module, &names[1]);
                    assert!(commands.batch.executions.is_empty());
                    Ok(())
                }
            },
        );
    assert!(
        matches!(
            &stopped.outcome,
            Outcome::Complete(Err(SourceProgramExecutionError::Validation { module, error }))
                if module == &names[2] && *error == "reject this module"
        ),
        "{stopped:?}"
    );
    assert_eq!(visited, vec![name("Init"), name("Lib")]);
    assert_eq!(stopped.attempts.len(), 2);
    assert!(stopped.completed_vm_usage.steps > 0);
    assert!(stopped.states.is_none());
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
}

pub(super) fn compile_deferred(
    imported: &SourceOleanImport,
    compilation: MacroCompilationInputs,
    files: &[(&str, &str)],
    macro_limits: MacroTreeLimits,
    write_budget: crate::OleanWriteBudget,
    cancellation: Option<&dyn CancellationProbe>,
) -> crate::source_check::modules::SourceMacroModuleBuild {
    let names: Vec<_> = files.iter().map(|(label, _)| name(label)).collect();
    let inputs: Vec<_> = files
        .iter()
        .zip(&names)
        .map(|((_, source), name)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    imported.compile_source_modules_with_deferred_imported_macros(
        &inputs,
        &name("Main"),
        &KVMap::new(),
        SourceModuleCheckLimits::new(SourceCheckLimits::new(admission())),
        SourceModuleDeferredMacroInputs {
            compilation,
            registry_limits: MacroRegistryLimits::default(),
            context: context(),
            state: MacroState {
                macro_scope: 17,
                ..MacroState::default()
            },
            limits: macro_limits,
        },
        write_budget,
        cancellation,
    )
}

#[test]
fn imported_macro_builds_emit_recheckable_artifacts_with_real_implicit_imports() {
    let (imported, code, retained) = batches::artifact_build_fixture();
    let before = imported.engine.logical_root(&KVMap::new());
    let declarations = users(&code);
    let compilation =
        MacroCompilationInputs::new(code, VerifiedPartition::user_fixture(), declarations);
    let files = [
        ("Main", "import Lib\ndef second : Nat := 13 + 17"),
        ("Init", "prelude"),
        (
            "Lib",
            "prelude\nimport SourceLibrary\ndef first : Nat := 7 + 11",
        ),
    ];
    let built = compile_deferred(
        &imported,
        compilation.clone(),
        &files,
        MacroTreeLimits::default(),
        crate::OleanWriteBudget::default(),
        None,
    );
    let Outcome::Complete(Ok(product)) = &built.outcome else {
        panic!("{built:?}")
    };
    assert_eq!(
        product.checked.module_order,
        [name("Init"), name("Lib"), name("Main")]
    );
    assert_eq!(product.elaborated_modules, 3);
    assert_eq!(product.reused_modules, 0);
    assert_eq!(product.persisted_modules, 0);
    assert_eq!(built.attempts.len(), 4);
    assert!(built.completed_vm_usage.steps > 0);
    assert_eq!(built.states.as_ref().unwrap().len(), 3);
    assert_declared_value(&product.checked.checked.engine, "first", 11);
    assert_declared_value(&product.checked.checked.engine, "second", 17);
    let mut imports: Vec<_> = retained
        .iter()
        .map(|(name, artifact)| crate::OleanModuleInput {
            name,
            artifact,
            server_artifact: None,
            private_artifact: None,
        })
        .collect();
    imports.extend(
        product
            .artifacts
            .iter()
            .map(|artifact| crate::OleanModuleInput {
                name: &artifact.name,
                artifact: &artifact.bytes,
                server_artifact: None,
                private_artifact: None,
            }),
    );
    let rechecked = Engine::builder()
        .build_empty()
        .check_olean_modules(
            &imports,
            &KVMap::new(),
            crate::OleanCheckLimits::new(4 * 1024 * 1024, admission().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_declared_value(&rechecked.engine, "first", 11);
    assert_declared_value(&rechecked.engine, "second", 17);
    assert_eq!(
        rechecked.engine.logical_root(&KVMap::new()),
        product.checked.checked.result_logical_root
    );
    let repeated = compile_deferred(
        &imported,
        compilation,
        &[files[2], files[0], files[1]],
        MacroTreeLimits::default(),
        crate::OleanWriteBudget::default(),
        None,
    );
    let Outcome::Complete(Ok(repeated_product)) = &repeated.outcome else {
        panic!("{repeated:?}")
    };
    let bytes = |product: &crate::source_check::modules::SourceModuleBuild| {
        product
            .artifacts
            .iter()
            .map(|artifact| (artifact.name.clone(), artifact.bytes.clone()))
            .collect::<Vec<_>>()
    };
    assert_eq!(bytes(product), bytes(repeated_product));
    assert_eq!(repeated.states, built.states);
    assert_eq!(repeated.completed_vm_usage, built.completed_vm_usage);
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
}

#[test]
fn imported_macro_build_failures_withhold_artifacts_and_states_and_recover() {
    let (imported, code, _) = batches::artifact_build_fixture();
    let before = imported.engine.logical_root(&KVMap::new());
    let declarations = users(&code);
    let compilation =
        MacroCompilationInputs::new(code, VerifiedPartition::user_fixture(), declarations);
    let library = (
        "Lib",
        "prelude\nimport SourceLibrary\ndef first : Nat := 7 + 11",
    );
    let main = ("Main", "prelude\nimport Lib\ndef second : Nat := 13 + 17");
    let good = compile_deferred(
        &imported,
        compilation.clone(),
        &[library, main],
        MacroTreeLimits::default(),
        crate::OleanWriteBudget::default(),
        None,
    );
    let Outcome::Complete(Ok(product)) = &good.outcome else {
        panic!("{good:?}")
    };
    let bytes: u64 = product.artifacts.iter().map(|a| a.report.file_bytes).sum();
    let failed = compile_deferred(
        &imported,
        compilation.clone(),
        &[
            library,
            (
                "Main",
                "prelude\nimport Lib\ntheorem impossible (P : Prop) : P := by rfl",
            ),
        ],
        MacroTreeLimits::default(),
        crate::OleanWriteBudget::default(),
        None,
    );
    assert!(
        matches!(failed.outcome, Outcome::Complete(Err(_))),
        "{failed:?}"
    );
    assert!(failed.states.is_none());
    assert!(!failed.attempts.is_empty());
    let limited = compile_deferred(
        &imported,
        compilation.clone(),
        &[library, main],
        MacroTreeLimits::default(),
        crate::OleanWriteBudget {
            max_bytes: bytes - 1,
            ..Default::default()
        },
        None,
    );
    assert!(
        matches!(
            limited.outcome,
            Outcome::Complete(Err(
                crate::source_check::modules::SourceModuleBuildError::Encode { .. }
            ))
        ),
        "{limited:?}"
    );
    assert!(limited.states.is_none());
    assert_eq!(limited.attempts.len(), good.attempts.len());
    assert_eq!(limited.completed_vm_usage, good.completed_vm_usage);
    let mut macro_limits = MacroTreeLimits::default();
    macro_limits.dispatch.max_attempts = 1;
    let stopped = compile_deferred(
        &imported,
        compilation.clone(),
        &[library, main],
        macro_limits,
        crate::OleanWriteBudget::default(),
        None,
    );
    assert!(
        matches!(stopped.outcome, Outcome::Inconclusive(_)),
        "{stopped:?}"
    );
    assert!(stopped.states.is_none());
    let recovered = compile_deferred(
        &imported,
        compilation,
        &[library, main],
        MacroTreeLimits::default(),
        crate::OleanWriteBudget::default(),
        None,
    );
    let Outcome::Complete(Ok(recovered_product)) = recovered.outcome else {
        panic!("{recovered:?}")
    };
    assert_eq!(
        recovered_product.checked.checked.result_logical_root,
        product.checked.checked.result_logical_root
    );
    assert_eq!(recovered.states, good.states);
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
    assert!(!imported.engine.environment().contains(&name("first")));
}

#[test]
fn cancellation_at_macro_artifact_publication_withholds_all_module_states() {
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
    let (imported, code, _) = batches::artifact_build_fixture();
    let before = imported.engine.logical_root(&KVMap::new());
    let declarations = users(&code);
    let compilation =
        MacroCompilationInputs::new(code, VerifiedPartition::user_fixture(), declarations);
    let files = [(
        "Main",
        "prelude\nimport SourceLibrary\ndef first : Nat := 7 + 11",
    )];
    let counter = Polls {
        count: Cell::new(0),
        stop_at: usize::MAX,
    };
    let complete = compile_deferred(
        &imported,
        compilation.clone(),
        &files,
        MacroTreeLimits::default(),
        crate::OleanWriteBudget::default(),
        Some(&counter),
    );
    assert!(
        matches!(complete.outcome, Outcome::Complete(Ok(_))),
        "{complete:?}"
    );
    let cancellation = Polls {
        count: Cell::new(0),
        stop_at: counter.count.get(),
    };
    let stopped = compile_deferred(
        &imported,
        compilation,
        &files,
        MacroTreeLimits::default(),
        crate::OleanWriteBudget::default(),
        Some(&cancellation),
    );
    assert!(
        matches!(stopped.outcome, Outcome::Inconclusive(_)),
        "{stopped:?}"
    );
    assert!(
        format!("{:?}", stopped.outcome).contains("source-modules/before-build-publication"),
        "{stopped:?}"
    );
    assert!(stopped.states.is_none());
    assert_eq!(stopped.attempts.len(), complete.attempts.len());
    assert_eq!(stopped.completed_vm_usage, complete.completed_vm_usage);
    assert_eq!(imported.engine.logical_root(&KVMap::new()), before);
}
