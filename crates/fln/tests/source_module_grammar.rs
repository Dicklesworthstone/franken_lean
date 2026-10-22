//! Native source imports carry checked grammar effects in their exact module worlds.
#![forbid(unsafe_code)]

use fln::source_check::modules::execution::{SourceProgramLimits, preflight_source_program};
use fln::source_check::modules::imported::SourceOleanImport;
use fln::source_check::modules::{
    SourceModuleBuildError, SourceModuleCacheLimits, SourceModuleCheck, SourceModuleCheckError,
    SourceModuleCheckLimits, SourceModuleSession, SourceModuleSessionCheck,
};
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name, OleanWriteBudget,
    Outcome, SourceCheckLimits, SourceModuleInput, VmExit,
};

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn limits() -> SourceModuleCheckLimits {
    SourceModuleCheckLimits::new(SourceCheckLimits::new(EngineAdmissionLimits::new(
        Budget::for_stack_bytes(2 * 1024 * 1024),
    )))
}

fn engine() -> Engine {
    Engine::with_source_seed(limits().source.admission)
        .unwrap()
        .into_complete()
        .unwrap()
}

fn with_modules<T>(files: &[(&str, &str)], run: impl FnOnce(&[SourceModuleInput<'_>]) -> T) -> T {
    let names: Vec<_> = files.iter().map(|(module, _)| name(module)).collect();
    let inputs: Vec<_> = files
        .iter()
        .zip(&names)
        .map(|((_, source), name)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    run(&inputs)
}

fn check(
    base: &Engine,
    files: &[(&str, &str)],
) -> Result<Outcome<SourceModuleCheck>, SourceModuleCheckError> {
    with_modules(files, |inputs| {
        base.check_source_modules(inputs, &name("Main"), &KVMap::new(), limits())
    })
}

fn checked(base: &Engine, files: &[(&str, &str)]) -> SourceModuleCheck {
    check(base, files)
        .unwrap_or_else(|error| panic!("{files:?}\n{error:?}"))
        .into_complete()
        .unwrap()
}

fn session_check(
    session: &mut SourceModuleSession,
    files: &[(&str, &str)],
) -> Result<Outcome<SourceModuleSessionCheck>, SourceModuleCheckError> {
    with_modules(files, |inputs| session.check(inputs, &name("Main")))
}

fn session_checked(
    session: &mut SourceModuleSession,
    files: &[(&str, &str)],
) -> SourceModuleSessionCheck {
    session_check(session, files)
        .unwrap_or_else(|error| panic!("{files:?}\n{error:?}"))
        .into_complete()
        .unwrap()
}

const BRACKETS: &str = "notation \"⟪\" x \"⟫\" => Nat.add x x\n";

#[test]
fn nested_quoted_patterns_survive_module_journals_and_direct_engine_reentry() {
    let base = engine();
    let imported = checked(&base, &[
        ("Main", "import Lib\ntheorem t : select! (Nat.add 5 6) = (5 : Nat) := rfl"),
        ("Lib", "syntax \"select! \" term:max : term\nmacro_rules | `(select! (Nat.add $x $y)) => `($x)"),
    ]).checked.engine;
    let options = KVMap::new();
    let before = imported.logical_root(&options);
    let good = imported
        .check_source_files(
            &[b"theorem afterReload : select! (Nat.add 7 8) = (7 : Nat) := rfl"],
            &options,
            limits().source,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(good.theorems, 1);
    for source in [
        b"theorem bad : select! (Nat.add 7 8) = (8 : Nat) := rfl".as_slice(),
        b"theorem bad : select! (Nat.mul 7 8) = (7 : Nat) := rfl",
    ] {
        assert!(
            imported
                .check_source_files(&[source], &options, limits().source)
                .is_err()
        );
    }
    assert_eq!(imported.logical_root(&options), before);
}

#[test]
fn direct_engine_entry_points_preserve_imported_interpolation_grammar() {
    let base = engine();
    let imported = checked(
        &base,
        &[
            ("Main", "import Lib"),
            (
                "Lib",
                r#"macro "fixed!" _s:interpolatedStr(term) : term => `(42)"#,
            ),
        ],
    )
    .checked
    .engine;
    let options = KVMap::new();
    let before = imported.logical_root(&options);
    let execution_limits = EngineExecutionLimits::new(limits().source.admission.kernel);
    let source = br#"def answer : Nat := fixed!"\{"
#eval answer"#;
    let commands = imported
        .execute_source_commands_with_presentation(
            source,
            &options,
            execution_limits,
            fln::EvaluationPresentation::Raw,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(commands.batch.source_evaluation_indices.len(), 1);
    assert_eq!(
        fln::closed_vm_value(&commands.batch.executions.last().unwrap().exit).unwrap(),
        Some(fln::ClosedVmValue::Scalar(42))
    );

    let definitions = imported
        .execute_source_definitions(
            &[br#"def answer : Nat := fixed!"\{""#, b"#eval answer"],
            &options,
            execution_limits,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        fln::closed_vm_value(&definitions.executions.last().unwrap().exit).unwrap(),
        Some(fln::ClosedVmValue::Scalar(42))
    );

    for source in [
        br#"#check fixed!"\{""#.as_slice(),
        br#"def answer : Nat := fixed!"\{"
#check answer"#,
    ] {
        let terminal = imported
            .check_terminal_source_command(source, &options, execution_limits)
            .unwrap()
            .into_complete()
            .unwrap();
        assert_eq!(
            terminal.check.checked_type,
            fln::Expr::const_(name("Nat"), Vec::new())
        );
    }

    for invalid in [br#"def bad := "\{""#.as_slice(), br#"def bad := "\q""#] {
        assert!(
            imported
                .execute_source_commands_with_presentation(
                    invalid,
                    &options,
                    execution_limits,
                    fln::EvaluationPresentation::Raw,
                )
                .is_err()
        );
        assert!(
            imported
                .execute_source_definitions(&[invalid], &options, execution_limits)
                .is_err()
        );
        let mut terminal = invalid.to_vec();
        terminal.extend_from_slice(b"\n#check Nat");
        assert!(
            imported
                .check_terminal_source_command(&terminal, &options, execution_limits)
                .is_err()
        );
    }
    assert_eq!(imported.logical_root(&options), before);
    assert!(!imported.environment().contains(&name("answer")));
    assert!(
        base.execute_source_commands_with_presentation(
            source,
            &options,
            execution_limits,
            fln::EvaluationPresentation::Raw,
        )
        .is_err(),
        "the macro must come from the checked source module"
    );
}

#[test]
fn syntax_only_libraries_export_notation_term_macros_and_tactic_macros() {
    let base = engine();
    let before = base.logical_root(&KVMap::new());
    let library = r#"
infixl:65 " +++ " => Nat.add
notation "⟪" x "⟫" => Nat.add x x
macro "twice " x:term:max : term => `(Nat.add $x $x)
syntax "trip " term:max : term
macro_rules | `(trip $x) => `(Nat.add $x (Nat.add $x $x))
macro "checked_rfl" : tactic => `(tactic| rfl)
"#;
    let main = r#"import Lib
theorem infix_works : (2 : Nat) +++ 3 = 5 := rfl
theorem brackets_work : ⟪(3 : Nat)⟫ = 6 := by checked_rfl
theorem macro_works : twice (3 : Nat) = 6 := rfl
theorem rules_work : trip (2 : Nat) = 6 := by checked_rfl
"#;
    let result = checked(&base, &[("Main", main), ("Lib", library)]);
    assert_eq!(result.module_order, [name("Lib"), name("Main")]);
    assert_eq!(result.checked.files, 2);
    assert_eq!(result.checked.theorems, 4);
    for declaration in ["infix_works", "brackets_work", "macro_works", "rules_work"] {
        assert!(
            result
                .checked
                .engine
                .environment()
                .contains(&name(declaration))
        );
        assert!(!base.environment().contains(&name(declaration)));
    }
    assert_eq!(base.logical_root(&KVMap::new()), before);
}

#[test]
fn transitive_diamonds_keep_shared_rules_once_and_distinct_module_macro_identities() {
    let files = [
        (
            "Main",
            "import Right\nimport Left\nimport Left\ntheorem combined : left_value + right_value = 10 := rfl\ntheorem shared : ⟪(3 : Nat)⟫ = 6 := rfl",
        ),
        (
            "Left",
            "import Base\nmacro \"left_value\" : term => `(⟪(2 : Nat)⟫)",
        ),
        (
            "Right",
            "import Base\nmacro \"right_value\" : term => `(⟪(3 : Nat)⟫)",
        ),
        ("Base", BRACKETS),
    ];
    let base = engine();
    let result = checked(&base, &files);
    assert_eq!(
        result.module_order,
        [name("Base"), name("Right"), name("Left"), name("Main")]
    );
    assert_eq!(result.checked.theorems, 2);
    let mut reversed = files;
    reversed.reverse();
    assert_eq!(
        result.checked.result_logical_root,
        checked(&base, &reversed).checked.result_logical_root,
        "caller array order must not change the grammar import order"
    );
}

#[test]
fn imported_scoped_notation_requires_activation_and_restores_at_scope_exit() {
    let library = "namespace Ops\nscoped infixl:65 \" +++ \" => Nat.add\nend Ops";
    let base = engine();
    for body in [
        "namespace Ops\ntheorem works : (2 : Nat) +++ 3 = 5 := rfl\nend Ops",
        "open Ops\ntheorem works : (2 : Nat) +++ 3 = 5 := rfl",
        "open scoped Ops\ntheorem works : (2 : Nat) +++ 3 = 5 := rfl",
    ] {
        let main = format!("import Lib\n{body}");
        assert_eq!(
            checked(&base, &[("Main", &main), ("Lib", library)])
                .checked
                .theorems,
            1
        );
    }
    for body in [
        "theorem leaked : (2 : Nat) +++ 3 = 5 := rfl",
        "section\nopen scoped Ops\ntheorem works : (2 : Nat) +++ 3 = 5 := rfl\nend\ntheorem leaked : (2 : Nat) +++ 3 = 5 := rfl",
        "namespace Ops\ntheorem works : (2 : Nat) +++ 3 = 5 := rfl\nend Ops\ntheorem leaked : (2 : Nat) +++ 3 = 5 := rfl",
    ] {
        let main = format!("import Lib\n{body}");
        assert!(matches!(
            check(&base, &[("Main", &main), ("Lib", library)]),
            Err(SourceModuleCheckError::Source { module, .. }) if module == name("Main")
        ));
    }
}

#[test]
fn imported_templates_retain_declaration_site_names_through_caller_shadowing() {
    let library = r#"namespace Library
def chosen : Nat := 7
notation "library_value" => chosen
macro "library_add " x:term:max : term => `(Nat.add chosen $x)
end Library
"#;
    let main = r#"import Lib
def chosen : Nat := 99
theorem closed : library_value = 7 := rfl
theorem shadowed (chosen : Nat) : library_add 3 = 10 := rfl
"#;
    assert_eq!(
        checked(&engine(), &[("Main", main), ("Lib", library)])
            .checked
            .theorems,
        2
    );
}

#[test]
fn siblings_and_local_declarations_cannot_lend_grammar_to_a_consumer() {
    let base = engine();
    let before = base.logical_root(&KVMap::new());
    let sibling = check(
        &base,
        &[
            ("Main", "import A\nimport B"),
            ("A", BRACKETS),
            ("B", "theorem stolen : ⟪(2 : Nat)⟫ = 4 := rfl"),
        ],
    );
    assert!(matches!(
        sibling,
        Err(SourceModuleCheckError::Source { module, .. }) if module == name("B")
    ));
    let library = "section\nlocal notation \"⟪\" x \"⟫\" => Nat.add x x\ntheorem local_works : ⟪(2 : Nat)⟫ = 4 := rfl\nend";
    checked(&base, &[("Main", "import Lib"), ("Lib", library)]);
    assert!(matches!(
        check(&base, &[("Main", "import Lib\ntheorem stolen : ⟪(2 : Nat)⟫ = 4 := rfl"), ("Lib", library)]),
        Err(SourceModuleCheckError::Source { module, .. }) if module == name("Main")
    ));
    assert_eq!(base.logical_root(&KVMap::new()), before);
}

#[test]
fn imported_macro_expansions_still_require_sound_elaboration_and_dual_admission() {
    let base = engine();
    let before = base.logical_root(&KVMap::new());
    for (library, main) in [
        (
            BRACKETS,
            "import Lib\ntheorem false_equation : ⟪(3 : Nat)⟫ = 7 := rfl",
        ),
        (
            "macro \"ghost_value\" : term => `(unavailable)",
            "import Lib\ndef bad : Nat := ghost_value",
        ),
        (
            "macro \"fake_proof\" : tactic => `(tactic| rfl)",
            "import Lib\ntheorem bad : (0 : Nat) = 1 := by fake_proof",
        ),
    ] {
        assert!(matches!(
            check(&base, &[("Main", main), ("Lib", library)]),
            Err(SourceModuleCheckError::Source { module, .. }) if module == name("Main")
        ));
        assert_eq!(base.logical_root(&KVMap::new()), before);
    }
    checked(
        &base,
        &[("Main", "theorem recovery : (0 : Nat) = 0 := rfl")],
    );
}

#[test]
fn session_reuses_grammar_and_invalidates_consumers_after_a_syntax_only_edit() {
    let base = engine();
    let mut session = SourceModuleSession::new(
        base,
        KVMap::new(),
        limits(),
        SourceModuleCacheLimits::default(),
    );
    let files = [
        (
            "Main",
            "import Lib\nimport Independent\ntheorem value : ⟪(3 : Nat)⟫ = 6 := rfl",
        ),
        ("Lib", BRACKETS),
        ("Independent", "def independent := 1"),
    ];
    let cold = session_checked(&mut session, &files);
    assert_eq!((cold.reused_modules, cold.elaborated_modules), (0, 3));
    let warm = session_checked(&mut session, &files);
    assert_eq!((warm.reused_modules, warm.elaborated_modules), (3, 0));
    assert_eq!(
        cold.checked.checked.result_logical_root,
        warm.checked.checked.result_logical_root
    );

    let mut changed = files;
    changed[1].1 = "notation \"⟪\" x \"⟫\" => Nat.add x (Nat.add x x)";
    assert!(
        session_check(&mut session, &changed).is_err(),
        "a cached proof cannot survive a changed expansion"
    );
    let recovery = session_checked(&mut session, &files);
    assert_eq!(
        recovery.reused_modules, 3,
        "a failed refresh keeps the previous complete cache"
    );
    assert_eq!(
        recovery.checked.checked.result_logical_root,
        cold.checked.checked.result_logical_root
    );

    changed[0].1 = "import Lib\nimport Independent\ntheorem value : ⟪(3 : Nat)⟫ = 9 := rfl";
    let repaired = session_checked(&mut session, &changed);
    assert_eq!(
        (repaired.reused_modules, repaired.elaborated_modules),
        (1, 2)
    );
    assert_ne!(
        repaired.checked.checked.result_logical_root,
        cold.checked.checked.result_logical_root
    );
    assert_eq!(session_checked(&mut session, &changed).reused_modules, 3);
    assert!(
        session_check(
            &mut session,
            &[
                (
                    "Main",
                    "import Independent\ntheorem stolen : ⟪(3 : Nat)⟫ = 9 := rfl"
                ),
                files[2]
            ],
        )
        .is_err(),
        "removing an import removes its grammar even when its cache entry exists"
    );
}

#[test]
fn receipt_execution_and_preflight_use_imported_grammar_without_an_ambient_seed() {
    let options = KVMap::new();
    let imported = SourceOleanImport::empty(&options);
    let before = imported.engine.logical_root(&options);
    let files = [
        ("Main", "prelude\nimport Lib\n#check Token\n#eval enabled"),
        (
            "Lib",
            "prelude\nimport Core\nmacro \"enabled\" : term => `(Token.on)",
        ),
        ("Core", "prelude\ninductive Token where\n | off\n | on"),
    ];
    with_modules(&files, |inputs| {
        preflight_source_program(inputs, limits()).expect("preflight sees the same source grammar");
        let program = imported
            .execute_source_modules(
                inputs,
                &name("Main"),
                &options,
                SourceProgramLimits::new(EngineExecutionLimits::new(
                    limits().source.admission.kernel,
                )),
                None,
            )
            .unwrap_or_else(|error| panic!("{error:?}"))
            .into_complete()
            .unwrap();
        assert_eq!(
            program
                .modules
                .iter()
                .map(|module| module.module.clone())
                .collect::<Vec<_>>(),
            [name("Core"), name("Lib"), name("Main")]
        );
        let main = &program.modules[2].commands;
        assert_eq!(main.checks.len(), 1);
        assert_eq!(main.batch.source_evaluation_indices.len(), 1);
        let execution = &main.batch.executions[main.batch.source_evaluation_indices[0]];
        let VmExit::Returned(returned) = &execution.exit else {
            panic!("Token.on must return")
        };
        assert!(!returned.value.is_scalar());
        assert_eq!(returned.value.header().tag, 1);
        let VmExit::Returned(replayed) =
            fln::execute_flbc_artifact(&execution.flbc_artifact, &options, Default::default())
                .unwrap()
                .into_complete()
                .unwrap()
        else {
            panic!("imported macro bytecode must replay")
        };
        assert!(!replayed.value.is_scalar());
        assert_eq!(replayed.value.header().tag, 1);
        assert_eq!(returned.usage.steps, replayed.usage.steps);
    });
    assert!(imported.engine.environment().is_empty());
    assert_eq!(imported.engine.logical_root(&options), before);
}

#[test]
fn olean_export_refuses_unrepresentable_grammar_instead_of_losing_it() {
    let base = Engine::builder().build_empty();
    for source in [
        "prelude\nnotation \"UnitType\" => Type\ndef identity (A : UnitType) (x : A) : A := x",
        "prelude\nsection\nlocal notation \"UnitType\" => Type\ndef identity (A : UnitType) (x : A) : A := x\nend",
    ] {
        with_modules(&[("Main", source)], |inputs| {
            let checked = base
                .check_source_modules(inputs, &name("Main"), &KVMap::new(), limits())
                .unwrap()
                .into_complete()
                .unwrap();
            assert!(
                checked
                    .checked
                    .engine
                    .environment()
                    .contains(&name("identity"))
            );
            let error = base
                .compile_source_modules(
                    inputs,
                    &name("Main"),
                    &KVMap::new(),
                    limits(),
                    OleanWriteBudget::default(),
                )
                .unwrap_err();
            assert!(
                matches!(
                    error,
                    SourceModuleBuildError::Check(SourceModuleCheckError::Extension { .. })
                ),
                "{error:?}"
            );
        });
    }
    assert!(base.environment().is_empty());
}

#[test]
fn module_system_grammar_keeps_an_explicit_phase_and_visibility_boundary() {
    let base = Engine::builder().build_empty();
    let options = KVMap::new();
    let imported = SourceOleanImport::empty(&options);
    let phase_refused = |error: SourceModuleCheckError| {
        assert!(
            matches!(
                &error,
                SourceModuleCheckError::Source {
                    error: fln::SourceCheckError::Command { error, .. },
                    ..
                } if matches!(error.as_ref(), fln::EngineExecutionError::NotImplemented { feature }
                    if feature.contains("module-system"))
            ),
            "{error:?}"
        );
    };
    for files in [
        vec![("Main", "module\nprelude\nnotation \"UnitType\" => Type")],
        vec![
            (
                "Main",
                "module\nprelude\nimport Lib\ndef identity (A : UnitType) (x : A) : A := x",
            ),
            ("Lib", "prelude\nnotation \"UnitType\" => Type"),
        ],
        vec![
            ("Main", "module\nprelude\nimport Lib"),
            ("Lib", "prelude\nnotation \"UnitType\" => Type"),
        ],
        vec![
            ("Main", "module\nprelude\nimport Lib"),
            (
                "Lib",
                "prelude\nsection\nlocal notation \"UnitType\" => Type\nend",
            ),
        ],
    ] {
        let error = check(&base, &files).expect_err("phase metadata must not be invented");
        phase_refused(error);
        with_modules(&files, |inputs| {
            let error = imported
                .execute_source_modules(
                    inputs,
                    &name("Main"),
                    &options,
                    SourceProgramLimits::new(EngineExecutionLimits::new(
                        limits().source.admission.kernel,
                    )),
                    None,
                )
                .expect_err("an empty forwarding module must enforce the same phase boundary");
            phase_refused(error);
        });
    }
    assert!(base.environment().is_empty());
    assert!(imported.engine.environment().is_empty());
}

#[test]
fn ordered_macro_fallbacks_replay_their_distinct_source_buffers() {
    let library = r#"
namespace Earlier
def α : Nat := 10
syntax "remember! " term:max : term
macro_rules | `(remember! $x) => `(Nat.add $x α)
end Earlier
namespace Later
def α : Nat := 90
macro_rules
  | `(remember! 0) => `((17 : Nat))
  | `(remember! 1) => `((19 : Nat))
end Later
"#
    .replace('\n', "\r\n");
    let base = engine();
    let result = checked(
        &base,
        &[
            ("Lib", &library),
            (
                "Main",
                "import Lib\ntheorem a : remember! 2 = 12 := rfl\ntheorem b : remember! 0 = 17 := rfl\ntheorem c : remember! 1 = 19 := rfl",
            ),
        ],
    );
    let resumed = result.checked.engine;
    assert_eq!(
        resumed
            .check_source_files(
                &[b"theorem resumed : remember! 3 = 13 := rfl"],
                &KVMap::new(),
                limits().source,
            )
            .unwrap()
            .into_complete()
            .unwrap()
            .theorems,
        1
    );
    assert!(
        resumed
            .check_source_files(
                &[b"theorem wrong : remember! 3 = 93 := rfl"],
                &KVMap::new(),
                limits().source,
            )
            .is_err()
    );
}

#[test]
fn an_imported_macro_override_does_not_silently_keep_an_old_native_rule() {
    let base = engine();
    let result = checked(
        &base,
        &[
            (
                "Lib",
                "syntax \"imported! \" term:max : term\nmacro_rules | `(imported! $x) => `((8 : Nat))",
            ),
            ("Main", "import Lib\ntheorem t : imported! 0 = 8 := rfl"),
        ],
    );
    assert!(
        result
            .checked
            .engine
            .check_source_files(
                &[br#"
macro_rules | `(imported! $x) => do pure `((9 : Nat))
theorem wrong : imported! 0 = 8 := rfl
"#],
                &KVMap::new(),
                limits().source
            )
            .is_err()
    );
}

#[test]
fn terminal_module_errors_keep_the_query_offset_and_inner_parse_position() {
    let base = engine();
    let options = KVMap::new();
    let before = base.logical_root(&options);
    let execution = EngineExecutionLimits::new(limits().source.admission.kernel);
    let library = "def libValue : Nat := 7";
    let invalid = "-- 😀\r\nimport Lib\r\n\r\n#check unknownTerminal\r\n";
    let error = with_modules(&[("Main", invalid), ("Lib", library)], |inputs| {
        base.check_terminal_source_modules(inputs, &name("Main"), &options, execution)
    })
    .unwrap_err();
    assert!(error.to_string().contains("unknownTerminal"), "{error:?}");
    assert_eq!(
        error.primary_source_offset().map(|offset| offset.0),
        invalid.find("#check"),
        "an elaboration failure must retain the terminal command's file offset: {error:?}"
    );
    assert_eq!(base.logical_root(&options), before);
    assert!(!base.environment().contains(&name("libValue")));

    let malformed = "-- 😀\r\nimport Lib\r\n\r\n#check (7 : )\r\n";
    let error = with_modules(&[("Main", malformed), ("Lib", library)], |inputs| {
        base.check_terminal_source_modules(inputs, &name("Main"), &options, execution)
    })
    .unwrap_err();
    assert_eq!(
        error.primary_source_offset().map(|offset| offset.0),
        malformed.find(')'),
        "a token-precise parse failure must outrank the command fallback: {error:?}"
    );
    assert_eq!(base.logical_root(&options), before);

    let checked = with_modules(
        &[("Main", "import Lib\n#check libValue"), ("Lib", library)],
        |inputs| base.check_terminal_source_modules(inputs, &name("Main"), &options, execution),
    )
    .unwrap()
    .into_complete()
    .unwrap();
    assert_eq!(
        checked.check.checked_type,
        fln::Expr::const_(name("Nat"), Vec::new())
    );
    assert!(
        checked
            .definition_prefix
            .unwrap()
            .engine
            .environment()
            .contains(&name("libValue"))
    );
    assert_eq!(base.logical_root(&options), before);
}

#[test]
fn flat_nat_batch_errors_keep_file_offsets_without_publishing_the_prefix() {
    let base = engine();
    let options = KVMap::new();
    let before = base.logical_root(&options);
    let execution = EngineExecutionLimits::new(limits().source.admission.kernel);
    let first = "-- a longer first file\r\ndef firstValue : Nat := 7\r\n";
    let invalid = "-- 😀\r\ndef secondValue : Nat := unknownBatch\r\n";
    let error = base
        .execute_nat_definitions(&[first.as_bytes(), invalid.as_bytes()], &options, execution)
        .unwrap_err();
    assert!(error.to_string().contains("unknownBatch"), "{error:?}");
    assert!(matches!(
        &error,
        fln::EngineExecutionError::BatchCommand { index: 1, .. }
    ));
    assert_eq!(
        error.primary_source_offset().map(|offset| offset.0),
        invalid.find("def"),
        "a flattened command index must not erase its per-file offset: {error:?}"
    );
    assert_eq!(base.logical_root(&options), before);
    assert!(!base.environment().contains(&name("firstValue")));
    assert!(!base.environment().contains(&name("secondValue")));

    let checked = base
        .execute_nat_definitions(
            &[first.as_bytes(), b"def secondValue : Nat := firstValue + 1"],
            &options,
            execution,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(checked.executions.len(), 2);
    assert_eq!(
        fln::closed_vm_value(&checked.executions.last().unwrap().exit).unwrap(),
        Some(fln::ClosedVmValue::Scalar(8))
    );
    assert_eq!(base.logical_root(&options), before);
}
