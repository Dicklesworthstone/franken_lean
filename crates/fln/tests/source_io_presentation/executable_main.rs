//! Executable mains share the ordinarily admitted IO fixture. Arguments are
//! passed through the engine API as checked Lean data, never parsed as source.
#![forbid(unsafe_code)]
use super::*;
use fln::source_main::{MainExecution, MainExecutionError, MainOutcome};

fn execute_main(engine: &Engine, arguments: &[String]) -> MainExecution {
    engine
        .execute_main(arguments, &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("checked main must execute: {error:?}"))
        .into_complete()
        .unwrap_or_else(|reason| panic!("checked main must complete: {reason:?}"))
}

fn assert_code(execution: &MainExecution, expected: u32, replayed: Option<&VmExit>) {
    let outcome = match replayed {
        Some(exit) => execution.outcome_for_exit(exit),
        None => execution.outcome(),
    }
    .expect("the retained checked main contract must project its result");
    match outcome {
        MainOutcome::Returned { exit_code } => assert_eq!(exit_code, expected),
        raised => panic!("main must return status {expected}: {raised:?}"),
    }
    assert_eq!(execution.execution.evaluation_presentation(), None);
}

#[test]
fn admitted_main_signatures_preserve_arguments_full_exit_codes_and_once_only_actions() {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(|| {
            let Some(engine) = imported() else { return };
            let arguments: Vec<_> = [
                "λ🙂",
                "--vm-max-steps",
                "--",
                "",
                "a b",
                "\"\\\n",
                "; #eval 999",
            ]
            .map(str::to_owned)
            .into();
            for (source, expected) in [
                ("def main : IO Unit := pure ()", 0),
                ("def main : IO PUnit := pure PUnit.unit", 0),
                ("def main : IO UInt32 := pure 7", 7),
                ("def main (_args : List String) : IO Unit := pure ()", 0),
                (
                    "def main (_args : List String) : IO PUnit := pure PUnit.unit",
                    0,
                ),
                ("def main (_args : List String) : IO UInt32 := pure 7", 7),
                // The pin's one-binder shape check does not require an
                // explicit BinderInfo; argv is still supplied by the shell.
                ("def main {_args : List String} : IO UInt32 := pure 7", 7),
                ("def main : IO UInt32 := pure 0", 0),
                ("def main : IO UInt32 := pure 256", 256),
                ("def main : IO UInt32 := pure 4294967295", u32::MAX),
            ] {
                let candidate = checked(engine, source);
                let root = candidate.logical_root(&KVMap::new());
                let execution = execute_main(&candidate, &arguments);
                assert_code(&execution, expected, None);
                assert_code(&execution, expected, Some(&replay(&execution.execution)));
                assert_eq!(candidate.logical_root(&KVMap::new()), root);
            }

            // Lean's shell passes its original runtime options to main. A
            // lexical source option affects source checking, not that caller
            // contract, even though main uses the final source environment.
            let mut caller_options = KVMap::new();
            caller_options.insert(
                name("maxHeartbeats"),
                fln_core::options::DataValue::OfNat(200_000),
            );
            let scoped = engine
                .execute_source_commands_with_checks(
                    b"set_option maxHeartbeats 400000\ndef main : IO Unit := pure ()",
                    &caller_options,
                    limits(),
                )
                .unwrap()
                .into_complete()
                .unwrap();
            assert_eq!(
                scoped.scope.options.get_nat(&name("maxHeartbeats"), 0),
                400_000,
            );
            let caller_root = scoped.batch.engine.logical_root(&caller_options);
            let lexical_root = scoped.batch.engine.logical_root(&scoped.scope.options);
            assert_ne!(caller_root, lexical_root);
            let execution = scoped
                .execute_main(&[], &caller_options, limits())
                .unwrap()
                .into_complete()
                .unwrap();
            assert_eq!(execution.execution.base_logical_root, caller_root);
            assert_ne!(execution.execution.base_logical_root, lexical_root);
            assert_code(&execution, 0, None);
            assert_code(&execution, 0, Some(&replay(&execution.execution)));

            let definitions = checked(
                engine,
                r#"def alternativeMain : IO UInt32 := pure 37
def main : IO UInt32 := pure 7"#,
            );
            let replaced = Engine::from_environment(
                fln_elab::implemented_by::register(
                    definitions.environment(),
                    &name("main"),
                    &name("alternativeMain"),
                )
                .unwrap(),
            );
            let selected = execute_main(&replaced, &[]);
            assert_code(&selected, 37, None);
            assert_code(&selected, 37, Some(&replay(&selected.execution)));
            let Some(ConstantInfo::Defn(actual_to_nat)) =
                replaced.environment().find(&name("UInt32.toNat"))
            else {
                panic!("the actual UInt32 projection is required");
            };
            let mut type_ = &actual_to_nat.base.type_;
            while let fln::ExprNode::MData { expr, .. } = type_.node() {
                type_ = expr;
            }
            let fln::ExprNode::ForallE {
                binder_name,
                binder_type,
                binder_info,
                ..
            } = type_.node()
            else {
                panic!("the actual UInt32 projection has one argument");
            };
            // Preserve the actual projection's complete telescope, including
            // borrowed annotations, while independently admitting a new body.
            let mut replacement = actual_to_nat.clone();
            replacement.base.name = name("mainStatusConversionOverride");
            replacement.all = vec![replacement.base.name.clone()];
            replacement.value = Expr::lam(
                binder_name.clone(),
                binder_type.clone(),
                Expr::lit(fln_core::expr::Literal::Nat(
                    fln_core::expr::NatLit::from_u64(0),
                )),
                *binder_info,
            );
            let with_conversion = replaced
                .admit_declaration(Declaration::Defn(replacement), &KVMap::new(), admission())
                .unwrap()
                .into_complete()
                .unwrap()
                .engine;
            let redirected = Engine::from_environment(
                fln_elab::implemented_by::register(
                    with_conversion.environment(),
                    &name("UInt32.toNat"),
                    &name("mainStatusConversionOverride"),
                )
                .unwrap(),
            );
            let raw = redirected
                .execute_source_commands_with_checks(
                    b"#eval UInt32.toNat (37 : UInt32)",
                    &KVMap::new(),
                    limits(),
                )
                .unwrap()
                .into_complete()
                .unwrap();
            assert_eq!(
                fln::closed_vm_value(&raw.batch.executions[0].exit).unwrap(),
                Some(fln::ClosedVmValue::Scalar(0)),
                "the checked conversion replacement must really be active"
            );
            let selected = execute_main(&redirected, &[]);
            assert_code(&selected, 37, None);
            assert_code(&selected, 37, Some(&replay(&selected.execution)));

            let directory = Directory::new("main-arguments");
            let output = directory.0.join("arguments.txt");
            let source = format!(
                r#"def mainArgumentText (args : List String) : String :=
  match args with
  | [] => ""
  | arg :: rest => String.append "[" (String.append arg (String.append "]" (mainArgumentText rest)))
def main (args : List String) : IO UInt32 := do
  let h ← IO.FS.Handle.mk {} IO.FS.Mode.append
  h.putStr "begin"
  h.putStr (mainArgumentText args)
  h.putStr "end\n"
  return 7"#,
                quoted(&output),
            );
            // The normal declaration stream may compile main, but its IO
            // action remains deferred until the explicit main entry request.
            let batch = engine
                .execute_source_commands_with_checks(source.as_bytes(), &KVMap::new(), limits())
                .unwrap()
                .into_complete()
                .unwrap();
            assert!(!output.exists());
            let mut bounded_arguments = limits();
            bounded_arguments.ingress.max_literal_bytes =
                arguments.iter().map(String::len).sum::<usize>() - 1;
            let argument_error = batch
                .execute_main(&arguments, &KVMap::new(), bounded_arguments)
                .unwrap_err();
            assert!(
                matches!(
                    argument_error,
                    MainExecutionError::Limit {
                        resource: "argument bytes",
                        ..
                    }
                ),
                "{argument_error:?}"
            );
            assert!(
                !output.exists(),
                "argument refusal must precede the main action"
            );
            let expected = format!(
                "begin{}end\n",
                arguments
                    .iter()
                    .map(|argument| format!("[{argument}]"))
                    .collect::<String>(),
            );
            let original = batch.batch.engine.logical_root(&KVMap::new());
            let execution = batch
                .execute_main(&arguments, &KVMap::new(), limits())
                .unwrap()
                .into_complete()
                .unwrap();
            assert_code(&execution, 7, None);
            assert_code(&execution, 7, None);
            assert_eq!(std::fs::read(&output).unwrap(), expected.as_bytes());
            assert_code(&execution, 7, Some(&replay(&execution.execution)));
            assert_eq!(
                std::fs::read(&output).unwrap(),
                expected.repeat(2).as_bytes()
            );
            let empty = execute_main(&batch.batch.engine, &[]);
            assert_code(&empty, 7, None);
            assert_eq!(
                std::fs::read(&output).unwrap(),
                format!("{}beginend\n", expected.repeat(2)).as_bytes(),
            );
            assert_eq!(batch.batch.engine.logical_root(&KVMap::new()), original);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn admitted_main_selection_refuses_before_effects_and_retains_typed_exceptions() {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(|| {
            let Some(engine) = imported() else { return };
            let original = engine.logical_root(&KVMap::new());
            let arguments = ["one".to_owned()];
            // A root `main` of another type is the pin's compile error (`isValidMainType`,
            // vendored `Lean/Compiler/LCNF/Main.lean:69-80, 153-156`), so checking it refuses. As
            // `noncomputable` it generates no code and is admitted, as at the pin, and the
            // executable door still refuses to select it.
            for source in [
                "def main : Nat := 0",
                "def main : IO Nat := pure 0",
                "def main : BaseIO Unit := pure ()",
                "def main (_arg : String) : IO Unit := pure ()",
                "def main (_args : List String) (_extra : Nat) : IO Unit := pure ()",
                "def MainArgsAlias := List String\ndef main (_args : MainArgsAlias) : IO Unit := pure ()",
                "def MainActionAlias := IO Unit\ndef main : MainActionAlias := show MainActionAlias from (pure () : IO Unit)",
                "def MainResultAlias := Unit\ndef main : IO MainResultAlias := pure (show MainResultAlias from ())",
            ] {
                let refusal = engine
                    .check_source_files(
                        &[source.as_bytes()],
                        &KVMap::new(),
                        SourceCheckLimits::new(admission()),
                    )
                    .err()
                    .map(|error| format!("{error:?}"))
                    .unwrap_or_default();
                assert!(refusal.contains("InvalidMainType"), "{source}\n{refusal}");
                let uncompiled = source.replace("def main", "noncomputable def main");
                let candidate = checked(engine, &uncompiled);
                let error = candidate.execute_main(&arguments, &KVMap::new(), limits()).unwrap_err();
                assert!(
                    matches!(error, MainExecutionError::InvalidMainType),
                    "selection must refuse before compilation: {uncompiled}\n{error:?}"
                );
            }
            for (source, missing) in [
                ("", true),
                ("namespace MainNamespace\ndef main : IO Unit := pure ()\nend MainNamespace", true),
            ] {
                let candidate = if source.is_empty() { engine.clone() } else { checked(engine, source) };
                let error = candidate.execute_main(&arguments, &KVMap::new(), limits()).unwrap_err();
                assert!(matches!((&error, missing),
                    (MainExecutionError::MissingMain, true) |
                    (MainExecutionError::InvalidMainType, false)
                ), "selection must refuse before compilation: {source}\n{error:?}");
            }
            // A private source declaration needs its real module identity.
            // Checking the module retains the private declaration in this
            // local engine, but the executable door still selects root main.
            let module = name("PrivateExecutable");
            let private = engine
                .check_source_modules(
                    &[fln::SourceModuleInput {
                        name: &module,
                        source: b"module\nprelude\nprivate def main : IO Unit := pure ()",
                    }],
                    &module,
                    &KVMap::new(),
                    fln::source_check::modules::SourceModuleCheckLimits::new(
                        SourceCheckLimits::new(admission()),
                    ),
                )
                .unwrap()
                .into_complete()
                .unwrap()
                .checked
                .engine;
            let private_name =
                Name::num(name("_private.PrivateExecutable"), 0).append_core(&name("main"));
            assert!(private.environment().contains(&private_name));
            assert!(!private.environment().contains(&name("main")));
            assert!(matches!(
                private.execute_main(&arguments, &KVMap::new(), limits()),
                Err(MainExecutionError::MissingMain),
            ));
            assert_eq!(engine.logical_root(&KVMap::new()), original);

            let directory = Directory::new("main-refusal");
            let sentinel = directory.0.join("sentinel.txt");
            std::fs::write(&sentinel, b"unchanged\n").unwrap();
            let invalid = checked(engine, &format!(r#"noncomputable def main : IO Nat := do
  let h ← IO.FS.Handle.mk {} IO.FS.Mode.append
  h.putStr "invalid main ran\n"
  return 42"#, quoted(&sentinel)));
            assert!(matches!(invalid.execute_main(&arguments, &KVMap::new(), limits()),
                Err(MainExecutionError::InvalidMainType)));
            assert_eq!(std::fs::read(&sentinel).unwrap(), b"unchanged\n");

            let action = checked(engine, &format!(r#"def main : IO Unit := do
  let h ← IO.FS.Handle.mk {} IO.FS.Mode.append
  h.putStr "main ran\n""#, quoted(&sentinel)));
            // Changing only an explicit runtime contract registration must
            // not make an unrecognized IO closure count as a successful Unit.
            let foreign = Engine::from_environment(fln_elab::externs::register(
                action.environment(), &name("IO"),
                vec![fln_elab::externs::ExternEntry::Standard {
                    backend: name("all"), symbol: "foreign_main_io_world".to_owned(),
                }],
            ).unwrap());
            let error = foreign.execute_main(&arguments, &KVMap::new(), limits()).unwrap_err();
            assert!(matches!(error,
                MainExecutionError::UnsupportedContract { .. } |
                MainExecutionError::Preparation(fln::IngressError::UnsupportedNode { .. })
            ), "the checked IO world must refuse: {error:?}");
            assert_eq!(std::fs::read(&sentinel).unwrap(), b"unchanged\n");
            let mut stopped = limits();
            stopped.vm.max_steps = 0;
            let result = action.execute_main(&arguments, &KVMap::new(), stopped).unwrap();
            assert!(matches!(result, Outcome::Inconclusive(_)), "{result:?}");
            assert_eq!(std::fs::read(&sentinel).unwrap(), b"unchanged\n");

            let output = directory.0.join("exception.txt");
            let failing = checked(engine, &format!(r#"def main : IO UInt32 := do
  let h ← IO.FS.Handle.mk {} IO.FS.Mode.append
  h.putStr "before main exception\n"
  throw (IO.userError "main failure")"#, quoted(&output)));
            let execution = execute_main(&failing, &arguments);
            let MainOutcome::Raised { runtime_type, exit } = execution.outcome().unwrap() else {
                panic!("a main exception must remain distinct from a successful exit code");
            };
            assert_eq!(runtime_type, Expr::const_(name("IO.Error"), vec![]));
            assert_eq!(error_message(&execution.execution.engine, &exit), "main failure");
            assert_eq!(std::fs::read(&output).unwrap(), b"before main exception\n");
            let replayed = replay(&execution.execution);
            let MainOutcome::Raised { runtime_type, exit } = execution.outcome_for_exit(&replayed).unwrap() else {
                panic!("replayed main must retain its typed exception");
            };
            assert_eq!(runtime_type, Expr::const_(name("IO.Error"), vec![]));
            assert_eq!(error_message(&execution.execution.engine, &exit), "main failure");
            assert_eq!(std::fs::read(&output).unwrap(), b"before main exception\nbefore main exception\n");
            assert_eq!(engine.logical_root(&KVMap::new()), original);
        })
        .unwrap()
        .join()
        .unwrap();
}
