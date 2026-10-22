//! Checked IO result printing over independently admitted, selected pin declarations.
//!
//! The fixture admits the complete actual ST/Repr/ToString closure, then the
//! actual IO declarations used here with their independent artifact readings.
//! It does not claim admission of the complete Init.System.IO module closure.
#![forbid(unsafe_code)]

use fln::{
    Budget, ConstantInfo, Declaration, Engine, EngineAdmissionLimits, EngineExecutionLimits,
    Environment, EvaluationPresentation, EvaluationResultPresentation, Expr, IoEvaluationOutcome,
    KVMap, Name, Outcome, SourceCheckLimits, VmExit,
};
use std::path::{Path, PathBuf};
use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering};

#[path = "source_io_presentation/executable_main.rs"]
mod executable_main;
#[path = "source_io_presentation/fixture.rs"]
mod fixture;

const STACK: usize = 256 * 1024 * 1024;
const BYTES: usize = 256 * 1024 * 1024;
const DECLARATIONS: &str = r#"
structure IoPrintRecord where
  value : Bool
deriving Repr
inductive IoPrintTree where
  | leaf (value : Bool)
  | branch (left right : IoPrintTree)
deriving Repr
inductive IoBoth where | mk
instance : Repr IoBoth where
  reprPrec _ _ := Std.Format.text "selected IO Repr"
instance : ToString IoBoth where
  toString _ := "incorrect IO ToString"
inductive IoStringOnly where | mk
instance : ToString IoStringOnly where
  toString _ := "unquoted λ\nsecond line"
def IoPayloadAlias := Nat
instance : Repr IoPayloadAlias where
  reprPrec _ _ := Std.Format.text "aliased IO payload"
def IoActionAlias := IO Nat
def ioExposedAction : Void IO.RealWorld → EST.Out IO.Error IO.RealWorld Nat :=
  (pure 42 : IO Nat)
def IoSilentAlias := Unit
inductive IoMissingPrinter where | mk
class IoNeed where
  value : Nat
def ioNeeds [IoNeed] : Nat := 42
inductive IoPrinterMustNotRun where | mk
def ioPrinterWork : Nat → Std.Format
  | 0 => Std.Format.text "printer ran"
  | n + 1 => ioPrinterWork n
instance : Repr IoPrinterMustNotRun where
  reprPrec _ _ := ioPrinterWork 10000000
"#;

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn admission() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK))
}

fn limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(admission().kernel)
}

fn checked(engine: &Engine, source: &str) -> Engine {
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(admission()),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("ordinary source declarations pass both checkers")
        .engine
}

fn imported() -> Option<&'static Engine> {
    static ENGINE: OnceLock<Option<Engine>> = OnceLock::new();
    ENGINE
        .get_or_init(|| {
            let library = std::env::var_os("FLN_REFERENCE_LIB")
                .map(PathBuf::from)
                .filter(|path| path.is_dir());
            let Some(library) = library else {
                assert!(
                    std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                    "the actual pinned library is required"
                );
                eprintln!("SKIP: set FLN_REFERENCE_LIB to the pinned lib/lean");
                return None;
            };
            Some(checked(&fixture::admitted(&library), DECLARATIONS))
        })
        .as_ref()
}

struct Directory(PathBuf);

impl Directory {
    fn new(label: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "fln-io-presentation-{label}-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed),
        ));
        std::fs::create_dir(&path).unwrap();
        Self(path)
    }
}

impl Drop for Directory {
    fn drop(&mut self) {
        std::fs::remove_dir_all(&self.0).unwrap();
    }
}

fn quoted(path: &Path) -> String {
    // Rust's quoted form agrees with Lean for these generated ASCII paths.
    format!("{:?}", path.to_str().unwrap())
}

fn run(engine: &Engine, source: &str) -> fln::SourceCommandBatchExecution {
    engine
        .execute_source_commands_with_presentation(
            source.as_bytes(),
            &KVMap::new(),
            limits(),
            EvaluationPresentation::Lean,
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap_or_else(|reason| {
            panic!("the checked IO program must complete: {source}\n{reason:?}")
        })
}

fn replay(execution: &fln::DefinitionExecution) -> VmExit {
    let program =
        fln_comp::flbc::decode_canonical(&execution.flbc_artifact, limits().flbc_codec).unwrap();
    assert_eq!(
        fln_comp::flbc::encode_canonical(&program, limits().flbc_codec).unwrap(),
        execution.flbc_artifact,
    );
    fln::execute_flbc_artifact(
        &execution.flbc_artifact,
        &KVMap::new(),
        fln::FlbcExecutionLimits {
            codec: limits().flbc_codec,
            vm: limits().vm,
        },
    )
    .unwrap()
    .into_complete()
    .expect("canonical FLBC reruns the action and its selected printer")
}

fn replay_payload(exit: &VmExit, expected_tag: u8) -> VmExit {
    let VmExit::Returned(returned) = exit else {
        panic!("the IO entry must return its logical ST/EST packet: {exit:?}");
    };
    let packet = &returned.value;
    assert!(!packet.is_scalar());
    assert_eq!(packet.header().tag, expected_tag);
    assert_eq!(packet.header().other, 2);
    let world = packet.try_ctor_child(1).expect("retained world slot");
    assert!(world.is_scalar());
    assert_eq!(world.unbox(), 0);
    VmExit::Returned(fln_vm::interpreter::CompletedExecution {
        value: packet.try_ctor_child(0).expect("typed payload slot"),
        usage: returned.usage,
    })
}

fn assert_format(execution: &fln::DefinitionExecution, expected: &str, replayed: Option<&VmExit>) {
    assert_eq!(
        execution.evaluation_presentation(),
        Some(EvaluationResultPresentation::IoFormat { width: 120 }),
    );
    assert_eq!(execution.evaluation_format_width(), None);
    let Some(IoEvaluationOutcome::Returned { runtime_type, exit }) =
        execution.io_evaluation_outcome().unwrap()
    else {
        panic!("a successful checked IO Format payload is required");
    };
    assert_eq!(runtime_type, Expr::const_(name("Std.Format"), vec![]));
    assert_eq!(
        fln::source_format::render_vm(
            execution.engine.environment(),
            &runtime_type,
            &exit,
            120,
            Default::default(),
        )
        .unwrap(),
        expected,
    );
    if let Some(replayed) = replayed {
        assert_eq!(
            fln::source_format::render_vm(
                execution.engine.environment(),
                &runtime_type,
                &replay_payload(replayed, 0),
                120,
                Default::default(),
            )
            .unwrap(),
            expected,
        );
    }
}

fn assert_unit(execution: &fln::DefinitionExecution, replayed: &VmExit) {
    assert_eq!(
        execution.evaluation_presentation(),
        Some(EvaluationResultPresentation::IoUnit),
    );
    assert_eq!(execution.evaluation_format_width(), None);
    let Some(IoEvaluationOutcome::Returned { runtime_type, exit }) =
        execution.io_evaluation_outcome().unwrap()
    else {
        panic!("a successful checked silent Unit payload is required");
    };
    assert_eq!(
        runtime_type,
        Expr::const_(name("PUnit"), vec![fln_core::level::Level::one()]),
    );
    let Some(ConstantInfo::Ctor(constructor)) =
        execution.engine.environment().find(&name("PUnit.unit"))
    else {
        panic!("actual checked PUnit constructor");
    };
    assert_eq!((constructor.num_params, constructor.num_fields), (0, 0));
    assert!(!constructor.is_unsafe);
    for payload in [exit, replay_payload(replayed, 0)] {
        let VmExit::Returned(returned) = payload else {
            unreachable!()
        };
        assert!(!returned.value.is_scalar());
        assert_eq!(u32::from(returned.value.header().tag), constructor.cidx);
        assert_eq!(returned.value.header().other, 0);
        assert_eq!(returned.value.byte_size(), 8);
    }
}

#[test]
fn admitted_io_payloads_use_actual_printers_once_and_replay_without_exporting_candidates() {
    std::thread::Builder::new().stack_size(STACK).spawn(|| {
        let Some(engine) = imported() else { return; };
        let original = engine.logical_root(&KVMap::new());
        for (label, source, expected) in [
            ("IO Nat", "#eval (pure 42 : IO Nat)", "42"),
            ("BaseIO Nat", "#eval (pure 42 : BaseIO Nat)", "42"),
            ("IO String", r#"#eval (pure "λ\n\"🙂\"" : IO String)"#, r#""λ\n\"🙂\"""#),
            ("derived record", "#eval (pure (IoPrintRecord.mk true) : IO IoPrintRecord)", "{ value := true }"),
            ("recursive Repr", "#eval (pure (IoPrintTree.branch (IoPrintTree.leaf true) (IoPrintTree.leaf false)) : IO IoPrintTree)", "IoPrintTree.branch (IoPrintTree.leaf true) (IoPrintTree.leaf false)"),
            ("Repr priority", "#eval (pure IoBoth.mk : IO IoBoth)", "selected IO Repr"),
            ("ToString fallback", "#eval (pure IoStringOnly.mk : IO IoStringOnly)", "unquoted λ\nsecond line"),
            ("payload alias instance", "#eval (pure (show IoPayloadAlias from (42 : Nat)) : IO IoPayloadAlias)", "aliased IO payload"),
            ("action alias", "#eval (show IoActionAlias from (pure (42 : Nat) : IO Nat))", "42"),
            ("canonical EIO functor", "#eval (pure 42 : EIO IO.Error Nat)", "42"),
            ("exposed world arrow", "#eval ioExposedAction", "42"),
        ] {
            eprintln!("checked IO presentation: {label}");
            let result = run(engine, source);
            assert_eq!(result.batch.executions.len(), 1);
            assert_eq!(result.batch.engine.logical_root(&KVMap::new()), original);
            let execution = &result.batch.executions[0];
            let Declaration::Defn(candidate) = &execution.declaration else {
                panic!("ordinary checked printer application");
            };
            assert!(!result.batch.engine.environment().contains(&candidate.base.name));
            assert!(execution.engine.environment().contains(&candidate.base.name));
            assert_format(execution, expected, Some(&replay(execution)));
        }
        for source in [
            "#eval (pure () : IO Unit)",
            "#eval (pure () : BaseIO Unit)",
            "#eval (pure () : IO IoSilentAlias)",
        ] {
            let result = run(engine, source);
            let execution = &result.batch.executions[0];
            assert_unit(execution, &replay(execution));
        }

        let directory = Directory::new("exactly-once");
        let output = directory.0.join("effects.txt");
        let source = format!(r#"#eval show IO IoBoth from do
  let h ← IO.FS.Handle.mk {} IO.FS.Mode.append
  h.putStr "action\n"
  return IoBoth.mk"#, quoted(&output));
        let result = run(engine, &source);
        let execution = &result.batch.executions[0];
        assert_format(execution, "selected IO Repr", None);
        assert_eq!(std::fs::read(&output).unwrap(), b"action\n");
        let replayed = replay(execution);
        assert_format(execution, "selected IO Repr", Some(&replayed));
        assert_eq!(std::fs::read(&output).unwrap(), b"action\naction\n");
        assert_eq!(engine.logical_root(&KVMap::new()), original);

        let raw = engine.execute_source_commands_with_checks(
            b"#eval (pure 42 : IO Nat)", &KVMap::new(), limits(),
        ).unwrap().into_complete().unwrap();
        let execution = &raw.batch.executions[0];
        assert_eq!(execution.evaluation_presentation(), None);
        assert_eq!(execution.evaluation_format_width(), None);
        let Some(IoEvaluationOutcome::Returned { runtime_type, exit }) =
            execution.io_evaluation_outcome().unwrap()
        else { panic!("raw IO retains its checked Nat payload") };
        assert_eq!(runtime_type, Expr::const_(name("Nat"), vec![]));
        assert_eq!(fln::closed_vm_value(&exit).unwrap(), Some(fln::ClosedVmValue::Scalar(42)));
        assert_eq!(engine.logical_root(&KVMap::new()), original);
    }).unwrap().join().unwrap();
}

fn inner_error(mut error: &fln::EngineExecutionError) -> &fln::EngineExecutionError {
    while let fln::EngineExecutionError::BatchCommand { error: nested, .. } = error {
        error = nested;
    }
    error
}

fn reason(error: &fln::EngineExecutionError) -> &fln_elab::source::SourceInferenceError {
    let fln::EngineExecutionError::Frontend(fln::NatDefinitionFrontendError::Elaborate(
        fln_elab::NatDefinitionElabError::Inference(reason),
    )) = inner_error(error)
    else {
        panic!("typed elaboration refusal: {error:?}")
    };
    reason
}

fn error_message(engine: &Engine, exit: &VmExit) -> String {
    let Some(ConstantInfo::Ctor(constructor)) =
        engine.environment().find(&name("IO.Error.userError"))
    else {
        panic!("actual checked IO.Error.userError constructor");
    };
    let VmExit::Returned(returned) = exit else {
        panic!("logical checked exception value")
    };
    assert!(!returned.value.is_scalar());
    assert_eq!(u32::from(returned.value.header().tag), constructor.cidx);
    assert_eq!(returned.value.header().other, 1);
    let payload = VmExit::Returned(fln_vm::interpreter::CompletedExecution {
        value: returned.value.try_ctor_child(0).unwrap(),
        usage: returned.usage,
    });
    let Some(fln::ClosedVmValue::String(message)) = fln::closed_vm_value(&payload).unwrap() else {
        panic!("the actual user error stores a String");
    };
    message
}

#[test]
fn admitted_io_printing_refuses_before_effects_and_skips_printers_on_exceptions() {
    use fln_elab::source::SourceInferenceError;
    use fln_elab::source::evaluation::PrintingError;
    std::thread::Builder::new().stack_size(STACK).spawn(|| {
        let Some(engine) = imported() else { return; };
        let original = engine.logical_root(&KVMap::new());
        let directory = Directory::new("refusals");
        let sentinel = directory.0.join("sentinel.txt");
        std::fs::write(&sentinel, b"unchanged\n").unwrap();
        let action = |payload: &str, returned: &str| format!(r#"#eval show IO {payload} from do
  let h ← IO.FS.Handle.mk {} IO.FS.Mode.append
  h.putStr "forbidden\n"
  return {returned}"#, quoted(&sentinel));
        let refused = |source: &str| engine.execute_source_commands_with_presentation(
            source.as_bytes(), &KVMap::new(), limits(), EvaluationPresentation::Lean,
        ).unwrap_err();
        let missing = refused(&action("IoMissingPrinter", "IoMissingPrinter.mk"));
        assert!(matches!(reason(&missing), SourceInferenceError::EvaluationPrinting(PrintingError::MissingPrinter)), "{missing:?}");
        assert_eq!(std::fs::read(&sentinel).unwrap(), b"unchanged\n");
        let unresolved = refused(&action("Nat", "ioNeeds"));
        assert!(matches!(reason(&unresolved), SourceInferenceError::InstanceSynthesisRequired), "{unresolved:?}");
        assert_eq!(std::fs::read(&sentinel).unwrap(), b"unchanged\n");
        // Under the `lean` presentation a guarded action runs, as the pin's `#eval` runs it
        // inside `withIsolatedStreams`: its stdout is retained for the guard, its other
        // effects happen. Every other presentation still refuses it before any effect.
        for (payload, returned) in [("Unit", "()"), ("Nat", "42")] {
            let effect = directory.0.join(format!("guarded-{payload}.txt"));
            let source = format!(r#"#guard_msgs in
#eval show IO {payload} from do
  let h ← IO.FS.Handle.mk {} IO.FS.Mode.append
  h.putStr "written\n"
  IO.print "printed λ"
  return {returned}"#, quoted(&effect));
            let guarded = engine.execute_source_commands_with_presentation(
                source.as_bytes(), &KVMap::new(), limits(), EvaluationPresentation::Lean,
            ).unwrap().into_complete().unwrap();
            assert_eq!(guarded.batch.executions[0].captured_stdout(), Some("printed λ".as_bytes()));
            assert_eq!(std::fs::read(&effect).unwrap(), b"written\n");
        }
        // An action that raises keeps what it wrote before raising: the pin logs that output
        // ahead of the exception.
        let raised = engine.execute_source_commands_with_presentation(
            "#eval show IO Nat from do\n  IO.print \"before λ\"\n  throw (IO.userError \"raised\")".as_bytes(),
            &KVMap::new(), limits(), EvaluationPresentation::Lean,
        ).unwrap().into_complete().unwrap();
        assert_eq!(raised.batch.executions[0].captured_stdout(), Some("before λ".as_bytes()));
        let raw = engine.execute_source_commands_with_presentation(
            format!("#guard_msgs in\n{}", action("IoBoth", "IoBoth.mk")).as_bytes(),
            &KVMap::new(), limits(), EvaluationPresentation::PreferRaw,
        ).unwrap_err();
        assert!(matches!(inner_error(&raw), fln::EngineExecutionError::NotImplemented {
            feature: "`#guard_msgs` over an IO action",
        }), "{raw:?}");
        assert_eq!(std::fs::read(&sentinel).unwrap(), b"unchanged\n");

        // Silent Unit has no printer options or MessageData requirement. The
        // same inputs remain explicit refusals when a payload needs printing.
        let mut options = KVMap::new();
        options.insert(name("format.width"), fln_core::options::DataValue::OfNat(80));
        options.insert(name("eval.type"), fln_core::options::DataValue::OfBool(true));
        for source in ["#eval (pure () : IO Unit)", "#eval (pure () : IO IoSilentAlias)"] {
            let result = engine.execute_source_commands_with_presentation(
                source.as_bytes(), &options, limits(), EvaluationPresentation::Lean,
            ).unwrap().into_complete().unwrap();
            let execution = &result.batch.executions[0];
            assert_unit(execution, &replay(execution));
        }
        let option_refusal = engine.execute_source_commands_with_presentation(
            b"#eval (pure 42 : IO Nat)", &options, limits(), EvaluationPresentation::Lean,
        ).unwrap_err();
        assert!(matches!(reason(&option_refusal), SourceInferenceError::EvaluationPrinting(
            PrintingError::UnsupportedOption(option),
        ) if option == &name("format.width")));
        // This is a checked presence sentinel for the existing unsupported
        // MessageData gate, not an implementation or imported MessageData model.
        let message_engine = checked(engine, "def Lean.MessageData.ofFormat : Nat := 0");
        let unit = run(&message_engine, "#eval (pure () : IO Unit)");
        assert_unit(&unit.batch.executions[0], &replay(&unit.batch.executions[0]));
        let message_refusal = message_engine.execute_source_commands_with_presentation(
            b"#eval (pure 42 : IO Nat)", &KVMap::new(), limits(), EvaluationPresentation::Lean,
        ).unwrap_err();
        assert!(matches!(reason(&message_refusal), SourceInferenceError::EvaluationPrinting(PrintingError::MessageData)));

        // Mapping to a canonical IO Format type must not discard explicit
        // foreign metadata on the original action's alias before checking it.
        let alias_engine = checked(engine, &format!(r#"def ioForeignAction : IoActionAlias := do
  let h ← IO.FS.Handle.mk {} IO.FS.Mode.append
  h.putStr "forbidden alias\n"
  return 42"#, quoted(&sentinel)));
        let foreign = Engine::from_environment(fln_elab::externs::register(
            alias_engine.environment(), &name("IoActionAlias"),
            vec![fln_elab::externs::ExternEntry::Standard {
                backend: name("all"), symbol: "foreign_io_alias_must_not_be_erased".to_owned(),
            }],
        ).unwrap());
        let foreign_root = foreign.logical_root(&KVMap::new());
        let foreign_refusal = foreign.execute_source_commands_with_presentation(
            b"#eval ioForeignAction", &KVMap::new(), limits(), EvaluationPresentation::Lean,
        ).unwrap_err();
        assert!(matches!(inner_error(&foreign_refusal),
            fln::EngineExecutionError::Ingress(fln::IngressError::UnsupportedNode { .. })));
        assert_eq!(std::fs::read(&sentinel).unwrap(), b"unchanged\n");
        assert_eq!(foreign.logical_root(&KVMap::new()), foreign_root);
        let failed_batch = refused("def IoMustNotEscape := 7\n#eval (pure 42 : IO Nat)\n#eval (pure IoMissingPrinter.mk : IO IoMissingPrinter)");
        assert!(matches!(reason(&failed_batch), SourceInferenceError::EvaluationPrinting(PrintingError::MissingPrinter)));
        assert!(!engine.environment().contains(&name("IoMustNotEscape")));
        assert_eq!(engine.logical_root(&KVMap::new()), original);

        // Establish that the selected checked printer cannot complete under
        // these unchanged VM limits, then prove an exception bypasses it.
        let would_print = engine.execute_source_commands_with_presentation(
            b"#eval (pure IoPrinterMustNotRun.mk : IO IoPrinterMustNotRun)",
            &KVMap::new(), limits(), EvaluationPresentation::Lean,
        ).unwrap();
        let Outcome::Inconclusive(stopped) = would_print else {
            panic!("the ten-million-step printer must exhaust the ordinary runtime budget");
        };
        assert!(matches!(stopped.cause, fln_core::outcome::InconclusiveCause::ResourceExhausted { usage }
            if matches!(usage.reason, fln_core::diag::ResourceReason::ExecutionSteps | fln_core::diag::ResourceReason::RecursionDepth { .. })));
        let output = directory.0.join("exception-prefix.txt");
        let source = format!(r#"#eval show IO IoPrinterMustNotRun from do
  let h ← IO.FS.Handle.mk {} IO.FS.Mode.append
  h.putStr "before exception\n"
  throw (IO.userError "expected failure")"#, quoted(&output));
        let result = run(engine, &source);
        let execution = &result.batch.executions[0];
        assert_eq!(execution.evaluation_presentation(), Some(EvaluationResultPresentation::IoFormat { width: 120 }));
        let Some(IoEvaluationOutcome::Raised { runtime_type, exit }) = execution.io_evaluation_outcome().unwrap() else {
            panic!("an exception must remain distinct from the successful Format payload");
        };
        assert_eq!(runtime_type, Expr::const_(name("IO.Error"), vec![]));
        assert_eq!(error_message(&execution.engine, &exit), "expected failure");
        assert_eq!(std::fs::read(&output).unwrap(), b"before exception\n");
        assert_eq!(error_message(&execution.engine, &replay_payload(&replay(execution), 1)), "expected failure");
        assert_eq!(std::fs::read(&output).unwrap(), b"before exception\nbefore exception\n");
        assert_eq!(engine.logical_root(&KVMap::new()), original);
    }).unwrap().join().unwrap();
}
