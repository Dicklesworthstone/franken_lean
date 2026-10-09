//! Explicit IO evaluation over actual pinned declarations and metadata.
#![forbid(unsafe_code)]

use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{
    Budget, CheckerAdmissionGround, ConstantInfo, Engine, EngineExecutionLimits, Environment, Expr,
    FlbcExecutionLimits, IoEvaluationOutcome, KVMap, Name, OleanCheckLimits, OleanDecodeLimits,
    VmExit, execute_flbc_artifact,
};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

const STACK: usize = 256 * 1024 * 1024;
const BYTES: usize = 256 * 1024 * 1024;
type Parts = (Vec<u8>, Option<Vec<u8>>, Option<Vec<u8>>);

#[path = "runtime_io_evaluation/actual.rs"]
mod actual;
#[path = "runtime_io_evaluation/selected.rs"]
mod selected;

fn name(value: &str) -> Name {
    Name::from_components(value.split('.'))
}

fn reference_library() -> Option<PathBuf> {
    let library = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .filter(|path| path.is_dir());
    if library.is_none() {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "the pinned Reference library is required"
        );
        eprintln!("SKIP: set FLN_REFERENCE_LIB to the pinned lib/lean");
    }
    library
}

fn artifacts(library: &Path, root: &Name) -> BTreeMap<Name, Parts> {
    let mut pending = vec![root.clone()];
    let mut modules = BTreeMap::new();
    while let Some(module) = pending.pop() {
        if modules.contains_key(&module) {
            continue;
        }
        let path = library
            .join(module.to_display_string().replace('.', "/"))
            .with_extension("olean");
        let public = std::fs::read(&path).unwrap();
        pending.extend(fln::olean_module_imports(&public, OleanDecodeLimits::new(BYTES)).unwrap());
        let optional = |path: PathBuf| match std::fs::read(&path) {
            Ok(bytes) => Some(bytes),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
            Err(error) => panic!("{}: {error}", path.display()),
        };
        modules.insert(
            module,
            (
                public,
                optional(path.with_extension("olean.server")),
                optional(path.with_extension("olean.private")),
            ),
        );
    }
    modules
}

const PROGRAMS: [(&str, &str); 9] = [
    ("IO pure", "#eval (pure 42 : IO Nat)"),
    ("BaseIO pure", "#eval (pure 42 : BaseIO Nat)"),
    (
        "IO references",
        r#"#eval show IO Nat from do
  let reference ← IO.mkRef (0 : Nat)
  reference.set 37
  let previous ← reference.swap 42
  let current ← reference.get
  return Nat.add previous (Nat.sub current 37)"#,
    ),
    (
        "IO caught exception retains the mutation prefix",
        r#"#eval show IO Nat from do
  let reference ← IO.mkRef (0 : Nat)
  try
    reference.set 37
    throw (IO.userError "expected failure")
    reference.set 99
    return 0
  catch _ =>
    let current ← reference.get
    return Nat.add current 5"#,
    ),
    (
        "explicit EIO adapter",
        "#eval EIO.toIO IO.userError (pure 42 : EIO String Nat)",
    ),
    (
        "checked IO type alias",
        "def NativeAction := IO Nat\n#eval (show NativeAction from (pure 42 : IO Nat))",
    ),
    ("IO Unit", "#eval (pure () : IO Unit)"),
    ("IO Bool", "#eval (pure false : IO Bool)"),
    ("IO Unicode String", "#eval (pure \"λ🙂\" : IO String)"),
];

#[derive(Debug, PartialEq, Eq)]
enum Payload {
    Unit,
    Value(fln::ClosedVmValue),
}

fn success_payload(engine: &Engine, exit: &VmExit) -> Payload {
    if let Some(value) = fln::closed_vm_value(exit).unwrap() {
        return Payload::Value(value);
    }
    // Imported PUnit is an ordinary checked constructor, not a seed scalar.
    // Validate its actual layout; two failed scalar projections cannot stand
    // in for a successful Unit execution or a bytecode replay comparison.
    let Some(ConstantInfo::Ctor(constructor)) = engine.environment().find(&name("PUnit.unit"))
    else {
        panic!("the admitted Unit constructor is required");
    };
    assert_eq!(constructor.induct, name("PUnit"));
    assert_eq!(constructor.num_params, 0);
    assert_eq!(constructor.num_fields, 0);
    assert!(!constructor.is_unsafe);
    let VmExit::Returned(returned) = exit else {
        panic!("Unit must return its checked constructor");
    };
    assert!(!returned.value.is_scalar());
    assert_eq!(u32::from(returned.value.header().tag), constructor.cidx);
    assert_eq!(returned.value.header().other, 0);
    assert_eq!(returned.value.byte_size(), 8);
    Payload::Unit
}

fn expected_success(index: usize) -> (Expr, Payload) {
    if index == 6 {
        return (
            Expr::const_(name("PUnit"), vec![fln_core::level::Level::one()]),
            Payload::Unit,
        );
    }
    let (type_, value) = match index {
        0..=5 => ("Nat", fln::ClosedVmValue::Scalar(42)),
        7 => ("Bool", fln::ClosedVmValue::Scalar(0)),
        8 => ("String", fln::ClosedVmValue::String("λ🙂".to_owned())),
        _ => panic!("unexpected success case"),
    };
    (Expr::const_(name(type_), vec![]), Payload::Value(value))
}

fn compare_packet(engine: &Engine, first: &VmExit, replay: &VmExit) {
    let project = |exit: &VmExit| {
        let VmExit::Returned(returned) = exit else {
            panic!("IO bytecode must return its logical result packet");
        };
        let packet = &returned.value;
        assert!(!packet.is_scalar());
        assert_eq!(packet.header().other, 2);
        let world = packet.try_ctor_child(1).expect("world field");
        assert!(world.is_scalar());
        assert_eq!(world.unbox(), 0);
        let payload = packet.try_ctor_child(0).expect("result field");
        match packet.header().tag {
            0 => {
                let payload = VmExit::Returned(fln_vm::interpreter::CompletedExecution {
                    value: payload,
                    usage: returned.usage,
                });
                let value = success_payload(engine, &payload);
                (0, value)
            }
            1 => {
                // Read the actual admitted constructor metadata instead of
                // guessing an IO.Error tag from its familiar printed name.
                let Some(ConstantInfo::Ctor(constructor)) =
                    engine.environment().find(&name("IO.Error.userError"))
                else {
                    panic!("the actual error family supplies userError");
                };
                assert_eq!(constructor.induct, name("IO.Error"));
                assert_eq!(constructor.num_params, 0);
                assert_eq!(constructor.num_fields, 1);
                assert!(!payload.is_scalar());
                assert_eq!(u32::from(payload.header().tag), constructor.cidx);
                assert_eq!(payload.header().other, 1);
                let message = payload.try_ctor_child(0).expect("message field");
                let message = VmExit::Returned(fln_vm::interpreter::CompletedExecution {
                    value: message,
                    usage: returned.usage,
                });
                let Some(fln::ClosedVmValue::String(message)) =
                    fln::closed_vm_value(&message).unwrap()
                else {
                    panic!("IO.userError retains its actual String payload");
                };
                assert_eq!(message, "expected failure");
                (1, Payload::Value(fln::ClosedVmValue::String(message)))
            }
            tag => panic!("invalid logical result tag {tag}"),
        }
    };
    assert_eq!(project(first), project(replay));
}

fn assert_deferred(execution: &fln::DefinitionExecution) {
    assert!(execution.io_evaluation_outcome().unwrap().is_none());
    let VmExit::Returned(value) = &execution.exit else {
        panic!("ordinary IO definition must return its deferred closure");
    };
    assert_eq!(fln::vm_value_kind(&value.value), fln::VmValueKind::Closure);
    assert!(matches!(
        execution.runtime_type.node(),
        fln::ExprNode::ForallE { .. }
    ));
}

fn assert_unsupported_command(engine: &Engine, source: &str) {
    let options = KVMap::new();
    let before = engine.logical_root(&options);
    let error = engine
        .execute_source_commands_with_checks(
            source.as_bytes(),
            &options,
            EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
        )
        .expect_err("this monad has no checked IO evaluation adapter");
    let fln::EngineExecutionError::BatchCommand { error, .. } = error else {
        panic!("expected command-level refusal");
    };
    assert!(
        matches!(
            *error,
            fln::EngineExecutionError::Ingress(fln::IngressError::UnsupportedNode { .. })
        ),
        "{error:?}"
    );
    assert_eq!(engine.logical_root(&options), before);
}

fn check_programs(engine: &Engine) {
    let options = KVMap::new();
    let before = engine.logical_root(&options);
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(STACK));
    for (case, (label, source)) in PROGRAMS.into_iter().enumerate() {
        let run = || {
            engine
                .execute_source_commands_with_checks(source.as_bytes(), &options, limits)
                .unwrap_or_else(|error| panic!("{label}: {error:?}"))
                .into_complete()
                .unwrap()
        };
        let first = run();
        assert_eq!(first.batch.source_evaluation_indices.len(), 1, "{label}");
        let index = first.batch.source_evaluation_indices[0];
        let execution = &first.batch.executions[index];
        assert_eq!(execution.checker.schema, "fln.checker-admission/1");
        assert_eq!(
            execution.checker.ground,
            CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
        );
        let Some(IoEvaluationOutcome::Returned { runtime_type, exit }) =
            execution.io_evaluation_outcome().unwrap()
        else {
            panic!("{label}: explicit IO evaluation must return a typed value");
        };
        let (expected_type, expected_value) = expected_success(case);
        assert_eq!(runtime_type, expected_type);
        assert_eq!(success_payload(engine, &exit), expected_value);
        let replay = execute_flbc_artifact(
            &execution.flbc_artifact,
            &options,
            FlbcExecutionLimits::default(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
        compare_packet(engine, &execution.exit, &replay);
        let repeated = run();
        assert_eq!(
            execution.flbc_artifact,
            repeated.batch.executions[repeated.batch.source_evaluation_indices[0]].flbc_artifact,
            "{label}"
        );
        assert_eq!(engine.logical_root(&options), before, "{label}");
        eprintln!("Explicit IO program passed: {label}");
    }
    for source in [
        "#eval (throw (IO.userError \"expected failure\") : IO Nat)",
        "#eval EIO.toIO IO.userError (throw \"expected failure\" : EIO String Nat)",
    ] {
        let completed = engine
            .execute_source_commands_with_checks(source.as_bytes(), &options, limits)
            .unwrap()
            .into_complete()
            .unwrap();
        assert_eq!(completed.batch.source_evaluation_indices.len(), 1);
        let execution = &completed.batch.executions[completed.batch.source_evaluation_indices[0]];
        let Some(IoEvaluationOutcome::Raised { runtime_type, exit }) =
            execution.io_evaluation_outcome().unwrap()
        else {
            panic!("uncaught IO exception must be distinct from a successful result");
        };
        assert_eq!(runtime_type, Expr::const_(name("IO.Error"), vec![]));
        assert!(matches!(exit, VmExit::Returned(_)));
        let replay = execute_flbc_artifact(
            &execution.flbc_artifact,
            &options,
            FlbcExecutionLimits::default(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
        compare_packet(engine, &execution.exit, &replay);
        assert_eq!(engine.logical_root(&options), before);
    }

    let dormant = engine
        .execute_source_definitions(
            &[b"def dormant : IO Nat := throw (IO.userError \"must stay deferred\")"],
            &options,
            limits,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(dormant.executions.len(), 1);
    assert_deferred(&dormant.executions[0]);
    assert_eq!(engine.logical_root(&options), before);
    assert_unsupported_command(engine, "#eval (pure 42 : EIO String Nat)");
}

#[test]
fn raw_actual_io_metadata_diagnostic_is_not_module_admission() {
    let Some(library) = reference_library() else {
        return;
    };
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let fixture = actual::decoded_io_with_source_metadata(&library);
            check_programs(&fixture.engine);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn retained_selected_io_runtime_diagnostic_is_not_module_admission() {
    let Some(fixture) = std::env::var_os("FLN_IO_SELECTED_FIXTURE_INPUT").map(PathBuf::from) else {
        eprintln!("SKIP: set FLN_IO_SELECTED_FIXTURE_INPUT to a retained selected IO fixture");
        return;
    };
    let library = reference_library().expect("the retained diagnostic requires the actual pin");
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            // Fast runtime isolation after the authoritative test has retained
            // its fixture. This raw installation creates no admission or reuse
            // receipt and cannot satisfy the independent module-admission gate.
            let mut environment = fln::Environment::new();
            for module in [
                "Init/Prelude",
                "Init/System/ST",
                "Init/System/IOError",
                "Init/System/IO",
            ] {
                let path = library.join(module).with_extension("olean");
                let decoded = fln::decode_olean_module_artifacts(
                    &std::fs::read(&path).unwrap(),
                    &std::fs::read(path.with_extension("olean.server")).unwrap(),
                    &std::fs::read(path.with_extension("olean.private")).unwrap(),
                    OleanDecodeLimits::new(BYTES),
                )
                .unwrap();
                for info in decoded.constants {
                    if !environment.contains(info.name()) {
                        environment = environment.add_decl(info).unwrap();
                    }
                }
            }
            let decoded = fln::decode_olean_artifact(
                &std::fs::read(fixture).unwrap(),
                OleanDecodeLimits::new(BYTES),
            )
            .unwrap();
            for info in decoded.constants {
                if let Some(existing) = environment.find(info.name()) {
                    assert_eq!(existing, &info, "retained declarations must match the pin");
                } else {
                    environment = environment.add_decl(info).unwrap();
                }
            }
            for label in [
                "ST.Prim.mkRef",
                "ST.Prim.Ref.get",
                "ST.Prim.Ref.set",
                "ST.Prim.Ref.swap",
            ] {
                let row = fln_vm::extern_table_generated::EXTERN_ROWS
                    .iter()
                    .find(|row| row.name == label)
                    .unwrap();
                environment = fln_elab::externs::register(
                    &environment,
                    &name(label),
                    vec![fln_elab::externs::ExternEntry::Standard {
                        backend: name("all"),
                        symbol: row.symbol.to_owned(),
                    }],
                )
                .unwrap();
            }
            selected::check_selected_programs(Engine::from_environment(environment));
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn selected_pinned_io_declarations_execute_after_independent_admission_over_st() {
    let Some(library) = reference_library() else {
        return;
    };
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || selected::run(&library))
        .unwrap()
        .join()
        .unwrap();
}
