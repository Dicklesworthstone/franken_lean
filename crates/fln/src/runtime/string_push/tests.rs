//! Checked-source and retained bytecode probes over actual pinned metadata.
//! Loading this small raw fixture is not admission of its library modules.

use super::*;
use fln_comp::flbc::{self, Instruction};

const STACK: usize = 256 * 1024 * 1024;

fn raw_pin_environment() -> Option<Environment> {
    let Some(library) = std::env::var_os("FLN_REFERENCE_LIB").map(std::path::PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "the pinned Reference library is required"
        );
        eprintln!("SKIP: set FLN_REFERENCE_LIB to the pinned lib/lean");
        return None;
    };
    let mut environment = Environment::new();
    for module in [
        "Init/Prelude",
        "Init/Data/String/Bootstrap",
        "Init/Data/ToString/Basic",
        "Init/System/ST",
        "Init/System/IOError",
        "Init/System/IO",
    ] {
        let path = library.join(module).with_extension("olean");
        let decoded = decode_olean_module_artifacts(
            &std::fs::read(&path).unwrap(),
            &std::fs::read(path.with_extension("olean.server")).unwrap(),
            &std::fs::read(path.with_extension("olean.private")).unwrap(),
            OleanDecodeLimits::new(STACK),
        )
        .unwrap();
        for constant in decoded.constants {
            if !environment.contains(constant.name()) {
                environment = environment.add_decl(constant).unwrap();
            }
        }
    }
    Some(environment)
}

fn register(environment: &Environment, label: &str, foreign: bool) -> Environment {
    let row = fln_vm::extern_table_generated::EXTERN_ROWS
        .iter()
        .find(|row| row.name == label)
        .unwrap();
    fln_elab::externs::register(
        environment,
        &name(label),
        vec![fln_elab::externs::ExternEntry::Standard {
            backend: name("all"),
            symbol: if foreign {
                "foreign_string_push".to_owned()
            } else {
                row.symbol.to_owned()
            },
        }],
    )
    .unwrap()
}

fn run(engine: &Engine, source: &str) -> SourceCommandBatchExecution {
    engine
        .execute_source_commands_with_checks(
            source.as_bytes(),
            &KVMap::new(),
            EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap()
}

fn assert_result(exit: &VmExit, expected: &str) {
    assert_eq!(
        closed_vm_value(exit).unwrap(),
        Some(ClosedVmValue::String(expected.to_owned()))
    );
}

fn assert_io_unit_packet(exit: &VmExit) {
    let VmExit::Returned(returned) = exit else {
        panic!("println returns its logical IO packet");
    };
    assert!(!returned.value.is_scalar());
    assert_eq!(
        (returned.value.header().tag, returned.value.header().other),
        (0, 2)
    );
    let unit = returned.value.try_ctor_child(0).unwrap();
    assert!(!unit.is_scalar());
    assert_eq!(
        (unit.header().tag, unit.header().other, unit.byte_size()),
        (0, 0, 8)
    );
    let world = returned.value.try_ctor_child(1).unwrap();
    assert!(world.is_scalar());
    assert_eq!(world.unbox(), 0);
}

fn assert_row(execution: &DefinitionExecution) {
    let program =
        flbc::decode_canonical(&execution.flbc_artifact, flbc::CodecLimits::default()).unwrap();
    assert!(program.functions().iter().flat_map(|function| &function.code).any(|instruction| matches!(
        instruction,
        Instruction::Intrinsic { row, argument_ownership, result_ownership, .. }
            if row == "extern:String.push"
                && argument_ownership == &[ArgumentOwnership::Owned, ArgumentOwnership::Scalar]
                && *result_ownership == ResultOwnership::Owned
    )), "the checked Char must reach the genuine generated String.push row");
}

#[test]
fn string_push_requires_the_complete_pin_and_matching_extern() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    string_push::assert_pin_models(&raw);
    let limits = IngressLimits::default();
    assert!(
        !string_push::contract_matches(
            &raw,
            &string_push::source_name(),
            &mut None,
            &mut 0,
            limits
        )
        .unwrap()
    );
    let environment = register(&raw, "String.push", false);
    let mut work = 0;
    assert!(
        string_push::contract_matches(
            &environment,
            &string_push::source_name(),
            &mut None,
            &mut work,
            limits
        )
        .unwrap()
    );
    assert!(work > 0);
    assert!(matches!(
        string_push::contract_matches(
            &environment,
            &string_push::source_name(),
            &mut None,
            &mut 0,
            IngressLimits {
                max_nodes: work - 1,
                ..limits
            }
        ),
        Err(IngressError::ResourceLimit { .. })
    ));
    assert!(
        string_push::contract_matches(
            &register(&raw, "String.push", true),
            &string_push::source_name(),
            &mut None,
            &mut 0,
            limits
        )
        .is_err()
    );
    for target in [
        "String.push",
        "String.push.match_1",
        "Char.mk",
        "UInt32.ofBitVec",
        "BitVec.ofFin",
        "Fin.mk",
    ] {
        let altered = raw
            .constants()
            .fold(Environment::new(), |environment, (label, info)| {
                let mut info = info.clone();
                if label == &name(target) {
                    match &mut info {
                        ConstantInfo::Defn(value) => value.value = c("Nat.zero"),
                        ConstantInfo::Ctor(value) => value.num_fields += 1,
                        _ => unreachable!("fixed contract mutation"),
                    }
                }
                environment.add_decl(info).unwrap()
            });
        assert!(
            string_push::contract_matches(
                &register(&altered, "String.push", false),
                &string_push::source_name(),
                &mut None,
                &mut 0,
                limits
            )
            .is_err(),
            "mutated {target}"
        );
    }
    let mut preparation = Preparation::new(&environment, limits);
    assert!(
        preparation
            .string_push_call(&c("String.push"), &[])
            .unwrap()
            .is_some()
    );
    assert!(
        preparation
            .string_push_call(
                &Expr::const_(Name::from_components(["String.push"]), vec![]),
                &[]
            )
            .unwrap()
            .is_none()
    );
    let binding = preparation
        .string_push_intrinsic_binding(&name(PRIMITIVE))
        .unwrap();
    assert_eq!(binding.arguments, [ValueType::String, ValueType::Nat]);
    assert_eq!(
        binding.argument_ownership,
        [ArgumentOwnership::Owned, ArgumentOwnership::Scalar]
    );
    assert_eq!(binding.result, ValueType::String);
    assert_eq!(binding.effect, EffectClass::Pure);
    assert_eq!(
        preparation.value_type(&c("Char")).unwrap(),
        Some(ValueType::Constructor)
    );
}

#[test]
fn checked_string_push_preserves_characters_partial_applications_and_replay() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    let engine = Engine::from_environment(register(&raw, "String.push", false));
    let root = engine.logical_root(&KVMap::new());
    let cases = [
        ("#eval String.push \"λ\" (Char.ofNat 128578)", "λ🙂"),
        ("#eval \"snow\".push (Char.ofNat 9731)", "snow☃"),
        ("#eval String.push \"zero\" (Char.ofNat 0)", "zero\0"),
        (
            "#eval String.push \"limit\" (Char.ofNat 1114111)",
            "limit\u{10ffff}",
        ),
        (
            "def pushAlias : String → Char → String := String.push\n#eval pushAlias \"left\" (Char.ofNat 955)",
            "leftλ",
        ),
        (
            "def appendMark : Char → String := String.push \"saved\"\n#eval appendMark (Char.ofNat 128578)",
            "saved🙂",
        ),
        (
            "def nestedPush (s : String) (c : Char) : String := let append := String.push s; append c\n#eval nestedPush \"nested\" (Char.ofNat 9731)",
            "nested☃",
        ),
    ];
    for (source, expected) in cases {
        let batch = run(&engine, source);
        let index = batch.batch.source_evaluation_indices[0];
        let execution = &batch.batch.executions[index];
        assert_eq!(
            execution.checker.ground,
            CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
        );
        assert_result(&execution.exit, expected);
        assert_row(execution);
        let replay = execute_flbc_artifact(
            &execution.flbc_artifact,
            &KVMap::new(),
            FlbcExecutionLimits::default(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
        assert_result(&replay, expected);
        let repeated = run(&engine, source);
        let next = repeated.batch.source_evaluation_indices[0];
        assert_eq!(
            execution.flbc_artifact,
            repeated.batch.executions[next].flbc_artifact
        );
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn pinned_io_println_uses_string_push_and_writes_one_newline_per_execution() {
    const CHILD: &str = "FLN_STRING_PUSH_PRINTLN_CHILD";
    if std::env::var_os(CHILD).is_none() {
        if std::env::var_os("FLN_REFERENCE_LIB").is_none() {
            assert!(
                std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                "the pinned Reference library is required"
            );
            return;
        }
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", "runtime::string_push::tests::pinned_io_println_uses_string_push_and_writes_one_newline_per_execution", "--nocapture"])
            .env(CHILD, "1").output().unwrap();
        assert!(
            output.status.success(),
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        let bytes = String::from_utf8(output.stdout).unwrap();
        assert_eq!(bytes.matches("fln-println-marker-λ🙂\n").count(), 3);
        assert_eq!(bytes.matches("fln-println-dormant-marker").count(), 0);
        return;
    }
    let raw = raw_pin_environment().unwrap();
    let environment = register(&register(&raw, "String.push", false), "IO.getStdout", false);
    let engine = Engine::from_environment(environment);
    let deferred = run(
        &engine,
        "def savedPrintln : IO Unit := @IO.println String instToStringString \"fln-println-dormant-marker\"",
    );
    for execution in &deferred.batch.executions {
        let VmExit::Returned(returned) = &execution.exit else {
            panic!("deferred println must return its action");
        };
        assert!(returned.value.closure_shell_parts().is_some());
    }
    let batch = run(
        &engine,
        "#eval @IO.println String instToStringString \"fln-println-marker-λ🙂\"",
    );
    let execution = &batch.batch.executions[batch.batch.source_evaluation_indices[0]];
    assert_row(execution);
    assert_io_unit_packet(&execution.exit);
    for _ in 0..2 {
        let replay = execute_flbc_artifact(
            &execution.flbc_artifact,
            &KVMap::new(),
            FlbcExecutionLimits::default(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
        assert_io_unit_packet(&replay);
    }
}
