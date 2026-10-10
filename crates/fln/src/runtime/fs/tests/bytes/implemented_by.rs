//! Executable replacements reuse exact native contracts and deferred IO.
//! The raw pinned fixture supplies comparison data; every replacement source
//! below is separately admitted before its checked registration is installed.
use super::*;

const ORIGINAL: &str = "replacementWrite";
const SOURCE_BYTES: &str =
    "ByteArray.mk (Array.mk [UInt8.ofNat 0, UInt8.ofNat 255, UInt8.ofNat 128, UInt8.ofNat 10])";
const EXPECTED: &[u8] = &[0, 255, 128, 10];

fn write_environment(raw: &Environment, omit: Option<&str>, primitive: bool) -> Environment {
    let environment = fs::WRITE_BYTE_HELPERS
        .into_iter()
        .filter(|helper| Some(*helper) != omit)
        .fold(environment(raw), |environment, helper| {
            helper_extern(&environment, helper, false)
        });
    if primitive {
        register_one(&environment, Operation::Write, false)
    } else {
        environment
    }
}

fn registered_write(environment: &Environment) -> Engine {
    let Some(ConstantInfo::Opaque(target)) = environment.find(&Operation::Write.source_name())
    else {
        panic!("the pinned write target is opaque")
    };
    let original = name(ORIGINAL);
    let mut base = target.base.clone();
    base.name = original.clone();
    // Keep the exact borrowed metadata in the signature. The ordinary logical
    // body is the pin's inert default, not an executable native write.
    let admitted = Engine::from_environment(environment.clone())
        .admit_declaration(
            Declaration::Defn(DefinitionVal {
                base,
                value: target.value.clone(),
                hints: ReducibilityHints::Regular(1),
                safety: DefinitionSafety::Safe,
                all: vec![original.clone()],
            }),
            &KVMap::new(),
            EngineAdmissionLimits::for_stack_bytes(STACK),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        admitted.checker.ground,
        CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
    );
    let environment = fln_elab::implemented_by::register(
        &admitted.engine.environment,
        &original,
        &Operation::Write.source_name(),
    )
    .unwrap();
    Engine::from_environment(environment)
}

#[test]
fn implemented_by_native_seed_executes_without_an_ordinary_body() {
    let base = Engine::with_source_seed(EngineAdmissionLimits::for_stack_bytes(STACK))
        .unwrap()
        .into_complete()
        .unwrap();
    let checked = base
        .check_source_files(
            &[b"def replacementLength (s : String) : Nat := 0\ndef lengthAlias := replacementLength"],
            &KVMap::new(),
            SourceCheckLimits::new(EngineAdmissionLimits::for_stack_bytes(STACK)),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    assert!(matches!(
        checked.environment.find(&name("String.length")),
        Some(ConstantInfo::Axiom(_))
    ));
    let environment = fln_elab::implemented_by::register(
        &checked.environment,
        &name("replacementLength"),
        &name("String.length"),
    )
    .unwrap();
    let engine = Engine::from_environment(environment);
    let logical = engine
        .check_source_files(
            &[b"theorem stillLogical : replacementLength \"abcd\" = 0 := by rfl"],
            &KVMap::new(),
            SourceCheckLimits::new(EngineAdmissionLimits::for_stack_bytes(STACK)),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(logical.engine.environment.contains(&name("stillLogical")));
    for expression in [
        "replacementLength \"abcd\"",
        "lengthAlias \"abcd\"",
        "let apply := fun (f : String -> Nat) => f \"abcd\"; apply replacementLength",
    ] {
        let batch = run(&engine, &format!("#eval {expression}"));
        let execution = evaluation(&batch);
        assert_eq!(
            fln_vm::interpreter::nat_decimal(returned(&execution.exit)).as_deref(),
            Some("4")
        );
        let replay =
            execute_flbc_artifact(&execution.flbc_artifact, &KVMap::new(), Default::default())
                .unwrap()
                .into_complete()
                .unwrap();
        assert_eq!(
            fln_vm::interpreter::nat_decimal(returned(&replay)).as_deref(),
            Some("4")
        );
    }
}

#[test]
fn implemented_by_native_binary_write_defers_aliases_and_replays_effects() {
    let Some(raw) = raw_bytes_environment() else {
        return;
    };
    let engine = registered_write(&write_environment(&raw, None, true));
    let directory = directory("implemented-by-bytes");
    let output = directory.join("output.bin");
    std::fs::write(&output, b"preserved").unwrap();
    let saved = run(
        &engine,
        &format!(
            "def writeAlias := {ORIGINAL}\ndef savedWrite : IO Unit := do\n  let h ← IO.FS.Handle.mk {} IO.FS.Mode.append\n  let bytes := {SOURCE_BYTES}\n  let action := writeAlias h bytes\n  action\n  action",
            quoted(&output)
        ),
    );
    assert_eq!(std::fs::read(&output).unwrap(), b"preserved");
    let batch = run(&saved.batch.engine, "#eval savedWrite");
    let execution = evaluation(&batch);
    assert_unit(&execution.exit);
    let program = assert_rows(execution, &[Operation::Open, Operation::Write]);
    let mut expected = b"preserved".to_vec();
    expected.extend(EXPECTED.repeat(2));
    assert_eq!(std::fs::read(&output).unwrap(), expected);

    std::fs::write(&output, b"fresh").unwrap();
    let replay = execute_golem_with_options(&program, &KVMap::new(), VmExecutionLimits::default())
        .into_complete()
        .unwrap();
    assert_unit(&replay);
    let mut expected = b"fresh".to_vec();
    expected.extend(EXPECTED.repeat(2));
    assert_eq!(std::fs::read(&output).unwrap(), expected);
}

#[test]
fn implemented_by_native_write_errors_remain_catchable() {
    let Some(raw) = raw_bytes_environment() else {
        return;
    };
    let engine = registered_write(&write_environment(&raw, None, true));
    let directory = directory("implemented-by-write-error");
    let input = directory.join("read-only.bin");
    let recovered = directory.join("recovered.bin");
    std::fs::write(&input, b"unchanged").unwrap();
    let source = format!(
        "#eval do\n  let h ← IO.FS.Handle.mk {} IO.FS.Mode.read\n  {ORIGINAL} h ({SOURCE_BYTES})",
        quoted(&input)
    );
    let batch = run(&engine, &source);
    assert_error(&evaluation(&batch).exit, 12, 9, None, "Bad file descriptor");
    let source = format!(
        "#eval do\n  let h ← IO.FS.Handle.mk {} IO.FS.Mode.read\n  try\n    {ORIGINAL} h ({SOURCE_BYTES})\n  catch _ =>\n    IO.FS.writeBinFile {} ({SOURCE_BYTES})",
        quoted(&input),
        quoted(&recovered)
    );
    let batch = run(&engine, &source);
    assert_unit(&evaluation(&batch).exit);
    assert_eq!(std::fs::read(&input).unwrap(), b"unchanged");
    assert_eq!(std::fs::read(&recovered).unwrap(), EXPECTED);
}

#[test]
fn implemented_by_native_write_rejects_incomplete_contracts_and_exhaustion() {
    let Some(raw) = raw_bytes_environment() else {
        return;
    };
    let exact = write_environment(&raw, None, true);
    let engine = registered_write(&exact);
    let limits = IngressLimits::default();
    let mut preparation = Preparation::new(&engine.environment, limits);
    assert_eq!(
        preparation.implementation_target(&name(ORIGINAL)).unwrap(),
        Some(Operation::Write.source_name())
    );
    let work = preparation.visited;
    let mut limited = Preparation::new(
        &engine.environment,
        IngressLimits {
            max_nodes: work - 1,
            ..limits
        },
    );
    assert!(matches!(
        limited.implementation_target(&name(ORIGINAL)),
        Err(IngressError::ResourceLimit { .. })
    ));

    let directory = directory("implemented-by-refusal");
    let output = directory.join("preserved.bin");
    std::fs::write(&output, b"never opened").unwrap();
    for invalid in [
        write_environment(&raw, None, false),
        register_one(&exact, Operation::Write, true),
        write_environment(&raw, Some("ByteArray.push"), true),
        helper_extern(&exact, "ByteArray.push", true),
    ] {
        let engine = registered_write(&invalid);
        let source = format!(
            "#eval do\n  let h ← IO.FS.Handle.mk {} IO.FS.Mode.write\n  {ORIGINAL} h ({SOURCE_BYTES})",
            quoted(&output)
        );
        assert!(
            engine
                .execute_source_commands_with_checks(
                    source.as_bytes(),
                    &KVMap::new(),
                    EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
                )
                .is_err()
        );
        assert_eq!(std::fs::read(&output).unwrap(), b"never opened");
    }

    // A safe, same-typed opaque value with an extra unused let is admitted,
    // but is not the exact native primitive model. Metadata cannot bless it.
    let target = Operation::Write.source_name();
    let Some(ConstantInfo::Opaque(original)) = raw.find(&target) else {
        panic!("the pinned opaque write")
    };
    let mut changed = original.clone();
    changed.value = Expr::let_e(
        name("unused"),
        c("Nat"),
        nat::literal(0),
        changed.value,
        true,
    );
    let without = raw
        .constants()
        .fold(Environment::new(), |environment, (label, constant)| {
            if label == &target {
                environment
            } else {
                environment.add_decl(constant.clone()).unwrap()
            }
        });
    let admitted = Engine::from_environment(without)
        .admit_declaration(
            Declaration::Opaque(changed),
            &KVMap::new(),
            EngineAdmissionLimits::for_stack_bytes(STACK),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let changed = registered_write(&write_environment(&admitted.engine.environment, None, true));
    assert!(matches!(
        Preparation::new(&changed.environment, limits).implementation_target(&name(ORIGINAL)),
        Err(IngressError::UnsupportedNode { .. })
    ));

    let unsafe_environment =
        raw.constants()
            .fold(Environment::new(), |environment, (label, constant)| {
                let mut constant = constant.clone();
                if label == &target {
                    let ConstantInfo::Opaque(value) = &mut constant else {
                        panic!("the pinned opaque write")
                    };
                    value.is_unsafe = true;
                }
                environment.add_decl(constant).unwrap()
            });
    let unsafe_engine = registered_write(&write_environment(&unsafe_environment, None, true));
    assert!(matches!(
        Preparation::new(&unsafe_engine.environment, limits).implementation_target(&name(ORIGINAL)),
        Err(IngressError::UnsupportedNode {
            kind: "implemented_by target has no supported safe or partial executable body"
        })
    ));
}
