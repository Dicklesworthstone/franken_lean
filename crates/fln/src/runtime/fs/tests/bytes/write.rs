//! Checked logical bytes cross into a private native buffer only at the write.
use super::*;

fn write_environment(raw: &Environment, omit: Option<&str>) -> Environment {
    let environment = fs::WRITE_BYTE_HELPERS
        .into_iter()
        .filter(|helper| Some(*helper) != omit)
        .fold(environment(raw), |environment, helper| {
            helper_extern(&environment, helper, false)
        });
    register_one(&environment, Operation::Write, false)
}

const SOURCE_BYTES: &str = "ByteArray.mk (Array.mk [UInt8.ofNat 0, UInt8.ofNat 255, UInt8.ofNat 128, UInt8.ofNat 10, UInt8.ofNat 226, UInt8.ofNat 130, UInt8.ofNat 90])";
const EXPECTED: &[u8] = &[0, 255, 128, 10, 226, 130, 90];

#[test]
fn binary_write_requires_exact_packing_dependencies_and_independent_externs() {
    let Some(raw) = raw_bytes_environment() else {
        return;
    };
    fs::assert_pin_models(&raw);
    fs::assert_pin_byte_layouts(&raw);
    fs::assert_pin_write_dependencies(&raw);
    let exact = write_environment(&raw, None);
    let limits = IngressLimits::default();
    let mut work = 0;
    assert!(fs::primitive_matches(&exact, Operation::Write, &mut None, &mut work, limits).unwrap());
    assert!(matches!(
        fs::primitive_matches(
            &exact,
            Operation::Write,
            &mut None,
            &mut 0,
            IngressLimits {
                max_nodes: work - 1,
                ..limits
            }
        ),
        Err(IngressError::ResourceLimit { .. })
    ));
    // A read conversion already cached in this preparation is no authority
    // for the distinct write primitive or its additional packing helpers.
    let only_read = environment(&raw);
    let mut preparation = Preparation::new(&only_read, limits);
    assert!(
        preparation
            .fs_call(&c("IO.FS.Handle.read"), &[])
            .unwrap()
            .is_some()
    );
    assert!(
        preparation
            .fs_call(&c("IO.FS.Handle.write"), &[])
            .unwrap()
            .is_none()
    );
    for helper in fs::WRITE_BYTE_HELPERS {
        let missing = write_environment(&raw, Some(helper));
        let mut preparation = Preparation::new(&missing, limits);
        assert!(
            preparation
                .fs_call(&c("IO.FS.Handle.read"), &[])
                .unwrap()
                .is_some()
        );
        assert!(
            preparation.fs_call(&c("IO.FS.Handle.write"), &[]).is_err(),
            "missing {helper}"
        );
        let foreign = helper_extern(&missing, helper, true);
        assert!(
            fs::primitive_matches(&foreign, Operation::Write, &mut None, &mut 0, limits).is_err(),
            "foreign {helper}"
        );
    }
    let foreign = register_one(&exact, Operation::Write, true);
    assert!(fs::primitive_matches(&foreign, Operation::Write, &mut None, &mut 0, limits).is_err());
    let mut preparation = Preparation::new(&exact, limits);
    assert!(
        preparation
            .fs_call(&c("IO.FS.Handle.write"), &[])
            .unwrap()
            .is_some()
    );
    let binding = preparation
        .fs_intrinsic_binding(&Operation::Write.private_name())
        .unwrap();
    assert_eq!(binding.arguments, [ValueType::Abi, ValueType::Abi]);
    assert_eq!(
        binding.argument_ownership,
        [ArgumentOwnership::Borrowed, ArgumentOwnership::Borrowed]
    );
    assert_eq!(binding.result_ownership, ResultOwnership::Owned);
}

#[test]
fn binary_write_rejects_a_checked_same_type_packing_mutant() {
    let Some(raw) = raw_bytes_environment() else {
        return;
    };
    let label = name("ByteArray.push");
    let Some(ConstantInfo::Defn(original)) = raw.find(&label) else {
        panic!("actual pinned ByteArray.push");
    };
    let mut changed = original.clone();
    // This is well typed, but would silently discard every appended byte.
    changed.value = Expr::lam(
        Name::anonymous(),
        c("ByteArray"),
        Expr::lam(
            Name::anonymous(),
            c("UInt8"),
            Expr::bvar(1).unwrap(),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let without = raw
        .constants()
        .fold(Environment::new(), |environment, (name, info)| {
            if name == &label {
                environment
            } else {
                environment.add_decl(info.clone()).unwrap()
            }
        });
    let admitted = Engine::from_environment(without)
        .admit_declaration(
            Declaration::Defn(changed),
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
    assert!(matches!(
        fs::primitive_matches(
            &write_environment(&admitted.engine.environment, None),
            Operation::Write,
            &mut None,
            &mut 0,
            IngressLimits::default()
        ),
        Err(IngressError::UnsupportedNode { .. })
    ));
}

#[test]
fn binary_write_checked_sources_preserve_raw_bytes_and_replay_live_effects() {
    let Some(raw) = raw_bytes_environment() else {
        return;
    };
    let engine = Engine::from_environment(write_environment(&raw, None));
    let root = engine.logical_root(&KVMap::new());
    let directory = directory("write-bytes");
    let input = directory.join("input.bin");
    let output = directory.join("output.bin");
    let output_path = quoted(&output);
    std::fs::write(&input, EXPECTED).unwrap();
    let source = format!(
        "#eval do\n  let input ← IO.FS.Handle.mk {} IO.FS.Mode.read\n  let bytes ← input.read 99\n  IO.FS.writeBinFile {output_path} bytes",
        quoted(&input)
    );
    let batch = run(&engine, &source);
    let execution = evaluation(&batch);
    assert_unit(&execution.exit);
    let program = assert_rows(
        execution,
        &[Operation::Open, Operation::Read, Operation::Write],
    );
    assert_eq!(std::fs::read(&output).unwrap(), EXPECTED);
    // Replay observes a new input, reconstructs logical bytes, and executes a
    // fresh write; no bytes or handles are serialized into the program.
    let changed = [255, 0, 254, 128];
    std::fs::write(&input, changed).unwrap();
    std::fs::write(&output, b"stale suffix must be truncated").unwrap();
    let exit = execute_golem_with_options(&program, &KVMap::new(), VmExecutionLimits::default())
        .into_complete()
        .unwrap();
    assert_unit(&exit);
    assert_eq!(std::fs::read(&output).unwrap(), changed);
    // Bytes supplied through ordinary constructors keep the same semantics.
    let batch = run(
        &engine,
        &format!("#eval IO.FS.writeBinFile {output_path} ({SOURCE_BYTES})"),
    );
    assert_unit(&evaluation(&batch).exit);
    assert_eq!(std::fs::read(&output).unwrap(), EXPECTED);
    let batch = run(
        &engine,
        &format!("#eval IO.FS.writeBinFile {output_path} (ByteArray.mk (Array.mk []))"),
    );
    assert_unit(&evaluation(&batch).exit);
    assert_eq!(std::fs::read(&output).unwrap(), b"");
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn binary_write_saved_actions_aliases_and_repeated_invocations_defer_effects() {
    let Some(raw) = raw_bytes_environment() else {
        return;
    };
    let engine = Engine::from_environment(write_environment(&raw, None));
    let directory = directory("saved-byte-writes");
    let output = directory.join("output.bin");
    let path = quoted(&output);
    std::fs::write(&output, b"survives construction").unwrap();
    let saved = run(
        &engine,
        &format!(
            "def bytes : ByteArray := {SOURCE_BYTES}\ndef savedWrite : IO Unit := IO.FS.writeBinFile {path} bytes\ndef writeHandle := IO.FS.Handle.write\ndef writeBinFile := IO.FS.writeBinFile"
        ),
    );
    assert_eq!(std::fs::read(&output).unwrap(), b"survives construction");
    let batch = run(&saved.batch.engine, "#eval savedWrite");
    assert_unit(&evaluation(&batch).exit);
    assert_eq!(std::fs::read(&output).unwrap(), EXPECTED);
    let batch = run(
        &saved.batch.engine,
        &format!("#eval writeBinFile {path} bytes"),
    );
    assert_unit(&evaluation(&batch).exit);
    assert_eq!(std::fs::read(&output).unwrap(), EXPECTED);
    let append = directory.join("append.bin");
    let saved = run(
        &saved.batch.engine,
        &format!(
            "def appendTwice : IO Unit := do\n  let h ← IO.FS.Handle.mk {} IO.FS.Mode.append\n  let alias := h\n  let write := writeHandle alias bytes\n  write\n  write",
            quoted(&append)
        ),
    );
    assert!(
        !append.exists(),
        "constructing the action must not open the file"
    );
    let batch = run(&saved.batch.engine, "#eval appendTwice\n#eval appendTwice");
    for index in &batch.batch.source_evaluation_indices {
        assert_unit(&batch.batch.executions[*index].exit);
    }
    assert_eq!(std::fs::read(&append).unwrap(), EXPECTED.repeat(4));
}

#[test]
fn binary_write_native_errors_remain_logical_and_catchable() {
    let Some(raw) = raw_bytes_environment() else {
        return;
    };
    let engine = Engine::from_environment(write_environment(&raw, None));
    let directory = directory("byte-write-errors");
    let input = directory.join("read-only.bin");
    let output = directory.join("recovered.bin");
    std::fs::write(&input, b"preserved").unwrap();
    let source = format!(
        "#eval do\n  let h ← IO.FS.Handle.mk {} IO.FS.Mode.read\n  h.write ({SOURCE_BYTES})",
        quoted(&input)
    );
    let batch = run(&engine, &source);
    assert_error(&evaluation(&batch).exit, 12, 9, None, "Bad file descriptor");
    assert_eq!(std::fs::read(&input).unwrap(), b"preserved");
    let source = format!(
        "#eval do\n  let h ← IO.FS.Handle.mk {} IO.FS.Mode.read\n  try\n    h.write ({SOURCE_BYTES})\n  catch _ =>\n    IO.FS.writeBinFile {} ({SOURCE_BYTES})",
        quoted(&input),
        quoted(&output)
    );
    let batch = run(&engine, &source);
    assert_unit(&evaluation(&batch).exit);
    assert_eq!(std::fs::read(&output).unwrap(), EXPECTED);
    assert_eq!(std::fs::read(&input).unwrap(), b"preserved");
}
