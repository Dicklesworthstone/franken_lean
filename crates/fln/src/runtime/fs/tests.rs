//! Live filesystem probes over actual pinned declarations and metadata.
//!
//! Raw dependency loading is not full module admission. Every source example
//! below still passes both ordinary declaration checkers before execution.
//! The Reference is used only for fixture/contract comparison, never runtime.

use super::*;
use fln_comp::flbc::{self, Instruction};
use fln_olean::source_extensions as metadata;
use fln_rt::obj::Obj;
use std::path::{Path, PathBuf};

mod bytes;
mod read;

const STACK: usize = 256 * 1024 * 1024;

fn raw_pin_environment() -> Option<Environment> {
    let Some(library) = std::env::var_os("FLN_REFERENCE_LIB").map(PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "the pinned Reference is required"
        );
        eprintln!("SKIP: set FLN_REFERENCE_LIB to the pinned lib/lean");
        return None;
    };
    let mut environment = Environment::new();
    for module in [
        "Init/Prelude",
        "Init/Coe",
        "Init/System/ST",
        "Init/System/IOError",
        "Init/System/IO",
        "Init/System/FilePath",
    ] {
        let path = library.join(module).with_extension("olean");
        let parts = [
            std::fs::read(&path).unwrap(),
            std::fs::read(path.with_extension("olean.server")).unwrap(),
            std::fs::read(path.with_extension("olean.private")).unwrap(),
        ];
        let decoded = decode_olean_module_artifacts(
            &parts[0],
            &parts[1],
            &parts[2],
            OleanDecodeLimits::new(STACK),
        )
        .unwrap();
        for constant in decoded.constants {
            if !environment.contains(constant.name()) {
                environment = environment.add_decl(constant).unwrap();
            }
        }
        if matches!(
            module,
            "Init/Prelude" | "Init/Coe" | "Init/System/IO" | "Init/System/FilePath"
        ) {
            let view = if decoded.module.is_module {
                fln_olean::region::OleanView::parse_with_dependencies(
                    &parts[2],
                    &[parts[0].as_slice(), parts[1].as_slice()],
                )
            } else {
                fln_olean::region::OleanView::parse(&parts[0])
            }
            .unwrap();
            let blocks = view
                .extension_payloads(OleanWalkBudget::default(), STACK)
                .unwrap();
            environment = activate_source_metadata(
                environment,
                metadata::decode(&blocks, metadata::DecodeLimits::default()).unwrap(),
                module,
            );
        }
    }
    Some(environment)
}

fn activate_source_metadata(
    environment: Environment,
    decoded: metadata::SourceExtensions,
    module: &str,
) -> Environment {
    use fln_elab::instances::imported;
    // Ordinary do sequencing and catch need their real class/projection
    // journals just as a string path needs the actual coercion chain.
    // These are imported rows, preserving priority, order, scope and keys.
    let (class_labels, instance_labels): (&[&str], &[&str]) = match module {
        "Init/Prelude" => (
            &["Bind", "Monad", "MonadExceptOf", "MonadExcept"],
            &["Monad.toBind", "instMonadExceptOfMonadExceptOf"],
        ),
        "Init/System/IO" => (&[], &["instMonadEIO", "instMonadExceptOfEIO"]),
        "Init/Coe" => (
            &["CoeT", "CoeHTCT", "CoeHTC", "CoeOTC", "CoeTC", "Coe"],
            &[
                "instCoeTOfCoeHTCT",
                "instCoeHTCTOfCoeHTC",
                "instCoeHTCOfCoeOTC",
                "instCoeOTCOfCoeTC",
                "instCoeTCOfCoe_1",
            ],
        ),
        "Init/System/FilePath" => (&[], &["System.instCoeStringFilePath"]),
        _ => unreachable!("the selected actual metadata modules"),
    };
    let wanted_classes: Vec<_> = class_labels.iter().map(|label| name(label)).collect();
    let wanted_instances: Vec<_> = instance_labels.iter().map(|label| name(label)).collect();
    let classes: Vec<_> = decoded
        .classes
        .into_iter()
        .filter(|row| wanted_classes.contains(&row.name))
        .collect();
    let instances: Vec<_> = decoded
        .instances
        .into_iter()
        .filter(|row| wanted_instances.contains(&row.declaration))
        .collect();
    let markers = [name("outParam"), name("semiOutParam")];
    let reducibility: Vec<_> = decoded
        .reducibility
        .into_iter()
        .filter(|row| module == "Init/Prelude" && markers.contains(&row.declaration))
        .collect();
    assert_eq!(
        classes.len(),
        wanted_classes.len(),
        "the actual class journal in {module}"
    );
    assert_eq!(
        instances.len(),
        wanted_instances.len(),
        "the actual instance journal in {module}"
    );
    assert_eq!(
        reducibility.len(),
        if module == "Init/Prelude" { 2 } else { 0 },
        "the actual output-marker reducibility journal"
    );
    let mut activation = imported::ImportActivation::new(environment);
    for row in reducibility {
        use fln_elab::reducibility::Reducibility;
        // The pin's markers are ordinary definitions with imported reducible
        // status. Output-type inference must not depend on seed-only hints.
        let status = match row.status {
            metadata::ReducibilityStatus::Reducible => Reducibility::Reducible,
            metadata::ReducibilityStatus::Semireducible => Reducibility::Semireducible,
            metadata::ReducibilityStatus::Irreducible => Reducibility::Irreducible,
            metadata::ReducibilityStatus::ImplicitReducible => Reducibility::ImplicitReducible,
        };
        assert_eq!(status, Reducibility::Reducible);
        activation = activation
            .register_reducibility(&row.declaration, status)
            .unwrap();
    }
    for row in classes {
        activation = activation
            .register_class(
                &row.name,
                &imported::ClassParameters {
                    out_params: row.out_params,
                    out_level_params: row.out_level_params,
                },
            )
            .unwrap();
    }
    for row in instances {
        assert!(
            matches!(row.value.node(), ExprNode::Const { name, .. } if name == &row.declaration)
        );
        activation = activation
            .register_instance(
                &row.declaration,
                &imported::InstanceParameters {
                    priority: row.priority,
                    synth_order: row.synth_order,
                    scope: row.scope,
                    keys: row.keys.into_iter().map(instance_key).collect(),
                },
            )
            .unwrap();
    }
    activation.finish().unwrap()
}

fn instance_key(key: metadata::InstanceKey) -> fln_elab::instances::discr_tree::Key {
    use fln_elab::instances::discr_tree::Key;
    match key {
        metadata::InstanceKey::Star => Key::Star,
        metadata::InstanceKey::Other => Key::Other,
        metadata::InstanceKey::Lit(literal) => Key::Lit(literal),
        metadata::InstanceKey::FVar(name, arity) => Key::FVar(fln_core::expr::FVarId(name), arity),
        metadata::InstanceKey::Const(name, arity) => Key::Const(name, arity),
        metadata::InstanceKey::Arrow => Key::Arrow,
        metadata::InstanceKey::Proj(name, field, arity) => Key::Proj(name, field, arity),
    }
}

fn register_one(environment: &Environment, operation: Operation, foreign: bool) -> Environment {
    let source = operation.source_name();
    let row = fln_vm::extern_table_generated::EXTERN_ROWS
        .iter()
        .find(|row| row.name == source.to_display_string())
        .unwrap();
    fln_elab::externs::register(
        environment,
        &source,
        vec![fln_elab::externs::ExternEntry::Standard {
            backend: name("all"),
            symbol: if foreign {
                "foreign_file_primitive".to_owned()
            } else {
                row.symbol.to_owned()
            },
        }],
    )
    .unwrap()
}

fn register(environment: &Environment) -> Environment {
    register_one(
        &register_one(environment, Operation::Open, false),
        Operation::PutStr,
        false,
    )
}

#[test]
fn filesystem_models_bind_paths_modes_handles_and_each_extern_independently() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    fs::assert_pin_models(&raw);
    let limits = IngressLimits::default();
    for operation in [Operation::Open, Operation::PutStr] {
        assert!(!fs::primitive_matches(&raw, operation, &mut None, &mut 0, limits).unwrap());
        let exact = register_one(&raw, operation, false);
        assert!(fs::primitive_matches(&exact, operation, &mut None, &mut 0, limits).unwrap());
        assert!(
            fs::primitive_matches(
                &register_one(&raw, operation, true),
                operation,
                &mut None,
                &mut 0,
                limits
            )
            .is_err()
        );
        let other = if operation == Operation::Open {
            Operation::PutStr
        } else {
            Operation::Open
        };
        assert!(!fs::primitive_matches(&exact, other, &mut None, &mut 0, limits).unwrap());
    }
    let exact = register(&raw);
    let externs = fln_elab::externs::ExternTable::read(&exact).unwrap();
    assert!(
        externs.get(&name("IO.getStdout")).is_none(),
        "file-only execution has no stdout prerequisite"
    );
    let mut preparation = Preparation::new(&exact, limits);
    assert_eq!(
        preparation.type_head(&c("IO.FS.Handle")).unwrap(),
        c(HANDLE)
    );
    assert_eq!(
        executable_value_type(&c(HANDLE), &preparation.value_types),
        Some((ValueType::Abi, CallableResultOwnership::Owned))
    );
    assert!(
        preparation
            .fs_call(
                &Expr::const_(Operation::Open.source_name(), Vec::new()),
                &[]
            )
            .unwrap()
            .is_some()
    );
    let lookalike = Name::from_components(["IO.FS.Handle.mk"]);
    assert_ne!(lookalike, Operation::Open.source_name());
    assert!(
        preparation
            .fs_call(&Expr::const_(lookalike, Vec::new()), &[])
            .unwrap()
            .is_none()
    );

    for target in [
        "System.FilePath.mk",
        "System.FilePath.toString",
        "IO.FS.Mode",
        "IO.FS.Mode.write",
        "IO.FS.Mode.rec",
        "IO.FS.Handle",
        "IO.FS.Handle.mk",
        "IO.FS.Handle.putStr",
        "IO",
        "IO.Error.interrupted",
        "UInt32.ofBitVec",
    ] {
        let changed = raw
            .constants()
            .fold(Environment::new(), |environment, (label, info)| {
                let mut info = info.clone();
                if label == &name(target) {
                    match &mut info {
                        ConstantInfo::Opaque(value) => value.value = Expr::sort(Level::zero()),
                        ConstantInfo::Defn(value) => value.value = c("Bool.false"),
                        ConstantInfo::Ctor(value) => value.num_fields += 1,
                        ConstantInfo::Induct(value) => value.ctors.reverse(),
                        ConstantInfo::Rec(value) => value.rules.reverse(),
                        _ => unreachable!("fixed filesystem mutation target"),
                    }
                }
                environment.add_decl(info).unwrap()
            });
        let operation = if target == "IO.FS.Handle.putStr" {
            Operation::PutStr
        } else {
            Operation::Open
        };
        assert!(
            fs::primitive_matches(
                &register_one(&changed, operation, false),
                operation,
                &mut None,
                &mut 0,
                limits
            )
            .is_err(),
            "mutated {target}"
        );
    }
    let mut work = 0;
    assert!(fs::primitive_matches(&exact, Operation::Open, &mut None, &mut work, limits).unwrap());
    assert!(matches!(
        fs::primitive_matches(
            &exact,
            Operation::Open,
            &mut None,
            &mut 0,
            IngressLimits {
                max_nodes: work - 1,
                ..limits
            }
        ),
        Err(IngressError::ResourceLimit { .. })
    ));
}

#[test]
fn checked_same_type_path_projection_change_cannot_redirect_a_native_open() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    let target = name("System.FilePath.toString");
    let Some(ConstantInfo::Defn(original)) = raw.find(&target) else {
        panic!("the pinned path projection")
    };
    let mut changed = original.clone();
    changed.value = Expr::lam(
        Name::anonymous(),
        c("System.FilePath"),
        Expr::lit(Literal::Str("different-path".to_owned())),
        BinderInfo::Default,
    );
    let without = raw
        .constants()
        .fold(Environment::new(), |environment, (label, info)| {
            if label == &target {
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
    let environment = register(&admitted.engine.environment);
    assert!(matches!(
        fs::primitive_matches(
            &environment,
            Operation::Open,
            &mut None,
            &mut 0,
            IngressLimits::default()
        ),
        Err(IngressError::UnsupportedNode { .. })
    ));
    // putStr does not inspect FilePath, so its separate contract is unaffected.
    assert!(
        fs::primitive_matches(
            &environment,
            Operation::PutStr,
            &mut None,
            &mut 0,
            IngressLimits::default()
        )
        .unwrap()
    );
}

#[test]
fn checked_same_type_equality_change_cannot_relabel_native_io_errors() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    let target = name("Nat.beq");
    let Some(ConstantInfo::Defn(original)) = raw.find(&target) else {
        panic!("the pinned Nat equality declaration")
    };
    let mut changed = original.clone();
    changed.value = Expr::lam(
        Name::anonymous(),
        c("Nat"),
        Expr::lam(
            Name::anonymous(),
            c("Nat"),
            c("Bool.true"),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let without = raw
        .constants()
        .fold(Environment::new(), |environment, (label, info)| {
            if label == &target {
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
    let environment = register(&admitted.engine.environment);
    for operation in [Operation::Open, Operation::PutStr] {
        assert!(matches!(
            fs::primitive_matches(
                &environment,
                operation,
                &mut None,
                &mut 0,
                IngressLimits::default()
            ),
            Err(IngressError::UnsupportedNode { .. })
        ));
    }
    let row = fln_vm::extern_table_generated::EXTERN_ROWS
        .iter()
        .find(|row| row.id == "extern:IO.getStdout")
        .unwrap();
    let environment = fln_elab::externs::register(
        &environment,
        &name("IO.getStdout"),
        vec![fln_elab::externs::ExternEntry::Standard {
            backend: name("all"),
            symbol: row.symbol.to_owned(),
        }],
    )
    .unwrap();
    assert!(
        matches!(
            source_intrinsics::io::stdout::contract_matches(
                &environment,
                &mut None,
                &mut 0,
                IngressLimits::default()
            ),
            Err(IngressError::UnsupportedNode { .. })
        ),
        "stdout shares the same checked error selector"
    );
}

fn directory(label: &str) -> PathBuf {
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let path = std::env::temp_dir().join(format!(
        "fln-fs-core-{label}-{}-{nonce}",
        std::process::id()
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

fn quoted(path: &Path) -> String {
    format!("{:?}", path.to_str().unwrap())
}

fn run(engine: &Engine, source: &str) -> SourceCommandBatchExecution {
    let batch = engine
        .execute_source_commands_with_checks(
            source.as_bytes(),
            &KVMap::new(),
            EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    for execution in &batch.batch.executions {
        assert_eq!(
            execution.checker.ground,
            CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
        );
    }
    batch
}

fn evaluation(batch: &SourceCommandBatchExecution) -> &DefinitionExecution {
    let index = *batch
        .batch
        .source_evaluation_indices
        .last()
        .expect("an explicit evaluation");
    &batch.batch.executions[index]
}

fn assert_constructor(value: &Obj, tag: u8, fields: u8) {
    assert!(!value.is_scalar());
    assert_eq!(value.header().tag, tag);
    assert_eq!(value.header().other, fields);
    assert_eq!(value.byte_size(), 8 + usize::from(fields) * 8);
}

fn child(value: &Obj, index: usize) -> Obj {
    value
        .try_ctor_child(index)
        .expect("a checked logical field")
}

fn returned(exit: &VmExit) -> &Obj {
    let VmExit::Returned(returned) = exit else {
        panic!("logical IO return: {exit:?}")
    };
    &returned.value
}

fn assert_unit(exit: &VmExit) {
    let value = returned(exit);
    assert_constructor(value, 0, 2);
    assert_constructor(&child(value, 0), 0, 0);
    assert!(child(value, 1).is_scalar());
    assert_eq!(child(value, 1).unbox(), 0);
}

fn assert_rows(
    execution: &DefinitionExecution,
    operations: &[Operation],
) -> flbc::ValidatedProgram {
    let program =
        flbc::decode_canonical(&execution.flbc_artifact, flbc::CodecLimits::default()).unwrap();
    for operation in operations {
        let wanted = format!("extern:{}", operation.source_name().to_display_string());
        assert!(program.functions().iter().flat_map(|function| &function.code).any(|instruction| matches!(instruction, Instruction::Intrinsic { row, .. } if row == &wanted)), "{wanted} is retained in FLBC");
    }
    assert!(!program.functions().iter().flat_map(|function| &function.code).any(|instruction| matches!(instruction, Instruction::Intrinsic { row, .. } if row == "extern:IO.getStdout")));
    program
}

#[test]
fn checked_write_file_sources_defer_effects_and_replay_live_file_writes() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    let engine = Engine::from_environment(register(&raw));
    let root = engine.logical_root(&KVMap::new());
    let directory = directory("writes");
    let file = directory.join("written.txt");
    let path = quoted(&file);
    std::fs::write(&file, b"the existing file must survive construction").unwrap();
    let dormant = run(
        &engine,
        &format!(
            "def savedWrite : IO Unit := IO.FS.writeFile (System.FilePath.mk {path}) \"dormant\"\ndef openFile := IO.FS.Handle.mk\ndef writeHandle := IO.FS.Handle.putStr\ndef writeFileAlias := IO.FS.writeFile"
        ),
    );
    for execution in &dormant.batch.executions {
        assert!(returned(&execution.exit).closure_shell_parts().is_some());
    }
    assert_rows(
        &dormant.batch.executions[0],
        &[Operation::Open, Operation::PutStr],
    );
    assert_eq!(
        std::fs::read(&file).unwrap(),
        b"the existing file must survive construction"
    );

    let explicit = run(
        &engine,
        &format!("#eval IO.FS.writeFile (System.FilePath.mk {path}) \"λ🙂\\x00tail\\n\""),
    );
    let execution = evaluation(&explicit);
    assert_unit(&execution.exit);
    let program = assert_rows(execution, &[Operation::Open, Operation::PutStr]);
    let expected = "λ🙂\0tail\n".as_bytes();
    assert_eq!(
        std::fs::read(&file).unwrap(),
        expected,
        "the pinned body writes bytes and final Handle release flushes them"
    );
    for marker in [
        b"first stale bytes".as_slice(),
        b"second stale bytes".as_slice(),
    ] {
        std::fs::write(&file, marker).unwrap();
        let exit =
            execute_golem_with_options(&program, &KVMap::new(), VmExecutionLimits::default())
                .into_complete()
                .unwrap();
        assert_unit(&exit);
        assert_eq!(
            std::fs::read(&file).unwrap(),
            expected,
            "retained FLBC executes a fresh write and truncates stale contents"
        );
    }

    // These two calls require the actual String-to-FilePath coercion chain.
    for source in [
        format!("#eval IO.FS.writeFile {path} \"ordinary\""),
        format!("#eval do IO.FS.writeFile {path} \"ordinary\""),
    ] {
        std::fs::write(&file, b"stale ordinary bytes").unwrap();
        let batch = run(&engine, &source);
        assert_unit(&evaluation(&batch).exit);
        assert_rows(evaluation(&batch), &[Operation::Open, Operation::PutStr]);
        assert_eq!(std::fs::read(&file).unwrap(), b"ordinary");
    }
    let batch = run(
        &dormant.batch.engine,
        &format!("#eval writeFileAlias {path} \"alias\""),
    );
    assert_unit(&evaluation(&batch).exit);
    assert_eq!(std::fs::read(&file).unwrap(), b"alias");

    let append = directory.join("append.txt");
    let append_path = quoted(&append);
    let source = format!(
        "def appendOnce : IO Unit := do\n  let h ← IO.FS.Handle.mk (System.FilePath.mk {append_path}) IO.FS.Mode.append\n  let write := IO.FS.Handle.putStr h \"λ\"\n  write\n  write"
    );
    let saved = run(&engine, &source);
    assert!(
        !append.exists(),
        "storing a write action must not create/open its file"
    );
    let batch = run(&saved.batch.engine, "#eval appendOnce\n#eval appendOnce");
    for index in &batch.batch.source_evaluation_indices {
        assert_unit(&batch.batch.executions[*index].exit);
    }
    assert_eq!(
        std::fs::read(&append).unwrap(),
        "λλλλ".as_bytes(),
        "the reusable action retains each Handle for both putStr invocations"
    );

    let explicit_world = format!(
        "#eval (show IO Unit from fun world => match IO.FS.Handle.mk (System.FilePath.mk {path}) IO.FS.Mode.write world with | .ok h next => IO.FS.Handle.putStr h \"explicit-world\" next | .error error next => @EST.Out.error IO.Error IO.RealWorld Unit error next)"
    );
    let batch = run(&engine, &explicit_world);
    assert_unit(&evaluation(&batch).exit);
    assert_eq!(std::fs::read(&file).unwrap(), b"explicit-world");
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

fn assert_text(value: &Obj, expected: &str) {
    assert_eq!(
        closed_obj_value(value).unwrap(),
        Some(ClosedVmValue::String(expected.to_owned()))
    );
}

fn assert_word(value: &Obj, expected: u32) {
    assert_constructor(value, 0, 1);
    let bits = child(value, 0);
    assert_constructor(&bits, 0, 1);
    let finite = child(&bits, 0);
    assert_constructor(&finite, 0, 2);
    assert_eq!(
        nat_decimal(&child(&finite, 0)).as_deref(),
        Some(expected.to_string().as_str())
    );
    assert!(child(&finite, 1).is_scalar());
    assert_eq!(child(&finite, 1).unbox(), 0);
}

fn assert_error(exit: &VmExit, tag: u8, code: u32, filename: Option<&str>, details: &str) {
    let result = returned(exit);
    assert_constructor(result, 1, 2);
    assert_eq!(child(result, 1).unbox(), 0);
    let error = child(result, 0);
    assert_constructor(&error, tag, 3);
    if tag == 11 {
        assert_text(&child(&error, 0), filename.unwrap());
    } else {
        let option = child(&error, 0);
        assert_constructor(
            &option,
            u8::from(filename.is_some()),
            u8::from(filename.is_some()),
        );
        if let Some(filename) = filename {
            assert_text(&child(&option, 0), filename);
        }
    }
    assert_word(&child(&error, 1), code);
    assert_text(&child(&error, 2), details);
}

#[test]
fn native_file_errors_keep_checked_payloads_and_support_ordinary_recovery() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    let engine = Engine::from_environment(register(&raw));
    let directory = directory("errors");
    let file = directory.join("existing.txt");
    let path = quoted(&file);
    std::fs::write(&file, b"preserve these bytes").unwrap();
    let batch = run(
        &engine,
        &format!("#eval IO.FS.Handle.mk (System.FilePath.mk {path}) IO.FS.Mode.writeNew"),
    );
    assert_error(
        &evaluation(&batch).exit,
        0,
        17,
        file.to_str(),
        "File exists",
    );
    assert_eq!(std::fs::read(&file).unwrap(), b"preserve these bytes");

    let invalid_path = format!("{}\0suffix", file.to_str().unwrap());
    let invalid_source = format!("\"{}\\x00suffix\"", file.to_str().unwrap());
    let batch = run(
        &engine,
        &format!("#eval IO.FS.writeFile (System.FilePath.mk {invalid_source}) \"never written\""),
    );
    assert_error(
        &evaluation(&batch).exit,
        12,
        22,
        Some(&invalid_path),
        "string contains NUL bytes",
    );
    assert_eq!(std::fs::read(&file).unwrap(), b"preserve these bytes");

    let batch = run(
        &engine,
        &format!(
            "#eval do\n  let h ← IO.FS.Handle.mk (System.FilePath.mk {path}) IO.FS.Mode.read\n  IO.FS.Handle.putStr h \"never written\""
        ),
    );
    assert_error(&evaluation(&batch).exit, 12, 9, None, "Bad file descriptor");
    assert_eq!(std::fs::read(&file).unwrap(), b"preserve these bytes");

    let absent = directory.join("missing-parent").join("child.txt");
    let missing = quoted(&absent);
    let batch = run(
        &engine,
        &format!("#eval IO.FS.writeFile (System.FilePath.mk {missing}) \"never written\""),
    );
    assert_error(
        &evaluation(&batch).exit,
        11,
        2,
        absent.to_str(),
        "No such file or directory",
    );
    assert!(!absent.exists());

    let recovered = directory.join("recovered.txt");
    let recovery_path = quoted(&recovered);
    let batch = run(
        &engine,
        &format!(
            "#eval do\n  try\n    IO.FS.writeFile (System.FilePath.mk {missing}) \"never written\"\n  catch _ =>\n    IO.FS.writeFile {recovery_path} \"caught-native-error\""
        ),
    );
    assert_unit(&evaluation(&batch).exit);
    assert_eq!(std::fs::read(&recovered).unwrap(), b"caught-native-error");
}
