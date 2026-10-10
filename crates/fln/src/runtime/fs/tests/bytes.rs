//! Actual pinned dependency data, checked source, and honest logical bytes.
//! This deliberately bounded raw fixture is not full IO module admission.

use super::*;

mod write;

fn raw_bytes_environment() -> Option<Environment> {
    let mut environment = raw_pin_environment()?;
    let library = PathBuf::from(std::env::var_os("FLN_REFERENCE_LIB").unwrap());
    for module in [
        "Init/Prelude",
        "Init/Data/UInt/BasicAux",
        "Init/GetElem",
        "Init/Data/ByteArray/Basic",
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
        // The ordinary `h.read 4` source uses the real OfNat class and the
        // pin's USize instance with its actual index/synthesis metadata.
        if !matches!(module, "Init/Prelude" | "Init/Data/UInt/BasicAux") {
            continue;
        }
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
        let metadata = metadata::decode(&blocks, metadata::DecodeLimits::default()).unwrap();
        use fln_elab::instances::imported;
        let mut activation = imported::ImportActivation::new(environment);
        for row in metadata.reducibility.into_iter().filter(|row| {
            [name("instOfNatNat"), name("USize.instOfNat")].contains(&row.declaration)
        }) {
            use fln_elab::reducibility::Reducibility;
            let status = match row.status {
                metadata::ReducibilityStatus::Reducible => Reducibility::Reducible,
                metadata::ReducibilityStatus::Semireducible => Reducibility::Semireducible,
                metadata::ReducibilityStatus::Irreducible => Reducibility::Irreducible,
                metadata::ReducibilityStatus::ImplicitReducible => Reducibility::ImplicitReducible,
            };
            activation = activation
                .register_reducibility(&row.declaration, status)
                .unwrap();
        }
        if module == "Init/Prelude" {
            let rows: Vec<_> = metadata
                .classes
                .into_iter()
                .filter(|row| row.name == name("OfNat"))
                .collect();
            assert_eq!(rows.len(), 1);
            for row in rows {
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
        }
        {
            // Once OfNat exists, Nat literals also require their actual
            // dictionary; they no longer use the deliberately raw fallback.
            let target = if module == "Init/Prelude" {
                "instOfNatNat"
            } else {
                "USize.instOfNat"
            };
            let rows: Vec<_> = metadata
                .instances
                .into_iter()
                .filter(|row| row.declaration == name(target))
                .collect();
            assert_eq!(rows.len(), 1);
            for row in rows {
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
        }
        environment = activation.finish().unwrap();
    }
    Some(environment)
}

fn helper_extern(environment: &Environment, helper: &str, foreign: bool) -> Environment {
    let row = fln_vm::extern_table_generated::EXTERN_ROWS
        .iter()
        .find(|row| row.name == helper)
        .unwrap();
    fln_elab::externs::register(
        environment,
        &name(helper),
        vec![fln_elab::externs::ExternEntry::Standard {
            backend: name("all"),
            symbol: if foreign {
                "foreign_byte_helper".to_owned()
            } else {
                row.symbol.to_owned()
            },
        }],
    )
    .unwrap()
}

fn helpers(raw: &Environment, omit: Option<&str>) -> Environment {
    fs::BYTE_HELPERS
        .into_iter()
        .filter(|helper| Some(*helper) != omit)
        .fold(raw.clone(), |environment, helper| {
            helper_extern(&environment, helper, false)
        })
}

fn environment(raw: &Environment) -> Environment {
    register_one(&register(&helpers(raw, None)), Operation::Read, false)
}

fn logical_bytes(value: &Obj) -> Vec<u8> {
    // ByteArray.mk (Array.mk (List UInt8)): no packed array or scalar-byte
    // object is accepted under the public logical types.
    assert_constructor(value, 0, 1);
    let array = child(value, 0);
    assert_constructor(&array, 0, 1);
    let mut list = child(&array, 0);
    let mut result = Vec::new();
    loop {
        if !list.is_scalar() && list.header().tag == 0 {
            assert_constructor(&list, 0, 0);
            break;
        }
        assert_constructor(&list, 1, 2);
        let byte = child(&list, 0);
        assert_constructor(&byte, 0, 1);
        let bits = child(&byte, 0);
        assert_constructor(&bits, 0, 1);
        let finite = child(&bits, 0);
        assert_constructor(&finite, 0, 2);
        let natural = child(&finite, 0);
        assert!(natural.is_scalar());
        result.push(u8::try_from(natural.unbox()).unwrap());
        list = child(&list, 1);
    }
    result
}

fn assert_bytes(exit: &VmExit, expected: &[u8]) {
    let packet = returned(exit);
    assert_constructor(packet, 0, 2);
    assert_eq!(logical_bytes(&child(packet, 0)), expected);
    assert!(child(packet, 1).is_scalar());
    assert_eq!(child(packet, 1).unbox(), 0);
}

fn sequence(path: &Path, counts: &[usize]) -> String {
    let mut source = format!(
        "#eval (show IO ByteArray from do\n  let h ← IO.FS.Handle.mk {} IO.FS.Mode.read\n  let alias := h\n",
        quoted(path)
    );
    for count in &counts[..counts.len() - 1] {
        source.push_str(&format!("  let _ ← alias.read {count}\n"));
    }
    source.push_str(&format!("  alias.read {})", counts.last().unwrap()));
    source
}

#[test]
fn counted_read_requires_complete_actual_dependencies_and_independent_externs() {
    let Some(raw) = raw_bytes_environment() else {
        return;
    };
    fs::assert_pin_models(&raw);
    fs::assert_pin_byte_layouts(&raw);
    let exact = environment(&raw);
    let limits = IngressLimits::default();
    let mut work = 0;
    assert!(fs::primitive_matches(&exact, Operation::Read, &mut None, &mut work, limits).unwrap());
    assert!(matches!(
        fs::primitive_matches(
            &exact,
            Operation::Read,
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
        !fs::primitive_matches(
            &helpers(&raw, None),
            Operation::Read,
            &mut None,
            &mut 0,
            limits
        )
        .unwrap()
    );
    for helper in fs::BYTE_HELPERS {
        let missing = register_one(&helpers(&raw, Some(helper)), Operation::Read, false);
        assert!(
            fs::primitive_matches(&missing, Operation::Read, &mut None, &mut 0, limits).is_err(),
            "missing {helper}"
        );
        let foreign = helper_extern(&missing, helper, true);
        assert!(
            fs::primitive_matches(&foreign, Operation::Read, &mut None, &mut 0, limits).is_err(),
            "foreign {helper}"
        );
    }
    let mut preparation = Preparation::new(&exact, limits);
    assert!(
        preparation
            .fs_call(&c("IO.FS.Handle.read"), &[])
            .unwrap()
            .is_some()
    );
    let binding = preparation
        .fs_intrinsic_binding(&Operation::Read.private_name())
        .unwrap();
    assert_eq!(binding.arguments, [ValueType::Abi, ValueType::Abi]);
    assert_eq!(
        binding.argument_ownership,
        [ArgumentOwnership::Borrowed, ArgumentOwnership::Borrowed]
    );
    assert_eq!(binding.result_ownership, ResultOwnership::Owned);
    assert_eq!(
        preparation.fs.bytes_layout.as_ref().unwrap().transport_name,
        name(BYTES_TRANSPORT)
    );
    assert!(
        preparation
            .fs_call(
                &Expr::const_(Name::from_components(["IO.FS.Handle.read"]), Vec::new()),
                &[]
            )
            .unwrap()
            .is_none()
    );

    let declaration = Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: name("_fln_runtime_fs_native_word"),
            level_params: Vec::new(),
            type_: Expr::sort(Level::one()),
        },
        value: c("Nat"),
        hints: fln_env::constants::ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![name("_fln_runtime_fs_native_word")],
    });
    let admitted = Engine::from_environment(exact)
        .admit_declaration(
            declaration,
            &KVMap::new(),
            EngineAdmissionLimits::for_stack_bytes(STACK),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(
        Preparation::new(&admitted.engine.environment, limits)
            .fs_call(&c("IO.FS.Handle.read"), &[])
            .is_err()
    );
}

#[test]
fn counted_read_rejects_checked_same_type_byte_and_platform_mutants() {
    let Some(raw) = raw_bytes_environment() else {
        return;
    };
    for target in [
        "Array.size",
        "List.length",
        "UInt8.toNat",
        "System.Platform.numBits",
    ] {
        let label = name(target);
        let Some(ConstantInfo::Defn(original)) = raw.find(&label) else {
            panic!("actual {target}");
        };
        let mut changed = original.clone();
        // Preserve the exact dependent telescope; replacing its Nat result
        // with a literal is still a real well-typed safe definition.
        fn constant_body(type_: &Expr, literal: u64) -> Expr {
            if let ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } = type_.node()
            {
                Expr::lam(
                    binder_name.clone(),
                    binder_type.clone(),
                    constant_body(body, literal),
                    *binder_info,
                )
            } else {
                Expr::lit(Literal::Nat(NatLit::from_u64(literal)))
            }
        }
        changed.value = constant_body(
            &original.base.type_,
            if target == "System.Platform.numBits" {
                32
            } else {
                0
            },
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
        assert!(
            matches!(
                fs::primitive_matches(
                    &environment(&admitted.engine.environment),
                    Operation::Read,
                    &mut None,
                    &mut 0,
                    IngressLimits::default()
                ),
                Err(IngressError::UnsupportedNode { .. })
            ),
            "checked mutant {target}"
        );
    }
}

#[test]
fn ordinary_counted_reads_preserve_raw_bytes_cursor_and_logical_observations() {
    let Some(raw) = raw_bytes_environment() else {
        return;
    };
    let engine = Engine::from_environment(environment(&raw));
    let root = engine.logical_root(&KVMap::new());
    let directory = directory("read-bytes");
    let file = directory.join("binary.bin");
    let original = [0, 255, 128, 10, 226, 130, 90];
    std::fs::write(&file, original).unwrap();
    for (counts, expected) in [
        (vec![3], &[0, 255, 128][..]),
        (vec![3, 0], &[][..]),
        (vec![3, 0, 2], &[10, 226][..]),
        (vec![3, 0, 2, 9], &[130, 90][..]),
        (vec![3, 0, 2, 9, 4], &[][..]),
        (vec![3, 0, 2, 9, 4, 4], &[][..]),
    ] {
        let batch = run(&engine, &sequence(&file, &counts));
        let execution = evaluation(&batch);
        assert_bytes(&execution.exit, expected);
        assert_rows(execution, &[Operation::Open, Operation::Read]);
    }
    // A saved action is invoked twice, not eagerly evaluated or memoized.
    let saved = format!(
        "#eval (show IO ByteArray from do\n  let h ← IO.FS.Handle.mk {} IO.FS.Mode.read\n  let read := h.read 3\n  let _ ← read\n  read)",
        quoted(&file)
    );
    assert_bytes(&evaluation(&run(&engine, &saved)).exit, &[10, 226, 130]);
    // The exact public conversion wraps before the native request limit, and
    // its logical word is boxed again by the genuine read-boundary row.
    let wrapped = format!(
        "#eval (show IO ByteArray from do\n  let h ← IO.FS.Handle.mk {} IO.FS.Mode.read\n  h.read (USize.ofNat 18446744073709551619))",
        quoted(&file)
    );
    assert_bytes(&evaluation(&run(&engine, &wrapped)).exit, &[0, 255, 128]);
    for (expression, expected) in [("bytes.size", 4), ("bytes.data.toList.length", 4)] {
        let source = format!(
            "#eval (show IO Nat from do\n  let h ← IO.FS.Handle.mk {} IO.FS.Mode.read\n  let bytes ← h.read 4\n  (EST.pure ({expression}) : IO Nat))",
            quoted(&file)
        );
        let batch = run(&engine, &source);
        let packet = returned(&evaluation(&batch).exit);
        assert_constructor(packet, 0, 2);
        assert_eq!(child(packet, 0).unbox(), expected);
    }
    let observed = format!(
        "#eval (show IO Nat from do\n  let h ← IO.FS.Handle.mk {} IO.FS.Mode.read\n  let _ ← h.read 1\n  let bytes ← h.read 3\n  match bytes.data.toList with\n  | [] => (EST.pure 0 : IO Nat)\n  | first :: _ => (EST.pure first.toNat : IO Nat))",
        quoted(&file)
    );
    let observed = run(&engine, &observed);
    assert_eq!(child(returned(&evaluation(&observed).exit), 0).unbox(), 255);
    // Public constructors and projections retain their ordinary logical
    // meaning; a packed-sarray relabel would fail this reconstruction.
    let rebuilt = format!(
        "#eval (show IO ByteArray from do\n  let h ← IO.FS.Handle.mk {} IO.FS.Mode.read\n  let bytes ← h.read 4\n  (EST.pure (ByteArray.mk (Array.mk bytes.data.toList)) : IO ByteArray))",
        quoted(&file)
    );
    assert_bytes(&evaluation(&run(&engine, &rebuilt)).exit, &original[..4]);
    assert_eq!(std::fs::read(&file).unwrap(), original);
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn counted_read_actions_defer_and_replay_reopens_live_files() {
    let Some(raw) = raw_bytes_environment() else {
        return;
    };
    let engine = Engine::from_environment(environment(&raw));
    let root = engine.logical_root(&KVMap::new());
    let directory = directory("deferred-byte-read");
    let file = directory.join("created-after-compilation.bin");
    let source = format!(
        "def savedBytes : IO ByteArray := do\n  let h ← IO.FS.Handle.mk {} IO.FS.Mode.read\n  h.read 4\ndef readBytesAlias := IO.FS.Handle.read",
        quoted(&file)
    );
    let saved = run(&engine, &source);
    assert!(!file.exists());
    for execution in &saved.batch.executions {
        assert!(returned(&execution.exit).closure_shell_parts().is_some());
        assert!(execution.io_evaluation_outcome().unwrap().is_none());
    }
    std::fs::write(&file, [0, 255, 128, 1]).unwrap();
    let batch = run(&saved.batch.engine, "#eval savedBytes\n#eval savedBytes");
    for index in &batch.batch.source_evaluation_indices {
        assert_bytes(&batch.batch.executions[*index].exit, &[0, 255, 128, 1]);
    }
    let alias = format!(
        "#eval (show IO ByteArray from do\n  let h ← IO.FS.Handle.mk {} IO.FS.Mode.read\n  readBytesAlias h 4)",
        quoted(&file)
    );
    assert_bytes(
        &evaluation(&run(&saved.batch.engine, &alias)).exit,
        &[0, 255, 128, 1],
    );
    let execution = evaluation(&batch);
    let program = assert_rows(execution, &[Operation::Open, Operation::Read]);
    for bytes in [&b"\0\xff"[..], &b"\x01\x80\xfe\x04tail"[..], &b""[..]] {
        std::fs::write(&file, bytes).unwrap();
        let exit =
            execute_golem_with_options(&program, &KVMap::new(), VmExecutionLimits::default())
                .into_complete()
                .unwrap();
        assert_bytes(&exit, &bytes[..bytes.len().min(4)]);
    }
    let repeated = run(&saved.batch.engine, "#eval savedBytes\n#eval savedBytes");
    assert_eq!(execution.flbc_artifact, evaluation(&repeated).flbc_artifact);
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn pure_word_conversion_is_checked_wraps_and_has_no_io_row() {
    let Some(raw) = raw_bytes_environment() else {
        return;
    };
    let engine = Engine::from_environment(helpers(&raw, None));
    let root = engine.logical_root(&KVMap::new());
    let batch = run(
        &engine,
        "#eval (USize.ofNat 18446744073709551619).toNat\n#eval (USize.ofNat 18446744073709551615).toNat\n#eval (4 : USize).toNat",
    );
    let expected = [
        ClosedVmValue::Scalar(3),
        ClosedVmValue::NonnegativeMpz("18446744073709551615".to_owned()),
        ClosedVmValue::Scalar(4),
    ];
    for (index, expected) in batch.batch.source_evaluation_indices.iter().zip(expected) {
        let execution = &batch.batch.executions[*index];
        assert_eq!(closed_vm_value(&execution.exit).unwrap(), Some(expected));
        let program =
            flbc::decode_canonical(&execution.flbc_artifact, flbc::CodecLimits::default()).unwrap();
        assert!(!program.functions().iter().flat_map(|f| &f.code).any(|instruction| matches!(instruction, Instruction::Intrinsic { row, .. } if row.starts_with("extern:IO."))));
    }
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn counted_read_errors_and_resource_limits_remain_distinct() {
    let Some(raw) = raw_bytes_environment() else {
        return;
    };
    let engine = Engine::from_environment(environment(&raw));
    let root = engine.logical_root(&KVMap::new());
    let directory = directory("counted-errors");
    let file = directory.join("input.bin");
    std::fs::write(&file, [0, 255, 128, 1]).unwrap();
    let path = quoted(&file);
    let bad = format!(
        "#eval (show IO ByteArray from do\n  let h ← IO.FS.Handle.mk {path} IO.FS.Mode.append\n  h.read 1)"
    );
    assert_error(
        &evaluation(&run(&engine, &bad)).exit,
        12,
        9,
        None,
        "Bad file descriptor",
    );
    let zero = format!(
        "#eval (show IO ByteArray from do\n  let h ← IO.FS.Handle.mk {path} IO.FS.Mode.append\n  h.read 0)"
    );
    assert_bytes(&evaluation(&run(&engine, &zero)).exit, &[]);
    let caught = format!(
        "#eval (show IO ByteArray from do\n  let bad ← IO.FS.Handle.mk {path} IO.FS.Mode.append\n  let good ← IO.FS.Handle.mk {path} IO.FS.Mode.read\n  try bad.read 1 catch _ => good.read 4)"
    );
    assert_bytes(&evaluation(&run(&engine, &caught)).exit, &[0, 255, 128, 1]);
    for count in ["65537", "(USize.ofNat 18446744073709551615)"] {
        let oversized = format!(
            "#eval (show IO ByteArray from do\n  let h ← IO.FS.Handle.mk {path} IO.FS.Mode.read\n  try h.read {count} catch _ => h.read 4)"
        );
        let result = engine
            .execute_source_commands_with_checks(
                oversized.as_bytes(),
                &KVMap::new(),
                EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
            )
            .unwrap();
        assert!(
            matches!(result, Outcome::Inconclusive(_)),
            "native counted-read ceiling for {count} is not an IO exception"
        );
    }
    assert_eq!(std::fs::read(&file).unwrap(), [0, 255, 128, 1]);
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn counted_read_materialization_obeys_vm_fuel_and_the_exact_chunk_ceiling() {
    let Some(raw) = raw_bytes_environment() else {
        return;
    };
    let engine = Engine::from_environment(environment(&raw));
    let directory = directory("counted-bound");
    let file = directory.join("max-chunk.bin");
    let bytes: Vec<_> = (0..65536).map(|i| (i % 251) as u8).collect();
    std::fs::write(&file, &bytes).unwrap();
    // Compile on a short file under the usual finite probe budget, then use
    // that identical bytecode against the maximum permitted live chunk.
    let small = directory.join("initially-short.bin");
    std::fs::write(&small, [0, 255, 128, 1]).unwrap();
    let batch = run(&engine, &sequence(&small, &[65536]));
    assert_bytes(&evaluation(&batch).exit, &[0, 255, 128, 1]);
    let program = assert_rows(evaluation(&batch), &[Operation::Open, Operation::Read]);
    std::fs::write(&small, &bytes).unwrap();
    let exhausted = execute_golem_with_options(
        &program,
        &KVMap::new(),
        VmExecutionLimits {
            max_steps: 1000,
            ..VmExecutionLimits::default()
        },
    );
    assert!(
        matches!(exhausted, Outcome::Inconclusive(_)),
        "logical expansion is metered by normal VM fuel"
    );
    let complete =
        execute_golem_with_options(&program, &KVMap::new(), VmExecutionLimits::user_program())
            .into_complete()
            .unwrap();
    assert_bytes(&complete, &bytes);
    assert_eq!(std::fs::read(&file).unwrap(), bytes);
}
