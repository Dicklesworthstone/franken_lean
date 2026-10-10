//! Fast adapter probes over actual pinned metadata. Raw dependency loading is
//! not a module-admission claim. Source examples pass both declaration checkers;
//! the transport fixtures separately test post-admission representation code.

use super::*;
use fln_comp::flbc::{self, Instruction};
use fln_olean::source_extensions as metadata;
use fln_rt::obj::Obj;

mod input;

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
        "Init/System/ST",
        "Init/System/IOError",
        "Init/System/IO",
        "Init/Data/ToString/Basic",
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
        if module == "Init/Data/ToString/Basic" {
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
            environment = activate_to_string_metadata(
                environment,
                metadata::decode(&blocks, metadata::DecodeLimits::default()).unwrap(),
            );
        }
    }
    Some(environment)
}

fn activate_to_string_metadata(
    environment: Environment,
    decoded: metadata::SourceExtensions,
) -> Environment {
    use fln_elab::instances::imported;
    let classes: Vec<_> = decoded
        .classes
        .into_iter()
        .filter(|row| row.name == name("ToString"))
        .collect();
    let instances: Vec<_> = decoded
        .instances
        .into_iter()
        .filter(|row| row.declaration == name("instToStringString"))
        .collect();
    assert_eq!(classes.len(), 1, "the actual ToString class journal");
    assert_eq!(instances.len(), 1, "the actual String instance journal");
    let mut activation = imported::ImportActivation::new(environment);
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
        assert_eq!(row.value, c("instToStringString"));
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

fn register(environment: &Environment, foreign: bool) -> Environment {
    let row = fln_vm::extern_table_generated::EXTERN_ROWS
        .iter()
        .find(|row| row.id == "extern:IO.getStdout")
        .unwrap();
    fln_elab::externs::register(
        environment,
        &stdout::source_name(),
        vec![fln_elab::externs::ExternEntry::Standard {
            backend: name("all"),
            symbol: if foreign {
                "foreign_stdout".to_owned()
            } else {
                row.symbol.to_owned()
            },
        }],
    )
    .unwrap()
}

#[test]
fn stdout_requires_exact_pin_layouts_and_extern_authority() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    stdout::assert_pin_models(&raw);
    let limits = IngressLimits::default();
    assert!(!stdout::contract_matches(&raw, &mut None, &mut 0, limits).unwrap());
    assert!(stdout::contract_matches(&register(&raw, false), &mut None, &mut 0, limits).unwrap());
    assert!(stdout::contract_matches(&register(&raw, true), &mut None, &mut 0, limits).is_err());
    for target in [
        "IO.getStdout",
        "IO.FS.Stream.mk",
        "IO.Error.interrupted",
        "UInt32.ofBitVec",
        "BitVec.ofFin",
        "Fin.mk",
        "Option.some",
        "Unit.unit",
    ] {
        let changed = raw
            .constants()
            .fold(Environment::new(), |environment, (label, info)| {
                let mut info = info.clone();
                if label == &name(target) {
                    match &mut info {
                        ConstantInfo::Opaque(value) => value.value = c("Unit.unit"),
                        ConstantInfo::Defn(value) => value.value = c("Bool.false"),
                        ConstantInfo::Ctor(value) => value.num_fields += 1,
                        _ => unreachable!("fixed mutation target"),
                    }
                }
                environment.add_decl(info).unwrap()
            });
        assert!(
            stdout::contract_matches(&register(&changed, false), &mut None, &mut 0, limits)
                .is_err(),
            "mutated {target}"
        );
    }
    let exact = register(&raw, false);
    let mut preparation = Preparation::new(&exact, limits);
    assert!(preparation.stdout_layout().unwrap().is_some());
    let lookalike = Name::from_components(["IO.getStdout"]);
    assert_ne!(lookalike, stdout::source_name());
    assert!(
        preparation
            .stdout_call(&Expr::const_(lookalike, Vec::new()), &[])
            .unwrap()
            .is_none(),
        "a cached native binding does not authorize a display-equal name",
    );
    let mut work = 0;
    assert!(stdout::contract_matches(&exact, &mut None, &mut work, limits).unwrap());
    assert!(matches!(
        stdout::contract_matches(
            &exact,
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

fn assert_constructor(value: &Obj, tag: u8, fields: u8) {
    assert!(
        !value.is_scalar(),
        "logical data uses its checked boxed constructor"
    );
    assert_eq!(value.header().tag, tag);
    assert_eq!(value.header().other, fields);
    assert_eq!(
        value.byte_size(),
        8 + usize::from(fields) * 8,
        "no native packed scalar area survives"
    );
}

#[test]
fn checked_same_type_numeric_dictionaries_cannot_change_the_native_word_bound() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    let lambda = |body| Expr::lam(Name::anonymous(), c("Nat"), body, BinderInfo::Default);
    let zero_power = Expr::app(
        Expr::app(
            Expr::const_(name("NatPow.mk"), vec![Level::zero()]),
            c("Nat"),
        ),
        lambda(lambda(c("Nat.zero"))),
    );
    let zero_literal = lambda(apply(
        Expr::const_(name("OfNat.mk"), vec![Level::zero()]),
        [c("Nat"), b(0).unwrap(), c("Nat.zero")],
    ));
    let impossible_order = Expr::app(
        Expr::app(Expr::const_(name("LT.mk"), vec![Level::zero()]), c("Nat")),
        lambda(lambda(c("False"))),
    );
    for (label, body) in [
        ("instNatPowNat", zero_power),
        ("instOfNatNat", zero_literal),
        ("instLTNat", impossible_order),
    ] {
        let target = name(label);
        let Some(ConstantInfo::Defn(original)) = raw.find(&target) else {
            panic!("actual numeric dictionary {label}");
        };
        let mut changed = original.clone();
        changed.value = body;
        let without = raw
            .constants()
            .fold(Environment::new(), |environment, (name, info)| {
                if name == &target {
                    environment
                } else {
                    environment.add_decl(info.clone()).unwrap()
                }
            });
        // Both checkers admit the different implementation at the original
        // declared type. The native bridge must distinguish its semantics;
        // refusing an ill-typed replacement would not exercise this gap.
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
            CheckerAdmissionGround::BodyCheckedAgainstDeclaredType,
        );
        let environment = register(&admitted.engine.environment, false);
        assert!(
            matches!(
                stdout::contract_matches(&environment, &mut None, &mut 0, IngressLimits::default(),),
                Err(IngressError::UnsupportedNode { .. }),
            ),
            "a checked same-typed {label} mutation cannot authorize native UInt32",
        );
    }
}

fn child(value: &Obj, index: usize) -> Obj {
    value.try_ctor_child(index).expect("checked logical field")
}

fn assert_text(value: &Obj, expected: &str) {
    assert_eq!(
        closed_obj_value(value).unwrap(),
        Some(ClosedVmValue::String(expected.to_owned()))
    );
}

fn assert_word(value: &Obj, expected: &str) {
    assert_constructor(value, 0, 1);
    let bits = child(value, 0);
    assert_constructor(&bits, 0, 1);
    let fin = child(&bits, 0);
    assert_constructor(&fin, 0, 2);
    assert_eq!(nat_decimal(&child(&fin, 0)).as_deref(), Some(expected));
    let proof = child(&fin, 1);
    assert!(proof.is_scalar());
    assert_eq!(proof.unbox(), 0);
}

fn compile_transport(
    environment: &Environment,
    success: bool,
    tag: usize,
    has_file: bool,
) -> VmExit {
    let limits = IngressLimits::default();
    let mut preparation = Preparation::new(environment, limits);
    let layout = preparation.stdout_layout().unwrap().unwrap();
    let result = preparation.stdout_put_str_result(&layout).unwrap();
    let transport = apply(
        Expr::const_(Name::str(name(TRANSPORT), "mk"), Vec::new()),
        [
            c(if success { "Bool.true" } else { "Bool.false" }),
            nat::literal(tag as u64),
            nat::literal(u64::from(u32::MAX)),
            c(if has_file { "Bool.true" } else { "Bool.false" }),
            Expr::lit(Literal::Str("stdout-file".to_owned())),
            Expr::lit(Literal::Str("stdout-details".to_owned())),
        ],
    );
    let body = Expr::let_e(
        name("transport"),
        layout.transport,
        transport,
        result,
        false,
    );
    let body = Expr::let_e(name("world"), layout.world, c("Bool.false"), body, false);
    // This is a compiler-private transport fixture, never a checked source
    // inhabitant or a replacement for admission of any library declaration.
    let expression = preparation
        .expression_at_type(&body, Some(layout.io_result.source))
        .unwrap();
    let mut catalog =
        executable_dependencies(environment, &expression, limits, &mut preparation).unwrap();
    preparation.refine_expression_captures(&expression).unwrap();
    let interfaces = preparation
        .finalize_callables(&mut catalog.functions, &mut catalog.intrinsics)
        .unwrap();
    let ingress = fln_comp::ingress::lower_closed_expr_at_result(
        &expression,
        &catalog.scalar_constructors,
        &catalog.intrinsics,
        &preparation.constructors,
        preparation.callables(&catalog.functions),
        &interfaces,
        Some(ValueType::Constructor),
        limits,
    )
    .unwrap();
    let lowered = fln_comp::fir::lower_to_flbc(ingress.fir()).unwrap();
    let bytes = flbc::encode_canonical(&lowered, flbc::CodecLimits::default()).unwrap();
    let program = flbc::decode_canonical(&bytes, flbc::CodecLimits::default()).unwrap();
    execute_golem_with_options(&program, &KVMap::new(), VmExecutionLimits::default())
        .into_complete()
        .unwrap()
}

#[test]
fn native_stdout_transport_reconstructs_all_logical_io_error_layouts() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    let environment = register(&raw, false);
    let VmExit::Returned(success) = compile_transport(&environment, true, 0, false) else {
        panic!("success conversion");
    };
    assert_constructor(&success.value, 0, 2);
    assert_constructor(&child(&success.value, 0), 0, 0);
    assert_eq!(child(&success.value, 1).unbox(), 0);
    for (tag, (_, shape)) in stdout::error_cases().into_iter().enumerate() {
        let optional = matches!(shape, ErrorFields::OptionalFileCodeDetails);
        for has_file in if optional {
            &[false, true][..]
        } else {
            &[true][..]
        } {
            let VmExit::Returned(returned) = compile_transport(&environment, false, tag, *has_file)
            else {
                panic!("error conversion {tag}");
            };
            assert_constructor(&returned.value, 1, 2);
            let error = child(&returned.value, 0);
            let world = child(&returned.value, 1);
            assert!(world.is_scalar());
            assert_eq!(world.unbox(), 0);
            match shape {
                ErrorFields::OptionalFileCodeDetails => {
                    assert_constructor(&error, tag as u8, 3);
                    let file = child(&error, 0);
                    assert_constructor(&file, u8::from(*has_file), u8::from(*has_file));
                    if *has_file {
                        assert_text(&child(&file, 0), "stdout-file");
                    }
                    assert_word(&child(&error, 1), "4294967295");
                    assert_text(&child(&error, 2), "stdout-details");
                }
                ErrorFields::CodeDetails => {
                    assert_constructor(&error, tag as u8, 2);
                    assert_word(&child(&error, 0), "4294967295");
                    assert_text(&child(&error, 1), "stdout-details");
                }
                ErrorFields::FileCodeDetails => {
                    assert_constructor(&error, tag as u8, 3);
                    assert_text(&child(&error, 0), "stdout-file");
                    assert_word(&child(&error, 1), "4294967295");
                    assert_text(&child(&error, 2), "stdout-details");
                }
                ErrorFields::Empty => assert_constructor(&error, tag as u8, 0),
                ErrorFields::Message => {
                    assert_constructor(&error, tag as u8, 1);
                    assert_text(&child(&error, 0), "stdout-details");
                }
            }
        }
    }
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

fn assert_native_row(execution: &DefinitionExecution) -> flbc::ValidatedProgram {
    let program =
        flbc::decode_canonical(&execution.flbc_artifact, flbc::CodecLimits::default()).unwrap();
    assert!(program.functions().iter().flat_map(|function| &function.code).any(|instruction| matches!(instruction, Instruction::Intrinsic { row, .. } if row == "extern:IO.getStdout")));
    program
}

fn assert_unit_packet(exit: &VmExit) {
    let VmExit::Returned(returned) = exit else {
        panic!("logical IO Unit returned: {exit:?}");
    };
    assert_constructor(&returned.value, 0, 2);
    assert_constructor(&child(&returned.value, 0), 0, 0);
    let world = child(&returned.value, 1);
    assert!(world.is_scalar());
    assert_eq!(world.unbox(), 0);
}

#[test]
fn checked_stdout_sources_are_deferred_and_replayable() {
    const CHILD: &str = "FLN_STDOUT_CORE_TEST_CHILD";
    if std::env::var_os(CHILD).is_none() {
        if std::env::var_os("FLN_REFERENCE_LIB").is_none() {
            assert!(
                std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                "the pinned Reference library is required"
            );
            return;
        }
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "runtime::stdout::tests::checked_stdout_sources_are_deferred_and_replayable",
                "--nocapture",
            ])
            .env(CHILD, "1")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        let output = String::from_utf8(output.stdout).unwrap();
        assert_eq!(
            output.matches("fln-stdout-deferred-marker").count(),
            0,
            "constructing an action must not write"
        );
        assert_eq!(
            output.matches("fln-stdout-replay-marker-☃").count(),
            3,
            "source execution and both retained FLBC replays write exactly once"
        );
        assert_eq!(
            output.matches("fln-stdout-explicit-world-marker").count(),
            1
        );
        assert_eq!(output.matches("fln-stdout-reused-action-marker").count(), 2);
        assert_eq!(
            output.matches("fln-stdout-ordinary-source-marker").count(),
            1
        );
        assert_eq!(output.matches("fln-stdout-do-source-marker").count(), 1);
        return;
    }
    let environment = register(&raw_pin_environment().unwrap(), false);
    let engine = Engine::from_environment(environment);
    let root = engine.logical_root(&KVMap::new());

    let batch = run(
        &engine,
        "def savedStdout : BaseIO IO.FS.Stream := IO.getStdout\ndef savedPrint : IO Unit := @IO.print String instToStringString \"fln-stdout-deferred-marker\\n\"",
    );
    for execution in &batch.batch.executions {
        let VmExit::Returned(returned) = &execution.exit else {
            panic!("deferred source action");
        };
        assert!(
            returned.value.closure_shell_parts().is_some(),
            "the stored value is an ordinary Golem closure"
        );
        assert_native_row(execution);
    }
    let batch = run(&engine, "#eval IO.getStdout");
    let execution = &batch.batch.executions[batch.batch.source_evaluation_indices[0]];
    let Some(IoEvaluationOutcome::Returned {
        exit: VmExit::Returned(stream),
        ..
    }) = execution.io_evaluation_outcome().unwrap()
    else {
        panic!("logical stream result");
    };
    assert_constructor(&stream.value, 0, 6);
    for index in 0..6 {
        assert!(
            child(&stream.value, index).closure_shell_parts().is_some(),
            "public Stream field {index} is a Golem wrapper"
        );
    }

    let batch = run(
        &engine,
        "#eval @IO.print String instToStringString \"fln-stdout-replay-marker-☃\\n\"",
    );
    let execution = &batch.batch.executions[batch.batch.source_evaluation_indices[0]];
    assert_unit_packet(&execution.exit);
    let program = assert_native_row(execution);
    for _ in 0..2 {
        assert_unit_packet(
            &execute_golem_with_options(&program, &KVMap::new(), VmExecutionLimits::default())
                .into_complete()
                .unwrap(),
        );
    }

    let batch = run(
        &engine,
        "#eval IO.print \"fln-stdout-ordinary-source-marker\\n\"",
    );
    assert_unit_packet(&batch.batch.executions[batch.batch.source_evaluation_indices[0]].exit);
    let batch = run(
        &engine,
        "#eval do IO.print \"fln-stdout-do-source-marker\\n\"",
    );
    assert_unit_packet(&batch.batch.executions[batch.batch.source_evaluation_indices[0]].exit);

    let batch = run(
        &engine,
        "#eval (show IO Unit from fun world => match IO.getStdout world with | .mk stream next => IO.FS.Stream.putStr stream \"fln-stdout-explicit-world-marker\\n\" next)",
    );
    assert_unit_packet(&batch.batch.executions[batch.batch.source_evaluation_indices[0]].exit);

    let batch = run(
        &engine,
        "#eval (show IO Unit from let write := @IO.print String instToStringString \"fln-stdout-reused-action-marker\\n\"; fun world => match write world with | .ok _ next => write next | .error error next => @EST.Out.error IO.Error IO.RealWorld Unit error next)",
    );
    assert_unit_packet(&batch.batch.executions[batch.batch.source_evaluation_indices[0]].exit);

    let batch = run(
        &engine,
        "#eval (show IO Unit from fun world => match IO.getStdout world with | .mk stream next => IO.FS.Stream.flush stream next)",
    );
    assert!(matches!(
        &batch.batch.executions[batch.batch.source_evaluation_indices[0]].exit,
        VmExit::Refused {
            refusal: fln_vm::interpreter::VmRefusal::UnsupportedNativeClosure,
            ..
        }
    ));
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}
