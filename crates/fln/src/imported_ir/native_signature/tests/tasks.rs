use super::*;
use crate::imported_ir::{EntryArgument, native_effects};

const TASKS: [&str; 5] = ["Task.pure", "Task.get", "Task.spawn", "Task.map", "Task.bind"];

fn typed(x: u64, ty: IrType, expr: IrExpr) -> IrStmt {
    IrStmt::VDecl { x, ty, expr }
}

fn function(
    target: &str,
    params: &[IrType],
    result: IrType,
    body: Vec<IrStmt>,
    ret: u64,
) -> IrDecl {
    IrDecl::Function {
        name: name(target),
        params: params
            .iter()
            .enumerate()
            .map(|(index, ty)| IrParam {
                x: index as u64 + 1,
                ty: ty.clone(),
                borrow: false,
            })
            .collect(),
        result,
        body: IrBody {
            stmts: body,
            terminal: Box::new(IrTerminal::Ret(var(ret))),
        },
        sorry_dep: None,
    }
}

fn compile_tasks(decls: Vec<IrDecl>) -> Result<CompiledIr, IrExecutionError> {
    let users = decls
        .iter()
        .filter(|declaration| {
            declaration.name() == &name("Arity.main")
                || declaration.name().to_string().starts_with("TaskIR.")
        })
        .map(|declaration| declaration.name().clone())
        .collect();
    compile(
        &[IrModule {
            decls,
            ..IrModule::default()
        }],
        &name("Arity.main"),
        &[],
        &VerifiedPartition::user_fixture(),
        &users,
        IrExecutionLimits::default(),
    )
}

fn task_call(statements: &mut Vec<IrStmt>, mode: u8, output: u64, target: &str, args: &[u64]) {
    let prefix = if matches!(target, "Task.map" | "Task.bind") {
        2
    } else {
        1
    };
    let result = if target == "Task.get" {
        IrType::TObject
    } else {
        IrType::Object
    };
    let mut operands = vec![IrArg::Erased; prefix];
    operands.extend(args.iter().copied().map(var));
    let target = if mode == 0 {
        name(target)
    } else {
        Name::str(name(target), "_boxed")
    };
    let expr = if mode == 2 {
        // Capture only the first type. map/bind must keep their second
        // independent erased parameter until this closure is saturated.
        statements.push(typed(
            output + 100,
            IrType::Object,
            IrExpr::Pap {
                function: target,
                args: vec![IrArg::Erased],
            },
        ));
        IrExpr::Ap {
            x: output + 100,
            args: operands.into_iter().skip(1).collect(),
        }
    } else {
        IrExpr::Fap {
            function: target,
            args: operands,
        }
    };
    statements.push(typed(output, result, expr));
}

fn pipeline(mode: u8) -> Vec<IrDecl> {
    let mut statements = vec![
        num(1, 42),
        num(2, 0),
        typed(
            3,
            if mode == 0 {
                IrType::UInt8
            } else {
                IrType::Tagged
            },
            IrExpr::Lit(IrLit::Num(IrNat::Small(1))),
        ),
        typed(
            4,
            IrType::Object,
            IrExpr::Pap {
                function: name("TaskIR.spawn"),
                args: vec![var(1)],
            },
        ),
        typed(
            5,
            IrType::Object,
            IrExpr::Pap {
                function: name("TaskIR.increment"),
                args: vec![],
            },
        ),
        typed(
            6,
            IrType::Object,
            IrExpr::Pap {
                function: name("TaskIR.wrap"),
                args: vec![],
            },
        ),
    ];
    task_call(&mut statements, mode, 7, "Task.spawn", &[4, 2]);
    task_call(&mut statements, mode, 8, "Task.map", &[5, 7, 2, 3]);
    task_call(&mut statements, mode, 9, "Task.bind", &[8, 6, 2, 3]);
    task_call(&mut statements, mode, 10, "Task.get", &[9]);
    task_call(&mut statements, mode, 11, "Task.get", &[9]);
    statements.push(call(12, "Nat.add", &[10, 11]));
    let mut wrap = vec![num(2, 2), call(3, "Nat.add", &[1, 2])];
    task_call(&mut wrap, mode, 4, "Task.pure", &[3]);
    vec![
        entry(statements, 12),
        function(
            "TaskIR.spawn",
            &[IrType::TObject, IrType::Tagged],
            IrType::TObject,
            vec![],
            1,
        ),
        function(
            "TaskIR.increment",
            &[IrType::TObject],
            IrType::TObject,
            vec![num(2, 1), call(3, "Nat.add", &[1, 2])],
            3,
        ),
        function("TaskIR.wrap", &[IrType::TObject], IrType::Object, wrap, 4),
    ]
}

#[test]
fn imported_tasks_execute_direct_boxed_and_partial_native_calls() {
    for mode in 0..=2 {
        let compiled = compile_tasks(pipeline(mode)).unwrap();
        arrays_reference::assert_nat_replay(&compiled, "90");
        assert_eq!(
            compiled
                .native_externs()
                .iter()
                .filter(|row| row.starts_with("extern:Task."))
                .count(),
            5
        );
        assert_eq!(compiled.reference_functions().len(), 4);
        assert!(
            compiled.reference_functions().iter().all(|function| {
                function.name == name("Arity.main")
                    || function.name.to_string().starts_with("TaskIR.")
            })
        );
    }
}

#[test]
fn task_contracts_bind_full_and_native_telescopes_boxing_and_effects() {
    for (target, prefix, types, result) in [
        ("Task.pure", 1, vec![IrType::TObject], IrType::Object),
        ("Task.get", 1, vec![IrType::Object], IrType::TObject),
        (
            "Task.spawn",
            1,
            vec![IrType::TObject, IrType::TObject],
            IrType::Object,
        ),
        (
            "Task.map",
            2,
            vec![IrType::TObject, IrType::Object, IrType::TObject, IrType::UInt8],
            IrType::Object,
        ),
        (
            "Task.bind",
            2,
            vec![IrType::Object, IrType::Object, IrType::TObject, IrType::UInt8],
            IrType::Object,
        ),
    ] {
        let row = crate::imported_ir::native_row(&name(target)).unwrap();
        let bridge = BoxedNative::from_row(row).unwrap().unwrap();
        assert_eq!(bridge.runtime_parameters(), prefix..prefix + types.len());
        let params: Vec<_> = std::iter::repeat_n(IrType::Erased, prefix)
            .chain(types.clone())
            .enumerate()
            .map(|(index, ty)| IrParam {
                x: index as u64,
                ty,
                borrow: false,
            })
            .collect();
        for supplied in [&params[..], &params[prefix..]] {
            assert_eq!(validated_ir_arity(row, supplied.len()).unwrap(), types.len());
            validate_extern_signature(row, supplied, &result).unwrap();
            for index in 0..supplied.len() {
                let mut changed = supplied.to_vec();
                changed[index].borrow = true;
                assert!(validate_extern_signature(row, &changed, &result).is_err());
                changed[index].borrow = false;
                changed[index].ty = IrType::UInt64;
                assert!(validate_extern_signature(row, &changed, &result).is_err());
            }
            assert!(validate_extern_signature(row, supplied, &IrType::UInt64).is_err());
        }
        let boxed_params = params
            .iter()
            .map(|parameter| IrParam {
                ty: match parameter.ty {
                    IrType::Erased => IrType::TObject,
                    IrType::UInt8 => IrType::Tagged,
                    _ => parameter.ty.clone(),
                },
                ..parameter.clone()
            })
            .collect();
        let boxed = IrDecl::Extern {
            name: Name::str(name(target), "_boxed"),
            params: boxed_params,
            result: result.clone(),
            entries: vec![],
        };
        bridge.validate_declaration(&boxed).unwrap();
        let mut wrong = boxed.clone();
        let IrDecl::Extern { params, .. } = &mut wrong else {
            unreachable!()
        };
        params[prefix].borrow = true;
        assert!(bridge.validate_declaration(&wrong).is_err());
        assert_eq!(
            native_effects::classify(row, false).unwrap(),
            if target == "Task.get" {
                crate::imported_ir::fir::EffectClass::Pure
            } else {
                crate::imported_ir::fir::EffectClass::Task
            }
        );
        for changed in [
            GeneratedExternRow {
                name: "Foreign.task",
                ..*row
            },
            GeneratedExternRow {
                symbol: "foreign_task",
                ..*row
            },
            GeneratedExternRow {
                module: "Foreign",
                ..*row
            },
            GeneratedExternRow {
                kind: "opaque",
                ..*row
            },
            GeneratedExternRow {
                arity: row.arity + 1,
                ..*row
            },
            GeneratedExternRow {
                levels: row.levels + 1,
                ..*row
            },
            GeneratedExternRow {
                safety: "unsafe",
                ..*row
            },
            GeneratedExternRow {
                effect: "io",
                ..*row
            },
            GeneratedExternRow {
                ownership: "rule(borrowed-args,owned-result)",
                ..*row
            },
            GeneratedExternRow {
                partition: "kernel",
                ..*row
            },
            GeneratedExternRow {
                entry_class: "foreign",
                ..*row
            },
            GeneratedExternRow {
                entry_scope: "foreign",
                ..*row
            },
            GeneratedExternRow {
                mode: "foreign",
                ..*row
            },
            GeneratedExternRow {
                profile: "sound",
                ..*row
            },
        ] {
            assert!(matches!(
                BoxedNative::from_row(&changed),
                Err(IrExecutionError::NativeContract { .. })
            ));
        }
    }
    for target in [
        "BaseIO.asTask",
        "BaseIO.mapTask",
        "BaseIO.bindTask",
        "IO.getTaskState",
    ] {
        let row = crate::imported_ir::native_row(&name(target)).unwrap();
        assert!(native_effects::classify(row, false).is_err(), "{target}");
    }
}

#[test]
fn task_type_erasure_cannot_hide_data_or_rebind_native_wrapper_bodies() {
    for index in 0..2 {
        let mut declarations = pipeline(0);
        let IrDecl::Function { body, .. } = &mut declarations[0] else {
            unreachable!()
        };
        let args = body
            .stmts
            .iter_mut()
            .find_map(|statement| match statement {
                IrStmt::VDecl {
                    expr: IrExpr::Fap { function, args },
                    ..
                } if function == &name("Task.map") => Some(args),
                _ => None,
            })
            .unwrap();
        args[index] = var(1);
        assert!(matches!(
            compile_tasks(declarations),
            Err(IrExecutionError::Unsupported { .. })
        ));
    }
    for target in ["Task.map", "Task.bind"] {
        let entry = entry(
            vec![bind(
                1,
                IrExpr::Pap {
                    function: name(target),
                    args: vec![IrArg::Erased],
                },
            )],
            1,
        );
        assert!(compile_tasks(vec![entry]).is_err());
    }
    let caller = entry(
        vec![
            num(1, 42),
            bind(
                2,
                IrExpr::Fap {
                    function: name("Task.pure._boxed"),
                    args: vec![IrArg::Erased, var(1)],
                },
            ),
            call(3, "Task.get", &[2]),
        ],
        3,
    );
    let forged = function(
        "Task.pure._boxed",
        &[IrType::TObject, IrType::TObject],
        IrType::Object,
        vec![num(3, 999)],
        3,
    );
    arrays_reference::assert_nat_replay(
        &compile_tasks(vec![caller.clone(), forged.clone()]).unwrap(),
        "42",
    );
    let mut malformed = forged;
    let IrDecl::Function { params, .. } = &mut malformed else {
        unreachable!()
    };
    params[0].ty = IrType::UInt8;
    assert!(compile_tasks(vec![caller, malformed]).is_err());
}

#[test]
fn live_pinned_task_ir_preserves_native_prototypes_partial_calls_and_universes() {
    use std::path::PathBuf;
    use std::process::Command;

    let reference = std::env::var_os("FLN_REFERENCE_LEAN")
        .map(PathBuf::from)
        .or_else(|| {
            let library = PathBuf::from(std::env::var_os("FLN_REFERENCE_LIB")?);
            Some(library.parent()?.parent()?.join("bin/lean"))
        });
    let Some(reference) = reference else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference required for imported Task execution"
        );
        eprintln!("SKIP: imported Task execution requires FLN_REFERENCE_LEAN");
        return;
    };
    let pin = include_str!("../../../../../../SUITE.lock")
        .lines()
        .find(|line| line.starts_with("reference "))
        .and_then(|line| {
            line.split_whitespace()
                .find_map(|part| part.strip_prefix("commit="))
        })
        .expect("SUITE.lock Reference commit");
    let version = Command::new(&reference).arg("--githash").output().unwrap();
    assert!(version.status.success());
    assert_eq!(String::from_utf8(version.stdout).unwrap().trim(), pin);
    let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    let stamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let directory = root.join(format!("task-reference-{}-{stamp}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let source = include_str!("../../../../../fln-olean/fixtures/ir/NativeTaskModule.lean");
    std::fs::write(directory.join("NativeTaskModule.lean"), source).unwrap();
    let generated = Command::new(&reference)
        .current_dir(&directory)
        .args(["-j1", "-o", "NativeTaskModule.olean", "NativeTaskModule.lean"])
        .output()
        .unwrap();
    std::fs::write(directory.join("compile.stdout"), &generated.stdout).unwrap();
    std::fs::write(directory.join("compile.stderr"), &generated.stderr).unwrap();
    assert!(
        generated.status.success(),
        "{directory:?}: {}{}",
        String::from_utf8_lossy(&generated.stdout),
        String::from_utf8_lossy(&generated.stderr)
    );
    let module = crate::decode_ir_artifact(
        &std::fs::read(directory.join("NativeTaskModule.ir")).unwrap(),
        32 * 1024 * 1024,
    )
    .unwrap();
    std::fs::write(directory.join("decoded-ir.txt"), format!("{module:#?}")).unwrap();
    let users: BTreeSet<_> = module
        .decls
        .iter()
        .filter(|declaration| matches!(declaration, IrDecl::Function { .. }))
        .map(|declaration| declaration.name().clone())
        .collect();
    let partials: BTreeSet<_> = module
        .decls
        .iter()
        .flat_map(|declaration| match declaration {
            IrDecl::Function { body, .. } => body.bodies(),
            IrDecl::Extern { .. } => Vec::new(),
        })
        .flat_map(|body| &body.stmts)
        .filter_map(|statement| match statement {
            IrStmt::VDecl {
                expr: IrExpr::Pap { function, .. },
                ..
            } => Some(function.clone()),
            _ => None,
        })
        .collect();
    for target in TASKS {
        let boxed = Name::str(name(target), "_boxed");
        assert!(partials.contains(&boxed), "{boxed} optimized away");
    }

    let library = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            reference
                .parent()
                .unwrap()
                .parent()
                .unwrap()
                .join("lib/lean")
        });
    let core = crate::decode_ir_artifact(
        &std::fs::read(library.join("Init/Core.ir")).unwrap(),
        32 * 1024 * 1024,
    )
    .unwrap();
    let targets = TASKS.map(name);
    let prototypes = IrModule {
        decls: core
            .decls
            .into_iter()
            .filter(|declaration| {
                targets.iter().any(|target| {
                    declaration.name() == target
                        || *declaration.name() == Name::str(target.clone(), "_boxed")
                })
            })
            .collect(),
        ..IrModule::default()
    };
    for target in &targets {
        assert!(
            prototypes
                .decls
                .iter()
                .any(|declaration| declaration.name() == target)
        );
        assert!(!users.contains(target));
    }
    let cases: Vec<_> = [
        "taskPure",
        "taskGet",
        "taskSpawn",
        "taskMap",
        "taskBind",
        "taskShared",
        "taskPipeline",
        "taskCallable",
        "taskBoundCallable",
        "taskUniverses",
    ]
    .into_iter()
    .flat_map(|target| {
        [0, 42, u64::MAX]
            .into_iter()
            .map(move |value| (target, value))
    })
    .collect();
    let mut oracle_source = source.replacen(
        "public import Init.Core",
        "public import Init.Core\npublic meta import Init.Data.Repr",
        1,
    );
    for (target, value) in &cases {
        oracle_source.push_str(&format!("\n#eval {target} {value}\n"));
    }
    std::fs::write(directory.join("Oracle.lean"), oracle_source).unwrap();
    let oracle = Command::new(&reference)
        .current_dir(&directory)
        .args(["-j1", "Oracle.lean"])
        .output()
        .unwrap();
    std::fs::write(directory.join("oracle.stdout"), &oracle.stdout).unwrap();
    std::fs::write(directory.join("oracle.stderr"), &oracle.stderr).unwrap();
    assert!(
        oracle.status.success(),
        "{directory:?}: {}{}",
        String::from_utf8_lossy(&oracle.stdout),
        String::from_utf8_lossy(&oracle.stderr)
    );
    let output = String::from_utf8(oracle.stdout).unwrap();
    let expected: Vec<_> = output.lines().collect();
    assert_eq!(expected.len(), cases.len(), "{output}");
    let mut exercised = BTreeSet::new();
    for ((target, value), expected) in cases.into_iter().zip(expected) {
        for include_prototypes in [false, true] {
            let modules = if include_prototypes {
                vec![module.clone(), prototypes.clone()]
            } else {
                vec![module.clone()]
            };
            let compiled = compile(
                &modules,
                &name(target),
                &[EntryArgument::Nat(IrNat::Small(value))],
                &VerifiedPartition::user_fixture(),
                &users,
                IrExecutionLimits::default(),
            )
            .unwrap_or_else(|error| {
                panic!("{target} {value}, prototypes={include_prototypes}: {error}; {directory:?}")
            });
            exercised.extend(compiled.native_externs().iter().cloned());
            arrays_reference::assert_nat_replay(&compiled, expected);
            assert!(
                compiled
                    .reference_functions()
                    .iter()
                    .all(|function| users.contains(&function.name))
            );
        }
    }
    for target in TASKS {
        assert!(exercised.contains(&format!("extern:{target}")));
    }
    eprintln!("Task Reference differential retained in {directory:?}");
}
