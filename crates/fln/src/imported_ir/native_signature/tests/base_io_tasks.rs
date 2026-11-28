use super::*;
use crate::imported_ir::{EntryArgument, native_effects};
use fln_olean::ir::IrCtorInfo;

const TASKS: [&str; 6] = [
    "BaseIO.asTask",
    "BaseIO.mapTask",
    "BaseIO.bindTask",
    "IO.wait",
    "IO.getTaskState",
    "IO.waitAny",
];

fn typed(x: u64, ty: IrType, expr: IrExpr) -> IrStmt {
    IrStmt::VDecl { x, ty, expr }
}

fn function(
    target: &str,
    params: &[IrType],
    result: IrType,
    stmts: Vec<IrStmt>,
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
            stmts,
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
                || declaration.name().parent() == name("BaseIOTaskIR")
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

fn task_call(stmts: &mut Vec<IrStmt>, mode: u8, output: u64, target: &str, args: &[u64]) {
    let prefix = if matches!(target, "BaseIO.mapTask" | "BaseIO.bindTask") {
        2
    } else {
        1
    };
    let result = match target {
        "IO.wait" | "IO.waitAny" => IrType::TObject,
        "IO.getTaskState" if mode == 0 => IrType::UInt8,
        "IO.getTaskState" => IrType::Tagged,
        _ => IrType::Object,
    };
    let mut operands = vec![IrArg::Erased; prefix];
    operands.extend(args.iter().copied().map(var));
    if target == "IO.waitAny" {
        operands.push(IrArg::Erased);
    }
    operands.push(IrArg::Erased);
    let target = if mode == 0 {
        name(target)
    } else {
        Name::str(name(target), "_boxed")
    };
    let expr = if mode >= 2 {
        // Mode 2 leaves the independent type slots pending. Mode 3 supplies
        // all data/proof slots but delays the world until a separate Apply.
        let captured = if mode == 2 { 1 } else { operands.len() - 1 };
        stmts.push(typed(
            output + 100,
            IrType::Object,
            IrExpr::Pap {
                function: target,
                args: operands[..captured].to_vec(),
            },
        ));
        IrExpr::Ap {
            x: output + 100,
            args: operands[captured..].to_vec(),
        }
    } else {
        IrExpr::Fap {
            function: target,
            args: operands,
        }
    };
    stmts.push(typed(output, result, expr));
}

fn pipeline(mode: u8) -> Vec<IrDecl> {
    let mut stmts = vec![
        num(1, 42),
        call(2, "ST.Prim.mkRef", &[1]),
        num(3, 0),
        typed(
            4,
            if mode == 0 {
                IrType::UInt8
            } else {
                IrType::Tagged
            },
            IrExpr::Lit(IrLit::Num(IrNat::Small(1))),
        ),
    ];
    for (output, callback) in [(5, "start"), (6, "map"), (7, "bind")] {
        stmts.push(typed(
            output,
            IrType::Object,
            IrExpr::Pap {
                function: name(&format!("BaseIOTaskIR.{callback}")),
                args: vec![var(2)],
            },
        ));
    }
    task_call(&mut stmts, mode, 8, "BaseIO.asTask", &[5, 3]);
    task_call(&mut stmts, mode, 9, "IO.wait", &[8]);
    task_call(&mut stmts, mode, 10, "BaseIO.mapTask", &[6, 8, 3, 4]);
    task_call(&mut stmts, mode, 11, "IO.wait", &[10]);
    task_call(&mut stmts, mode, 12, "BaseIO.bindTask", &[10, 7, 3, 4]);
    task_call(&mut stmts, mode, 13, "IO.wait", &[12]);
    task_call(&mut stmts, mode, 14, "IO.getTaskState", &[12]);
    let state = if mode == 0 {
        14
    } else {
        stmts.push(typed(15, IrType::UInt8, IrExpr::Unbox { x: 14 }));
        15
    };
    stmts.extend([
        call(16, "UInt8.toNat", &[state]),
        typed(17, IrType::Tagged, IrExpr::Lit(IrLit::Num(IrNat::Small(0)))),
        typed(
            18,
            IrType::Object,
            IrExpr::Ctor {
                info: IrCtorInfo {
                    name: name("List.cons"),
                    cidx: 1,
                    size: 2,
                    usize: 0,
                    ssize: 0,
                },
                args: vec![var(12), var(17)],
            },
        ),
    ]);
    task_call(&mut stmts, mode, 19, "IO.waitAny", &[18]);
    stmts.extend([
        call(20, "ST.Prim.Ref.get", &[2]),
        call(21, "Nat.add", &[9, 11]),
        call(22, "Nat.add", &[21, 13]),
        call(23, "Nat.add", &[22, 16]),
        call(24, "Nat.add", &[23, 19]),
        call(25, "Nat.add", &[24, 20]),
    ]);
    let mut declarations = vec![
        entry(stmts, 25),
        function(
            "BaseIOTaskIR.start",
            &[IrType::TObject, IrType::Tagged],
            IrType::TObject,
            vec![
                call(3, "ST.Prim.Ref.get", &[1]),
                num(4, 1),
                call(5, "Nat.add", &[3, 4]),
                typed(
                    6,
                    IrType::Tagged,
                    IrExpr::Fap {
                        function: name("ST.Prim.Ref.set"),
                        args: vec![var(1), var(5)],
                    },
                ),
            ],
            5,
        ),
    ];
    for (callback, delta, added) in [("map", 10, 2), ("bind", 100, 3)] {
        let mut stmts = vec![
            call(4, "ST.Prim.Ref.get", &[1]),
            num(5, delta),
            call(6, "Nat.add", &[4, 5]),
            typed(
                7,
                IrType::Tagged,
                IrExpr::Fap {
                    function: name("ST.Prim.Ref.set"),
                    args: vec![var(1), var(6)],
                },
            ),
            num(8, added),
            call(9, "Nat.add", &[2, 8]),
        ];
        if callback == "bind" {
            stmts.push(typed(
                10,
                IrType::Object,
                IrExpr::Fap {
                    function: name("Task.pure"),
                    args: vec![var(9)],
                },
            ));
        }
        declarations.push(function(
            &format!("BaseIOTaskIR.{callback}"),
            &[IrType::TObject, IrType::TObject, IrType::Tagged],
            if callback == "bind" {
                IrType::Object
            } else {
                IrType::TObject
            },
            stmts,
            if callback == "bind" { 10 } else { 9 },
        ));
    }
    declarations
}

#[test]
fn imported_base_io_tasks_execute_mutating_callbacks_direct_boxed_and_partial() {
    for mode in 0..=3 {
        let compiled = compile_tasks(pipeline(mode)).unwrap();
        arrays_reference::assert_nat_replay(&compiled, "339");
        for target in TASKS {
            assert!(
                compiled
                    .native_externs()
                    .contains(&format!("extern:{target}"))
            );
        }
        assert_eq!(compiled.reference_functions().len(), 4);
    }
    // Supplying the callback and priority creates a stored action. Its cell
    // mutation must remain absent until the final world slot is applied.
    let mut deferred = pipeline(0);
    let IrDecl::Function { body, .. } = &mut deferred[0] else {
        unreachable!()
    };
    body.stmts.truncate(7);
    body.stmts.extend([
        typed(
            30,
            IrType::Object,
            IrExpr::Pap {
                function: name("BaseIO.asTask._boxed"),
                args: vec![IrArg::Erased, var(5), var(3)],
            },
        ),
        call(31, "ST.Prim.Ref.get", &[2]),
    ]);
    body.terminal = Box::new(IrTerminal::Ret(var(31)));
    let compiled = compile_tasks(deferred).unwrap();
    assert!(
        compiled
            .native_externs()
            .contains(&"extern:BaseIO.asTask".to_owned())
    );
    arrays_reference::assert_nat_replay(&compiled, "42");
}

#[test]
fn base_io_task_contracts_bind_native_full_and_boxed_telescopes() {
    for (target, prefix, proofs, types, borrowed, result) in [
        (
            "BaseIO.asTask",
            1,
            0,
            vec![IrType::Object, IrType::TObject],
            vec![false, false],
            IrType::Object,
        ),
        (
            "BaseIO.mapTask",
            2,
            0,
            vec![
                IrType::Object,
                IrType::Object,
                IrType::TObject,
                IrType::UInt8,
            ],
            vec![false; 4],
            IrType::Object,
        ),
        (
            "BaseIO.bindTask",
            2,
            0,
            vec![
                IrType::Object,
                IrType::Object,
                IrType::TObject,
                IrType::UInt8,
            ],
            vec![false; 4],
            IrType::Object,
        ),
        (
            "IO.wait",
            1,
            0,
            vec![IrType::Object],
            vec![false],
            IrType::TObject,
        ),
        (
            "IO.getTaskState",
            1,
            0,
            vec![IrType::Object],
            vec![true],
            IrType::UInt8,
        ),
        (
            "IO.waitAny",
            1,
            1,
            vec![IrType::TObject],
            vec![true],
            IrType::TObject,
        ),
    ] {
        let row = crate::imported_ir::native_row(&name(target)).unwrap();
        let bridge = BoxedNative::from_row(row).unwrap().unwrap();
        assert_eq!(inferred_arity(row).unwrap(), types.len());
        assert_eq!(bridge.runtime_parameters(), prefix..prefix + types.len());
        let params: Vec<_> = std::iter::repeat_n(IrType::Erased, prefix)
            .chain(types.clone())
            .chain(std::iter::repeat_n(IrType::Erased, proofs))
            .chain([IrType::Void])
            .enumerate()
            .map(|(index, ty)| IrParam {
                x: index as u64 + 1,
                ty,
                borrow: (prefix..prefix + types.len()).contains(&index) && borrowed[index - prefix],
            })
            .collect();
        for supplied in [&params[..], &params[prefix..prefix + types.len()]] {
            assert_eq!(
                validated_ir_arity(row, supplied.len()).unwrap(),
                types.len()
            );
            validate_extern_signature(row, supplied, &result).unwrap();
            for index in 0..supplied.len() {
                let mut changed = supplied.to_vec();
                changed[index].borrow = !changed[index].borrow;
                assert!(validate_extern_signature(row, &changed, &result).is_err());
                changed = supplied.to_vec();
                changed[index].ty = IrType::UInt64;
                assert!(validate_extern_signature(row, &changed, &result).is_err());
            }
            assert!(validate_extern_signature(row, supplied, &IrType::UInt64).is_err());
        }
        let boxed_type = |ty: &IrType| match ty {
            IrType::Erased => IrType::TObject,
            IrType::Void | IrType::UInt8 => IrType::Tagged,
            _ => ty.clone(),
        };
        let boxed = IrDecl::Extern {
            name: Name::str(name(target), "_boxed"),
            params: params
                .iter()
                .map(|param| IrParam {
                    ty: boxed_type(&param.ty),
                    borrow: false,
                    ..param.clone()
                })
                .collect(),
            result: boxed_type(&result),
            entries: vec![],
        };
        bridge.validate_declaration(&boxed).unwrap();
        let mut changed = boxed;
        let IrDecl::Extern { params, .. } = &mut changed else {
            unreachable!()
        };
        params.last_mut().unwrap().ty = IrType::TObject;
        assert!(bridge.validate_declaration(&changed).is_err());
        assert_eq!(
            native_effects::classify(row, false).unwrap(),
            crate::imported_ir::fir::EffectClass::Io
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
                kind: "defn",
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
                effect: "pure",
                ..*row
            },
            GeneratedExternRow {
                ownership: "abi((owned_arg) -> owned_res)",
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
            assert!(inferred_arity(&changed).is_err());
        }
    }
}

#[test]
fn base_io_task_erasure_cannot_hide_types_proofs_worlds_or_native_replacements() {
    for target in TASKS {
        let prefix = if matches!(target, "BaseIO.mapTask" | "BaseIO.bindTask") {
            2
        } else {
            1
        };
        let runtime = if target == "BaseIO.asTask" {
            2
        } else if prefix == 2 {
            4
        } else {
            1
        };
        let suffix = if target == "IO.waitAny" { 2 } else { 1 };
        for index in (0..prefix).chain(prefix + runtime..prefix + runtime + suffix) {
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
                    } if function == &name(target) => Some(args),
                    _ => None,
                })
                .unwrap();
            args[index] = var(1);
            assert!(
                matches!(
                    compile_tasks(declarations),
                    Err(IrExecutionError::Unsupported {
                        form: "unreviewed native erased operand",
                        ..
                    })
                ),
                "{target} operand {index}"
            );
        }
        let mut declarations = pipeline(0);
        let IrDecl::Function { body, .. } = &mut declarations[0] else {
            unreachable!()
        };
        body.stmts.insert(
            1,
            typed(
                500,
                IrType::Object,
                IrExpr::Pap {
                    function: name(target),
                    args: vec![IrArg::Erased],
                },
            ),
        );
        assert!(matches!(
            compile_tasks(declarations),
            Err(IrExecutionError::Unsupported {
                form: "first-class erased native primitive",
                ..
            })
        ));
        let row = crate::imported_ir::native_row(&name(target)).unwrap();
        let signature = super::super::base_io_tasks::signature(row)
            .unwrap()
            .unwrap();
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
                } if function == &name(target) => Some(args),
                _ => None,
            })
            .unwrap();
        args.truncate(prefix + runtime);
        args.drain(..prefix).for_each(drop);
        declarations.push(IrDecl::Extern {
            name: name(target),
            params: std::iter::repeat_n(IrType::Erased, prefix)
                .chain(signature.parameters.iter().cloned())
                .chain(std::iter::repeat_n(IrType::Erased, signature.erased_proofs))
                .chain([IrType::Void])
                .enumerate()
                .map(|(index, ty)| IrParam {
                    x: index as u64 + 1,
                    ty,
                    borrow: (prefix..prefix + runtime).contains(&index)
                        && signature.borrowed[index - prefix],
                })
                .collect(),
            result: signature.result.clone(),
            entries: vec![],
        });
        assert!(
            matches!(
                compile_tasks(declarations),
                Err(IrExecutionError::Unsupported {
                    form: "native BaseIO task call omits explicit erased telescope",
                    ..
                })
            ),
            "{target} must retain its explicit world telescope"
        );
    }
    let forged = function(
        "BaseIO.asTask._boxed",
        &[
            IrType::TObject,
            IrType::Object,
            IrType::TObject,
            IrType::Tagged,
        ],
        IrType::Object,
        vec![num(5, 999)],
        5,
    );
    let mut declarations = pipeline(1);
    declarations.push(forged.clone());
    arrays_reference::assert_nat_replay(&compile_tasks(declarations).unwrap(), "339");
    let mut wrong = forged;
    let IrDecl::Function { params, .. } = &mut wrong else {
        unreachable!()
    };
    params[1].borrow = true;
    let mut declarations = pipeline(1);
    declarations.push(wrong);
    assert!(compile_tasks(declarations).is_err());
    for target in [
        "IO.cancel",
        "IO.checkCanceled",
        "IO.monoMsNow",
        "IO.Process.spawn",
    ] {
        let row = crate::imported_ir::native_row(&name(target)).unwrap();
        assert!(native_effects::classify(row, false).is_err(), "{target}");
    }
}

#[test]
fn live_pinned_base_io_task_ir_preserves_effects_worlds_and_except_payloads() {
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
            "pinned Reference required for imported BaseIO task execution"
        );
        eprintln!("SKIP: imported BaseIO task execution requires FLN_REFERENCE_LEAN");
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
    let directory = root.join(format!(
        "base-io-task-reference-{}-{stamp}",
        std::process::id()
    ));
    std::fs::create_dir_all(&directory).unwrap();
    let source = include_str!("../../../../../fln-olean/fixtures/ir/NativeBaseIOTaskModule.lean");
    std::fs::write(directory.join("NativeBaseIOTaskModule.lean"), source).unwrap();
    let generated = Command::new(&reference)
        .current_dir(&directory)
        .args([
            "-j1",
            "-o",
            "NativeBaseIOTaskModule.olean",
            "NativeBaseIOTaskModule.lean",
        ])
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
        &std::fs::read(directory.join("NativeBaseIOTaskModule.ir")).unwrap(),
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
    let partials: Vec<_> = module
        .decls
        .iter()
        .flat_map(|declaration| match declaration {
            IrDecl::Function { body, .. } => body.bodies(),
            IrDecl::Extern { .. } => Vec::new(),
        })
        .flat_map(|body| &body.stmts)
        .filter_map(|statement| match statement {
            IrStmt::VDecl {
                expr: IrExpr::Pap { function, args },
                ..
            } => Some((function.clone(), args.clone())),
            _ => None,
        })
        .collect();
    for (target, prefix) in [
        ("BaseIO.asTask", 1),
        ("BaseIO.mapTask", 2),
        ("BaseIO.bindTask", 2),
    ] {
        let boxed = Name::str(name(target), "_boxed");
        assert!(
            partials.contains(&(boxed.clone(), vec![IrArg::Erased; prefix])),
            "{boxed:?} erased-type partial application optimized away"
        );
    }
    assert!(
        partials.iter().any(|(function, args)| {
            function == &name("BaseIO.mapTask._boxed")
                && matches!(
                    args.as_slice(),
                    [IrArg::Erased, IrArg::Erased, IrArg::Var(_)]
                )
        }),
        "shared map must retain its callback and both erased types"
    );

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
    let targets: BTreeSet<_> = TASKS
        .into_iter()
        .chain([
            "Task.pure",
            "Task.get",
            "ST.Prim.mkRef",
            "ST.Prim.Ref.get",
            "ST.Prim.Ref.set",
        ])
        .map(name)
        .collect();
    let mut prototypes = IrModule::default();
    for relative in ["Init/Core.ir", "Init/System/ST.ir", "Init/System/IO.ir"] {
        let imported = crate::decode_ir_artifact(
            &std::fs::read(library.join(relative)).unwrap(),
            32 * 1024 * 1024,
        )
        .unwrap();
        prototypes
            .decls
            .extend(imported.decls.into_iter().filter(|declaration| {
                targets.contains(declaration.name())
                    || targets
                        .iter()
                        .any(|target| *declaration.name() == Name::str(target.clone(), "_boxed"))
            }));
    }
    for target in &targets {
        assert!(
            prototypes
                .decls
                .iter()
                .any(|declaration| declaration.name() == target),
            "missing {target:?} prototype"
        );
        assert!(!users.contains(target));
    }
    let cases: Vec<_> = [
        "baseIOAsTask",
        "baseIOMapTask",
        "baseIOBindTask",
        "baseIOShared",
        "baseIOPipeline",
        "baseIOObserve",
        "baseIOCallable",
        "baseIOBoundCallable",
        "baseIOUniverses",
        "baseIOExceptSuccess",
        "baseIOExceptError",
        "baseIOExceptMap",
        "baseIOExceptBind",
        "baseIOIOSuccess",
    ]
    .into_iter()
    .flat_map(|target| {
        [0, 42, u64::MAX]
            .into_iter()
            .map(move |value| (target, value))
    })
    .collect();
    let mut oracle_source = source.replacen(
        "public import Init.System.IO",
        "public import Init.System.IO\npublic meta import Init.System.IO\npublic meta import Init.Data.Repr",
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
                &[
                    EntryArgument::Nat(IrNat::Small(value)),
                    EntryArgument::Erased,
                ],
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
    for target in TASKS
        .into_iter()
        .chain(["ST.Prim.mkRef", "ST.Prim.Ref.get", "ST.Prim.Ref.set"])
    {
        assert!(exercised.contains(&format!("extern:{target}")), "{target}");
    }
    eprintln!("BaseIO Task Reference differential retained in {directory:?}");
}
