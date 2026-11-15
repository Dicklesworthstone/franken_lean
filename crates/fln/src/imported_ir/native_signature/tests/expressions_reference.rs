//! Actual pinned expression IR, including scalar/boxed native prototypes.

use super::arrays_reference::assert_nat_replay;
use super::*;
use crate::imported_ir::EntryArgument;
use std::path::PathBuf;
use std::process::Command;

const TARGETS: [&str; 16] = [
    "Lean.Expr.data",
    "Lean.Expr.mkData",
    "Lean.Expr.mkAppData",
    "Lean.Expr.equal",
    "Lean.Expr.hasLooseBVar",
    "Lean.Expr.liftLooseBVars",
    "Lean.Expr.instantiate1",
    "Lean.Expr.instantiate",
    "Lean.Expr.instantiateRev",
    "Lean.Expr.instantiateRange",
    "Lean.Expr.instantiateRevRange",
    "Lean.Expr.abstract",
    "Lean.Expr.abstractRange",
    "Lean.Expr.replaceImpl",
    "Lean.Expr.findImpl?",
    "Lean.Expr.findExtImpl?",
];

#[test]
fn live_pinned_expr_primitives_preserve_binders_arrays_data_and_boxed_calls() {
    let Some(reference) = std::env::var_os("FLN_REFERENCE_LEAN").map(PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference required for native expression primitives"
        );
        eprintln!("SKIP: native expression primitives require FLN_REFERENCE_LEAN");
        return;
    };
    let pin = include_str!("../../../../../../SUITE.lock")
        .lines()
        .find(|line| line.starts_with("reference "))
        .and_then(|line| {
            line.split_whitespace()
                .find_map(|part| part.strip_prefix("commit="))
        })
        .unwrap();
    let version = Command::new(&reference).arg("--githash").output().unwrap();
    assert!(version.status.success());
    assert_eq!(String::from_utf8(version.stdout).unwrap().trim(), pin);
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
    let stamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    let dir = root.join(format!(
        "native-expr-reference-{}-{stamp}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    let source = include_str!("../../../../../fln-olean/fixtures/ir/NativeExprModule.lean");
    std::fs::write(dir.join("NativeExprModule.lean"), source).unwrap();
    let generated = Command::new(&reference)
        .current_dir(&dir)
        .args(["-o", "NativeExprModule.olean", "NativeExprModule.lean"])
        .output()
        .unwrap();
    assert!(
        generated.status.success(),
        "{dir:?}: {}{}",
        String::from_utf8_lossy(&generated.stdout),
        String::from_utf8_lossy(&generated.stderr)
    );
    let module = crate::decode_ir_artifact(
        &std::fs::read(dir.join("NativeExprModule.ir")).unwrap(),
        32 * 1024 * 1024,
    )
    .unwrap();
    std::fs::write(dir.join("decoded-ir.txt"), format!("{module:#?}")).unwrap();
    let users: BTreeSet<_> = module
        .decls
        .iter()
        .map(|declaration| declaration.name().clone())
        .collect();
    assert!(
        users
            .iter()
            .all(|declaration| declaration.to_display_string().starts_with("NativeExpr."))
    );

    let mut prototypes = IrModule::default();
    for path in [
        "Lean/Expr.ir",
        "Lean/Util/ReplaceExpr.ir",
        "Lean/Util/FindExpr.ir",
    ] {
        let bytes = std::fs::read(library.join(path)).unwrap();
        fln_olean::pin::check_pinned_header(&bytes).unwrap();
        let decoded = crate::decode_ir_artifact(&bytes, 32 * 1024 * 1024).unwrap();
        prototypes.decls.extend(decoded.decls);
    }
    let mut native = IrModule::default();
    for target in TARGETS {
        let row = crate::imported_ir::native_row(&name(target)).unwrap();
        let external = prototypes
            .decls
            .iter()
            .find(|declaration| declaration.name() == &name(target))
            .unwrap();
        let IrDecl::Extern { params, result, .. } = external else {
            panic!("{target} must be an extern")
        };
        validate_extern_signature(row, params, result)
            .unwrap_or_else(|error| panic!("{target}: {error:?}; {external:?}"));
        // Raw prototype borrowing is exact even for rows whose generated VM
        // lifetime rule differs. Neither direction is an admission shortcut.
        for index in 0..params.len() {
            let mut changed = params.clone();
            changed[index].borrow = !changed[index].borrow;
            assert!(
                matches!(
                    validate_extern_signature(row, &changed, result),
                    Err(IrExecutionError::NativeContract { .. })
                ),
                "{target} parameter {index}"
            );
        }
        let mut changed = params.clone();
        changed[0].ty = IrType::Void;
        assert!(matches!(
            validate_extern_signature(row, &changed, result),
            Err(IrExecutionError::NativeContract { .. })
        ));
        assert!(matches!(
            validate_extern_signature(row, params, &IrType::Void),
            Err(IrExecutionError::NativeContract { .. })
        ));
        native.decls.push(external.clone());
        let boxed = Name::str(name(target), "_boxed");
        let wrapper = prototypes
            .decls
            .iter()
            .find(|declaration| declaration.name() == &boxed)
            .unwrap();
        BoxedNative::from_row(row)
            .unwrap()
            .unwrap()
            .validate_declaration(wrapper)
            .unwrap_or_else(|error| panic!("{target}: {error:?}; {wrapper:?}"));
        native.decls.push(wrapper.clone());
        if matches!(
            target,
            "Lean.Expr.replaceImpl" | "Lean.Expr.findImpl?" | "Lean.Expr.findExtImpl?"
        ) {
            assert!(
                module.decls.iter().any(|declaration| match declaration {
                    IrDecl::Function { body, .. } => body.bodies().into_iter().any(|body| body
                        .stmts
                        .iter()
                        .any(|statement| matches!(
                            statement,
                            IrStmt::VDecl {
                                expr: IrExpr::Pap { function, args },
                                ..
                            } if function == &boxed && args.len() == 1
                        ))),
                    IrDecl::Extern { .. } => false,
                }),
                "{target} captured callback call was optimized away"
            );
        }
    }
    let mut cases: Vec<(&str, Vec<u64>)> = vec![
        ("single", vec![0]),
        ("single", vec![3]),
        ("single", vec![42]),
        ("arrayOrder", vec![0, 0]),
        ("arrayOrder", vec![0, 1]),
        ("arrayOrder", vec![37, 0]),
        ("arrayOrder", vec![37, 1]),
        ("lift", vec![0, 0]),
        ("lift", vec![0, 4]),
        ("lift", vec![1, 4]),
        ("lift", vec![1_u64 << 32, (1_u64 << 32) + 4]),
        ("lift", vec![u64::MAX, 7]),
        ("contains", vec![0]),
        ("contains", vec![1]),
        ("contains", vec![2]),
        ("contains", vec![3]),
        ("contains", vec![1_u64 << 32]),
        ("contains", vec![u64::MAX]),
        ("strictEquality", vec![0]),
        ("strictEquality", vec![1]),
        ("data", vec![0]),
        ("data", vec![41]),
        ("packData", vec![u64::MAX, 103, 256, 15]),
        (
            "packData",
            vec![0x1234_5678_9abc_def0, 1_048_575, u32::MAX as u64, 10],
        ),
        ("packAppData", vec![0, u64::MAX]),
        (
            "packAppData",
            vec![0x1234_5678_9abc_def0, 0xfedc_ba98_7654_3210],
        ),
    ];
    for entry in ["replaceDirect", "replaceCaptured"] {
        for (value, mode) in [(0, 0), (7, 0), (7, 1), (65_536, 0)] {
            cases.push((entry, vec![value, mode]));
        }
    }
    // Every Expr constructor is returned unchanged, replaced at the root,
    // and rebuilt after replacing its Expr children. Non-expression fields
    // remain visible in the user fingerprint, including nonempty metadata.
    for kind in 0..12 {
        for mode in 0..3 {
            cases.push(("replaceKinds", vec![kind, 7, mode]));
        }
    }
    for value in [0, 7, 65_536] {
        cases.push(("replaceData", vec![value]));
    }
    for entry in ["findDirect", "findCaptured"] {
        for (needle, mode) in [(7, 0), (7, 1), (8, 2), (9, 2)] {
            cases.push((entry, vec![7, needle, mode]));
        }
    }
    for entry in ["findExtDirect", "findExtCaptured"] {
        for (needle, mode, tree) in [
            (99, 2, 0), // Inner partial application is never inspected.
            (99, 3, 0), // Function precedes application arguments.
            (99, 4, 0), // Root match precedes its children.
            (7, 0, 1),
            (8, 0, 1),
            (7, 1, 1), // A done lambda prunes both type and body.
            (9, 1, 1), // Pruning preserves the outer argument search.
            (99, 0, 0),
            (7, 0, 0),
            (8, 0, 0),
            (9, 0, 0),
        ] {
            cases.push((entry, vec![7, needle, mode, tree]));
        }
    }
    // Ordinary find still inspects the partial application skipped by findExt.
    cases.push(("findPartialApplication", vec![7]));
    for captured in [0, 1] {
        cases.push(("abstractBinders", vec![7, 0, 0, captured]));
        for count in [0, 1, 2, 3, 4, 100, 1_u64 << 32, u64::MAX] {
            cases.push(("abstractBinders", vec![7, count, 1, captured]));
        }
        for reverse in [0, 1] {
            for (begin, end) in [(0, 0), (0, 4), (1, 3), (2, 4), (4, 4)] {
                cases.push(("rangeOrder", vec![17, begin, end, reverse, captured]));
            }
        }
    }
    let mut oracle_source = source.to_owned();
    for (entry, args) in &cases {
        oracle_source.push_str(&format!("\n#eval NativeExpr.{entry}"));
        for value in args {
            oracle_source.push_str(&format!(" {value}"));
        }
    }
    std::fs::write(dir.join("Oracle.lean"), oracle_source).unwrap();
    let oracle = Command::new(&reference)
        .current_dir(&dir)
        .arg("Oracle.lean")
        .output()
        .unwrap();
    std::fs::write(dir.join("oracle.stdout"), &oracle.stdout).unwrap();
    std::fs::write(dir.join("oracle.stderr"), &oracle.stderr).unwrap();
    assert!(
        oracle.status.success(),
        "{dir:?}: {}{}",
        String::from_utf8_lossy(&oracle.stdout),
        String::from_utf8_lossy(&oracle.stderr)
    );
    let output = String::from_utf8(oracle.stdout).unwrap();
    let expected: Vec<_> = output.lines().collect();
    assert_eq!(expected.len(), cases.len(), "{output}");
    let modules = [module, native];
    let partition = VerifiedPartition::user_fixture();
    let mut observed = BTreeSet::new();
    for ((entry, args), expected) in cases.iter().zip(expected) {
        let arguments: Vec<_> = args
            .iter()
            .map(|value| EntryArgument::Nat(IrNat::Small(*value)))
            .collect();
        let compiled = compile(
            &modules,
            &name(&format!("NativeExpr.{entry}")),
            &arguments,
            &partition,
            &users,
            IrExecutionLimits::default(),
        )
        .unwrap_or_else(|error| panic!("{entry} {args:?}: {error:?}; {dir:?}"));
        assert_nat_replay(&compiled, expected);
        assert!(
            compiled
                .reference_functions()
                .iter()
                .all(
                    |function| function.producer() == "reference" && users.contains(&function.name)
                )
        );
        assert!(matches!(
            compiled
                .execute(
                    ExecutionLimits {
                        max_steps: 0,
                        ..ExecutionLimits::default()
                    },
                    None
                )
                .outcome,
            Outcome::Inconclusive(_)
        ));
        assert!(matches!(
            compiled
                .execute(ExecutionLimits::default(), Some(&|| true))
                .outcome,
            Outcome::Inconclusive(_)
        ));
        assert_nat_replay(&compiled, expected);
        observed.extend(compiled.native_externs().iter().cloned());
    }
    for target in TARGETS {
        assert!(
            observed.contains(&format!("extern:{target}")),
            "{target} not linked by actual user IR"
        );
    }
}

#[test]
fn imported_expr_binder_primitives_link_execute_and_replay_without_toolchain_bodies() {
    for abstract_target in ["Lean.Expr.abstract", "Lean.Expr.abstractRange"] {
        for (instantiate_target, expected) in [
            ("Lean.Expr.instantiateRange", "2917"),
            ("Lean.Expr.instantiateRevRange", "1729"),
        ] {
            for captured in [false, true] {
                let mut stmts = vec![
                    num(1, 0),
                    num(2, 1),
                    num(3, 2),
                    num(4, 3),
                    call(5, "Lean.Expr.fvar._override", &[1]),
                    call(6, "Lean.Expr.mvar._override", &[1]),
                    call(7, "Lean.Expr.app._override", &[5, 6]),
                    call(8, "Array.emptyWithCapacity", &[1]),
                    call(9, "Array.push", &[8, 5]),
                    call(10, "Array.push", &[9, 6]),
                ];
                let abstract_args = if abstract_target == "Lean.Expr.abstract" {
                    vec![7, 10]
                } else {
                    vec![7, 3, 10]
                };
                if captured {
                    stmts.extend([
                        bind(
                            11,
                            IrExpr::Pap {
                                function: name(abstract_target),
                                args: abstract_args[..abstract_args.len() - 1]
                                    .iter()
                                    .copied()
                                    .map(var)
                                    .collect(),
                            },
                        ),
                        bind(
                            12,
                            IrExpr::Ap {
                                x: 11,
                                args: vec![var(10)],
                            },
                        ),
                    ]);
                } else {
                    stmts.push(call(12, abstract_target, &abstract_args));
                }
                stmts.extend([
                    num(13, 17),
                    num(14, 29),
                    call(15, "Lean.Expr.bvar._override", &[13]),
                    call(16, "Lean.Expr.bvar._override", &[14]),
                    call(17, "Array.push", &[8, 5]), // Prefix is outside the selected range.
                    call(18, "Array.push", &[17, 15]),
                    call(19, "Array.push", &[18, 16]),
                    call(20, "Array.push", &[19, 6]), // Suffix is outside the selected range.
                ]);
                if captured {
                    stmts.extend([
                        bind(
                            21,
                            IrExpr::Pap {
                                function: name(instantiate_target),
                                args: vec![var(12), var(2), var(4)],
                            },
                        ),
                        bind(
                            22,
                            IrExpr::Ap {
                                x: 21,
                                args: vec![var(20)],
                            },
                        ),
                    ]);
                } else {
                    stmts.push(call(22, instantiate_target, &[12, 2, 4, 20]));
                }
                stmts.extend([
                    bind(23, IrExpr::Proj { i: 0, x: 22 }),
                    bind(24, IrExpr::Proj { i: 1, x: 22 }),
                    bind(25, IrExpr::Proj { i: 0, x: 23 }),
                    bind(26, IrExpr::Proj { i: 0, x: 24 }),
                    num(27, 100),
                    call(28, "Nat.mul", &[25, 27]),
                    call(29, "Nat.add", &[28, 26]),
                ]);
                let compiled = compile_declarations(vec![entry(stmts, 29)])
                    .unwrap_or_else(|error| panic!("{abstract_target}, {instantiate_target}, captured={captured}: {error:?}"));
                assert_nat(&compiled, expected);
                for target in [abstract_target, instantiate_target] {
                    assert!(
                        compiled
                            .native_externs()
                            .contains(&format!("extern:{target}"))
                    );
                }
                assert_eq!(compiled.reference_functions()[0].name, name("Arity.main"));
            }
        }
    }
}

#[test]
fn reviewed_expr_native_contracts_reject_forged_signatures_and_authority() {
    for target in TARGETS {
        let original = crate::imported_ir::native_row(&name(target)).unwrap();
        assert!(BoxedNative::from_row(original).unwrap().is_some());
        for changed in [
            GeneratedExternRow {
                symbol: "foreign",
                ..*original
            },
            GeneratedExternRow {
                module: "Foreign",
                ..*original
            },
            GeneratedExternRow {
                kind: "axiom",
                ..*original
            },
            GeneratedExternRow {
                arity: original.arity + 1,
                ..*original
            },
            GeneratedExternRow {
                ownership: "rule(scalar)",
                ..*original
            },
            GeneratedExternRow {
                effect: "io",
                ..*original
            },
            GeneratedExternRow {
                partition: "library-code",
                ..*original
            },
        ] {
            assert!(matches!(
                BoxedNative::from_row(&changed),
                Err(IrExecutionError::NativeContract { .. })
            ));
        }
    }
}
