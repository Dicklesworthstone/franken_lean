//! Signed primitive closures use native semantics, with exact pinned IR types.
use super::arrays_reference::assert_nat_replay;
use super::*;
use crate::imported_ir::EntryArgument;
use fln_vm::interpreter::VmRefusal;
use std::path::{Path, PathBuf};
use std::process::Command;

const NAMES: [&str; 15] = [
    "Int.add",
    "Int.sub",
    "Int.mul",
    "Int.neg",
    "Int.natAbs",
    "Int.ofNat",
    "Int.negSucc",
    "Int.ediv",
    "Int.emod",
    "Int.tdiv",
    "Int.tmod",
    "Int.decEq",
    "Int.decLe",
    "Int.decLt",
    "Int.decNonneg",
];

#[test]
fn signed_primitive_closures_authenticate_the_complete_generated_contract() {
    for target in NAMES {
        let row = crate::imported_ir::native_row(&name(target)).unwrap();
        assert!(BoxedNative::from_row(row).unwrap().is_some(), "{target}");
        for changed in [
            GeneratedExternRow {
                name: "Foreign.value",
                ..*row
            },
            GeneratedExternRow {
                symbol: "foreign_value",
                ..*row
            },
            GeneratedExternRow {
                module: "Foreign",
                ..*row
            },
            GeneratedExternRow {
                kind: "axiom",
                ..*row
            },
            GeneratedExternRow {
                arity: row.arity + 1,
                ..*row
            },
            GeneratedExternRow { levels: 1, ..*row },
            GeneratedExternRow {
                ownership: "rule(borrowed-args,owned-result)",
                ..*row
            },
            GeneratedExternRow {
                effect: "io",
                ..*row
            },
            GeneratedExternRow {
                safety: "unsafe",
                ..*row
            },
            GeneratedExternRow {
                partition: "library-code",
                ..*row
            },
            GeneratedExternRow {
                entry_class: "unreviewed",
                ..*row
            },
            GeneratedExternRow {
                entry_scope: "unreviewed",
                ..*row
            },
            GeneratedExternRow {
                mode: "unreviewed",
                ..*row
            },
            GeneratedExternRow {
                profile: "standard",
                ..*row
            },
        ] {
            assert!(
                matches!(
                    BoxedNative::from_row(&changed),
                    Err(IrExecutionError::NativeContract { .. })
                ),
                "{target}: {changed:?}"
            );
        }
    }
    // A C arity of two does not authorize dropping divExact's proof slot
    // from a compiler-generated closure.
    let exact = crate::imported_ir::native_row(&name("Int.divExact")).unwrap();
    assert!(BoxedNative::from_row(exact).unwrap().is_none());
}

#[test]
fn signed_closures_preserve_reused_negative_heap_captures() {
    let compiled = compile_declarations(vec![entry(
        vec![
            num(1, u64::MAX),
            call(2, "Int.ofNat", &[1]),
            call(3, "Int.neg", &[2]),
            bind(
                4,
                IrExpr::Pap {
                    function: name("Int.add._boxed"),
                    args: vec![var(3)],
                },
            ),
            num(5, 1),
            call(6, "Int.ofNat", &[5]),
            call(7, "Int.neg", &[6]),
            bind(
                8,
                IrExpr::Ap {
                    x: 4,
                    args: vec![var(6)],
                },
            ),
            bind(
                9,
                IrExpr::Ap {
                    x: 4,
                    args: vec![var(7)],
                },
            ),
            call(10, "Int.natAbs", &[8]),
            call(11, "Int.natAbs", &[9]),
            call(12, "Int.natAbs", &[3]),
            call(13, "Nat.add", &[10, 11]),
            call(14, "Nat.add", &[13, 12]),
        ],
        14,
    )])
    .unwrap();
    assert_nat(&compiled, &(u128::from(u64::MAX) * 3).to_string());
}

#[test]
fn signed_constructors_preserve_reused_consumed_heap_arguments() {
    for (target, successor) in [("Int.ofNat", 0), ("Int.negSucc", 1)] {
        let compiled = compile_declarations(vec![entry(
            vec![
                num(1, u64::MAX),
                bind(
                    2,
                    IrExpr::Pap {
                        function: Name::str(name(target), "_boxed"),
                        args: vec![],
                    },
                ),
                bind(
                    3,
                    IrExpr::Ap {
                        x: 2,
                        args: vec![var(1)],
                    },
                ),
                bind(
                    4,
                    IrExpr::Ap {
                        x: 2,
                        args: vec![var(1)],
                    },
                ),
                call(5, "Int.natAbs", &[3]),
                call(6, "Int.natAbs", &[4]),
                call(7, "Nat.add", &[5, 6]),
                call(8, "Nat.add", &[7, 1]),
            ],
            8,
        )])
        .unwrap();
        assert_nat(
            &compiled,
            &(u128::from(u64::MAX) * 3 + successor * 2).to_string(),
        );
    }
}

#[test]
fn signed_native_wrappers_refuse_bad_types_and_cannot_supply_interpreted_bodies() {
    let caller = || {
        entry(
            vec![
                num(1, 19),
                call(2, "Int.ofNat", &[1]),
                call(3, "Int.neg", &[2]),
                bind(
                    4,
                    IrExpr::Pap {
                        function: name("Int.add._boxed"),
                        args: vec![var(3)],
                    },
                ),
                num(5, 23),
                call(6, "Int.ofNat", &[5]),
                bind(
                    7,
                    IrExpr::Ap {
                        x: 4,
                        args: vec![var(6)],
                    },
                ),
                call(8, "Int.natAbs", &[7]),
            ],
            8,
        )
    };
    let forged = IrDecl::Function {
        name: name("Int.add._boxed"),
        params: (1..=2)
            .map(|x| IrParam {
                x,
                borrow: false,
                ty: IrType::TObject,
            })
            .collect(),
        result: IrType::TObject,
        body: IrBody {
            stmts: vec![num(3, 999)],
            terminal: Box::new(IrTerminal::Ret(var(3))),
        },
        sorry_dep: None,
    };
    assert_nat(
        &compile_declarations(vec![caller(), forged.clone()]).unwrap(),
        "4",
    );
    for change in 0..5 {
        let mut wrong = forged.clone();
        let IrDecl::Function {
            params,
            result,
            sorry_dep,
            ..
        } = &mut wrong
        else {
            unreachable!()
        };
        match change {
            0 => params[0].borrow = true,
            1 => params[1].ty = IrType::UInt64,
            2 => *result = IrType::UInt64,
            3 => *sorry_dep = Some(name("sorryAx")),
            _ => {
                params.pop();
            }
        }
        assert!(matches!(
            compile_declarations(vec![caller(), wrong]),
            Err(IrExecutionError::NativeContract { .. })
        ));
    }
    let mut bad_value = caller();
    let IrDecl::Function { body, .. } = &mut bad_value else {
        unreachable!()
    };
    // Replace the signed capture directly, leaving the compiler telescope valid.
    body.stmts[2] = bind(3, IrExpr::Lit(IrLit::Str("not an Int".to_owned())));
    let compiled = compile_declarations(vec![bad_value]).unwrap();
    assert!(matches!(
        compiled.execute(ExecutionLimits::default(), None).outcome,
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::TypeMismatch { .. },
            ..
        })
    ));
    assert_nat(&compile_declarations(vec![caller()]).unwrap(), "4");
}

#[test]
fn live_pinned_integer_closures_match_signed_arithmetic_and_exact_native_prototypes() {
    let reference = std::env::var_os("FLN_REFERENCE_LEAN")
        .map(PathBuf::from)
        .or_else(|| {
            let library = PathBuf::from(std::env::var_os("FLN_REFERENCE_LIB")?);
            Some(library.parent()?.parent()?.join("bin/lean"))
        });
    let Some(reference) = reference else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference required for live signed primitive closures"
        );
        eprintln!("SKIP: live signed primitive closures require FLN_REFERENCE_LEAN");
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
    // Validate the actual raw and boxed telescope before using any fixture.
    let prototypes = native_integer_prototypes(&reference);
    let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = root.join(format!("integer-reference-{}-{unique}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let source = include_str!("../../../../../fln-olean/fixtures/ir/NativeIntModule.lean");
    std::fs::write(dir.join("NativeIntModule.lean"), source).unwrap();
    let generated = Command::new(&reference)
        .current_dir(&dir)
        .args(["-j1", "-o", "NativeIntModule.olean", "NativeIntModule.lean"])
        .output()
        .unwrap();
    std::fs::write(dir.join("compile.stdout"), &generated.stdout).unwrap();
    std::fs::write(dir.join("compile.stderr"), &generated.stderr).unwrap();
    assert!(
        generated.status.success(),
        "{dir:?}: {}{}",
        String::from_utf8_lossy(&generated.stdout),
        String::from_utf8_lossy(&generated.stderr)
    );
    let module = crate::decode_ir_artifact(
        &std::fs::read(dir.join("NativeIntModule.ir")).unwrap(),
        32 * 1024 * 1024,
    )
    .unwrap();
    std::fs::write(dir.join("decoded-ir.txt"), format!("{module:#?}")).unwrap();
    let boxed_partials: BTreeSet<_> = module
        .decls
        .iter()
        .flat_map(|declaration| {
            let bodies = match declaration {
                IrDecl::Function { body, .. } => body.bodies(),
                IrDecl::Extern { .. } => Vec::new(),
            };
            bodies
                .into_iter()
                .flat_map(|body| body.stmts.iter())
                .filter_map(|statement| match statement {
                    IrStmt::VDecl {
                        expr: IrExpr::Pap { function, .. },
                        ..
                    } => Some(function.clone()),
                    _ => None,
                })
        })
        .collect();
    for target in NAMES {
        assert!(
            boxed_partials.contains(&Name::str(name(target), "_boxed")),
            "{target} closure optimized away; {dir:?}"
        );
    }
    let cases = cases();
    let mut roots: BTreeSet<_> = cases.iter().map(|(entry, _)| *entry).collect();
    roots.extend([
        "integerFromMagnitude",
        "integerEncoding",
        "useIntTransform",
        "useIntMeasure",
        "useNatIntTransform",
        "useIntDecision",
    ]);
    // Admit only declarations generated for this fixture's named user functions.
    // System prototypes below are intentionally absent from this allowlist.
    let users: BTreeSet<_> = module
        .decls
        .iter()
        .map(|declaration| {
            let text = declaration.name().to_string();
            assert!(
                roots.contains(text.split('.').next().unwrap()),
                "unexpected fixture declaration: {text}"
            );
            assert!(crate::imported_ir::native_row(declaration.name()).is_none());
            assert!(boxed_row(declaration.name()).is_none());
            declaration.name().clone()
        })
        .collect();
    let mut oracle_source = source.to_owned();
    for (entry, values) in &cases {
        oracle_source.push_str(&format!("\n#eval {entry}"));
        for value in values {
            oracle_source.push_str(&format!(" {value}"));
        }
        oracle_source.push('\n');
    }
    std::fs::write(dir.join("Oracle.lean"), oracle_source).unwrap();
    let oracle = Command::new(&reference)
        .current_dir(&dir)
        .args(["-j1", "Oracle.lean"])
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
    assert_eq!(
        expected.len(),
        cases.len(),
        "unexpected oracle output: {output}"
    );
    assert!(
        expected.iter().any(|value| value.parse::<u128>().is_err()),
        "fixture must retain results beyond a machine integer"
    );
    let modules = [module, prototypes];
    let partition = VerifiedPartition::user_fixture();
    let mut observed = BTreeSet::new();
    for ((entry, values), expected) in cases.into_iter().zip(expected) {
        let arguments: Vec<_> = values
            .iter()
            .map(|&value| {
                EntryArgument::Nat(if value <= u128::from(u64::MAX) {
                    IrNat::Small(value as u64)
                } else {
                    IrNat::Big(vec![value as u64, (value >> 64) as u64])
                })
            })
            .collect();
        let compiled = compile(
            &modules,
            &name(entry),
            &arguments,
            &partition,
            &users,
            IrExecutionLimits::default(),
        )
        .unwrap_or_else(|error| panic!("{entry} {values:?}: {error:?}; {dir:?}"));
        eprintln!("live signed Reference and Golem: {entry} {values:?} = {expected}");
        assert_nat_replay(&compiled, expected);
        assert!(
            compiled
                .reference_functions()
                .iter()
                .any(|function| function.name == name(entry))
        );
        assert!(
            compiled
                .reference_functions()
                .iter()
                .all(
                    |function| function.producer() == "reference" && users.contains(&function.name)
                ),
            "native integer bodies must not acquire interpretation authority"
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
    for target in NAMES {
        assert!(
            observed.contains(&format!("extern:{target}")),
            "{target} not linked"
        );
    }
}

fn cases() -> Vec<(&'static str, Vec<u128>)> {
    let mut cases = Vec::new();
    for entry in [
        "intBoxedAdd",
        "intBoxedSub",
        "intBoxedMul",
        "intBoxedEDiv",
        "intBoxedEMod",
        "intBoxedTDiv",
        "intBoxedTMod",
        "intBoxedDecEq",
        "intBoxedDecLe",
        "intBoxedDecLt",
    ] {
        for (sa, a, sb, b) in [
            (0, 0, 0, 0),
            (0, 7, 0, 3),
            (1, 7, 0, 3),
            (0, 7, 1, 3),
            (1, 7, 1, 3),
            (1, 7, 1, 7),
            (0, 42, 0, 0),
            (1, 42, 0, 0),
            (1, 42, 1, 1),
            (1, 2_147_483_648, 0, 2_147_483_647),
            (0, u128::from(u64::MAX), 1, 2),
            (1, u128::MAX, 0, 3),
            (0, u128::MAX, 0, u128::MAX),
        ] {
            cases.push((entry, vec![sa, a, sb, b]));
        }
    }
    let magnitudes = [
        0,
        1,
        2_147_483_647,
        2_147_483_648,
        u128::from(u64::MAX),
        u128::MAX,
    ];
    for entry in ["intBoxedNeg", "intBoxedNatAbs", "intBoxedDecNonneg"] {
        for sign in [0, 1] {
            for magnitude in magnitudes {
                cases.push((entry, vec![sign, magnitude]));
            }
        }
    }
    for entry in ["intBoxedOfNat", "intBoxedNegSucc"] {
        for magnitude in magnitudes {
            cases.push((entry, vec![magnitude]));
        }
    }
    cases
}

fn native_integer_prototypes(reference: &Path) -> IrModule {
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
    let wanted: BTreeSet<_> = NAMES.into_iter().collect();
    let mut externs = BTreeSet::new();
    let mut wrappers = BTreeSet::new();
    let mut declarations = Vec::new();
    for relative in ["Init/Data/Int/Basic.ir", "Init/Data/Int/DivMod/Basic.ir"] {
        let path = library.join(relative);
        let module = crate::decode_ir_artifact(&std::fs::read(&path).unwrap(), 32 * 1024 * 1024)
            .unwrap_or_else(|error| panic!("{path:?}: {error:?}"));
        for declaration in module.decls {
            let (row, is_boxed) = match crate::imported_ir::native_row(declaration.name()) {
                Some(row) => (row, false),
                None => {
                    let Some(row) = boxed_row(declaration.name()) else {
                        continue;
                    };
                    (row, true)
                }
            };
            if !wanted.contains(row.name) {
                continue;
            }
            let bridge = BoxedNative::from_row(row).unwrap().unwrap();
            if is_boxed {
                bridge
                    .validate_declaration(&declaration)
                    .unwrap_or_else(|error| {
                        panic!("{} in {path:?}: {error:?}; {declaration:?}", row.name)
                    });
                assert!(wrappers.insert(row.name));
            } else {
                let IrDecl::Extern { params, result, .. } = &declaration else {
                    panic!("{} is not an extern in {path:?}", row.name)
                };
                validate_extern_signature(row, params, result).unwrap_or_else(|error| {
                    panic!("{} in {path:?}: {error:?}; {declaration:?}", row.name)
                });
                assert_eq!(
                    validated_ir_arity(row, params.len()).unwrap(),
                    bridge.arity()
                );
                assert!(externs.insert(row.name));
                // Mutating the genuine prototype cannot change the native ABI.
                for index in 0..params.len() {
                    let mut wrong = params.clone();
                    wrong[index].borrow = !wrong[index].borrow;
                    assert!(validate_extern_signature(row, &wrong, result).is_err());
                    wrong = params.clone();
                    wrong[index].ty = IrType::Erased;
                    assert!(validate_extern_signature(row, &wrong, result).is_err());
                }
                assert!(validate_extern_signature(row, params, &IrType::Void).is_err());
            }
            declarations.push(declaration);
        }
    }
    assert_eq!(externs, wanted, "all reviewed signed native raw prototypes");
    assert_eq!(
        wrappers, wanted,
        "all reviewed signed compiler boxed prototypes"
    );
    assert_eq!(declarations.len(), NAMES.len() * 2);
    IrModule {
        decls: declarations,
        ..IrModule::default()
    }
}
