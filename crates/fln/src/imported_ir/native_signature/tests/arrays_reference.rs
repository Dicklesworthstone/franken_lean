//! Actual compiler-produced array IR, compared with the exact pinned Reference.
//! Reference subprocesses are test oracles; production execution stays native.
use super::*;
use crate::imported_ir::EntryArgument;
use std::path::PathBuf;
use std::process::Command;

const LIBRARY_FUNCTIONS: [&str; 4] = [
    "Array.reverse",
    "Array.reverse._redArg",
    "Array.reverse.loop",
    "Array.reverse.loop._redArg",
];

#[test]
fn live_pinned_arrays_match_reference_with_erased_proofs_and_canonical_replay() {
    let reference = std::env::var_os("FLN_REFERENCE_LEAN")
        .map(PathBuf::from)
        .or_else(|| {
            let lib = PathBuf::from(std::env::var_os("FLN_REFERENCE_LIB")?);
            Some(lib.parent()?.parent()?.join("bin/lean"))
        });
    let Some(reference) = reference else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference required for live imported array IR"
        );
        eprintln!("SKIP: live imported arrays require FLN_REFERENCE_LEAN");
        return;
    };
    let lock = include_str!("../../../../../../SUITE.lock");
    let pin = lock
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
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = root.join(format!("array-reference-{}-{unique}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let source = include_str!("../../../../../fln-olean/fixtures/ir/NativeArrayModule.lean");
    std::fs::write(dir.join("NativeArrayModule.lean"), source).unwrap();
    let generated = Command::new(&reference)
        .current_dir(&dir)
        .args([
            "-j1",
            "-o",
            "NativeArrayModule.olean",
            "NativeArrayModule.lean",
        ])
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
        &std::fs::read(dir.join("NativeArrayModule.ir")).unwrap(),
        32 * 1024 * 1024,
    )
    .unwrap();
    std::fs::write(dir.join("decoded-ir.txt"), format!("{module:#?}")).unwrap();
    // Supply the pin's actual full extern and boxed declarations for the
    // complete Array family. Native bodies never acquire interpretation
    // authority. The actual Array.reverse library functions use the complete
    // authenticated partition and ordinary compiler-helper witness checks.
    let (prototypes, library) = native_array_prototypes(&reference);
    let partition_path = std::env::var_os("FLN_REFERENCE_PARTITION")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            fln_core::checked_workspace_root!().join("contracts/builtin_partition.tsv")
        });
    let partition = VerifiedPartition::from_pinned_tsv(
        &std::fs::read_to_string(&partition_path).unwrap_or_else(|error| {
            panic!("actual library execution requires {partition_path:?}: {error}")
        }),
    )
    .unwrap();
    let cases = [
        ("arrayNativeEmpty", 0),
        ("arrayNativeEmpty", 4),
        ("arrayPartialEmpty", 0),
        ("arrayPartialEmpty", 4),
        ("arrayPartialEmpty", 17),
        ("arrayNativeRoundTrip", 0),
        ("arrayNativeRoundTrip", 42),
        ("arrayNativeRoundTrip", u64::MAX),
        ("arrayNativeSize", 0),
        ("arrayNativeSize", 3),
        ("arrayNativeHeap", 42),
        ("byteArrayNativeRoundTrip", 0),
        ("byteArrayNativeRoundTrip", 255),
        ("byteArrayNativeBounds", 0),
        ("byteArrayNativeBounds", 1),
        ("byteArrayNativeBounds", u64::MAX),
        ("byteArrayNativeHash", 0),
        ("byteArrayNativeHash", 1),
        ("byteArrayNativeHash", 255),
        ("arrayProofRoundTrip", 42),
        ("arrayProofRoundTrip", u64::MAX),
        ("arrayProofUSize", 42),
        ("byteArrayProofRoundTrip", 255),
        ("byteArrayProofUSize", 255),
        ("arrayPartialPush", 0),
        ("arrayPartialPush", 42),
        ("arrayPartialPush", u64::MAX),
        ("arrayPartialRead", 0),
        ("arrayPartialRead", 42),
        ("arrayPartialRead", u64::MAX),
        ("arrayPartialWrite", 0),
        ("arrayPartialWrite", 42),
        ("arrayPartialWrite", u64::MAX),
        ("byteArrayPartialRead", 0),
        ("byteArrayPartialRead", 255),
        ("byteArrayPartialRead", 256),
        ("arrayNativeListRoundTrip", 0),
        ("arrayNativeListRoundTrip", 42),
        ("arrayNativeListRoundTrip", u64::MAX),
        ("arrayNativePopEmpty", 0),
        ("arrayNativePopEmpty", 1),
        ("arrayNativePopEmpty", 4),
        ("arrayNativeSwap", 0),
        ("arrayNativeSwap", 42),
        ("arrayNativeSwap", u64::MAX),
        ("arrayNativeSwapIfInBounds", 0),
        ("arrayNativeSwapIfInBounds", 1),
        ("arrayNativeSwapIfInBounds", 2),
        ("arrayNativeSwapIfInBounds", u64::MAX),
        ("arrayPartialFromList", 0),
        ("arrayPartialFromList", 42),
        ("arrayPartialFromList", u64::MAX),
        ("arrayPartialToList", 0),
        ("arrayPartialToList", 42),
        ("arrayPartialToList", u64::MAX),
        ("arrayPartialPop", 0),
        ("arrayPartialPop", 42),
        ("arrayPartialPop", u64::MAX),
        ("arrayPartialSwap", 0),
        ("arrayPartialSwap", 42),
        ("arrayPartialSwap", u64::MAX),
        ("arrayPartialSwapProofs", 0),
        ("arrayPartialSwapProofs", 42),
        ("arrayPartialSwapProofs", u64::MAX),
        ("arrayPartialSwapIfInBounds", 0),
        ("arrayPartialSwapIfInBounds", 1),
        ("arrayPartialSwapIfInBounds", 2),
        ("arrayPartialSwapIfInBounds", u64::MAX),
        ("arrayNativeHeapSwap", 0),
        ("arrayNativeHeapSwap", 42),
        ("arrayNativeHeapSwap", u64::MAX),
        ("arrayLibraryReverse", 0),
        ("arrayLibraryReverse", 42),
        ("arrayLibraryReverse", u64::MAX),
        ("arrayLibraryReverseSmall", 0),
        ("arrayLibraryReverseSmall", 1),
        ("arrayLibraryReverseSmall", 2),
        ("arrayLibraryReverseSmall", 7),
    ];
    // Only exact function names emitted in this test's own source module are
    // users. Imported library helpers are never added to this authority set.
    let users: BTreeSet<_> = module
        .decls
        .iter()
        .filter(|declaration| matches!(declaration, IrDecl::Function { .. }))
        .map(|declaration| declaration.name().clone())
        .collect();
    let library_names: BTreeSet<_> = LIBRARY_FUNCTIONS.into_iter().map(name).collect();
    assert!(users.is_disjoint(&library_names));
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
    for target in [
        "Array.emptyWithCapacity._boxed",
        "Array.push._boxed",
        "Array.getInternal._boxed",
        "Array.set._boxed",
        "ByteArray.get._boxed",
        // Constructor/projection values are eta-expanded by the pin into
        // these user lambdas, whose bodies call Array.mk/toList natively.
        "arrayPartialFromList._lam_0",
        "arrayPartialToList._lam_0",
        "Array.pop._boxed",
        "Array.swap._boxed",
        "Array.swapIfInBounds._boxed",
    ] {
        assert!(
            boxed_partials.contains(&name(target)),
            "{target} optimized away; {dir:?}"
        );
    }
    let mut oracle_source = source.to_owned();
    for (entry, value) in cases {
        oracle_source.push_str(&format!("\n#eval {entry} {value}\n"));
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
        expected
            .iter()
            .all(|line| !line.is_empty() && line.bytes().all(|byte| byte.is_ascii_digit()))
    );
    assert!(
        cases
            .iter()
            .zip(&expected)
            .any(|((entry, _), value)| *entry == "byteArrayNativeHash"
                && value.parse::<u64>().unwrap() > u64::MAX / 2),
        "the differential must cover a full-width hash"
    );

    let mut observed = BTreeSet::new();
    let modules = [module, prototypes, library];
    for ((entry, value), expected) in cases.into_iter().zip(expected) {
        let compiled = compile(
            &modules,
            &name(entry),
            &[EntryArgument::Nat(IrNat::Small(value))],
            &partition,
            &users,
            IrExecutionLimits::default(),
        )
        .unwrap_or_else(|error| panic!("{entry} {value}: {error:?}; {dir:?}"));
        assert_nat_replay(&compiled, expected);
        assert!(
            compiled
                .reference_functions()
                .iter()
                .any(|function| function.name == name(entry) && function.producer() == "reference")
        );
        assert!(
            compiled
                .reference_functions()
                .iter()
                .all(|function| function.producer() == "reference"
                    && (users.contains(&function.name) || library_names.contains(&function.name)))
        );
        if entry.starts_with("arrayLibraryReverse") {
            for target in ["Array.reverse._redArg", "Array.reverse.loop._redArg"] {
                assert!(
                    compiled
                        .reference_functions()
                        .iter()
                        .any(|function| function.name == name(target)),
                    "{entry}: actual library code {target} must be selected"
                );
            }
        }
        let stopped = compiled.execute(
            ExecutionLimits {
                max_steps: 0,
                ..ExecutionLimits::default()
            },
            None,
        );
        assert!(matches!(stopped.outcome, Outcome::Inconclusive(_)));
        let cancel = || true;
        assert!(matches!(
            compiled
                .execute(ExecutionLimits::default(), Some(&cancel))
                .outcome,
            Outcome::Inconclusive(_)
        ));
        assert_nat_replay(&compiled, expected);
        observed.extend(compiled.native_externs().iter().cloned());
        eprintln!("live Reference and Golem: {entry} {value} = {expected}");
    }
    for operation in [
        "Array.mk",
        "Array.toList",
        "Array.pop",
        "Array.swap",
        "Array.swapIfInBounds",
        "Array.emptyWithCapacity",
        "Array.replicate",
        "Array.set!",
        "Array.usize",
        "Array.set",
        "Array.uset",
        "ByteArray.get!",
        "ByteArray.set!",
        "ByteArray.usize",
        "ByteArray.hash",
        "ByteArray.get",
        "ByteArray.set",
        "ByteArray.uget",
        "ByteArray.uset",
    ] {
        assert!(
            observed.contains(&format!("extern:{operation}")),
            "{operation} optimized away; {dir:?}"
        );
    }
    for alternatives in [
        ["Array.get!Internal", "Array.get!InternalBorrowed"],
        ["Array.getInternal", "Array.getInternalBorrowed"],
        ["Array.uget", "Array.ugetBorrowed"],
    ] {
        assert!(
            alternatives
                .iter()
                .any(|operation| observed.contains(&format!("extern:{operation}"))),
            "{alternatives:?} optimized away; {dir:?}"
        );
    }
}

fn native_array_prototypes(reference: &std::path::Path) -> (IrModule, IrModule) {
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
    let mut declarations = Vec::new();
    let mut library_functions = Vec::new();
    let library_names: BTreeSet<_> = LIBRARY_FUNCTIONS.into_iter().map(name).collect();
    let mut externs = BTreeSet::new();
    let mut wrappers = BTreeSet::new();
    for relative in [
        "Init/Prelude.ir",
        "Init/Data/Array/Basic.ir",
        "Init/Data/Array/Set.ir",
        "Init/Data/ByteArray/Basic.ir",
    ] {
        let path = library.join(relative);
        let bytes = std::fs::read(&path).unwrap();
        fln_olean::pin::check_pinned_header(&bytes)
            .unwrap_or_else(|error| panic!("{path:?}: {error:?}"));
        let module = crate::decode_ir_artifact(&bytes, 32 * 1024 * 1024)
            .unwrap_or_else(|error| panic!("{path:?}: {error:?}"));
        for declaration in module.decls {
            if library_names.contains(declaration.name()) {
                assert!(matches!(declaration, IrDecl::Function { .. }));
                library_functions.push(declaration);
                continue;
            }
            let (row, is_boxed) = match crate::imported_ir::native_row(declaration.name()) {
                Some(row) => (row, false),
                None => {
                    let Some(row) = boxed_row(declaration.name()) else {
                        continue;
                    };
                    (row, true)
                }
            };
            if !row.name.starts_with("Array.") && !row.name.starts_with("ByteArray.") {
                continue;
            }
            let Some(bridge) = BoxedNative::from_row(row).unwrap() else {
                continue;
            };
            if is_boxed {
                bridge.validate_declaration(&declaration).unwrap();
                assert!(wrappers.insert(row.name));
            } else {
                let IrDecl::Extern { params, result, .. } = &declaration else {
                    panic!("reviewed extern {} is a function in {path:?}", row.name);
                };
                assert_eq!(params.len(), bridge.arity());
                validate_extern_signature(row, params, result).unwrap();
                assert_eq!(
                    validated_ir_arity(row, params.len()).unwrap(),
                    bridge.runtime_parameters().len()
                );
                assert!(externs.insert(row.name));
            }
            declarations.push(declaration);
        }
    }
    assert_eq!(
        externs.len(),
        24,
        "20 Array and four proof-bearing ByteArray prototypes"
    );
    let array_census: BTreeSet<_> = fln_vm::extern_table_generated::EXTERN_ROWS
        .iter()
        .filter(|row| row.name.starts_with("Array."))
        .map(|row| row.name)
        .collect();
    assert_eq!(
        externs
            .iter()
            .copied()
            .filter(|name| name.starts_with("Array."))
            .collect::<BTreeSet<_>>(),
        array_census,
        "every Array census row must have an actual reviewed IR prototype"
    );
    assert_eq!(
        wrappers, externs,
        "every raw prototype has its boxed wrapper"
    );
    assert_eq!(declarations.len(), 48);
    assert_eq!(library_functions.len(), LIBRARY_FUNCTIONS.len());
    (
        IrModule {
            decls: declarations,
            ..IrModule::default()
        },
        IrModule {
            decls: library_functions,
            ..IrModule::default()
        },
    )
}

#[test]
fn boxed_list_array_conversions_preserve_heap_payloads_and_shared_arrays() {
    use fln_olean::ir::IrCtorInfo;
    let list = |x, tag, args: Vec<IrArg>| {
        bind(
            x,
            IrExpr::Ctor {
                info: IrCtorInfo {
                    name: name(if tag == 0 { "List.nil" } else { "List.cons" }),
                    cidx: tag,
                    size: args.len() as u64,
                    usize: 0,
                    ssize: 0,
                },
                args,
            },
        )
    };
    let pap = |x, target| {
        bind(
            x,
            IrExpr::Pap {
                function: name(target),
                args: vec![IrArg::Erased],
            },
        )
    };
    let ap = |x, function, argument| {
        bind(
            x,
            IrExpr::Ap {
                x: function,
                args: vec![var(argument)],
            },
        )
    };
    let stmts = vec![
        bind(1, IrExpr::Lit(IrLit::Num(IrNat::Big(vec![0, 1])))),
        num(2, 23),
        list(3, 0, vec![]),
        list(4, 1, vec![var(2), var(3)]),
        list(5, 1, vec![var(1), var(4)]),
        pap(6, "Array.mk._boxed"),
        ap(7, 6, 5),
        pap(8, "Array.toList._boxed"),
        ap(9, 8, 7),
        ap(10, 6, 9),
        pap(11, "Array.pop._boxed"),
        ap(12, 11, 7),
        ap(13, 11, 10),
        num(14, 0),
        call(15, "Array.get!Internal", &[14, 7, 14]),
        call(16, "Array.get!Internal", &[14, 10, 14]),
        num(17, 1),
        call(18, "Array.get!Internal", &[14, 10, 17]),
        call(19, "Array.size", &[12]),
        call(20, "Array.size", &[13]),
        call(21, "Array.size", &[7]),
        call(22, "Nat.add", &[15, 16]),
        call(23, "Nat.add", &[18, 22]),
        call(24, "Nat.add", &[19, 20]),
        call(25, "Nat.add", &[21, 24]),
        call(26, "Nat.add", &[23, 25]),
    ];
    assert_nat(
        &compile_declarations(vec![entry(stmts, 26)]).unwrap(),
        "36893488147419103259",
    );
}

pub(super) fn assert_nat_replay(compiled: &CompiledIr, expected: &str) {
    let bytes =
        flbc::encode_canonical(compiled.program.program(), flbc::CodecLimits::default()).unwrap();
    let replay = flbc::decode_canonical(&bytes, flbc::CodecLimits::default()).unwrap();
    assert_eq!(
        flbc::encode_canonical(&replay, flbc::CodecLimits::default()).unwrap(),
        bytes
    );
    for program in [compiled.program.program(), &replay] {
        let outcome = execute(program, ExecutionLimits::default(), None);
        let Outcome::Complete(VmExit::Returned(value)) = outcome else {
            panic!("{outcome:?}")
        };
        assert_eq!(nat_decimal(&value.value).as_deref(), Some(expected));
    }
}
