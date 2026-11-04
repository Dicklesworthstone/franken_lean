//! Actual compiler-produced array IR, compared with the exact pinned Reference.
//! Reference subprocesses are test oracles; production execution stays native.
use super::*;
use crate::imported_ir::EntryArgument;
use std::path::PathBuf;
use std::process::Command;

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
    // reviewed array subset. Their bodies never acquire interpretation
    // authority; only explicitly allowed fixture functions can be executed.
    let prototypes = native_array_prototypes(&reference);
    // The test-only partition does not stand in for the full library census.
    let partition = VerifiedPartition::user_fixture();
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
    ];
    let mut users: BTreeSet<_> = cases.iter().map(|(entry, _)| name(entry)).collect();
    // Exact closed-value initializers emitted by this pinned fixture.
    users.extend([
        name("arrayPartialEmpty._closed_0"),
        name("useArrayEmpty"),
        name("arrayNativeHeap._closed_0"),
        name("byteArrayNativeRoundTrip._closed_0"),
        name("byteArrayNativeBounds._closed_0"),
        name("useArrayPush"),
        name("useArrayRead._redArg"),
        name("useArrayWrite"),
        name("useArrayWrite._redArg"),
        name("useByteArrayRead._redArg"),
    ]);
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
    let modules = [module, prototypes];
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
                .all(
                    |function| function.producer() == "reference" && users.contains(&function.name)
                )
        );
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

fn native_array_prototypes(reference: &std::path::Path) -> IrModule {
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
    let mut externs = BTreeSet::new();
    let mut wrappers = BTreeSet::new();
    for relative in [
        "Init/Prelude.ir",
        "Init/Data/Array/Basic.ir",
        "Init/Data/Array/Set.ir",
        "Init/Data/ByteArray/Basic.ir",
    ] {
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
    assert_eq!(externs.len(), 19, "all reviewed raw native prototypes");
    assert_eq!(
        wrappers, externs,
        "every raw prototype has its boxed wrapper"
    );
    assert_eq!(declarations.len(), 38);
    IrModule {
        decls: declarations,
        ..IrModule::default()
    }
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
