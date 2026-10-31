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
    let lock = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../SUITE.lock"));
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
    let source = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../fln-olean/fixtures/ir/NativeArrayModule.lean"
    ));
    std::fs::write(dir.join("NativeArrayModule.lean"), source).unwrap();
    let generated = Command::new(&reference)
        .current_dir(&dir)
        .args(["-o", "NativeArrayModule.olean", "NativeArrayModule.lean"])
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
    // Only this fixture's explicitly allowed user functions are supplied.
    // The test-only partition does not stand in for the full library census;
    // all native calls still bind to the canonical generated ABI contracts.
    let partition = VerifiedPartition::user_fixture();
    let cases = [
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
    ];
    let mut users: BTreeSet<_> = cases.iter().map(|(entry, _)| name(entry)).collect();
    // Exact closed-value initializers emitted by this pinned fixture.
    users.extend([
        name("arrayNativeHeap._closed_0"),
        name("byteArrayNativeRoundTrip._closed_0"),
        name("byteArrayNativeBounds._closed_0"),
    ]);
    let mut oracle_source = source.to_owned();
    for (entry, value) in cases {
        oracle_source.push_str(&format!("\n#eval {entry} {value}\n"));
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
    for ((entry, value), expected) in cases.into_iter().zip(expected) {
        let compiled = compile(
            std::slice::from_ref(&module),
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

fn assert_nat_replay(compiled: &CompiledIr, expected: &str) {
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
