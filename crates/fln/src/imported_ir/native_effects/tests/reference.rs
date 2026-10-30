//! Actual compiler-produced stateful IR, compared with the pinned Reference.
//! Subprocess execution is test-only; production execution remains on Golem.

use super::*;
use std::path::PathBuf;
use std::process::Command;

#[test]
fn live_pinned_local_state_matches_reference_and_canonical_replay() {
    let reference = std::env::var_os("FLN_REFERENCE_LEAN")
        .map(PathBuf::from)
        .or_else(|| {
            let lib = PathBuf::from(std::env::var_os("FLN_REFERENCE_LIB")?);
            Some(lib.parent()?.parent()?.join("bin/lean"))
        });
    let Some(reference) = reference else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "the pinned Reference is required for live imported state IR"
        );
        eprintln!("SKIP: live imported state IR requires the pinned Reference");
        return;
    };
    let lock = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../SUITE.lock"));
    let pin = lock
        .lines()
        .find(|line| line.starts_with("reference "))
        .and_then(|line| line.split_whitespace().find_map(|s| s.strip_prefix("commit=")))
        .expect("SUITE.lock Reference commit");
    let version = Command::new(&reference).arg("--githash").output().unwrap();
    assert!(version.status.success());
    assert_eq!(String::from_utf8(version.stdout).unwrap().trim(), pin);

    let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    std::fs::create_dir_all(&root).unwrap();
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = root.join(format!("state-reference-{}-{unique}", std::process::id()));
    std::fs::create_dir(&dir).unwrap();
    let source = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../fln-olean/fixtures/ir/NativeStateModule.lean"
    ));
    std::fs::write(dir.join("NativeStateModule.lean"), source).unwrap();
    let generated = Command::new(&reference)
        .current_dir(&dir)
        .args(["-o", "NativeStateModule.olean", "NativeStateModule.lean"])
        .output()
        .unwrap();
    std::fs::write(dir.join("compile.stdout"), &generated.stdout).unwrap();
    std::fs::write(dir.join("compile.stderr"), &generated.stderr).unwrap();
    assert!(
        generated.status.success(),
        "Reference compilation failed in {dir:?}: {}{}",
        String::from_utf8_lossy(&generated.stdout),
        String::from_utf8_lossy(&generated.stderr),
    );
    let bytes = std::fs::read(dir.join("NativeStateModule.ir")).unwrap();
    let module = crate::decode_ir_artifact(&bytes, 32 * 1024 * 1024).unwrap();
    std::fs::write(dir.join("decoded-ir.txt"), format!("{module:#?}")).unwrap();

    let cases = [
        ("localStateAnswer", 0),
        ("localStateAnswer", 7),
        ("localStateAnswer", u64::MAX),
        ("localStateSharedAnswer", 19),
        ("localStateClosureAnswer", 23),
        ("localStateArrayAnswer", 42),
        ("localStateModifyAnswer", 0),
        ("localStateModifyAnswer", u64::MAX),
        ("localStateArrayModifyAnswer", 42),
        ("localStateModifyClosureAnswer", 19),
        ("localStateModifyClosureAnswer", u64::MAX),
    ];
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
        "Reference oracle failed: {}{}",
        String::from_utf8_lossy(&oracle.stdout),
        String::from_utf8_lossy(&oracle.stderr),
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
            .all(|s| !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit()))
    );

    let mut observed = BTreeSet::new();
    for ((entry, value), expected) in cases.into_iter().zip(expected) {
        let compiled = compile_module(
            &module,
            entry,
            &[EntryArgument::Nat(IrNat::Small(value))],
            IrExecutionLimits::default(),
        )
        .unwrap_or_else(|error| panic!("{entry} {value}: {error:?}; artifacts {dir:?}"));
        assert_nat_replay(&compiled, expected);
        if entry.contains("Modify") {
            assert!(
                compiled.native_externs().iter().any(|row| row == "extern:ST.Prim.Ref.take"),
                "{entry} did not retain its take-based implementation; {dir:?}"
            );
        }
        observed.extend(compiled.native_externs().iter().cloned());
        eprintln!("live Reference and Golem: {entry} {value} = {expected}");
    }
    // Do not count an optimized-away program as native state coverage.
    for operation in CELL_ROWS.into_iter().chain(["ST.Prim.Ref.take"]) {
        assert!(
            observed.contains(&format!("extern:{operation}")),
            "{operation}; {dir:?}"
        );
    }
}
