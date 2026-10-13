//! Installed native `lean` guard specifications, with optional pinned differential checks.
//! CI sets FLN_GUARD_REFERENCE_LEAN to the checksum-verified v4.32.0 oracle.
#![forbid(unsafe_code)]
use std::{
    path::PathBuf,
    process::Command,
    sync::atomic::{AtomicUsize, Ordering},
};

static NEXT: AtomicUsize = AtomicUsize::new(0);

fn check(source: &str, expected_stdout: &str) {
    let directory = std::env::temp_dir().join(format!(
        "fln-guard-spec-parity-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&directory).unwrap();
    let path = directory.join("Main.lean");
    std::fs::write(&path, source).unwrap();
    let native = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(&path)
        .output()
        .unwrap();
    assert_eq!(native.status.code(), Some(0), "{source}\n{native:?}");
    assert_eq!(
        native.stdout,
        expected_stdout.as_bytes(),
        "{source}\n{native:?}"
    );
    assert!(native.stderr.is_empty(), "{source}\n{native:?}");
    if let Some(reference) = std::env::var_os("FLN_GUARD_REFERENCE_LEAN") {
        let reference = PathBuf::from(reference);
        let version = Command::new(&reference).arg("--githash").output().unwrap();
        assert!(version.status.success(), "{version:?}");
        assert_eq!(
            String::from_utf8(version.stdout).unwrap().trim(),
            "8c9756b28d64dab099da31a4c09229a9e6a2ef35",
            "wrong guard oracle"
        );
        let oracle = Command::new(reference).arg(&path).output().unwrap();
        assert_eq!(
            oracle.status.code(),
            native.status.code(),
            "{source}\n{oracle:?}"
        );
        assert_eq!(oracle.stdout, native.stdout, "{source}\n{oracle:?}");
        assert_eq!(oracle.stderr, native.stderr, "{source}\n{oracle:?}");
    }
}

#[test]
fn installed_guard_specs_compare_normalize_and_filter_like_the_pin() {
    // One real file crosses installed CLI import resolution, command execution,
    // guarded Repr formatting, filtering, matching, and neighboring output order.
    check(
        concat!(
            "#eval 1\n",
            "/-- info: 4 -/\n#guard_msgs (whitespace := exact) in\n#eval 2 + 2\n",
            "/-- info:\n4 -/\n#guard_msgs (whitespace := normalized) in\n#eval 2 + 2\n",
            "/-- info:   4 -/\n#guard_msgs (whitespace := lax) in\n#eval 2 + 2\n",
            "/-- 4 -/\n#guard_msgs (substring := true) in\n#eval 2 + 2\n",
            "/-- info: 4 -/\n#guard_msgs (drop warning, info) in\n#eval 2 + 2\n",
            "#guard_msgs (drop info) in\n#eval 4\n",
            "#guard_msgs (pass info) in\n#eval 4\n",
            "#guard_msgs (pass all, drop info) in\n#eval 4\n",
            "#guard_msgs (drop info, pass all) in\n#eval 4\n",
            "#guard_msgs (pass error, drop all) in\n#eval 4\n",
            "/-- info: 1 : Nat -/\n#guard_msgs (info) in\n#check 1\n",
            "#guard_msgs (drop info) in\n#check 1\n",
            "#guard_msgs () in\ndef guardSilent : Nat := 9\n",
            "/-- info: 9 -/\n#guard_msgs (positions := false, ordering := sorted) in\n#eval guardSilent\n",
            "#eval 3\n",
        ),
        "1\n4\n4\n3\n",
    );
}
