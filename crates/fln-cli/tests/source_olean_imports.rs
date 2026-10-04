//! `fln check-source` resolves an import with no local source file to an
//! `.olean` on the search path and admits its closure through K1 and the
//! independent checker before checking the source (bead `franken_lean-z8j.1.8`).
#![forbid(unsafe_code)]

use std::path::PathBuf;
use std::process::Command;

fn fixture(case: &str) -> PathBuf {
    fln_core::checked_manifest_dir!()
        .join("tests/fixtures/olean_imports")
        .join(case)
        .join("Main.lean")
}

fn check_source(case: &str) -> (i32, String, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .arg(fixture(case))
        .output()
        .expect("run fln check-source");
    (
        output.status.code().expect("exit code"),
        String::from_utf8(output.stdout).expect("utf8 stdout"),
        String::from_utf8(output.stderr).expect("utf8 stderr"),
    )
}

fn pinned_prelude_present() -> bool {
    let present = std::env::var_os("HOME")
        .map(PathBuf::from)
        .map(|home| {
            home.join(".elan/toolchains")
                .join(format!("leanprover--lean4---{}", fln::OLEAN_PIN_TAG))
                .join("lib/lean/Init/Prelude.olean")
        })
        .is_some_and(|prelude| prelude.is_file());
    assert!(
        present || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "FLN_REQUIRE_REFERENCE is set but the pinned Reference Init.Prelude is absent"
    );
    present
}

#[test]
fn a_real_prelude_import_is_council_admitted_and_journaled() {
    if std::env::var_os("LEAN_PATH").is_some() || !pinned_prelude_present() {
        eprintln!("SKIP: pinned Reference lib/lean absent or LEAN_PATH overrides it");
        return;
    }
    let (code, stdout, stderr) = check_source("prelude");
    assert_eq!(code, 0, "stdout: {stdout}\nstderr: {stderr}");
    assert!(
        stdout.contains("\"schema\":\"fln.source-check/1\""),
        "{stdout}"
    );
    assert!(stdout.contains("\"theorems\":2"), "{stdout}");
    // Keep the exact prior declaration-only council root independently of
    // the source base root, which now also includes native metadata replay.
    assert!(
        stdout.contains(
            "\"declarationLogicalRoot\":\"a6ddda2c686b7badff7fb82388f59c1ccf821019684d8dbd19abe5066f874203\""
        ),
        "{stdout}"
    );
    assert!(
        stdout.contains(
            "\"oleanImports\":{\"trust\":\"recheck\",\"modules\":1,\"declarations\":2314}"
        ),
        "{stdout}"
    );
}

/// Source over the real Prelude's classes (bead `fln-13lk`). `instDecidableEqBool`
/// and its peers are stated through the `DecidableEq` abbreviation, which the
/// Reference keys under `Decidable`; before the registry unfolded it, activating
/// the Prelude's metadata refused every `import Init.Prelude`. `==` on `Nat`
/// reaches `instBEqOfDecidableEq [DecidableEq α]`, so the search also has to use
/// such an instance as a prerequisite. The counts are the Reference's own
/// `Init.Prelude` entries in `classExtension`, `instanceExtension` and
/// `defaultInstanceExtension` (75, 151 and 18 at the pin), so none is dropped.
#[test]
fn real_prelude_classes_and_instances_elaborate_source() {
    if std::env::var_os("LEAN_PATH").is_some() || !pinned_prelude_present() {
        eprintln!("SKIP: pinned Reference lib/lean absent or LEAN_PATH overrides it");
        return;
    }
    let (code, stdout, stderr) = check_source("prelude_classes");
    assert_eq!(code, 0, "stdout: {stdout}\nstderr: {stderr}");
    assert!(stdout.contains("\"commands\":4"), "{stdout}");
    assert!(stdout.contains("\"theorems\":2"), "{stdout}");
    assert!(
        stdout.contains(
            "\"oleanMetadata\":{\"classes\":75,\"instances\":151,\"defaultInstances\":18,"
        ),
        "{stdout}"
    );
}

#[test]
fn an_import_found_nowhere_is_refused_naming_the_search_path() {
    let (code, stdout, stderr) = check_source("missing");
    assert_eq!(code, 1, "stdout: {stdout}\nstderr: {stderr}");
    assert!(stdout.is_empty(), "{stdout}");
    assert!(stderr.contains("\"outcome\":\"input\""), "{stderr}");
    assert!(
        stderr.contains("import `Init.NoSuchModule` is neither a source file (")
            && stderr.contains("Init/NoSuchModule.lean)"),
        "{stderr}"
    );
    assert!(
        stderr.contains("nor an .olean on the search path"),
        "{stderr}"
    );
}

/// Unparseable source is refused before its imports are admitted (bead
/// `fln-parse-before-imports-j8p6`). Admitting the pinned `Init` closure through
/// both checkers takes over an hour here, so a refusal inside the deadline can
/// only come from the parse preflight, and it must be the parse refusal.
#[test]
fn unparseable_source_is_refused_before_its_init_closure_is_admitted() {
    use std::process::Stdio;
    use std::time::{Duration, Instant};
    if std::env::var_os("LEAN_PATH").is_some() || !pinned_prelude_present() {
        eprintln!("SKIP: pinned Reference lib/lean absent or LEAN_PATH overrides it");
        return;
    }
    let mut child = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .arg(fixture("unparseable"))
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("run fln check-source");
    let deadline = Instant::now() + Duration::from_secs(120);
    while child.try_wait().expect("poll fln check-source").is_none() {
        if Instant::now() > deadline {
            let _ = child.kill();
            let _ = child.wait();
            panic!(
                "no verdict within 120 s: the Init closure was admitted before the source was parsed"
            );
        }
        std::thread::sleep(Duration::from_millis(50));
    }
    let output = child.wait_with_output().expect("collect fln check-source");
    let stdout = String::from_utf8(output.stdout).expect("utf8 stdout");
    let stderr = String::from_utf8(output.stderr).expect("utf8 stderr");
    assert_eq!(
        output.status.code(),
        Some(1),
        "stdout: {stdout}\nstderr: {stderr}"
    );
    assert!(stdout.is_empty(), "{stdout}");
    assert!(stderr.contains("\"outcome\":\"input\""), "{stderr}");
    assert!(stderr.contains("parse refused source"), "{stderr}");
}
