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
        // Council admission is this suite's subject, so the posture is pinned;
        // `source_import_reuse.rs` covers `reuse-verified`.
        .args(["check-source", "--json", "--import-posture", "recheck"])
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
            "\"oleanImports\":{\"trust\":\"recheck\",\"admission\":\"council\",\"modules\":1,\"declarations\":2314}"
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

fn check_source_with(
    jobs: &str,
    entry: &std::path::Path,
    lean_path: Option<&std::path::Path>,
) -> (Option<i32>, String, String) {
    let mut command = Command::new(env!("CARGO_BIN_EXE_fln"));
    command
        .args([
            "check-source",
            "--json",
            "--import-posture",
            "recheck",
            "--jobs",
            jobs,
        ])
        .arg(entry);
    if let Some(lean_path) = lean_path {
        command.env("LEAN_PATH", lean_path);
    }
    let output = command.output().expect("run fln check-source");
    (
        output.status.code(),
        String::from_utf8(output.stdout).expect("utf8 stdout"),
        String::from_utf8(output.stderr).expect("utf8 stderr"),
    )
}

/// `--jobs` changes how many closure modules the council checks at once, never
/// the report: the closure of `siblings` holds two modules that import only
/// `Init.Coe`, so they are checked side by side above one job. Equal bytes here
/// show the parallel import matches the serial one on this closure; they do not
/// prove schedule independence in general.
#[test]
fn the_report_is_byte_identical_at_one_and_several_jobs() {
    if std::env::var_os("LEAN_PATH").is_some() || !pinned_prelude_present() {
        eprintln!("SKIP: pinned Reference lib/lean absent or LEAN_PATH overrides it");
        return;
    }
    let serial = check_source_with("1", &fixture("siblings"), None);
    assert_eq!(serial.0, Some(0), "{serial:?}");
    assert!(
        serial.1.contains(
            "\"oleanImports\":{\"trust\":\"recheck\",\"admission\":\"council\",\"modules\":7,"
        ),
        "{serial:?}"
    );
    for jobs in ["3", "8"] {
        assert_eq!(
            check_source_with(jobs, &fixture("siblings"), None),
            serial,
            "--jobs {jobs}"
        );
    }
}

/// A closure member that does not decode is refused with the same report at any
/// `--jobs`. Its exported part is intact, so the closure still loads and the
/// refusal comes from the council's own decoding.
#[test]
fn a_corrupted_closure_member_is_refused_identically_at_one_and_several_jobs() {
    if std::env::var_os("LEAN_PATH").is_some() || !pinned_prelude_present() {
        eprintln!("SKIP: pinned Reference lib/lean absent or LEAN_PATH overrides it");
        return;
    }
    let pinned = std::env::var_os("HOME")
        .map(PathBuf::from)
        .expect("HOME names the pinned toolchain's home")
        .join(".elan/toolchains")
        .join(format!("leanprover--lean4---{}", fln::OLEAN_PIN_TAG))
        .join("lib/lean");
    let search = std::env::temp_dir().join(format!("fln-corrupted-closure-{}", std::process::id()));
    for module in [
        "Init/Prelude",
        "Init/Coe",
        "Init/Notation",
        "Init/Tactics",
        "Init/Data/Cast",
        "Init/Data/Option/Coe",
        "Init/Data/Zero",
    ] {
        for extension in ["olean", "olean.server", "olean.private"] {
            let from = pinned.join(format!("{module}.{extension}"));
            let to = search.join(format!("{module}.{extension}"));
            std::fs::create_dir_all(to.parent().expect("a module directory"))
                .expect("create the search path");
            std::fs::copy(&from, &to)
                .unwrap_or_else(|error| panic!("copy {}: {error}", from.display()));
        }
    }
    let private = search.join("Init/Coe.olean.private");
    let mut bytes = std::fs::read(&private).expect("read the private part");
    bytes[0] ^= u8::MAX;
    std::fs::write(&private, bytes).expect("corrupt the private part");

    let serial = check_source_with("1", &fixture("siblings"), Some(&search));
    let parallel = check_source_with("3", &fixture("siblings"), Some(&search));
    std::fs::remove_dir_all(&search).expect("remove the copied search path");
    assert_eq!(serial.0, Some(1), "{serial:?}");
    assert!(serial.1.is_empty(), "{serial:?}");
    assert!(serial.2.contains("Init.Coe"), "{serial:?}");
    assert_eq!(parallel, serial);
}

#[test]
fn jobs_takes_one_positive_count() {
    let entry = fixture("prelude");
    for (arguments, message) in [
        (vec!["--jobs", "0"], "--jobs takes a positive thread count"),
        (
            vec!["--jobs", "two"],
            "--jobs takes a positive thread count",
        ),
        (vec!["--jobs=-1"], "--jobs takes a positive thread count"),
        (vec!["--jobs"], "--jobs requires a following thread count"),
        (
            vec!["--jobs=2", "--jobs", "3"],
            "--jobs may be supplied at most once",
        ),
    ] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_fln"));
        command.arg("check-source").args(&arguments);
        if arguments != ["--jobs"] {
            command.arg(&entry);
        }
        let output = command.output().expect("run fln check-source");
        let stderr = String::from_utf8(output.stderr).expect("utf8 stderr");
        assert_eq!(output.status.code(), Some(2), "{arguments:?}: {stderr}");
        assert!(stderr.contains(message), "{arguments:?}: {stderr}");
    }
}
