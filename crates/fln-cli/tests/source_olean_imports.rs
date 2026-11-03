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
            "\"declarationLogicalRoot\":\"ce452c45bc263fe4d5abad6ead8952db93611e364e5930f884860c9f96ced44b\""
        ),
        "{stdout}"
    );
    assert!(
        stdout.contains(
            "\"oleanImports\":{\"trust\":\"recheck\",\"admission\":\"council\",\"reusedModules\":0,\"councilModules\":1,\"modules\":1,\"declarations\":2314}"
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
            "\"oleanImports\":{\"trust\":\"recheck\",\"admission\":\"council\",\"reusedModules\":0,\"councilModules\":7,\"modules\":7,"
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

/// The pin's relation notations beyond `<`/`<=`/`=`/`==` (`Init/Notation.lean:370-392`,
/// `Init/Core.lean:775-880`): `>`, `≥`, `>=`, `≤`, `≠` and `!=` are `binrel%` /
/// `binrel_no_prop%` over `GT.gt`, `GE.ge`, `LE.le`, `Ne` and `bne`; `&&` and `||` are
/// plain applications of `Bool.and` / `Bool.or`. The fixture is accepted by the pinned
/// Reference as written. A false relation is still refused.
#[test]
fn relation_and_boolean_notations_elaborate_over_the_real_core() {
    if std::env::var_os("LEAN_PATH").is_some() || !pinned_prelude_present() {
        eprintln!("SKIP: pinned Reference lib/lean absent or LEAN_PATH overrides it");
        return;
    }
    let (code, stdout, stderr) = check_source("core_relations");
    assert_eq!(code, 0, "stdout: {stdout}\nstderr: {stderr}");
    assert!(stdout.contains("\"theorems\":9"), "{stdout}");

    let scratch = std::env::temp_dir().join(format!("fln-relations-{}", std::process::id()));
    std::fs::create_dir_all(&scratch).unwrap();
    let wrong = scratch.join("Main.lean");
    std::fs::write(
        &wrong,
        "prelude\nimport Init.Core\ntheorem bad : 2 > 3 := by decide\n",
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json", "--import-posture", "recheck"])
        .arg(&wrong)
        .output()
        .expect("run fln check-source");
    let _ = std::fs::remove_dir_all(&scratch);
    assert!(!output.status.success(), "{output:?}");
    assert!(output.stdout.is_empty(), "{output:?}");
}

/// `∃ binders, body` is the pin's macro (`Init/NotationExtra.lean`): one
/// `Exists fun x : T => …` per bound name. `⟨a, b, c⟩` against a constructor with fewer
/// explicit fields nests the extra arguments into the last one, as `elabAnonymousCtor`
/// does. The fixture is accepted by the pinned Reference as written.
///
/// On demand (the `Init.NotationExtra` closure is 51 modules, about a minute in release):
///
/// ```text
/// FLN_REQUIRE_REFERENCE=1 cargo test --release -p fln-cli --test source_olean_imports \
///     -- --ignored --exact existential_notation_and_nested_anonymous_constructors
/// ```
#[test]
#[ignore = "on-demand: council of the 51-module Init.NotationExtra closure"]
fn existential_notation_and_nested_anonymous_constructors() {
    if std::env::var_os("LEAN_PATH").is_some() || !pinned_prelude_present() {
        eprintln!("SKIP: pinned Reference lib/lean absent or LEAN_PATH overrides it");
        return;
    }
    let (code, stdout, stderr) = check_source("notation_exists");
    assert_eq!(code, 0, "stdout: {stdout}\nstderr: {stderr}");
    assert!(stdout.contains("\"commands\":4"), "{stdout}");
    assert!(stdout.contains("\"theorems\":3"), "{stdout}");
}

/// Over the real `Init.Prelude`, which declares ten axioms of its own (`Classical.choice`,
/// `sorryAx`, eight `unsafe` ones), the report counts only the file's one. A value-less
/// `opaque` is `default` where its type is `Inhabited`; where it is only `Nonempty` the pin
/// refuses it at the `opaque` ("failed to compile definition … depends on
/// 'Classical.ofNonempty'", exit 1, measured 2026-10-11), and so does this checker. The two
/// fixtures differ only in that instance.
#[test]
fn an_opaque_needs_an_inhabited_type_and_only_the_files_axioms_are_counted() {
    if std::env::var_os("LEAN_PATH").is_some() || !pinned_prelude_present() {
        eprintln!("SKIP: pinned Reference lib/lean absent or LEAN_PATH overrides it");
        return;
    }
    let (code, stdout, stderr) = check_source("opaque_inhabited");
    assert_eq!(code, 0, "stdout: {stdout}\nstderr: {stderr}");
    for expected in ["\"commands\":6", "\"theorems\":1", "\"axioms\":1,"] {
        assert!(stdout.contains(expected), "{stdout}");
    }
    // A refusal is reported on stderr, and names the `opaque` (command 2).
    let (code, stdout, stderr) = check_source("opaque_nonempty");
    assert_eq!(code, 1, "stdout: {stdout}\nstderr: {stderr}");
    assert!(stdout.is_empty(), "{stdout}");
    assert!(stderr.contains("\"outcome\":\"elaboration\""), "{stderr}");
    assert!(stderr.contains("command 2,"), "{stderr}");
}

#[test]
fn imported_macro_options_are_explicit_and_unambiguous() {
    let entry = fixture("prelude");
    for (arguments, message) in [
        (
            vec!["--macro-max-bytes", "1"],
            "--macro-max-bytes requires --imported-macros",
        ),
        (
            vec!["--imported-macros="],
            "--imported-macros requires a census path",
        ),
        (
            vec!["--imported-macros", "a.tsv", "--imported-macros=b.tsv"],
            "--imported-macros may be supplied at most once",
        ),
        (
            vec![
                "--imported-macros",
                "a.tsv",
                "--macro-max-bytes=1",
                "--macro-max-bytes",
                "2",
            ],
            "--macro-max-bytes may be supplied at most once",
        ),
        (
            vec!["--imported-macros", "a.tsv", "--macro-max-bytes=-1"],
            "--macro-max-bytes requires a non-negative byte count",
        ),
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_fln"))
            .arg("check-source")
            .args(arguments)
            .arg(&entry)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(2), "{output:?}");
        assert!(output.stdout.is_empty(), "{output:?}");
        assert!(
            String::from_utf8_lossy(&output.stderr).contains(message),
            "{output:?}"
        );
    }
    for option in ["--imported-macros", "--macro-max-bytes"] {
        let output = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", option])
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(2), "{output:?}");
        assert!(
            String::from_utf8_lossy(&output.stderr).contains("requires a following value"),
            "{output:?}"
        );
    }
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--imported-macros", "a.tsv"])
        .arg(&entry)
        .arg(&entry)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2), "{output:?}");
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("exactly one source entry"),
        "{output:?}"
    );
}

#[test]
fn imported_macro_mode_requires_an_admitted_artifact_receipt() {
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "fln-cli-macro-no-receipt-{}-{unique}",
        std::process::id()
    ));
    std::fs::create_dir_all(&root).unwrap();
    let entry = root.join("Main.lean");
    std::fs::write(&entry, "prelude\naxiom Token : Type\n").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json", "--imported-macros"])
        .arg(root.join("not-read.tsv"))
        .arg(&entry)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert!(output.stdout.is_empty(), "{output:?}");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("external .olean import"), "{stderr}");
    assert!(stderr.contains("\"authority\":false"), "{stderr}");
}

fn macro_check(
    entry: &std::path::Path,
    search: &std::ffi::OsStr,
    partition: &std::path::Path,
    cache: &std::path::Path,
    bytes: Option<usize>,
) -> std::process::Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_fln"));
    command
        .args([
            "check-source",
            "--json",
            "--jobs",
            "1",
            "--import-posture",
            "reuse-verified",
            "--imported-macros",
        ])
        .arg(partition)
        .env("LEAN_PATH", search)
        .env("FLN_IMPORT_REUSE_DIR", cache);
    if let Some(bytes) = bytes {
        command.arg(format!("--macro-max-bytes={bytes}"));
    }
    command.arg(entry).output().unwrap()
}

fn compile_macro_provider(
    reference: &std::path::Path,
    directory: &std::path::Path,
    source: &str,
) {
    std::fs::create_dir_all(directory).unwrap();
    std::fs::write(directory.join("AdmittedSourceMacro.lean"), source).unwrap();
    let output = Command::new(reference)
        .current_dir(directory)
        .args([
            "-o",
            "AdmittedSourceMacro.olean",
            "AdmittedSourceMacro.lean",
        ])
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}; {directory:?}");
}

#[test]
fn imported_macro_checking_runs_the_real_companion_and_keeps_admission_authority() {
    let reference = std::env::var_os("FLN_REFERENCE_LEAN").map(PathBuf::from);
    let library = std::env::var_os("FLN_REFERENCE_LIB").map(PathBuf::from);
    let partition = std::env::var_os("FLN_REFERENCE_PARTITION").map(PathBuf::from);
    let (Some(reference), Some(library), Some(partition)) = (reference, library, partition) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "imported macro CLI checking requires the pinned executable, library and partition"
        );
        eprintln!("SKIP: set FLN_REFERENCE_LEAN, FLN_REFERENCE_LIB and FLN_REFERENCE_PARTITION");
        return;
    };
    let version = Command::new(&reference).arg("--githash").output().unwrap();
    assert!(version.status.success(), "{version:?}");
    assert_eq!(
        String::from_utf8(version.stdout).unwrap().trim(),
        fln_olean::format::PIN_COMMIT
    );
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "fln-cli-imported-macros-{}-{unique}",
        std::process::id()
    ));
    let provider = root.join("provider");
    let client = root.join("client");
    let cache = root.join("reuse");
    std::fs::create_dir_all(&client).unwrap();
    compile_macro_provider(
        &reference,
        &provider,
        include_str!("../../fln-olean/fixtures/ir/AdmittedSourceMacro.lean"),
    );
    // Keep the client outside the provider: local sources take precedence over
    // LEAN_PATH, so co-location would never exercise imported macro artifacts.
    let search = std::env::join_paths([&provider, &library]).unwrap();
    let entry = client.join("Main.lean");
    let source = concat!(
        "prelude\nimport AdmittedSourceMacro\n",
        "def expanded : Nat := (11 : Bool)\n",
        "theorem expanded_eq : Eq expanded 11 := Eq.refl expanded\n",
    );
    std::fs::write(&entry, source).unwrap();
    let oracle = Command::new(&reference)
        .env("LEAN_PATH", &search)
        .arg(&entry)
        .output()
        .unwrap();
    assert!(oracle.status.success(), "{oracle:?}; {root:?}");
    let accepted = macro_check(&entry, &search, &partition, &cache, None);
    assert_eq!(accepted.status.code(), Some(0), "{accepted:?}; {root:?}");
    assert!(accepted.stderr.is_empty(), "{accepted:?}");
    let stdout = String::from_utf8(accepted.stdout).unwrap();
    assert!(stdout.contains("\"theorems\":1"), "{stdout}");
    assert!(stdout.contains("\"executed\":true"), "{stdout}");
    assert!(
        stdout.contains("\"importedMacros\":{\"producer\":\"reference\",\"attempts\":"),
        "{stdout}"
    );
    assert!(!stdout.contains("\"vmSteps\":0,"), "{stdout}");

    let ordinary = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .env("LEAN_PATH", &search)
        .env("FLN_IMPORT_REUSE_DIR", &cache)
        .arg(&entry)
        .output()
        .unwrap();
    assert_eq!(ordinary.status.code(), Some(1), "{ordinary:?}");
    assert!(ordinary.stdout.is_empty(), "{ordinary:?}");

    let bad = client.join("Bad.lean");
    std::fs::write(
        &bad,
        concat!(
            "prelude\nimport AdmittedSourceMacro\n",
            "theorem bad : Eq (11 : Bool) 12 := Eq.refl 11\n",
        ),
    )
    .unwrap();
    let rejected_oracle = Command::new(&reference)
        .env("LEAN_PATH", &search)
        .arg(&bad)
        .output()
        .unwrap();
    assert!(!rejected_oracle.status.success(), "{rejected_oracle:?}");
    let rejected = macro_check(&bad, &search, &partition, &cache, None);
    assert_eq!(rejected.status.code(), Some(1), "{rejected:?}");
    assert!(rejected.stdout.is_empty(), "{rejected:?}");
    assert!(!rejected.stderr.is_empty(), "{rejected:?}");

    let zero = macro_check(&entry, &search, &partition, &cache, Some(0));
    assert_eq!(zero.status.code(), Some(3), "{zero:?}");
    assert!(zero.stdout.is_empty(), "{zero:?}");
    assert!(
        String::from_utf8_lossy(&zero.stderr).contains("resource"),
        "{zero:?}"
    );

    let corrupt_partition = root.join("corrupt-partition.tsv");
    let mut policy = std::fs::read(&partition).unwrap();
    policy.extend_from_slice(b"\n");
    std::fs::write(&corrupt_partition, policy).unwrap();
    let corrupt = macro_check(&entry, &search, &corrupt_partition, &cache, None);
    assert_eq!(corrupt.status.code(), Some(1), "{corrupt:?}");
    assert!(corrupt.stdout.is_empty(), "{corrupt:?}");
    assert!(
        String::from_utf8_lossy(&corrupt.stderr).contains("policy-refusal"),
        "{corrupt:?}"
    );

    // A later root has the right IR, but it cannot supply a companion for the
    // .olean selected from the first root. A corrupt first companion is final too.
    let shadow = root.join("shadow");
    std::fs::create_dir_all(&shadow).unwrap();
    for suffix in ["olean", "olean.server", "olean.private"] {
        let relative = format!("AdmittedSourceMacro.{suffix}");
        std::fs::copy(provider.join(&relative), shadow.join(relative)).unwrap();
    }
    let shadow_search = std::env::join_paths([&shadow, &provider, &library]).unwrap();
    let missing = macro_check(&entry, &shadow_search, &partition, &cache, None);
    assert_eq!(missing.status.code(), Some(5), "{missing:?}");
    assert!(
        String::from_utf8_lossy(&missing.stderr).contains("\"outcome\":\"capability\"")
            && String::from_utf8_lossy(&missing.stderr).contains("\"authority\":false"),
        "{missing:?}"
    );
    assert!(missing.stdout.is_empty(), "{missing:?}");
    assert!(
        String::from_utf8_lossy(&missing.stderr).contains("admittedChooseTerm"),
        "{missing:?}"
    );
    std::fs::write(shadow.join("AdmittedSourceMacro.ir"), b"invalid IR").unwrap();
    let corrupt = macro_check(&entry, &shadow_search, &partition, &cache, None);
    assert_eq!(corrupt.status.code(), Some(1), "{corrupt:?}");
    assert!(corrupt.stdout.is_empty(), "{corrupt:?}");
    assert!(
        String::from_utf8_lossy(&corrupt.stderr).contains("\"outcome\":\"codec\""),
        "{corrupt:?}"
    );

    #[cfg(unix)]
    {
        let redirected = root.join("redirected");
        std::fs::create_dir_all(&redirected).unwrap();
        for suffix in ["olean", "olean.server", "olean.private"] {
            let relative = format!("AdmittedSourceMacro.{suffix}");
            std::fs::copy(provider.join(&relative), redirected.join(relative)).unwrap();
        }
        std::os::unix::fs::symlink(
            provider.join("AdmittedSourceMacro.ir"),
            redirected.join("AdmittedSourceMacro.ir"),
        )
        .unwrap();
        let redirected_search = std::env::join_paths([&redirected, &library]).unwrap();
        let refused = macro_check(&entry, &redirected_search, &partition, &cache, None);
        assert_eq!(refused.status.code(), Some(1), "{refused:?}");
        assert!(refused.stdout.is_empty(), "{refused:?}");
        assert!(
            String::from_utf8_lossy(&refused.stderr)
                .contains("not a regular imported-macro IR file"),
            "{refused:?}"
        );
    }

    // A valid replacement IR defines the registered macro but calls a helper
    // absent from the selected checked module. Unclassified IR is never
    // automatically authorized just because its file has a familiar stem.
    let foreign = root.join("foreign");
    compile_macro_provider(
        &reference,
        &foreign,
        concat!(
            "module\nprelude\npublic import Init.Prelude\n",
            "public meta import Init.Prelude\nopen Lean\n",
            "@[noinline] public meta def unownedMacroHelper (stx : Syntax) : Syntax := stx.getArg 1\n",
            "@[macro Lean.Parser.Term.typeAscription]\n",
            "public meta def admittedChooseTerm : Macro := fun stx _ state =>\n",
            "  .ok (unownedMacroHelper stx) state\n",
        ),
    );
    std::fs::copy(
        foreign.join("AdmittedSourceMacro.ir"),
        shadow.join("AdmittedSourceMacro.ir"),
    )
    .unwrap();
    let unowned = macro_check(&entry, &shadow_search, &partition, &cache, None);
    assert_eq!(unowned.status.code(), Some(5), "{unowned:?}");
    assert!(
        String::from_utf8_lossy(&unowned.stderr).contains("\"outcome\":\"capability\"")
            && String::from_utf8_lossy(&unowned.stderr).contains("\"authority\":false"),
        "{unowned:?}"
    );
    assert!(unowned.stdout.is_empty(), "{unowned:?}");
    assert!(
        String::from_utf8_lossy(&unowned.stderr).contains("unownedMacroHelper"),
        "{unowned:?}"
    );

    // Enabling the mode is different from actually running a macro.
    let plain = client.join("Plain.lean");
    std::fs::write(
        &plain,
        "prelude\nimport Init.Prelude\ntheorem plain : Eq Nat Nat := Eq.refl Nat\n",
    )
    .unwrap();
    let idle = macro_check(&plain, &search, &partition, &cache, None);
    assert_eq!(idle.status.code(), Some(0), "{idle:?}");
    let stdout = String::from_utf8(idle.stdout).unwrap();
    assert!(stdout.contains("\"executed\":false"), "{stdout}");
    assert!(stdout.contains("\"attempts\":0,"), "{stdout}");
    assert!(stdout.contains("\"vmSteps\":0,"), "{stdout}");

    // A complete registration table can contain macros whose runtime support
    // is not needed by this program. Compile bodies only when dispatch selects
    // them, then preserve the existing typed refusal if the body is demanded.
    let dormant = root.join("dormant");
    let dormant_source = format!(
        "{}\n{}",
        include_str!("../../fln-olean/fixtures/ir/AdmittedSourceMacro.lean"),
        concat!(
            "@[extern \"fln_missing_macro_native\", noinline]\n",
            "public meta def absentMacroPrimitive (stx : Syntax) : Syntax := stx\n",
            "@[macro Lean.Parser.Term.hole]\n",
            "public meta def dormantMacro : Macro := fun stx _ state =>\n",
            "  .ok (absentMacroPrimitive stx) state\n",
        )
    );
    compile_macro_provider(&reference, &dormant, &dormant_source);
    let dormant_search = std::env::join_paths([&dormant, &library]).unwrap();
    let unused = macro_check(&entry, &dormant_search, &partition, &cache, None);
    assert_eq!(unused.status.code(), Some(0), "{unused:?}");
    let stdout = String::from_utf8_lossy(&unused.stdout);
    assert!(stdout.contains("\"executed\":true"), "{stdout}");
    assert!(stdout.contains("\"theorems\":1"), "{stdout}");
    let demanded = client.join("Demanded.lean");
    std::fs::write(
        &demanded,
        concat!(
            "prelude\nimport AdmittedSourceMacro\n",
            "def checkedPrefix : Nat := (11 : Bool)\n",
            "def demanded : Nat := _\n",
        ),
    )
    .unwrap();
    let refused = macro_check(&demanded, &dormant_search, &partition, &cache, None);
    assert_eq!(refused.status.code(), Some(5), "{refused:?}");
    assert!(refused.stdout.is_empty(), "{refused:?}");
    let stderr = String::from_utf8_lossy(&refused.stderr);
    assert!(stderr.contains("\"outcome\":\"capability\""), "{stderr}");
    assert!(stderr.contains("\"authority\":false"), "{stderr}");
    assert!(stderr.contains("absentMacroPrimitive"), "{stderr}");
}

/// An actual pinned compiler produces the macro code and its checked owner;
/// the installed native commands receive only the resulting artifact closure.
struct ImportedMacroProject {
    root: PathBuf,
    reference: PathBuf,
    library: PathBuf,
    partition: PathBuf,
}

impl ImportedMacroProject {
    fn prepare() -> Option<Self> {
        let explicit_partition = std::env::var_os("FLN_REFERENCE_PARTITION")
            .or_else(|| std::env::var_os("FLN_BUILTIN_PARTITION"));
        let partition = explicit_partition
            .clone()
            .map(PathBuf::from)
            .unwrap_or_else(|| {
                fln_core::checked_workspace_root!().join("contracts/builtin_partition.tsv")
            });
        if !partition.is_file() {
            assert!(
                explicit_partition.is_none()
                    && std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                "the configured macro execution partition is absent: {}",
                partition.display()
            );
            eprintln!(
                "SKIP imported macro commands: materialize the pinned partition at {}",
                partition.display()
            );
            return None;
        }
        let library = std::env::var_os("FLN_REFERENCE_LIB")
            .map(PathBuf::from)
            .or_else(|| {
                std::env::var_os("HOME").map(|home| {
                    PathBuf::from(home)
                        .join(".elan/toolchains")
                        .join(format!("leanprover--lean4---{}", fln::OLEAN_PIN_TAG))
                        .join("lib/lean")
                })
            })
            .filter(|path| path.join("Init/Prelude.olean").is_file());
        let reference = std::env::var_os("FLN_REFERENCE_LEAN")
            .map(PathBuf::from)
            .or_else(|| {
                library.as_ref()?.parent()?.parent().map(|root| {
                    root.join("bin")
                        .join(format!("lean{}", std::env::consts::EXE_SUFFIX))
                })
            })
            .filter(|path| path.is_file());
        let (Some(reference), Some(library)) = (reference, library) else {
            assert!(
                std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                "the installed macro test requires the pinned executable and Prelude artifacts"
            );
            eprintln!("SKIP imported macro commands: the pinned Reference is absent");
            return None;
        };
        let version = Command::new(&reference).arg("--githash").output().unwrap();
        assert!(version.status.success(), "{version:?}");
        assert_eq!(
            String::from_utf8(version.stdout).unwrap().trim(),
            fln::OLEAN_PIN_COMMIT
        );
        fln::imported_ir::VerifiedPartition::from_pinned_tsv(
            &std::fs::read_to_string(&partition).unwrap(),
        )
        .unwrap();

        let stamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let root = std::env::temp_dir().join(format!(
            "fln-installed-source-macros-{}-{stamp}",
            std::process::id()
        ));
        std::fs::create_dir(&root).unwrap();
        std::fs::create_dir(root.join("objects")).unwrap();
        std::fs::create_dir(root.join("client")).unwrap();
        std::fs::write(
            root.join("objects/AdmittedSourceMacro.lean"),
            include_str!("../../fln-olean/fixtures/ir/AdmittedSourceMacro.lean"),
        )
        .unwrap();
        let compiled = Command::new(&reference)
            .current_dir(root.join("objects"))
            .env("LEAN_PATH", &library)
            .args(["-o", "AdmittedSourceMacro.olean", "AdmittedSourceMacro.lean"])
            .output()
            .unwrap();
        assert!(compiled.status.success(), "{compiled:?}; {root:?}");
        assert_eq!(compiled.stdout, b"Nat : Type\nadmittedMacroValue : Nat\n");
        assert!(compiled.stderr.is_empty(), "{compiled:?}");
        assert!(root.join("objects/AdmittedSourceMacro.ir").is_file());
        Some(Self {
            root,
            reference,
            library,
            partition,
        })
    }

    fn source(&self, source: &str) -> PathBuf {
        let path = self.root.join("client/Main.lean");
        std::fs::write(&path, source).unwrap();
        path
    }

    fn search_path(&self) -> std::ffi::OsString {
        std::env::join_paths([self.root.join("objects"), self.library.clone()]).unwrap()
    }

    fn oracle(&self, source: &str) -> std::process::Output {
        Command::new(&self.reference)
            .arg(self.source(source))
            .current_dir(self.root.join("client"))
            .env("LEAN_PATH", self.search_path())
            .output()
            .unwrap()
    }

    fn native(
        &self,
        verb: &str,
        source: &str,
        partition: Option<&std::path::Path>,
    ) -> std::process::Output {
        let mut command = if verb == "lean" {
            Command::new(env!("CARGO_BIN_EXE_lean"))
        } else {
            let mut command = Command::new(env!("CARGO_BIN_EXE_fln"));
            command.args([verb, "--json", "--jobs", "1", "--import-posture", "recheck"]);
            command
        };
        command
            .arg(self.source(source))
            .current_dir(self.root.join("client"))
            .env("LEAN_PATH", self.search_path())
            .env("FLN_IMPORT_REUSE_DIR", self.root.join("records"))
            .env_remove("FLN_MACRO_PARTITION");
        if let Some(partition) = partition {
            if verb == "check-source" {
                command.arg("--imported-macros").arg(partition);
            } else {
                command.env("FLN_MACRO_PARTITION", partition);
            }
        }
        command.output().unwrap()
    }

    fn check(&self, source: &str) -> String {
        let output = self.native("check-source", source, Some(&self.partition));
        assert!(output.status.success(), "{output:?}; {:?}", self.root);
        assert!(output.stderr.is_empty(), "{output:?}");
        let stdout = String::from_utf8(output.stdout).unwrap();
        assert!(stdout.contains("\"outcome\":\"complete\""), "{stdout}");
        assert_eq!(stdout.lines().count(), 1, "{stdout}");
        assert_imported_macro_provenance(&stdout);
        stdout
    }

    fn refused(output: std::process::Output) -> String {
        assert!(!output.status.success(), "{output:?}");
        assert!(output.stdout.is_empty(), "partial success escaped: {output:?}");
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert!(!stderr.is_empty());
        assert!(!stderr.contains("\"outcome\":\"complete\""), "{stderr}");
        stderr
    }
}

fn assert_imported_macro_provenance(report: &str) {
    let (_, macros) = report
        .split_once("\"importedMacros\":{")
        .expect("an imported macro result must retain its execution provenance");
    assert!(macros.starts_with("\"producer\":\"reference\","), "{report}");
    for field in ["attempts", "vmSteps"] {
        let key = format!("\"{field}\":");
        let (_, value) = macros.split_once(&key).unwrap();
        let (value, _) = value.split_once(',').unwrap();
        let value: u64 = value.parse().unwrap();
        assert!(value > 0, "macro {field} must record actual work: {report}");
    }
    let (_, reference) = macros.split_once("\"linkedReferenceFunctions\":[").unwrap();
    let (reference, _) = reference.split_once(']').unwrap();
    assert!(
        reference.contains("{\"name\":\"admittedChooseTerm\",\"producer\":\"reference\"}"),
        "{report}"
    );
    let (_, native) = macros.split_once("\"linkedNativeFunctions\":[").unwrap();
    let (native, _) = native.split_once(']').unwrap();
    // These are the three methods called by the real fixture's macro body.
    // The report is a linked-closure inventory, not a per-function call trace.
    for method in [
        "mirror:Lean.Macro.resolveNamespace",
        "mirror:Lean.Macro.resolveGlobalName",
        "mirror:Lean.Macro.addMacroScope",
    ] {
        assert!(native.contains(&format!("\"{method}\"")), "{report}");
    }
}

fn assert_macro_refusal(output: std::process::Output, exit: i32, class: &str, detail: &str) {
    assert_eq!(output.status.code(), Some(exit), "{output:?}");
    let error = ImportedMacroProject::refused(output);
    assert!(error.contains(&format!("\"outcome\":\"{class}\"")), "{error}");
    assert!(error.contains("\"authority\":false"), "{error}");
    assert!(error.contains(detail), "{error}");
}

const IMPORTED_MACRO_CLIENT: &str = concat!(
    "prelude\n",
    "import AdmittedSourceMacro\n",
    "def commandMacroValue : Nat := (11 : Bool)\n",
    "theorem commandMacroValue_eq : Eq commandMacroValue 11 := Eq.refl commandMacroValue\n",
    "#check (Nat : Bool)\n",
    "#check commandMacroValue\n",
);

#[test]
fn installed_imported_macros_drive_checked_source_and_runtime_commands() {
    let Some(project) = ImportedMacroProject::prepare() else {
        return;
    };
    // The client has no macro implementation source beside it. The changed
    // meaning of type ascription therefore requires executing the imported IR.
    assert!(!project.root.join("client/AdmittedSourceMacro.lean").exists());
    let oracle = project.oracle(IMPORTED_MACRO_CLIENT);
    assert!(oracle.status.success(), "{oracle:?}");
    assert_eq!(oracle.stdout, b"Nat : Type\ncommandMacroValue : Nat\n");
    assert!(oracle.stderr.is_empty(), "{oracle:?}");
    let accepted = project.check(IMPORTED_MACRO_CLIENT);
    assert!(accepted.contains("\"theorems\":1"), "{accepted}");

    let lean = project.native("lean", IMPORTED_MACRO_CLIENT, Some(&project.partition));
    assert!(lean.status.success(), "{lean:?}");
    assert_eq!(lean.stdout, oracle.stdout);
    assert!(lean.stderr.is_empty(), "{lean:?}");

    // fln run exposes its documented raw Nat projection without needing Repr
    // from a larger Init closure. The preceding checked theorem pins its value.
    let executable = format!("{IMPORTED_MACRO_CLIENT}#eval commandMacroValue\n");
    let run = project.native("run", &executable, Some(&project.partition));
    assert!(run.status.success(), "{run:?}");
    assert!(run.stderr.is_empty(), "{run:?}");
    let stdout = String::from_utf8(run.stdout).unwrap();
    assert!(
        stdout.contains("\"schema\":\"fln.source-program/1\""),
        "{stdout}"
    );
    assert!(stdout.contains("\"outcome\":\"complete\""), "{stdout}");
    assert!(stdout.contains("\"kind\":\"nat\",\"value\":11"), "{stdout}");
    assert_eq!(stdout.matches("\"event\":\"check\"").count(), 2, "{stdout}");
    assert_imported_macro_provenance(&stdout);

    // A source sidecar currently binds source and olean inputs, but not the
    // imported executable macro IR. Refuse it before publishing either file.
    let flbc = project.root.join("macro.flbc");
    let sidecar = project.root.join("macro.sidecar");
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["run", "--json", "--jobs", "1", "--import-posture", "recheck"])
        .arg("--emit-flbc")
        .arg(&flbc)
        .arg("--emit-sidecar")
        .arg(&sidecar)
        .arg(project.source(&executable))
        .current_dir(project.root.join("client"))
        .env("LEAN_PATH", project.search_path())
        .env("FLN_MACRO_PARTITION", &project.partition)
        .output()
        .unwrap();
    assert_macro_refusal(
        output,
        5,
        "capability",
        "source-closure sidecars do not yet bind imported macro IR",
    );
    assert!(!flbc.exists(), "a refused sidecar published executable bytes");
    assert!(!sidecar.exists(), "a refused sidecar published a manifest");

    // Opt-in is not permission to accept a bad expansion result or false proof.
    for source in [
        "prelude\nimport AdmittedSourceMacro\ndef badMacroValue : Bool := (11 : Bool)\n",
        concat!(
            "prelude\nimport AdmittedSourceMacro\n",
            "def commandMacroValue : Nat := (11 : Bool)\n",
            "theorem wrong : Eq commandMacroValue 18 := Eq.refl commandMacroValue\n",
        ),
    ] {
        let oracle = project.oracle(source);
        assert!(!oracle.status.success(), "{oracle:?}");
        for verb in ["check-source", "run", "lean"] {
            ImportedMacroProject::refused(project.native(verb, source, Some(&project.partition)));
        }
        assert_eq!(project.check(IMPORTED_MACRO_CLIENT), accepted);
    }

    // Without explicit policy the original frontend remains in use; the
    // otherwise ill-typed ascription must not silently acquire macro semantics.
    ImportedMacroProject::refused(project.native("check-source", IMPORTED_MACRO_CLIENT, None));
    let ordinary = concat!(
        "prelude\nimport Init.Prelude\n",
        "def ordinaryValue : Nat := 11\n",
        "theorem ordinaryValue_eq : Eq ordinaryValue 11 := Eq.refl ordinaryValue\n",
    );
    let ordinary = project.native("check-source", ordinary, None);
    assert!(ordinary.status.success(), "{ordinary:?}");
    assert!(ordinary.stderr.is_empty(), "{ordinary:?}");

    let ir = project.root.join("objects/AdmittedSourceMacro.ir");
    let original_ir = std::fs::read(&ir).unwrap();
    let olean = project.root.join("objects/AdmittedSourceMacro.olean");
    let original_olean = std::fs::read(&olean).unwrap();
    let retained_ir = project.root.join("objects/AdmittedSourceMacro.ir.saved");
    std::fs::rename(&ir, &retained_ir).unwrap();
    assert_macro_refusal(
        project.native("check-source", IMPORTED_MACRO_CLIENT, Some(&project.partition)),
        5,
        "capability",
        concat!(
            "registered macro admittedChooseTerm in AdmittedSourceMacro: ",
            "macro compilation: IR execution refuses unclassified declaration admittedChooseTerm",
        ),
    );
    std::fs::rename(&retained_ir, &ir).unwrap();
    assert_eq!(project.check(IMPORTED_MACRO_CLIENT), accepted);

    std::fs::write(&ir, b"not a Lean IR artifact").unwrap();
    assert_macro_refusal(
        project.native("check-source", IMPORTED_MACRO_CLIENT, Some(&project.partition)),
        1,
        "codec",
        "AdmittedSourceMacro.ir:",
    );
    std::fs::write(&ir, &original_ir).unwrap();
    assert_eq!(project.check(IMPORTED_MACRO_CLIENT), accepted);

    let wrong_partition = project.root.join("wrong-partition.tsv");
    std::fs::write(&wrong_partition, "constant_count\t0\n").unwrap();
    assert_macro_refusal(
        project.native("check-source", IMPORTED_MACRO_CLIENT, Some(&wrong_partition)),
        1,
        "policy-refusal",
        "IR execution requires the exact pinned census partition",
    );
    assert_eq!(project.check(IMPORTED_MACRO_CLIENT), accepted);
    assert_eq!(std::fs::read(&ir).unwrap(), original_ir);
    assert_eq!(std::fs::read(&olean).unwrap(), original_olean);
}
