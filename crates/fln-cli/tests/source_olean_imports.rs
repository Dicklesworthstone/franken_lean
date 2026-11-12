//! `fln check-source` resolves an import with no local source file to an
//! `.olean` on the search path and admits its closure through K1 and the
//! independent checker before checking the source (bead `franken_lean-z8j.1.8`).
#![forbid(unsafe_code)]

use std::path::PathBuf;
use std::process::Command;

#[path = "source_olean_imports/abbreviations.rs"]
mod abbreviations;
#[path = "source_olean_imports/tactics.rs"]
mod tactics;

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
            vec!["--imported-syntax", "User.Notation"],
            "--imported-syntax requires --imported-macros",
        ),
        (
            vec!["--imported-macros=a.tsv", "--imported-syntax="],
            "--imported-syntax: expected one imported module name",
        ),
        (
            vec!["--imported-macros=a.tsv", "--imported-syntax=A B"],
            "--imported-syntax: expected one imported module name",
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
    for option in [
        "--imported-macros",
        "--macro-max-bytes",
        "--imported-syntax",
    ] {
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

fn dormant_macro_provider_source() -> String {
    format!(
        "{}\n{}",
        include_str!("../../fln-olean/fixtures/ir/AdmittedSourceMacro.lean"),
        concat!(
            "@[extern \"fln_missing_macro_native\", noinline]\n",
            "public meta def absentMacroPrimitive (stx : Syntax) : Syntax := stx\n",
            "@[macro Lean.Parser.Term.hole]\n",
            "public meta def dormantMacro : Macro := fun stx _ state =>\n",
            "  .ok (absentMacroPrimitive stx) state\n",
        )
    )
}

fn compile_macro_provider(reference: &std::path::Path, directory: &std::path::Path, source: &str) {
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
    compile_macro_provider(&reference, &dormant, &dormant_macro_provider_source());
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
        Self::prepare_with_source(include_str!(
            "../../fln-olean/fixtures/ir/AdmittedSourceMacro.lean"
        ))
    }

    fn prepare_with_source(source: &str) -> Option<Self> {
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
                explicit_partition.is_none() && std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
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
        std::fs::write(root.join("objects/AdmittedSourceMacro.lean"), source).unwrap();
        let compiled = Command::new(&reference)
            .current_dir(root.join("objects"))
            .env("LEAN_PATH", &library)
            .args([
                "-o",
                "AdmittedSourceMacro.olean",
                "AdmittedSourceMacro.lean",
            ])
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

    fn lake(
        &self,
        targets: &[&str],
        macros: bool,
        syntax_modules: &[&str],
    ) -> std::process::Output {
        let mut command = Command::new(env!("CARGO_BIN_EXE_lake"));
        command
            .args(["--json", "build"])
            .args(targets)
            .current_dir(self.root.join("client"))
            .env("LEAN_PATH", self.search_path())
            .env("FLN_IMPORT_REUSE_DIR", self.root.join("records"))
            .env_remove("FLN_MACRO_PARTITION")
            .env_remove("FLN_SYNTAX_MODULES");
        if macros {
            command.env("FLN_MACRO_PARTITION", &self.partition);
        }
        if !syntax_modules.is_empty() {
            command.env("FLN_SYNTAX_MODULES", syntax_modules.join(","));
        }
        command.output().unwrap()
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
        self.native_with_syntax(verb, source, partition, &[])
    }

    fn native_with_syntax(
        &self,
        verb: &str,
        source: &str,
        partition: Option<&std::path::Path>,
        syntax_modules: &[&str],
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
            .env_remove("FLN_MACRO_PARTITION")
            .env_remove("FLN_SYNTAX_MODULES");
        if let Some(partition) = partition {
            if verb == "check-source" {
                command.arg("--imported-macros").arg(partition);
            } else {
                command.env("FLN_MACRO_PARTITION", partition);
            }
        }
        if verb == "check-source" {
            for module in syntax_modules {
                command.arg("--imported-syntax").arg(module);
            }
        } else if !syntax_modules.is_empty() {
            command.env("FLN_SYNTAX_MODULES", syntax_modules.join(","));
        }
        command.output().unwrap()
    }

    fn check(&self, source: &str) -> String {
        self.check_with_syntax(source, &[])
    }

    fn check_with_syntax(&self, source: &str, syntax_modules: &[&str]) -> String {
        let report = self.check_with_syntax_report(source, syntax_modules);
        assert_imported_macro_provenance(&report);
        report
    }

    fn check_with_syntax_report(&self, source: &str, syntax_modules: &[&str]) -> String {
        let output = self.native_with_syntax(
            "check-source",
            source,
            Some(&self.partition),
            syntax_modules,
        );
        assert!(output.status.success(), "{output:?}; {:?}", self.root);
        assert!(output.stderr.is_empty(), "{output:?}");
        let stdout = String::from_utf8(output.stdout).unwrap();
        assert!(stdout.contains("\"outcome\":\"complete\""), "{stdout}");
        assert!(stdout.contains("\"authority\":true"), "{stdout}");
        assert_eq!(stdout.lines().count(), 1, "{stdout}");
        stdout
    }

    fn refused(output: std::process::Output) -> String {
        assert!(!output.status.success(), "{output:?}");
        assert!(
            output.stdout.is_empty(),
            "partial success escaped: {output:?}"
        );
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert!(!stderr.is_empty());
        assert!(!stderr.contains("\"outcome\":\"complete\""), "{stderr}");
        stderr
    }
}

fn assert_imported_macro_execution(report: &str) -> &str {
    let (_, macros) = report
        .split_once("\"importedMacros\":{")
        .expect("an imported macro result must retain its execution provenance");
    assert!(
        macros.starts_with("\"producer\":\"reference\","),
        "{report}"
    );
    for field in ["attempts", "vmSteps"] {
        let key = format!("\"{field}\":");
        let (_, value) = macros.split_once(&key).unwrap();
        let (value, _) = value.split_once(',').unwrap();
        let value: u64 = value.parse().unwrap();
        assert!(value > 0, "macro {field} must record actual work: {report}");
    }
    macros
}

fn assert_imported_macro_provenance(report: &str) {
    let macros = assert_imported_macro_execution(report);
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
    assert!(
        error.contains(&format!("\"outcome\":\"{class}\"")),
        "{error}"
    );
    assert!(error.contains("\"authority\":false"), "{error}");
    assert!(error.contains(detail), "{error}");
}

fn assert_macro_program_refusal(
    output: std::process::Output,
    exit: i32,
    class: &str,
    authority: bool,
    detail: &str,
) {
    assert_eq!(output.status.code(), Some(exit), "{output:?}");
    let error = ImportedMacroProject::refused(output);
    assert!(
        error.contains("\"schema\":\"fln.source-program/1\""),
        "{error}"
    );
    assert!(error.contains("\"outcome\":\"error\""), "{error}");
    assert!(error.contains(&format!("\"class\":\"{class}\"")), "{error}");
    assert!(
        error.contains(&format!("\"authority\":{authority}")),
        "{error}"
    );
    assert!(error.contains(detail), "{error}");
}

// check-source accepts declarations and proofs; runtime personalities also
// process queries. Keep each test on its documented command surface.
const IMPORTED_MACRO_DECLARATIONS: &str = concat!(
    "prelude\n",
    "import AdmittedSourceMacro\n",
    "def commandMacroValue : Nat := (11 : Bool)\n",
    "theorem commandMacroValue_eq : Eq commandMacroValue 11 := Eq.refl commandMacroValue\n",
);

const IMPORTED_MACRO_CLIENT: &str = concat!(
    "prelude\n",
    "import AdmittedSourceMacro\n",
    "def commandMacroValue : Nat := (11 : Bool)\n",
    "theorem commandMacroValue_eq : Eq commandMacroValue 11 := Eq.refl commandMacroValue\n",
    "#check (Nat : Bool)\n",
    "#check commandMacroValue\n",
);

#[test]
fn installed_imported_syntax_drives_checking_and_runtime_with_scoped_isolation() {
    let provider = format!(
        "{}\n{}",
        include_str!("../../fln-olean/fixtures/ir/AdmittedSourceMacro.lean"),
        r#"
public section

syntax (name := admittedBoxTerm) "box%" term "end%" : term

@[macro admittedBoxTerm]
meta def admittedUnboxTerm : Macro := fun stx _ state =>
  .ok (stx.getArg 1) state

namespace ImportedBoxScope

scoped syntax (name := admittedScopedBoxTerm) "scopedBox%" term "end%" : term

@[scoped macro admittedScopedBoxTerm]
meta def admittedUnboxScopedTerm : Macro := fun stx _ state =>
  .ok (stx.getArg 1) state

end ImportedBoxScope
"#
    );
    let Some(project) = ImportedMacroProject::prepare_with_source(&provider) else {
        return;
    };
    let selected = ["AdmittedSourceMacro"];
    assert!(
        !project
            .root
            .join("client/AdmittedSourceMacro.lean")
            .exists()
    );
    let declarations = concat!(
        "prelude\nimport AdmittedSourceMacro\n",
        "def importedBoxValue : Nat := box% (11 : Bool) end%\n",
        "theorem importedBoxValue_eq : Eq importedBoxValue 11 := Eq.refl importedBoxValue\n",
        "section\nopen scoped ImportedBoxScope\n",
        "def scopedBoxValue : Nat := scopedBox% (13 : Bool) end%\n",
        "theorem scopedBoxValue_eq : Eq scopedBoxValue 13 := Eq.refl scopedBoxValue\n",
        "end\n",
    );
    let client = format!("{declarations}#check box% (Nat : Bool) end%\n#check importedBoxValue\n");
    let oracle = project.oracle(&client);
    assert!(oracle.status.success(), "{oracle:?}; {:?}", project.root);
    assert_eq!(oracle.stdout, b"Nat : Type\nimportedBoxValue : Nat\n");
    assert!(oracle.stderr.is_empty(), "{oracle:?}");
    let report = project.check_with_syntax(declarations, &selected);
    assert!(report.contains("\"theorems\":2"), "{report}");
    assert!(
        report.contains("\"name\":\"admittedUnboxTerm\""),
        "{report}"
    );
    assert!(
        report.contains("ImportedBoxScope.admittedUnboxScopedTerm"),
        "{report}"
    );

    let lean = project.native_with_syntax("lean", &client, Some(&project.partition), &selected);
    assert!(lean.status.success(), "{lean:?}; {:?}", project.root);
    assert_eq!(lean.stdout, oracle.stdout);
    assert!(lean.stderr.is_empty(), "{lean:?}");
    let run = project.native_with_syntax(
        "run",
        &format!("{client}#eval importedBoxValue\n#eval scopedBoxValue\n"),
        Some(&project.partition),
        &selected,
    );
    assert!(run.status.success(), "{run:?}; {:?}", project.root);
    assert!(run.stderr.is_empty(), "{run:?}");
    let report = String::from_utf8(run.stdout).unwrap();
    assert!(report.contains("\"outcome\":\"complete\""), "{report}");
    for value in [11, 13] {
        assert!(
            report.contains(&format!("\"kind\":\"nat\",\"value\":{value}")),
            "{report}"
        );
    }
    assert_imported_macro_provenance(&report);

    for invalid in [
        format!("{declarations}theorem bad : Eq importedBoxValue 19 := Eq.refl importedBoxValue\n"),
        format!("{declarations}def leakedScope : Nat := scopedBox% (17 : Bool) end%\n"),
    ] {
        ImportedMacroProject::refused(project.native_with_syntax(
            "check-source",
            &invalid,
            Some(&project.partition),
            &selected,
        ));
    }
    std::fs::write(
        project.root.join("client/Left.lean"),
        concat!(
            "prelude\nimport AdmittedSourceMacro\nopen scoped ImportedBoxScope\n",
            "def leftValue : Nat := scopedBox% (23 : Bool) end%\n",
        ),
    )
    .unwrap();
    let right = project.root.join("client/Right.lean");
    std::fs::write(
        &right,
        concat!(
            "prelude\nimport AdmittedSourceMacro\n",
            "def rightValue : Nat := scopedBox% (29 : Bool) end%\n",
        ),
    )
    .unwrap();
    let joined = "prelude\nimport Left\nimport Right\ndef joinedValue : Nat := leftValue\n";
    ImportedMacroProject::refused(project.native_with_syntax(
        "check-source",
        joined,
        Some(&project.partition),
        &selected,
    ));
    std::fs::write(
        &right,
        concat!(
            "prelude\nimport AdmittedSourceMacro\nopen scoped ImportedBoxScope\n",
            "def rightValue : Nat := scopedBox% (29 : Bool) end%\n",
        ),
    )
    .unwrap();
    let joined =
        project.native_with_syntax("check-source", joined, Some(&project.partition), &selected);
    assert!(joined.status.success(), "{joined:?}; {:?}", project.root);
    assert!(joined.stderr.is_empty(), "{joined:?}");
}

#[test]
fn installed_imported_command_syntax_admits_and_executes_real_artifact_expansions() {
    let selected = ["AdmittedSourceMacro"];
    let provider = format!(
        "{}\n{}",
        include_str!("../../fln-olean/fixtures/ir/AdmittedSourceMacro.lean"),
        r#"
public section

syntax (name := admittedDeclare) "declare%" "[" command "]" : command

@[macro admittedDeclare]
meta def admittedDeclareCommand : Macro := fun stx _ state =>
  .ok (stx.getArg 2) state

namespace ImportedCommandScope

scoped syntax (name := admittedScopedDeclare) "scopedDeclare%" "[" command "]" : command

@[scoped macro admittedScopedDeclare]
meta def admittedScopedDeclareCommand : Macro := fun stx _ state =>
  .ok (stx.getArg 2) state

end ImportedCommandScope
"#
    );
    let Some(project) = ImportedMacroProject::prepare_with_source(&provider) else {
        return;
    };
    assert!(
        !project
            .root
            .join("client/AdmittedSourceMacro.lean")
            .exists()
    );
    // The pinned compiler constructs the command descriptors and their macro
    // companions. The macro selects the parser's real command child; neither
    // the fixture nor the native runner manufactures a declaration layout.
    let declarations = concat!(
        "prelude\nimport AdmittedSourceMacro\n",
        "declare% [declare% [def importedCommandValue : Nat := (31 : Bool)]]\n",
        "declare% [theorem importedCommandValue_eq : Eq importedCommandValue 31 := Eq.refl importedCommandValue]\n",
        "section\nopen scoped ImportedCommandScope\n",
        "scopedDeclare% [def scopedCommandValue : Nat := (37 : Bool)]\n",
        "end\n",
    );
    let client = format!("{declarations}#check importedCommandValue\n#check scopedCommandValue\n");
    let oracle = project.oracle(&client);
    assert!(oracle.status.success(), "{oracle:?}; {:?}", project.root);
    assert_eq!(
        oracle.stdout,
        b"importedCommandValue : Nat\nscopedCommandValue : Nat\n"
    );
    assert!(oracle.stderr.is_empty(), "{oracle:?}");

    let accepted = project.check_with_syntax(declarations, &selected);
    assert!(accepted.contains("\"theorems\":1"), "{accepted}");
    for declaration in [
        "admittedDeclareCommand",
        "ImportedCommandScope.admittedScopedDeclareCommand",
    ] {
        assert!(
            accepted.contains(&format!("\"name\":\"{declaration}\"")),
            "{accepted}"
        );
    }

    let lean = project.native_with_syntax("lean", &client, Some(&project.partition), &selected);
    assert!(lean.status.success(), "{lean:?}; {:?}", project.root);
    assert_eq!(lean.stdout, oracle.stdout);
    assert!(lean.stderr.is_empty(), "{lean:?}");
    let run = project.native_with_syntax(
        "run",
        &format!("{client}#eval importedCommandValue\n#eval scopedCommandValue\n"),
        Some(&project.partition),
        &selected,
    );
    assert!(run.status.success(), "{run:?}; {:?}", project.root);
    assert!(run.stderr.is_empty(), "{run:?}");
    let report = String::from_utf8(run.stdout).unwrap();
    assert!(report.contains("\"outcome\":\"complete\""), "{report}");
    for value in [31, 37] {
        assert!(
            report.contains(&format!("\"kind\":\"nat\",\"value\":{value}")),
            "{report}"
        );
    }
    assert_imported_macro_provenance(&report);
    assert!(
        report.contains("\"name\":\"admittedDeclareCommand\""),
        "{report}"
    );

    let false_proof = concat!(
        "declare% [theorem wrongCommandProof : Eq importedCommandValue 99 := ",
        "Eq.refl importedCommandValue]\n",
    );
    let invalid = format!("{declarations}{false_proof}");
    let oracle = project.oracle(&invalid);
    assert!(!oracle.status.success(), "{oracle:?}");
    ImportedMacroProject::refused(project.native_with_syntax(
        "check-source",
        &invalid,
        Some(&project.partition),
        &selected,
    ));
    // Runtime queries before the bad generated theorem remain buffered. No
    // successful prefix may escape when its ordinary admission rejects it.
    ImportedMacroProject::refused(project.native_with_syntax(
        "run",
        &format!("{client}#eval importedCommandValue\n{false_proof}"),
        Some(&project.partition),
        &selected,
    ));

    let inactive =
        format!("{declarations}scopedDeclare% [def escapedCommandScope : Nat := (41 : Bool)]\n");
    let oracle = project.oracle(&inactive);
    assert!(!oracle.status.success(), "{oracle:?}");
    ImportedMacroProject::refused(project.native_with_syntax(
        "check-source",
        &inactive,
        Some(&project.partition),
        &selected,
    ));
    // Registering macro bodies alone does not activate their artifact grammar.
    for verb in ["check-source", "run", "lean"] {
        ImportedMacroProject::refused(project.native(verb, declarations, Some(&project.partition)));
    }
    assert_eq!(project.check_with_syntax(declarations, &selected), accepted);
}

#[test]
fn installed_imported_macros_drive_checked_source_and_runtime_commands() {
    let Some(project) = ImportedMacroProject::prepare() else {
        return;
    };
    // The client has no macro implementation source beside it. The changed
    // meaning of type ascription therefore requires executing the imported IR.
    assert!(
        !project
            .root
            .join("client/AdmittedSourceMacro.lean")
            .exists()
    );
    let oracle = project.oracle(IMPORTED_MACRO_CLIENT);
    assert!(oracle.status.success(), "{oracle:?}");
    assert_eq!(oracle.stdout, b"Nat : Type\ncommandMacroValue : Nat\n");
    assert!(oracle.stderr.is_empty(), "{oracle:?}");
    let accepted = project.check(IMPORTED_MACRO_DECLARATIONS);
    assert!(accepted.contains("\"theorems\":1"), "{accepted}");

    let lean = project.native("lean", IMPORTED_MACRO_CLIENT, Some(&project.partition));
    assert!(lean.status.success(), "{lean:?}");
    assert_eq!(lean.stdout, oracle.stdout);
    assert!(lean.stderr.is_empty(), "{lean:?}");

    // fln run exposes its documented raw Nat projection without needing Repr
    // from a larger Init closure. The preceding checked theorem pins its value.
    let executable = format!("{IMPORTED_MACRO_CLIENT}#eval commandMacroValue\n#eval (13 : Bool)\n");
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
    assert!(stdout.contains("\"kind\":\"nat\",\"value\":13"), "{stdout}");
    assert_eq!(
        stdout.matches("\"event\":\"evaluation\"").count(),
        2,
        "{stdout}"
    );
    assert_eq!(stdout.matches("\"event\":\"check\"").count(), 2, "{stdout}");
    assert_imported_macro_provenance(&stdout);

    // A source sidecar currently binds source and olean inputs, but not the
    // imported executable macro IR. Refuse it before publishing either file.
    let flbc = project.root.join("macro.flbc");
    let sidecar = project.root.join("macro.sidecar");
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args([
            "run",
            "--json",
            "--jobs",
            "1",
            "--import-posture",
            "recheck",
        ])
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
    assert_macro_program_refusal(
        output,
        5,
        "capability",
        false,
        "source-closure sidecars do not yet bind imported macro IR",
    );
    assert!(
        !flbc.exists(),
        "a refused sidecar published executable bytes"
    );
    assert!(!sidecar.exists(), "a refused sidecar published a manifest");

    // Raw FLBC retains the final evaluation after its imported macro expanded.
    // Replaying it needs neither the source frontend nor the macro policy.
    let product = project.root.join("macro-expanded.flbc");
    let emit = |source: &str| {
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args([
                "run",
                "--json",
                "--jobs",
                "1",
                "--import-posture",
                "recheck",
            ])
            .arg("--emit-flbc")
            .arg(&product)
            .arg(project.source(source))
            .current_dir(project.root.join("client"))
            .env("LEAN_PATH", project.search_path())
            .env("FLN_MACRO_PARTITION", &project.partition)
            .output()
            .unwrap()
    };
    let emitted = emit(&executable);
    assert!(emitted.status.success(), "{emitted:?}");
    assert!(emitted.stderr.is_empty(), "{emitted:?}");
    let stdout = String::from_utf8(emitted.stdout).unwrap();
    assert!(stdout.contains("\"outcome\":\"complete\""), "{stdout}");
    assert!(stdout.contains("\"kind\":\"nat\",\"value\":13"), "{stdout}");
    assert!(stdout.contains("\"emittedFlbc\":{\"path\":"), "{stdout}");
    assert!(stdout.contains("\"emittedSidecar\":null"), "{stdout}");
    assert_imported_macro_provenance(&stdout);
    let product_bytes = std::fs::read(&product).unwrap();
    assert!(!product_bytes.is_empty());
    let replayed = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["flbc", "run", "--json"])
        .arg(&product)
        .current_dir(&project.root)
        .env_remove("LEAN_PATH")
        .env_remove("FLN_MACRO_PARTITION")
        .output()
        .unwrap();
    assert!(replayed.status.success(), "{replayed:?}");
    assert!(replayed.stderr.is_empty(), "{replayed:?}");
    let stdout = String::from_utf8(replayed.stdout).unwrap();
    assert!(stdout.contains("\"schema\":\"fln.flbc-run/3\""), "{stdout}");
    assert!(stdout.contains("\"outcome\":\"complete\""), "{stdout}");
    assert!(stdout.contains("\"returnValue\":13,"), "{stdout}");
    assert!(stdout.contains("\"sidecar\":null"), "{stdout}");
    assert_eq!(std::fs::read(&product).unwrap(), product_bytes);

    let replacement = format!("{IMPORTED_MACRO_CLIENT}#eval (17 : Bool)\n");
    assert_macro_program_refusal(
        emit(&replacement),
        1,
        "output",
        true,
        "already exists; no artifact was published",
    );
    assert_eq!(std::fs::read(&product).unwrap(), product_bytes);
    assert!(!flbc.exists() && !sidecar.exists());

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
        assert_eq!(project.check(IMPORTED_MACRO_DECLARATIONS), accepted);
    }

    // Without explicit policy the original frontend remains in use; the
    // otherwise ill-typed ascription must not silently acquire macro semantics.
    ImportedMacroProject::refused(project.native(
        "check-source",
        IMPORTED_MACRO_DECLARATIONS,
        None,
    ));
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
        project.native(
            "check-source",
            IMPORTED_MACRO_DECLARATIONS,
            Some(&project.partition),
        ),
        5,
        "capability",
        "IR execution refuses unclassified declaration admittedChooseTerm",
    );
    std::fs::rename(&retained_ir, &ir).unwrap();
    assert_eq!(project.check(IMPORTED_MACRO_DECLARATIONS), accepted);

    std::fs::write(&ir, b"not a Lean IR artifact").unwrap();
    assert_macro_refusal(
        project.native(
            "check-source",
            IMPORTED_MACRO_DECLARATIONS,
            Some(&project.partition),
        ),
        1,
        "codec",
        "AdmittedSourceMacro.ir:",
    );
    std::fs::write(&ir, &original_ir).unwrap();
    assert_eq!(project.check(IMPORTED_MACRO_DECLARATIONS), accepted);

    let wrong_partition = project.root.join("wrong-partition.tsv");
    std::fs::write(&wrong_partition, "constant_count\t0\n").unwrap();
    assert_macro_refusal(
        project.native(
            "check-source",
            IMPORTED_MACRO_DECLARATIONS,
            Some(&wrong_partition),
        ),
        1,
        "policy-refusal",
        "IR execution requires the exact pinned census partition",
    );
    assert_eq!(project.check(IMPORTED_MACRO_DECLARATIONS), accepted);
    assert_eq!(std::fs::read(&ir).unwrap(), original_ir);
    assert_eq!(std::fs::read(&olean).unwrap(), original_olean);
}

#[test]
fn installed_runtime_compiles_only_dispatched_imported_macros() {
    let Some(project) = ImportedMacroProject::prepare_with_source(&dormant_macro_provider_source())
    else {
        return;
    };
    let oracle = project.oracle(IMPORTED_MACRO_CLIENT);
    assert!(oracle.status.success(), "{oracle:?}");
    let lean = project.native("lean", IMPORTED_MACRO_CLIENT, Some(&project.partition));
    assert!(lean.status.success(), "{lean:?}");
    assert_eq!(lean.stdout, oracle.stdout);
    assert!(lean.stderr.is_empty(), "{lean:?}");

    let executable = format!("{IMPORTED_MACRO_CLIENT}#eval commandMacroValue\n");
    let run = project.native("run", &executable, Some(&project.partition));
    assert!(run.status.success(), "{run:?}");
    assert!(run.stderr.is_empty(), "{run:?}");
    let stdout = String::from_utf8(run.stdout).unwrap();
    assert!(stdout.contains("\"outcome\":\"complete\""), "{stdout}");
    assert!(stdout.contains("\"kind\":\"nat\",\"value\":11"), "{stdout}");
    assert_imported_macro_provenance(&stdout);
    assert!(!stdout.contains("dormantMacro"), "{stdout}");
    assert!(!stdout.contains("absentMacroPrimitive"), "{stdout}");

    // Earlier checks and evaluations stay unpublished if a later command
    // actually dispatches the unsupported macro.
    let demanded_lean = format!("{IMPORTED_MACRO_CLIENT}def demanded : Nat := _\n");
    let refused = project.native("lean", &demanded_lean, Some(&project.partition));
    assert_eq!(refused.status.code(), Some(5), "{refused:?}");
    let error = ImportedMacroProject::refused(refused);
    assert!(error.contains("absentMacroPrimitive"), "{error}");

    let demanded_run = format!("{executable}#eval _\n");
    assert_macro_program_refusal(
        project.native("run", &demanded_run, Some(&project.partition)),
        5,
        "capability",
        false,
        "absentMacroPrimitive",
    );

    // Raw FLBC publication is allowed in macro mode, but a failed expansion
    // must not publish the already executed prefix as a successful artifact.
    let flbc = project.root.join("demanded.flbc");
    let refused = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args([
            "run",
            "--json",
            "--jobs",
            "1",
            "--import-posture",
            "recheck",
        ])
        .arg("--emit-flbc")
        .arg(&flbc)
        .arg(project.source(&demanded_run))
        .current_dir(project.root.join("client"))
        .env("LEAN_PATH", project.search_path())
        .env("FLN_MACRO_PARTITION", &project.partition)
        .output()
        .unwrap();
    assert_macro_program_refusal(refused, 5, "capability", false, "absentMacroPrimitive");
    assert!(
        !flbc.exists(),
        "a refused macro published an executable prefix"
    );
}

fn imported_syntax_provider_source() -> String {
    // Extend this test's real provider without changing the registration table
    // expected by the older eager-compilation fixtures.
    format!(
        "{}\n{}",
        include_str!("../../fln-olean/fixtures/ir/AdmittedSourceMacro.lean"),
        concat!(
            "syntax (name := admittedWrap) \"admittedWrap%\" term \"endWrap%\" : term\n",
            "@[macro admittedWrap]\n",
            "public meta def admittedWrapMacro : Macro := fun stx _ state =>\n",
            "  .ok (stx.getArg 1) state\n",
            "syntax:65 (name := admittedPickRight) term:66 \" <+> \" term:65 : term\n",
            "@[macro admittedPickRight]\n",
            "public meta def admittedPickRightMacro : Macro := fun stx _ state =>\n",
            "  .ok (stx.getArg 2) state\n",
            "namespace AdmittedScope\n",
            "scoped syntax (name := admittedScopedWrap) \"admittedScoped%\" term \"endScoped%\" : term\n",
            "@[macro admittedScopedWrap]\n",
            "public meta def admittedScopedMacro : Macro := fun stx _ state =>\n",
            "  .ok (stx.getArg 1) state\n",
            "end AdmittedScope\n",
        ),
    )
}

const IMPORTED_SYNTAX_DECLARATIONS: &str = concat!(
    "prelude\n",
    "import AdmittedSourceMacro\n",
    "def commandMacroValue : Nat := (11 : Bool)\n",
    "def syntaxMacroValue : Nat := admittedWrap% commandMacroValue endWrap%\n",
    "theorem syntaxMacroValue_eq : Eq syntaxMacroValue 11 := Eq.refl syntaxMacroValue\n",
    "def chosenMacroValue : Nat := 17 <+> 23\n",
    "theorem chosenMacroValue_eq : Eq chosenMacroValue 23 := Eq.refl chosenMacroValue\n",
    "open scoped AdmittedScope\n",
    "def scopedMacroValue : Nat := admittedScoped% 29 endScoped%\n",
    "theorem scopedMacroValue_eq : Eq scopedMacroValue 29 := Eq.refl scopedMacroValue\n",
);

#[test]
fn installed_imported_syntax_drives_macro_parsing_and_execution() {
    let Some(project) =
        ImportedMacroProject::prepare_with_source(&imported_syntax_provider_source())
    else {
        return;
    };
    let selected = ["AdmittedSourceMacro"];
    let checked = project.native_with_syntax(
        "check-source",
        IMPORTED_SYNTAX_DECLARATIONS,
        Some(&project.partition),
        &selected,
    );
    assert!(checked.status.success(), "{checked:?}; {:?}", project.root);
    assert!(checked.stderr.is_empty(), "{checked:?}");
    let report = String::from_utf8(checked.stdout).unwrap();
    assert!(report.contains("\"outcome\":\"complete\""), "{report}");
    assert!(report.contains("\"theorems\":3"), "{report}");
    assert_imported_macro_provenance(&report);
    for name in [
        "admittedWrapMacro",
        "admittedPickRightMacro",
        "AdmittedScope.admittedScopedMacro",
    ] {
        assert!(
            report.contains(&format!(
                "{{\"name\":\"{name}\",\"producer\":\"reference\"}}"
            )),
            "{report}"
        );
    }

    let queries = format!(
        "{IMPORTED_SYNTAX_DECLARATIONS}#check syntaxMacroValue\n#check chosenMacroValue\n#check scopedMacroValue\n"
    );
    let oracle = project.oracle(&queries);
    assert!(oracle.status.success(), "{oracle:?}");
    assert_eq!(
        oracle.stdout,
        b"syntaxMacroValue : Nat\nchosenMacroValue : Nat\nscopedMacroValue : Nat\n"
    );
    assert!(oracle.stderr.is_empty(), "{oracle:?}");
    let lean = project.native_with_syntax("lean", &queries, Some(&project.partition), &selected);
    assert!(lean.status.success(), "{lean:?}");
    assert_eq!(lean.stdout, oracle.stdout);
    assert!(lean.stderr.is_empty(), "{lean:?}");

    let executable = format!(
        "{queries}#eval admittedWrap% (31 : Bool) endWrap%\n#eval 17 <+> admittedScoped% 37 endScoped%\n"
    );
    let run = project.native_with_syntax("run", &executable, Some(&project.partition), &selected);
    assert!(run.status.success(), "{run:?}");
    assert!(run.stderr.is_empty(), "{run:?}");
    let report = String::from_utf8(run.stdout).unwrap();
    assert!(report.contains("\"kind\":\"nat\",\"value\":31"), "{report}");
    assert!(report.contains("\"kind\":\"nat\",\"value\":37"), "{report}");
    assert_eq!(
        report.matches("\"event\":\"evaluation\"").count(),
        2,
        "{report}"
    );
    assert_imported_macro_provenance(&report);

    let product = project.root.join("imported-syntax.flbc");
    let emitted = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args([
            "run",
            "--json",
            "--jobs",
            "1",
            "--import-posture",
            "recheck",
        ])
        .arg("--emit-flbc")
        .arg(&product)
        .arg(project.source(&executable))
        .current_dir(project.root.join("client"))
        .env("LEAN_PATH", project.search_path())
        .env("FLN_MACRO_PARTITION", &project.partition)
        .env("FLN_SYNTAX_MODULES", selected.join(","))
        .output()
        .unwrap();
    assert!(emitted.status.success(), "{emitted:?}");
    assert!(emitted.stderr.is_empty(), "{emitted:?}");
    assert!(product.is_file());
    let replay = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["flbc", "run", "--json"])
        .arg(&product)
        .env_remove("LEAN_PATH")
        .env_remove("FLN_MACRO_PARTITION")
        .env_remove("FLN_SYNTAX_MODULES")
        .output()
        .unwrap();
    assert!(replay.status.success(), "{replay:?}");
    assert!(replay.stderr.is_empty(), "{replay:?}");
    let replay = String::from_utf8(replay.stdout).unwrap();
    assert!(replay.contains("\"returnValue\":37,"), "{replay}");
    assert!(replay.contains("\"sidecar\":null"), "{replay}");

    // A parser selection grants no proof authority and cannot be silently
    // omitted, borrowed from another closure or activated by a sibling.
    let false_proof = format!(
        "{IMPORTED_SYNTAX_DECLARATIONS}theorem bad : Eq chosenMacroValue 29 := Eq.refl chosenMacroValue\n"
    );
    for verb in ["check-source", "run", "lean"] {
        ImportedMacroProject::refused(project.native_with_syntax(
            verb,
            &false_proof,
            Some(&project.partition),
            &selected,
        ));
        ImportedMacroProject::refused(project.native(
            verb,
            IMPORTED_SYNTAX_DECLARATIONS,
            Some(&project.partition),
        ));
    }
    assert_macro_refusal(
        project.native_with_syntax(
            "check-source",
            IMPORTED_SYNTAX_DECLARATIONS,
            Some(&project.partition),
            &["Absent.Syntax"],
        ),
        5,
        "capability",
        "selected parser module is not in the admitted artifact closure",
    );
    assert_macro_program_refusal(
        project.native_with_syntax(
            "run",
            &executable,
            Some(&project.partition),
            &["AdmittedSourceMacro", "AdmittedSourceMacro"],
        ),
        5,
        "capability",
        false,
        "duplicate parser module AdmittedSourceMacro",
    );
    assert_macro_program_refusal(
        project.native_with_syntax("run", &executable, None, &selected),
        1,
        "input",
        false,
        "FLN_SYNTAX_MODULES requires FLN_MACRO_PARTITION",
    );

    std::fs::write(
        project.root.join("client/ScopedSibling.lean"),
        concat!(
            "prelude\nimport AdmittedSourceMacro\nopen scoped AdmittedScope\n",
            "def siblingValue : Nat := admittedScoped% 41 endScoped%\n",
        ),
    )
    .unwrap();
    let leaked_scope = concat!(
        "prelude\nimport AdmittedSourceMacro\nimport ScopedSibling\n",
        "def mustNotLeak : Nat := admittedScoped% 43 endScoped%\n",
    );
    for verb in ["check-source", "run"] {
        ImportedMacroProject::refused(project.native_with_syntax(
            verb,
            leaked_scope,
            Some(&project.partition),
            &selected,
        ));
    }
    let activated_scope = concat!(
        "prelude\nimport AdmittedSourceMacro\nimport ScopedSibling\n",
        "open scoped AdmittedScope\n",
        "def explicitScope : Nat := admittedScoped% 43 endScoped%\n",
        "theorem explicitScope_eq : Eq explicitScope 43 := Eq.refl explicitScope\n",
    );
    let activated = project.native_with_syntax(
        "check-source",
        activated_scope,
        Some(&project.partition),
        &selected,
    );
    assert!(activated.status.success(), "{activated:?}");
    assert!(activated.stderr.is_empty(), "{activated:?}");
    let recovered = project.native_with_syntax(
        "check-source",
        IMPORTED_SYNTAX_DECLARATIONS,
        Some(&project.partition),
        &selected,
    );
    assert!(recovered.status.success(), "{recovered:?}");
    assert!(recovered.stderr.is_empty(), "{recovered:?}");
}

fn imported_category_provider_source() -> String {
    // The actual Parser.Category declaration is supplied by Init.Notation.
    // Keep its complete Prelude/Coe/Notation closure in the pinned library;
    // the provider alone is selected for imported parser activation.
    let provider = imported_syntax_provider_source();
    let (header, body) = provider
        .split_once("\nopen Lean\n")
        .expect("the macro provider has an explicit import header");
    format!(
        "{header}\npublic import Init.Notation\npublic meta import Init.Notation\n\nopen Lean\n{body}\n{}",
        concat!(
            "declare_syntax_cat admittedData\n",
            "syntax (name := admittedDatum) \"datum%\" num : admittedData\n",
            "syntax (name := admittedUseDatum) \"useDatum%\" admittedData \"endDatum%\" : term\n",
            "@[macro admittedUseDatum]\n",
            "public meta def admittedUseDatumMacro : Macro := fun stx _ state =>\n",
            "  .ok ((stx.getArg 1).getArg 1) state\n",
            "syntax (name := admittedQuoteDatum) \"quoteDatum%\" term \"endQuote%\" : term\n",
            "@[macro admittedQuoteDatum]\n",
            "public meta def admittedQuoteDatumMacro : Macro := fun stx _ state =>\n",
            "  .ok ((((stx.getArg 1).getArg 0).getArg 1).getArg 1) state\n",
        ),
    )
}

#[test]
fn installed_custom_categories_keep_the_generated_quotation_journal() {
    // The pin generates admittedData.quot in the same parser journal as the
    // category. Selecting this whole module must accept and install that exact
    // quotation description. Both forms reach an imported macro before ordinary
    // elaboration; a quote-consuming macro extracts the quoted numeric syntax.
    let Some(project) =
        ImportedMacroProject::prepare_with_source(&imported_category_provider_source())
    else {
        return;
    };
    let selected = ["AdmittedSourceMacro"];
    let declarations = format!(
        "{IMPORTED_MACRO_DECLARATIONS}def categoryValue : Nat := useDatum% datum% 47 endDatum%\n\
         theorem categoryValue_eq : Eq categoryValue 47 := Eq.refl categoryValue\n\
         def quotedCategoryValue : Nat := quoteDatum% `(admittedData| datum% 51) endQuote%\n\
         theorem quotedCategoryValue_eq : Eq quotedCategoryValue 51 := Eq.refl quotedCategoryValue\n"
    );
    let checked = project.native_with_syntax(
        "check-source",
        &declarations,
        Some(&project.partition),
        &selected,
    );
    assert!(checked.status.success(), "{checked:?}; {:?}", project.root);
    assert!(checked.stderr.is_empty(), "{checked:?}");
    let report = String::from_utf8(checked.stdout).unwrap();
    assert!(report.contains("\"outcome\":\"complete\""), "{report}");
    assert!(report.contains("\"theorems\":3"), "{report}");
    assert_imported_macro_provenance(&report);
    for name in ["admittedUseDatumMacro", "admittedQuoteDatumMacro"] {
        assert!(
            report.contains(&format!(
                "{{\"name\":\"{name}\",\"producer\":\"reference\"}}"
            )),
            "{report}"
        );
    }

    let queries = format!("{declarations}#check categoryValue\n#check quotedCategoryValue\n");
    let oracle = project.oracle(&queries);
    assert!(oracle.status.success(), "{oracle:?}");
    assert_eq!(
        oracle.stdout,
        b"categoryValue : Nat\nquotedCategoryValue : Nat\n"
    );
    assert!(oracle.stderr.is_empty(), "{oracle:?}");
    let lean = project.native_with_syntax("lean", &queries, Some(&project.partition), &selected);
    assert!(lean.status.success(), "{lean:?}");
    assert_eq!(lean.stdout, oracle.stdout);
    assert!(lean.stderr.is_empty(), "{lean:?}");

    let executable = format!(
        "{queries}#eval useDatum% datum% 51 endDatum%\n\
         #eval quoteDatum% `(admittedData| datum% 53) endQuote%\n"
    );
    let product = project.root.join("imported-category.flbc");
    let emit = |source: &str, product: &std::path::Path| {
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args([
                "run",
                "--json",
                "--jobs",
                "1",
                "--import-posture",
                "recheck",
            ])
            .arg("--emit-flbc")
            .arg(product)
            .arg(project.source(source))
            .current_dir(project.root.join("client"))
            .env("LEAN_PATH", project.search_path())
            .env("FLN_MACRO_PARTITION", &project.partition)
            .env("FLN_SYNTAX_MODULES", selected.join(","))
            .output()
            .unwrap()
    };
    let emitted = emit(&executable, &product);
    assert!(emitted.status.success(), "{emitted:?}");
    assert!(emitted.stderr.is_empty(), "{emitted:?}");
    let report = String::from_utf8(emitted.stdout).unwrap();
    assert!(report.contains("\"kind\":\"nat\",\"value\":51"), "{report}");
    assert!(report.contains("\"kind\":\"nat\",\"value\":53"), "{report}");
    assert_eq!(
        report.matches("\"event\":\"evaluation\"").count(),
        2,
        "{report}"
    );
    assert!(report.contains("\"emittedFlbc\":{\"path\":"), "{report}");
    assert_imported_macro_provenance(&report);
    let replay = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["flbc", "run", "--json"])
        .arg(&product)
        .env_remove("LEAN_PATH")
        .env_remove("FLN_MACRO_PARTITION")
        .env_remove("FLN_SYNTAX_MODULES")
        .output()
        .unwrap();
    assert!(replay.status.success(), "{replay:?}");
    assert!(replay.stderr.is_empty(), "{replay:?}");
    let replay = String::from_utf8(replay.stdout).unwrap();
    assert!(replay.contains("\"returnValue\":53,"), "{replay}");
    assert!(replay.contains("\"sidecar\":null"), "{replay}");

    let false_proof = format!(
        "{declarations}theorem badCategory : Eq categoryValue 51 := Eq.refl categoryValue\n"
    );
    for verb in ["check-source", "run"] {
        ImportedMacroProject::refused(project.native_with_syntax(
            verb,
            &false_proof,
            Some(&project.partition),
            &selected,
        ));
        ImportedMacroProject::refused(project.native(
            verb,
            &declarations,
            Some(&project.partition),
        ));
    }
    let malformed = format!("{executable}#eval useDatum% datum% endDatum%\n");
    let refused_product = project.root.join("malformed-category.flbc");
    ImportedMacroProject::refused(emit(&malformed, &refused_product));
    assert!(
        !refused_product.exists(),
        "malformed category syntax published an executable prefix"
    );
}

#[test]
fn installed_lake_builds_imported_macro_expansions_and_reimports_the_checked_artifacts() {
    let Some(project) =
        ImportedMacroProject::prepare_with_source(&imported_syntax_provider_source())
    else {
        return;
    };
    let client = project.root.join("client");
    std::fs::write(
        client.join("lakefile.toml"),
        "name = \"macro_build\"\n[[lean_lib]]\nname = \"Client\"\nroots = [\"Main\", \"Other\", \"Bad\"]\n",
    )
    .unwrap();
    let main = concat!(
        "prelude\nimport AdmittedSourceMacro\n",
        "def compiledMacroValue : Nat := admittedWrap% (11 : Bool) endWrap%\n",
        "theorem compiledMacroValue_eq : Eq compiledMacroValue 11 := Eq.refl compiledMacroValue\n",
    );
    let other = concat!(
        "prelude\nimport AdmittedSourceMacro\n",
        "def otherMacroValue : Nat := admittedWrap% (13 : Bool) endWrap%\n",
    );
    let oracle = project.oracle(main);
    assert!(oracle.status.success(), "{oracle:?}; {:?}", project.root);
    assert!(oracle.stdout.is_empty(), "{oracle:?}");
    assert!(oracle.stderr.is_empty(), "{oracle:?}");
    std::fs::write(client.join("Other.lean"), other).unwrap();
    let output = client.join(".lake/build/lib/lean");
    let main_artifact = output.join("Main.olean");
    let other_artifact = output.join("Other.olean");
    let selected = ["AdmittedSourceMacro"];

    // Neither ordinary parsing nor macro registration without the selected
    // artifact grammar may silently give custom source a different meaning.
    for refused in [
        project.lake(&["+Main:olean"], false, &[]),
        project.lake(&["+Main:olean"], true, &[]),
        project.lake(&["+Main:olean"], false, &selected),
    ] {
        ImportedMacroProject::refused(refused);
        assert!(!main_artifact.exists());
    }

    let built = project.lake(&["+Main:olean", "+Other:olean"], true, &selected);
    assert!(built.status.success(), "{built:?}; {:?}", project.root);
    assert!(built.stderr.is_empty(), "{built:?}");
    let report = String::from_utf8(built.stdout).unwrap();
    assert!(
        report.contains("\"schema\":\"fln.lake-build/2\""),
        "{report}"
    );
    assert!(report.contains("\"modules_built\":2"), "{report}");
    assert!(report.contains("\"module_elaborations\":2"), "{report}");
    assert!(report.contains("\"module_checks_reused\":0"), "{report}");
    assert!(report.contains("\"modules_cached\":0"), "{report}");
    assert!(
        report.contains("\"module_records\":\"disabled-imported-macros\""),
        "{report}"
    );
    assert!(report.contains("\"importedMacroBuilds\":["), "{report}");
    assert!(report.contains("\"entry\":\"Main\""), "{report}");
    assert!(report.contains("\"entry\":\"Other\""), "{report}");
    assert_eq!(
        report.matches("\"importedMacros\":{").count(),
        2,
        "{report}"
    );
    assert_imported_macro_provenance(&report);
    let main_bytes = std::fs::read(&main_artifact).unwrap();
    let other_bytes = std::fs::read(&other_artifact).unwrap();
    assert!(!main_bytes.is_empty());
    assert!(!other_bytes.is_empty());

    // The produced module is consumed without this package's source files or
    // imported macro mode. Both native checkers and the pinned Reference must
    // accept the ordinary theorem about the serialized expansion.
    let consumer = project.root.join("consumer");
    std::fs::create_dir(&consumer).unwrap();
    let use_path = consumer.join("Use.lean");
    std::fs::write(
        &use_path,
        "prelude\nimport Main\ntheorem serializedMacroProof : Eq compiledMacroValue 11 := Eq.refl compiledMacroValue\n",
    )
    .unwrap();
    let search = std::env::join_paths([
        output.clone(),
        project.root.join("objects"),
        project.library.clone(),
    ])
    .unwrap();
    let reimported = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json", "--jobs", "1"])
        .arg(&use_path)
        .current_dir(&consumer)
        .env("LEAN_PATH", &search)
        .env("FLN_IMPORT_REUSE_DIR", project.root.join("records"))
        .env_remove("FLN_MACRO_PARTITION")
        .env_remove("FLN_SYNTAX_MODULES")
        .output()
        .unwrap();
    assert!(reimported.status.success(), "{reimported:?}");
    assert!(reimported.stderr.is_empty(), "{reimported:?}");
    let reimported = String::from_utf8(reimported.stdout).unwrap();
    assert!(reimported.contains("\"authority\":true"), "{reimported}");
    assert!(!reimported.contains("\"importedMacros\""), "{reimported}");
    let oracle = Command::new(&project.reference)
        .arg(&use_path)
        .current_dir(&consumer)
        .env("LEAN_PATH", &search)
        .output()
        .unwrap();
    assert!(oracle.status.success(), "{oracle:?}; {:?}", project.root);
    assert!(oracle.stdout.is_empty(), "{oracle:?}");
    assert!(oracle.stderr.is_empty(), "{oracle:?}");

    // A warm invocation still expands every source and never uses ordinary
    // source records whose identity omits macro IR and the selected grammar.
    let repeated = project.lake(&["+Main:olean", "+Other:olean"], true, &selected);
    assert!(repeated.status.success(), "{repeated:?}");
    let repeated = String::from_utf8(repeated.stdout).unwrap();
    assert!(repeated.contains("\"module_elaborations\":2"), "{repeated}");
    assert!(repeated.contains("\"modules_cached\":0"), "{repeated}");
    assert_imported_macro_provenance(&repeated);
    assert_eq!(std::fs::read(&main_artifact).unwrap(), main_bytes);
    assert_eq!(std::fs::read(&other_artifact).unwrap(), other_bytes);

    // Code is captured again on each invocation. An earlier successful source
    // artifact cannot conceal a now-corrupt imported executable companion.
    let ir = project.root.join("objects/AdmittedSourceMacro.ir");
    let ir_bytes = std::fs::read(&ir).unwrap();
    std::fs::write(&ir, b"invalid imported macro IR").unwrap();
    ImportedMacroProject::refused(project.lake(&["+Main:olean"], true, &selected));
    assert_eq!(std::fs::read(&main_artifact).unwrap(), main_bytes);
    std::fs::write(&ir, ir_bytes).unwrap();

    // A late false theorem withholds all products of the invocation, including
    // the already compiled changed sibling and a newly requested module.
    std::fs::write(client.join("Other.lean"), other.replace("13", "17")).unwrap();
    std::fs::write(
        client.join("Bad.lean"),
        concat!(
            "prelude\nimport AdmittedSourceMacro\n",
            "def badMacroValue : Nat := admittedWrap% (19 : Bool) endWrap%\n",
            "theorem falseMacroProof : Eq badMacroValue 20 := Eq.refl badMacroValue\n",
        ),
    )
    .unwrap();
    ImportedMacroProject::refused(project.lake(&["+Other:olean", "+Bad:olean"], true, &selected));
    assert_eq!(std::fs::read(&main_artifact).unwrap(), main_bytes);
    assert_eq!(std::fs::read(&other_artifact).unwrap(), other_bytes);
    assert!(!output.join("Bad.olean").exists());

    // The snapshot records that its macro inputs are not yet a rebuild model.
    // It cannot claim an up-to-date build, even after opting out of macro mode.
    let explanation = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["build", "explain", "--json"])
        .current_dir(&client)
        .env("LEAN_PATH", project.search_path())
        .env_remove("FLN_MACRO_PARTITION")
        .env_remove("FLN_SYNTAX_MODULES")
        .output()
        .unwrap();
    assert_eq!(explanation.status.code(), Some(5), "{explanation:?}");
    let explanation = String::from_utf8(explanation.stderr).unwrap();
    assert!(
        explanation.contains("do not yet bind executable IR"),
        "{explanation}"
    );
}

fn imported_hygiene_provider_source() -> String {
    format!(
        "{}\n{}",
        include_str!("../../fln-olean/fixtures/ir/AdmittedSourceMacro.lean"),
        r#"public section

mutual
meta partial def replaceIdentSyntax (target : Name) (replacement : Syntax) : Syntax → Syntax
  | .ident info raw val pre =>
    match Name.beq val target with
    | true =>
      match replacement with
      | .ident _ _ repVal repPre => .ident info raw repVal (List.append repPre pre)
      | other => other
    | false => .ident info raw val pre
  | .node info kind args =>
    .node info kind (Array.mk (replaceIdentSyntaxList target replacement args.toList))
  | other => other

meta partial def replaceIdentSyntaxList (target : Name) (replacement : Syntax) : List Syntax → List Syntax
  | .nil => .nil
  | .cons h t => .cons (replaceIdentSyntax target replacement h) (replaceIdentSyntaxList target replacement t)
end

syntax (name := hygTerm) "hygTerm%" ident ":" term : term

@[macro hygTerm]
public meta def hygTermMacro : Macro := fun stx context state =>
  match stx.getArg 1 with
  | .ident info raw id pre =>
    match Lean.Macro.addMacroScope id context state with
    | .ok hyg next => .ok (replaceIdentSyntax id (.ident info raw hyg pre) (stx.getArg 3)) next
    | .error err next => .error err next
  | _ => .error .unsupportedSyntax state

syntax (name := hygSplice) "hygSplice%" ident ":" term "=>" term : term

@[macro hygSplice]
public meta def hygSpliceMacro : Macro := fun stx context state =>
  match stx.getArg 1 with
  | .ident info raw id pre =>
    match Lean.Macro.addMacroScope id context state with
    | .ok hyg next =>
      let stamped := replaceIdentSyntax id (.ident info raw hyg pre) (stx.getArg 3)
      .ok (replaceIdentSyntax `HOLE (stx.getArg 5) stamped) next
    | .error err next => .error err next
  | _ => .error .unsupportedSyntax state

syntax (name := hygCmd) "hygCmd%" ident ":" "[" command "]" : command

@[macro hygCmd]
public meta def hygCmdMacro : Macro := fun stx context state =>
  match stx.getArg 1 with
  | .ident info raw id pre =>
    match Lean.Macro.addMacroScope id context state with
    | .ok hyg next => .ok (replaceIdentSyntax id (.ident info raw hyg pre) (stx.getArg 4)) next
    | .error err next => .error err next
  | _ => .error .unsupportedSyntax state
"#,
    )
}

fn collect_hygienic_binders(
    expr: &fln_core::expr::Expr,
    out: &mut Vec<(fln_core::name::Name, fln_core::name::Name)>,
) {
    use fln_core::expr::ExprNode;
    use fln_core::name::Name;
    use fln_core::name::hygiene::extract_macro_scopes;

    let internal = Name::from_components(["_internal"]);
    let mut record = |binder: &Name| {
        if let Ok(view) = extract_macro_scopes(binder)
            && !view.scopes.is_empty()
            && view.context != internal
        {
            out.push((view.name, view.context));
        }
    };
    match expr.node() {
        ExprNode::Lam {
            binder_name,
            binder_type,
            body,
            ..
        }
        | ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            ..
        } => {
            record(binder_name);
            collect_hygienic_binders(binder_type, out);
            collect_hygienic_binders(body, out);
        }
        ExprNode::LetE {
            decl_name,
            type_,
            value,
            body,
            ..
        } => {
            record(decl_name);
            collect_hygienic_binders(type_, out);
            collect_hygienic_binders(value, out);
            collect_hygienic_binders(body, out);
        }
        ExprNode::App { fun, arg } => {
            collect_hygienic_binders(fun, out);
            collect_hygienic_binders(arg, out);
        }
        ExprNode::MData { expr: inner, .. }
        | ExprNode::Proj {
            struct_expr: inner, ..
        } => {
            collect_hygienic_binders(inner, out);
        }
        _ => {}
    }
}

fn decode_olean_hygienic_contexts(
    path: &std::path::Path,
) -> std::collections::BTreeMap<
    fln_core::name::Name,
    Vec<(fln_core::name::Name, fln_core::name::Name)>,
> {
    use fln::ConstantInfo;
    use fln_olean::decl::DeclDecoder;
    use fln_olean::region::{OleanView, WalkBudget};

    let bytes = std::fs::read(path).unwrap();
    let view = OleanView::parse(&bytes).unwrap();
    let constants = DeclDecoder::new(&view, WalkBudget::default())
        .decode_module_constants()
        .unwrap();
    let mut by_decl = std::collections::BTreeMap::new();
    for info in constants {
        let target = match &info {
            ConstantInfo::Defn(v) => &v.value,
            ConstantInfo::Thm(v) => &v.value,
            ConstantInfo::Opaque(v) => &v.value,
            other => &other.constant_val().type_,
        };
        let mut binders = Vec::new();
        collect_hygienic_binders(target, &mut binders);
        by_decl.insert(info.name().clone(), binders);
    }
    by_decl
}

#[test]
fn imported_macro_hygiene_matches_pinned_reference_quot_contexts_and_proves_collision_safety() {
    use fln_core::name::Name;

    let Some(project) =
        ImportedMacroProject::prepare_with_source(&imported_hygiene_provider_source())
    else {
        return;
    };
    let client = project.root.join("client");
    std::fs::write(
        client.join("lakefile.toml"),
        "name = \"macro_hygiene\"\n[[lean_lib]]\nname = \"Client\"\nroots = [\"Main\"]\n",
    )
    .unwrap();
    let main_src = r#"prelude
import AdmittedSourceMacro

-- leading trivia
def first : Nat := (hygTerm% z : (fun z : Nat => z)) 10 -- trailing

namespace Sub
def second : Nat := (hygTerm% z : (fun z : Nat => z)) 20
end Sub

def Sub.dottedDef : Nat := (hygTerm% z : (fun z : Nat => z)) 25

private def privDef : Nat := (hygTerm% z : (fun z : Nat => z)) 35

mutual
  def mA : Nat := (hygTerm% z : (fun z : Nat => z)) mB
  def mB : Nat := (hygTerm% z : (fun z : Nat => z)) 11
end

inductive MyInd : Type where
  | mk : (x : Nat) → (h : Eq ((hygTerm% z : (fun z : Nat => z)) x) x) → MyInd

mutual
  inductive MutIndA : Type where
    | mk : (x : Nat) → (h : Eq ((hygTerm% z : (fun z : Nat => z)) x) x) → MutIndA
    | step : MutIndB → MutIndA
  inductive MutIndB : Type where
    | mk : (x : Nat) → (h : Eq ((hygTerm% z : (fun z : Nat => z)) x) x) → MutIndB
end

hygCmd% z : [def third : Nat := (fun z : Nat => z) 30]

open Sub in
hygCmd% z : [def fromOpenIn : Nat := (fun z : Nat => z) second]

hygCmd% u : [def fourth : Nat := (fun u : Nat => (hygTerm% z : (fun z : Nat => u)) 0) 4]

namespace DupA
def dupName : Nat := (hygTerm% z : (fun z : Nat => z)) 5
end DupA

namespace DupB
def dupName : Nat := (hygTerm% z : (fun z : Nat => z)) 6
end DupB

def nonCapture (z : Nat) : Nat := (hygSplice% z : (fun z : Nat => HOLE) => z) 99

theorem fourth_eq : Eq fourth 4 := Eq.refl fourth
theorem nonCapture_eq (z : Nat) : Eq (nonCapture z) z := Eq.refl z
"#;
    let main_path = project.source(main_src);
    let ref_olean = project.root.join("ref_out/Main.olean");
    std::fs::create_dir(project.root.join("ref_out")).unwrap();
    let ref_build = Command::new(&project.reference)
        .arg("-R")
        .arg(&client)
        .arg("-o")
        .arg(&ref_olean)
        .arg(&main_path)
        .current_dir(&client)
        .env("LEAN_PATH", project.search_path())
        .output()
        .unwrap();
    assert!(ref_build.status.success(), "{ref_build:?}");
    assert!(ref_build.stdout.is_empty(), "{ref_build:?}");
    assert!(ref_build.stderr.is_empty(), "{ref_build:?}");

    let selected = ["AdmittedSourceMacro"];
    let built = project.lake(&["+Main:olean"], true, &selected);
    assert!(built.status.success(), "{built:?}; {:?}", project.root);
    assert!(built.stderr.is_empty(), "{built:?}");

    let fln_olean = client.join(".lake/build/lib/lean/Main.olean");
    let fln_map = decode_olean_hygienic_contexts(&fln_olean);
    let ref_map = decode_olean_hygienic_contexts(&ref_olean);

    let priv_name = Name::str(
        Name::num(Name::from_components(["_private", "Main"]), 0),
        "privDef",
    );
    let targets = [
        Name::from_components(["first"]),
        Name::from_components(["Sub", "second"]),
        Name::from_components(["Sub", "dottedDef"]),
        priv_name,
        Name::from_components(["mA"]),
        Name::from_components(["mB"]),
        Name::from_components(["MyInd", "mk"]),
        Name::from_components(["MutIndA", "mk"]),
        Name::from_components(["MutIndB", "mk"]),
        Name::from_components(["third"]),
        Name::from_components(["fromOpenIn"]),
        Name::from_components(["fourth"]),
        Name::from_components(["DupA", "dupName"]),
        Name::from_components(["DupB", "dupName"]),
        Name::from_components(["nonCapture"]),
    ];
    for decl in &targets {
        let fln_binders = fln_map
            .get(decl)
            .unwrap_or_else(|| panic!("missing {decl:?} in FrankenLean Main.olean"));
        let ref_binders = ref_map
            .get(decl)
            .unwrap_or_else(|| panic!("missing {decl:?} in Reference Main.olean"));
        assert!(
            !ref_binders.is_empty(),
            "expected hygienic binders in {decl:?}"
        );
        assert_eq!(
            fln_binders,
            ref_binders,
            "quotation context mismatch for {}",
            decl.to_display_string()
        );
    }

    // Two-stage hygiene invariant: Stage 1 command macro `u` and Stage 2 term macro `z`
    // in `fourth` carry distinct `Main.<idx>._hygCtx` quotation contexts.
    let fourth = &fln_map[&Name::from_components(["fourth"])];
    assert_eq!(fourth.len(), 2, "{fourth:?}");
    assert_ne!(fourth[0].1, fourth[1].1, "{fourth:?}");

    // Collision-probing invariant: `DupA.dupName` and `DupB.dupName` share the same short
    // declaration name (`dupName`), so `DupB.dupName` probes `idx + 1` in `used_quot_ctxts`.
    let dup_a = &fln_map[&Name::from_components(["DupA", "dupName"])][0].1;
    let dup_b = &fln_map[&Name::from_components(["DupB", "dupName"])][0].1;
    assert_eq!(
        dup_a,
        &Name::str(
            Name::num(Name::from_components(["Main"]), 3_247_554_766),
            "_hygCtx"
        )
    );
    assert_eq!(
        dup_b,
        &Name::str(
            Name::num(Name::from_components(["Main"]), 3_247_554_767),
            "_hygCtx"
        )
    );

    // Negative control: if `hygSplice%` failed to stamp `z` hygienically, `nonCapture 7`
    // would evaluate to `99` instead of `7`. Both Reference and FrankenLean reject that claim.
    let bad_capture =
        format!("{main_src}\ntheorem captured_wrong : Eq (nonCapture 7) 99 := Eq.refl 99\n");
    let oracle_bad = project.oracle(&bad_capture);
    assert!(!oracle_bad.status.success(), "{oracle_bad:?}");
    project.source(&bad_capture);
    ImportedMacroProject::refused(project.lake(&["+Main:olean"], true, &selected));
}
