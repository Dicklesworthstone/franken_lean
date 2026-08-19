//! Real-process producer-to-consumer evidence for the bounded FLBC product seam.
//!
//! This is deliberately narrower than D18: it proves supported checked Nat
//! arithmetic, String, and Bool sources reach the filesystem only after batch success
//! and that their exact bytes are consumed by Golem. It does not claim a
//! certified build, general Lean source support, closure-complete
//! reproducibility, or thread-matrix determinism.

#![forbid(unsafe_code)]

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

fn run_fln(arguments: &[&Path]) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_fln"));
    for argument in arguments {
        command.arg(argument);
    }
    command.output().expect("run the real fln binary")
}

fn run_lean(arguments: &[&Path]) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_lean"));
    for argument in arguments {
        command.arg(argument);
    }
    command.output().expect("run the real lean binary")
}

fn run_lean_stdin(arguments: &[&Path], input: &[u8]) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_lean"));
    for argument in arguments {
        command.arg(argument);
    }
    let mut child = command
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("start the real lean binary with a standard-input pipe");
    child
        .stdin
        .take()
        .expect("the standard-input pipe was requested")
        .write_all(input)
        .expect("write the bounded standard-input source");
    child
        .wait_with_output()
        .expect("collect the real lean standard-input result")
}

fn utf8(bytes: &[u8]) -> &str {
    std::str::from_utf8(bytes).expect("CLI output is UTF-8")
}

fn fresh_test_root(label: &str) -> std::io::Result<PathBuf> {
    let parent = PathBuf::from(env!("CARGO_TARGET_TMPDIR"));
    for attempt in 0..1_024_u32 {
        let candidate = parent.join(format!(
            "{label}-{}-{:?}-{attempt}",
            std::process::id(),
            std::thread::current().id()
        ));
        match std::fs::create_dir(&candidate) {
            Ok(()) => return Ok(candidate),
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {}
            Err(error) => return Err(error),
        }
    }
    Err(std::io::Error::new(
        std::io::ErrorKind::AlreadyExists,
        "could not allocate a retained integration-test directory after 1024 attempts",
    ))
}

#[test]
fn bounded_native_lean_personality_runs_checks_and_evaluations_and_recovers_from_refusal() {
    let root = fresh_test_root("native-lean-personality-e2e")
        .expect("allocate retained native-lean integration-test directory");
    let source = root.join("Main.lean");

    let githash = run_lean(&[Path::new("--githash")]);
    assert!(githash.status.success());
    assert_eq!(
        utf8(&githash.stdout),
        format!("{}\n", fln::OLEAN_PIN_COMMIT)
    );
    assert!(githash.stderr.is_empty());

    let features = run_lean(&[Path::new("--features")]);
    assert!(features.status.success());
    assert_eq!(utf8(&features.stdout), "[]\n");
    assert!(features.stderr.is_empty());

    for option in ["--print-prefix", "--print-libdir"] {
        let uninstalled = run_lean(&[Path::new(option)]);
        assert!(!uninstalled.status.success());
        assert!(uninstalled.stdout.is_empty());
        assert!(utf8(&uninstalled.stderr).starts_with("lean: installation: "));
        assert!(utf8(&uninstalled.stderr).contains("<prefix>/bin/lean"));
    }

    let toolchain = root.join("toolchain");
    let bin = toolchain.join("bin");
    let libdir = toolchain.join("lib").join("lean");
    std::fs::create_dir_all(&bin).expect("create the conventional toolchain bin directory");
    std::fs::create_dir_all(&libdir).expect("create the conventional Lean library directory");
    let installed_lean = bin.join("lean");
    std::fs::copy(env!("CARGO_BIN_EXE_lean"), &installed_lean)
        .expect("copy the real lean binary into the conventional installed layout");

    let prefix = Command::new(&installed_lean)
        .arg("--print-prefix")
        .output()
        .expect("query the copied installed lean binary for its prefix");
    assert!(
        prefix.status.success(),
        "installed lean --print-prefix stderr: {}",
        utf8(&prefix.stderr)
    );
    assert_eq!(utf8(&prefix.stdout), format!("{}\n", toolchain.display()));
    assert!(prefix.stderr.is_empty());

    let reported_libdir = Command::new(&installed_lean)
        .arg("--print-libdir")
        .output()
        .expect("query the copied installed lean binary for its library directory");
    assert!(
        reported_libdir.status.success(),
        "installed lean --print-libdir stderr: {}",
        utf8(&reported_libdir.stderr)
    );
    assert_eq!(
        utf8(&reported_libdir.stdout),
        format!("{}\n", libdir.display())
    );
    assert!(reported_libdir.stderr.is_empty());

    std::fs::write(
        &source,
        b"def answer : Nat := 40 + 2\n#eval \"native\"\n#eval answer\n#eval answer == 42\ndef retained : Nat := 7\n",
    )
    .expect("write supported evaluating source");

    let evaluated = run_lean(&[Path::new("-q"), Path::new("--quiet"), &source]);
    assert!(
        evaluated.status.success(),
        "native lean stderr: {}",
        utf8(&evaluated.stderr)
    );
    assert_eq!(utf8(&evaluated.stdout), "\"native\"\n42\ntrue\n");
    assert!(evaluated.stderr.is_empty());

    let piped = run_lean_stdin(
        &[Path::new("--stdin")],
        b"def piped : Nat := 40 + 2\n#eval \"stdin\"\n#eval piped\n#eval piped == 42\n",
    );
    assert!(
        piped.status.success(),
        "native lean --stdin stderr: {}",
        utf8(&piped.stderr)
    );
    assert_eq!(utf8(&piped.stdout), "\"stdin\"\n42\ntrue\n");
    assert!(piped.stderr.is_empty());

    // `Nat` itself has type `Sort 1`: this positive cannot be implemented by
    // delegating the query to the closed-scalar `#eval`/Golem path.
    for (query, expected) in [
        (b"#check Nat\n".as_slice(), "Nat : Type\n"),
        (
            b"#check Nat.add\n".as_slice(),
            "Nat.add : Nat → Nat → Nat\n",
        ),
        (
            b"#check let x : Nat := 40; x + 2\n".as_slice(),
            "let x : Nat := 40; x + 2 : Nat\n",
        ),
    ] {
        let checked = run_lean_stdin(&[Path::new("--stdin")], query);
        assert!(
            checked.status.success(),
            "native lean #check stderr: {}",
            utf8(&checked.stderr)
        );
        assert_eq!(utf8(&checked.stdout), expected);
        assert!(checked.stderr.is_empty());
    }

    std::fs::write(&source, b"#check Nat.add\n").expect("write standalone checked query");
    let checked_file = run_lean(&[&source]);
    assert!(
        checked_file.status.success(),
        "file-backed native lean #check stderr: {}",
        utf8(&checked_file.stderr)
    );
    assert_eq!(utf8(&checked_file.stdout), "Nat.add : Nat → Nat → Nat\n");
    assert!(checked_file.stderr.is_empty());

    let imported_dir = root.join("Project");
    std::fs::create_dir_all(&imported_dir).expect("create the imported check fixture directory");
    std::fs::write(imported_dir.join("Base.lean"), b"def base : Nat := 40\n")
        .expect("write the transitive imported check fixture dependency");
    std::fs::write(
        imported_dir.join("Seed.lean"),
        b"import Project.Base\ndef seed : Nat := base + 2\n",
    )
    .expect("write the imported check fixture dependency");
    std::fs::write(&source, b"import Project.Seed\n#check seed\n")
        .expect("write an imported check query");
    let imported_check = run_lean(&[&source]);
    assert!(
        imported_check.status.success(),
        "imported native lean #check stderr: {}",
        utf8(&imported_check.stderr)
    );
    assert_eq!(utf8(&imported_check.stdout), "seed : Nat\n");
    assert!(imported_check.stderr.is_empty());

    std::fs::write(
        imported_dir.join("Seed.lean"),
        b"import Project.Base\n#eval base + 1\ndef seed : Nat := base + 2\n",
    )
    .expect("plant a checked evaluation in the imported query closure");
    std::fs::write(&source, b"import Project.Seed\n#check seed\n")
        .expect("write the evaluation-bearing imported check query");
    let imported_evaluation = run_lean(&[&source]);
    assert!(
        imported_evaluation.status.success(),
        "evaluation-bearing imported check stderr: {}",
        utf8(&imported_evaluation.stderr)
    );
    assert_eq!(utf8(&imported_evaluation.stdout), "seed : Nat\n");
    assert!(imported_evaluation.stderr.is_empty());

    std::fs::write(
        imported_dir.join("Seed.lean"),
        b"import Project.Base\n#check base\ndef seed : Nat := base + 2\n",
    )
    .expect("plant a scratch-only dependency check");
    let imported_dependency_check = run_lean(&[&source]);
    assert!(
        imported_dependency_check.status.success(),
        "dependency-check native lean stderr: {}",
        utf8(&imported_dependency_check.stderr)
    );
    assert_eq!(utf8(&imported_dependency_check.stdout), "seed : Nat\n");
    assert!(imported_dependency_check.stderr.is_empty());

    std::fs::write(
        imported_dir.join("Seed.lean"),
        b"import Project.Base\n#check later\ndef later : Nat := base + 2\n",
    )
    .expect("plant a dependency check before its definition");
    let future_dependency_check = run_lean(&[&source]);
    assert!(!future_dependency_check.status.success());
    assert!(future_dependency_check.stdout.is_empty());
    assert!(
        utf8(&future_dependency_check.stderr).contains("no inferable type"),
        "future dependency check stderr: {}",
        utf8(&future_dependency_check.stderr)
    );

    let unknown_check = run_lean_stdin(
        &[Path::new("--stdin")],
        b"def retained : Nat := 7\n#check Missing\n",
    );
    assert!(!unknown_check.status.success());
    assert!(unknown_check.stdout.is_empty());
    assert!(utf8(&unknown_check.stderr).starts_with("lean: execution: "));
    assert!(utf8(&unknown_check.stderr).contains("no inferable type"));

    let terminal_check = run_lean_stdin(
        &[Path::new("--stdin")],
        b"def first (x : Nat) : Nat := x + 2\ndef answer : Nat := first 40\n#check answer\n",
    );
    assert!(
        terminal_check.status.success(),
        "terminal native lean #check stderr: {}",
        utf8(&terminal_check.stderr)
    );
    assert_eq!(utf8(&terminal_check.stdout), "answer : Nat\n");
    assert!(terminal_check.stderr.is_empty());

    let terminal_function_check = run_lean_stdin(
        &[Path::new("--stdin")],
        b"def add (x : Nat) : Nat := x + 1\n#check add\n",
    );
    assert!(terminal_function_check.status.success());
    assert_eq!(utf8(&terminal_function_check.stdout), "add : Nat → Nat\n");
    assert!(terminal_function_check.stderr.is_empty());

    let evaluation_prefix = run_lean_stdin(&[Path::new("--stdin")], b"#eval 1\n#check Nat\n");
    assert!(evaluation_prefix.status.success());
    assert_eq!(utf8(&evaluation_prefix.stdout), "1\nNat : Type\n");
    assert!(evaluation_prefix.stderr.is_empty());

    let mixed_checks = run_lean_stdin(
        &[Path::new("--stdin")],
        b"#check Nat\n#eval 40 + 2\ndef later : Nat := 1\n#check later\n#eval later + 1\n#check Nat.add\n",
    );
    assert!(
        mixed_checks.status.success(),
        "mixed native lean command stderr: {}",
        utf8(&mixed_checks.stderr)
    );
    assert_eq!(
        utf8(&mixed_checks.stdout),
        "Nat : Type\n42\nlater : Nat\n2\nNat.add : Nat → Nat → Nat\n"
    );
    assert!(mixed_checks.stderr.is_empty());

    let late_check_refusal = run_lean_stdin(
        &[Path::new("--stdin")],
        b"#check Nat\n#eval 42\ndef retained : Nat := 7\n#check Missing\n",
    );
    assert!(!late_check_refusal.status.success());
    assert!(late_check_refusal.stdout.is_empty());
    assert!(utf8(&late_check_refusal.stderr).starts_with("lean: execution: "));
    assert!(utf8(&late_check_refusal.stderr).contains("no inferable type"));

    let future_definition = run_lean_stdin(
        &[Path::new("--stdin")],
        b"#check later\ndef later : Nat := 1\n",
    );
    assert!(!future_definition.status.success());
    assert!(future_definition.stdout.is_empty());
    assert!(utf8(&future_definition.stderr).starts_with("lean: execution: "));
    assert!(utf8(&future_definition.stderr).contains("no inferable type"));

    let piped_late_refusal = run_lean_stdin(
        &[Path::new("--stdin")],
        b"#eval 42\ndef broken : Nat := missing\n",
    );
    assert!(!piped_late_refusal.status.success());
    assert!(piped_late_refusal.stdout.is_empty());
    assert!(utf8(&piped_late_refusal.stderr).starts_with("lean: execution: "));
    assert!(utf8(&piped_late_refusal.stderr).contains("unknown constant"));

    let piped_budget_stop = run_lean_stdin(
        &[Path::new("--stdin"), Path::new("--max-bytes=1")],
        b"#eval 42\n",
    );
    assert!(!piped_budget_stop.status.success());
    assert!(piped_budget_stop.stdout.is_empty());
    assert!(utf8(&piped_budget_stop.stderr).starts_with("lean: resource: "));
    assert!(utf8(&piped_budget_stop.stderr).contains("standard input source exceeded"));

    let piped_import = run_lean_stdin(
        &[Path::new("--stdin")],
        b"import Project.Missing\n#eval 42\n",
    );
    assert!(!piped_import.status.success());
    assert!(piped_import.stdout.is_empty());
    assert!(utf8(&piped_import.stderr).starts_with("lean: input: "));
    assert!(utf8(&piped_import.stderr).contains("does not resolve imports"));

    let piped_after_refusals = run_lean_stdin(&[Path::new("--stdin")], b"#eval 42\n");
    assert!(piped_after_refusals.status.success());
    assert_eq!(utf8(&piped_after_refusals.stdout), "42\n");
    assert!(piped_after_refusals.stderr.is_empty());

    let checked_after_refusals = run_lean_stdin(&[Path::new("--stdin")], b"#check 40 + 2\n");
    assert!(checked_after_refusals.status.success());
    assert_eq!(utf8(&checked_after_refusals.stdout), "40 + 2 : Nat\n");
    assert!(checked_after_refusals.stderr.is_empty());

    let definition_only = root.join("DefinitionOnly.lean");
    std::fs::write(&definition_only, b"def answer : Nat := 40 + 2\n")
        .expect("write definition-only source");
    let silent = run_lean(&[&definition_only]);
    assert!(
        silent.status.success(),
        "definition-only native lean stderr: {}",
        utf8(&silent.stderr)
    );
    assert!(silent.stdout.is_empty());
    assert!(silent.stderr.is_empty());

    let function_only = root.join("FunctionOnly.lean");
    std::fs::write(&function_only, b"def add (x : Nat) : Nat := x + 1\n")
        .expect("write function-only source");
    let silent_function = run_lean(&[&function_only]);
    assert!(
        silent_function.status.success(),
        "function-only native lean stderr: {}",
        utf8(&silent_function.stderr)
    );
    assert!(silent_function.stdout.is_empty());
    assert!(silent_function.stderr.is_empty());

    let final_function = root.join("FinalFunction.lean");
    std::fs::write(
        &final_function,
        b"def add (x : Nat) : Nat := x + 1\n#eval add 41\ndef keep (x : Nat) : Nat := x\n",
    )
    .expect("write a function evaluation followed by another function declaration");
    let evaluated_before_function = run_lean(&[&final_function]);
    assert!(
        evaluated_before_function.status.success(),
        "final-function native lean stderr: {}",
        utf8(&evaluated_before_function.stderr)
    );
    assert_eq!(utf8(&evaluated_before_function.stdout), "42\n");
    assert!(evaluated_before_function.stderr.is_empty());

    std::fs::write(&source, b"#eval 40 + 2\ndef answer : Nat := missing\n")
        .expect("plant an unsupported open definition");
    let refused = run_lean(&[&source]);
    assert!(!refused.status.success());
    assert!(refused.stdout.is_empty());
    assert!(utf8(&refused.stderr).starts_with("lean: execution: "));
    assert!(utf8(&refused.stderr).contains("unknown constant"));

    std::fs::write(&source, b"def answer : Nat := 40 + 2\n#eval answer\n")
        .expect("repair the refused source");
    let recovered = run_lean(&[&source]);
    assert!(
        recovered.status.success(),
        "recovered native lean stderr: {}",
        utf8(&recovered.stderr)
    );
    assert_eq!(utf8(&recovered.stdout), "42\n");
    assert!(recovered.stderr.is_empty());
}

#[test]
fn checked_source_publishes_a_standalone_olean_snapshot_consumed_by_the_real_checker() {
    let root = fresh_test_root("source-olean-snapshot-e2e")
        .expect("allocate retained source-snapshot integration-test directory");
    let source = root.join("Snapshot.lean");
    let snapshot = root.join("Snapshot.olean");
    std::fs::write(
        &source,
        b"def base : Nat := 40\n#eval base + 2\ndef answer : Bool := base + 2 == 42\n",
    )
    .expect("write the checked snapshot source");

    let produced = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-olean-snapshot"),
        &snapshot,
        &source,
    ]);
    assert!(
        produced.status.success(),
        "snapshot producer stderr: {}",
        utf8(&produced.stderr)
    );
    assert!(produced.stderr.is_empty());
    let producer_stdout = utf8(&produced.stdout);
    assert!(producer_stdout.contains("\"schema\":\"fln.source-run/9\""));
    assert!(producer_stdout.contains("\"emittedOleanSnapshot\":{"));
    assert!(producer_stdout.contains("\"module\":false"));

    let pristine = std::fs::read(&snapshot).expect("read the standalone snapshot product");
    assert!(!pristine.is_empty());
    let checked = run_fln(&[Path::new("check-olean"), Path::new("--json"), &snapshot]);
    assert!(
        checked.status.success(),
        "snapshot checker stderr: {}",
        utf8(&checked.stderr)
    );
    assert!(checked.stderr.is_empty());
    assert!(utf8(&checked.stdout).contains("\"schema\":\"fln.check-olean/1\""));
    assert!(utf8(&checked.stdout).contains("\"outcome\":\"complete\""));
    assert!(utf8(&checked.stdout).contains("\"authority\":true"));

    let failed_source = root.join("Failed.lean");
    let failed_snapshot = root.join("Failed.olean");
    std::fs::write(
        &failed_source,
        b"#eval 40 + 2\ndef broken : Nat := missing\n",
    )
    .expect("write a late failing snapshot source");
    let refused = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-olean-snapshot"),
        &failed_snapshot,
        &failed_source,
    ]);
    assert!(!refused.status.success());
    assert!(refused.stdout.is_empty());
    assert!(utf8(&refused.stderr).contains("\"class\":\"execution\""));
    assert!(matches!(
        std::fs::symlink_metadata(&failed_snapshot),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound
    ));

    let collision = root.join("Collision.olean");
    let sentinel = b"preexisting snapshot sentinel";
    std::fs::write(&collision, sentinel).expect("write a collision sentinel");
    let collided = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-olean-snapshot"),
        &collision,
        &source,
    ]);
    assert!(!collided.status.success());
    assert!(collided.stdout.is_empty());
    assert!(utf8(&collided.stderr).contains("\"class\":\"output\""));
    assert_eq!(
        std::fs::read(&collision).expect("read the retained collision sentinel"),
        sentinel
    );

    let mut corrupt = pristine.clone();
    corrupt[0] ^= 0xff;
    std::fs::write(&snapshot, &corrupt).expect("plant corrupted snapshot bytes");
    let corrupted = run_fln(&[Path::new("check-olean"), Path::new("--json"), &snapshot]);
    assert!(!corrupted.status.success());
    assert!(corrupted.stdout.is_empty());
    assert!(utf8(&corrupted.stderr).contains("\"class\":\"decode\""));
    assert!(utf8(&corrupted.stderr).contains("\"authority\":false"));

    std::fs::write(&snapshot, &pristine).expect("restore exact snapshot bytes");
    let recovered = run_fln(&[Path::new("check-olean"), Path::new("--json"), &snapshot]);
    assert!(
        recovered.status.success(),
        "restored snapshot checker stderr: {}",
        utf8(&recovered.stderr)
    );
    assert!(recovered.stderr.is_empty());
    assert!(utf8(&recovered.stdout).contains("\"outcome\":\"complete\""));
}

#[test]
fn source_import_closure_reaches_the_real_binary_and_refuses_open_graphs() {
    let root = fresh_test_root("source-import-closure-e2e")
        .expect("allocate retained source-import integration-test directory");
    let project = root.join("Project");
    std::fs::create_dir(&project).expect("create module namespace directory");
    let base = project.join("Base.lean");
    let middle = project.join("Middle.lean");
    let main = root.join("Main.lean");
    let product = root.join("Main.flbc");
    std::fs::write(&base, b"def base : Nat := 20\n").expect("write base module");
    std::fs::write(
        &middle,
        b"import Project.Base\ndef middle : Nat := Nat.mul base 2\n",
    )
    .expect("write middle module");
    std::fs::write(
        &main,
        b"import Project.Middle\ndef verified : Bool := middle + 2 == 42\n#eval middle + 2\n",
    )
    .expect("write evaluating entry module");

    let produced = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &product,
        &middle,
        &base,
        &main,
    ]);
    assert!(
        produced.status.success(),
        "module producer stderr: {}",
        utf8(&produced.stderr)
    );
    assert!(produced.stderr.is_empty());
    let stdout = utf8(&produced.stdout);
    assert!(stdout.contains("\"schema\":\"fln.source-run/9\""));
    assert!(stdout.contains("\"commands\":4"));
    assert!(stdout.contains("\"definitions\":3"));
    assert!(stdout.contains("\"evaluations\":1"));
    assert!(stdout.contains("\"finalValue\":42"));

    let consumed = run_fln(&[
        Path::new("flbc"),
        Path::new("run"),
        Path::new("--json"),
        &product,
    ]);
    assert!(
        consumed.status.success(),
        "module consumer stderr: {}",
        utf8(&consumed.stderr)
    );
    assert!(consumed.stderr.is_empty());
    assert!(utf8(&consumed.stdout).contains("\"returnValue\":42"));

    let discovered_product = root.join("Discovered.flbc");
    let discovered = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &discovered_product,
        &main,
    ]);
    assert!(
        discovered.status.success(),
        "fln run import discovery stderr: {}",
        utf8(&discovered.stderr)
    );
    assert!(discovered.stderr.is_empty());
    let discovered_stdout = utf8(&discovered.stdout);
    assert!(discovered_stdout.contains("\"commands\":4"));
    assert!(discovered_stdout.contains("\"definitions\":3"));
    assert!(discovered_stdout.contains("\"evaluations\":1"));
    assert!(discovered_stdout.contains("\"finalValue\":42"));
    let consumed_discovered = run_fln(&[
        Path::new("flbc"),
        Path::new("run"),
        Path::new("--json"),
        &discovered_product,
    ]);
    assert!(
        consumed_discovered.status.success(),
        "discovered product consumer stderr: {}",
        utf8(&consumed_discovered.stderr)
    );
    assert!(consumed_discovered.stderr.is_empty());
    assert!(utf8(&consumed_discovered.stdout).contains("\"returnValue\":42"));

    let base_before_alias = std::fs::read(&base).expect("read the imported source before aliasing");
    let alias = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &base,
        &main,
    ]);
    assert!(!alias.status.success());
    assert!(alias.stdout.is_empty());
    assert!(utf8(&alias.stderr).contains("\"class\":\"output\""));
    assert!(utf8(&alias.stderr).contains("aliases discovered source input"));
    assert_eq!(
        std::fs::read(&base).expect("read the imported source after alias refusal"),
        base_before_alias
    );

    let native = run_lean(&[&main]);
    assert!(
        native.status.success(),
        "native lean import discovery stderr: {}",
        utf8(&native.stderr)
    );
    assert_eq!(utf8(&native.stdout), "42\n");
    assert!(native.stderr.is_empty());

    std::fs::write(
        &main,
        b"import Project.Middle\n#check middle\n#eval middle + 2\ndef answer : Nat := middle + 3\n#check answer\n#eval answer\n",
    )
    .expect("write a mixed imported entry command stream");
    let mixed_native = run_lean(&[&main]);
    assert!(
        mixed_native.status.success(),
        "mixed imported native lean stderr: {}",
        utf8(&mixed_native.stderr)
    );
    assert_eq!(
        utf8(&mixed_native.stdout),
        "middle : Nat\n42\nanswer : Nat\n43\n"
    );
    assert!(mixed_native.stderr.is_empty());

    std::fs::write(
        &main,
        b"import Project.Middle\n#check later\ndef later : Nat := middle\n",
    )
    .expect("plant a future-definition imported entry query");
    let future_entry = run_lean(&[&main]);
    assert!(!future_entry.status.success());
    assert!(future_entry.stdout.is_empty());
    assert!(utf8(&future_entry.stderr).starts_with("lean: execution: "));
    assert!(utf8(&future_entry.stderr).contains("no inferable type"));

    std::fs::write(&base, b"#eval 99\ndef base : Nat := 20\n")
        .expect("plant an output-producing imported dependency");
    std::fs::write(&main, b"import Project.Base\n#check base\n")
        .expect("write an entry over the noisy dependency");
    let noisy_dependency = run_lean(&[&main]);
    assert!(
        noisy_dependency.status.success(),
        "silent dependency evaluation stderr: {}",
        utf8(&noisy_dependency.stderr)
    );
    assert_eq!(utf8(&noisy_dependency.stdout), "base : Nat\n");
    assert!(noisy_dependency.stderr.is_empty());

    std::fs::write(&base, b"def base : Nat := 20\n").expect("restore the base dependency");
    std::fs::write(
        &main,
        b"import Project.Middle\ndef verified : Bool := middle + 2 == 42\n#eval middle + 2\n",
    )
    .expect("restore the evaluating entry after mixed command controls");

    let dependency_probe = root.join("DependencyProbe.lean");
    std::fs::write(
        &dependency_probe,
        b"import Project.Middle Project.Base Project.Middle\ntheorem bodyIsNotExecuted : Nat := missing\n",
    )
    .expect("write the direct source-dependency probe");
    let dependencies = run_lean(&[
        Path::new("--quiet"),
        Path::new("--src-deps"),
        &dependency_probe,
    ]);
    assert!(
        dependencies.status.success(),
        "native lean --src-deps stderr: {}",
        utf8(&dependencies.stderr)
    );
    assert!(dependencies.stderr.is_empty());
    assert_eq!(
        utf8(&dependencies.stdout),
        format!(
            "{}\n{}\n{}\n",
            middle.display(),
            base.display(),
            middle.display()
        )
    );

    let dependency_budget_stop = run_lean(&[
        Path::new("--src-deps"),
        Path::new("--max-bytes=1"),
        &dependency_probe,
    ]);
    assert!(!dependency_budget_stop.status.success());
    assert!(dependency_budget_stop.stdout.is_empty());
    assert!(utf8(&dependency_budget_stop.stderr).starts_with("lean: resource: "));
    assert!(
        utf8(&dependency_budget_stop.stderr).contains("source import closure exceeded the 1-byte")
    );

    let missing_dependency_probe = root.join("MissingDependencyProbe.lean");
    std::fs::write(
        &missing_dependency_probe,
        b"import Project.Middle Project.Absent\ntheorem bodyIsStillNotExecuted : Nat := missing\n",
    )
    .expect("write the missing direct source-dependency probe");
    let missing_dependencies = run_lean(&[Path::new("--src-deps"), &missing_dependency_probe]);
    assert!(!missing_dependencies.status.success());
    assert!(missing_dependencies.stdout.is_empty());
    assert!(utf8(&missing_dependencies.stderr).starts_with("lean: input: "));
    assert!(utf8(&missing_dependencies.stderr).contains("Project.Absent"));

    let dependencies_after_refusal = run_lean(&[Path::new("--src-deps"), &dependency_probe]);
    assert!(dependencies_after_refusal.status.success());
    assert_eq!(
        dependencies_after_refusal.stdout, dependencies.stdout,
        "a missing dependency refusal must not poison a later listing"
    );
    assert!(dependencies_after_refusal.stderr.is_empty());

    std::fs::write(
        &main,
        b"import Project.Middle\n#eval middle + 2\ndef broken : Nat := missing\n",
    )
    .expect("plant a late entry failure after a discovered evaluation");
    let late_refusal = run_lean(&[&main]);
    assert!(!late_refusal.status.success());
    assert!(late_refusal.stdout.is_empty());
    assert!(utf8(&late_refusal.stderr).starts_with("lean: execution: "));
    assert!(utf8(&late_refusal.stderr).contains("unknown constant"));

    let late_product = root.join("LateFailure.flbc");
    let late_fln = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &late_product,
        &main,
    ]);
    assert!(!late_fln.status.success());
    assert!(late_fln.stdout.is_empty());
    assert!(utf8(&late_fln.stderr).contains("\"class\":\"execution\""));
    assert!(matches!(
        std::fs::symlink_metadata(&late_product),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound
    ));

    std::fs::write(
        &main,
        b"import Project.Middle\ndef verified : Bool := middle + 2 == 42\n#eval middle + 2\n",
    )
    .expect("restore the checked import entry");

    let entry_only_limit = format!(
        "--max-bytes={}",
        std::fs::read(&main)
            .expect("read the import entry for its exact byte length")
            .len()
    );
    let exhausted = run_lean(&[Path::new(&entry_only_limit), &main]);
    assert!(!exhausted.status.success());
    assert!(exhausted.stdout.is_empty());
    assert!(utf8(&exhausted.stderr).starts_with("lean: resource: "));
    assert!(utf8(&exhausted.stderr).contains("source import closure"));

    std::fs::write(&middle, b"import Project.Absent\ndef middle : Nat := 40\n")
        .expect("plant a missing transitive import");
    let open_native = run_lean(&[&main]);
    assert!(!open_native.status.success());
    assert!(open_native.stdout.is_empty());
    assert!(utf8(&open_native.stderr).starts_with("lean: input: "));
    assert!(utf8(&open_native.stderr).contains("Project.Absent"));

    std::fs::write(
        &middle,
        b"import Project.Base\ndef middle : Nat := Nat.mul base 2\n",
    )
    .expect("restore the transitive import closure");
    let recovered_native = run_lean(&[&main]);
    assert!(
        recovered_native.status.success(),
        "recovered native lean import stderr: {}",
        utf8(&recovered_native.stderr)
    );
    assert_eq!(utf8(&recovered_native.stdout), "42\n");
    assert!(recovered_native.stderr.is_empty());

    let nested = root.join("Nested");
    let nested_project = nested.join("Project");
    std::fs::create_dir_all(&nested_project).expect("create the nearer ambiguous import namespace");
    let nested_base = nested_project.join("Base.lean");
    let ambiguous_main = nested.join("Ambiguous.lean");
    std::fs::write(&nested_base, b"def base : Nat := 99\n")
        .expect("write the nearer ambiguous module");
    std::fs::write(&ambiguous_main, b"import Project.Base\n#eval base\n")
        .expect("write an entry with two possible source roots");
    let ambiguous = run_lean(&[&ambiguous_main]);
    assert!(!ambiguous.status.success());
    assert!(ambiguous.stdout.is_empty());
    assert!(utf8(&ambiguous.stderr).starts_with("lean: input: "));
    assert!(utf8(&ambiguous.stderr).contains("is ambiguous"));
    assert!(utf8(&ambiguous.stderr).contains(&nested_base.display().to_string()));
    assert!(utf8(&ambiguous.stderr).contains(&base.display().to_string()));
    let ambiguous_dependencies = run_lean(&[Path::new("--src-deps"), &ambiguous_main]);
    assert!(!ambiguous_dependencies.status.success());
    assert!(ambiguous_dependencies.stdout.is_empty());
    assert!(utf8(&ambiguous_dependencies.stderr).starts_with("lean: input: "));
    assert!(utf8(&ambiguous_dependencies.stderr).contains("is ambiguous"));

    #[cfg(unix)]
    {
        let linked = root.join("Linked.lean");
        let linked_main = root.join("LinkedMain.lean");
        std::os::unix::fs::symlink(&base, &linked).expect("plant a source-import symlink");
        std::fs::write(&linked_main, b"import Linked\n#eval base\n")
            .expect("write an entry naming the source-import symlink");
        let refused_link = run_lean(&[&linked_main]);
        assert!(!refused_link.status.success());
        assert!(refused_link.stdout.is_empty());
        assert!(utf8(&refused_link.stderr).starts_with("lean: input: "));
        assert!(utf8(&refused_link.stderr).contains("refusing symlink source import"));
        let refused_link_dependencies = run_lean(&[Path::new("--src-deps"), &linked_main]);
        assert!(!refused_link_dependencies.status.success());
        assert!(refused_link_dependencies.stdout.is_empty());
        assert!(utf8(&refused_link_dependencies.stderr).starts_with("lean: input: "));
        assert!(utf8(&refused_link_dependencies.stderr).contains("refusing symlink source import"));
    }

    let interleaved_eval = root.join("InterleavedEval.lean");
    let interleaved_product = root.join("InterleavedEval.flbc");
    std::fs::write(
        &interleaved_eval,
        b"#eval Nat.add 40 2\ndef later : Nat := 7\n",
    )
    .expect("write an evaluation followed by a definition");
    let interleaved = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &interleaved_product,
        &interleaved_eval,
    ]);
    assert!(
        interleaved.status.success(),
        "interleaved #eval stderr: {}",
        utf8(&interleaved.stderr)
    );
    assert!(interleaved.stderr.is_empty());
    let interleaved_stdout = utf8(&interleaved.stdout);
    assert!(interleaved_stdout.contains("\"commands\":2"));
    assert!(interleaved_stdout.contains("\"definitions\":1"));
    assert!(interleaved_stdout.contains("\"evaluations\":1"));
    assert!(
        interleaved_stdout
            .contains("\"evaluationResults\":[{\"command\":0,\"kind\":\"nat\",\"value\":42}]")
    );
    assert!(interleaved_stdout.contains("\"finalValue\":7"));
    let pristine_product =
        std::fs::read(&interleaved_product).expect("read the interleaved final product");
    let consumed_interleaved = run_fln(&[
        Path::new("flbc"),
        Path::new("run"),
        Path::new("--json"),
        &interleaved_product,
    ]);
    assert!(
        consumed_interleaved.status.success(),
        "interleaved consumer stderr: {}",
        utf8(&consumed_interleaved.stderr)
    );
    assert!(consumed_interleaved.stderr.is_empty());
    assert!(utf8(&consumed_interleaved.stdout).contains("\"returnValue\":7"));

    let failed_product = root.join("FailedInterleavedEval.flbc");
    std::fs::write(
        &interleaved_eval,
        b"#eval Nat.add 40 2\ndef later : Nat := missing\n",
    )
    .expect("plant a later checked-definition failure");
    let failed_interleaved = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &failed_product,
        &interleaved_eval,
    ]);
    assert!(!failed_interleaved.status.success());
    assert!(failed_interleaved.stdout.is_empty());
    assert!(utf8(&failed_interleaved.stderr).contains("\"class\":\"execution\""));
    assert!(matches!(
        std::fs::symlink_metadata(&failed_product),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound
    ));

    let recovered_product = root.join("RecoveredInterleavedEval.flbc");
    std::fs::write(
        &interleaved_eval,
        b"#eval Nat.add 40 2\ndef later : Nat := 7\n",
    )
    .expect("restore the interleaved source bytes");
    let recovered_eval = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &recovered_product,
        &interleaved_eval,
    ]);
    assert!(
        recovered_eval.status.success(),
        "recovered #eval stderr: {}",
        utf8(&recovered_eval.stderr)
    );
    assert!(recovered_eval.stderr.is_empty());
    let recovered_stdout = utf8(&recovered_eval.stdout);
    assert!(recovered_stdout.contains("\"commands\":2"));
    assert!(recovered_stdout.contains("\"definitions\":1"));
    assert!(recovered_stdout.contains("\"evaluations\":1"));
    assert!(recovered_stdout.contains("\"finalValue\":7"));
    assert_eq!(
        std::fs::read(&recovered_product).expect("read the recovered final product"),
        pristine_product
    );

    let empty_entry = root.join("EmptyEntry.lean");
    let empty_entry_product = root.join("EmptyEntry.flbc");
    std::fs::write(&empty_entry, b"import Project.Base\n")
        .expect("write imports-only entry module");
    let empty_entry_run = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &empty_entry_product,
        &base,
        &empty_entry,
    ]);
    assert!(!empty_entry_run.status.success());
    assert!(empty_entry_run.stdout.is_empty());
    let empty_entry_stderr = utf8(&empty_entry_run.stderr);
    assert!(empty_entry_stderr.contains("\"class\":\"module-graph\""));
    assert!(empty_entry_stderr.contains("\"authority\":false"));
    assert!(empty_entry_stderr.contains("contains no supported command to execute"));
    assert!(matches!(
        std::fs::symlink_metadata(&empty_entry_product),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound
    ));

    std::fs::write(
        &empty_entry,
        b"import Project.Base\ndef answer : Nat := Nat.add base 22\n",
    )
    .expect("repair entry module with an exact final definition");
    let repaired_entry = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &empty_entry_product,
        &base,
        &empty_entry,
    ]);
    assert!(
        repaired_entry.status.success(),
        "repaired entry stderr: {}",
        utf8(&repaired_entry.stderr)
    );
    assert!(repaired_entry.stderr.is_empty());
    assert!(utf8(&repaired_entry.stdout).contains("\"finalValue\":42"));
    assert!(
        !std::fs::read(&empty_entry_product)
            .expect("read repaired entry product")
            .is_empty()
    );

    let missing = root.join("MissingMain.lean");
    std::fs::write(&missing, b"import Project.Absent\ndef answer : Nat := 1\n")
        .expect("write open import graph");
    let refused = run_fln(&[Path::new("run"), Path::new("--json"), &missing]);
    assert!(!refused.status.success());
    assert!(refused.stdout.is_empty());
    let stderr = utf8(&refused.stderr);
    assert!(stderr.contains("\"class\":\"input\""));
    assert!(stderr.contains("\"authority\":false"));
    assert!(stderr.contains("Project.Absent"));

    let explicit_refused = run_fln(&[Path::new("run"), Path::new("--json"), &base, &missing]);
    assert!(!explicit_refused.status.success());
    assert!(explicit_refused.stdout.is_empty());
    let explicit_stderr = utf8(&explicit_refused.stderr);
    assert!(explicit_stderr.contains("\"class\":\"module-graph\""));
    assert!(explicit_stderr.contains("\"authority\":false"));
    assert!(explicit_stderr.contains("Project.Absent"));

    let cycle_dir = root.join("Cycle");
    std::fs::create_dir(&cycle_dir).expect("create cyclic module namespace");
    let cycle_a = cycle_dir.join("A.lean");
    let cycle_b = cycle_dir.join("B.lean");
    std::fs::write(&cycle_a, b"import Cycle.B\ndef a : Nat := 1\n")
        .expect("write first cyclic module");
    std::fs::write(&cycle_b, b"import Cycle.A\ndef b : Nat := 2\n")
        .expect("write second cyclic module");
    let cycled = run_fln(&[Path::new("run"), Path::new("--json"), &cycle_b, &cycle_a]);
    assert!(!cycled.status.success());
    assert!(cycled.stdout.is_empty());
    let stderr = utf8(&cycled.stderr);
    assert!(stderr.contains("\"class\":\"module-graph\""));
    assert!(stderr.contains("source import graph contains a cycle"));

    let native_cycle = run_lean(&[&cycle_a]);
    assert!(!native_cycle.status.success());
    assert!(native_cycle.stdout.is_empty());
    assert!(utf8(&native_cycle.stderr).starts_with("lean: module-graph: "));
    assert!(utf8(&native_cycle.stderr).contains("source import graph contains a cycle"));

    let provider = root.join("A.lean");
    let consumer = root.join("B.lean");
    let sibling_main = root.join("SiblingMain.lean");
    let sibling_product = root.join("SiblingMain.flbc");
    std::fs::write(&provider, b"def leaked : Nat := 40\n").expect("write sibling provider");
    std::fs::write(&consumer, b"def borrowed : Nat := Nat.add leaked 1\n")
        .expect("write sibling consumer without its import");
    std::fs::write(
        &sibling_main,
        b"import A\nimport B\ndef answer : Nat := Nat.add borrowed 1\n",
    )
    .expect("write sibling entry");
    let leaked = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &sibling_product,
        &consumer,
        &provider,
        &sibling_main,
    ]);
    assert!(!leaked.status.success());
    assert!(leaked.stdout.is_empty());
    let stderr = utf8(&leaked.stderr);
    assert!(stderr.contains("\"class\":\"module-graph\""));
    assert!(stderr.contains("declaration `borrowed` in module `B`"));
    assert!(stderr.contains("references `leaked` from module `A`"));
    assert!(matches!(
        std::fs::symlink_metadata(&sibling_product),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound
    ));

    std::fs::write(
        &consumer,
        b"import A\ndef borrowed : Nat := Nat.add leaked 1\n",
    )
    .expect("repair sibling consumer with an exact import");
    std::fs::write(
        &sibling_main,
        b"import B\ndef answer : Nat := Nat.add leaked 2\n",
    )
    .expect("exercise visibility through the repaired transitive import chain");
    let recovered = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &sibling_product,
        &provider,
        &consumer,
        &sibling_main,
    ]);
    assert!(
        recovered.status.success(),
        "repaired sibling graph stderr: {}",
        utf8(&recovered.stderr)
    );
    assert!(recovered.stderr.is_empty());
    assert!(utf8(&recovered.stdout).contains("\"finalValue\":42"));
    assert!(
        !std::fs::read(&sibling_product)
            .expect("read repaired sibling product")
            .is_empty()
    );
}

#[test]
fn source_product_crosses_the_filesystem_and_real_golem_consumer() {
    // ubs:ignore — test-only retained scratch discriminator, not a security token.
    let root = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(format!(
        "flbc-product-e2e-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    std::fs::create_dir(&root).expect("create fresh retained integration-test directory");
    let source = root.join("Answer.lean");
    let string_source = root.join("Message.lean");
    let string_metric_source = root.join("StringMetric.lean");
    let bounded_nat_source = root.join("BoundedNat.lean");
    let comparison_source = root.join("Comparison.lean");
    let bad_source = root.join("Open.lean");
    let product = root.join("Answer.flbc");
    let string_product = root.join("Message.flbc");
    let string_metric_product = root.join("StringMetric.flbc");
    let bounded_nat_product = root.join("BoundedNat.flbc");
    let comparison_product = root.join("Comparison.flbc");
    let failed_product = root.join("Failed.flbc");
    let collision = root.join("Collision.flbc");
    std::fs::write(
        &source,
        b"def product : Nat := 6 * 7\ndef incremented : Nat := product + 1\ndef answer : Nat := (incremented + 0) - 1\n",
    )
    .expect("write supported dependent source batch");
    std::fs::write(
        &string_source,
        "def copy (value : String) := value\ndef prefix := copy \"artifact\\n\"\ndef message := let output : String := copy prefix ++ \"β\"; output\n"
            .as_bytes(),
    )
    .expect("write supported String source");
    std::fs::write(
        &string_metric_source,
        "def answer := Nat.add (String.length \"βeta\") (String.utf8ByteSize \"βeta\")\n"
            .as_bytes(),
    )
    .expect("write supported String metric source");
    std::fs::write(
        &bounded_nat_source,
        b"def legacy := Nat.add (Nat.pred 9) (Nat.add (Nat.div 20 6) (Nat.add (Nat.mod 20 6) (Nat.add (Nat.gcd 48 18) (Nat.add (Nat.land 12 10) (Nat.add (Nat.lor 12 10) (Nat.xor 12 10))))))\ndef power := Nat.pow 3 4\ndef shifted := Nat.add (Nat.shiftLeft 7 3) (Nat.shiftRight 56 3)\ndef subtotal := Nat.add legacy (Nat.add power (Nat.add (Nat.log2 8) shifted))\ndef huge := 1208925819614629174706176\ndef answer := Nat.add huge subtotal\n",
    )
    .expect("write supported bounded Nat source");
    std::fs::write(
        &comparison_source,
        "def choose (left right : Bool) : Bool := left\n#eval false\ndef natEq : Bool := Nat.beq 42 42\ndef natLe : Bool := Nat.ble 41 42\ndef stringEq : Bool := String.decEq \"βeta\" \"βeta\"\ndef literal := true\ndef answer : Bool := choose (choose natEq natLe) (choose stringEq literal)\n"
            .as_bytes(),
    )
    .expect("write supported Bool comparison source");
    std::fs::write(&bad_source, b"def open (x : Nat) : Nat := x\n")
        .expect("write non-closed source");

    let failed = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &failed_product,
        &bad_source,
    ]);
    assert!(!failed.status.success());
    assert!(failed.stdout.is_empty());
    assert!(utf8(&failed.stderr).contains("\"schema\":\"fln.source-run/9\""));
    assert!(matches!(
        std::fs::symlink_metadata(&failed_product),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound
    ));

    let produced = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &product,
        &source,
    ]);
    assert!(
        produced.status.success(),
        "producer stderr: {}",
        utf8(&produced.stderr)
    );
    assert!(produced.stderr.is_empty());
    let producer_stdout = utf8(&produced.stdout);
    assert!(producer_stdout.contains("\"schema\":\"fln.source-run/9\""));
    assert!(producer_stdout.contains("\"definitions\":3"));
    assert!(producer_stdout.contains("\"finalValue\":42"));
    assert!(producer_stdout.contains("\"emittedFlbc\":{"));
    let original = std::fs::read(&product).expect("read emitted FLBC product");
    assert!(!original.is_empty());

    let sentinel = b"retained collision sentinel";
    fln::publish_file_atomic(sentinel, &collision).expect("seed existing output");
    let collided = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &collision,
        &source,
    ]);
    assert!(!collided.status.success());
    assert!(collided.stdout.is_empty());
    let collision_stderr = utf8(&collided.stderr);
    assert!(collision_stderr.contains("\"class\":\"output\""));
    assert!(collision_stderr.contains("create target link"));
    assert!(collision_stderr.contains("target not created"));
    assert!(collision_stderr.contains("File exists"));
    assert_eq!(
        std::fs::read(&collision).expect("read retained collision"),
        sentinel,
        "default product publication must never clobber an existing entry"
    );

    let source_before = std::fs::read(&source).expect("read source before alias attempt");
    let aliased = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &source,
        &source,
    ]);
    assert!(!aliased.status.success());
    assert!(aliased.stdout.is_empty());
    assert!(utf8(&aliased.stderr).contains("aliases source input"));
    assert_eq!(
        std::fs::read(&source).expect("read source after alias refusal"),
        source_before
    );

    let consumed = run_fln(&[
        Path::new("flbc"),
        Path::new("run"),
        Path::new("--json"),
        &product,
    ]);
    assert!(
        consumed.status.success(),
        "consumer stderr: {}",
        utf8(&consumed.stderr)
    );
    assert!(consumed.stderr.is_empty());
    let consumer_stdout = utf8(&consumed.stdout);
    assert!(consumer_stdout.contains("\"schema\":\"fln.flbc-run/3\""));
    assert!(consumer_stdout.contains("\"returnValue\":42"));

    let string_produced = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &string_product,
        &string_source,
    ]);
    assert!(
        string_produced.status.success(),
        "String producer stderr: {}",
        utf8(&string_produced.stderr)
    );
    assert!(string_produced.stderr.is_empty());
    let string_producer_stdout = utf8(&string_produced.stdout);
    assert!(string_producer_stdout.contains("\"definitions\":3"));
    assert!(string_producer_stdout.contains("\"finalKind\":\"string\""));
    assert!(string_producer_stdout.contains("\"finalValue\":\"artifact\\nβ\""));
    assert!(string_producer_stdout.contains("\"emittedFlbc\":{"));
    let original_string = std::fs::read(&string_product).expect("read emitted String FLBC product");
    assert!(!original_string.is_empty());

    let string_consumed = run_fln(&[
        Path::new("flbc"),
        Path::new("run"),
        Path::new("--json"),
        &string_product,
    ]);
    assert!(
        string_consumed.status.success(),
        "String consumer stderr: {}",
        utf8(&string_consumed.stderr)
    );
    assert!(string_consumed.stderr.is_empty());
    let string_consumer_stdout = utf8(&string_consumed.stdout).to_owned();
    assert!(string_consumer_stdout.contains("\"schema\":\"fln.flbc-run/3\""));
    assert!(string_consumer_stdout.contains("\"returnKind\":\"string\""));
    assert!(string_consumer_stdout.contains("\"returnValue\":\"artifact\\nβ\""));

    let string_metric_produced = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &string_metric_product,
        &string_metric_source,
    ]);
    assert!(
        string_metric_produced.status.success(),
        "String metric producer stderr: {}",
        utf8(&string_metric_produced.stderr)
    );
    assert!(string_metric_produced.stderr.is_empty());
    let string_metric_stdout = utf8(&string_metric_produced.stdout);
    assert!(string_metric_stdout.contains("\"definitions\":1"));
    assert!(string_metric_stdout.contains("\"finalValue\":9"));
    let string_metric_consumed = run_fln(&[
        Path::new("flbc"),
        Path::new("run"),
        Path::new("--json"),
        &string_metric_product,
    ]);
    assert!(
        string_metric_consumed.status.success(),
        "String metric consumer stderr: {}",
        utf8(&string_metric_consumed.stderr)
    );
    assert!(string_metric_consumed.stderr.is_empty());
    assert!(utf8(&string_metric_consumed.stdout).contains("\"returnValue\":9"));

    let bounded_nat_produced = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &bounded_nat_product,
        &bounded_nat_source,
    ]);
    assert!(
        bounded_nat_produced.status.success(),
        "bounded Nat producer stderr: {}",
        utf8(&bounded_nat_produced.stderr)
    );
    assert!(bounded_nat_produced.stderr.is_empty());
    let bounded_nat_stdout = utf8(&bounded_nat_produced.stdout);
    assert!(bounded_nat_stdout.contains("\"definitions\":6"));
    assert!(bounded_nat_stdout.contains("\"finalValue\":1208925819614629174706370"));
    let bounded_nat_consumed = run_fln(&[
        Path::new("flbc"),
        Path::new("run"),
        Path::new("--json"),
        &bounded_nat_product,
    ]);
    assert!(
        bounded_nat_consumed.status.success(),
        "bounded Nat consumer stderr: {}",
        utf8(&bounded_nat_consumed.stderr)
    );
    assert!(bounded_nat_consumed.stderr.is_empty());
    assert!(
        utf8(&bounded_nat_consumed.stdout).contains("\"returnValue\":1208925819614629174706370")
    );

    let comparison_produced = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &comparison_product,
        &comparison_source,
    ]);
    assert!(
        comparison_produced.status.success(),
        "comparison producer stderr: {}",
        utf8(&comparison_produced.stderr)
    );
    assert!(comparison_produced.stderr.is_empty());
    let comparison_stdout = utf8(&comparison_produced.stdout);
    assert!(comparison_stdout.contains("\"definitions\":6"));
    assert!(comparison_stdout.contains("\"evaluations\":1"));
    assert!(
        comparison_stdout
            .contains("\"evaluationResults\":[{\"command\":1,\"kind\":\"bool\",\"value\":false}]")
    );
    assert!(comparison_stdout.contains("\"finalKind\":\"bool\""));
    assert!(comparison_stdout.contains("\"finalValue\":true"));
    let comparison_consumed = run_fln(&[
        Path::new("flbc"),
        Path::new("run"),
        Path::new("--json"),
        &comparison_product,
    ]);
    assert!(
        comparison_consumed.status.success(),
        "comparison consumer stderr: {}",
        utf8(&comparison_consumed.stderr)
    );
    assert!(comparison_consumed.stderr.is_empty());
    assert!(utf8(&comparison_consumed.stdout).contains("\"returnValue\":1"));

    let mut corrupt_string = original_string.clone();
    corrupt_string[0] ^= 0xff;
    fln::publish_file_atomic(&corrupt_string, &string_product)
        .expect("publish planted String corruption");
    let string_rejected = run_fln(&[
        Path::new("flbc"),
        Path::new("run"),
        Path::new("--json"),
        &string_product,
    ]);
    assert!(!string_rejected.status.success());
    assert!(string_rejected.stdout.is_empty());
    let string_rejected_stderr = utf8(&string_rejected.stderr);
    assert!(string_rejected_stderr.contains("\"schema\":\"fln.flbc-run/3\""));
    assert!(string_rejected_stderr.contains("\"class\":\"codec\""));
    assert!(string_rejected_stderr.contains("FLBC artifact magic mismatch"));

    fln::publish_file_atomic(&original_string, &string_product)
        .expect("restore exact String product bytes");
    assert_eq!(
        std::fs::read(&string_product).expect("read restored String product"),
        original_string
    );
    let string_recovered = run_fln(&[
        Path::new("flbc"),
        Path::new("run"),
        Path::new("--json"),
        &string_product,
    ]);
    assert!(
        string_recovered.status.success(),
        "String recovery stderr: {}",
        utf8(&string_recovered.stderr)
    );
    assert!(string_recovered.stderr.is_empty());
    assert_eq!(utf8(&string_recovered.stdout), string_consumer_stdout);

    let mut corrupt = original.clone();
    corrupt[0] ^= 0xff;
    fln::publish_file_atomic(&corrupt, &product).expect("publish planted corruption");
    let rejected = run_fln(&[
        Path::new("flbc"),
        Path::new("run"),
        Path::new("--json"),
        &product,
    ]);
    assert!(!rejected.status.success());
    assert!(rejected.stdout.is_empty());
    let rejected_stderr = utf8(&rejected.stderr);
    assert!(rejected_stderr.contains("\"schema\":\"fln.flbc-run/3\""));
    assert!(rejected_stderr.contains("\"class\":\"codec\""));
    assert!(rejected_stderr.contains("FLBC artifact magic mismatch"));

    fln::publish_file_atomic(&original, &product).expect("restore exact product bytes");
    assert_eq!(
        std::fs::read(&product).expect("read restored product"),
        original
    );
    let recovered = run_fln(&[
        Path::new("flbc"),
        Path::new("run"),
        Path::new("--json"),
        &product,
    ]);
    assert!(
        recovered.status.success(),
        "recovery stderr: {}",
        utf8(&recovered.stderr)
    );
    assert!(recovered.stderr.is_empty());
    assert!(utf8(&recovered.stdout).contains("\"returnValue\":42"));
}

/// Real-process D18 increment for the live `fln-cli` product root.
///
/// This proves the sidecar that the CLI actually emits: two isolated producer
/// invocations are byte-identical, the sound consumer binds that pair, a
/// frontier-tagged sidecar and a 12-component (omitted-closure) sidecar are
/// both refused before Golem runs, and restoring the original pair recovers.
/// Concurrent consumers of the restored pair return identical JSON.
///
/// It does not claim a certified profile, mode-separated cache reuse, 1/8/32
/// engine scheduling, or general Lean. Those remain open on
/// `fln-d18-product-half-rgsg`.
#[test]
fn d18_sidecar_isolated_rebuilds_refuse_plants_and_recover() {
    // ubs:ignore — test-only retained scratch discriminator, not a security token.
    let root = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(format!(
        "d18-sidecar-e2e-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    std::fs::create_dir(&root).expect("create retained D18 integration-test directory");
    let source = root.join("Answer.lean");
    std::fs::write(
        &source,
        b"def product : Nat := Nat.mul 6 7\ndef incremented : Nat := Nat.add product 1\ndef answer : Nat := Nat.sub (Nat.add incremented 0) 1\n",
    )
    .expect("write supported dependent source batch");

    let first_product = root.join("first.flbc");
    let first_sidecar = root.join("first.sidecar");
    let second_product = root.join("second.flbc");
    let second_sidecar = root.join("second.sidecar");

    let first = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &first_product,
        Path::new("--emit-sidecar"),
        &first_sidecar,
        &source,
    ]);
    assert!(
        first.status.success(),
        "first isolated producer stderr: {}",
        utf8(&first.stderr)
    );
    assert!(first.stderr.is_empty());
    let first_stdout = utf8(&first.stdout);
    assert!(first_stdout.contains("\"schema\":\"fln.source-run/9\""));
    assert!(first_stdout.contains("\"finalValue\":42"));
    assert!(first_stdout.contains("\"emittedSidecar\":{"));
    assert!(first_stdout.contains("\"profile\":\"standard\""));

    let second = run_fln(&[
        Path::new("run"),
        Path::new("--json"),
        Path::new("--emit-flbc"),
        &second_product,
        Path::new("--emit-sidecar"),
        &second_sidecar,
        &source,
    ]);
    assert!(
        second.status.success(),
        "second isolated producer stderr: {}",
        utf8(&second.stderr)
    );
    assert!(second.stderr.is_empty());
    let product = std::fs::read(&first_product).expect("read first product");
    let sidecar = std::fs::read(&first_sidecar).expect("read first sidecar");
    assert_eq!(
        product,
        std::fs::read(&second_product).expect("read second product"),
        "two isolated standard-profile builds must emit byte-identical FLBC"
    );
    assert_eq!(
        sidecar,
        std::fs::read(&second_sidecar).expect("read second sidecar"),
        "two isolated standard-profile builds must emit byte-identical sidecars"
    );
    assert!(!product.is_empty());
    assert!(!sidecar.is_empty());
    fln::decode_flbc_product_sidecar(&sidecar).expect("emitted sidecar decodes");

    let bound = run_fln(&[
        Path::new("flbc"),
        Path::new("run"),
        Path::new("--json"),
        Path::new("--sidecar"),
        &first_sidecar,
        &first_product,
    ]);
    assert!(
        bound.status.success(),
        "bound consumer stderr: {}",
        utf8(&bound.stderr)
    );
    assert!(bound.stderr.is_empty());
    let bound_stdout = utf8(&bound.stdout).to_owned();
    assert!(bound_stdout.contains("\"schema\":\"fln.flbc-run/3\""));
    assert!(bound_stdout.contains("\"returnValue\":42"));
    assert!(bound_stdout.contains("\"sidecar\":{\"verified\":true"));

    let mode_at = sidecar_mode_offset(&sidecar);
    assert_eq!(sidecar[mode_at], 2, "producer emits the sound mode tag");
    let mut frontier = sidecar.clone();
    frontier[mode_at] = 3;
    fln::publish_file_atomic(&frontier, &first_sidecar).expect("plant frontier-tagged sidecar");
    let contaminated = run_fln(&[
        Path::new("flbc"),
        Path::new("run"),
        Path::new("--json"),
        Path::new("--sidecar"),
        &first_sidecar,
        &first_product,
    ]);
    assert!(!contaminated.status.success());
    assert!(contaminated.stdout.is_empty());
    let contaminated_stderr = utf8(&contaminated.stderr);
    assert!(contaminated_stderr.contains("\"schema\":\"fln.flbc-run/3\""));
    assert!(contaminated_stderr.contains("\"class\":\"sidecar\""));
    assert!(contaminated_stderr.contains("product coordinate mode"));

    fln::publish_file_atomic(&sidecar, &first_sidecar).expect("restore exact sidecar");
    let after_frontier = run_fln(&[
        Path::new("flbc"),
        Path::new("run"),
        Path::new("--json"),
        Path::new("--sidecar"),
        &first_sidecar,
        &first_product,
    ]);
    assert!(
        after_frontier.status.success(),
        "post-frontier recovery stderr: {}",
        utf8(&after_frontier.stderr)
    );
    assert_eq!(utf8(&after_frontier.stdout), bound_stdout);

    let count_at = sidecar_component_count_offset(&sidecar);
    let mut omitted = sidecar.clone();
    omitted[count_at..count_at + 8].copy_from_slice(&12_u64.to_le_bytes());
    let planted = fln::decode_flbc_product_sidecar(&omitted)
        .expect_err("a 12-component sidecar must not decode");
    let planted_text = planted.to_string();
    assert!(
        planted_text.contains("all 13 closure components"),
        "component-count plant must be the omission refusal, not a nearby field: {planted_text}"
    );
    fln::publish_file_atomic(&omitted, &first_sidecar).expect("plant omitted-closure sidecar");
    let omitted_run = run_fln(&[
        Path::new("flbc"),
        Path::new("run"),
        Path::new("--json"),
        Path::new("--sidecar"),
        &first_sidecar,
        &first_product,
    ]);
    assert!(!omitted_run.status.success());
    assert!(omitted_run.stdout.is_empty());
    let omitted_stderr = utf8(&omitted_run.stderr);
    assert!(
        omitted_stderr.contains("\"class\":\"sidecar\""),
        "omitted-closure consumer stderr: {omitted_stderr}"
    );
    assert!(
        omitted_stderr.contains("all 13 closure components"),
        "omitted-closure consumer must quote the planted decode refusal: {omitted_stderr}"
    );

    fln::publish_file_atomic(&sidecar, &first_sidecar)
        .expect("restore exact sidecar after omission");
    let recovered = run_fln(&[
        Path::new("flbc"),
        Path::new("run"),
        Path::new("--json"),
        Path::new("--sidecar"),
        &first_sidecar,
        &first_product,
    ]);
    assert!(
        recovered.status.success(),
        "post-omission recovery stderr: {}",
        utf8(&recovered.stderr)
    );
    assert_eq!(utf8(&recovered.stdout), bound_stdout);

    let product_path = first_product.clone();
    let sidecar_path = first_sidecar.clone();
    let expected = bound_stdout.clone();
    std::thread::scope(|scope| {
        let handles: Vec<_> = (0..3)
            .map(|_| {
                let product_path = product_path.clone();
                let sidecar_path = sidecar_path.clone();
                let expected = expected.clone();
                scope.spawn(move || {
                    let output = run_fln(&[
                        Path::new("flbc"),
                        Path::new("run"),
                        Path::new("--json"),
                        Path::new("--sidecar"),
                        &sidecar_path,
                        &product_path,
                    ]);
                    assert!(
                        output.status.success(),
                        "concurrent consumer stderr: {}",
                        utf8(&output.stderr)
                    );
                    assert_eq!(utf8(&output.stdout), expected);
                })
            })
            .collect();
        for handle in handles {
            handle.join().expect("concurrent consumer thread");
        }
    });
}

fn sidecar_schema_body_offset(bytes: &[u8]) -> usize {
    const NAME: &[u8] = b"fln.canon.flbc-product-sidecar";
    assert!(
        bytes.len() >= 10,
        "sidecar is too small to carry a schema header"
    );
    let name_len = usize::try_from(u64::from_le_bytes(
        bytes[0..8].try_into().expect("schema name length"),
    ))
    .expect("schema name length fits this host");
    let name_end = 8 + name_len;
    assert_eq!(
        &bytes[8..name_end],
        NAME,
        "plant offsets are only valid for the live sidecar schema"
    );
    name_end + 2
}

fn sidecar_mode_offset(bytes: &[u8]) -> usize {
    sidecar_schema_body_offset(bytes)
}

fn sidecar_component_count_offset(bytes: &[u8]) -> usize {
    // write_u128 is length-prefixed (`u64` length + 16 payload bytes), not a
    // bare 16-byte integer. After the mode tag: epoch, CGSE, determinism u8,
    // profile u8, target, build profile, then the component count.
    const PREFIXED_U128: usize = 8 + 16;
    sidecar_schema_body_offset(bytes)
        + 1
        + PREFIXED_U128
        + PREFIXED_U128
        + 1
        + 1
        + PREFIXED_U128
        + PREFIXED_U128
}
