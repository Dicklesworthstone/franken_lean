//! Installed IO result presentation through the complete actual import loader.
//! All cases retain one Lean executable and record directory. This fixture does
//! not treat a selected-declaration environment as full module admission.
#![forbid(unsafe_code)]

use super::*;

const DEFINITIONS: &str = r#"prelude
import Init.System.IO
import Init.Data.Repr
structure PrintedIO where
  message : String
instance : Repr PrintedIO where
  reprPrec value _ := Std.Format.text value.message
"#;

fn assert_capability(run: &Run) {
    assert_eq!(run.code, 5, "{run:?}");
    assert!(run.stdout.is_empty(), "refused action ran: {run:?}");
    assert!(run.stderr.starts_with("lean: capability: "), "{run:?}");
}

fn lean_io(workspace: &Workspace, entry: &Path, lib: &Path) -> Run {
    // IO imports the full FilePath closure. Retain the same executable-bound
    // record store for all cases, with normal scheduling and execution limits.
    eprintln!("[checked IO CLI] start {}", entry.display());
    let output = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(entry)
        .env("LEAN_PATH", lib)
        .env("FLN_IMPORT_REUSE_DIR", full_io_records(workspace))
        .output()
        .expect("run the installed lean");
    let run = Run {
        code: output.status.code().expect("normal process exit"),
        stdout: String::from_utf8(output.stdout).unwrap(),
        stderr: String::from_utf8(output.stderr).unwrap(),
    };
    eprintln!("[checked IO CLI] exit {} for {}", run.code, entry.display());
    run
}

#[test]
fn checked_io_results_print_once_refuse_unprintable_actions_and_guard_their_output() {
    let Some(lib) = pinned_lib() else { return };
    let workspace = Workspace::new("lean-door-checked-io");
    let sentinel = workspace.write("sentinel.txt", "preserved");
    let source_path = format!(
        "(System.FilePath.mk {:?})",
        sentinel.to_str().expect("UTF-8 fixture path")
    );

    // The named action stays deferred until its one evaluation. Unit has no
    // result line; the record's checked printer uses its actual String field.
    let positive = workspace.write(
        "Printed.lean",
        format!(
            r#"{DEFINITIONS}def savedUnit : IO Unit := IO.println "unit-effect λ"
#eval savedUnit
#eval (show IO PrintedIO from do
  let stream ← IO.getStdout
  stream.putStr "record-effect λ\n"
  pure (PrintedIO.mk "\"io record λ\"\n"))
"#
        ),
    );
    let printed = lean_io(&workspace, &positive, &lib);
    assert_eq!(printed.code, 0, "{printed:?}");
    assert!(printed.stderr.is_empty(), "{printed:?}");
    assert_eq!(
        printed.stdout, "unit-effect λ\nrecord-effect λ\n\"io record λ\"\n",
        "{printed:?}"
    );

    // Exceptions keep their IO disposition. Effects completed before the
    // exception remain visible exactly once; no successful result is printed.
    let exception = workspace.write(
        "Exception.lean",
        format!(
            r#"{DEFINITIONS}#eval (show IO PrintedIO from do
  let stream ← IO.getStdout
  stream.putStr "before-exception\n"
  throw (IO.userError "expected exception λ"))
"#
        ),
    );
    let raised = lean_io(&workspace, &exception, &lib);
    assert_eq!(raised.code, 1, "{raised:?}");
    assert_eq!(raised.stdout, "before-exception\n", "{raised:?}");
    assert!(
        raised.stderr.starts_with("lean: io-exception: ")
            && raised.stderr.contains("expected exception λ"),
        "{raised:?}"
    );

    // Printer selection happens before this otherwise valid action can
    // overwrite the sentinel or write stdout. There is no scalar fallback.
    let missing = workspace.write(
        "MissingPrinter.lean",
        format!(
            r#"{DEFINITIONS}inductive UnprintedIO where
  | value
#eval (show IO UnprintedIO from do
  IO.FS.writeFile {source_path} "must not write"
  let stream ← IO.getStdout
  stream.putStr "must not print\n"
  pure UnprintedIO.value)
"#
        ),
    );
    let missing = lean_io(&workspace, &missing, &lib);
    assert_capability(&missing);
    assert!(
        missing
            .stderr
            .contains("requires an existing Repr or ToString instance"),
        "{missing:?}"
    );
    assert_eq!(std::fs::read(&sentinel).unwrap(), b"preserved");

    // An action's output is a message of its own, as the pin's `#eval` logs it from inside
    // `withIsolatedStreams`: printed where the command is (after an earlier command's
    // warning), judged by a guard over it, and dropped with `drop info`, while the action's
    // other effects happen. The expected bytes are the pinned v4.32.0's on this file
    // (measured 2026-10-21).
    let guarded = workspace.write(
        "Guarded.lean",
        format!(
            r#"{DEFINITIONS}def warned : Nat := sorry
#eval IO.println "first"
/-- info: guarded λ -/
#guard_msgs in
#eval (show IO Unit from do
  IO.FS.writeFile {source_path} "written"
  IO.println "guarded λ")
/--
info: y
---
info: printed record
-/
#guard_msgs in
#eval (show IO PrintedIO from do
  IO.print "y"
  pure (PrintedIO.mk "printed record"))
#guard_msgs (drop info) in
#eval IO.println "dropped"
#eval (show IO PrintedIO from do
  IO.print "no newline"
  pure (PrintedIO.mk "record"))
#eval IO.println "last"
"#
        ),
    );
    let ran = lean_io(&workspace, &guarded, &lib);
    let expected = format!(
        "{}:8:4: warning: declaration uses `sorry`\nfirst\nno newline\nrecord\nlast\n",
        guarded.display()
    );
    assert_eq!(
        (ran.code, ran.stdout.as_str(), ran.stderr.as_str()),
        (0, expected.as_str(), ""),
        "{ran:?}"
    );
    assert_eq!(std::fs::read(&sentinel).unwrap(), b"written");

    // A guard whose expectation the output does not match is an error, as at the pin.
    let mismatch = workspace.write(
        "Mismatch.lean",
        format!(
            "{DEFINITIONS}/-- info: expected -/\n#guard_msgs in\n#eval IO.println \"actual\"\n"
        ),
    );
    let failed = lean_io(&workspace, &mismatch, &lib);
    assert_eq!(failed.code, 1, "{failed:?}");
    assert!(failed.stderr.contains("info: actual"), "{failed:?}");
}
