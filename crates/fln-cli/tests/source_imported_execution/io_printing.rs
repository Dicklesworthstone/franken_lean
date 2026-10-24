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
        .env("LEAN_BACKTRACE", "0")
        .env_remove("LEAN_ABORT_ON_PANIC")
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
fn checked_io_results_print_once_and_guard_isolated_effects() {
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
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["run", "--json"])
        .arg(&exception)
        .env("LEAN_PATH", &lib)
        .env("FLN_IMPORT_REUSE_DIR", full_io_records(&workspace))
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert!(output.stdout.is_empty(), "{output:?}");
    let json = String::from_utf8(output.stderr).unwrap();
    assert!(json.starts_with('{') && json.ends_with("}\n"), "{json}");
    assert!(json.contains("\"class\":\"io-exception\""), "{json}");
    assert_eq!(json.matches("\"stdout\":").count(), 1, "{json}");
    assert!(
        json.contains("\"stdout\":\"before-exception\\n\""),
        "{json}"
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

    // Stream output is one info message before the separately printed value.
    // A guarded action really executes once, including non-stream effects;
    // the guard compares its isolated messages rather than suppressing IO.
    for (file, type_, result, expected) in [
        ("GuardUnit.lean", "Unit", "()", "info: guard-effect"),
        (
            "GuardFormat.lean",
            "PrintedIO",
            "PrintedIO.mk \"guard-value\"",
            "info: guard-effect\n---\ninfo: guard-value",
        ),
    ] {
        let guarded = workspace.write(
            file,
            format!(
                r#"{DEFINITIONS}/-- {expected} -/
#guard_msgs in
#eval (show IO {type_} from do
  IO.FS.writeFile {source_path} "guard ran"
  let stream ← IO.getStdout
  stream.putStr "guard-effect\n"
  pure ({result}))
"#
            ),
        );
        let checked = lean_io(&workspace, &guarded, &lib);
        assert_eq!(checked.code, 0, "{checked:?}");
        assert!(checked.stdout.is_empty(), "{checked:?}");
        assert!(checked.stderr.is_empty(), "{checked:?}");
        assert_eq!(std::fs::read(&sentinel).unwrap(), b"guard ran");
        if type_ == "Unit" {
            // FLBC publication validates guards on the PreferRaw route too.
            // A retained isolated transcript authorizes judging silent Unit;
            // it must not be mistaken for a Raw batch without that transcript.
            let artifact = workspace.0.join("guarded-unit.flbc");
            workspace
                .run(
                    &guarded,
                    Some(&lib),
                    &["--emit-flbc", artifact.to_str().unwrap()],
                )
                .complete();
            assert!(artifact.is_file());

            let wrong = workspace.write(
                "WrongGuardUnit.lean",
                format!("{DEFINITIONS}/-- info: different -/\n#guard_msgs in\n#eval IO.println \"guard-effect\"\n"),
            );
            let refused_artifact = workspace.0.join("wrong-guard-unit.flbc");
            workspace
                .run(
                    &wrong,
                    Some(&lib),
                    &["--emit-flbc", refused_artifact.to_str().unwrap()],
                )
                .refused("guard-msgs", 1);
            assert!(!refused_artifact.exists());
        }
    }

    let streams = workspace.write(
        "Streams.lean",
        format!(
            r#"{DEFINITIONS}#eval IO.print "first"
#eval IO.eprintln "second"
#eval (dbgTrace "traced" fun _ => (1 : Nat))
#eval (panicCore (7 : Nat) "recover")
#eval ([] : List Nat).head!
#eval "after"
"#
        ),
    );
    let captured = lean_io(&workspace, &streams, &lib);
    assert_eq!(captured.code, 0, "{captured:?}");
    assert!(captured.stderr.is_empty(), "{captured:?}");
    // The pin observation disables backtraces: compare the original message
    // and its stream, never host-dependent return addresses.
    let list_panic = "PANIC at List.head! Init.Data.List.BasicAux:80:12: empty list";
    assert_eq!(
        captured.stdout,
        format!("first\nsecond\ntraced\n1\nrecover\n7\n{list_panic}\n0\n\"after\"\n")
    );
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["run", "--json"])
        .arg(&streams)
        .env("LEAN_PATH", &lib)
        .env("FLN_IMPORT_REUSE_DIR", full_io_records(&workspace))
        .env("LEAN_BACKTRACE", "0")
        .env_remove("LEAN_ABORT_ON_PANIC")
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    let json = String::from_utf8(output.stdout).unwrap();
    assert!(json.starts_with('{') && json.ends_with("}\n"), "{json}");
    assert_eq!(json.matches("\"stdout\":").count(), 1, "{json}");
    assert!(
        json.contains(&format!(
            "\"stdout\":\"firstsecond\\ntraced\\nrecover\\n{list_panic}\\n\""
        )),
        "{json}"
    );
}
