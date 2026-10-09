//! `#guard_msgs` through the installed `lean` front door (bead `fln-guard-msgs-lls1`).
//!
//! The expected exit codes and stdout are the pinned v4.32.0's on the same files (measured
//! 2026-10-09):
//! - A matching `info:` passes silently, including a multi-line doc and a string value.
//! - An unguarded `#eval` around a guarded one still prints.
//! - An empty guard around a silent `def` passes.
//! - A mismatch is an error, exit 1.
//!
//! What this engine does not reproduce is refused with exit 5, never judged:
//! - an expectation with `error:`, `warning:` or `trace:` (their text is not the pin's here);
//! - a `(…)` spec (it changes which messages are checked);
//! - a guard over `#check` or an IO action.
#![forbid(unsafe_code)]
use std::{
    path::Path,
    process::{Command, Output},
    sync::atomic::{AtomicUsize, Ordering},
};

static NEXT: AtomicUsize = AtomicUsize::new(0);

fn lean(program: &str) -> Output {
    let dir = std::env::temp_dir().join(format!(
        "fln-guard-msgs-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&dir).unwrap();
    let source = dir.join("Main.lean");
    std::fs::write(&source, program).unwrap();
    run(&source)
}

fn run(source: &Path) -> Output {
    Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(source)
        .output()
        .unwrap()
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

#[test]
fn a_matching_guard_is_silent_and_its_neighbours_still_print() {
    for program in [
        "/-- info: 4 -/\n#guard_msgs in\n#eval 2 + 2\n",
        "/--\ninfo: 4\n-/\n#guard_msgs in\n#eval 2 + 2\n",
        "/-- info: \"ab\" -/\n#guard_msgs in\n#eval \"ab\"\n",
        "#guard_msgs in\ndef x : Nat := 1\n",
    ] {
        let output = lean(program);
        assert_eq!(output.status.code(), Some(0), "{program}\n{output:?}");
        assert_eq!(stdout(&output), "", "{program}");
    }
    let output = lean("#eval 1\n/-- info: 4 -/\n#guard_msgs in\n#eval 2 + 2\n#eval 3\n");
    assert_eq!(output.status.code(), Some(0), "{output:?}");
    assert_eq!(stdout(&output), "1\n3\n");
}

#[test]
fn a_mismatch_is_the_pins_error() {
    let output = lean("/-- info: 5 -/\n#guard_msgs in\n#eval 2 + 2\n");
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("Docstring on `#guard_msgs` does not match generated message"),
        "{stderr}"
    );
    assert!(stderr.contains("info: 4"), "{stderr}");
}

#[test]
fn what_this_engine_cannot_reproduce_is_refused_never_judged() {
    for (program, named) in [
        (
            "/-- error: boom -/\n#guard_msgs in\n#eval 2 + 2\n",
            "error, warning or trace",
        ),
        (
            "/-- info: 4 -/\n#guard_msgs (drop warning) in\n#eval 2 + 2\n",
            "specification",
        ),
        ("/-- info: 1 : Nat -/\n#guard_msgs in\n#check 1\n", "#check"),
    ] {
        let output = lean(program);
        assert_eq!(output.status.code(), Some(5), "{program}\n{output:?}");
        assert_eq!(stdout(&output), "", "{program}");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains(named), "{program}: {stderr}");
    }
}
