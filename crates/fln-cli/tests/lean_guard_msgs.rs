//! `#guard_msgs` through the installed `lean` front door (bead `fln-guard-msgs-lls1`).
//!
//! The expected exit codes and stdout are the pinned v4.32.0's on the same files (measured
//! 2026-10-09):
//! - A matching `info:` passes silently, including a multi-line doc and a string value.
//! - A matching `#check` passes silently too. On ten `#check` shapes, from `1` to `@Nat.rec`'s
//!   full telescope, this door's line is byte-identical to the pin's.
//! - An unguarded `#eval` around a guarded one still prints.
//! - An empty guard around a silent `def` passes.
//! - A mismatch over `#eval` is an error, exit 1.
//!
//! What this engine does not reproduce is refused with exit 5, never judged:
//! - an expectation with `error:`, `warning:` or `trace:` (their text is not the pin's here);
//! - a `(…)` spec (it changes which messages are checked);
//! - a guard over an IO action;
//! - a mismatch over `#check`. Its rendering is not proven to be the pin's in general, so a
//!   difference may be this door's; the pin would report an error.
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
        "/-- info: 1 : Nat -/\n#guard_msgs in\n#check 1\n",
        "/-- info: fun x => x + 1 : Nat → Nat -/\n#guard_msgs in\n#check (fun (x : Nat) => x + 1)\n",
        // The pin's suite (`tests/elab/fieldNamesWithMinus.lean`): a name that is not an
        // identifier prints escaped, `«i-love-lisp»`.
        "structure Minus where\n  «i-love-lisp» : Bool\n/-- info: Minus.«i-love-lisp» (self : Minus) : Bool -/\n#guard_msgs in\n#check Minus.«i-love-lisp»\n",
        // `pp.proofs`: a proof that is not atomic is `⋯` inside a term that is not a proof,
        // and in full when the term printed is one. A promoted index binds `a`. The pin
        // passes all three guards (exit 0, silent).
        "inductive P : Nat → Prop where\n  | mk (n : Nat) : P n\n/-- info: @P.rec : {a : Nat} → {motive : P a → Sort u_1} → motive ⋯ → (t : P a) → motive t -/\n#guard_msgs in\n#check @P.rec\n",
        "inductive Q : Nat → Prop where\n  | zero : Q 0\n  | succ (n : Nat) : Q n → Q (n + 1)\n/-- info: Q.succ 0 Q.zero : Q (0 + 1) -/\n#guard_msgs in\n#check Q.succ 0 Q.zero\n/-- info: Q.succ : ∀ (n : Nat), Q n → Q (n + 1) -/\n#guard_msgs in\n#check @Q.succ\n",
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
        ("/-- info: 1 : Int -/\n#guard_msgs in\n#check 1\n", "#check"),
    ] {
        let output = lean(program);
        assert_eq!(output.status.code(), Some(5), "{program}\n{output:?}");
        assert_eq!(stdout(&output), "", "{program}");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains(named), "{program}: {stderr}");
    }
}
