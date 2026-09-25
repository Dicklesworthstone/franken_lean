//! Installed-command regressions: parsing alone is not evidence of a proof.

use std::fs::OpenOptions;
use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_INPUT: AtomicU64 = AtomicU64::new(0);

struct Input(PathBuf);

impl Drop for Input {
    fn drop(&mut self) {
        // This path was acquired with create_new; it is this test's file only.
        let _ = std::fs::remove_file(&self.0);
    }
}

fn check_source(source: &str) -> Output {
    let (input, mut file) = loop {
        let sequence = NEXT_INPUT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "fln-relation-tactics-{}-{sequence}.lean",
            std::process::id()
        ));
        match OpenOptions::new().write(true).create_new(true).open(&path) {
            Ok(file) => break (Input(path), file),
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(error) => panic!("cannot create relation-tactic input: {error}"),
        }
    };
    file.write_all(source.as_bytes()).expect("write source");
    drop(file);
    Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .arg(&input.0)
        .output()
        .expect("run the installed source checker")
}

fn accepted(source: &str) {
    let output = check_source(source);
    assert!(
        output.status.success(),
        "source was not admitted:\n{source}\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}

fn refused(source: &str) {
    let output = check_source(source);
    assert!(
        !output.status.success(),
        "unexpected source admission:\n{source}\n{}",
        String::from_utf8_lossy(&output.stdout),
    );
    assert_ne!(output.status.code(), Some(101), "checker panicked");
    assert!(output.status.code().is_some(), "checker was terminated");
}

#[test]
fn symm_builds_a_checked_equality_proof() {
    accepted("theorem reverse (a b : Nat) (h : b = a) : a = b := by\n  symm\n  exact h\n");
}

#[test]
fn symm_preserves_introduced_and_dependent_binders() {
    accepted("theorem reverse (a b : Nat) : b = a -> a = b := by\n  intro h\n  symm\n  exact h\n");
    accepted(
        "theorem reverse (A : Type) (F : A -> Type) (a : A) (x y : F a) (h : y = x) : x = y := by\n  symm\n  exact h\n",
    );
}

#[test]
fn repeated_symmetry_does_not_close_a_goal_by_itself() {
    accepted("theorem twice (a b : Nat) (h : a = b) : a = b := by\n  symm\n  symm\n  exact h\n");
    refused("theorem missing (a b : Nat) : a = b := by\n  symm\n");
    refused("theorem falseEquality : 0 = 1 := by\n  symm\n  rfl\n");
}

#[test]
fn symm_refuses_unsupported_goals_and_locations() {
    refused("theorem wrongGoal (P : Prop) : P := by\n  symm\n");
    refused("theorem unsupported (a b : Nat) (h : a = b) : a = b := by\n  symm at h\n  exact h\n");
}

#[test]
fn symm_remains_a_contextual_keyword() {
    accepted("def symm (a : Nat) : Nat := a\ntheorem useName (a : Nat) : symm a = a := by rfl\n");
}
