//! Installed and library CLI source-proof checking. No fake compiler or checker.
#![forbid(unsafe_code)]
use std::{
    ffi::OsString,
    path::PathBuf,
    process::Command,
    sync::atomic::{AtomicUsize, Ordering},
};
static NEXT: AtomicUsize = AtomicUsize::new(0);
fn file(text: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "fln-proof-check-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&dir).unwrap();
    let path = dir.join("proof.lean");
    std::fs::write(&path, text).unwrap();
    path
}
fn run(args: Vec<OsString>) -> fln_cli::MultiplexerOutput {
    fln_cli::run(args)
}
#[test]
fn installed_binary_checks_a_real_source_proof_file() {
    let path = file(
        "def identity (x : Nat) : Nat := x\ntheorem self (x : Nat) : identity x = x := by rfl\ntheorem symm (x y : Nat) (h : x = y) : y = x := by rw [h]\n",
    );
    let before = std::fs::read(&path).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .arg(&path)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let text = String::from_utf8(output.stdout).unwrap();
    for required in [
        "\"schema\":\"fln.source-check/1\"",
        "\"outcome\":\"complete\"",
        "\"authority\":true",
        "\"commands\":3",
        "\"theorems\":2",
        "\"executed\":false",
    ] {
        assert!(text.contains(required), "{text}");
    }
    assert!(output.stderr.is_empty());
    assert_eq!(std::fs::read(&path).unwrap(), before);
    assert_eq!(
        std::fs::read_dir(path.parent().unwrap()).unwrap().count(),
        1
    );
}
#[test]
fn later_files_can_use_prior_theorems_and_failure_emits_no_partial_success() {
    let one = file("theorem self (x : Nat) : x = x := by rfl");
    let two = file("theorem reuse (x : Nat) : x = x := by apply self");
    let args = vec![
        "check-source".into(),
        "--json".into(),
        one.clone().into_os_string(),
        two.clone().into_os_string(),
    ];
    let output = run(args.clone());
    assert_eq!(output.exit_code, 0, "{}", output.stderr);
    assert!(output.stdout.contains("\"files\":2"));
    std::fs::write(two, "theorem bad : 1 = 2 := by rfl").unwrap();
    let output = run(args);
    assert_eq!(output.exit_code, 1);
    assert!(output.stdout.is_empty());
    assert!(output.stderr.contains("\"outcome\":\"kernel-rejection\""));
    assert!(!output.stderr.contains("\"outcome\":\"complete\""));
}
#[test]
fn byte_budget_is_aggregate_and_duplicate_options_are_refused() {
    let path = file("def x : Nat := 1");
    let output = run(vec![
        "check-source".into(),
        "--json".into(),
        "--max-bytes=20".into(),
        path.clone().into_os_string(),
        path.clone().into_os_string(),
    ]);
    assert_eq!(output.exit_code, 3);
    assert!(output.stdout.is_empty());
    assert!(output.stderr.contains("\"authority\":false"));
    for flags in [
        vec!["--json", "--json"],
        vec!["--max-bytes=20", "--max-bytes=30"],
    ] {
        let args = std::iter::once(OsString::from("check-source"))
            .chain(flags.into_iter().map(OsString::from))
            .chain(std::iter::once(path.clone().into_os_string()))
            .collect();
        assert_ne!(run(args).exit_code, 0);
    }
}
#[test]
fn unsupported_commands_never_execute_and_end_of_options_preserves_dash_paths() {
    let path = file("#eval 1");
    let output = run(vec![
        "check-source".into(),
        "--json".into(),
        "--".into(),
        path.clone().into_os_string(),
    ]);
    assert_ne!(output.exit_code, 0);
    assert!(output.stdout.is_empty());
    assert!(output.stderr.contains("\"authority\":false"));
    let dir = path.parent().unwrap();
    std::fs::write(dir.join("-proof.lean"), "theorem same : 7 = 7 := by rfl").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .current_dir(dir)
        .args(["check-source", "--", "-proof.lean"])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn installed_binary_checks_quantified_simp_and_selected_definition_proofs() {
    let example = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples/native_simplification.lean");
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .arg(example)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let text = String::from_utf8(output.stdout).unwrap();
    for field in [
        "\"commands\":6",
        "\"theorems\":5",
        "\"executed\":false",
        "\"outcome\":\"complete\"",
    ] {
        assert!(text.contains(field), "{text}");
    }
    assert!(output.stderr.is_empty());
}

#[test]
fn a_late_simp_failure_does_not_emit_partial_success_for_prior_files() {
    let one =
        file("theorem contract (f : Nat -> Nat) (x : Nat) (h : f x = x) : f x = x := by exact h");
    let two = file(
        "theorem use (f : Nat -> Nat) (x : Nat) (h : f x = x) : f (f x) = x := by simp only [contract f, h]",
    );
    let args = vec![
        "check-source".into(),
        "--json".into(),
        one.into_os_string(),
        two.clone().into_os_string(),
    ];
    let complete = run(args.clone());
    assert_eq!(complete.exit_code, 0, "{}", complete.stderr);
    std::fs::write(two, "theorem bad : 1 = 2 := by simp only []").unwrap();
    let refused = run(args);
    assert_ne!(refused.exit_code, 0);
    assert!(refused.stdout.is_empty());
    assert!(!refused.stderr.contains("\"outcome\":\"complete\""));
}
