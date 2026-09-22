//! Real file and import admission for mutually dependent source data families.
#![forbid(unsafe_code)]
use std::{
    path::PathBuf,
    process::{Command, Output},
    sync::atomic::{AtomicUsize, Ordering},
};
static NEXT: AtomicUsize = AtomicUsize::new(0);
fn directory() -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fln-mutual-groups-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&path).unwrap();
    path
}
fn run(dir: &PathBuf, paths: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_fln"))
        .current_dir(dir)
        .args(["check-source", "--json"])
        .args(paths)
        .output()
        .unwrap()
}
const EXAMPLE: &str = include_str!("../../../examples/native_mutual_groups.lean");
#[test]
fn installed_source_files_use_real_mutual_recursor_proofs() {
    let dir = directory();
    std::fs::write(dir.join("Proof.lean"), EXAMPLE).unwrap();
    let result = run(&dir, &["Proof.lean"]);
    assert!(result.status.success(), "{result:?}");
    assert!(result.stderr.is_empty());
    let json = String::from_utf8(result.stdout).unwrap();
    for field in [
        "\"commands\":5",
        "\"theorems\":2",
        "\"authority\":true",
        "\"executed\":false",
    ] {
        assert!(json.contains(field), "{json}");
    }
    assert_eq!(
        std::fs::read_to_string(dir.join("Proof.lean")).unwrap(),
        EXAMPLE
    );
}
#[test]
fn imported_groups_replay_as_one_authority_unit_and_late_failure_is_atomic() {
    let dir = directory();
    std::fs::write(dir.join("Data.lean"), EXAMPLE).unwrap();
    let main = "import Data\ntheorem imported : value sample = 7 := by rfl";
    std::fs::write(dir.join("Main.lean"), main).unwrap();
    let first = run(&dir, &["Main.lean"]);
    assert!(first.status.success(), "{first:?}");
    assert!(first.stderr.is_empty());
    assert!(String::from_utf8_lossy(&first.stdout).contains("\"files\":2"));
    std::fs::write(dir.join("Bad.lean"), "theorem falseClaim : 0 = 1 := by rfl").unwrap();
    let failed = run(&dir, &["Main.lean", "Bad.lean"]);
    assert!(!failed.status.success());
    assert!(failed.stdout.is_empty());
    assert!(String::from_utf8_lossy(&failed.stderr).contains("\"authority\":false"));
    let recovered = run(&dir, &["Main.lean"]);
    assert!(recovered.status.success(), "{recovered:?}");
    assert_eq!(recovered.stdout, first.stdout);
    assert_eq!(
        std::fs::read_to_string(dir.join("Data.lean")).unwrap(),
        EXAMPLE
    );
    assert_eq!(
        std::fs::read_to_string(dir.join("Main.lean")).unwrap(),
        main
    );
}
#[test]
fn an_invalid_member_or_missing_end_never_reports_success() {
    let dir = directory();
    for text in [
        "mutual inductive A where | mk (f : B -> Nat) inductive B where | mk (a : A) end",
        "mutual inductive A where | mk inductive B where | mk",
        "mutual inductive A where | mk def b := 7 end",
        "mutual inductive A where | mk inductive B where | bad : Nat end",
    ] {
        std::fs::write(dir.join("Bad.lean"), text).unwrap();
        let result = run(&dir, &["Bad.lean"]);
        assert!(!result.status.success(), "{text}: {result:?}");
        assert!(result.stdout.is_empty());
        assert_eq!(std::fs::read_to_string(dir.join("Bad.lean")).unwrap(), text);
    }
}
