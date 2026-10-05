//! Installed indexed-data execution, import recovery, and independent FLBC replay.
#![forbid(unsafe_code)]
use std::{
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::atomic::{AtomicUsize, Ordering},
};
static NEXT: AtomicUsize = AtomicUsize::new(0);
fn directory() -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fln-indexed-runtime-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&path).unwrap();
    path
}
fn run(source: &Path, artifact: &Path) -> Output {
    Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["run", "--json", "--emit-flbc"])
        .arg(artifact)
        .arg(source)
        .output()
        .unwrap()
}
fn replay(artifact: &Path) {
    let before = std::fs::read(artifact).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["flbc", "run", "--json"])
        .arg(artifact)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    assert!(String::from_utf8_lossy(&output.stdout).contains("\"returnValue\":42"));
    assert_eq!(before, std::fs::read(artifact).unwrap());
}
fn personalities_and_replay(source: &str) {
    let path = directory().join("Main.lean");
    let artifact = path.with_extension("flbc");
    std::fs::write(&path, source).unwrap();
    let output = run(&path, &artifact);
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    assert!(String::from_utf8_lossy(&output.stdout).contains("\"finalValue\":42"));
    replay(&artifact);
    let lean = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(&path)
        .output()
        .unwrap();
    assert!(lean.status.success(), "{lean:?}");
    assert!(lean.stderr.is_empty(), "{lean:?}");
    assert_eq!(lean.stdout, b"42\n");
    assert_eq!(source, std::fs::read_to_string(&path).unwrap());
}
#[test]
fn indexed_mapping_executes_through_both_personalities_and_serialized_replay() {
    personalities_and_replay(include_str!(
        "../../../examples/native_indexed_vectors.lean"
    ));
}
#[test]
fn imported_indexed_families_reject_wrong_indices_without_publishing_artifacts() {
    let dir = directory();
    let dependency = dir.join("Vector.lean");
    let entry = dir.join("Main.lean");
    let example = include_str!("../../../examples/native_indexed_vectors.lean");
    let (definitions, expression) = example.split_once("#eval").unwrap();
    std::fs::write(&dependency, definitions).unwrap();
    let source = format!("import Vector\n#eval {expression}");
    std::fs::write(&entry, &source).unwrap();
    let artifact = dir.join("good.flbc");
    let output = run(&entry, &artifact);
    assert!(output.status.success(), "{output:?}");
    replay(&artifact);
    let before = std::fs::read(&artifact).unwrap();
    for invalid in [
        format!("{definitions}\ndef invalidLength : Vec Nat 1 := Vec.nil\n"),
        format!("{definitions}\ntheorem invalidEvidence : 0 = 1 := by rfl\n"),
    ] {
        std::fs::write(&dependency, invalid).unwrap();
        let failed = dir.join("failed.flbc");
        let output = run(&entry, &failed);
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        assert!(output.stdout.is_empty(), "{output:?}");
        assert!(!failed.exists());
        assert_eq!(before, std::fs::read(&artifact).unwrap());
    }
    std::fs::write(&dependency, definitions).unwrap();
    let recovered = dir.join("recovered.flbc");
    assert!(run(&entry, &recovered).status.success());
    assert_eq!(before, std::fs::read(&recovered).unwrap());
    assert_eq!(source, std::fs::read_to_string(&entry).unwrap());
}

/// Recursive matches that refine `Vec`'s index (and the non-variable index
/// `Nat.succ n` in `head`), with an `Eq.rec` transport, accepted by the pinned
/// Reference `lean` v4.32.0, which prints `42`. It replaces
/// `examples/native_equality_transport.lean`, which the pin refuses: `Walk`'s
/// index is promoted to a parameter, so `.done k` names an inaccessible
/// position and `copy` there refines nothing.
const REFINED_TRANSPORT: &str = r#"-- Both checkers see the real indices and equality proofs. Native casts retain
-- the checked value only when its source and destination layouts agree.
inductive Vec (A : Type) : Nat -> Type where
  | nil : Vec A 0
  | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)

def copy : (n : Nat) -> Vec Nat n -> Vec Nat n
  | _, .nil => Vec.nil
  | _, .cons k x tail => Vec.cons k x (copy k tail)

def total : (n : Nat) -> Vec Nat n -> Nat
  | _, .nil => 0
  | _, .cons k x tail => x + total k tail

def head : (n : Nat) -> Vec Nat (Nat.succ n) -> Nat
  | _, .cons _ x _ => x

def transport (a b : Nat) (h : a = b) (x : Nat) : Nat :=
  Eq.rec (motive := fun k proof => Nat) x h

#eval transport 1 1 (by rfl) (head 1 (Vec.cons 1 10 (Vec.cons 0 22 Vec.nil)) + total 2 (copy 2 (Vec.cons 1 10 (Vec.cons 0 22 Vec.nil))))
"#;

/// The former example's `copy`, refused by the pin ("Type mismatch" at the
/// named `k` in `Walk`'s promoted parameter position).
const NAMED_PARAMETER: &str = r#"inductive Walk : Nat -> Type where
  | done (n : Nat) : Walk n
  | step (n : Nat) (child : Walk n) : Walk n

def copy (n : Nat) (w : Walk n) : Walk n :=
  match w with
  | .done k => Walk.done k
  | .step k child => Walk.step k (copy k child)

#eval match copy 40 (Walk.done 40) with | .done _ => 42 | .step _ _ => 0
"#;

#[test]
fn refined_recursive_matches_and_transports_have_independent_bytecode_replay() {
    personalities_and_replay(REFINED_TRANSPORT);
    let path = directory().join("Main.lean");
    let artifact = path.with_extension("flbc");
    std::fs::write(&path, NAMED_PARAMETER).unwrap();
    let output = run(&path, &artifact);
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert!(output.stdout.is_empty(), "{output:?}");
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("a constructor parameter is inaccessible in a pattern"),
        "{output:?}"
    );
    assert!(!artifact.exists());
    assert_eq!(NAMED_PARAMETER, std::fs::read_to_string(&path).unwrap());
}
#[test]
fn imported_transports_keep_false_evidence_out_of_executable_artifacts() {
    let dir = directory();
    let dependency = dir.join("Transport.lean");
    let entry = dir.join("Main.lean");
    let definition = "def transport (a b : Nat) (h : a = b) (x : Nat) : Nat := Eq.rec (motive := fun k proof => Nat) x h\n";
    std::fs::write(&dependency, definition).unwrap();
    let source = "import Transport\n#eval transport 1 1 (by rfl) 42";
    std::fs::write(&entry, source).unwrap();
    let artifact = dir.join("good.flbc");
    assert!(run(&entry, &artifact).status.success());
    replay(&artifact);
    let before = std::fs::read(&artifact).unwrap();
    std::fs::write(&entry, source.replace("transport 1 1", "transport 1 2")).unwrap();
    let failed = dir.join("failed.flbc");
    let output = run(&entry, &failed);
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert!(output.stdout.is_empty());
    assert!(!failed.exists());
    assert_eq!(before, std::fs::read(&artifact).unwrap());
    std::fs::write(&entry, source).unwrap();
    let recovered = dir.join("recovered.flbc");
    assert!(run(&entry, &recovered).status.success());
    assert_eq!(before, std::fs::read(&recovered).unwrap());
}
