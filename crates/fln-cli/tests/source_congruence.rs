//! Real executable admission, failed-command atomicity, and recovery.
#![forbid(unsafe_code)]
use std::process::Command;

#[test]
fn installed_congruence_constructs_proofs_and_refuses_missing_evidence() {
    let root = std::env::temp_dir().join(format!("fln-congruence-{}", std::process::id()));
    std::fs::create_dir_all(&root).unwrap();
    let path = root.join("Congruence.lean");
    for (source, status, count) in [
        (
            "theorem arrows (P Q R S : Prop) (h : P = R) (k : Q = S) : (P -> Q) = (R -> S) := by congr\n",
            0,
            1,
        ),
        (
            "theorem missing (F : Nat -> Type) (f : (n : Nat) -> F n -> Nat) (n m : Nat) (a : F n) (b : F m) (h : n = m) : f n a = f m b := by congr\n",
            1,
            0,
        ),
        (
            "theorem ordinary (f : Nat -> Nat) (a b : Nat) (h : a = b) : f a = f b := by congr\ntheorem dependent (F : Nat -> Type) (f : (n : Nat) -> F n) (a b : Nat) (h : a = b) : HEq (f a) (f b) := by congr\n",
            0,
            2,
        ),
        (
            "def preceding : Nat := 7\ntheorem bad (f : Nat -> Nat) (a b : Nat) : f a = f b := by congr\n",
            1,
            0,
        ),
        (
            "theorem recovered (P : Nat -> Prop) (f : (n : Nat) -> P n -> Nat) (n m : Nat) (a : P n) (b : P m) (h : n = m) : f n a = f m b := by congr\n",
            0,
            1,
        ),
    ] {
        std::fs::write(&path, source).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json"])
            .arg(&path)
            .output()
            .unwrap();
        assert_eq!(
            output.status.code(),
            Some(status),
            "{source}\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if status == 0 {
            assert!(output.stderr.is_empty());
            let text = String::from_utf8(output.stdout).unwrap();
            for field in [
                "\"authority\":true".to_owned(),
                "\"executed\":false".to_owned(),
                format!("\"theorems\":{count}"),
            ] {
                assert!(text.contains(&field), "{text}");
            }
        } else {
            assert!(output.stdout.is_empty());
            assert!(
                String::from_utf8(output.stderr)
                    .unwrap()
                    .contains("\"authority\":false")
            );
        }
        assert_eq!(std::fs::read_to_string(&path).unwrap(), source);
    }
}
