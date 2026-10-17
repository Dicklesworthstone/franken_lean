//! Configured search reaches executable admission, refusal and recovery paths.
#![forbid(unsafe_code)]
use std::process::Command;

#[test]
fn installed_configured_search_preserves_exit_classes_and_never_publishes_a_prefix() {
    let root = std::env::temp_dir().join(format!("fln-search-config-{}", std::process::id()));
    std::fs::create_dir_all(&root).unwrap();
    let path = root.join("Proofs.lean");
    for (source, status, expected) in [
        (
            "theorem result (P : Prop) : P -> P := by solve_by_elim (maxDepth := 3) +intro -constructor\n",
            0,
            "\"theorems\":1",
        ),
        (
            "def preceding : Nat := 7\ntheorem bad (P : Prop) (h : P) : P := by solve_by_elim (maxDepth := 0) only [h]\n",
            1,
            "\"authority\":false",
        ),
        (
            "theorem bad : True := by first | solve_by_elim (maxDepth := 18446744073709551616) | constructor\n",
            3,
            "\"outcome\":\"resource\"",
        ),
        (
            "theorem recovered : True := by solve_by_elim (maxDepth := 2) -intro -constructor\n",
            0,
            "\"theorems\":1",
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
        let text = if status == 0 {
            assert!(output.stderr.is_empty());
            let text = String::from_utf8(output.stdout).unwrap();
            assert!(text.contains("\"authority\":true"), "{text}");
            assert!(text.contains("\"executed\":false"), "{text}");
            text
        } else {
            assert!(output.stdout.is_empty());
            String::from_utf8(output.stderr).unwrap()
        };
        assert!(text.contains(expected), "{text}");
        assert_eq!(std::fs::read_to_string(&path).unwrap(), source);
    }
}
