//! Selected and joint search reach the executable's authoritative source door.
#![forbid(unsafe_code)]
use std::process::Command;

#[test]
fn installed_selected_and_joint_search_preserves_verdict_and_exit_status() {
    let directory =
        std::env::temp_dir().join(format!("fln-selected-search-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let path = directory.join("source.lean");
    for (source, status) in [
        (
            "theorem selected : (0 = 0) ∧ (true = true) := by solve_by_elim only [And.intro, Eq.refl]\ntheorem joint (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by\n  constructor\n  solve_by_elim* only [hp, hq]\n",
            0,
        ),
        (
            "def preceding : Nat := 7\ntheorem bad (P Q : Prop) (hp : P) : P ∧ Q := by\n  constructor\n  solve_by_elim* only [hp]\n",
            1,
        ),
        (
            "theorem exhausted (P : Prop) (cycle : P -> P) : True ∧ P := by\n  constructor\n  solve_by_elim* only [True.intro, cycle, cycle, cycle, cycle, cycle, cycle, cycle, cycle]\n",
            3,
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
            let json = String::from_utf8(output.stdout).unwrap();
            for field in [
                "\"authority\":true",
                "\"outcome\":\"complete\"",
                "\"theorems\":2",
                "\"executed\":false",
            ] {
                assert!(json.contains(field), "{json}");
            }
        } else {
            assert!(output.stdout.is_empty());
            let json = String::from_utf8(output.stderr).unwrap();
            assert!(json.contains("\"authority\":false"), "{json}");
            if status == 3 {
                assert!(json.contains("\"outcome\":\"resource\""), "{json}");
            }
        }
        assert_eq!(std::fs::read_to_string(&path).unwrap(), source);
    }
}
