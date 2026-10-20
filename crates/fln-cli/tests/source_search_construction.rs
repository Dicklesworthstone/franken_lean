//! Automatic introductions and constructor choices reach executable admission.
#![forbid(unsafe_code)]
use std::process::Command;

#[test]
fn installed_search_builds_checked_terms_without_publishing_failed_prefixes() {
    let root = std::env::temp_dir().join(format!("fln-search-construction-{}", std::process::id()));
    std::fs::create_dir_all(&root).unwrap();
    let path = root.join("Proofs.lean");
    for (source, accepted, count, safety_rejection) in [
        (
            "theorem identity (P : Prop) : P -> P := by solve_by_elim\ntheorem both (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by solve_by_elim\ntheorem fromFalse (P Q : Prop) (hp : P) (no : P -> False) : Q := by solve_by_elim only [hp, no]\n",
            true,
            3,
            false,
        ),
        (
            "def preceding : Nat := 7\ntheorem bad (P : Prop) (hp : P) : False ∨ P := by solve_by_elim\n",
            false,
            0,
            false,
        ),
        (
            "unsafe def impossible : False := impossible\ntheorem bad (P : Prop) : P := by solve_by_elim only [impossible]\n",
            false,
            0,
            true,
        ),
        (
            "theorem recovered (P : Prop) : (P -> P) ∧ True := by solve_by_elim\n",
            true,
            1,
            false,
        ),
    ] {
        std::fs::write(&path, source).unwrap();
        let result = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json"])
            .arg(&path)
            .output()
            .unwrap();
        assert_eq!(
            result.status.code(),
            Some(if accepted { 0 } else { 1 }),
            "{source}\n{}",
            String::from_utf8_lossy(&result.stderr)
        );
        if accepted {
            assert!(result.stderr.is_empty());
            let text = String::from_utf8(result.stdout).unwrap();
            for field in [
                "\"authority\":true".to_owned(),
                "\"executed\":false".to_owned(),
                format!("\"theorems\":{count}"),
            ] {
                assert!(text.contains(&field), "{text}");
            }
        } else {
            assert!(result.stdout.is_empty());
            let text = String::from_utf8(result.stderr).unwrap();
            if safety_rejection {
                // An actual kernel rejection is authoritative, unlike an
                // incomplete elaboration; neither is an accepted theorem.
                assert!(text.contains("\"outcome\":\"kernel-rejection\""), "{text}");
                assert!(text.contains("\"authority\":true"), "{text}");
                assert!(text.contains("SafetyViolation"), "{text}");
            } else {
                assert!(text.contains("\"authority\":false"), "{text}");
            }
        }
        assert_eq!(std::fs::read_to_string(&path).unwrap(), source);
    }
}
