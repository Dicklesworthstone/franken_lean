//! Polymorphic dictionary inference through the installed check-source command.
#![forbid(unsafe_code)]
use std::process::Command;

#[test]
fn inferred_universe_outputs_keep_checked_success_and_failure_boundaries() {
    let directory =
        std::env::temp_dir().join(format!("fln-universe-outputs-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let declarations = directory.join("declarations.lean");
    let theorem = directory.join("theorem.lean");
    let mut source = String::from(
        "class U0.{u} (A : outParam (Type u)) where\n  value : Nat\ninstance u0 : U0 Nat := U0.mk 7\n",
    );
    for level in 1..=9 {
        let previous = level - 1;
        source.push_str(&format!("class U{level}.{{u}} (A : outParam (Type u)) where\n  value : Nat\ninstance u{level}.{{u,v}} {{A : Type u}} {{B : Type v}} [left : U{previous} A] [right : U{previous} B] : U{level} Nat := U{level}.mk left.value\n"));
    }
    source.push_str("class Answer where\n  value : Nat\ninstance answer.{u} {A : Type u} [dict : U9 A] : Answer := Answer.mk dict.value\ndef result : Answer := inferInstance\n");
    std::fs::write(&declarations, &source).unwrap();
    for expected in [7, 8, 7] {
        std::fs::write(
            &theorem,
            format!("theorem resultValue : result.value = {expected} := by rfl\n"),
        )
        .unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json"])
            .arg(&declarations)
            .arg(&theorem)
            .output()
            .unwrap();
        if expected == 7 {
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            assert!(output.stderr.is_empty());
            let json = String::from_utf8(output.stdout).unwrap();
            for field in [
                "\"outcome\":\"complete\"",
                "\"authority\":true",
                "\"theorems\":1",
                "\"executed\":false",
            ] {
                assert!(json.contains(field), "{json}");
            }
        } else {
            assert_eq!(output.status.code(), Some(1));
            assert!(output.stdout.is_empty());
            assert!(!output.stderr.is_empty());
        }
        assert_eq!(std::fs::read_to_string(&declarations).unwrap(), source);
    }
}
