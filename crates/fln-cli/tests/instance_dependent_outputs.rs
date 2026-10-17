//! Dependent dictionary synthesis through the installed source-check command.
#![forbid(unsafe_code)]
use std::process::Command;

#[test]
fn dependent_output_tree_is_checked_and_bad_suffix_publishes_no_success() {
    let directory =
        std::env::temp_dir().join(format!("fln-dependent-outputs-{}", std::process::id(),));
    std::fs::create_dir_all(&directory).unwrap();
    let declarations = directory.join("declarations.lean");
    let theorem = directory.join("theorem.lean");
    let mut source = String::from(
        "class D0 (A : outParam Type) (a : outParam A) where\n  value : Nat\ninstance d0 : D0 Nat 7 := D0.mk 7\n",
    );
    for level in 1..=12 {
        let previous = level - 1;
        source.push_str(&format!("class D{level} (A : outParam Type) (a : outParam A) where\n  value : Nat\ninstance d{level} {{A B : Type}} {{a : A}} {{b : B}} [left : D{previous} A a] [right : D{previous} B b] : D{level} A a := D{level}.mk left.value\n"));
    }
    // The solution doubles at each level, so it is far larger than the pin's default
    // `synthInstance.maxSize` (128): there the request is refused (`failed to synthesize`), as it
    // is here since df2f1d37. The test measures tabling, not that limit, so it raises the limit
    // as a user would; both the pin (v4.32.0, 2026-10-11) and this checker accept then.
    source.push_str("class Answer where\n  value : Nat\ninstance answer {A : Type} {a : A} [dict : D12 A a] : Answer := Answer.mk dict.value\nset_option synthInstance.maxSize 8192\ndef result : Answer := inferInstance\n");
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
            assert!(!output.status.success());
            assert!(output.stdout.is_empty());
            assert!(!output.stderr.is_empty());
        }
        assert_eq!(std::fs::read_to_string(&declarations).unwrap(), source);
    }
}
