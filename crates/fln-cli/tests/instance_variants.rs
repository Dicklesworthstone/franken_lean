//! Installed command regressions for bounded native instance tabling.
#![forbid(unsafe_code)]
use std::{path::PathBuf, process::Command};

fn file(name: &str, source: &str) -> PathBuf {
    let directory = std::env::temp_dir().join(format!(
        "fln-instance-tabling-{}-{name}",
        std::process::id(),
    ));
    std::fs::create_dir_all(&directory).unwrap();
    let path = directory.join("source.lean");
    std::fs::write(&path, source).unwrap();
    path
}

#[test]
fn installed_command_infers_repeated_open_outputs_in_both_parameter_modes() {
    for mode in ["outParam", "semiOutParam"] {
        let mut source = format!(
            "class Open0 (A : {mode} Type) where\n  value : Nat\ninstance open0 : Open0 Nat := Open0.mk 7\n"
        );
        for depth in 1..=12 {
            let previous = depth - 1;
            source.push_str(&format!(
                "class Open{depth} (A : {mode} Type) where\n  value : Nat\ninstance open{depth} {{A B : Type}} [first : Open{previous} A] [second : Open{previous} B] : Open{depth} Nat := Open{depth}.mk first.value\n"
            ));
        }
        source.push_str("def result : Open12 Nat := inferInstance\ntheorem correct : result.value = 7 := by rfl\n");
        let path = file(mode, &source);
        let output = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json"])
            .arg(&path)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{mode}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(output.stderr.is_empty());
        let json = String::from_utf8(output.stdout).unwrap();
        for expected in [
            "\"outcome\":\"complete\"",
            "\"authority\":true",
            "\"theorems\":1",
            "\"executed\":false",
        ] {
            assert!(json.contains(expected), "{json}");
        }
        assert_eq!(std::fs::read_to_string(path).unwrap(), source);
    }
}

#[test]
fn installed_command_reports_a_real_cycle_failure_and_accepts_its_repair() {
    let source = "class Choose (A : semiOutParam Type) where\n  tag : Nat\ninstance step {A : Type} [next : Choose A] : Choose Bool := Choose.mk (next.tag + 1)\n";
    let path = file(
        "semi-cycle-failure",
        &format!("{source}def result : Choose Bool := inferInstance\n"),
    );
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .arg(path)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    let error = String::from_utf8(output.stderr).unwrap();
    assert!(error.contains("\"authority\":false"), "{error}");
    assert!(
        !error.contains("ResourceLimit") && !error.contains("HeartbeatLimit"),
        "{error}"
    );
    let repaired = format!(
        "{source}instance base : Choose Nat := Choose.mk 7\ndef result : Choose Bool := inferInstance\ntheorem repaired : result.tag = 8 := by rfl\n"
    );
    let path = file("semi-cycle-repair", &repaired);
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .arg(path)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.stderr.is_empty());
    let json = String::from_utf8(output.stdout).unwrap();
    assert!(
        json.contains("\"authority\":true") && json.contains("\"theorems\":1"),
        "{json}"
    );
}
