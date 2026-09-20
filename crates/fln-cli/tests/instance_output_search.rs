//! Installed source checker: inferred outputs, semi-output cycles and recovery.
#![forbid(unsafe_code)]
use std::process::{Command, Output};

fn run(name: &str, source: &str) -> Output {
    let directory = std::env::temp_dir().join(format!(
        "fln-instance-output-search-{}-{name}",
        std::process::id()
    ));
    std::fs::create_dir_all(&directory).unwrap();
    let path = directory.join("source.lean");
    std::fs::write(&path, source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .arg(&path)
        .output()
        .unwrap();
    assert_eq!(std::fs::read_to_string(path).unwrap(), source);
    output
}

fn complete(output: Output) {
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    let json = String::from_utf8(output.stdout).unwrap();
    for field in [
        "\"outcome\":\"complete\"",
        "\"authority\":true",
        "\"executed\":false",
    ] {
        assert!(json.contains(field), "{json}");
    }
}

#[test]
fn installed_checker_infers_repeated_outputs_in_both_parameter_modes() {
    for mode in ["outParam", "semiOutParam"] {
        let mut source = format!(
            "class C0 (A : {mode} Type) where\n  value : A\ninstance c0 : C0 Nat := C0.mk 7\n"
        );
        for depth in 1..=12 {
            let previous = depth - 1;
            source.push_str(&format!("class C{depth} (A : {mode} Type) where\n  value : A\ninstance c{depth} {{A B : Type}} [first : C{previous} A] [second : C{previous} B] : C{depth} Nat := C{depth}.mk 7\n"));
        }
        source.push_str(
            "def result : C12 Nat := inferInstance\ntheorem correct : result.value = 7 := by rfl\n",
        );
        complete(run(mode, &source));
    }
}

#[test]
fn installed_checker_preserves_missing_instance_failure_and_recovery() {
    let missing = "class Required (A : outParam Type) where\n  value : A\n";
    let output = run(
        "missing",
        &format!("{missing}def result : Required Nat := inferInstance\n"),
    );
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert!(!String::from_utf8_lossy(&output.stdout).contains("\"outcome\":\"complete\""));
    complete(run(
        "recovered",
        &format!(
            "{missing}instance supplied : Required Nat := Required.mk 7\ndef result : Required Nat := inferInstance\ntheorem checked : result.value = 7 := by rfl\n"
        ),
    ));
}

#[test]
fn installed_checker_checks_the_recursive_semi_output_example() {
    complete(run(
        "example",
        include_str!("../../../examples/native_instance_output_search.lean"),
    ));
}
