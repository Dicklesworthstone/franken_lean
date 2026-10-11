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
fn installed_command_checks_repeated_output_dictionaries_and_their_proof() {
    let mut source = String::from(
        "class C0 (A : outParam Type) where\n  value : A\ninstance c0 : C0 Nat := C0.mk 7\n",
    );
    for depth in 1..=12 {
        let previous = depth - 1;
        source.push_str(&format!(
            "class C{depth} (A : outParam Type) where\n  value : A\ninstance c{depth} [a : C{previous} Nat] [b : C{previous} Nat] : C{depth} Nat := C{depth}.mk a.value\n"
        ));
    }
    // The solution doubles at each level, so it is far larger than the pin's default
    // `synthInstance.maxSize` (128): there the request is refused (`failed to synthesize`), as it
    // is here since df2f1d37. The test measures tabling, not that limit, so it raises the limit
    // as a user would; both the pin (v4.32.0, 2026-10-11) and this checker accept then.
    source.push_str(
        "set_option synthInstance.maxSize 8192\ndef result : C12 Nat := inferInstance\ntheorem correct : result.value = 7 := by rfl\n",
    );
    let path = file("outputs", &source);
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .arg(&path)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
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

#[test]
fn installed_command_finds_fallback_after_repeated_exhausted_prerequisites() {
    let mut source = String::from("class Missing0 where\n  value : Nat\n");
    for depth in 1..=12 {
        let previous = depth - 1;
        source.push_str(&format!(
            "class Missing{depth} where\n  value : Nat\ninstance a{depth} [d : Missing{previous}] : Missing{depth} := Missing{depth}.mk d.value\ninstance b{depth} [d : Missing{previous}] : Missing{depth} := Missing{depth}.mk d.value\n"
        ));
    }
    source.push_str("class Root where\n  value : Nat\ninstance fallback : Root := Root.mk 7\ninstance unavailable [d : Missing12] : Root := Root.mk 99\ndef result : Root := inferInstance\ntheorem correct : result.value = 7 := by rfl\n");
    let path = file("fallback", &source);
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
    assert!(
        String::from_utf8(output.stdout)
            .unwrap()
            .contains("\"theorems\":1")
    );
}
