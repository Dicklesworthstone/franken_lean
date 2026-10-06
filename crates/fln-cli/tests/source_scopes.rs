//! Scope commands reach the installed CLI without executing code or publishing
//! success for an invalid suffix. Fixtures use the real engine and both checkers.
#![forbid(unsafe_code)]
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT: AtomicUsize = AtomicUsize::new(0);
fn file(source: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "fln-scope-cli-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&dir).unwrap();
    let path = dir.join("scope.lean");
    std::fs::write(&path, source).unwrap();
    path
}
#[test]
fn installed_cli_checks_scoped_polymorphic_recursion_without_execution() {
    let path = fln_core::checked_workspace_root!().join("examples/native_scopes.lean");
    let before = std::fs::read(&path).unwrap();
    for json in [true, false] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_fln"));
        command.arg("check-source");
        if json {
            command.arg("--json");
        }
        let output = command.arg(&path).output().unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(output.stderr.is_empty());
        let text = String::from_utf8(output.stdout).unwrap();
        if json {
            for field in [
                "\"commands\":11",
                "\"theorems\":2",
                "\"executed\":false",
                "\"authority\":true",
            ] {
                assert!(text.contains(field), "{text}");
            }
        } else {
            assert!(
                text.contains("Checked 11 source commands (2 theorems)"),
                "{text}"
            );
        }
    }
    assert_eq!(std::fs::read(path).unwrap(), before);
}
#[test]
fn invalid_scope_suffixes_emit_no_success_or_artifacts() {
    for (source, outcome, authority) in [
        ("def pfx := 7\nnamespace A\nend B", "input", false),
        // After restoring the root scope, `value` is unknown again. The pin reports it during
        // elaboration (`8:11: error(lean.unknownIdentifier): Unknown identifier `value``;
        // v4.32.0, 2026-10-05), so this is an elaboration refusal, not a K1 rejection of a
        // rebuilt candidate.
        (
            "namespace A\ndef value := 7\nend A\nsection\nopen A\ndef pfx := value\nend\ndef bad := value",
            "elaboration",
            false,
        ),
        ("def pfx := 7\nopen Missing", "input", false),
    ] {
        let path = file(source);
        let before = std::fs::read(&path).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json"])
            .arg(&path)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(1));
        assert!(output.stdout.is_empty());
        let error = String::from_utf8(output.stderr).unwrap();
        assert!(
            error.contains(&format!("\"authority\":{authority}")),
            "{error}"
        );
        assert!(
            error.contains(&format!("\"outcome\":\"{outcome}\"")),
            "{error}"
        );
        assert!(!error.contains("\"outcome\":\"complete\""));
        assert_eq!(std::fs::read(&path).unwrap(), before);
        assert_eq!(
            std::fs::read_dir(path.parent().unwrap()).unwrap().count(),
            1
        );
    }
}
#[test]
fn scope_depth_limit_is_reported_as_resource_not_kernel_rejection() {
    let path = file(&format!("{}def never := 7", "section\n".repeat(257)));
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .arg(path)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(3));
    assert!(output.stdout.is_empty());
    let error = String::from_utf8(output.stderr).unwrap();
    assert!(error.contains("\"outcome\":\"resource\""), "{error}");
    assert!(error.contains("\"authority\":false"), "{error}");
}

/// The drop-in `lean` door keeps the same scopes as `check-source`: declarations are
/// named in their namespace, `open` and `open … in` (the pin's `section open … end`)
/// resolve names for `#eval` and `#check`, and leaving a scope forgets its opens. The
/// expected output is the pinned Reference's `lean <file>`, byte for byte.
#[test]
fn the_lean_door_evaluates_and_checks_under_namespaces_and_opens() {
    let path = file(
        "namespace A\ndef x : Nat := 1\nnamespace B\ndef y : Nat := x + 1\nend B\nend A\n\
         #eval A.B.y\nsection S\nopen A\n#eval x\nend S\nopen A in\n#eval B.y\n#check A.x\n",
    );
    let output = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(&path)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "2\n1\n2\nA.x : Nat\n"
    );
    assert!(output.stderr.is_empty());

    // After `end A`, `x` is unknown again (the pin: "Unknown identifier `x`").
    let closed = file("namespace A\ndef x : Nat := 1\nend A\n#eval x\n");
    let output = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(&closed)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert!(output.stdout.is_empty(), "{output:?}");
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("Unknown identifier `x`"),
        "{output:?}"
    );
}
