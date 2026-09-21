//! Installed CLI coverage; no model parser, compiler or fake checker.
#![forbid(unsafe_code)]
use std::process::Command;

#[test]
fn installed_cli_checks_instance_registration_and_priority_changes() {
    let source =
        fln_core::checked_workspace_root!().join("examples/native_instance_attributes.lean");
    let before = std::fs::read(&source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .arg(&source)
        .output()
        .unwrap();
    assert!(output.status.success(), "{:?}", output);
    assert!(output.stderr.is_empty());
    let text = String::from_utf8(output.stdout).unwrap();
    for expected in [
        "\"schema\":\"fln.source-check/1\"",
        "\"outcome\":\"complete\"",
        "\"authority\":true",
        "\"commands\":14",
        "\"theorems\":5",
        "\"executed\":false",
    ] {
        assert!(text.contains(expected), "{text}");
    }
    assert_eq!(std::fs::read(source).unwrap(), before);
}

#[test]
fn installed_cli_does_not_publish_success_for_a_nonclass_attribute() {
    let source =
        fln_core::checked_manifest_dir!().join("tests/fixtures/instance_attribute_nonclass.lean");
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .arg(source)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    assert!(!output.stderr.is_empty());
}
