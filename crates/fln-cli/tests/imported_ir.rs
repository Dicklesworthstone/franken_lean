//! Installed CLI: real Reference IR -> checked lowering -> native Golem.
#![forbid(unsafe_code)]

use std::path::PathBuf;
use std::process::Command;

fn partition() -> Option<PathBuf> {
    let path = std::env::var_os("FLN_BUILTIN_PARTITION")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            fln_core::checked_workspace_root!().join("contracts/builtin_partition.tsv")
        });
    if path.is_file() {
        Some(path)
    } else {
        eprintln!(
            "SKIP imported IR installed CLI: materialize the pinned census at {}",
            path.display()
        );
        None
    }
}

fn command(entry: &str, args: &[&str], policy: &PathBuf) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["ir", "run", "--json", "--entry", entry, "--partition"])
        .arg(policy)
        .args(args)
        .arg(
            fln_core::checked_workspace_root!()
                .join("crates/fln-olean/fixtures/ir/Init.Data.Nat.Basic.ir"),
        )
        .output()
        .unwrap()
}

#[test]
fn installed_command_executes_pinned_ir_and_reports_its_producer() {
    let Some(policy) = partition() else {
        return;
    };
    for (entry, args, expected) in [
        ("Nat.min", ["--nat", "42", "--nat", "9"], 9),
        ("Nat.max", ["--nat", "42", "--nat", "9"], 42),
        ("Nat.blt", ["--nat", "2", "--nat", "3"], 1),
    ] {
        let output = command(entry, &args, &policy);
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(output.stderr.is_empty());
        let stdout = String::from_utf8(output.stdout).unwrap();
        assert!(stdout.contains("\"outcome\":\"complete\""), "{stdout}");
        assert!(
            stdout.contains(&format!("\"value\":{expected},")),
            "{stdout}"
        );
        assert!(stdout.contains("\"producer\":\"reference\""), "{stdout}");
        assert!(stdout.contains("\"authority\":false"), "{stdout}");
        assert!(
            stdout.contains("\"nativeExterns\":[\"extern:Nat."),
            "{stdout}"
        );
    }
}

#[test]
fn installed_execution_budget_is_inconclusive_and_cannot_publish_a_value() {
    let Some(policy) = partition() else {
        return;
    };
    let output = command(
        "Nat.blt",
        &["--nat", "2", "--nat", "3", "--fln-max-steps", "1"],
        &policy,
    );
    assert_eq!(output.status.code(), Some(3));
    assert!(output.stdout.is_empty());
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(stderr.contains("\"outcome\":\"inconclusive\""), "{stderr}");
    assert!(stderr.contains("\"value\":null"), "{stderr}");
    assert!(stderr.contains("\"producer\":\"reference\""), "{stderr}");
}

#[test]
fn installed_command_does_not_reclassify_native_api_or_missing_census_rows() {
    let Some(policy) = partition() else {
        return;
    };
    let overridden = command(
        "Nat.blt",
        &["--nat", "2", "--nat", "3", "--user", "Nat.blt"],
        &policy,
    );
    assert_eq!(overridden.status.code(), Some(1));
    assert!(overridden.stdout.is_empty());
    assert!(
        String::from_utf8(overridden.stderr)
            .unwrap()
            .contains("policy-refusal")
    );
    let unknown = command("Nat.blt._boxed", &["--nat", "2", "--nat", "3"], &policy);
    assert_eq!(unknown.status.code(), Some(3));
    assert!(unknown.stdout.is_empty());
    assert!(
        String::from_utf8(unknown.stderr)
            .unwrap()
            .contains("unclassified")
    );
}

#[test]
fn cli_rejects_missing_policy_and_malformed_arguments_before_running() {
    for args in [
        vec!["ir", "run"],
        vec!["ir", "run", "--entry", "Nat.min", "input.ir"],
        vec![
            "ir",
            "run",
            "--entry",
            "Nat.min",
            "--partition",
            "p.tsv",
            "--nat",
            "-1",
            "input.ir",
        ],
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(args)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(2));
        assert!(output.stdout.is_empty());
    }
}
