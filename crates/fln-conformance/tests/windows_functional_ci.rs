//! Static contract for the real Windows functional workflow (bead fln-wgz).
//!
//! Linux cannot prove a Windows runner executed, but it can prevent the workflow
//! from silently changing into a Linux lane, floating its toolchain, dropping the
//! whole-workspace/conformance run, or claiming reproducibility certification.

#![forbid(unsafe_code)]

use std::fs;
use std::path::PathBuf;

fn root() -> PathBuf {
    fln_conformance::checked_workspace_root!()
}

#[test]
fn windows_functional_workflow_keeps_the_declared_native_scope() {
    let path = root().join(".github/workflows/windows-functional.yml");
    let workflow = fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("cannot read {}: {error}", path.display()));

    for required in [
        "name: windows-functional",
        "runs-on: windows-2022",
        "workflow_dispatch:",
        "shell: bash",
        "actions/checkout@11d5960a326750d5838078e36cf38b85af677262",
        "persist-credentials: false",
        "SUITE.lock-pinned Rust toolchain",
        "rustup toolchain install \"$channel\" --profile minimal",
        "rustup override set \"$channel\"",
        "cargo check --locked --workspace --all-targets",
        "cargo test --locked --workspace --no-fail-fast",
        "--test fault_boundary_registry",
        "every_capability_has_a_platform_row_chosen_at_compile_time",
        "functional-not-certified boundary",
        "fln.windows-functional-evidence/1",
        "finalize Windows functional evidence",
        "actions/upload-artifact@ea165f8d65b6e75b540449e92b4886f43607fa02",
        "windows-functional-evidence-${{ github.run_id }}-${{ github.run_attempt }}",
        "if: always()",
    ] {
        assert!(
            workflow.contains(required),
            "Windows functional workflow lost required contract {required:?}"
        );
    }
    assert!(
        !workflow.contains("--reproducible"),
        "the functional Windows lane must not silently claim bit certification"
    );
    let initialization = workflow
        .find("- name: initialize the Windows functional evidence bundle")
        .expect("the Windows evidence initializer is present");
    let checkout = workflow
        .find("- name: checkout FrankenLean")
        .expect("the checkout step is present");
    assert!(
        initialization < checkout,
        "the evidence bundle must exist before checkout so an early checkout failure remains diagnosable"
    );

    let ledger = fs::read_to_string(root().join("ci/PARITY_LEDGER.txt"))
        .expect("the Parity Ledger must remain readable");
    assert!(
        ledger.contains(
            "row platform | windows-x86-64.functional-workspace | ci-lane | unavailable | L0 | sound | native-ci | real-windows-host-required | .github/workflows/windows-functional.yml | D4 | BLOCKED | crosscheck-x86_64-pc-windows-msvc-20260804"
        ),
        "until a real Windows host passes the workspace lane, the ledger must retain its exact L0 BLOCKED row"
    );
}
