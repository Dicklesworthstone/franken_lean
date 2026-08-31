//! Regression coverage for build-gate path selection outside the shared development host.
//!
//! The canonical shared host exposes `/data/tmp`; GitHub-hosted runners do not. The gate must
//! preserve the machine-wide path when it exists while selecting a writable runner/temp root when
//! it does not. The probe validates the selected paths before acquisition, so even a regression to
//! the old hard-coded default cannot touch or block on the real shared gate.

#![forbid(unsafe_code)]

use fln_core::scratch::{GATE_DISCRIMINATOR_PREFIX, ScratchRoot};
use std::process::Command;

fn library() -> std::path::PathBuf {
    let lib = fln_conformance::checked_workspace_root!().join("scripts/lib/gate_lock.sh");
    assert!(
        lib.is_file(),
        "scripts/lib/gate_lock.sh must exist; otherwise the portability probe measures nothing"
    );
    lib
}

#[test]
fn absent_shared_root_falls_back_to_runner_temp_before_acquisition() {
    let guard = ScratchRoot::create(
        GATE_DISCRIMINATOR_PREFIX,
        "gate-portability",
        "runner-temp-fallback",
    )
    .expect("scratch directory is creatable");
    let runner_temp = guard.join("runner-temp");
    std::fs::create_dir(&runner_temp).expect("runner temp directory is creatable");
    let absent_shared = guard.join("absent-shared-root");
    let expected_lock = runner_temp.join("fln-gate.lockfile");
    let expected_journal = runner_temp.join("fln-gate.journal");

    let script = r#"set -eu
        unset FLN_GATE_LOCKFILE FLN_GATE_JOURNAL TMPDIR
        . "$GATE_LIB"
        if [ "$FLN_GATE_LOCKFILE" != "$EXPECTED_LOCK" ]; then
          printf 'wrong lock path: %s\n' "$FLN_GATE_LOCKFILE" >&2
          exit 91
        fi
        if [ "$FLN_GATE_JOURNAL" != "$EXPECTED_JOURNAL" ]; then
          printf 'wrong journal path: %s\n' "$FLN_GATE_JOURNAL" >&2
          exit 92
        fi
        fln_gate_acquire portability_probe
        printf 'STATE=%s\n' "$FLN_GATE_STATE"
        fln_gate_release_note portability_probe
    "#;

    let output = Command::new("bash")
        .arg("-c")
        .arg(script)
        .env("GATE_LIB", library())
        .env("FLN_GATE_SHARED_DIR", &absent_shared)
        .env("RUNNER_TEMP", &runner_temp)
        .env("EXPECTED_LOCK", &expected_lock)
        .env("EXPECTED_JOURNAL", &expected_journal)
        .env("FLN_GATE_WAIT_S", "1")
        .env_remove("FLN_GATE_LOCKFILE")
        .env_remove("FLN_GATE_JOURNAL")
        .env_remove("TMPDIR")
        .output()
        .expect("bash/flock are available; their absence is an environment fault, not a pass");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "the gate did not select and acquire the runner-temp fallback: {:?}\nstdout: {stdout}\nstderr: {stderr}",
        output.status.code()
    );
    assert!(
        stdout.contains("STATE=acquired"),
        "the fallback path was selected but not actually acquired: {stdout}"
    );
    assert!(
        expected_lock.is_file(),
        "acquisition did not materialize the selected lockfile: {}",
        expected_lock.display()
    );
    let journal = std::fs::read_to_string(&expected_journal)
        .expect("acquisition and release notes materialize the selected journal");
    assert!(
        journal.contains(r#""event":"acquired""#)
            && journal.contains(r#""event":"released-acquired""#),
        "the selected journal does not bind both acquisition and release:\n{journal}"
    );
    assert!(
        !absent_shared.exists(),
        "path selection must not create or write the absent shared-root candidate: {}",
        absent_shared.display()
    );
}
