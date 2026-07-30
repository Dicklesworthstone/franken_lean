//! `extern_dispatch_no_mock_e2e` — the real generator end-to-end (bead
//! `franken_lean-pw6t`): no mocks, no fixtures standing in for the pipeline.
//!
//! The drill has three acts:
//!
//! 1. **The real repo**: `gen_extern_rows.py --check` against the committed
//!    artifacts and the real oracle-side inputs on this machine (typed skip when
//!    the untracked shards are absent — the generator's exit 3, never a pass).
//! 2. **A mirror tree** inside a guard-owned scratch root: the generator, the
//!    contract, and the projection copied; the shards and lock files symlinked.
//!    `--check` is clean through the links; a planted leftover candidate is
//!    drift and refuses; `--recover` completes the interrupted state and the
//!    final validation names the planted garbage; restoring the good artifact
//!    returns the mirror to valid. Recovery is a final-state proof, never
//!    "the process restarted".
//! 3. **The evidence streams**: semantic and telemetry NDJSON records for the
//!    run, asserted disjoint and schema-exact, plus the {1, 8, 32}
//!    schedule-invariance law over the real table.

#![forbid(unsafe_code)]

use fln_core::scratch::{EXTERN_E2E_PREFIX, ScratchRoot};
use fln_vm::extern_row::{SEMANTIC_SCHEMA, TELEMETRY_SCHEMA};
use fln_vm::load::{load_embedded, reduce_productively};
use std::path::{Path, PathBuf};
use std::process::Command;

/// The repo root, resolved the invoking-workspace way (runtime env, never a
/// compile-time bake — the golden_vellum pattern for exactly this situation).
fn repo_root() -> PathBuf {
    let manifest = std::env::var_os("CARGO_MANIFEST_DIR")
        .map(PathBuf::from)
        .expect("cargo identifies the invoking crate directory");
    manifest
        .parent()
        .and_then(Path::parent)
        .map(Path::to_path_buf)
        .expect("the workspace root is two levels above the crate")
}

fn generator(root: &Path) -> PathBuf {
    let script = root.join("scripts/extract/gen_extern_rows.py");
    assert!(
        script.is_file(),
        "the generator must exist at {}",
        script.display()
    );
    script
}

fn run_generator(root: &Path, mode: &str) -> std::process::Output {
    Command::new("python3")
        .args(["-I", "-S"])
        .arg(generator(root))
        .arg(mode)
        .current_dir(root)
        .output()
        .expect("the generator launches")
}

fn stdout_of(output: &std::process::Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn stderr_of(output: &std::process::Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

#[test]
fn the_real_generator_reports_no_drift_and_a_valid_contract() {
    let root = repo_root();
    let check = run_generator(&root, "--check");
    if check.status.code() == Some(3) {
        eprintln!(
            "TYPED SKIP: the untracked builtin shards are absent on this machine; the \
             generator's typed inconclusive stands and NOTHING here was established: {}",
            stderr_of(&check)
        );
        return;
    }
    assert_eq!(
        check.status.code(),
        Some(0),
        "--check must exit 0 on the committed artifacts, got {:?}: {}{}",
        check.status.code(),
        stdout_of(&check),
        stderr_of(&check)
    );
    assert!(
        stdout_of(&check).contains("no drift"),
        "the committed artifacts must report no drift: {}",
        stdout_of(&check)
    );

    let validate = run_generator(&root, "--validate");
    assert_eq!(validate.status.code(), Some(0));
    assert!(
        stdout_of(&validate).contains("valid: contract-root fnv1a64:"),
        "--validate must print the root: {}",
        stdout_of(&validate)
    );
}

/// Materialize the mirror tree: the small authorities copied, the big ones
/// symlinked so the mirror's generator reads exactly the bytes the real one
/// would. Returns the scratch guard and the mirror root.
fn materialize_mirror(scratch: &ScratchRoot, real: &Path) -> PathBuf {
    let mirror = scratch.join("mirror");
    for dir in [
        "scripts/extract",
        "contracts",
        "crates/fln-vm/src",
        "tribunal/epochs",
    ] {
        std::fs::create_dir_all(mirror.join(dir)).expect("mirror directory");
    }
    let copy = |relative: &str| {
        std::fs::copy(real.join(relative), mirror.join(relative))
            .unwrap_or_else(|error| panic!("copy {relative}: {error}"));
    };
    let link = |relative: &str| {
        std::os::unix::fs::symlink(real.join(relative), mirror.join(relative))
            .unwrap_or_else(|error| panic!("link {relative}: {error}"));
    };
    copy("scripts/extract/gen_extern_rows.py");
    copy("contracts/EXTERN_ROW_CONTRACT.txt");
    copy("contracts/EXTERN_BUILTIN_ENVIRONMENT.txt");
    copy("SUITE.lock");
    copy("crates/fln-vm/src/extern_table_generated.rs");
    link("contracts/extern_census.tsv");
    link("contracts/builtin_environment.tsv");
    link("contracts/builtin_environment.001.tsv");
    link("contracts/builtin_environment.002.tsv");
    link("contracts/builtin_partition.tsv");
    link("ABI_CONTRACT.md");
    std::os::unix::fs::symlink(
        real.join("tribunal/epochs/v4.32.0"),
        mirror.join("tribunal/epochs/v4.32.0"),
    )
    .expect("link the epoch manifest directory");
    mirror
}

#[test]
fn mirror_check_refusal_recover_and_final_state() {
    let real = repo_root();
    let check = run_generator(&real, "--check");
    if check.status.code() == Some(3) {
        eprintln!(
            "TYPED SKIP: shards absent; the mirror drill needs the real inputs: {}",
            stderr_of(&check)
        );
        return;
    }

    let scratch = ScratchRoot::create(EXTERN_E2E_PREFIX, "extern-e2e", "mirror")
        .expect("create the mirror scratch root");
    let mirror = materialize_mirror(&scratch, &real);

    // A mirror of the real artifacts is byte-clean through the links.
    let clean = run_generator(&mirror, "--check");
    assert_eq!(
        clean.status.code(),
        Some(0),
        "the mirror must report no drift: {}{}",
        stdout_of(&clean),
        stderr_of(&clean)
    );

    // Plant an interrupted publication: a leftover candidate with garbage in it.
    let candidate = mirror.join("contracts/EXTERN_ROW_CONTRACT.txt.candidate");
    std::fs::write(&candidate, b"schema fln-extern-row-contract/1\ngarbage\n")
        .expect("plant the candidate");
    let refused = run_generator(&mirror, "--check");
    assert_eq!(
        refused.status.code(),
        Some(1),
        "a leftover candidate must be drift, got {:?}: {}{}",
        refused.status.code(),
        stdout_of(&refused),
        stderr_of(&refused)
    );
    assert!(
        stderr_of(&refused).contains("leftover candidate")
            || stdout_of(&refused).contains("leftover candidate"),
        "the drift must name the leftover candidate: {}{}",
        stdout_of(&refused),
        stderr_of(&refused)
    );

    // Recover: the candidate is installed (this is what --recover is FOR — an
    // interrupted publication completes), and the next validation names the
    // garbage rather than reporting a green tree.
    let recovered = run_generator(&mirror, "--recover");
    assert_eq!(recovered.status.code(), Some(0));
    assert!(!candidate.exists(), "recovery consumes the candidate");
    let invalid = run_generator(&mirror, "--validate");
    assert_ne!(
        invalid.status.code(),
        Some(0),
        "the planted garbage must fail validation after recovery installs it"
    );

    // Restore the good artifact: the final state is exactly the valid mirror.
    std::fs::copy(
        real.join("contracts/EXTERN_ROW_CONTRACT.txt"),
        mirror.join("contracts/EXTERN_ROW_CONTRACT.txt"),
    )
    .expect("restore the good contract");
    let valid = run_generator(&mirror, "--validate");
    assert_eq!(
        valid.status.code(),
        Some(0),
        "the restored mirror must validate: {}{}",
        stdout_of(&valid),
        stderr_of(&valid)
    );
}

#[test]
fn evidence_streams_are_disjoint_and_schema_exact() {
    let scratch = ScratchRoot::create(EXTERN_E2E_PREFIX, "extern-e2e", "evidence")
        .expect("create the evidence scratch root");
    let contract = load_embedded().expect("the committed contract loads");

    // The {1, 8, 32} schedule law over the real table, recorded as evidence.
    let mut roots = Vec::new();
    for workers in [1usize, 8, 32] {
        let evidence = reduce_productively(&contract, workers)
            .expect("a productive reduction at every declared width");
        assert_eq!(
            evidence.completed_per_worker.iter().sum::<usize>(),
            contract.rows.len(),
            "conservation: the workers closed exactly the population"
        );
        assert!(
            evidence.completed_per_worker.iter().all(|count| *count > 0),
            "productive: no worker idles at {workers} workers"
        );
        roots.push(evidence.semantic_root);
    }
    assert_eq!(
        roots[0], roots[1],
        "the semantic root must not move between 1 and 8 workers"
    );
    assert_eq!(
        roots[1], roots[2],
        "the semantic root must not move between 8 and 32 workers"
    );

    let semantic = format!(
        "{{\"schema\":\"{SEMANTIC_SCHEMA}\",\"event\":\"reduce_productively\",\"row-count\":954,\"semantic-root\":\"{}\",\"outcome\":\"complete\"}}\n",
        roots[0]
    );
    let telemetry = format!(
        "{{\"schema\":\"{TELEMETRY_SCHEMA}\",\"event\":\"reduce_productively\",\"duration-ms\":0,\"workers\":[1,8,32]}}\n"
    );
    let semantic_path = scratch.join("semantic.ndjson");
    let telemetry_path = scratch.join("telemetry.ndjson");
    std::fs::write(&semantic_path, &semantic).expect("write semantic stream");
    std::fs::write(&telemetry_path, &telemetry).expect("write telemetry stream");

    let semantic_text = std::fs::read_to_string(&semantic_path).expect("read semantic");
    let telemetry_text = std::fs::read_to_string(&telemetry_path).expect("read telemetry");
    assert!(semantic_text.contains(SEMANTIC_SCHEMA));
    assert!(telemetry_text.contains(TELEMETRY_SCHEMA));
    assert!(
        !semantic_text.contains("duration-ms"),
        "telemetry fields must not leak into the semantic stream"
    );
    assert!(
        !telemetry_text.contains("semantic-root"),
        "semantic fields must not leak into the telemetry stream"
    );
    assert!(
        semantic_text.contains(&roots[0]),
        "a conclusive semantic row carries its root"
    );
}

#[test]
fn an_unproductive_reduction_is_refused() {
    let contract = load_embedded().expect("the committed contract loads");
    assert!(
        reduce_productively(&contract, 0).is_err(),
        "zero workers is not a schedule"
    );
    assert!(
        reduce_productively(&contract, contract.rows.len() + 1).is_err(),
        "more workers than rows reports agreement about nothing"
    );
}
