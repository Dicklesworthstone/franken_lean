//! File-scale T2/T3 declaration-identity differential against the pinned Reference
//! (bead `fln-file-scale-t2-differential-5f1b`, plan §18.2).
//!
//! Runs the shared `fln_conformance::t2_differential::runner` over all four declared
//! populations (`source_ladder`, `ordinary_probe`, `local_imports`, `upstream_elab`),
//! executes all live negative/trivia/artifact-corruption/crash-resume controls, and
//! verifies the checked-in ratchet ledger at
//! `crates/fln-conformance/evidence/t2_differential/ledger.tsv`.
//!
//! Without the pinned Reference toolchain, emits a typed skip via
//! `PinRig::FileScaleT2Differential` (failing when `FLN_REQUIRE_REFERENCE=1`).
#![forbid(unsafe_code)]

use std::path::PathBuf;

use fln_conformance::pin;
use fln_conformance::t2_differential::T2NormalizerId;
use fln_conformance::t2_differential::runner::{RunOptions, run_file_scale_differential};

fn require_reference_env() -> bool {
    matches!(
        std::env::var("FLN_REQUIRE_REFERENCE").ok().as_deref(),
        Some(v) if !v.is_empty() && v != "0"
    )
}

#[test]
fn file_scale_t2_differential_matches_ratchet_and_controls() {
    let rig = pin::RigRun::new(pin::PinRig::FileScaleT2Differential);
    let Some(pin_lean) = pin::pinned_lean() else {
        if require_reference_env() {
            panic!("FLN_REQUIRE_REFERENCE is set, but pinned Reference lean was not found");
        }
        eprintln!(
            "{}",
            rig.typed_skip()
                .expect("record typed skip for FileScaleT2Differential")
        );
        return;
    };

    let root = pin::workspace_root();
    let pin_tag = pin::pinned_tag().expect("SUITE.lock reference tag");
    let pin_commit = pin::pinned_commit().expect("SUITE.lock reference commit");
    let options = RunOptions {
        workers: 4,
        write_ledger: std::env::var("FLN_T2_LEDGER_WRITE").ok().as_deref() == Some("1"),
        log_path: std::env::var("FLN_T2_LOG_PATH")
            .ok()
            .filter(|s| !s.is_empty())
            .map(PathBuf::from),
    };

    let summary = run_file_scale_differential(&root, &pin_lean, &pin_tag, &pin_commit, &options)
        .unwrap_or_else(|error| panic!("file_scale_t2_differential failed: {error}"));

    eprintln!(
        "file_scale_t2_differential: pin={} commit={} normalizer={} total={}",
        summary.pin_tag,
        summary.pin_commit,
        T2NormalizerId::V1.as_str(),
        summary.observed.len()
    );
    for (family, s) in &summary.per_family {
        eprintln!(
            "  family={family:<15} total={:<3} both_accept={:<3} both_reject={:<2} native_rejects={:<2} false_accept={} inconclusive={} primary_t2_id={:<3} full_t2_id={:<3} t3_id={:<3}",
            s.total,
            s.both_accept,
            s.both_reject,
            s.native_rejects,
            s.false_accept,
            s.inconclusive,
            s.primary_t2_identical,
            s.full_t2_identical,
            s.t3_identical
        );
    }

    rig.executed()
        .expect("record executed disposition for FileScaleT2Differential");
}
