//! `baseline_resume_and_recovery` — odwj's fourth named suite.
//!
//! odwj requires that every attempt is retained immutably, including invalid,
//! interrupted, thermal, cancelled and insufficient ones; that resume does not
//! duplicate; and that summaries regenerate from raw data. It names five
//! mutations this suite is responsible for:
//!
//!   * **raw sample drop** — an attempt disappears from the record
//!   * **invalid attempt averaging** — an invalid attempt enters the aggregate
//!   * **duplicate resume** — a resumed run re-submits an attempt id
//!   * **hidden instrumentation** — a profiled attempt is reported as clean
//!   * **telemetry-root drift** — telemetry stops corresponding to the attempts
//!   * **partial publication** — a bundle is published missing a component
//!
//! Every cell here rests on ONE fully valid bundle
//! (`a_complete_baseline_bundle_assembles_and_validates`). That positive control
//! is what makes the rest non-vacuous: without it, `assemble_bundle` refusing
//! everything would keep all six mutation cells green while proving nothing.
//! Each mutation changes exactly one thing about that bundle and must be refused
//! by its own NAMED refusal — never merely by "an error", which any unrelated
//! malformation would also produce.
//!
//! What this suite does NOT establish: no attempt here is a real measurement.
//! The measurements are synthetic, so this is about the record-keeping laws, not
//! about any timing. odwj's host qualification is unaffected and still fails on
//! this host.

#![forbid(unsafe_code)]

use fln_bench::{
    AttemptRecord, AttemptStatus, AttemptTelemetry, BENCHMARK_EVIDENCE_VERSION, BenchmarkRefusal,
    BenchmarkTelemetry, CacheCondition, CacheState, ConfidenceAlgorithm, HostProfile,
    HostQualificationPolicy, LocalBuildIdentity, MeasurementUnit, OutlierPolicy, ProfilerState,
    QuantileAlgorithm, ResourceBounds, SamplePlan, WorkloadKind, WorkloadManifest, assemble_bundle,
};
use fln_hash::domain::{Digest, Domain, hash};

const VALID_SAMPLES: u32 = 5;

fn host() -> HostProfile {
    HostProfile::capture_local(LocalBuildIdentity {
        toolchain_manifest: b"fln-bench::baseline_resume_and_recovery/1",
        target_triple: "x86_64-unknown-linux-gnu",
        build_profile: "test",
        enabled_features: &[],
    })
    .expect("host capture")
}

/// Permissive on purpose: host admission is `linux_host_qualification`'s
/// subject, and a host refusal here would mask every record-keeping result.
fn permissive_host_policy() -> HostQualificationPolicy {
    HostQualificationPolicy {
        require_physical_topology: false,
        require_power_governor: false,
        require_thermal_sensors: false,
        require_exclusive_cores: false,
        require_stable_frequency: false,
        require_thermal_stability: false,
        allow_virtualization: true,
        allow_translation: true,
        allow_profiler: false,
    }
}

fn cache_state() -> CacheState {
    CacheState {
        filesystem: CacheCondition::Warm,
        page_cache: CacheCondition::Warm,
        reference_artifacts: CacheCondition::Warm,
        candidate_artifacts: CacheCondition::NotApplicable,
        build_cache: CacheCondition::NotApplicable,
        imported_modules: CacheCondition::Cold,
        daemon: CacheCondition::Cold,
    }
}

fn workload() -> WorkloadManifest {
    WorkloadManifest {
        schema_version: BENCHMARK_EVIDENCE_VERSION,
        workload_id: "odwj-baseline-resume".to_string(),
        workload_kind: WorkloadKind::KernelRecheck,
        corpus_root: hash(Domain::OperationalMeta, b"olean-set/reference@pin"),
        input_order_root: hash(Domain::OperationalMeta, b"olean-set/declared-order"),
        warmup_iterations: 1,
        sample_plan: SamplePlan::FixedValidSamples {
            samples: VALID_SAMPLES,
        },
        quantile_algorithm: QuantileAlgorithm::NearestRankV1,
        confidence_algorithm: ConfidenceAlgorithm::DistributionFreeMedian95V1,
        outlier_policy: OutlierPolicy::RetainAllV1,
        variance_threshold_basis_points: 10_000,
        cache_state: cache_state(),
        unit: MeasurementUnit::Nanoseconds,
        host_policy: permissive_host_policy(),
        resource_bounds: ResourceBounds {
            max_attempts: 64,
            max_measurement: 1_000_000_000,
            max_elapsed_ns_per_attempt: 1_000_000_000,
        },
    }
}

fn attempt(
    ordinal: u32,
    host_root: Digest,
    workload_root: Digest,
    status: AttemptStatus,
) -> AttemptRecord {
    AttemptRecord {
        attempt_id: format!("odwj-attempt-{ordinal}"),
        ordinal,
        host_root,
        workload_root,
        cache_state: cache_state(),
        profiler: ProfilerState::Disabled,
        status,
    }
}

/// The retained record of one interrupted baseline run: five valid attempts and
/// two that must be kept but never aggregated. odwj requires precisely this —
/// invalid and cancelled attempts are retained immutably rather than discarded.
fn attempts(host_root: Digest, workload_root: Digest) -> Vec<AttemptRecord> {
    let mut records = Vec::new();
    for ordinal in 0..VALID_SAMPLES {
        records.push(attempt(
            ordinal,
            host_root,
            workload_root,
            AttemptStatus::Valid {
                measurement: 10_000 + u64::from(ordinal) * 7,
            },
        ));
    }
    records.push(attempt(
        VALID_SAMPLES,
        host_root,
        workload_root,
        AttemptStatus::InvalidHost {
            reason: "thermal precheck failed".to_string(),
        },
    ));
    records.push(attempt(
        VALID_SAMPLES + 1,
        host_root,
        workload_root,
        AttemptStatus::Cancelled {
            reason: "operator cancellation".to_string(),
        },
    ));
    records
}

fn telemetry_for(records: &[AttemptRecord]) -> BenchmarkTelemetry {
    BenchmarkTelemetry {
        schema_version: BENCHMARK_EVIDENCE_VERSION,
        attempts: records
            .iter()
            .enumerate()
            .map(|(index, record)| AttemptTelemetry {
                attempt_id: record.attempt_id.clone(),
                wall_clock_start_ns: 1_000 + index as u64,
                elapsed_ns: 42,
                process_id: 4242,
                absolute_working_directory: "/data/projects/franken_lean".to_string(),
                counters: Vec::new(),
            })
            .collect(),
    }
}

struct Bundle {
    host: HostProfile,
    workload: WorkloadManifest,
    attempts: Vec<AttemptRecord>,
    telemetry: BenchmarkTelemetry,
}

fn baseline() -> Bundle {
    let host = host();
    let workload = workload();
    let records = attempts(host.root(), workload.root());
    let telemetry = telemetry_for(&records);
    Bundle {
        host,
        workload,
        attempts: records,
        telemetry,
    }
}

fn assemble(run: &str, b: Bundle) -> Result<fln_bench::BenchmarkBundleCandidate, BenchmarkRefusal> {
    assemble_bundle(run, b.host, b.workload, b.attempts, b.telemetry)
}

#[test]
fn a_complete_baseline_bundle_assembles_and_validates() {
    // THE POSITIVE CONTROL. Every mutation cell below is meaningless without
    // it: if this bundle could not assemble, refusals would prove nothing.
    let candidate = assemble("odwj-baseline-complete", baseline())
        .expect("a complete, internally consistent baseline bundle must assemble");

    let summary = candidate.summary.expect("summary must be regenerated");
    assert_eq!(
        summary.valid_samples, VALID_SAMPLES,
        "only the valid attempts may be aggregated"
    );
    assert_eq!(
        summary.excluded_attempts, 2,
        "the invalid and cancelled attempts must be RETAINED and EXCLUDED, not dropped"
    );
    assert_eq!(
        candidate.attempts_started,
        VALID_SAMPLES + 2,
        "every started attempt must remain in the record"
    );
    assert!(
        candidate.claimed_roots.is_some(),
        "a complete bundle must carry its root chain"
    );
}

#[test]
fn a_dropped_raw_attempt_is_refused() {
    // MUTATION: raw sample drop. The attempt vanishes from the record while the
    // started count still claims it.
    let mut b = baseline();
    b.attempts.pop().expect("attempts");
    // telemetry deliberately still describes the full set, so the drop is the
    // only thing that changed about the attempt record itself.
    let refusal =
        assemble("odwj-raw-sample-drop", b).expect_err("a dropped attempt must be refused");
    assert!(
        matches!(
            refusal,
            BenchmarkRefusal::TelemetryLinkMismatch { .. }
                | BenchmarkRefusal::AttemptsStartedMismatch { .. }
        ),
        "expected a link/count refusal naming the dropped attempt, got {refusal:?}"
    );
}

#[test]
fn an_invalid_attempt_relabelled_valid_is_refused_by_name() {
    // MUTATION: invalid attempt averaging. The thermally-invalidated attempt is
    // relabelled Valid, which is exactly how a bad run is made to look clean.
    //
    // I expected the substrate to be unable to refuse this — a relabelled
    // attempt is internally consistent — and wrote a weaker cell asserting only
    // that the aggregate moves. Measured, the substrate is STRONGER than that:
    // the pre-registered stopping rule fixes how many valid samples there may
    // be, so a sixth valid sample against a plan of five is a typed overrun.
    // Pre-registration and invalid-attempt retention turn out to defend each
    // other — you cannot smuggle an attempt into the aggregate without also
    // breaking the sample plan that was frozen before measurement.
    let mut b = baseline();
    let index = usize::try_from(VALID_SAMPLES).expect("fits");
    assert!(
        matches!(b.attempts[index].status, AttemptStatus::InvalidHost { .. }),
        "this cell must relabel the INVALID attempt, not a valid one"
    );
    b.attempts[index].status = AttemptStatus::Valid { measurement: 1 };

    let refusal = assemble("odwj-invalid-averaged", b)
        .expect_err("an invalid attempt relabelled Valid must be refused");
    match refusal {
        BenchmarkRefusal::SamplePlanOverrun { valid, allowed } => {
            assert_eq!(
                valid,
                VALID_SAMPLES + 1,
                "the promoted attempt must be counted"
            );
            assert_eq!(
                allowed, VALID_SAMPLES,
                "the allowance is the pre-registered plan"
            );
        }
        other => panic!("expected SamplePlanOverrun, got {other:?}"),
    }
}

#[test]
fn a_duplicated_attempt_id_from_a_resume_is_refused_by_name() {
    // MUTATION: duplicate resume. A resumed run re-submits an id it already
    // recorded, which would double-count a measurement.
    let mut b = baseline();
    let host_root = b.host.root();
    let workload_root = b.workload.root();
    let mut clash = attempt(
        u32::try_from(b.attempts.len()).expect("fits"),
        host_root,
        workload_root,
        AttemptStatus::Valid {
            measurement: 10_000,
        },
    );
    clash.attempt_id = "odwj-attempt-0".to_string(); // already recorded
    b.attempts.push(clash);
    b.telemetry = telemetry_for(&b.attempts);

    let refusal =
        assemble("odwj-duplicate-resume", b).expect_err("a duplicate attempt id must be refused");
    match refusal {
        BenchmarkRefusal::DuplicateAttemptId { attempt_id } => assert_eq!(
            attempt_id, "odwj-attempt-0",
            "the refusal must name the duplicated attempt"
        ),
        other => panic!("expected DuplicateAttemptId, got {other:?}"),
    }
}

#[test]
fn a_profiled_attempt_under_a_policy_forbidding_profilers_is_refused() {
    // MUTATION: hidden instrumentation. An attempt was measured with a profiler
    // attached under a workload whose policy forbids one; reporting it as a
    // clean measurement understates the overhead odwj requires to be accounted.
    let mut b = baseline();
    assert!(
        !b.workload.host_policy.allow_profiler,
        "this cell requires a policy that forbids profilers"
    );
    b.attempts[0].profiler = ProfilerState::Enabled;

    let refusal = assemble("odwj-hidden-instrumentation", b)
        .expect_err("a profiled attempt must be refused where the policy forbids profilers");
    match refusal {
        BenchmarkRefusal::ProfilerContamination { attempt_id } => assert_eq!(
            attempt_id, "odwj-attempt-0",
            "the refusal must name the contaminated attempt"
        ),
        other => panic!("expected ProfilerContamination, got {other:?}"),
    }
}

#[test]
fn a_profiled_attempt_is_admitted_where_the_policy_allows_one() {
    // Positive control for the cell above: without it, a ProfilerContamination
    // raised unconditionally would keep that test green while making profiled
    // measurement impossible everywhere.
    let mut b = baseline();
    b.workload.host_policy.allow_profiler = true;
    // The workload identity moved, so the attempts must be re-bound to it.
    let workload_root = b.workload.root();
    for record in &mut b.attempts {
        record.workload_root = workload_root;
    }
    b.attempts[0].profiler = ProfilerState::Enabled;

    let outcome = assemble("odwj-declared-instrumentation", b);
    if let Err(BenchmarkRefusal::ProfilerContamination { attempt_id }) = &outcome {
        panic!(
            "a profiled attempt was refused under a policy that ALLOWS profilers \
             (attempt {attempt_id}); the contamination check ignores the policy"
        );
    }
}

#[test]
fn telemetry_that_stops_corresponding_to_the_attempts_is_refused_by_name() {
    // MUTATION: telemetry-root drift. Telemetry is non-semantic by design, so
    // nothing about the measurement changes — which is exactly why a silent
    // drift would leave the operational record describing a different run.
    let mut b = baseline();
    b.telemetry.attempts[2].attempt_id = "odwj-attempt-not-in-this-run".to_string();

    let refusal =
        assemble("odwj-telemetry-drift", b).expect_err("drifted telemetry must be refused");
    match refusal {
        BenchmarkRefusal::TelemetryLinkMismatch { attempt_id } => assert_eq!(
            attempt_id, "odwj-attempt-not-in-this-run",
            "the refusal must name the telemetry record that stopped corresponding"
        ),
        other => panic!("expected TelemetryLinkMismatch, got {other:?}"),
    }
}

#[test]
fn a_run_that_never_reached_its_stopping_rule_is_refused_rather_than_summarised() {
    // MUTATION: partial publication. The run was interrupted before enough
    // valid samples existed; publishing a summary over what it did collect is
    // the shape odwj forbids. The stopping rule is pre-registered, so falling
    // short must refuse rather than quietly summarise fewer samples.
    let mut b = baseline();
    b.attempts.truncate(2); // two valid attempts against a plan demanding five
    for (ordinal, record) in b.attempts.iter_mut().enumerate() {
        record.ordinal = u32::try_from(ordinal).expect("fits");
    }
    b.telemetry = telemetry_for(&b.attempts);

    let refusal = assemble("odwj-partial-publication", b)
        .expect_err("a run short of its pre-registered stopping rule must be refused");
    assert!(
        matches!(refusal, BenchmarkRefusal::SamplePlanUnsatisfied { .. }),
        "expected SamplePlanUnsatisfied, got {refusal:?}"
    );
}
