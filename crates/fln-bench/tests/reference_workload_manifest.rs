//! `reference_workload_manifest` — the second named suite of `franken_lean-odwj`.
//!
//! odwj requires that workload order, warmups, sampling/stopping, invalidation,
//! quantile/confidence/dispersion, and outlier and variance rules are
//! **pre-registered before measurement**, and it names "post-observation rule
//! change" among the mutations that must be killed.
//!
//! Pre-registration is only meaningful if two things hold, and this suite
//! measures exactly those two rather than asserting that a manifest can be
//! built:
//!
//! 1. **Every pre-registered rule is bound into the workload root.** A field
//!    that does not move the root could be rewritten after the numbers were
//!    seen and nothing would notice. This is the anti-vacuity property of the
//!    whole scheme, and it is checked field by field: each cell below changes
//!    exactly one rule and requires the root to move. Binding the *count* of
//!    fields, rather than each field, would pass while a specific rule silently
//!    floated free.
//! 2. **A rule changed after the attempts exist is refused by name.** Every
//!    attempt carries the workload root it was measured under, so re-registering
//!    a rule and re-submitting the same attempts must be refused as a
//!    substitution — not merely "an error", which any malformed field would also
//!    produce.
//!
//! What this suite does NOT establish: it does not measure a workload, and it
//! does not show that the *values* pre-registered here are the right ones for a
//! Reference baseline. It shows that whatever is registered cannot be changed
//! afterwards without detection.

#![forbid(unsafe_code)]

use fln_bench::{
    AttemptRecord, AttemptStatus, BENCHMARK_EVIDENCE_VERSION, BenchmarkRefusal, BenchmarkTelemetry,
    CacheCondition, CacheState, ConfidenceAlgorithm, HostQualificationPolicy, MeasurementUnit,
    OutlierPolicy, ProfilerState, QuantileAlgorithm, ResourceBounds, SamplePlan, WorkloadManifest,
    assemble_bundle,
};
use fln_hash::domain::{Digest, Domain, hash};

fn digest(label: &str) -> Digest {
    hash(Domain::OperationalMeta, label.as_bytes())
}

/// A permissive host policy: this suite is about the *workload*, and a host
/// refusal would mask every workload result. The host-admission property is the
/// subject of `linux_host_qualification`, not of this file.
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
        filesystem: CacheCondition::Cold,
        page_cache: CacheCondition::Cold,
        reference_artifacts: CacheCondition::Warm,
        candidate_artifacts: CacheCondition::Cold,
        build_cache: CacheCondition::Cold,
        imported_modules: CacheCondition::Cold,
        daemon: CacheCondition::Cold,
    }
}

/// The pre-registration under test. Every field below is a rule frozen before
/// the first attempt.
fn preregistered() -> WorkloadManifest {
    WorkloadManifest {
        schema_version: BENCHMARK_EVIDENCE_VERSION,
        workload_id: "odwj-reference-baseline".to_string(),
        corpus_root: digest("corpus/mathlib4@pin"),
        input_order_root: digest("input-order/declared"),
        warmup_iterations: 3,
        sample_plan: SamplePlan::FixedValidSamples { samples: 5 },
        quantile_algorithm: QuantileAlgorithm::NearestRankV1,
        confidence_algorithm: ConfidenceAlgorithm::DistributionFreeMedian95V1,
        outlier_policy: OutlierPolicy::RetainAllV1,
        variance_threshold_basis_points: 2_000,
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

/// Each entry renames one pre-registered rule and returns the altered manifest.
/// Adding a rule to `WorkloadManifest` without adding it here leaves that rule
/// unchecked, which is why the list is written out rather than derived from a
/// count.
fn one_rule_changed() -> Vec<(&'static str, WorkloadManifest)> {
    let mut cells: Vec<(&'static str, WorkloadManifest)> = Vec::new();

    let mut m = preregistered();
    m.workload_id = "odwj-reference-baseline-other".to_string();
    cells.push(("workload-id", m));

    let mut m = preregistered();
    m.corpus_root = digest("corpus/mathlib4@different-pin");
    cells.push(("corpus-root", m));

    let mut m = preregistered();
    m.input_order_root = digest("input-order/reshuffled");
    cells.push(("input-order-root", m));

    let mut m = preregistered();
    m.warmup_iterations = 4;
    cells.push(("warmup-iterations", m));

    let mut m = preregistered();
    m.sample_plan = SamplePlan::FixedValidSamples { samples: 6 };
    cells.push(("sample-plan", m));

    // NOT COVERED, and named rather than silently omitted: `quantile_algorithm`
    // and `confidence_algorithm` are single-variant enums today
    // (`NearestRankV1`, `DistributionFreeMedian95V1`), so there is no second
    // value to change and no cell can show they are bound into the root. They
    // are pre-registered rules that this suite cannot yet check. When either
    // enum gains a variant, a cell is owed here — the floor below will not
    // catch that, because it counts cells rather than fields.
    let mut m = preregistered();
    m.outlier_policy = OutlierPolicy::ReportTukeyOnlyV1;
    cells.push(("outlier-policy", m));

    let mut m = preregistered();
    m.variance_threshold_basis_points = 2_500;
    cells.push(("variance-threshold", m));

    let mut m = preregistered();
    m.cache_state.page_cache = CacheCondition::Warm;
    cells.push(("cache-state", m));

    let mut m = preregistered();
    m.unit = MeasurementUnit::Operations;
    cells.push(("unit", m));

    let mut m = preregistered();
    m.host_policy.require_power_governor = true;
    cells.push(("host-policy", m));

    let mut m = preregistered();
    m.resource_bounds.max_attempts = 65;
    cells.push(("resource-bounds", m));

    cells
}

#[test]
fn every_preregistered_rule_is_bound_into_the_workload_root() {
    let baseline = preregistered();
    let baseline_root = baseline.root();

    // Anti-vacuity floor: if the cell list ever empties or is gutted, this test
    // must refuse rather than pass over nothing.
    let cells = one_rule_changed();
    assert!(
        cells.len() >= 11,
        "the pre-registration cell list has shrunk to {}; a rule is going unchecked",
        cells.len()
    );

    for (rule, changed) in cells {
        assert_ne!(
            changed.root(),
            baseline_root,
            "changing the pre-registered rule {rule:?} did not move the workload root, \
             so that rule could be rewritten after the numbers were seen and nothing \
             would detect it"
        );
    }
}

#[test]
fn the_root_is_stable_under_no_change() {
    // The control for the cell above: without it, a `root()` that simply
    // returned a fresh value each call would satisfy every inequality and the
    // suite would be measuring nothing at all.
    assert_eq!(
        preregistered().root(),
        preregistered().root(),
        "the workload root must be a function of the pre-registration, not of the call"
    );
}

fn attempts_bound_to(host_root: Digest, workload_root: Digest, count: u32) -> Vec<AttemptRecord> {
    (0..count)
        .map(|ordinal| AttemptRecord {
            attempt_id: format!("odwj-attempt-{ordinal}"),
            ordinal,
            host_root,
            workload_root,
            cache_state: cache_state(),
            profiler: ProfilerState::Disabled,
            status: AttemptStatus::Valid {
                measurement: 1_000 + u64::from(ordinal),
            },
        })
        .collect()
}

fn telemetry_for(attempts: &[AttemptRecord]) -> BenchmarkTelemetry {
    let _ = attempts;
    BenchmarkTelemetry {
        schema_version: BENCHMARK_EVIDENCE_VERSION,
        attempts: Vec::new(),
    }
}

#[test]
fn a_rule_changed_after_the_attempts_exist_is_refused_as_a_substitution() {
    let host = fln_bench::HostProfile::capture_local(fln_bench::LocalBuildIdentity {
        toolchain_manifest: b"fln-bench::reference_workload_manifest/1",
        target_triple: "x86_64-unknown-linux-gnu",
        build_profile: "test",
        enabled_features: &[],
    })
    .expect("host capture");
    let host_root = host.root();

    let registered = preregistered();
    let attempts = attempts_bound_to(host_root, registered.root(), 5);
    let telemetry = telemetry_for(&attempts);

    // The post-observation rule change: the attempts were measured under
    // `RetainAllV1`, and the manifest is now re-registered as trimming
    // extremes — the classic way to make a noisy run look repeatable.
    let mut rewritten = preregistered();
    rewritten.outlier_policy = OutlierPolicy::ReportTukeyOnlyV1;

    let refusal = assemble_bundle(
        "odwj-post-observation-rule-change",
        host,
        rewritten,
        attempts,
        telemetry,
    )
    .expect_err("a rule rewritten after the attempts were measured must be refused");

    // It must be the substitution refusal specifically. A malformed-field or
    // statistics refusal would also be an `Err`, and scoring "an error" would
    // let this cell pass for a reason that has nothing to do with
    // pre-registration.
    assert!(
        matches!(refusal, BenchmarkRefusal::WorkloadSubstitution { .. }),
        "expected WorkloadSubstitution, got {refusal:?}"
    );
}

#[test]
fn the_same_attempts_under_their_own_registration_are_not_refused_as_a_substitution() {
    // The positive control for the cell above. Without it, `assemble_bundle`
    // refusing every bundle would keep that test green while proving nothing
    // about post-observation changes specifically.
    let host = fln_bench::HostProfile::capture_local(fln_bench::LocalBuildIdentity {
        toolchain_manifest: b"fln-bench::reference_workload_manifest/1",
        target_triple: "x86_64-unknown-linux-gnu",
        build_profile: "test",
        enabled_features: &[],
    })
    .expect("host capture");
    let host_root = host.root();

    let registered = preregistered();
    let attempts = attempts_bound_to(host_root, registered.root(), 5);
    let telemetry = telemetry_for(&attempts);

    let outcome = assemble_bundle(
        "odwj-unchanged-registration",
        host,
        registered,
        attempts,
        telemetry,
    );

    if let Err(BenchmarkRefusal::WorkloadSubstitution { attempt_id }) = &outcome {
        panic!(
            "attempts bound to their own registration were refused as a substitution \
             (attempt {attempt_id}); the substitution check is firing on unchanged input"
        );
    }
}

#[test]
fn a_sampling_rule_that_cannot_be_satisfied_is_refused_by_its_named_field() {
    // Pre-registration must be refused when it is internally impossible, and
    // the refusal must name the field so the operator learns which rule is
    // wrong rather than that "the workload is malformed".
    let mut impossible = preregistered();
    impossible.sample_plan = SamplePlan::FixedValidSamples { samples: 0 };

    let host = fln_bench::HostProfile::capture_local(fln_bench::LocalBuildIdentity {
        toolchain_manifest: b"fln-bench::reference_workload_manifest/1",
        target_triple: "x86_64-unknown-linux-gnu",
        build_profile: "test",
        enabled_features: &[],
    })
    .expect("host capture");
    let host_root = host.root();
    let workload_root = impossible.root();

    let refusal = assemble_bundle(
        "odwj-impossible-sampling",
        host,
        impossible,
        attempts_bound_to(host_root, workload_root, 1),
        BenchmarkTelemetry {
            schema_version: BENCHMARK_EVIDENCE_VERSION,
            attempts: Vec::new(),
        },
    )
    .expect_err("a zero-sample plan can never be satisfied and must be refused");

    match refusal {
        BenchmarkRefusal::MalformedWorkload { field } => assert_eq!(
            field, "fixed-samples",
            "the refusal must name the offending pre-registration field"
        ),
        other => panic!("expected MalformedWorkload{{fixed-samples}}, got {other:?}"),
    }
}

#[test]
fn a_sample_plan_exceeding_its_own_attempt_budget_is_refused() {
    // The stopping rule and the resource budget are separate pre-registrations
    // and can contradict each other: demanding more valid samples than the
    // attempt budget permits is unsatisfiable, and discovering that after
    // measurement starts is exactly what pre-registration exists to prevent.
    let mut contradictory = preregistered();
    contradictory.sample_plan = SamplePlan::FixedValidSamples { samples: 8 };
    contradictory.resource_bounds.max_attempts = 4;

    let host = fln_bench::HostProfile::capture_local(fln_bench::LocalBuildIdentity {
        toolchain_manifest: b"fln-bench::reference_workload_manifest/1",
        target_triple: "x86_64-unknown-linux-gnu",
        build_profile: "test",
        enabled_features: &[],
    })
    .expect("host capture");
    let host_root = host.root();
    let workload_root = contradictory.root();

    let refusal = assemble_bundle(
        "odwj-contradictory-budget",
        host,
        contradictory,
        attempts_bound_to(host_root, workload_root, 1),
        BenchmarkTelemetry {
            schema_version: BENCHMARK_EVIDENCE_VERSION,
            attempts: Vec::new(),
        },
    )
    .expect_err("a stopping rule exceeding the attempt budget must be refused");

    match refusal {
        BenchmarkRefusal::MalformedWorkload { field } => assert_eq!(
            field, "resource-or-variance-bounds",
            "the refusal must name the contradicting budget"
        ),
        other => panic!("expected MalformedWorkload, got {other:?}"),
    }
}
