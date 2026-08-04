//! `linux_host_qualification` — the first named suite of `franken_lean-odwj`
//! (W1 Reference baseline: pinned 32-core x86-64 Linux lane).
//!
//! `crates/fln-bench` is a complete evidence substrate — schemas, statistics,
//! bundle assembly and validation — with, until this file, **zero producers**
//! (bead `fln-bench-apparatus-empty-referent-bkw6`).  This suite is the first
//! real producer against it, and it deliberately produces the cheapest thing
//! odwj needs: the host-qualification verdict that every later workload row
//! depends on.
//!
//! Two properties are load-bearing and are the reason this file is not a
//! restatement of `lib.rs`'s own unit tests:
//!
//! 1. **The facts are cross-checked against an independent source.**  The
//!    substrate derives physical topology by parsing `/proc/cpuinfo`.  This
//!    suite re-derives it from `/sys/devices/system/cpu/*/topology/`, a
//!    different producer for the same truth, and requires the two to agree.
//!    A test that re-ran the substrate's own algorithm would agree with itself
//!    and measure nothing.
//! 2. **The refusal is asserted by its named check, never by "an error".**
//!    `BenchmarkRefusal::HostNotQualified` carries the exact check that failed;
//!    scoring a refusal as "non-zero" would pass for any unrelated reason and
//!    is the failure mode this repository has already paid for elsewhere.
//!
//! What this suite does NOT establish, stated here because odwj's acceptance
//! turns on it: nothing here measures a workload, a cache state, or a timing.
//! It establishes only whether this host may be admitted as a measurement host
//! at all.  On a host that fails admission the honest lane output is a BLOCKED
//! evidence artifact and odwj stays open — which is what this host produces
//! today (no cpufreq governor, no thermal zones, no isolated cores).

#![forbid(unsafe_code)]

use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

use fln_bench::{
    AttemptRecord, AttemptStatus, BENCHMARK_EVIDENCE_VERSION, BenchmarkRefusal, BenchmarkTelemetry,
    CacheCondition, CacheState, Captured, ClaimBinding, ClaimClass, ClaimState,
    ConfidenceAlgorithm, HostProfile, HostQualificationPolicy, LocalBuildIdentity, MeasurementUnit,
    OutlierPolicy, ProfilerState, QuantileAlgorithm, ResourceBounds, SamplePlan, WorkloadKind,
    WorkloadManifest, assemble_bundle, qualify_host,
};
use fln_hash::domain::{Digest, Domain, hash};

/// The build identity of this probe.  It is not the identity of a release
/// measurement binary and must never be reused as one: `build_profile` says
/// `test`, so a bundle carrying it is self-evidently not a baseline artifact.
fn probe_build_identity() -> LocalBuildIdentity<'static> {
    LocalBuildIdentity {
        toolchain_manifest: b"fln-bench::linux_host_qualification/1",
        target_triple: "x86_64-unknown-linux-gnu",
        build_profile: "test",
        enabled_features: &[],
    }
}

fn capture() -> HostProfile {
    HostProfile::capture_local(probe_build_identity())
        .expect("the local host profile must be capturable on a Linux measurement host")
}

/// odwj's host policy: every environmental control the bead names must be
/// attested.  This is the policy a real Reference-baseline workload must carry;
/// a lane that relaxes it is measuring a different host than the one odwj
/// qualifies.
fn strict_baseline_policy() -> HostQualificationPolicy {
    HostQualificationPolicy {
        require_physical_topology: true,
        require_power_governor: true,
        require_thermal_sensors: true,
        require_exclusive_cores: true,
        require_stable_frequency: true,
        require_thermal_stability: true,
        allow_virtualization: false,
        allow_translation: false,
        allow_profiler: false,
    }
}

fn cold_cache_state() -> CacheState {
    CacheState {
        filesystem: CacheCondition::Cold,
        page_cache: CacheCondition::Cold,
        reference_artifacts: CacheCondition::Cold,
        candidate_artifacts: CacheCondition::Cold,
        build_cache: CacheCondition::Cold,
        imported_modules: CacheCondition::Cold,
        daemon: CacheCondition::Cold,
    }
}

fn workload_with(policy: HostQualificationPolicy) -> WorkloadManifest {
    WorkloadManifest {
        schema_version: BENCHMARK_EVIDENCE_VERSION,
        workload_id: "odwj-host-qualification-probe".to_string(),
        // A placeholder kind: this probe measures no workload at all, and the
        // host-admission verdict under test is independent of the operation.
        workload_kind: WorkloadKind::CorpusBuild,
        corpus_root: hash(
            Domain::OperationalMeta,
            b"odwj-host-qualification-probe/corpus",
        ),
        input_order_root: hash(
            Domain::OperationalMeta,
            b"odwj-host-qualification-probe/order",
        ),
        warmup_iterations: 0,
        sample_plan: SamplePlan::FixedValidSamples { samples: 1 },
        quantile_algorithm: QuantileAlgorithm::NearestRankV1,
        confidence_algorithm: ConfidenceAlgorithm::DistributionFreeMedian95V1,
        outlier_policy: OutlierPolicy::RetainAllV1,
        variance_threshold_basis_points: 10_000,
        cache_state: cold_cache_state(),
        unit: MeasurementUnit::Nanoseconds,
        host_policy: policy,
        resource_bounds: ResourceBounds {
            max_attempts: 32,
            max_measurement: 1_000_000_000,
            max_elapsed_ns_per_attempt: 1_000_000_000,
        },
    }
}

fn one_valid_attempt(host_root: Digest, workload_root: Digest) -> Vec<AttemptRecord> {
    vec![AttemptRecord {
        attempt_id: "odwj-host-qualification-probe-0".to_string(),
        ordinal: 0,
        host_root,
        workload_root,
        cache_state: cold_cache_state(),
        profiler: ProfilerState::Disabled,
        status: AttemptStatus::Valid { measurement: 1 },
    }]
}

fn empty_telemetry() -> BenchmarkTelemetry {
    BenchmarkTelemetry {
        schema_version: BENCHMARK_EVIDENCE_VERSION,
        attempts: Vec::new(),
    }
}

/// Re-derive physical cores from sysfs topology, which is a *different*
/// producer from the substrate's `/proc/cpuinfo` parse.
///
/// A physical core is identified by the pair (package id, core id); counting
/// distinct pairs counts cores rather than hardware threads, so an SMT host
/// yields half its logical count.  Returns `None` when sysfs does not expose
/// topology, so the cross-check declines rather than inventing agreement.
fn physical_cores_from_sysfs() -> Option<u64> {
    let mut cores: BTreeSet<(String, String)> = BTreeSet::new();
    for entry in fs::read_dir("/sys/devices/system/cpu").ok()? {
        let entry = entry.ok()?;
        let name = entry.file_name().to_string_lossy().into_owned();
        if !name.starts_with("cpu") || !name[3..].chars().all(|c| c.is_ascii_digit()) {
            continue;
        }
        let topology = entry.path().join("topology");
        let package = fs::read_to_string(topology.join("physical_package_id")).ok()?;
        let core = fs::read_to_string(topology.join("core_id")).ok()?;
        cores.insert((package.trim().to_string(), core.trim().to_string()));
    }
    if cores.is_empty() {
        return None;
    }
    Some(cores.len() as u64)
}

/// Count `thermal_zone*` entries directly, independently of the substrate.
fn thermal_zone_count() -> Option<usize> {
    let entries = fs::read_dir("/sys/class/thermal").ok()?;
    Some(
        entries
            .filter_map(Result::ok)
            .filter(|entry| {
                entry
                    .file_name()
                    .to_string_lossy()
                    .starts_with("thermal_zone")
            })
            .count(),
    )
}

#[test]
fn the_local_host_profile_captures_with_explicit_provenance() {
    let profile = capture();

    assert_eq!(
        profile.schema_version, BENCHMARK_EVIDENCE_VERSION,
        "a captured profile must carry the substrate's evidence version"
    );

    // Every fact a measurement host is compared by must be Observed here.  These
    // are the facts that cannot be Unavailable on any Linux host that could host
    // a baseline at all, so asserting them is not vacuous: a host missing one is
    // not a candidate.
    for (label, present) in [
        ("cpu-sku", profile.cpu_sku.observed_value().is_some()),
        (
            "architecture",
            profile.architecture.observed_value().is_some(),
        ),
        (
            "enabled-logical-cores",
            profile.enabled_logical_cores.observed_value().is_some(),
        ),
        ("ram-bytes", profile.ram_bytes.observed_value().is_some()),
        ("os-release", profile.os_release.observed_value().is_some()),
        (
            "kernel-release",
            profile.kernel_release.observed_value().is_some(),
        ),
        (
            "monotonic-clock",
            profile
                .monotonic_clock_resolution_ns
                .observed_value()
                .is_some(),
        ),
    ] {
        assert!(present, "{label} must be Observed on a Linux host");
    }

    // `Captured` has no `Assumed` variant by construction; an unavailable fact
    // must retain a non-empty reason rather than degrade to a default.  Check
    // the two facts that are Unavailable *by construction* in `capture_local`,
    // so this assertion cannot pass vacuously on a fully-attested host.
    for (label, fact) in [
        ("exclusive-cores", &profile.isolation.exclusive_cores),
        ("thermal-stable", &profile.isolation.thermal_stable),
    ] {
        match fact {
            Captured::Unavailable { reason, .. } => assert!(
                !reason.trim().is_empty(),
                "{label} is Unavailable and must say why"
            ),
            Captured::Observed { .. } => panic!(
                "{label} is Unavailable by construction in capture_local; if that has changed, \
                 this suite and the odwj producer must both be revisited"
            ),
        }
    }
}

#[test]
fn captured_physical_topology_agrees_with_an_independent_sysfs_derivation() {
    let profile = capture();
    let Some(sysfs_cores) = physical_cores_from_sysfs() else {
        // Declining is correct: with no sysfs topology there is no second
        // producer, and agreeing with ourselves would measure nothing.
        eprintln!("sysfs topology unavailable; cross-check declined");
        return;
    };

    let captured = *profile
        .physical_cores
        .observed_value()
        .expect("physical cores must be Observed where sysfs exposes topology");

    assert_eq!(
        captured, sysfs_cores,
        "the substrate's /proc/cpuinfo topology disagrees with sysfs \
         (package-id, core-id) pairs; one of the two producers is wrong"
    );

    let logical = *profile
        .enabled_logical_cores
        .observed_value()
        .expect("logical cores must be Observed");
    assert!(
        captured <= logical,
        "physical cores ({captured}) cannot exceed logical cores ({logical})"
    );

    let smt = *profile
        .smt_enabled
        .observed_value()
        .expect("SMT must be decidable once both core counts are Observed");
    assert_eq!(
        smt,
        logical > captured,
        "the SMT flag must follow from the two core counts"
    );
}

#[test]
fn this_host_is_refused_by_the_strict_baseline_policy_and_the_check_is_named() {
    let profile = capture();
    let workload = workload_with(strict_baseline_policy());
    let host_root = profile.root();
    let workload_root = workload.root();

    let refusal = assemble_bundle(
        "odwj-host-qualification-probe",
        profile,
        workload,
        one_valid_attempt(host_root, workload_root),
        empty_telemetry(),
    )
    .expect_err(
        "no host may pass the strict baseline policy through capture_local alone: \
         exclusive_cores and thermal_stable are Unavailable by construction",
    );

    // The refusal must be the *host* one, and it must name its check.  Scoring
    // "some error" would be satisfied by an unrelated workload or telemetry
    // refusal and would prove nothing about host admission.
    let BenchmarkRefusal::HostNotQualified { check } = refusal else {
        panic!("expected HostNotQualified, got {refusal:?}");
    };

    // Which check fires first is an ordering fact of `validate_host`, so bind
    // the set rather than the order: any of these is a legitimate first refusal
    // on a host lacking environmental attestation.
    const ENVIRONMENTAL_CHECKS: [&str; 5] = [
        "power-governor",
        "thermal-sensors",
        "exclusive-cores",
        "stable-frequency",
        "thermal-stability",
    ];
    assert!(
        ENVIRONMENTAL_CHECKS.contains(&check),
        "expected an environmental-attestation check, got {check:?}"
    );
}

#[test]
fn a_host_that_clears_topology_is_still_refused_for_the_attestations_it_cannot_supply() {
    // Narrow the policy to *only* physical topology: this host does supply it,
    // so the bundle must get past host admission.  Without this cell the test
    // above could pass because `validate_host` refuses everything, and the
    // suite would be a wall rather than a measurement.
    let profile = capture();
    let policy = HostQualificationPolicy {
        require_physical_topology: true,
        require_power_governor: false,
        require_thermal_sensors: false,
        require_exclusive_cores: false,
        require_stable_frequency: false,
        require_thermal_stability: false,
        allow_virtualization: false,
        allow_translation: false,
        allow_profiler: false,
    };
    let workload = workload_with(policy);
    let host_root = profile.root();
    let workload_root = workload.root();

    let outcome = assemble_bundle(
        "odwj-host-qualification-topology-only",
        profile,
        workload,
        one_valid_attempt(host_root, workload_root),
        empty_telemetry(),
    );

    // The positive control: whatever else happens, it must NOT be a host
    // refusal.  A later refusal (telemetry, statistics) is acceptable here and
    // is not this suite's subject; a HostNotQualified is a real regression.
    if let Err(BenchmarkRefusal::HostNotQualified { check }) = outcome {
        panic!(
            "this host supplies physical topology, yet host admission refused on {check:?}; \
             the topology-only control must pass host admission"
        );
    }
}

/// THE ARTIFACT odwj PRESCRIBES FOR THIS HOST.
///
/// odwj's acceptance says in as many words: "A missing or invalid host lane
/// yields a BLOCKED evidence artifact and this task remains open." This cell
/// produces that artifact from the live host and pins what it must and must not
/// contain. It is the honest terminal output of the baseline lane here, and it
/// is deliberately the absence of a measurement made citable.
#[test]
fn this_host_yields_a_blocked_qualification_artifact_naming_every_failing_check() {
    let profile = capture();
    let blocked = qualify_host(&profile, strict_baseline_policy())
        .expect_err("this host cannot satisfy the strict baseline policy");

    assert_eq!(
        blocked.claim,
        ClaimBinding {
            class: ClaimClass::Benchmark,
            state: ClaimState::Blocked,
        },
        "a blocked lane may claim no state other than BLOCKED; anything else \
         would let this artifact read as a weak pass"
    );
    assert_eq!(
        blocked.host_root,
        profile.root(),
        "the artifact must bind the host it judged"
    );

    // EVERY failing check, not the first: an evidence artifact has to say what
    // would need to change, which `validate_host` cannot because it
    // short-circuits at the first refusal.
    assert!(
        blocked.failing_checks.len() >= 2,
        "a short-circuited single check is not an evidence artifact; got {:?}",
        blocked.failing_checks
    );
    assert_eq!(
        blocked.failing_checks,
        {
            let mut sorted = blocked.failing_checks.clone();
            sorted.sort_unstable();
            sorted.dedup();
            sorted
        },
        "failing checks must be sorted and duplicate-free"
    );

    // The artifact must carry no measurement. A blocked lane measured nothing,
    // and emitting a figure anyway is the manufacture this cell exists to stop.
    let line = blocked.ndjson();
    assert!(
        line.contains("\"benchmark_claim_state\":\"BLOCKED\""),
        "{line}"
    );
    assert!(line.contains("\"valid_samples\":0"), "{line}");
    assert!(line.contains("\"measurements\":0"), "{line}");
    assert!(
        line.ends_with('\n'),
        "NDJSON records are newline-terminated"
    );

    // Emit it so a run produces a citable artifact rather than only an
    // assertion. stdout under --nocapture is the retention surface here; no
    // host-specific bytes are committed, because binary_hash moves on every
    // rebuild and a committed copy would be stale the moment it landed.
    eprintln!("odwj-blocked-host-qualification: {line}");
}

#[test]
fn blocked_host_qualification_agrees_with_bundle_admission() {
    // THE JOIN. `qualify_host` is a second reading of the same policy, and a
    // second copy of a predicate that can drift from the enforcing one is the
    // defect this repository names most often. This binds the two: whenever
    // `qualify_host` refuses, `assemble_bundle` must also refuse for a HOST
    // reason, and whenever it admits, `assemble_bundle` must not raise a host
    // refusal. Checked under both a strict and a permissive policy, so it
    // cannot pass by both sides always refusing.
    for (label, policy) in [
        ("strict", strict_baseline_policy()),
        (
            "topology-only",
            HostQualificationPolicy {
                require_physical_topology: true,
                require_power_governor: false,
                require_thermal_sensors: false,
                require_exclusive_cores: false,
                require_stable_frequency: false,
                require_thermal_stability: false,
                allow_virtualization: false,
                allow_translation: false,
                allow_profiler: false,
            },
        ),
    ] {
        let profile = capture();
        let report = qualify_host(&profile, policy);
        let workload = workload_with(policy);
        let host_root = profile.root();
        let workload_root = workload.root();
        let outcome = assemble_bundle(
            "odwj-qualification-join",
            profile,
            workload,
            one_valid_attempt(host_root, workload_root),
            empty_telemetry(),
        );
        let bundle_refused_host = matches!(outcome, Err(BenchmarkRefusal::HostNotQualified { .. }));

        assert_eq!(
            report.is_err(),
            bundle_refused_host,
            "under the {label:?} policy, qualify_host says blocked={} while \
             bundle admission says host-refused={} — the two readings of the \
             same policy have drifted",
            report.is_err(),
            bundle_refused_host
        );

        // Anti-vacuity: the strict policy must refuse and the topology-only one
        // must not, so this loop cannot agree by refusing everything.
        match label {
            "strict" => assert!(report.is_err(), "the strict policy must block this host"),
            _ => assert!(
                report.is_ok(),
                "this host supplies physical topology; blocked on {:?}",
                report.err().map(|b| b.failing_checks)
            ),
        }
    }
}

#[test]
fn virtualization_and_translation_are_attested_rather_than_assumed() {
    let profile = capture();

    let virtualization = profile
        .virtualization
        .observed_value()
        .expect("virtualization must be Observed: absence of a hypervisor is itself a finding");
    assert!(
        virtualization == "hypervisor-detected" || virtualization == "no-hypervisor-flag",
        "unexpected virtualization attestation {virtualization:?}"
    );

    let translation = profile
        .translation
        .observed_value()
        .expect("translation must be Observed");
    assert_eq!(
        translation, "native-target-architecture",
        "a translated (emulated) target cannot host a baseline measurement"
    );
}

/// The thermal-sensor fact is captured from a directory that exists on every
/// modern Linux host, so its *presence* says nothing about whether any sensor
/// does.  This cell pins the producer's contract — the captured text must
/// report the count it actually found — which is the fact a consumer needs in
/// order to decide admission.
///
/// It deliberately asserts the producer, not the policy: whether
/// `require_thermal_sensors` should refuse a zero-sensor host is a substrate
/// question filed separately, and encoding today's answer here would wall the
/// repair.
#[test]
fn the_thermal_sensor_fact_reports_the_count_it_actually_found() {
    let profile = capture();
    let Some(zones) = thermal_zone_count() else {
        eprintln!("/sys/class/thermal unreadable; cross-check declined");
        return;
    };

    match &profile.thermal_sensors {
        Captured::Observed { value, .. } => {
            assert!(
                value.starts_with(&format!("{zones} ")),
                "captured thermal fact {value:?} disagrees with the {zones} zones \
                 independently counted in /sys/class/thermal"
            );
        }
        Captured::Unavailable { reason, .. } => {
            assert!(
                !Path::new("/sys/class/thermal").is_dir(),
                "thermal sensors reported Unavailable ({reason}) while \
                 /sys/class/thermal is readable and holds {zones} zones"
            );
        }
    }
}
