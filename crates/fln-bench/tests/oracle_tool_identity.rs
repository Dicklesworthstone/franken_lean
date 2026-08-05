//! `oracle_tool_identity` — odwj's fifth named suite, and the home of its
//! eleventh declared mutation, **CaDiCaL identity loss**.
//!
//! odwj requires "bv_decide with the exact CaDiCaL binary identity" and names
//! that identity's loss among the mutations that must be killed. Until
//! `OracleToolIdentity` existed the mutation was **unkillable**, for the same
//! reason `module-load-as-recheck` was before `WorkloadKind`: the property had
//! nowhere to live. The substrate's only semantic identity slots were
//! `HostProfile::toolchain_hash` (the *Rust* toolchain) and `binary_hash` (the
//! measurement executable), neither of which can name an external solver.
//!
//! The trap this suite exists to close is that the *obvious* place to record it
//! is provably the wrong one. `AttemptTelemetry` is **non-semantic by the
//! crate's own stated law** — changing it must move the telemetry and bundle
//! roots *without* moving the semantic root. An identity recorded there could be
//! swapped with no semantic consequence at all, which is precisely the mutation
//! dressed as its own remedy.
//!
//! What this suite does NOT establish: that the declared tool is the tool that
//! ran. Nothing in `fln-bench` can witness execution — the same honest limit
//! `WorkloadKind` carries. What it establishes is that the claim is explicit,
//! semantic, and falsifiable.

#![forbid(unsafe_code)]

use fln_bench::{
    AttemptRecord, AttemptStatus, BENCHMARK_EVIDENCE_VERSION, BenchmarkRefusal, BenchmarkTelemetry,
    CacheCondition, CacheState, ConfidenceAlgorithm, HostProfile, HostQualificationPolicy,
    LocalBuildIdentity, MeasurementUnit, OracleToolIdentity, OutlierPolicy, ProfilerState,
    QuantileAlgorithm, ResourceBounds, SamplePlan, WorkloadKind, WorkloadManifest, assemble_bundle,
};
use fln_hash::domain::{Digest, Domain, hash};

fn host() -> HostProfile {
    HostProfile::capture_local(LocalBuildIdentity {
        toolchain_manifest: b"fln-bench::oracle_tool_identity/1",
        target_triple: "x86_64-unknown-linux-gnu",
        build_profile: "test",
        enabled_features: &[],
    })
    .expect("host capture")
}

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

fn cadical(bytes: &[u8]) -> OracleToolIdentity {
    OracleToolIdentity {
        name: "cadical".to_string(),
        binary_hash: hash(Domain::OperationalMeta, bytes),
    }
}

/// A `bv_decide` workload — odwj's one required row whose measurement depends on
/// an oracle-side solver.
fn bv_decide_with(tools: Vec<OracleToolIdentity>) -> WorkloadManifest {
    WorkloadManifest {
        schema_version: BENCHMARK_EVIDENCE_VERSION,
        workload_id: "odwj-bv-decide".to_string(),
        workload_kind: WorkloadKind::BvDecide,
        oracle_tools: tools,
        corpus_root: hash(Domain::OperationalMeta, b"corpus/bv-decide"),
        input_order_root: hash(Domain::OperationalMeta, b"corpus/bv-decide/order"),
        warmup_iterations: 0,
        sample_plan: SamplePlan::FixedValidSamples { samples: 1 },
        quantile_algorithm: QuantileAlgorithm::NearestRankV1,
        confidence_algorithm: ConfidenceAlgorithm::DistributionFreeMedian95V1,
        outlier_policy: OutlierPolicy::RetainAllV1,
        variance_threshold_basis_points: 10_000,
        cache_state: cache_state(),
        unit: MeasurementUnit::Nanoseconds,
        host_policy: permissive_host_policy(),
        resource_bounds: ResourceBounds {
            max_attempts: 16,
            max_measurement: 1_000_000_000,
            max_elapsed_ns_per_attempt: 1_000_000_000,
        },
    }
}

fn one_attempt(host_root: Digest, workload_root: Digest) -> Vec<AttemptRecord> {
    vec![AttemptRecord {
        attempt_id: "odwj-bv-decide-0".to_string(),
        ordinal: 0,
        host_root,
        workload_root,
        cache_state: cache_state(),
        profiler: ProfilerState::Disabled,
        status: AttemptStatus::Valid { measurement: 1 },
    }]
}

fn no_telemetry() -> BenchmarkTelemetry {
    BenchmarkTelemetry {
        schema_version: BENCHMARK_EVIDENCE_VERSION,
        attempts: Vec::new(),
    }
}

/// THE MUTATION odwj OWES: CaDiCaL identity loss.
///
/// Two workloads identical in **every other field** — same id, same kind, same
/// corpus, same cache state, same bounds — differing only in the solver's binary
/// hash. They must not share an identity, and an attempt measured under one must
/// not be admissible under the other.
#[test]
fn a_swapped_oracle_binary_cannot_reuse_the_workload_identity() {
    let measured = bv_decide_with(vec![cadical(b"cadical-2.0.0-bytes")]);
    let swapped = bv_decide_with(vec![cadical(b"cadical-1.9.5-DIFFERENT-bytes")]);

    assert_eq!(
        measured.workload_id, swapped.workload_id,
        "the mutation must differ ONLY in the solver binary"
    );
    assert_eq!(measured.cache_state, swapped.cache_state);
    assert_eq!(measured.workload_kind, swapped.workload_kind);

    assert_ne!(
        measured.root(),
        swapped.root(),
        "two bv_decide workloads differing only in the CaDiCaL binary share a \
         workload identity; the oracle tool identity is not bound into the root \
         and CaDiCaL identity loss is undetectable again"
    );

    // And the identity is load-bearing rather than cosmetic: an attempt measured
    // under one solver cannot enter a bundle claiming the other.
    let h = host();
    let host_root = h.root();
    let attempts = one_attempt(host_root, swapped.root());
    let refusal = assemble_bundle("odwj-oracle-swap", h, measured, attempts, no_telemetry())
        .expect_err("an attempt measured under a different solver must not be admitted");
    assert!(
        matches!(refusal, BenchmarkRefusal::WorkloadSubstitution { .. }),
        "expected WorkloadSubstitution, got {refusal:?}"
    );
}

/// The control that stops the cell above passing for the wrong reason: the same
/// tool list must produce the same identity. Without it, a `root()` that mixed in
/// anything unstable would satisfy the inequality and measure nothing.
#[test]
fn the_same_oracle_tool_list_yields_the_same_identity() {
    assert_eq!(
        bv_decide_with(vec![cadical(b"cadical-2.0.0-bytes")]).root(),
        bv_decide_with(vec![cadical(b"cadical-2.0.0-bytes")]).root(),
        "the workload root must be a function of the declared tools, not of the call"
    );
}

/// An empty list is a positive declaration that no external tool participated,
/// so it must be a *different* identity from a workload that declares one —
/// otherwise "no oracle tool" and "some oracle tool" are indistinguishable.
#[test]
fn declaring_no_oracle_tool_is_distinct_from_declaring_one() {
    assert_ne!(
        bv_decide_with(Vec::new()).root(),
        bv_decide_with(vec![cadical(b"cadical-2.0.0-bytes")]).root(),
        "a workload declaring NO oracle tool shares an identity with one declaring \
         a solver; the empty declaration carries no information"
    );
}

/// Order must not be free, or the same set of tools in two orders would be two
/// identities and a re-registration could be passed off as a different workload.
#[test]
fn an_unsorted_or_duplicated_tool_list_is_refused_by_its_named_field() {
    let h = host();
    let host_root = h.root();

    for (label, tools) in [
        (
            "unsorted",
            vec![
                cadical(b"z"),
                OracleToolIdentity {
                    name: "abzu".to_string(),
                    binary_hash: hash(Domain::OperationalMeta, b"a"),
                },
            ],
        ),
        ("duplicated", vec![cadical(b"x"), cadical(b"y")]),
    ] {
        let workload = bv_decide_with(tools);
        let workload_root = workload.root();
        let refusal = assemble_bundle(
            "odwj-oracle-order",
            host().clone(),
            workload,
            one_attempt(host_root, workload_root),
            no_telemetry(),
        )
        .unwrap_err();
        match refusal {
            BenchmarkRefusal::MalformedWorkload { field } => assert_eq!(
                field, "oracle-tools",
                "the {label} list must be refused by its own named field"
            ),
            other => {
                panic!("expected MalformedWorkload{{oracle-tools}} for {label}, got {other:?}")
            }
        }
    }

    // Positive control: a correctly sorted, duplicate-free list is NOT refused
    // for this reason, so the check above is not a blanket ban on oracle tools.
    let good = bv_decide_with(vec![
        OracleToolIdentity {
            name: "abzu".to_string(),
            binary_hash: hash(Domain::OperationalMeta, b"a"),
        },
        cadical(b"z"),
    ]);
    let good_root = good.root();
    if let Err(BenchmarkRefusal::MalformedWorkload { field }) = assemble_bundle(
        "odwj-oracle-good",
        h,
        good,
        one_attempt(host_root, good_root),
        no_telemetry(),
    ) && field == "oracle-tools"
    {
        panic!("a sorted, duplicate-free oracle tool list was refused as malformed");
    }
}
