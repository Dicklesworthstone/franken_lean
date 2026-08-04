//! `reference_kernel_recheck_definition` — odwj's third named suite, and the
//! one that must report a gap rather than a clean kill.
//!
//! odwj demands "explicitly defined kernel recheck of the olean set (not module
//! loading relabeled as checking)" and names two mutations this suite is
//! responsible for: **cache conflation** and **module-load-as-recheck**.
//!
//! # One of those two is killable here, and one is not
//!
//! **Cache conflation IS killable, and this suite kills it.** `CacheState`
//! carries seven independent layers, and the substrate's own doc comment states
//! the law: "A warm daemon cannot masquerade as a warm page cache, and a warm
//! candidate cache cannot be reported as a warm Reference cache." That law is
//! only real if every layer is independently bound into the workload root and
//! independently compared per attempt. Both directions are measured below, layer
//! by layer — not by a count of layers, because a count stays green while one
//! specific layer floats free.
//!
//! **Module-load-as-recheck is NOT killable by this substrate, and saying so is
//! this file's main result.** `WorkloadManifest` has no field expressing what a
//! workload *does*: there is no operation kind, no measured-verb, nothing. The
//! difference between rechecking an olean set and merely loading the modules is
//! carried entirely by
//!
//!   * `workload_id` — a free-form `String` that nothing constrains, and
//!   * `cache_state.imported_modules` — a *cache condition*, not an operation.
//!
//! So a lane that loads modules and registers itself as
//! `"reference-kernel-recheck"` produces a bundle that is valid, internally
//! consistent, and wrong, and no assertion available in this crate can refuse
//! it. That is `fln-bench-apparatus-empty-referent-bkw6`'s shape exactly: the
//! mutation names a property with **no representation to attack**. Writing a
//! cell that asserted today's permissiveness would wall the repair, so this file
//! deliberately does not; the gap is stated here and routed, and the honest
//! repair is a discriminator in the schema, which is not this suite's to add.
//!
//! What is therefore established: the cache layers cannot be conflated. What is
//! NOT established: that a workload calling itself a recheck performed one.

#![forbid(unsafe_code)]

use fln_bench::{
    AttemptRecord, AttemptStatus, BENCHMARK_EVIDENCE_VERSION, BenchmarkRefusal, BenchmarkTelemetry,
    CacheCondition, CacheState, ConfidenceAlgorithm, HostProfile, HostQualificationPolicy,
    LocalBuildIdentity, MeasurementUnit, OutlierPolicy, ProfilerState, QuantileAlgorithm,
    ResourceBounds, SamplePlan, WorkloadKind, WorkloadManifest, assemble_bundle,
};
use fln_hash::domain::{Digest, Domain, hash};

fn host() -> HostProfile {
    HostProfile::capture_local(LocalBuildIdentity {
        toolchain_manifest: b"fln-bench::reference_kernel_recheck_definition/1",
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

/// The cache state a *kernel recheck* of an olean set is measured under: the
/// Reference artifacts are present on disk, and nothing is already imported —
/// if modules were already imported, the thing being timed is not a recheck.
fn recheck_cache_state() -> CacheState {
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

fn workload_under(cache: CacheState) -> WorkloadManifest {
    WorkloadManifest {
        schema_version: BENCHMARK_EVIDENCE_VERSION,
        workload_id: "reference-kernel-recheck".to_string(),
        workload_kind: WorkloadKind::KernelRecheck,
        corpus_root: hash(Domain::OperationalMeta, b"olean-set/reference@pin"),
        input_order_root: hash(Domain::OperationalMeta, b"olean-set/declared-order"),
        warmup_iterations: 0,
        sample_plan: SamplePlan::FixedValidSamples { samples: 3 },
        quantile_algorithm: QuantileAlgorithm::NearestRankV1,
        confidence_algorithm: ConfidenceAlgorithm::DistributionFreeMedian95V1,
        outlier_policy: OutlierPolicy::RetainAllV1,
        variance_threshold_basis_points: 5_000,
        cache_state: cache,
        unit: MeasurementUnit::Nanoseconds,
        host_policy: permissive_host_policy(),
        resource_bounds: ResourceBounds {
            max_attempts: 16,
            max_measurement: 1_000_000_000,
            max_elapsed_ns_per_attempt: 1_000_000_000,
        },
    }
}

/// Every layer of `CacheState`, each paired with a function that changes ONLY
/// that layer. Written out per layer on purpose: binding the number of layers
/// would stay green while one specific layer stopped being compared, which is
/// precisely the conflation this suite exists to refuse.
fn one_layer_changed() -> Vec<(&'static str, CacheState)> {
    let flip = |c: CacheCondition| match c {
        CacheCondition::Cold => CacheCondition::Warm,
        CacheCondition::Warm => CacheCondition::Cold,
        CacheCondition::NotApplicable => CacheCondition::Warm,
    };
    let base = recheck_cache_state();
    let mut cells: Vec<(&'static str, CacheState)> = Vec::new();

    let mut c = base;
    c.filesystem = flip(c.filesystem);
    cells.push(("filesystem", c));

    let mut c = base;
    c.page_cache = flip(c.page_cache);
    cells.push(("page_cache", c));

    let mut c = base;
    c.reference_artifacts = flip(c.reference_artifacts);
    cells.push(("reference_artifacts", c));

    let mut c = base;
    c.candidate_artifacts = flip(c.candidate_artifacts);
    cells.push(("candidate_artifacts", c));

    let mut c = base;
    c.build_cache = flip(c.build_cache);
    cells.push(("build_cache", c));

    let mut c = base;
    c.imported_modules = flip(c.imported_modules);
    cells.push(("imported_modules", c));

    let mut c = base;
    c.daemon = flip(c.daemon);
    cells.push(("daemon", c));

    cells
}

#[test]
fn every_cache_layer_is_independently_bound_into_the_workload_root() {
    let baseline = workload_under(recheck_cache_state());
    let baseline_root = baseline.root();

    let cells = one_layer_changed();
    assert_eq!(
        cells.len(),
        7,
        "CacheState has 7 layers; the cell list holds {} — a layer is unchecked",
        cells.len()
    );

    for (layer, cache) in cells {
        assert_ne!(
            workload_under(cache).root(),
            baseline_root,
            "changing only the {layer:?} cache layer left the workload root unmoved, \
             so that layer can be conflated with another and no evidence would differ"
        );
    }
}

#[test]
fn the_workload_root_is_stable_when_no_layer_changes() {
    // Control for the cell above: a `root()` returning a fresh value per call
    // would satisfy all seven inequalities while measuring nothing.
    assert_eq!(
        workload_under(recheck_cache_state()).root(),
        workload_under(recheck_cache_state()).root(),
        "the workload root must be a function of the cache state, not of the call"
    );
}

fn attempt_with(
    ordinal: u32,
    host_root: Digest,
    workload_root: Digest,
    cache: CacheState,
) -> AttemptRecord {
    AttemptRecord {
        attempt_id: format!("recheck-{ordinal}"),
        ordinal,
        host_root,
        workload_root,
        cache_state: cache,
        profiler: ProfilerState::Disabled,
        status: AttemptStatus::Valid {
            measurement: 10_000 + u64::from(ordinal),
        },
    }
}

fn no_telemetry() -> BenchmarkTelemetry {
    BenchmarkTelemetry {
        schema_version: BENCHMARK_EVIDENCE_VERSION,
        attempts: Vec::new(),
    }
}

#[test]
fn a_valid_attempt_measured_under_a_different_cache_state_is_refused_per_layer() {
    // The root binding above stops a *manifest* being rewritten. This stops an
    // individual attempt measured under different cache conditions from being
    // folded into the aggregate — the conflation that actually corrupts a
    // number, since a warm-import attempt timed as a cold recheck is simply a
    // faster, wrong measurement.
    let workload = workload_under(recheck_cache_state());
    let workload_root = workload.root();
    let h = host();
    let host_root = h.root();

    // Exactly one attempt carries a different `imported_modules` condition: the
    // module-load-versus-recheck confusion in its measurable form.
    let mut warm_import = recheck_cache_state();
    warm_import.imported_modules = CacheCondition::Warm;

    let attempts = vec![
        attempt_with(0, host_root, workload_root, recheck_cache_state()),
        attempt_with(1, host_root, workload_root, warm_import),
        attempt_with(2, host_root, workload_root, recheck_cache_state()),
    ];

    let refusal = assemble_bundle(
        "odwj-cache-conflation",
        h,
        workload,
        attempts,
        no_telemetry(),
    )
    .expect_err("an attempt measured under a different cache state must not be aggregated");

    // Named refusal, not "an error": a malformed-attempt or statistics refusal
    // would also be an Err and would prove nothing about cache conflation.
    match refusal {
        BenchmarkRefusal::CacheStateMismatch { attempt_id } => assert_eq!(
            attempt_id, "recheck-1",
            "the refusal must name the attempt whose cache state differed"
        ),
        other => panic!("expected CacheStateMismatch on recheck-1, got {other:?}"),
    }
}

#[test]
fn attempts_agreeing_with_their_workloads_cache_state_are_not_refused_for_it() {
    // Positive control for the cell above. Without it, `assemble_bundle`
    // refusing every bundle would keep the conflation cell green while proving
    // nothing about cache states specifically.
    let workload = workload_under(recheck_cache_state());
    let workload_root = workload.root();
    let h = host();
    let host_root = h.root();

    let attempts = (0..3)
        .map(|ordinal| attempt_with(ordinal, host_root, workload_root, recheck_cache_state()))
        .collect::<Vec<_>>();

    let outcome = assemble_bundle(
        "odwj-cache-agreement",
        h,
        workload,
        attempts,
        no_telemetry(),
    );

    if let Err(BenchmarkRefusal::CacheStateMismatch { attempt_id }) = &outcome {
        panic!(
            "attempts agreeing with their workload's cache state were refused \
             (attempt {attempt_id}); the cache comparison is firing on unchanged input"
        );
    }
}

/// THE MUTATION THIS SUITE OWES odwj: module-load-as-recheck.
///
/// Before `WorkloadKind` existed this mutation was unkillable, because the
/// property it attacks had nowhere to live — a module-load lane could be
/// byte-identical to a recheck lane. The discriminator gives it a place, and
/// this cell is the kill: two workloads identical in **every other field**,
/// differing only in the declared operation, must not share an identity, and an
/// attempt measured under one must not be admissible under the other.
///
/// Note precisely what this earns. It does **not** establish that a workload
/// declaring `KernelRecheck` performed one — nothing in this crate can witness
/// what a lane actually ran, and no cell here pretends otherwise. What it earns
/// is that the claim is now **explicit, semantic, and falsifiable**: passing a
/// module load off as a recheck now requires writing `KernelRecheck` into a
/// field whose only purpose is that assertion, rather than relying on a
/// free-form `workload_id` string nobody checks.
#[test]
fn a_module_load_cannot_be_presented_as_a_kernel_recheck() {
    let recheck = workload_under(recheck_cache_state());
    assert_eq!(
        recheck.workload_kind,
        WorkloadKind::KernelRecheck,
        "the baseline of this suite must be the recheck kind"
    );

    // Identical in every field except the declared operation — including the
    // cache state, so this cell cannot pass for slice 3's cache reason.
    let mut relabelled = workload_under(recheck_cache_state());
    relabelled.workload_kind = WorkloadKind::ModuleImport;
    assert_eq!(
        relabelled.cache_state, recheck.cache_state,
        "the mutation must differ ONLY in the declared operation"
    );
    assert_eq!(
        relabelled.workload_id, recheck.workload_id,
        "the mutation must differ ONLY in the declared operation"
    );

    assert_ne!(
        relabelled.root(),
        recheck.root(),
        "a module import and a kernel recheck that differ only in the declared \
         operation share a workload identity; the discriminator is not bound \
         into the root and module-load-as-recheck is undetectable again"
    );

    // And the identity is load-bearing rather than cosmetic: an attempt
    // measured as a module import cannot enter a recheck bundle.
    let h = host();
    let host_root = h.root();
    let attempts = vec![attempt_with(
        0,
        host_root,
        relabelled.root(),
        recheck_cache_state(),
    )];

    let refusal = assemble_bundle(
        "odwj-module-load-as-recheck",
        h,
        recheck,
        attempts,
        no_telemetry(),
    )
    .expect_err("an attempt measured as a module import must not enter a recheck bundle");

    assert!(
        matches!(refusal, BenchmarkRefusal::WorkloadSubstitution { .. }),
        "expected WorkloadSubstitution, got {refusal:?}"
    );
}

#[test]
fn every_workload_kind_has_a_distinct_identity() {
    // Anti-vacuity for the kill above: if two kinds shared a wire tag, the
    // mutation cell could pass for one pair while another pair silently
    // collided. All eight are compared pairwise.
    let mut roots = Vec::new();
    for kind in WorkloadKind::ALL {
        let mut w = workload_under(recheck_cache_state());
        w.workload_kind = kind;
        roots.push((kind, w.root()));
    }
    assert_eq!(roots.len(), 8, "WorkloadKind::ALL must list every variant");

    for (i, (kind_a, root_a)) in roots.iter().enumerate() {
        for (kind_b, root_b) in roots.iter().skip(i + 1) {
            assert_ne!(
                root_a, root_b,
                "workload kinds {kind_a:?} and {kind_b:?} produce the same workload \
                 root, so one can be substituted for the other undetected"
            );
        }
    }
}

/// A recheck and a module-load differ in `imported_modules`, so *when the lane
/// records that layer honestly* the two workloads are distinct identities and
/// attempts cannot cross between them.
///
/// This is the strongest statement the current schema supports, and it is
/// strictly weaker than odwj's requirement: it holds only if the producer
/// records the cache layer truthfully. Nothing here — and nothing in this crate
/// — refuses a module-load lane that declares `imported_modules: Cold` and calls
/// itself a recheck.
#[test]
fn a_recheck_and_a_module_load_are_distinct_identities_when_recorded_honestly() {
    let recheck = workload_under(recheck_cache_state());

    let mut module_load_cache = recheck_cache_state();
    module_load_cache.imported_modules = CacheCondition::Warm;
    let module_load = workload_under(module_load_cache);

    assert_ne!(
        recheck.root(),
        module_load.root(),
        "a recheck and a module load recorded honestly must not share a workload identity"
    );

    // And an attempt from one cannot be presented under the other.
    let h = host();
    let host_root = h.root();
    let attempts = vec![attempt_with(
        0,
        host_root,
        module_load.root(),
        module_load_cache,
    )];

    let refusal = assemble_bundle(
        "odwj-crossed-identity",
        h,
        recheck,
        attempts,
        no_telemetry(),
    )
    .expect_err("an attempt from the module-load workload must not enter the recheck bundle");

    assert!(
        matches!(refusal, BenchmarkRefusal::WorkloadSubstitution { .. }),
        "expected WorkloadSubstitution, got {refusal:?}"
    );
}
