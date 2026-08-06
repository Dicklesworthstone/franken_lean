//! Neutral benchmark-evidence substrate (plan §19; bead `fln-9wya`).
//!
//! This crate does not run a product benchmark and does not own a target threshold.
//! It owns the evidence boundary shared by those downstream systems:
//!
//! * one captured host profile per bundle;
//! * one preregistered workload and cache state;
//! * every started raw attempt, including invalid and interrupted attempts;
//! * deterministic, exact statistics regenerated from valid attempts;
//! * schema-headed semantic and telemetry roots;
//! * publication authority that can only be obtained from the independent validator.
//!
//! Benchmark observations are D7 benchmark evidence, repeatability decisions are
//! statistical evidence, and performance targets are SLOs.  [`ClaimState::Proven`]
//! is representable so a hostile bundle can try the promotion and be refused; no
//! benchmark result can earn that state here.

#![forbid(unsafe_code)]

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;

use fln_hash::canon::{CanonError, CanonReader, CanonWriter, Canonical, SchemaId};
use fln_hash::domain::{Digest, Domain, hash};

/// Bumped 1 -> 2 by `franken_lean-odwj` when [`WorkloadKind`] was added,
/// 2 -> 3 by the same bead when [`OracleToolIdentity`] was added, and 3 -> 4
/// by `fln-odva` when the thermal-zone population became a typed host fact.
///
/// All six schema ids below share this version deliberately, so the durable
/// shapes move together and `read_supported_evidence_version` refuses any other
/// version outright rather than guessing at a layout. Version 1 bytes are
/// therefore rejected rather than silently reinterpreted — there are no
/// persisted older-version bundles, which is exactly why each discriminator
/// was added now rather than after baselines existed.
pub const BENCHMARK_EVIDENCE_VERSION: u16 = 4;

pub const BENCHMARK_HOST_PROFILE_SCHEMA: SchemaId = SchemaId {
    name: "fln.bench.host-profile",
    version: BENCHMARK_EVIDENCE_VERSION,
};
pub const BENCHMARK_WORKLOAD_SCHEMA: SchemaId = SchemaId {
    name: "fln.bench.workload",
    version: BENCHMARK_EVIDENCE_VERSION,
};
pub const BENCHMARK_ATTEMPTS_SCHEMA: SchemaId = SchemaId {
    name: "fln.bench.attempts",
    version: BENCHMARK_EVIDENCE_VERSION,
};
pub const BENCHMARK_SUMMARY_SCHEMA: SchemaId = SchemaId {
    name: "fln.bench.summary",
    version: BENCHMARK_EVIDENCE_VERSION,
};
pub const BENCHMARK_TELEMETRY_SCHEMA: SchemaId = SchemaId {
    name: "fln.bench.telemetry",
    version: BENCHMARK_EVIDENCE_VERSION,
};
pub const BENCHMARK_BUNDLE_SCHEMA: SchemaId = SchemaId {
    name: "fln.bench.bundle",
    version: BENCHMARK_EVIDENCE_VERSION,
};

/// The six durable benchmark-evidence shapes.
///
/// A kind identifies a byte shape, not an evidence claim. Registering one does not
/// make a workload measured, a host qualified, or a bundle publishable.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum BenchmarkSchemaKind {
    HostProfile,
    Workload,
    RawAttempts,
    StatisticalSummary,
    Telemetry,
    Bundle,
}

impl BenchmarkSchemaKind {
    pub const ALL: [Self; 6] = [
        Self::HostProfile,
        Self::Workload,
        Self::RawAttempts,
        Self::StatisticalSummary,
        Self::Telemetry,
        Self::Bundle,
    ];
}

/// One registered durable shape owned by `fln-bench`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BenchmarkSchemaRow {
    pub kind: BenchmarkSchemaKind,
    pub id: SchemaId,
    pub covers: &'static str,
}

/// Complete local registry for the durable benchmark evidence surface.
///
/// The rows deliberately contain no claim state or publication authority. Those can
/// only come from [`validate_bundle`]; a schema row proves that bytes have a named,
/// versioned shape and nothing more.
pub const BENCHMARK_SCHEMA_REGISTRY: [BenchmarkSchemaRow; 6] = [
    BenchmarkSchemaRow {
        kind: BenchmarkSchemaKind::HostProfile,
        id: BENCHMARK_HOST_PROFILE_SCHEMA,
        covers: "captured host identity, build identity, capabilities, and isolation facts",
    },
    BenchmarkSchemaRow {
        kind: BenchmarkSchemaKind::Workload,
        id: BENCHMARK_WORKLOAD_SCHEMA,
        covers: "predeclared workload, sample policy, cache state, and resource bounds",
    },
    BenchmarkSchemaRow {
        kind: BenchmarkSchemaKind::RawAttempts,
        id: BENCHMARK_ATTEMPTS_SCHEMA,
        covers: "every started raw attempt, including invalid and interrupted attempts",
    },
    BenchmarkSchemaRow {
        kind: BenchmarkSchemaKind::StatisticalSummary,
        id: BENCHMARK_SUMMARY_SCHEMA,
        covers: "deterministically regenerated distribution and tail statistics",
    },
    BenchmarkSchemaRow {
        kind: BenchmarkSchemaKind::Telemetry,
        id: BENCHMARK_TELEMETRY_SCHEMA,
        covers: "operational attempt telemetry excluded from semantic benchmark identity",
    },
    BenchmarkSchemaRow {
        kind: BenchmarkSchemaKind::Bundle,
        id: BENCHMARK_BUNDLE_SCHEMA,
        covers: "candidate evidence bundle joining claims, durable components, and roots",
    },
];

/// Typed refusal at the schema-admission boundary.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BenchmarkSchemaRefusal {
    UnknownName {
        name: String,
    },
    UnsupportedVersion {
        name: &'static str,
        seen: u16,
        supported: u16,
    },
}

impl BenchmarkSchemaRefusal {
    pub const fn finding_code(&self) -> &'static str {
        match self {
            Self::UnknownName { .. } => "FLN-BENCH-SCHEMA-001",
            Self::UnsupportedVersion { .. } => "FLN-BENCH-SCHEMA-002",
        }
    }
}

/// Decode or schema-admission failure for one independently stored evidence shape.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BenchmarkSchemaValidationError {
    Decode(CanonError),
    Refused(BenchmarkSchemaRefusal),
}

impl From<CanonError> for BenchmarkSchemaValidationError {
    fn from(error: CanonError) -> Self {
        Self::Decode(error)
    }
}

impl From<BenchmarkSchemaRefusal> for BenchmarkSchemaValidationError {
    fn from(error: BenchmarkSchemaRefusal) -> Self {
        Self::Refused(error)
    }
}

/// Resolve an exact benchmark schema identity.
///
/// Looking up by name and then silently choosing the only decoder is forbidden: the
/// caller must also present the registered version.
pub fn registered_benchmark_schema(
    name: &str,
    version: u16,
) -> Result<&'static BenchmarkSchemaRow, BenchmarkSchemaRefusal> {
    let Some(row) = BENCHMARK_SCHEMA_REGISTRY
        .iter()
        .find(|row| row.id.name == name)
    else {
        return Err(BenchmarkSchemaRefusal::UnknownName {
            name: name.to_string(),
        });
    };
    if version != row.id.version {
        return Err(BenchmarkSchemaRefusal::UnsupportedVersion {
            name: row.id.name,
            seen: version,
            supported: row.id.version,
        });
    }
    Ok(row)
}

pub const MAX_VALID_SAMPLES: u32 = 127;
pub const MAX_ATTEMPTS: u32 = 10_000;
pub const MAX_TEXT_BYTES: usize = 16 * 1024;
pub const MAX_FEATURES: usize = 256;
pub const MAX_COUNTERS_PER_ATTEMPT: usize = 128;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum CaptureSource {
    Procfs,
    Sysfs,
    OperatingSystem,
    RuntimeProbe,
    BuildMetadata,
}

/// A captured fact has explicit provenance.  There is intentionally no `Assumed`
/// variant, and unavailable facts retain the failed source and reason.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Captured<T> {
    Observed {
        value: T,
        source: CaptureSource,
    },
    Unavailable {
        source: CaptureSource,
        reason: String,
    },
}

impl<T> Captured<T> {
    pub const fn observed(value: T, source: CaptureSource) -> Self {
        Self::Observed { value, source }
    }

    pub fn unavailable(source: CaptureSource, reason: impl Into<String>) -> Self {
        Self::Unavailable {
            source,
            reason: reason.into(),
        }
    }

    pub const fn observed_value(&self) -> Option<&T> {
        match self {
            Self::Observed { value, .. } => Some(value),
            Self::Unavailable { .. } => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HostIsolation {
    pub exclusive_cores: Captured<bool>,
    pub stable_frequency: Captured<bool>,
    pub thermal_stable: Captured<bool>,
}

/// The comparison identity of one measurement host and executable.
///
/// Absolute paths, process ids, and wall-clock timestamps are excluded; they belong
/// to linked telemetry and therefore cannot change the semantic result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HostProfile {
    pub schema_version: u16,
    pub cpu_sku: Captured<String>,
    pub architecture: Captured<String>,
    pub physical_cores: Captured<u64>,
    pub enabled_logical_cores: Captured<u64>,
    pub smt_enabled: Captured<bool>,
    pub ram_bytes: Captured<u64>,
    pub storage_device: Captured<String>,
    pub filesystem: Captured<String>,
    pub os_release: Captured<String>,
    pub kernel_release: Captured<String>,
    pub power_governor: Captured<String>,
    pub thermal_policy: Captured<String>,
    /// Number of `thermal_zone*` entries observed by the same sysfs read that
    /// produced [`Self::thermal_sensors`]. Admission consumes this typed fact;
    /// the display text is never parsed back into policy.
    pub thermal_sensor_count: Captured<u64>,
    pub thermal_sensors: Captured<String>,
    pub virtualization: Captured<String>,
    pub translation: Captured<String>,
    pub toolchain_hash: Digest,
    pub binary_hash: Digest,
    pub target_triple: Captured<String>,
    pub build_profile: Captured<String>,
    pub enabled_features: Vec<String>,
    pub monotonic_clock_resolution_ns: Captured<u64>,
    pub counter_capabilities: Vec<String>,
    pub isolation: HostIsolation,
}

#[derive(Debug, Clone)]
pub struct LocalBuildIdentity<'a> {
    /// The exact toolchain manifest or equivalent captured bytes.
    pub toolchain_manifest: &'a [u8],
    pub target_triple: &'a str,
    pub build_profile: &'a str,
    pub enabled_features: &'a [&'a str],
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HostCaptureError {
    CurrentExecutable { message: String },
    ReadExecutable { path: PathBuf, message: String },
}

impl std::fmt::Display for HostCaptureError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::CurrentExecutable { message } => {
                write!(f, "cannot resolve current benchmark executable: {message}")
            }
            Self::ReadExecutable { path, message } => {
                write!(
                    f,
                    "cannot read benchmark executable {}: {message}",
                    path.display()
                )
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CacheCondition {
    Cold,
    Warm,
    NotApplicable,
}

/// Cache layers stay independent.  A warm daemon cannot masquerade as a warm page
/// cache, and a warm candidate cache cannot be reported as a warm Reference cache.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CacheState {
    pub filesystem: CacheCondition,
    pub page_cache: CacheCondition,
    pub reference_artifacts: CacheCondition,
    pub candidate_artifacts: CacheCondition,
    pub build_cache: CacheCondition,
    pub imported_modules: CacheCondition,
    pub daemon: CacheCondition,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MeasurementUnit {
    Nanoseconds,
    Bytes,
    Operations,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SamplePlan {
    FixedValidSamples {
        samples: u32,
    },
    RelativeMad {
        min_valid: u32,
        max_valid: u32,
        threshold_basis_points: u32,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuantileAlgorithm {
    NearestRankV1,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConfidenceAlgorithm {
    DistributionFreeMedian95V1,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OutlierPolicy {
    RetainAllV1,
    ReportTukeyOnlyV1,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HostQualificationPolicy {
    pub require_physical_topology: bool,
    pub require_power_governor: bool,
    pub require_thermal_sensors: bool,
    pub require_exclusive_cores: bool,
    pub require_stable_frequency: bool,
    pub require_thermal_stability: bool,
    pub allow_virtualization: bool,
    pub allow_translation: bool,
    pub allow_profiler: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ResourceBounds {
    pub max_attempts: u32,
    pub max_measurement: u64,
    pub max_elapsed_ns_per_attempt: u64,
}

/// What a workload actually DOES, as a first-class declaration.
///
/// Added by `franken_lean-odwj`. Before it existed, the manifest carried no
/// representation of the measured operation at all: the difference between
/// rechecking an olean set and merely loading the modules lived in
/// `workload_id`, a free-form string nothing constrains, and in
/// `cache_state.imported_modules`, which is a cache *condition* rather than an
/// operation. A lane that loaded modules and called itself a recheck produced a
/// bundle that was valid, internally consistent, and wrong.
///
/// odwj requires the "module-load-as-recheck" mutation to be killed, and a
/// mutation cannot be killed while the property it attacks has nowhere to live
/// (`fln-bench-apparatus-empty-referent-bkw6`). This enum is that place. It does
/// not make a declaration *true* — nothing in this crate can witness what a
/// lane actually ran — but it makes the claim explicit, bound into the workload
/// root, and therefore falsifiable by review and refusable when it contradicts
/// the cache state declared alongside it.
///
/// The variants are odwj's own required workload matrix, so a row of that matrix
/// cannot be measured without saying which row it is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WorkloadKind {
    /// Full-Corpus build wall time, cold or warm per the declared cache state.
    CorpusBuild,
    /// Per-file elaboration latency.
    Elaboration,
    /// Kernel recheck of an olean set. Distinct from [`Self::ModuleImport`] by
    /// construction: this is the "not module loading relabeled as checking"
    /// requirement expressed as a type rather than as a naming convention.
    KernelRecheck,
    /// Loading/importing modules. The operation most easily mistaken for — or
    /// passed off as — a recheck.
    ModuleImport,
    /// Server worker import/attach and resident set size.
    ServerAttach,
    /// First-goal latency in an editor session.
    FirstGoalLatency,
    /// Interpreter micro-corpus.
    InterpreterMicro,
    /// `bv_decide`, whose oracle-side tool identity is D4 and lives in the
    /// Tribunal baseline only, never as a FrankenLean runtime dependency.
    BvDecide,
}

impl WorkloadKind {
    /// Every variant, so a scan over kinds cannot silently miss one.
    pub const ALL: [Self; 8] = [
        Self::CorpusBuild,
        Self::Elaboration,
        Self::KernelRecheck,
        Self::ModuleImport,
        Self::ServerAttach,
        Self::FirstGoalLatency,
        Self::InterpreterMicro,
        Self::BvDecide,
    ];

    /// The stable wire tag. Written out per variant rather than derived from
    /// discriminant order, so reordering the enum cannot silently reinterpret
    /// persisted bytes.
    const fn tag(self) -> u8 {
        match self {
            Self::CorpusBuild => 0,
            Self::Elaboration => 1,
            Self::KernelRecheck => 2,
            Self::ModuleImport => 3,
            Self::ServerAttach => 4,
            Self::FirstGoalLatency => 5,
            Self::InterpreterMicro => 6,
            Self::BvDecide => 7,
        }
    }

    const fn from_tag(tag: u8) -> Option<Self> {
        match tag {
            0 => Some(Self::CorpusBuild),
            1 => Some(Self::Elaboration),
            2 => Some(Self::KernelRecheck),
            3 => Some(Self::ModuleImport),
            4 => Some(Self::ServerAttach),
            5 => Some(Self::FirstGoalLatency),
            6 => Some(Self::InterpreterMicro),
            7 => Some(Self::BvDecide),
            _ => None,
        }
    }
}

/// Identity of one external, oracle-side tool a workload's measurement depends
/// on.
///
/// Added by `franken_lean-odwj`. odwj requires the "CaDiCaL identity loss"
/// mutation to be killed, and before this type existed there was nowhere for
/// that identity to live: the only semantic identity slots in the substrate were
/// [`HostProfile::toolchain_hash`] (the *Rust* toolchain) and `binary_hash` (the
/// measurement executable), neither of which can name an external solver. The
/// obvious alternative — recording it in [`AttemptTelemetry`] — is worse than
/// nothing, because telemetry is *non-semantic by this crate's own stated law*:
/// changing it must move the telemetry and bundle roots **without** moving the
/// semantic root. An identity recorded there could be swapped with no semantic
/// consequence, which is precisely the mutation.
///
/// **D4/Tribunal-side only.** These are tools the *oracle* runs. Recording one
/// here does not admit it into FrankenLean: D2's two inherited tools are
/// unchanged, and nothing in this crate executes anything named here.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct OracleToolIdentity {
    /// Stable tool name, e.g. `"cadical"`.
    pub name: String,
    /// Digest of the tool **binary**, not of its version string. A version
    /// string is a claim the tool makes about itself; the binary hash is a fact
    /// about the bytes that produced the oracle's side of the comparison.
    pub binary_hash: Digest,
}

/// Frozen before the first attempt.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WorkloadManifest {
    pub schema_version: u16,
    pub workload_id: String,
    /// What this workload measures. See [`WorkloadKind`].
    pub workload_kind: WorkloadKind,
    /// Oracle-side tools this workload's measurement depends on, sorted by name
    /// and duplicate-free.
    ///
    /// **Empty is a positive declaration**, not an absence of information: it
    /// states that no external tool participated. Most workloads carry none.
    pub oracle_tools: Vec<OracleToolIdentity>,
    pub corpus_root: Digest,
    pub input_order_root: Digest,
    pub warmup_iterations: u32,
    pub sample_plan: SamplePlan,
    pub quantile_algorithm: QuantileAlgorithm,
    pub confidence_algorithm: ConfidenceAlgorithm,
    pub outlier_policy: OutlierPolicy,
    /// Predeclared repeatability decision over median absolute deviation.
    pub variance_threshold_basis_points: u32,
    pub cache_state: CacheState,
    pub unit: MeasurementUnit,
    pub host_policy: HostQualificationPolicy,
    pub resource_bounds: ResourceBounds,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProfilerState {
    Disabled,
    Enabled,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResourceKind {
    Time,
    Memory,
    Operations,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AttemptStatus {
    Valid {
        measurement: u64,
    },
    InvalidHost {
        reason: String,
    },
    Cancelled {
        reason: String,
    },
    ResourceRefused {
        resource: ResourceKind,
        allowed: u64,
        observed: u64,
    },
    TargetFailed {
        exit_code: i32,
    },
    InfrastructureFault {
        code: String,
    },
    InsufficientSample {
        valid_observed: u32,
        valid_required: u32,
    },
}

/// One immutable raw attempt.  Status, cache, host, workload, and profiler state are
/// semantic because they decide whether the measurement enters the aggregate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AttemptRecord {
    pub attempt_id: String,
    pub ordinal: u32,
    pub host_root: Digest,
    pub workload_root: Digest,
    pub cache_state: CacheState,
    pub profiler: ProfilerState,
    pub status: AttemptStatus,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClaimClass {
    Benchmark,
    Statistical,
    Slo,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClaimState {
    Observed,
    Targeted,
    Hypothesis,
    Proven,
    Blocked,
    Retired,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClaimBinding {
    pub class: ClaimClass,
    pub state: ClaimState,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExactRatio {
    pub numerator: u128,
    pub denominator: u128,
}

impl ExactRatio {
    pub fn new(numerator: u128, denominator: u128) -> Option<Self> {
        if denominator == 0 {
            return None;
        }
        let divisor = gcd(numerator, denominator);
        Some(Self {
            numerator: numerator / divisor,
            denominator: denominator / divisor,
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StatisticalSummary {
    pub valid_samples: u32,
    pub excluded_attempts: u32,
    pub minimum: u64,
    pub maximum: u64,
    pub median: ExactRatio,
    pub p95: u64,
    pub p99: u64,
    pub mean: ExactRatio,
    pub sample_variance: ExactRatio,
    pub median_absolute_deviation: ExactRatio,
    pub relative_mad_basis_points: u64,
    pub median_confidence_low: u64,
    pub median_confidence_high: u64,
    pub repeatable: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CounterReading {
    pub name: String,
    pub value: u64,
}

/// Non-comparison facts.  Changing any of these must change the telemetry and outer
/// bundle roots without changing the semantic root.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AttemptTelemetry {
    pub attempt_id: String,
    pub wall_clock_start_ns: u64,
    pub elapsed_ns: u64,
    pub process_id: u32,
    pub absolute_working_directory: String,
    pub counters: Vec<CounterReading>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BenchmarkTelemetry {
    pub schema_version: u16,
    pub attempts: Vec<AttemptTelemetry>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BundleRoots {
    pub host: Digest,
    pub workload: Digest,
    pub raw_attempts: Digest,
    pub statistics: Digest,
    pub report: Digest,
    pub semantic: Digest,
    pub telemetry: Digest,
    pub bundle: Digest,
}

/// Fully representable untrusted input.  Optional fields allow the validator to name
/// an incomplete bundle rather than accepting a "thin" result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BenchmarkBundleCandidate {
    pub schema_version: u16,
    pub run_id: String,
    pub benchmark_claim: ClaimBinding,
    pub repeatability_claim: ClaimBinding,
    pub host_profile: Option<HostProfile>,
    pub workload: Option<WorkloadManifest>,
    pub attempts_started: u32,
    pub attempts: Vec<AttemptRecord>,
    pub summary: Option<StatisticalSummary>,
    pub telemetry: Option<BenchmarkTelemetry>,
    pub claimed_roots: Option<BundleRoots>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RootComponent {
    Host,
    Workload,
    RawAttempts,
    Statistics,
    Report,
    Semantic,
    Telemetry,
    Bundle,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BenchmarkRefusal {
    UnsupportedSchema {
        object: &'static str,
        seen: u16,
        supported: u16,
    },
    MissingHostProfile,
    MissingWorkload,
    MissingSummary,
    MissingTelemetry,
    MissingRootChain,
    MalformedHostProfile {
        field: &'static str,
    },
    HostNotQualified {
        check: &'static str,
    },
    MalformedWorkload {
        field: &'static str,
    },
    AttemptsStartedMismatch {
        declared: u32,
        actual: usize,
    },
    TooManyAttempts {
        observed: usize,
        allowed: u32,
    },
    AttemptOrdinalMismatch {
        attempt_id: String,
        expected: u32,
        actual: u32,
    },
    DuplicateAttemptId {
        attempt_id: String,
    },
    HostProfileSubstitution {
        attempt_id: String,
    },
    WorkloadSubstitution {
        attempt_id: String,
    },
    CacheStateMismatch {
        attempt_id: String,
    },
    ProfilerContamination {
        attempt_id: String,
    },
    MalformedAttempt {
        attempt_id: String,
        field: &'static str,
    },
    SamplePlanUnsatisfied {
        valid: u32,
        required: u32,
    },
    SamplePlanOverrun {
        valid: u32,
        allowed: u32,
    },
    StatisticsOverflow,
    StaleSummary,
    ClaimAuthorityMismatch {
        class: ClaimClass,
        state: ClaimState,
    },
    TelemetryLinkMismatch {
        attempt_id: String,
    },
    TelemetryOutOfBounds {
        attempt_id: String,
        field: &'static str,
    },
    RootMismatch {
        component: RootComponent,
        expected: Digest,
        actual: Digest,
    },
}

impl BenchmarkRefusal {
    pub const fn finding_code(&self) -> &'static str {
        match self {
            Self::UnsupportedSchema { .. } => "FLN-BENCH-001",
            Self::MissingHostProfile => "FLN-BENCH-002",
            Self::MissingWorkload => "FLN-BENCH-003",
            Self::MissingSummary => "FLN-BENCH-004",
            Self::MissingTelemetry => "FLN-BENCH-005",
            Self::MissingRootChain => "FLN-BENCH-006",
            Self::MalformedHostProfile { .. } => "FLN-BENCH-007",
            Self::HostNotQualified { .. } => "FLN-BENCH-008",
            Self::MalformedWorkload { .. } => "FLN-BENCH-009",
            Self::AttemptsStartedMismatch { .. } => "FLN-BENCH-010",
            Self::TooManyAttempts { .. } => "FLN-BENCH-011",
            Self::AttemptOrdinalMismatch { .. } => "FLN-BENCH-012",
            Self::DuplicateAttemptId { .. } => "FLN-BENCH-013",
            Self::HostProfileSubstitution { .. } => "FLN-BENCH-014",
            Self::WorkloadSubstitution { .. } => "FLN-BENCH-015",
            Self::CacheStateMismatch { .. } => "FLN-BENCH-016",
            Self::ProfilerContamination { .. } => "FLN-BENCH-017",
            Self::MalformedAttempt { .. } => "FLN-BENCH-018",
            Self::SamplePlanUnsatisfied { .. } => "FLN-BENCH-019",
            Self::SamplePlanOverrun { .. } => "FLN-BENCH-020",
            Self::StatisticsOverflow => "FLN-BENCH-021",
            Self::StaleSummary => "FLN-BENCH-022",
            Self::ClaimAuthorityMismatch { .. } => "FLN-BENCH-023",
            Self::TelemetryLinkMismatch { .. } => "FLN-BENCH-024",
            Self::TelemetryOutOfBounds { .. } => "FLN-BENCH-025",
            Self::RootMismatch { .. } => "FLN-BENCH-026",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BundleValidationError {
    Decode(CanonError),
    Refused(BenchmarkRefusal),
}

/// Opaque publication authority.  There is no public constructor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValidatedBenchmarkBundle {
    candidate: BenchmarkBundleCandidate,
    roots: BundleRoots,
    report: String,
}

impl ValidatedBenchmarkBundle {
    pub const fn roots(&self) -> BundleRoots {
        self.roots
    }

    pub fn report(&self) -> &str {
        &self.report
    }

    pub fn candidate(&self) -> &BenchmarkBundleCandidate {
        &self.candidate
    }

    /// Canonical semantic NDJSON.  Operational telemetry has no field through which
    /// to enter this rendering or its root.
    pub fn semantic_ndjson(&self) -> String {
        let mut output = String::new();
        output.push_str(&format!(
            "{{\"schema\":\"fln.bench.bundle\",\"version\":1,\"run_id\":\"{}\",\
             \"claim_class\":\"benchmark\",\"claim_state\":\"OBSERVED\",\
             \"publication_authority\":\"validated\",\"final_state\":\"complete\",\
             \"cleanup\":\"not-applicable\",\"host_root\":\"{}\",\"workload_root\":\"{}\",\
             \"raw_attempts_root\":\"{}\",\"statistics_root\":\"{}\",\"report_root\":\"{}\",\
             \"semantic_root\":\"{}\"}}\n",
            json_escape(&self.candidate.run_id),
            self.roots.host,
            self.roots.workload,
            self.roots.raw_attempts,
            self.roots.statistics,
            self.roots.report,
            self.roots.semantic,
        ));
        if let Some(host) = &self.candidate.host_profile {
            output.push_str(&format!(
                "{{\"schema\":\"fln.bench.host-profile\",\"version\":1,\
                 \"run_id\":\"{}\",\"host_root\":\"{}\",\"cpu_sku\":\"{}\",\
                 \"architecture\":\"{}\"}}\n",
                json_escape(&self.candidate.run_id),
                self.roots.host,
                json_escape(captured_text(&host.cpu_sku)),
                json_escape(captured_text(&host.architecture)),
            ));
        }
        if let Some(workload) = &self.candidate.workload {
            let (stopping_rule, minimum_valid, maximum_valid, stopping_threshold) =
                match workload.sample_plan {
                    SamplePlan::FixedValidSamples { samples } => {
                        ("fixed-valid-samples", samples, samples, "null".to_string())
                    }
                    SamplePlan::RelativeMad {
                        min_valid,
                        max_valid,
                        threshold_basis_points,
                    } => (
                        "relative-mad",
                        min_valid,
                        max_valid,
                        threshold_basis_points.to_string(),
                    ),
                };
            output.push_str(&format!(
                "{{\"schema\":\"fln.bench.workload\",\"version\":1,\
                 \"run_id\":\"{}\",\"workload_id\":\"{}\",\"workload_root\":\"{}\",\
                 \"unit\":\"{}\",\"attempts_started\":{},\"warmup_iterations\":{},\
                 \"stopping_rule\":\"{}\",\"minimum_valid_samples\":{},\
                 \"maximum_valid_samples\":{},\"stopping_threshold_basis_points\":{},\
                 \"quantile_method\":\"nearest-rank-v1\",\
                 \"confidence_method\":\"distribution-free-median-95-v1\",\
                 \"outlier_policy\":\"{}\",\"variance_threshold_basis_points\":{},\
                 \"cache_filesystem\":\"{}\",\"cache_page\":\"{}\",\
                 \"cache_reference_artifacts\":\"{}\",\"cache_candidate_artifacts\":\"{}\",\
                 \"cache_build\":\"{}\",\"cache_imported_modules\":\"{}\",\
                 \"cache_daemon\":\"{}\",\"resource_max_attempts\":{},\
                 \"resource_max_measurement\":{},\"resource_max_elapsed_ns\":{}}}\n",
                json_escape(&self.candidate.run_id),
                json_escape(&workload.workload_id),
                self.roots.workload,
                unit_name(workload.unit),
                self.candidate.attempts_started,
                workload.warmup_iterations,
                stopping_rule,
                minimum_valid,
                maximum_valid,
                stopping_threshold,
                outlier_name(workload.outlier_policy),
                workload.variance_threshold_basis_points,
                cache_name(workload.cache_state.filesystem),
                cache_name(workload.cache_state.page_cache),
                cache_name(workload.cache_state.reference_artifacts),
                cache_name(workload.cache_state.candidate_artifacts),
                cache_name(workload.cache_state.build_cache),
                cache_name(workload.cache_state.imported_modules),
                cache_name(workload.cache_state.daemon),
                workload.resource_bounds.max_attempts,
                workload.resource_bounds.max_measurement,
                workload.resource_bounds.max_elapsed_ns_per_attempt,
            ));
            for attempt in &self.candidate.attempts {
                let details = attempt_details(&attempt.status);
                output.push_str(&format!(
                    "{{\"schema\":\"fln.bench.attempt\",\"version\":1,\
                     \"run_id\":\"{}\",\"workload_id\":\"{}\",\"attempt_id\":\"{}\",\
                     \"ordinal\":{},\"status\":\"{}\",\"valid\":{},\"unit\":\"{}\",\
                     \"measurement\":{},\"reason\":{},\"resource\":{},\"allowed\":{},\
                     \"observed\":{},\"exit_code\":{},\"valid_observed\":{},\
                     \"valid_required\":{},\"profiler\":\"{}\",\
                     \"cache_filesystem\":\"{}\",\"cache_page\":\"{}\",\
                     \"cache_reference_artifacts\":\"{}\",\
                     \"cache_candidate_artifacts\":\"{}\",\"cache_build\":\"{}\",\
                     \"cache_imported_modules\":\"{}\",\"cache_daemon\":\"{}\",\
                     \"host_root\":\"{}\",\"workload_root\":\"{}\"}}\n",
                    json_escape(&self.candidate.run_id),
                    json_escape(&workload.workload_id),
                    json_escape(&attempt.attempt_id),
                    attempt.ordinal,
                    status_name(&attempt.status),
                    matches!(&attempt.status, AttemptStatus::Valid { .. }),
                    unit_name(workload.unit),
                    details.measurement,
                    details.reason,
                    details.resource,
                    details.allowed,
                    details.observed,
                    details.exit_code,
                    details.valid_observed,
                    details.valid_required,
                    profiler_name(attempt.profiler),
                    cache_name(attempt.cache_state.filesystem),
                    cache_name(attempt.cache_state.page_cache),
                    cache_name(attempt.cache_state.reference_artifacts),
                    cache_name(attempt.cache_state.candidate_artifacts),
                    cache_name(attempt.cache_state.build_cache),
                    cache_name(attempt.cache_state.imported_modules),
                    cache_name(attempt.cache_state.daemon),
                    attempt.host_root,
                    attempt.workload_root,
                ));
            }
        }
        if let Some(summary) = &self.candidate.summary {
            output.push_str(&format!(
                "{{\"schema\":\"fln.bench.summary\",\"version\":1,\
                 \"run_id\":\"{}\",\"statistics_root\":\"{}\",\"valid_samples\":{},\
                 \"excluded_attempts\":{},\"median\":\"{}\",\"p95\":{},\"p99\":{},\
                 \"mean\":\"{}\",\"sample_variance\":\"{}\",\
                 \"median_absolute_deviation\":\"{}\",\"relative_mad_basis_points\":{},\
                 \"median_confidence_low\":{},\"median_confidence_high\":{},\
                 \"quantile_method\":\"nearest-rank-v1\",\
                 \"confidence_method\":\"distribution-free-median-95-v1\",\
                 \"repeatability_claim_class\":\"statistical\",\
                 \"repeatability_claim_state\":\"OBSERVED\",\"repeatable\":{}}}\n",
                json_escape(&self.candidate.run_id),
                self.roots.statistics,
                summary.valid_samples,
                summary.excluded_attempts,
                ratio_text(&summary.median),
                summary.p95,
                summary.p99,
                ratio_text(&summary.mean),
                ratio_text(&summary.sample_variance),
                ratio_text(&summary.median_absolute_deviation),
                summary.relative_mad_basis_points,
                summary.median_confidence_low,
                summary.median_confidence_high,
                summary.repeatable,
            ));
        }
        output
    }

    pub fn telemetry_ndjson(&self) -> String {
        let mut output = String::new();
        output.push_str(&format!(
            "{{\"schema\":\"fln.bench.telemetry-root\",\"version\":1,\
             \"run_id\":\"{}\",\"semantic_root\":\"{}\",\"telemetry_root\":\"{}\",\
             \"expected_bundle_root\":\"{}\",\"actual_bundle_root\":\"{}\",\
             \"publication_authority\":\"validated\",\"final_state\":\"complete\",\
             \"cleanup\":\"not-applicable\"}}\n",
            json_escape(&self.candidate.run_id),
            self.roots.semantic,
            self.roots.telemetry,
            self.roots.bundle,
            self.roots.bundle,
        ));
        if let Some(telemetry) = &self.candidate.telemetry {
            for record in &telemetry.attempts {
                output.push_str(&format!(
                    "{{\"schema\":\"fln.bench.telemetry\",\"version\":1,\
                     \"run_id\":\"{}\",\"attempt_id\":\"{}\",\"wall_clock_start_ns\":{},\
                     \"elapsed_ns\":{},\"process_id\":{},\"absolute_working_directory\":\"{}\",\
                     \"telemetry_root\":\"{}\",\"bundle_root\":\"{}\"}}\n",
                    json_escape(&self.candidate.run_id),
                    json_escape(&record.attempt_id),
                    record.wall_clock_start_ns,
                    record.elapsed_ns,
                    record.process_id,
                    json_escape(&record.absolute_working_directory),
                    self.roots.telemetry,
                    self.roots.bundle,
                ));
            }
        }
        output
    }
}

fn captured_text(fact: &Captured<String>) -> &str {
    match fact {
        Captured::Observed { value, .. } => value,
        Captured::Unavailable { reason, .. } => reason,
    }
}

fn json_escape(text: &str) -> String {
    let mut output = String::with_capacity(text.len());
    for character in text.chars() {
        match character {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            '\n' => output.push_str("\\n"),
            '\r' => output.push_str("\\r"),
            '\t' => output.push_str("\\t"),
            character if character.is_control() => {
                output.push_str(&format!("\\u{:04x}", u32::from(character)));
            }
            character => output.push(character),
        }
    }
    output
}

const fn unit_name(unit: MeasurementUnit) -> &'static str {
    match unit {
        MeasurementUnit::Nanoseconds => "nanoseconds",
        MeasurementUnit::Bytes => "bytes",
        MeasurementUnit::Operations => "operations",
    }
}

const fn status_name(status: &AttemptStatus) -> &'static str {
    match status {
        AttemptStatus::Valid { .. } => "valid",
        AttemptStatus::InvalidHost { .. } => "invalid-host",
        AttemptStatus::Cancelled { .. } => "cancelled",
        AttemptStatus::ResourceRefused { .. } => "resource-refused",
        AttemptStatus::TargetFailed { .. } => "target-failed",
        AttemptStatus::InfrastructureFault { .. } => "infrastructure-fault",
        AttemptStatus::InsufficientSample { .. } => "insufficient-sample",
    }
}

const fn cache_name(condition: CacheCondition) -> &'static str {
    match condition {
        CacheCondition::Cold => "cold",
        CacheCondition::Warm => "warm",
        CacheCondition::NotApplicable => "not-applicable",
    }
}

const fn outlier_name(policy: OutlierPolicy) -> &'static str {
    match policy {
        OutlierPolicy::RetainAllV1 => "retain-all-v1",
        OutlierPolicy::ReportTukeyOnlyV1 => "report-tukey-only-v1",
    }
}

const fn profiler_name(state: ProfilerState) -> &'static str {
    match state {
        ProfilerState::Disabled => "disabled",
        ProfilerState::Enabled => "enabled",
    }
}

const fn resource_name(resource: ResourceKind) -> &'static str {
    match resource {
        ResourceKind::Time => "time",
        ResourceKind::Memory => "memory",
        ResourceKind::Operations => "operations",
    }
}

struct AttemptJsonDetails {
    measurement: String,
    reason: String,
    resource: String,
    allowed: String,
    observed: String,
    exit_code: String,
    valid_observed: String,
    valid_required: String,
}

fn attempt_details(status: &AttemptStatus) -> AttemptJsonDetails {
    let mut details = AttemptJsonDetails {
        measurement: "null".to_string(),
        reason: "null".to_string(),
        resource: "null".to_string(),
        allowed: "null".to_string(),
        observed: "null".to_string(),
        exit_code: "null".to_string(),
        valid_observed: "null".to_string(),
        valid_required: "null".to_string(),
    };
    match status {
        AttemptStatus::Valid { measurement } => {
            details.measurement = measurement.to_string();
        }
        AttemptStatus::InvalidHost { reason } | AttemptStatus::Cancelled { reason } => {
            details.reason = format!("\"{}\"", json_escape(reason));
        }
        AttemptStatus::ResourceRefused {
            resource,
            allowed,
            observed,
        } => {
            details.resource = format!("\"{}\"", resource_name(*resource));
            details.allowed = allowed.to_string();
            details.observed = observed.to_string();
        }
        AttemptStatus::TargetFailed { exit_code } => {
            details.exit_code = exit_code.to_string();
        }
        AttemptStatus::InfrastructureFault { code } => {
            details.reason = format!("\"{}\"", json_escape(code));
        }
        AttemptStatus::InsufficientSample {
            valid_observed,
            valid_required,
        } => {
            details.valid_observed = valid_observed.to_string();
            details.valid_required = valid_required.to_string();
        }
    }
    details
}

fn text_fact(path: &Path, source: CaptureSource) -> Captured<String> {
    match fs::read_to_string(path) {
        Ok(text) if !text.trim().is_empty() => Captured::observed(text.trim().to_string(), source),
        Ok(_) => Captured::unavailable(source, format!("{} was empty", path.display())),
        Err(error) => Captured::unavailable(source, format!("{}: {error}", path.display())),
    }
}

fn proc_field(source: &str, key: &str) -> Option<String> {
    source.lines().find_map(|line| {
        let (name, value) = line.split_once(':')?;
        (name.trim() == key).then(|| value.trim().to_string())
    })
}

fn cpu_topology(cpuinfo: &str) -> Captured<u64> {
    let mut pairs = BTreeSet::new();
    let mut physical = None::<String>;
    let mut core = None::<String>;
    for line in cpuinfo.lines().chain(std::iter::once("")) {
        if line.trim().is_empty() {
            if let (Some(physical), Some(core)) = (physical.take(), core.take()) {
                pairs.insert((physical, core));
            }
            continue;
        }
        if let Some((name, value)) = line.split_once(':') {
            match name.trim() {
                "physical id" => physical = Some(value.trim().to_string()),
                "core id" => core = Some(value.trim().to_string()),
                _ => {}
            }
        }
    }
    if pairs.is_empty() {
        Captured::unavailable(
            CaptureSource::Procfs,
            "/proc/cpuinfo exposes no physical/core topology",
        )
    } else {
        Captured::observed(pairs.len() as u64, CaptureSource::Procfs)
    }
}

fn memory_bytes(meminfo: &str) -> Captured<u64> {
    let Some(kib) = proc_field(meminfo, "MemTotal") else {
        return Captured::unavailable(CaptureSource::Procfs, "MemTotal is absent");
    };
    let Some(number) = kib.split_whitespace().next() else {
        return Captured::unavailable(CaptureSource::Procfs, "MemTotal has no value");
    };
    match number
        .parse::<u64>()
        .ok()
        .and_then(|value| value.checked_mul(1024))
    {
        Some(bytes) => Captured::observed(bytes, CaptureSource::Procfs),
        None => Captured::unavailable(CaptureSource::Procfs, "MemTotal is malformed"),
    }
}

fn os_release() -> Captured<String> {
    match fs::read_to_string("/etc/os-release") {
        Ok(text) => text
            .lines()
            .find_map(|line| line.strip_prefix("PRETTY_NAME="))
            .map(|value| value.trim_matches('"').to_string())
            .map_or_else(
                || {
                    Captured::unavailable(
                        CaptureSource::OperatingSystem,
                        "/etc/os-release has no PRETTY_NAME",
                    )
                },
                |value| Captured::observed(value, CaptureSource::OperatingSystem),
            ),
        Err(error) => Captured::unavailable(
            CaptureSource::OperatingSystem,
            format!("/etc/os-release: {error}"),
        ),
    }
}

fn mount_facts() -> (Captured<String>, Captured<String>) {
    let source = match fs::read_to_string("/proc/self/mountinfo") {
        Ok(source) => source,
        Err(error) => {
            let reason = format!("/proc/self/mountinfo: {error}");
            return (
                Captured::unavailable(CaptureSource::Procfs, reason.clone()),
                Captured::unavailable(CaptureSource::Procfs, reason),
            );
        }
    };
    let cwd = match std::env::current_dir() {
        Ok(cwd) => cwd.to_string_lossy().into_owned(),
        Err(error) => {
            let reason = format!("current_dir: {error}");
            return (
                Captured::unavailable(CaptureSource::RuntimeProbe, reason.clone()),
                Captured::unavailable(CaptureSource::RuntimeProbe, reason),
            );
        }
    };
    let mut best: Option<(usize, String, String)> = None;
    for line in source.lines() {
        let Some((left, right)) = line.split_once(" - ") else {
            continue;
        };
        let left_fields: Vec<&str> = left.split_whitespace().collect();
        let right_fields: Vec<&str> = right.split_whitespace().collect();
        if left_fields.len() < 5 || right_fields.len() < 2 {
            continue;
        }
        let Some(mount) = left_fields.get(4).copied() else {
            continue;
        };
        let (Some(device), Some(filesystem)) = (right_fields.get(1), right_fields.first()) else {
            continue;
        };
        let is_better = match &best {
            Some((length, _, _)) => mount.len() > *length,
            None => true,
        };
        if cwd.starts_with(mount) && is_better {
            best = Some((
                mount.len(),
                (*device).to_string(),
                (*filesystem).to_string(),
            ));
        }
    }
    match best {
        Some((_, device, filesystem)) => (
            Captured::observed(device, CaptureSource::Procfs),
            Captured::observed(filesystem, CaptureSource::Procfs),
        ),
        None => (
            Captured::unavailable(CaptureSource::Procfs, "no mount covers current_dir"),
            Captured::unavailable(CaptureSource::Procfs, "no mount covers current_dir"),
        ),
    }
}

fn unavailable_thermal_sensor_facts(reason: String) -> (Captured<u64>, Captured<String>) {
    (
        Captured::unavailable(CaptureSource::Sysfs, reason.clone()),
        Captured::unavailable(CaptureSource::Sysfs, reason),
    )
}

fn thermal_sensor_facts() -> (Captured<u64>, Captured<String>) {
    let entries = match fs::read_dir("/sys/class/thermal") {
        Ok(entries) => entries,
        Err(error) => {
            return unavailable_thermal_sensor_facts(format!("/sys/class/thermal: {error}"));
        }
    };
    let mut count = 0_u64;
    for entry in entries {
        let entry = match entry {
            Ok(entry) => entry,
            Err(error) => {
                return unavailable_thermal_sensor_facts(format!(
                    "/sys/class/thermal entry: {error}"
                ));
            }
        };
        if entry
            .file_name()
            .to_string_lossy()
            .starts_with("thermal_zone")
        {
            let Some(next) = count.checked_add(1) else {
                return unavailable_thermal_sensor_facts(
                    "/sys/class/thermal contains more entries than u64 can count".to_string(),
                );
            };
            count = next;
        }
    }
    (
        Captured::observed(count, CaptureSource::Sysfs),
        Captured::observed(
            format!("{count} thermal zones exposed"),
            CaptureSource::Sysfs,
        ),
    )
}

fn clock_resolution_ns() -> Captured<u64> {
    let start = Instant::now();
    for _ in 0..1_000_000 {
        let elapsed = Instant::now().saturating_duration_since(start).as_nanos();
        if elapsed > 0 {
            return Captured::observed(
                u64::try_from(elapsed).unwrap_or(u64::MAX),
                CaptureSource::RuntimeProbe,
            );
        }
    }
    Captured::unavailable(
        CaptureSource::RuntimeProbe,
        "monotonic clock did not advance in one million probes",
    )
}

fn sorted_unique_strings(values: impl IntoIterator<Item = String>) -> Vec<String> {
    values
        .into_iter()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

impl HostProfile {
    /// Capture a real local profile without invoking an external program.
    pub fn capture_local(build: LocalBuildIdentity<'_>) -> Result<Self, HostCaptureError> {
        let cpuinfo = fs::read_to_string("/proc/cpuinfo").unwrap_or_default();
        let meminfo = fs::read_to_string("/proc/meminfo").unwrap_or_default();
        let logical = std::thread::available_parallelism()
            .map(|count| Captured::observed(count.get() as u64, CaptureSource::RuntimeProbe))
            .unwrap_or_else(|error| {
                Captured::unavailable(
                    CaptureSource::RuntimeProbe,
                    format!("available_parallelism: {error}"),
                )
            });
        let physical = cpu_topology(&cpuinfo);
        let smt_enabled = match (physical.observed_value(), logical.observed_value()) {
            (Some(physical), Some(logical)) => {
                Captured::observed(logical > physical, CaptureSource::RuntimeProbe)
            }
            _ => Captured::unavailable(
                CaptureSource::RuntimeProbe,
                "physical/logical topology incomplete",
            ),
        };
        let (storage_device, filesystem) = mount_facts();
        let governor = text_fact(
            Path::new("/sys/devices/system/cpu/cpu0/cpufreq/scaling_governor"),
            CaptureSource::Sysfs,
        );
        let stable_frequency = match governor.observed_value().map(String::as_str) {
            Some("performance" | "powersave") => Captured::observed(true, CaptureSource::Sysfs),
            Some(_) => Captured::observed(false, CaptureSource::Sysfs),
            None => {
                Captured::unavailable(CaptureSource::Sysfs, "frequency governor is unavailable")
            }
        };
        let (thermal_sensor_count, thermal_sensors) = thermal_sensor_facts();
        let virtualization = if cpuinfo.lines().any(|line| {
            line.starts_with("flags") && line.split_whitespace().any(|flag| flag == "hypervisor")
        }) {
            Captured::observed("hypervisor-detected".to_string(), CaptureSource::Procfs)
        } else {
            Captured::observed("no-hypervisor-flag".to_string(), CaptureSource::Procfs)
        };
        let mut counters = vec!["std::time::Instant".to_string()];
        for flag in ["constant_tsc", "nonstop_tsc", "rdtscp"] {
            if cpuinfo.split_whitespace().any(|word| word == flag) {
                counters.push(flag.to_string());
            }
        }

        let executable =
            std::env::current_exe().map_err(|error| HostCaptureError::CurrentExecutable {
                message: error.to_string(),
            })?;
        let executable_bytes =
            fs::read(&executable).map_err(|error| HostCaptureError::ReadExecutable {
                path: executable,
                message: error.to_string(),
            })?;
        let mut features = build
            .enabled_features
            .iter()
            .map(|feature| (*feature).to_string())
            .collect::<Vec<_>>();
        features.sort();
        features.dedup();

        Ok(Self {
            schema_version: BENCHMARK_EVIDENCE_VERSION,
            cpu_sku: proc_field(&cpuinfo, "model name")
                .or_else(|| proc_field(&cpuinfo, "Hardware"))
                .map_or_else(
                    || {
                        Captured::unavailable(
                            CaptureSource::Procfs,
                            "CPU model is absent from /proc/cpuinfo",
                        )
                    },
                    |value| Captured::observed(value, CaptureSource::Procfs),
                ),
            architecture: Captured::observed(
                std::env::consts::ARCH.to_string(),
                CaptureSource::BuildMetadata,
            ),
            physical_cores: physical,
            enabled_logical_cores: logical,
            smt_enabled,
            ram_bytes: memory_bytes(&meminfo),
            storage_device,
            filesystem,
            os_release: os_release(),
            kernel_release: text_fact(
                Path::new("/proc/sys/kernel/osrelease"),
                CaptureSource::Procfs,
            ),
            power_governor: governor,
            thermal_policy: Captured::observed(
                "kernel/default".to_string(),
                CaptureSource::OperatingSystem,
            ),
            thermal_sensor_count,
            thermal_sensors,
            virtualization,
            translation: Captured::observed(
                "native-target-architecture".to_string(),
                CaptureSource::BuildMetadata,
            ),
            toolchain_hash: hash(Domain::OperationalMeta, build.toolchain_manifest),
            binary_hash: hash(Domain::OperationalMeta, &executable_bytes),
            target_triple: Captured::observed(
                build.target_triple.to_string(),
                CaptureSource::BuildMetadata,
            ),
            build_profile: Captured::observed(
                build.build_profile.to_string(),
                CaptureSource::BuildMetadata,
            ),
            enabled_features: features,
            monotonic_clock_resolution_ns: clock_resolution_ns(),
            counter_capabilities: sorted_unique_strings(counters),
            isolation: HostIsolation {
                exclusive_cores: Captured::unavailable(
                    CaptureSource::OperatingSystem,
                    "exclusive CPU allocation was not attested",
                ),
                stable_frequency,
                thermal_stable: Captured::unavailable(
                    CaptureSource::Sysfs,
                    "thermal stability needs a lane-specific pre/post probe",
                ),
            },
        })
    }

    pub fn root(&self) -> Digest {
        hash(Domain::OperationalMeta, &host_profile_bytes(self))
    }
}

impl WorkloadManifest {
    pub fn root(&self) -> Digest {
        hash(Domain::OperationalMeta, &workload_bytes(self))
    }
}

fn decode_problem(what: &'static str) -> CanonError {
    CanonError { at: 0, what }
}

fn read_supported_evidence_version(
    reader: &mut CanonReader<'_>,
    unsupported: &'static str,
) -> Result<u16, CanonError> {
    let version = reader.u16()?;
    if version != BENCHMARK_EVIDENCE_VERSION {
        return Err(decode_problem(unsupported));
    }
    Ok(version)
}

fn write_source(writer: &mut CanonWriter, source: CaptureSource) {
    writer.u8(match source {
        CaptureSource::Procfs => 0,
        CaptureSource::Sysfs => 1,
        CaptureSource::OperatingSystem => 2,
        CaptureSource::RuntimeProbe => 3,
        CaptureSource::BuildMetadata => 4,
    });
}

fn read_source(reader: &mut CanonReader<'_>) -> Result<CaptureSource, CanonError> {
    match reader.u8()? {
        0 => Ok(CaptureSource::Procfs),
        1 => Ok(CaptureSource::Sysfs),
        2 => Ok(CaptureSource::OperatingSystem),
        3 => Ok(CaptureSource::RuntimeProbe),
        4 => Ok(CaptureSource::BuildMetadata),
        _ => Err(decode_problem("unknown benchmark capture source")),
    }
}

fn write_text_fact(writer: &mut CanonWriter, fact: &Captured<String>) {
    match fact {
        Captured::Observed { value, source } => {
            writer.u8(0);
            write_source(writer, *source);
            writer.str(value);
        }
        Captured::Unavailable { source, reason } => {
            writer.u8(1);
            write_source(writer, *source);
            writer.str(reason);
        }
    }
}

fn read_text_fact(reader: &mut CanonReader<'_>) -> Result<Captured<String>, CanonError> {
    let tag = reader.u8()?;
    let source = read_source(reader)?;
    let value = reader.str()?.to_string();
    if value.len() > MAX_TEXT_BYTES {
        return Err(decode_problem("benchmark text exceeds limit"));
    }
    match tag {
        0 => Ok(Captured::observed(value, source)),
        1 => Ok(Captured::unavailable(source, value)),
        _ => Err(decode_problem("unknown captured-text tag")),
    }
}

fn write_u64_fact(writer: &mut CanonWriter, fact: &Captured<u64>) {
    match fact {
        Captured::Observed { value, source } => {
            writer.u8(0);
            write_source(writer, *source);
            writer.u64(*value);
        }
        Captured::Unavailable { source, reason } => {
            writer.u8(1);
            write_source(writer, *source);
            writer.str(reason);
        }
    }
}

fn read_u64_fact(reader: &mut CanonReader<'_>) -> Result<Captured<u64>, CanonError> {
    let tag = reader.u8()?;
    let source = read_source(reader)?;
    match tag {
        0 => Ok(Captured::observed(reader.u64()?, source)),
        1 => {
            let reason = reader.str()?.to_string();
            if reason.len() > MAX_TEXT_BYTES {
                return Err(decode_problem("benchmark text exceeds limit"));
            }
            Ok(Captured::unavailable(source, reason))
        }
        _ => Err(decode_problem("unknown captured-u64 tag")),
    }
}

fn write_bool_fact(writer: &mut CanonWriter, fact: &Captured<bool>) {
    match fact {
        Captured::Observed { value, source } => {
            writer.u8(0);
            write_source(writer, *source);
            writer.bool(*value);
        }
        Captured::Unavailable { source, reason } => {
            writer.u8(1);
            write_source(writer, *source);
            writer.str(reason);
        }
    }
}

fn read_bool_fact(reader: &mut CanonReader<'_>) -> Result<Captured<bool>, CanonError> {
    let tag = reader.u8()?;
    let source = read_source(reader)?;
    match tag {
        0 => Ok(Captured::observed(reader.bool()?, source)),
        1 => {
            let reason = reader.str()?.to_string();
            if reason.len() > MAX_TEXT_BYTES {
                return Err(decode_problem("benchmark text exceeds limit"));
            }
            Ok(Captured::unavailable(source, reason))
        }
        _ => Err(decode_problem("unknown captured-bool tag")),
    }
}

fn write_digest(writer: &mut CanonWriter, digest: Digest) {
    writer.bytes(&digest.0);
}

fn read_digest(reader: &mut CanonReader<'_>) -> Result<Digest, CanonError> {
    let bytes = reader.bytes()?;
    let array: [u8; 32] = bytes
        .try_into()
        .map_err(|_| decode_problem("benchmark digest is not 32 bytes"))?;
    Ok(Digest(array))
}

fn write_strings(writer: &mut CanonWriter, values: &[String]) {
    writer.u64(values.len() as u64);
    for value in values {
        writer.str(value);
    }
}

fn read_strings(reader: &mut CanonReader<'_>, limit: usize) -> Result<Vec<String>, CanonError> {
    let count = usize::try_from(reader.u64()?)
        .map_err(|_| decode_problem("benchmark collection exceeds address space"))?;
    if count > limit {
        return Err(decode_problem("benchmark collection exceeds limit"));
    }
    let mut values = Vec::new();
    for _ in 0..count {
        let value = reader.str()?.to_string();
        if value.len() > MAX_TEXT_BYTES {
            return Err(decode_problem("benchmark text exceeds limit"));
        }
        values.push(value);
    }
    Ok(values)
}

fn write_host_body(writer: &mut CanonWriter, profile: &HostProfile) {
    writer.u16(profile.schema_version);
    write_text_fact(writer, &profile.cpu_sku);
    write_text_fact(writer, &profile.architecture);
    write_u64_fact(writer, &profile.physical_cores);
    write_u64_fact(writer, &profile.enabled_logical_cores);
    write_bool_fact(writer, &profile.smt_enabled);
    write_u64_fact(writer, &profile.ram_bytes);
    write_text_fact(writer, &profile.storage_device);
    write_text_fact(writer, &profile.filesystem);
    write_text_fact(writer, &profile.os_release);
    write_text_fact(writer, &profile.kernel_release);
    write_text_fact(writer, &profile.power_governor);
    write_text_fact(writer, &profile.thermal_policy);
    write_u64_fact(writer, &profile.thermal_sensor_count);
    write_text_fact(writer, &profile.thermal_sensors);
    write_text_fact(writer, &profile.virtualization);
    write_text_fact(writer, &profile.translation);
    write_digest(writer, profile.toolchain_hash);
    write_digest(writer, profile.binary_hash);
    write_text_fact(writer, &profile.target_triple);
    write_text_fact(writer, &profile.build_profile);
    write_strings(writer, &profile.enabled_features);
    write_u64_fact(writer, &profile.monotonic_clock_resolution_ns);
    write_strings(writer, &profile.counter_capabilities);
    write_bool_fact(writer, &profile.isolation.exclusive_cores);
    write_bool_fact(writer, &profile.isolation.stable_frequency);
    write_bool_fact(writer, &profile.isolation.thermal_stable);
}

fn read_host_body(reader: &mut CanonReader<'_>) -> Result<HostProfile, CanonError> {
    Ok(HostProfile {
        schema_version: read_supported_evidence_version(
            reader,
            "unsupported benchmark host-profile version",
        )?,
        cpu_sku: read_text_fact(reader)?,
        architecture: read_text_fact(reader)?,
        physical_cores: read_u64_fact(reader)?,
        enabled_logical_cores: read_u64_fact(reader)?,
        smt_enabled: read_bool_fact(reader)?,
        ram_bytes: read_u64_fact(reader)?,
        storage_device: read_text_fact(reader)?,
        filesystem: read_text_fact(reader)?,
        os_release: read_text_fact(reader)?,
        kernel_release: read_text_fact(reader)?,
        power_governor: read_text_fact(reader)?,
        thermal_policy: read_text_fact(reader)?,
        thermal_sensor_count: read_u64_fact(reader)?,
        thermal_sensors: read_text_fact(reader)?,
        virtualization: read_text_fact(reader)?,
        translation: read_text_fact(reader)?,
        toolchain_hash: read_digest(reader)?,
        binary_hash: read_digest(reader)?,
        target_triple: read_text_fact(reader)?,
        build_profile: read_text_fact(reader)?,
        enabled_features: read_strings(reader, MAX_FEATURES)?,
        monotonic_clock_resolution_ns: read_u64_fact(reader)?,
        counter_capabilities: read_strings(reader, MAX_FEATURES)?,
        isolation: HostIsolation {
            exclusive_cores: read_bool_fact(reader)?,
            stable_frequency: read_bool_fact(reader)?,
            thermal_stable: read_bool_fact(reader)?,
        },
    })
}

fn host_profile_bytes(profile: &HostProfile) -> Vec<u8> {
    let mut writer = CanonWriter::new();
    writer.schema(BENCHMARK_HOST_PROFILE_SCHEMA);
    write_host_body(&mut writer, profile);
    writer.into_bytes()
}

fn write_cache_condition(writer: &mut CanonWriter, condition: CacheCondition) {
    writer.u8(match condition {
        CacheCondition::Cold => 0,
        CacheCondition::Warm => 1,
        CacheCondition::NotApplicable => 2,
    });
}

fn read_cache_condition(reader: &mut CanonReader<'_>) -> Result<CacheCondition, CanonError> {
    match reader.u8()? {
        0 => Ok(CacheCondition::Cold),
        1 => Ok(CacheCondition::Warm),
        2 => Ok(CacheCondition::NotApplicable),
        _ => Err(decode_problem("unknown benchmark cache condition")),
    }
}

fn write_cache_state(writer: &mut CanonWriter, state: CacheState) {
    write_cache_condition(writer, state.filesystem);
    write_cache_condition(writer, state.page_cache);
    write_cache_condition(writer, state.reference_artifacts);
    write_cache_condition(writer, state.candidate_artifacts);
    write_cache_condition(writer, state.build_cache);
    write_cache_condition(writer, state.imported_modules);
    write_cache_condition(writer, state.daemon);
}

fn read_cache_state(reader: &mut CanonReader<'_>) -> Result<CacheState, CanonError> {
    Ok(CacheState {
        filesystem: read_cache_condition(reader)?,
        page_cache: read_cache_condition(reader)?,
        reference_artifacts: read_cache_condition(reader)?,
        candidate_artifacts: read_cache_condition(reader)?,
        build_cache: read_cache_condition(reader)?,
        imported_modules: read_cache_condition(reader)?,
        daemon: read_cache_condition(reader)?,
    })
}

fn write_sample_plan(writer: &mut CanonWriter, plan: SamplePlan) {
    match plan {
        SamplePlan::FixedValidSamples { samples } => {
            writer.u8(0);
            writer.u32(samples);
        }
        SamplePlan::RelativeMad {
            min_valid,
            max_valid,
            threshold_basis_points,
        } => {
            writer.u8(1);
            writer.u32(min_valid);
            writer.u32(max_valid);
            writer.u32(threshold_basis_points);
        }
    }
}

fn read_sample_plan(reader: &mut CanonReader<'_>) -> Result<SamplePlan, CanonError> {
    match reader.u8()? {
        0 => Ok(SamplePlan::FixedValidSamples {
            samples: reader.u32()?,
        }),
        1 => Ok(SamplePlan::RelativeMad {
            min_valid: reader.u32()?,
            max_valid: reader.u32()?,
            threshold_basis_points: reader.u32()?,
        }),
        _ => Err(decode_problem("unknown benchmark sample-plan tag")),
    }
}

fn write_host_policy(writer: &mut CanonWriter, policy: HostQualificationPolicy) {
    writer.bool(policy.require_physical_topology);
    writer.bool(policy.require_power_governor);
    writer.bool(policy.require_thermal_sensors);
    writer.bool(policy.require_exclusive_cores);
    writer.bool(policy.require_stable_frequency);
    writer.bool(policy.require_thermal_stability);
    writer.bool(policy.allow_virtualization);
    writer.bool(policy.allow_translation);
    writer.bool(policy.allow_profiler);
}

fn read_host_policy(reader: &mut CanonReader<'_>) -> Result<HostQualificationPolicy, CanonError> {
    Ok(HostQualificationPolicy {
        require_physical_topology: reader.bool()?,
        require_power_governor: reader.bool()?,
        require_thermal_sensors: reader.bool()?,
        require_exclusive_cores: reader.bool()?,
        require_stable_frequency: reader.bool()?,
        require_thermal_stability: reader.bool()?,
        allow_virtualization: reader.bool()?,
        allow_translation: reader.bool()?,
        allow_profiler: reader.bool()?,
    })
}

fn write_workload_body(writer: &mut CanonWriter, workload: &WorkloadManifest) {
    writer.u16(workload.schema_version);
    writer.str(&workload.workload_id);
    // The measured operation is SEMANTIC: it must move the workload root, so a
    // module import cannot share an identity with a kernel recheck.
    writer.u8(workload.workload_kind.tag());
    // Oracle-side tool identities are SEMANTIC for the same reason: swapping the
    // solver that produced the oracle's side of a comparison must move the
    // workload root, or "CaDiCaL identity loss" is undetectable.
    writer.u32(workload.oracle_tools.len() as u32);
    for tool in &workload.oracle_tools {
        writer.str(&tool.name);
        write_digest(writer, tool.binary_hash);
    }
    write_digest(writer, workload.corpus_root);
    write_digest(writer, workload.input_order_root);
    writer.u32(workload.warmup_iterations);
    write_sample_plan(writer, workload.sample_plan);
    writer.u8(match workload.quantile_algorithm {
        QuantileAlgorithm::NearestRankV1 => 0,
    });
    writer.u8(match workload.confidence_algorithm {
        ConfidenceAlgorithm::DistributionFreeMedian95V1 => 0,
    });
    writer.u8(match workload.outlier_policy {
        OutlierPolicy::RetainAllV1 => 0,
        OutlierPolicy::ReportTukeyOnlyV1 => 1,
    });
    writer.u32(workload.variance_threshold_basis_points);
    write_cache_state(writer, workload.cache_state);
    writer.u8(match workload.unit {
        MeasurementUnit::Nanoseconds => 0,
        MeasurementUnit::Bytes => 1,
        MeasurementUnit::Operations => 2,
    });
    write_host_policy(writer, workload.host_policy);
    writer.u32(workload.resource_bounds.max_attempts);
    writer.u64(workload.resource_bounds.max_measurement);
    writer.u64(workload.resource_bounds.max_elapsed_ns_per_attempt);
}

fn read_workload_body(reader: &mut CanonReader<'_>) -> Result<WorkloadManifest, CanonError> {
    let schema_version =
        read_supported_evidence_version(reader, "unsupported benchmark workload version")?;
    let workload_id = reader.str()?.to_string();
    if workload_id.len() > MAX_TEXT_BYTES {
        return Err(decode_problem("benchmark workload id exceeds limit"));
    }
    let workload_kind = WorkloadKind::from_tag(reader.u8()?)
        .ok_or_else(|| decode_problem("unknown benchmark workload kind"))?;
    let oracle_tool_count = reader.u32()?;
    if oracle_tool_count as usize > MAX_FEATURES {
        return Err(decode_problem("benchmark oracle tool count exceeds limit"));
    }
    let mut oracle_tools = Vec::with_capacity(oracle_tool_count as usize);
    for _ in 0..oracle_tool_count {
        let name = reader.str()?.to_string();
        if name.is_empty() || name.len() > MAX_TEXT_BYTES {
            return Err(decode_problem(
                "benchmark oracle tool name is out of bounds",
            ));
        }
        oracle_tools.push(OracleToolIdentity {
            name,
            binary_hash: read_digest(reader)?,
        });
    }
    let corpus_root = read_digest(reader)?;
    let input_order_root = read_digest(reader)?;
    let warmup_iterations = reader.u32()?;
    let sample_plan = read_sample_plan(reader)?;
    let quantile_algorithm = match reader.u8()? {
        0 => QuantileAlgorithm::NearestRankV1,
        _ => return Err(decode_problem("unknown benchmark quantile algorithm")),
    };
    let confidence_algorithm = match reader.u8()? {
        0 => ConfidenceAlgorithm::DistributionFreeMedian95V1,
        _ => return Err(decode_problem("unknown benchmark confidence algorithm")),
    };
    let outlier_policy = match reader.u8()? {
        0 => OutlierPolicy::RetainAllV1,
        1 => OutlierPolicy::ReportTukeyOnlyV1,
        _ => return Err(decode_problem("unknown benchmark outlier policy")),
    };
    let variance_threshold_basis_points = reader.u32()?;
    let cache_state = read_cache_state(reader)?;
    let unit = match reader.u8()? {
        0 => MeasurementUnit::Nanoseconds,
        1 => MeasurementUnit::Bytes,
        2 => MeasurementUnit::Operations,
        _ => return Err(decode_problem("unknown benchmark measurement unit")),
    };
    let host_policy = read_host_policy(reader)?;
    Ok(WorkloadManifest {
        schema_version,
        workload_id,
        workload_kind,
        oracle_tools,
        corpus_root,
        input_order_root,
        warmup_iterations,
        sample_plan,
        quantile_algorithm,
        confidence_algorithm,
        outlier_policy,
        variance_threshold_basis_points,
        cache_state,
        unit,
        host_policy,
        resource_bounds: ResourceBounds {
            max_attempts: reader.u32()?,
            max_measurement: reader.u64()?,
            max_elapsed_ns_per_attempt: reader.u64()?,
        },
    })
}

fn workload_bytes(workload: &WorkloadManifest) -> Vec<u8> {
    let mut writer = CanonWriter::new();
    writer.schema(BENCHMARK_WORKLOAD_SCHEMA);
    write_workload_body(&mut writer, workload);
    writer.into_bytes()
}

fn write_attempt_status(writer: &mut CanonWriter, status: &AttemptStatus) {
    match status {
        AttemptStatus::Valid { measurement } => {
            writer.u8(0);
            writer.u64(*measurement);
        }
        AttemptStatus::InvalidHost { reason } => {
            writer.u8(1);
            writer.str(reason);
        }
        AttemptStatus::Cancelled { reason } => {
            writer.u8(2);
            writer.str(reason);
        }
        AttemptStatus::ResourceRefused {
            resource,
            allowed,
            observed,
        } => {
            writer.u8(3);
            writer.u8(match resource {
                ResourceKind::Time => 0,
                ResourceKind::Memory => 1,
                ResourceKind::Operations => 2,
            });
            writer.u64(*allowed);
            writer.u64(*observed);
        }
        AttemptStatus::TargetFailed { exit_code } => {
            writer.u8(4);
            writer.i64(i64::from(*exit_code));
        }
        AttemptStatus::InfrastructureFault { code } => {
            writer.u8(5);
            writer.str(code);
        }
        AttemptStatus::InsufficientSample {
            valid_observed,
            valid_required,
        } => {
            writer.u8(6);
            writer.u32(*valid_observed);
            writer.u32(*valid_required);
        }
    }
}

fn read_limited_text(reader: &mut CanonReader<'_>) -> Result<String, CanonError> {
    let text = reader.str()?.to_string();
    if text.is_empty() || text.len() > MAX_TEXT_BYTES {
        return Err(decode_problem("benchmark text is empty or exceeds limit"));
    }
    Ok(text)
}

fn read_attempt_status(reader: &mut CanonReader<'_>) -> Result<AttemptStatus, CanonError> {
    match reader.u8()? {
        0 => Ok(AttemptStatus::Valid {
            measurement: reader.u64()?,
        }),
        1 => Ok(AttemptStatus::InvalidHost {
            reason: read_limited_text(reader)?,
        }),
        2 => Ok(AttemptStatus::Cancelled {
            reason: read_limited_text(reader)?,
        }),
        3 => {
            let resource = match reader.u8()? {
                0 => ResourceKind::Time,
                1 => ResourceKind::Memory,
                2 => ResourceKind::Operations,
                _ => return Err(decode_problem("unknown benchmark resource kind")),
            };
            Ok(AttemptStatus::ResourceRefused {
                resource,
                allowed: reader.u64()?,
                observed: reader.u64()?,
            })
        }
        4 => {
            let value = reader.i64()?;
            Ok(AttemptStatus::TargetFailed {
                exit_code: i32::try_from(value)
                    .map_err(|_| decode_problem("benchmark exit code exceeds i32"))?,
            })
        }
        5 => Ok(AttemptStatus::InfrastructureFault {
            code: read_limited_text(reader)?,
        }),
        6 => Ok(AttemptStatus::InsufficientSample {
            valid_observed: reader.u32()?,
            valid_required: reader.u32()?,
        }),
        _ => Err(decode_problem("unknown benchmark attempt status")),
    }
}

fn write_attempt_body(writer: &mut CanonWriter, attempt: &AttemptRecord) {
    writer.str(&attempt.attempt_id);
    writer.u32(attempt.ordinal);
    write_digest(writer, attempt.host_root);
    write_digest(writer, attempt.workload_root);
    write_cache_state(writer, attempt.cache_state);
    writer.u8(match attempt.profiler {
        ProfilerState::Disabled => 0,
        ProfilerState::Enabled => 1,
    });
    write_attempt_status(writer, &attempt.status);
}

fn read_attempt_body(reader: &mut CanonReader<'_>) -> Result<AttemptRecord, CanonError> {
    let attempt_id = read_limited_text(reader)?;
    let ordinal = reader.u32()?;
    let host_root = read_digest(reader)?;
    let workload_root = read_digest(reader)?;
    let cache_state = read_cache_state(reader)?;
    let profiler = match reader.u8()? {
        0 => ProfilerState::Disabled,
        1 => ProfilerState::Enabled,
        _ => return Err(decode_problem("unknown profiler state")),
    };
    Ok(AttemptRecord {
        attempt_id,
        ordinal,
        host_root,
        workload_root,
        cache_state,
        profiler,
        status: read_attempt_status(reader)?,
    })
}

fn attempts_bytes(attempts_started: u32, attempts: &[AttemptRecord]) -> Vec<u8> {
    let mut writer = CanonWriter::new();
    writer.schema(BENCHMARK_ATTEMPTS_SCHEMA);
    writer.u32(attempts_started);
    writer.u64(attempts.len() as u64);
    for attempt in attempts {
        write_attempt_body(&mut writer, attempt);
    }
    writer.into_bytes()
}

fn read_attempts_body(reader: &mut CanonReader<'_>) -> Result<(), CanonError> {
    let _attempts_started = reader.u32()?;
    let count = usize::try_from(reader.u64()?)
        .map_err(|_| decode_problem("attempt count exceeds address space"))?;
    if count > MAX_ATTEMPTS as usize {
        return Err(decode_problem("attempt count exceeds limit"));
    }
    for _ in 0..count {
        let _attempt = read_attempt_body(reader)?;
    }
    Ok(())
}

fn write_u128(writer: &mut CanonWriter, value: u128) {
    writer.bytes(&value.to_le_bytes());
}

fn read_u128(reader: &mut CanonReader<'_>) -> Result<u128, CanonError> {
    let bytes: [u8; 16] = reader
        .bytes()?
        .try_into()
        .map_err(|_| decode_problem("benchmark u128 is not 16 bytes"))?;
    Ok(u128::from_le_bytes(bytes))
}

fn write_ratio(writer: &mut CanonWriter, ratio: &ExactRatio) {
    write_u128(writer, ratio.numerator);
    write_u128(writer, ratio.denominator);
}

fn read_ratio(reader: &mut CanonReader<'_>) -> Result<ExactRatio, CanonError> {
    Ok(ExactRatio {
        numerator: read_u128(reader)?,
        denominator: read_u128(reader)?,
    })
}

fn write_summary_body(writer: &mut CanonWriter, summary: &StatisticalSummary) {
    writer.u32(summary.valid_samples);
    writer.u32(summary.excluded_attempts);
    writer.u64(summary.minimum);
    writer.u64(summary.maximum);
    write_ratio(writer, &summary.median);
    writer.u64(summary.p95);
    writer.u64(summary.p99);
    write_ratio(writer, &summary.mean);
    write_ratio(writer, &summary.sample_variance);
    write_ratio(writer, &summary.median_absolute_deviation);
    writer.u64(summary.relative_mad_basis_points);
    writer.u64(summary.median_confidence_low);
    writer.u64(summary.median_confidence_high);
    writer.bool(summary.repeatable);
}

fn read_summary_body(reader: &mut CanonReader<'_>) -> Result<StatisticalSummary, CanonError> {
    Ok(StatisticalSummary {
        valid_samples: reader.u32()?,
        excluded_attempts: reader.u32()?,
        minimum: reader.u64()?,
        maximum: reader.u64()?,
        median: read_ratio(reader)?,
        p95: reader.u64()?,
        p99: reader.u64()?,
        mean: read_ratio(reader)?,
        sample_variance: read_ratio(reader)?,
        median_absolute_deviation: read_ratio(reader)?,
        relative_mad_basis_points: reader.u64()?,
        median_confidence_low: reader.u64()?,
        median_confidence_high: reader.u64()?,
        repeatable: reader.bool()?,
    })
}

fn summary_bytes(summary: &StatisticalSummary) -> Vec<u8> {
    let mut writer = CanonWriter::new();
    writer.schema(BENCHMARK_SUMMARY_SCHEMA);
    write_summary_body(&mut writer, summary);
    writer.into_bytes()
}

fn write_telemetry_body(writer: &mut CanonWriter, telemetry: &BenchmarkTelemetry) {
    writer.u16(telemetry.schema_version);
    writer.u64(telemetry.attempts.len() as u64);
    for attempt in &telemetry.attempts {
        writer.str(&attempt.attempt_id);
        writer.u64(attempt.wall_clock_start_ns);
        writer.u64(attempt.elapsed_ns);
        writer.u32(attempt.process_id);
        writer.str(&attempt.absolute_working_directory);
        writer.u64(attempt.counters.len() as u64);
        for counter in &attempt.counters {
            writer.str(&counter.name);
            writer.u64(counter.value);
        }
    }
}

fn read_telemetry_body(reader: &mut CanonReader<'_>) -> Result<BenchmarkTelemetry, CanonError> {
    let schema_version =
        read_supported_evidence_version(reader, "unsupported benchmark telemetry version")?;
    let count = usize::try_from(reader.u64()?)
        .map_err(|_| decode_problem("telemetry count exceeds address space"))?;
    if count > MAX_ATTEMPTS as usize {
        return Err(decode_problem("telemetry count exceeds limit"));
    }
    let mut attempts = Vec::new();
    for _ in 0..count {
        let attempt_id = read_limited_text(reader)?;
        let wall_clock_start_ns = reader.u64()?;
        let elapsed_ns = reader.u64()?;
        let process_id = reader.u32()?;
        let absolute_working_directory = read_limited_text(reader)?;
        let counter_count = usize::try_from(reader.u64()?)
            .map_err(|_| decode_problem("counter count exceeds address space"))?;
        if counter_count > MAX_COUNTERS_PER_ATTEMPT {
            return Err(decode_problem("counter count exceeds limit"));
        }
        let mut counters = Vec::new();
        for _ in 0..counter_count {
            counters.push(CounterReading {
                name: read_limited_text(reader)?,
                value: reader.u64()?,
            });
        }
        attempts.push(AttemptTelemetry {
            attempt_id,
            wall_clock_start_ns,
            elapsed_ns,
            process_id,
            absolute_working_directory,
            counters,
        });
    }
    Ok(BenchmarkTelemetry {
        schema_version,
        attempts,
    })
}

fn telemetry_bytes(telemetry: &BenchmarkTelemetry) -> Vec<u8> {
    let mut writer = CanonWriter::new();
    writer.schema(BENCHMARK_TELEMETRY_SCHEMA);
    write_telemetry_body(&mut writer, telemetry);
    writer.into_bytes()
}

fn write_claim(writer: &mut CanonWriter, claim: ClaimBinding) {
    writer.u8(match claim.class {
        ClaimClass::Benchmark => 0,
        ClaimClass::Statistical => 1,
        ClaimClass::Slo => 2,
    });
    writer.u8(match claim.state {
        ClaimState::Observed => 0,
        ClaimState::Targeted => 1,
        ClaimState::Hypothesis => 2,
        ClaimState::Proven => 3,
        ClaimState::Blocked => 4,
        ClaimState::Retired => 5,
    });
}

fn read_claim(reader: &mut CanonReader<'_>) -> Result<ClaimBinding, CanonError> {
    let class = match reader.u8()? {
        0 => ClaimClass::Benchmark,
        1 => ClaimClass::Statistical,
        2 => ClaimClass::Slo,
        _ => return Err(decode_problem("unknown benchmark claim class")),
    };
    let state = match reader.u8()? {
        0 => ClaimState::Observed,
        1 => ClaimState::Targeted,
        2 => ClaimState::Hypothesis,
        3 => ClaimState::Proven,
        4 => ClaimState::Blocked,
        5 => ClaimState::Retired,
        _ => return Err(decode_problem("unknown benchmark claim state")),
    };
    Ok(ClaimBinding { class, state })
}

fn write_roots(writer: &mut CanonWriter, roots: BundleRoots) {
    for root in [
        roots.host,
        roots.workload,
        roots.raw_attempts,
        roots.statistics,
        roots.report,
        roots.semantic,
        roots.telemetry,
        roots.bundle,
    ] {
        write_digest(writer, root);
    }
}

fn read_roots(reader: &mut CanonReader<'_>) -> Result<BundleRoots, CanonError> {
    Ok(BundleRoots {
        host: read_digest(reader)?,
        workload: read_digest(reader)?,
        raw_attempts: read_digest(reader)?,
        statistics: read_digest(reader)?,
        report: read_digest(reader)?,
        semantic: read_digest(reader)?,
        telemetry: read_digest(reader)?,
        bundle: read_digest(reader)?,
    })
}

impl Canonical for BenchmarkBundleCandidate {
    const SCHEMA: SchemaId = BENCHMARK_BUNDLE_SCHEMA;

    fn write_body(&self, writer: &mut CanonWriter) {
        writer.u16(self.schema_version);
        writer.str(&self.run_id);
        write_claim(writer, self.benchmark_claim);
        write_claim(writer, self.repeatability_claim);
        match &self.host_profile {
            Some(profile) => {
                writer.u8(1);
                write_host_body(writer, profile);
            }
            None => writer.u8(0),
        }
        match &self.workload {
            Some(workload) => {
                writer.u8(1);
                write_workload_body(writer, workload);
            }
            None => writer.u8(0),
        }
        writer.u32(self.attempts_started);
        writer.u64(self.attempts.len() as u64);
        for attempt in &self.attempts {
            write_attempt_body(writer, attempt);
        }
        match &self.summary {
            Some(summary) => {
                writer.u8(1);
                write_summary_body(writer, summary);
            }
            None => writer.u8(0),
        }
        match &self.telemetry {
            Some(telemetry) => {
                writer.u8(1);
                write_telemetry_body(writer, telemetry);
            }
            None => writer.u8(0),
        }
        match self.claimed_roots {
            Some(roots) => {
                writer.u8(1);
                write_roots(writer, roots);
            }
            None => writer.u8(0),
        }
    }

    fn read_body(reader: &mut CanonReader<'_>) -> Result<Self, CanonError> {
        let schema_version =
            read_supported_evidence_version(reader, "unsupported benchmark bundle version")?;
        let run_id = read_limited_text(reader)?;
        let benchmark_claim = read_claim(reader)?;
        let repeatability_claim = read_claim(reader)?;
        let host_profile = match reader.u8()? {
            0 => None,
            1 => Some(read_host_body(reader)?),
            _ => return Err(decode_problem("non-canonical host-profile option")),
        };
        let workload = match reader.u8()? {
            0 => None,
            1 => Some(read_workload_body(reader)?),
            _ => return Err(decode_problem("non-canonical workload option")),
        };
        let attempts_started = reader.u32()?;
        let count = usize::try_from(reader.u64()?)
            .map_err(|_| decode_problem("attempt count exceeds address space"))?;
        if count > MAX_ATTEMPTS as usize {
            return Err(decode_problem("attempt count exceeds limit"));
        }
        let mut attempts = Vec::new();
        for _ in 0..count {
            attempts.push(read_attempt_body(reader)?);
        }
        let summary = match reader.u8()? {
            0 => None,
            1 => Some(read_summary_body(reader)?),
            _ => return Err(decode_problem("non-canonical summary option")),
        };
        let telemetry = match reader.u8()? {
            0 => None,
            1 => Some(read_telemetry_body(reader)?),
            _ => return Err(decode_problem("non-canonical telemetry option")),
        };
        let claimed_roots = match reader.u8()? {
            0 => None,
            1 => Some(read_roots(reader)?),
            _ => return Err(decode_problem("non-canonical roots option")),
        };
        Ok(Self {
            schema_version,
            run_id,
            benchmark_claim,
            repeatability_claim,
            host_profile,
            workload,
            attempts_started,
            attempts,
            summary,
            telemetry,
            claimed_roots,
        })
    }
}

/// Check the exact registered shape of independently stored benchmark evidence.
///
/// The schema header is admitted before its body is read, and the version-bearing
/// bodies reject an unknown inner version before reading any later field. Success is
/// deliberately weaker than [`validate_bundle`]: it grants no publication authority
/// and cannot turn a schema registration into an observed benchmark claim.
pub fn validate_benchmark_schema_bytes(
    bytes: &[u8],
) -> Result<BenchmarkSchemaKind, BenchmarkSchemaValidationError> {
    let mut reader = CanonReader::new(bytes);
    let name = reader.str()?;
    if name.len() > MAX_TEXT_BYTES {
        return Err(decode_problem("benchmark schema name exceeds limit").into());
    }
    let version = reader.u16()?;
    let row = registered_benchmark_schema(name, version)?;
    match row.kind {
        BenchmarkSchemaKind::HostProfile => {
            let _profile = read_host_body(&mut reader)?;
        }
        BenchmarkSchemaKind::Workload => {
            let _workload = read_workload_body(&mut reader)?;
        }
        BenchmarkSchemaKind::RawAttempts => read_attempts_body(&mut reader)?,
        BenchmarkSchemaKind::StatisticalSummary => {
            let _summary = read_summary_body(&mut reader)?;
        }
        BenchmarkSchemaKind::Telemetry => {
            let _telemetry = read_telemetry_body(&mut reader)?;
        }
        BenchmarkSchemaKind::Bundle => {
            let _bundle = <BenchmarkBundleCandidate as Canonical>::read_body(&mut reader)?;
        }
    }
    reader.finish()?;
    Ok(row.kind)
}

fn gcd(mut left: u128, mut right: u128) -> u128 {
    while right != 0 {
        let remainder = left % right;
        left = right;
        right = remainder;
    }
    left.max(1)
}

fn median_u128(sorted: &[u128]) -> Result<ExactRatio, BenchmarkRefusal> {
    if sorted.is_empty() {
        return Err(BenchmarkRefusal::SamplePlanUnsatisfied {
            valid: 0,
            required: 1,
        });
    }
    let middle = sorted.len() / 2;
    if sorted.len() % 2 == 1 {
        let value = sorted
            .get(middle)
            .copied()
            .ok_or(BenchmarkRefusal::StatisticsOverflow)?;
        ExactRatio::new(value, 1).ok_or(BenchmarkRefusal::StatisticsOverflow)
    } else {
        let lower = sorted
            .get(middle - 1)
            .copied()
            .ok_or(BenchmarkRefusal::StatisticsOverflow)?;
        let upper = sorted
            .get(middle)
            .copied()
            .ok_or(BenchmarkRefusal::StatisticsOverflow)?;
        let numerator = lower
            .checked_add(upper)
            .ok_or(BenchmarkRefusal::StatisticsOverflow)?;
        ExactRatio::new(numerator, 2).ok_or(BenchmarkRefusal::StatisticsOverflow)
    }
}

fn nearest_rank(sorted: &[u64], basis_points: u32) -> Result<u64, BenchmarkRefusal> {
    let length = u64::try_from(sorted.len()).map_err(|_| BenchmarkRefusal::StatisticsOverflow)?;
    let numerator = u64::from(basis_points)
        .checked_mul(length)
        .ok_or(BenchmarkRefusal::StatisticsOverflow)?;
    let rank = numerator.div_ceil(10_000).max(1);
    let index = usize::try_from(rank.saturating_sub(1))
        .map_err(|_| BenchmarkRefusal::StatisticsOverflow)?
        .min(sorted.len().saturating_sub(1));
    sorted
        .get(index)
        .copied()
        .ok_or(BenchmarkRefusal::StatisticsOverflow)
}

fn binomial(n: u32, k: u32) -> Option<u128> {
    let k = k.min(n - k);
    let mut result = 1_u128;
    for i in 0..k {
        result = result.checked_mul(u128::from(n - i))?;
        result /= u128::from(i + 1);
    }
    Some(result)
}

/// Conservative distribution-free 95% confidence interval for the population
/// median.  The sign-test tail is compared exactly: no floating-point platform
/// behavior can move an index.
fn median_confidence_95(sorted: &[u64]) -> Result<(u64, u64), BenchmarkRefusal> {
    if sorted.is_empty() {
        return Err(BenchmarkRefusal::SamplePlanUnsatisfied {
            valid: 0,
            required: 1,
        });
    }
    let n = u32::try_from(sorted.len()).map_err(|_| BenchmarkRefusal::StatisticsOverflow)?;
    let total = 1_u128
        .checked_shl(n)
        .ok_or(BenchmarkRefusal::StatisticsOverflow)?;
    let mut tail = 0_u128;
    let mut k = 0_u32;
    for candidate in 1..=n / 2 {
        tail = tail
            .checked_add(binomial(n, candidate - 1).ok_or(BenchmarkRefusal::StatisticsOverflow)?)
            .ok_or(BenchmarkRefusal::StatisticsOverflow)?;
        if tail.checked_mul(40).is_some_and(|scaled| scaled <= total) {
            k = candidate;
        } else {
            break;
        }
    }
    let (low, high) = if k == 0 {
        (0, sorted.len() - 1)
    } else {
        (
            usize::try_from(k - 1).map_err(|_| BenchmarkRefusal::StatisticsOverflow)?,
            usize::try_from(n - k).map_err(|_| BenchmarkRefusal::StatisticsOverflow)?,
        )
    };
    let low = sorted
        .get(low)
        .copied()
        .ok_or(BenchmarkRefusal::StatisticsOverflow)?;
    let high = sorted
        .get(high)
        .copied()
        .ok_or(BenchmarkRefusal::StatisticsOverflow)?;
    Ok((low, high))
}

fn relative_mad_basis_points(
    median: &ExactRatio,
    mad: &ExactRatio,
) -> Result<u64, BenchmarkRefusal> {
    if median.numerator == 0 {
        return if mad.numerator == 0 {
            Ok(0)
        } else {
            Ok(u64::MAX)
        };
    }
    let numerator = mad
        .numerator
        .checked_mul(median.denominator)
        .and_then(|value| value.checked_mul(10_000))
        .ok_or(BenchmarkRefusal::StatisticsOverflow)?;
    let denominator = mad
        .denominator
        .checked_mul(median.numerator)
        .ok_or(BenchmarkRefusal::StatisticsOverflow)?;
    let rounded_up = numerator
        .checked_add(denominator - 1)
        .ok_or(BenchmarkRefusal::StatisticsOverflow)?
        / denominator;
    u64::try_from(rounded_up).map_err(|_| BenchmarkRefusal::StatisticsOverflow)
}

/// Exact deterministic regeneration.  Only `Valid` attempts enter the distribution;
/// every other attempt remains counted in `excluded_attempts`.
pub fn regenerate_summary(
    workload: &WorkloadManifest,
    attempts: &[AttemptRecord],
) -> Result<StatisticalSummary, BenchmarkRefusal> {
    let mut values = attempts
        .iter()
        .filter_map(|attempt| match attempt.status {
            AttemptStatus::Valid { measurement } => Some(measurement),
            _ => None,
        })
        .collect::<Vec<_>>();
    if values.is_empty() {
        return Err(BenchmarkRefusal::SamplePlanUnsatisfied {
            valid: 0,
            required: match workload.sample_plan {
                SamplePlan::FixedValidSamples { samples } => samples,
                SamplePlan::RelativeMad { min_valid, .. } => min_valid,
            },
        });
    }
    values.sort_unstable();
    let valid_samples =
        u32::try_from(values.len()).map_err(|_| BenchmarkRefusal::StatisticsOverflow)?;
    if valid_samples > MAX_VALID_SAMPLES {
        return Err(BenchmarkRefusal::StatisticsOverflow);
    }

    let sum = values
        .iter()
        .try_fold(0_u128, |sum, value| sum.checked_add(u128::from(*value)));
    let sum = sum.ok_or(BenchmarkRefusal::StatisticsOverflow)?;
    let sum_squares = values.iter().try_fold(0_u128, |sum, value| {
        let value = u128::from(*value);
        sum.checked_add(value.checked_mul(value)?)
    });
    let sum_squares = sum_squares.ok_or(BenchmarkRefusal::StatisticsOverflow)?;
    let n = u128::from(valid_samples);
    let mean = ExactRatio::new(sum, n).ok_or(BenchmarkRefusal::StatisticsOverflow)?;
    let sample_variance = if valid_samples == 1 {
        ExactRatio::new(0, 1).ok_or(BenchmarkRefusal::StatisticsOverflow)?
    } else {
        let numerator = n
            .checked_mul(sum_squares)
            .and_then(|value| value.checked_sub(sum.checked_mul(sum)?))
            .ok_or(BenchmarkRefusal::StatisticsOverflow)?;
        let denominator = n
            .checked_mul(n - 1)
            .ok_or(BenchmarkRefusal::StatisticsOverflow)?;
        ExactRatio::new(numerator, denominator).ok_or(BenchmarkRefusal::StatisticsOverflow)?
    };
    let as_u128 = values
        .iter()
        .map(|value| u128::from(*value))
        .collect::<Vec<_>>();
    let median = median_u128(&as_u128)?;
    let mut deviations = values
        .iter()
        .map(|value| {
            u128::from(*value)
                .checked_mul(median.denominator)
                .map(|scaled| scaled.abs_diff(median.numerator))
                .ok_or(BenchmarkRefusal::StatisticsOverflow)
        })
        .collect::<Result<Vec<_>, _>>()?;
    deviations.sort_unstable();
    let scaled_mad = median_u128(&deviations)?;
    let mad_denominator = scaled_mad
        .denominator
        .checked_mul(median.denominator)
        .ok_or(BenchmarkRefusal::StatisticsOverflow)?;
    let median_absolute_deviation = ExactRatio::new(scaled_mad.numerator, mad_denominator)
        .ok_or(BenchmarkRefusal::StatisticsOverflow)?;
    let relative_mad_basis_points = relative_mad_basis_points(&median, &median_absolute_deviation)?;
    let (median_confidence_low, median_confidence_high) = median_confidence_95(&values)?;

    let minimum = values
        .first()
        .copied()
        .ok_or(BenchmarkRefusal::StatisticsOverflow)?;
    let maximum = values
        .last()
        .copied()
        .ok_or(BenchmarkRefusal::StatisticsOverflow)?;
    Ok(StatisticalSummary {
        valid_samples,
        excluded_attempts: u32::try_from(attempts.len() - values.len())
            .map_err(|_| BenchmarkRefusal::StatisticsOverflow)?,
        minimum,
        maximum,
        median,
        p95: nearest_rank(&values, 9_500)?,
        p99: nearest_rank(&values, 9_900)?,
        mean,
        sample_variance,
        median_absolute_deviation,
        relative_mad_basis_points,
        median_confidence_low,
        median_confidence_high,
        repeatable: relative_mad_basis_points
            <= u64::from(workload.variance_threshold_basis_points),
    })
}

fn observed_text<'a>(
    fact: &'a Captured<String>,
    check: &'static str,
) -> Result<&'a str, BenchmarkRefusal> {
    match fact {
        Captured::Observed { value, .. } if !value.is_empty() && value.len() <= MAX_TEXT_BYTES => {
            Ok(value)
        }
        _ => Err(BenchmarkRefusal::HostNotQualified { check }),
    }
}

fn observed_positive(fact: &Captured<u64>, check: &'static str) -> Result<u64, BenchmarkRefusal> {
    match fact {
        Captured::Observed { value, .. } if *value > 0 => Ok(*value),
        _ => Err(BenchmarkRefusal::HostNotQualified { check }),
    }
}

fn observed_true(fact: &Captured<bool>, check: &'static str) -> Result<(), BenchmarkRefusal> {
    match fact {
        Captured::Observed { value: true, .. } => Ok(()),
        _ => Err(BenchmarkRefusal::HostNotQualified { check }),
    }
}

fn sorted_unique(values: &[String]) -> bool {
    values
        .windows(2)
        .all(|window| matches!(window, [left, right] if left.as_str() < right.as_str()))
}

fn validate_host(
    profile: &HostProfile,
    policy: HostQualificationPolicy,
) -> Result<(), BenchmarkRefusal> {
    if profile.schema_version.ne(&BENCHMARK_EVIDENCE_VERSION) {
        return Err(BenchmarkRefusal::UnsupportedSchema {
            object: "host-profile",
            seen: profile.schema_version,
            supported: BENCHMARK_EVIDENCE_VERSION,
        });
    }
    observed_text(&profile.cpu_sku, "cpu-sku")?;
    observed_text(&profile.architecture, "architecture")?;
    let logical = observed_positive(&profile.enabled_logical_cores, "logical-cores")?;
    observed_positive(&profile.ram_bytes, "ram-bytes")?;
    observed_text(&profile.storage_device, "storage-device")?;
    observed_text(&profile.filesystem, "filesystem")?;
    observed_text(&profile.os_release, "os-release")?;
    observed_text(&profile.kernel_release, "kernel-release")?;
    observed_text(&profile.target_triple, "target-triple")?;
    observed_text(&profile.build_profile, "build-profile")?;
    observed_positive(&profile.monotonic_clock_resolution_ns, "monotonic-clock")?;
    if profile.enabled_features.len() > MAX_FEATURES
        || profile.counter_capabilities.len() > MAX_FEATURES
        || !sorted_unique(&profile.enabled_features)
        || !sorted_unique(&profile.counter_capabilities)
    {
        return Err(BenchmarkRefusal::MalformedHostProfile {
            field: "features-or-counters",
        });
    }
    if policy.require_physical_topology {
        let physical = observed_positive(&profile.physical_cores, "physical-topology")?;
        if physical > logical {
            return Err(BenchmarkRefusal::MalformedHostProfile {
                field: "physical-cores",
            });
        }
        if profile.smt_enabled.observed_value().is_none() {
            return Err(BenchmarkRefusal::HostNotQualified { check: "smt" });
        }
    }
    if policy.require_power_governor {
        observed_text(&profile.power_governor, "power-governor")?;
    }
    if policy.require_thermal_sensors {
        observed_positive(&profile.thermal_sensor_count, "thermal-sensors")?;
    }
    if policy.require_exclusive_cores {
        observed_true(&profile.isolation.exclusive_cores, "exclusive-cores")?;
    }
    if policy.require_stable_frequency {
        observed_true(&profile.isolation.stable_frequency, "stable-frequency")?;
    }
    if policy.require_thermal_stability {
        observed_true(&profile.isolation.thermal_stable, "thermal-stability")?;
    }
    if !policy.allow_virtualization
        && observed_text(&profile.virtualization, "virtualization")? == "hypervisor-detected"
    {
        return Err(BenchmarkRefusal::HostNotQualified {
            check: "virtualization-forbidden",
        });
    }
    if !policy.allow_translation
        && observed_text(&profile.translation, "translation")? != "native-target-architecture"
    {
        return Err(BenchmarkRefusal::HostNotQualified {
            check: "translation-forbidden",
        });
    }
    Ok(())
}

/// The artifact `franken_lean-odwj` prescribes for a host that cannot be
/// qualified: *"A missing or invalid host lane yields a BLOCKED evidence
/// artifact and this task remains open."*
///
/// It is deliberately the **absence** of a measurement made citable. It carries
/// no sample, no timing and no summary, because a host that failed admission
/// produced none — and a lane that emitted a figure anyway would be
/// manufacturing one.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BlockedHostQualification {
    pub schema_version: u16,
    /// Always `{ Benchmark, Blocked }`. A blocked lane may not claim any other
    /// state, which is what stops this artifact being read as a weak pass.
    pub claim: ClaimBinding,
    pub host_root: Digest,
    /// EVERY policy check the host failed, sorted and duplicate-free — not the
    /// first one. `validate_host` short-circuits because it only has to decide
    /// admission; an evidence artifact has to say what would need to change.
    pub failing_checks: Vec<&'static str>,
}

impl BlockedHostQualification {
    pub fn ndjson(&self) -> String {
        let checks = self
            .failing_checks
            .iter()
            .map(|check| format!("\"{}\"", json_escape(check)))
            .collect::<Vec<_>>()
            .join(",");
        format!(
            "{{\"schema\":\"fln.bench.host-qualification-blocked\",\"version\":{},\
             \"host_root\":\"{}\",\"benchmark_claim_class\":\"benchmark\",\
             \"benchmark_claim_state\":\"BLOCKED\",\"failing_checks\":[{}],\
             \"valid_samples\":0,\"measurements\":0}}\n",
            self.schema_version, self.host_root, checks,
        )
    }
}

/// Evaluate a host against a policy, collecting every failing check.
///
/// The `Ok`/`Err` verdict must agree with the admission `assemble_bundle`
/// performs; `blocked_host_qualification_agrees_with_bundle_admission` in
/// `linux_host_qualification` holds the two together, because a second copy of
/// this predicate that could drift from the enforcing one is the defect this
/// repository names most often.
pub fn qualify_host(
    profile: &HostProfile,
    policy: HostQualificationPolicy,
) -> Result<(), BlockedHostQualification> {
    let mut failing: Vec<&'static str> = Vec::new();

    // The unconditional facts, in validate_host's own order.
    for (check, ok) in [
        (
            "cpu-sku",
            observed_text(&profile.cpu_sku, "cpu-sku").is_ok(),
        ),
        (
            "architecture",
            observed_text(&profile.architecture, "architecture").is_ok(),
        ),
        (
            "logical-cores",
            observed_positive(&profile.enabled_logical_cores, "logical-cores").is_ok(),
        ),
        (
            "ram-bytes",
            observed_positive(&profile.ram_bytes, "ram-bytes").is_ok(),
        ),
        (
            "storage-device",
            observed_text(&profile.storage_device, "storage-device").is_ok(),
        ),
        (
            "filesystem",
            observed_text(&profile.filesystem, "filesystem").is_ok(),
        ),
        (
            "os-release",
            observed_text(&profile.os_release, "os-release").is_ok(),
        ),
        (
            "kernel-release",
            observed_text(&profile.kernel_release, "kernel-release").is_ok(),
        ),
        (
            "target-triple",
            observed_text(&profile.target_triple, "target-triple").is_ok(),
        ),
        (
            "build-profile",
            observed_text(&profile.build_profile, "build-profile").is_ok(),
        ),
        (
            "monotonic-clock",
            observed_positive(&profile.monotonic_clock_resolution_ns, "monotonic-clock").is_ok(),
        ),
    ] {
        if !ok {
            failing.push(check);
        }
    }

    if policy.require_physical_topology {
        if observed_positive(&profile.physical_cores, "physical-topology").is_err() {
            failing.push("physical-topology");
        }
        if profile.smt_enabled.observed_value().is_none() {
            failing.push("smt");
        }
    }
    if policy.require_power_governor
        && observed_text(&profile.power_governor, "power-governor").is_err()
    {
        failing.push("power-governor");
    }
    if policy.require_thermal_sensors
        && observed_positive(&profile.thermal_sensor_count, "thermal-sensors").is_err()
    {
        failing.push("thermal-sensors");
    }
    if policy.require_exclusive_cores
        && observed_true(&profile.isolation.exclusive_cores, "exclusive-cores").is_err()
    {
        failing.push("exclusive-cores");
    }
    if policy.require_stable_frequency
        && observed_true(&profile.isolation.stable_frequency, "stable-frequency").is_err()
    {
        failing.push("stable-frequency");
    }
    if policy.require_thermal_stability
        && observed_true(&profile.isolation.thermal_stable, "thermal-stability").is_err()
    {
        failing.push("thermal-stability");
    }
    if !policy.allow_virtualization
        && profile.virtualization.observed_value().map(String::as_str)
            == Some("hypervisor-detected")
    {
        failing.push("virtualization-forbidden");
    }
    if !policy.allow_translation
        && profile.translation.observed_value().map(String::as_str)
            != Some("native-target-architecture")
    {
        failing.push("translation-forbidden");
    }

    if failing.is_empty() {
        return Ok(());
    }
    failing.sort_unstable();
    failing.dedup();
    Err(BlockedHostQualification {
        schema_version: BENCHMARK_EVIDENCE_VERSION,
        claim: ClaimBinding {
            class: ClaimClass::Benchmark,
            state: ClaimState::Blocked,
        },
        host_root: profile.root(),
        failing_checks: failing,
    })
}

fn validate_workload(workload: &WorkloadManifest) -> Result<(), BenchmarkRefusal> {
    if workload.schema_version.ne(&BENCHMARK_EVIDENCE_VERSION) {
        return Err(BenchmarkRefusal::UnsupportedSchema {
            object: "workload",
            seen: workload.schema_version,
            supported: BENCHMARK_EVIDENCE_VERSION,
        });
    }
    if workload.workload_id.is_empty() || workload.workload_id.len() > MAX_TEXT_BYTES {
        return Err(BenchmarkRefusal::MalformedWorkload {
            field: "workload-id",
        });
    }
    // Sorted and duplicate-free, or two orderings of the SAME oracle tool set
    // would produce different workload roots and a re-registration could be
    // passed off as a different workload. Each name and digest is bounded for
    // the same reason every other text field here is.
    if workload.oracle_tools.len() > MAX_FEATURES
        || workload
            .oracle_tools
            .iter()
            .any(|tool| tool.name.is_empty() || tool.name.len() > MAX_TEXT_BYTES)
        || !workload
            .oracle_tools
            .windows(2)
            .all(|pair| pair[0].name < pair[1].name)
    {
        return Err(BenchmarkRefusal::MalformedWorkload {
            field: "oracle-tools",
        });
    }
    let max_valid = match workload.sample_plan {
        SamplePlan::FixedValidSamples { samples } if samples > 0 => samples,
        SamplePlan::FixedValidSamples { .. } => {
            return Err(BenchmarkRefusal::MalformedWorkload {
                field: "fixed-samples",
            });
        }
        SamplePlan::RelativeMad {
            min_valid,
            max_valid,
            threshold_basis_points,
        } if min_valid > 0 && min_valid <= max_valid && threshold_basis_points <= 10_000 => {
            max_valid
        }
        SamplePlan::RelativeMad { .. } => {
            return Err(BenchmarkRefusal::MalformedWorkload {
                field: "relative-mad-plan",
            });
        }
    };
    if max_valid > MAX_VALID_SAMPLES
        || workload.resource_bounds.max_attempts == 0
        || workload.resource_bounds.max_attempts > MAX_ATTEMPTS
        || max_valid > workload.resource_bounds.max_attempts
        || workload.resource_bounds.max_measurement == 0
        || workload.resource_bounds.max_elapsed_ns_per_attempt == 0
        || workload.variance_threshold_basis_points > 10_000
    {
        return Err(BenchmarkRefusal::MalformedWorkload {
            field: "resource-or-variance-bounds",
        });
    }
    Ok(())
}

fn validate_attempts(
    candidate: &BenchmarkBundleCandidate,
    host_root: Digest,
    workload: &WorkloadManifest,
    workload_root: Digest,
) -> Result<(), BenchmarkRefusal> {
    if candidate.attempts_started as usize != candidate.attempts.len() {
        return Err(BenchmarkRefusal::AttemptsStartedMismatch {
            declared: candidate.attempts_started,
            actual: candidate.attempts.len(),
        });
    }
    if candidate.attempts.len() > workload.resource_bounds.max_attempts as usize {
        return Err(BenchmarkRefusal::TooManyAttempts {
            observed: candidate.attempts.len(),
            allowed: workload.resource_bounds.max_attempts,
        });
    }
    let mut ids = BTreeSet::new();
    for (index, attempt) in candidate.attempts.iter().enumerate() {
        let expected = index as u32;
        if attempt.ordinal != expected {
            return Err(BenchmarkRefusal::AttemptOrdinalMismatch {
                attempt_id: attempt.attempt_id.clone(),
                expected,
                actual: attempt.ordinal,
            });
        }
        if attempt.attempt_id.is_empty() || attempt.attempt_id.len() > MAX_TEXT_BYTES {
            return Err(BenchmarkRefusal::MalformedAttempt {
                attempt_id: attempt.attempt_id.clone(),
                field: "attempt-id",
            });
        }
        if !ids.insert(attempt.attempt_id.as_str()) {
            return Err(BenchmarkRefusal::DuplicateAttemptId {
                attempt_id: attempt.attempt_id.clone(),
            });
        }
        if attempt.host_root.ne(&host_root) {
            return Err(BenchmarkRefusal::HostProfileSubstitution {
                attempt_id: attempt.attempt_id.clone(),
            });
        }
        if attempt.workload_root.ne(&workload_root) {
            return Err(BenchmarkRefusal::WorkloadSubstitution {
                attempt_id: attempt.attempt_id.clone(),
            });
        }
        match &attempt.status {
            AttemptStatus::Valid { measurement } => {
                if attempt.cache_state.ne(&workload.cache_state) {
                    return Err(BenchmarkRefusal::CacheStateMismatch {
                        attempt_id: attempt.attempt_id.clone(),
                    });
                }
                if attempt.profiler == ProfilerState::Enabled
                    && !workload.host_policy.allow_profiler
                {
                    return Err(BenchmarkRefusal::ProfilerContamination {
                        attempt_id: attempt.attempt_id.clone(),
                    });
                }
                if *measurement > workload.resource_bounds.max_measurement {
                    return Err(BenchmarkRefusal::MalformedAttempt {
                        attempt_id: attempt.attempt_id.clone(),
                        field: "measurement-bound",
                    });
                }
            }
            AttemptStatus::InvalidHost { reason }
            | AttemptStatus::Cancelled { reason }
            | AttemptStatus::InfrastructureFault { code: reason } => {
                if reason.is_empty() || reason.len() > MAX_TEXT_BYTES {
                    return Err(BenchmarkRefusal::MalformedAttempt {
                        attempt_id: attempt.attempt_id.clone(),
                        field: "reason",
                    });
                }
            }
            AttemptStatus::ResourceRefused {
                allowed, observed, ..
            } if observed <= allowed => {
                return Err(BenchmarkRefusal::MalformedAttempt {
                    attempt_id: attempt.attempt_id.clone(),
                    field: "resource-refusal",
                });
            }
            AttemptStatus::TargetFailed { exit_code: 0 } => {
                return Err(BenchmarkRefusal::MalformedAttempt {
                    attempt_id: attempt.attempt_id.clone(),
                    field: "target-exit-code",
                });
            }
            AttemptStatus::InsufficientSample {
                valid_observed,
                valid_required,
            } if valid_observed >= valid_required || *valid_required == 0 => {
                return Err(BenchmarkRefusal::MalformedAttempt {
                    attempt_id: attempt.attempt_id.clone(),
                    field: "insufficient-sample",
                });
            }
            _ => {}
        }
    }
    Ok(())
}

fn validate_sample_plan(
    workload: &WorkloadManifest,
    summary: &StatisticalSummary,
) -> Result<(), BenchmarkRefusal> {
    match workload.sample_plan {
        SamplePlan::FixedValidSamples { samples } => {
            if summary.valid_samples < samples {
                return Err(BenchmarkRefusal::SamplePlanUnsatisfied {
                    valid: summary.valid_samples,
                    required: samples,
                });
            }
            if summary.valid_samples > samples {
                return Err(BenchmarkRefusal::SamplePlanOverrun {
                    valid: summary.valid_samples,
                    allowed: samples,
                });
            }
        }
        SamplePlan::RelativeMad {
            min_valid,
            max_valid,
            threshold_basis_points,
        } => {
            if summary.valid_samples < min_valid {
                return Err(BenchmarkRefusal::SamplePlanUnsatisfied {
                    valid: summary.valid_samples,
                    required: min_valid,
                });
            }
            if summary.valid_samples > max_valid {
                return Err(BenchmarkRefusal::SamplePlanOverrun {
                    valid: summary.valid_samples,
                    allowed: max_valid,
                });
            }
            if summary.valid_samples < max_valid
                && summary.relative_mad_basis_points > u64::from(threshold_basis_points)
            {
                return Err(BenchmarkRefusal::SamplePlanUnsatisfied {
                    valid: summary.valid_samples,
                    required: max_valid,
                });
            }
        }
    }
    Ok(())
}

fn validate_claim(binding: ClaimBinding, expected: ClaimClass) -> Result<(), BenchmarkRefusal> {
    if binding.class == expected && binding.state == ClaimState::Observed {
        Ok(())
    } else {
        Err(BenchmarkRefusal::ClaimAuthorityMismatch {
            class: binding.class,
            state: binding.state,
        })
    }
}

fn validate_telemetry(
    telemetry: &BenchmarkTelemetry,
    attempts: &[AttemptRecord],
    workload: &WorkloadManifest,
) -> Result<(), BenchmarkRefusal> {
    if telemetry.schema_version.ne(&BENCHMARK_EVIDENCE_VERSION) {
        return Err(BenchmarkRefusal::UnsupportedSchema {
            object: "telemetry",
            seen: telemetry.schema_version,
            supported: BENCHMARK_EVIDENCE_VERSION,
        });
    }
    if telemetry.attempts.len() != attempts.len() {
        return Err(BenchmarkRefusal::TelemetryLinkMismatch {
            attempt_id: "<count>".to_string(),
        });
    }
    for (record, attempt) in telemetry.attempts.iter().zip(attempts) {
        if record.attempt_id != attempt.attempt_id {
            return Err(BenchmarkRefusal::TelemetryLinkMismatch {
                attempt_id: record.attempt_id.clone(),
            });
        }
        if record.absolute_working_directory.is_empty()
            || record.absolute_working_directory.len() > MAX_TEXT_BYTES
        {
            return Err(BenchmarkRefusal::TelemetryOutOfBounds {
                attempt_id: record.attempt_id.clone(),
                field: "working-directory",
            });
        }
        if record.counters.len() > MAX_COUNTERS_PER_ATTEMPT {
            return Err(BenchmarkRefusal::TelemetryOutOfBounds {
                attempt_id: record.attempt_id.clone(),
                field: "counter-count",
            });
        }
        if record
            .counters
            .windows(2)
            .any(|window| matches!(window, [left, right] if left.name >= right.name))
            || record
                .counters
                .iter()
                .any(|counter| counter.name.is_empty() || counter.name.len() > MAX_TEXT_BYTES)
        {
            return Err(BenchmarkRefusal::TelemetryOutOfBounds {
                attempt_id: record.attempt_id.clone(),
                field: "counter-names",
            });
        }
        if matches!(attempt.status, AttemptStatus::Valid { .. })
            && record.elapsed_ns > workload.resource_bounds.max_elapsed_ns_per_attempt
        {
            return Err(BenchmarkRefusal::TelemetryOutOfBounds {
                attempt_id: record.attempt_id.clone(),
                field: "elapsed-bound",
            });
        }
    }
    Ok(())
}

fn ratio_text(ratio: &ExactRatio) -> String {
    format!("{}/{}", ratio.numerator, ratio.denominator)
}

fn render_report(
    candidate: &BenchmarkBundleCandidate,
    host_root: Digest,
    workload: &WorkloadManifest,
    workload_root: Digest,
    summary: &StatisticalSummary,
) -> String {
    format!(
        "schema=fln.bench.report/1\n\
         run_id={}\n\
         claim=OBSERVED\n\
         host_root={host_root}\n\
         workload_id={}\n\
         workload_root={workload_root}\n\
         unit={:?}\n\
         attempts_started={}\n\
         valid_samples={}\n\
         excluded_attempts={}\n\
         median={}\n\
         p95={}\n\
         p99={}\n\
         sample_variance={}\n\
         median_absolute_deviation={}\n\
         relative_mad_basis_points={}\n\
         median_confidence_95=[{},{}]\n\
         repeatable={}\n",
        candidate.run_id,
        workload.workload_id,
        workload.unit,
        candidate.attempts_started,
        summary.valid_samples,
        summary.excluded_attempts,
        ratio_text(&summary.median),
        summary.p95,
        summary.p99,
        ratio_text(&summary.sample_variance),
        ratio_text(&summary.median_absolute_deviation),
        summary.relative_mad_basis_points,
        summary.median_confidence_low,
        summary.median_confidence_high,
        summary.repeatable,
    )
}

fn tagged_root(tag: &str, write: impl FnOnce(&mut CanonWriter)) -> Digest {
    let mut writer = CanonWriter::new();
    writer.schema(BENCHMARK_BUNDLE_SCHEMA);
    writer.str(tag);
    write(&mut writer);
    hash(Domain::OperationalMeta, &writer.into_bytes())
}

fn compute_roots(
    candidate: &BenchmarkBundleCandidate,
    host: &HostProfile,
    workload: &WorkloadManifest,
    summary: &StatisticalSummary,
    telemetry: &BenchmarkTelemetry,
) -> (BundleRoots, String) {
    let host_root = host.root();
    let workload_root = workload.root();
    let raw_attempts = hash(
        Domain::OperationalMeta,
        &attempts_bytes(candidate.attempts_started, &candidate.attempts),
    );
    let statistics = hash(Domain::OperationalMeta, &summary_bytes(summary));
    let report = render_report(candidate, host_root, workload, workload_root, summary);
    let report_root = tagged_root("report/1", |writer| writer.str(&report));
    let semantic = tagged_root("semantic/1", |writer| {
        writer.str(&candidate.run_id);
        write_claim(writer, candidate.benchmark_claim);
        write_claim(writer, candidate.repeatability_claim);
        for root in [
            host_root,
            workload_root,
            raw_attempts,
            statistics,
            report_root,
        ] {
            write_digest(writer, root);
        }
    });
    let telemetry_root = hash(Domain::OperationalMeta, &telemetry_bytes(telemetry));
    let bundle = tagged_root("outer/1", |writer| {
        write_digest(writer, semantic);
        write_digest(writer, telemetry_root);
    });
    (
        BundleRoots {
            host: host_root,
            workload: workload_root,
            raw_attempts,
            statistics,
            report: report_root,
            semantic,
            telemetry: telemetry_root,
            bundle,
        },
        report,
    )
}

fn compare_root(
    component: RootComponent,
    expected: Digest,
    actual: Digest,
) -> Result<(), BenchmarkRefusal> {
    if expected == actual {
        Ok(())
    } else {
        Err(BenchmarkRefusal::RootMismatch {
            component,
            expected,
            actual,
        })
    }
}

/// Independently validate every field, regenerate the statistics and root chain, and
/// return the only publication-capable type.
pub fn validate_bundle(
    candidate: &BenchmarkBundleCandidate,
) -> Result<ValidatedBenchmarkBundle, BenchmarkRefusal> {
    if candidate.schema_version.ne(&BENCHMARK_EVIDENCE_VERSION) {
        return Err(BenchmarkRefusal::UnsupportedSchema {
            object: "bundle",
            seen: candidate.schema_version,
            supported: BENCHMARK_EVIDENCE_VERSION,
        });
    }
    if candidate.run_id.is_empty() || candidate.run_id.len() > MAX_TEXT_BYTES {
        return Err(BenchmarkRefusal::MalformedWorkload { field: "run-id" });
    }
    validate_claim(candidate.benchmark_claim, ClaimClass::Benchmark)?;
    validate_claim(candidate.repeatability_claim, ClaimClass::Statistical)?;
    let host = candidate
        .host_profile
        .as_ref()
        .ok_or(BenchmarkRefusal::MissingHostProfile)?;
    let workload = candidate
        .workload
        .as_ref()
        .ok_or(BenchmarkRefusal::MissingWorkload)?;
    validate_workload(workload)?;
    validate_host(host, workload.host_policy)?;
    let host_root = host.root();
    let workload_root = workload.root();
    validate_attempts(candidate, host_root, workload, workload_root)?;
    let summary = candidate
        .summary
        .as_ref()
        .ok_or(BenchmarkRefusal::MissingSummary)?;
    let regenerated = regenerate_summary(workload, &candidate.attempts)?;
    if *summary != regenerated {
        return Err(BenchmarkRefusal::StaleSummary);
    }
    validate_sample_plan(workload, summary)?;
    let telemetry = candidate
        .telemetry
        .as_ref()
        .ok_or(BenchmarkRefusal::MissingTelemetry)?;
    validate_telemetry(telemetry, &candidate.attempts, workload)?;
    let claimed = candidate
        .claimed_roots
        .ok_or(BenchmarkRefusal::MissingRootChain)?;
    let (actual, report) = compute_roots(candidate, host, workload, summary, telemetry);
    for (component, expected, observed) in [
        (RootComponent::Host, claimed.host, actual.host),
        (RootComponent::Workload, claimed.workload, actual.workload),
        (
            RootComponent::RawAttempts,
            claimed.raw_attempts,
            actual.raw_attempts,
        ),
        (
            RootComponent::Statistics,
            claimed.statistics,
            actual.statistics,
        ),
        (RootComponent::Report, claimed.report, actual.report),
        (RootComponent::Semantic, claimed.semantic, actual.semantic),
        (
            RootComponent::Telemetry,
            claimed.telemetry,
            actual.telemetry,
        ),
        (RootComponent::Bundle, claimed.bundle, actual.bundle),
    ] {
        compare_root(component, expected, observed)?;
    }
    Ok(ValidatedBenchmarkBundle {
        candidate: candidate.clone(),
        roots: actual,
        report,
    })
}

/// Producer convenience.  It has no publication authority: it creates a candidate,
/// then drives the same validator an independent consumer uses.
pub fn assemble_bundle(
    run_id: impl Into<String>,
    host: HostProfile,
    workload: WorkloadManifest,
    attempts: Vec<AttemptRecord>,
    telemetry: BenchmarkTelemetry,
) -> Result<BenchmarkBundleCandidate, BenchmarkRefusal> {
    validate_workload(&workload)?;
    validate_host(&host, workload.host_policy)?;
    let summary = regenerate_summary(&workload, &attempts)?;
    let mut candidate = BenchmarkBundleCandidate {
        schema_version: BENCHMARK_EVIDENCE_VERSION,
        run_id: run_id.into(),
        benchmark_claim: ClaimBinding {
            class: ClaimClass::Benchmark,
            state: ClaimState::Observed,
        },
        repeatability_claim: ClaimBinding {
            class: ClaimClass::Statistical,
            state: ClaimState::Observed,
        },
        host_profile: Some(host),
        workload: Some(workload),
        attempts_started: u32::try_from(attempts.len())
            .map_err(|_| BenchmarkRefusal::StatisticsOverflow)?,
        attempts,
        summary: Some(summary),
        telemetry: Some(telemetry),
        claimed_roots: None,
    };
    let host = candidate
        .host_profile
        .as_ref()
        .ok_or(BenchmarkRefusal::MissingHostProfile)?;
    let workload = candidate
        .workload
        .as_ref()
        .ok_or(BenchmarkRefusal::MissingWorkload)?;
    validate_attempts(&candidate, host.root(), workload, workload.root())?;
    validate_sample_plan(
        workload,
        candidate
            .summary
            .as_ref()
            .ok_or(BenchmarkRefusal::MissingSummary)?,
    )?;
    validate_telemetry(
        candidate
            .telemetry
            .as_ref()
            .ok_or(BenchmarkRefusal::MissingTelemetry)?,
        &candidate.attempts,
        workload,
    )?;
    let (roots, _) = compute_roots(
        &candidate,
        host,
        workload,
        candidate
            .summary
            .as_ref()
            .ok_or(BenchmarkRefusal::MissingSummary)?,
        candidate
            .telemetry
            .as_ref()
            .ok_or(BenchmarkRefusal::MissingTelemetry)?,
    );
    candidate.claimed_roots = Some(roots);
    validate_bundle(&candidate)?;
    Ok(candidate)
}

pub fn validate_bundle_bytes(
    bytes: &[u8],
) -> Result<ValidatedBenchmarkBundle, BundleValidationError> {
    let candidate = BenchmarkBundleCandidate::from_canonical_bytes(bytes)
        .map_err(BundleValidationError::Decode)?;
    validate_bundle(&candidate).map_err(BundleValidationError::Refused)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::hint::black_box;

    #[derive(Debug, Clone, PartialEq, Eq)]
    struct DeclaredSchema {
        name: String,
        version: String,
    }

    fn matching_brace(rest: &str) -> Option<usize> {
        let mut depth = 1usize;
        for (index, character) in rest.char_indices() {
            match character {
                '{' => depth = depth.saturating_add(1),
                '}' => {
                    depth = depth.checked_sub(1)?;
                    if depth == 0 {
                        return Some(index);
                    }
                }
                _ => {}
            }
        }
        None
    }

    fn schema_field(body: &str, key: &str) -> Option<String> {
        let offset = body.find(&format!("{key}:"))?;
        let rest = body.get(offset + key.len() + 1..)?;
        let end = rest.find(',').unwrap_or(rest.len());
        Some(rest.get(..end)?.trim().to_string())
    }

    fn declared_schemas(source: &str) -> Vec<DeclaredSchema> {
        const NEEDLE: &str = ": SchemaId = SchemaId {";
        let mut declarations = Vec::new();
        let mut cursor = 0usize;
        while let Some(offset) = source.get(cursor..).and_then(|rest| rest.find(NEEDLE)) {
            let body_start = cursor + offset + NEEDLE.len();
            cursor = body_start;
            let Some(body_source) = source.get(body_start..) else {
                break;
            };
            let Some(body_len) = matching_brace(body_source) else {
                continue;
            };
            let Some(body) = body_source.get(..body_len) else {
                continue;
            };
            let (Some(quoted_name), Some(version)) =
                (schema_field(body, "name"), schema_field(body, "version"))
            else {
                continue;
            };
            let Some(name) = quoted_name
                .strip_prefix('"')
                .and_then(|rest| rest.strip_suffix('"'))
            else {
                continue;
            };
            declarations.push(DeclaredSchema {
                name: name.to_string(),
                version,
            });
        }
        declarations
    }

    fn resolve_declared_version(source: &str, version: &str) -> Option<u16> {
        if let Ok(literal) = version.parse::<u16>() {
            return Some(literal);
        }
        let declaration = format!("const {version}: u16 = ");
        let offset = source.find(&declaration)?;
        let rest = source.get(offset + declaration.len()..)?;
        let end = rest.find(';')?;
        rest.get(..end)?.trim().parse().ok()
    }

    fn declared_schema_pairs(source: &str) -> Result<Vec<(String, u16)>, String> {
        let mut pairs = Vec::new();
        for declaration in declared_schemas(source) {
            let version =
                resolve_declared_version(source, &declaration.version).ok_or_else(|| {
                    format!(
                        "cannot resolve version {} for {}",
                        declaration.version, declaration.name
                    )
                })?;
            pairs.push((declaration.name, version));
        }
        pairs.sort();
        Ok(pairs)
    }

    fn registered_schema_pairs() -> Vec<(String, u16)> {
        let mut pairs = BENCHMARK_SCHEMA_REGISTRY
            .iter()
            .map(|row| (row.id.name.to_string(), row.id.version))
            .collect::<Vec<_>>();
        pairs.sort();
        pairs
    }

    fn production_source() -> Result<&'static str, String> {
        include_str!("lib.rs")
            .split_once("\n#[cfg(test)]")
            .map(|(production, _)| production)
            .ok_or_else(|| "fln-bench source has no cfg(test) boundary".to_string())
    }

    fn digest(label: &str) -> Digest {
        hash(Domain::OperationalMeta, label.as_bytes())
    }

    fn text(value: &str) -> Captured<String> {
        Captured::observed(value.to_string(), CaptureSource::RuntimeProbe)
    }

    fn number(value: u64) -> Captured<u64> {
        Captured::observed(value, CaptureSource::RuntimeProbe)
    }

    fn boolean(value: bool) -> Captured<bool> {
        Captured::observed(value, CaptureSource::RuntimeProbe)
    }

    fn fixture_host(sku: &str) -> HostProfile {
        HostProfile {
            schema_version: BENCHMARK_EVIDENCE_VERSION,
            cpu_sku: text(sku),
            architecture: text("x86_64"),
            physical_cores: number(16),
            enabled_logical_cores: number(32),
            smt_enabled: boolean(true),
            ram_bytes: number(64 * 1024 * 1024 * 1024),
            storage_device: text("nvme-fixture"),
            filesystem: text("ext4"),
            os_release: text("Fixture Linux 1"),
            kernel_release: text("6.12.fixture"),
            power_governor: text("performance"),
            thermal_policy: text("fixture-stable"),
            thermal_sensor_count: number(2),
            thermal_sensors: text("2 thermal zones exposed"),
            virtualization: text("no-hypervisor-flag"),
            translation: text("native-target-architecture"),
            toolchain_hash: digest("toolchain"),
            binary_hash: digest("binary"),
            target_triple: text("x86_64-unknown-linux-gnu"),
            build_profile: text("release"),
            enabled_features: vec!["feature-a".to_string(), "feature-b".to_string()],
            monotonic_clock_resolution_ns: number(1),
            counter_capabilities: vec!["cycles".to_string(), "instructions".to_string()],
            isolation: HostIsolation {
                exclusive_cores: boolean(true),
                stable_frequency: boolean(true),
                thermal_stable: boolean(true),
            },
        }
    }

    fn permissive_policy() -> HostQualificationPolicy {
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
            reference_artifacts: CacheCondition::NotApplicable,
            candidate_artifacts: CacheCondition::Cold,
            build_cache: CacheCondition::Cold,
            imported_modules: CacheCondition::Cold,
            daemon: CacheCondition::Cold,
        }
    }

    fn fixture_workload(samples: u32) -> WorkloadManifest {
        WorkloadManifest {
            schema_version: BENCHMARK_EVIDENCE_VERSION,
            workload_id: "fixture-workload".to_string(),
            workload_kind: WorkloadKind::CorpusBuild,
            oracle_tools: Vec::new(),
            corpus_root: digest("corpus"),
            input_order_root: digest("input-order"),
            warmup_iterations: 2,
            sample_plan: SamplePlan::FixedValidSamples { samples },
            quantile_algorithm: QuantileAlgorithm::NearestRankV1,
            confidence_algorithm: ConfidenceAlgorithm::DistributionFreeMedian95V1,
            outlier_policy: OutlierPolicy::RetainAllV1,
            variance_threshold_basis_points: 10_000,
            cache_state: cache_state(),
            unit: MeasurementUnit::Nanoseconds,
            host_policy: permissive_policy(),
            resource_bounds: ResourceBounds {
                max_attempts: 32,
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
            attempt_id: format!("attempt-{ordinal}"),
            ordinal,
            host_root,
            workload_root,
            cache_state: cache_state(),
            profiler: ProfilerState::Disabled,
            status,
        }
    }

    fn fixture_attempts(host: &HostProfile, workload: &WorkloadManifest) -> Vec<AttemptRecord> {
        let host_root = host.root();
        let workload_root = workload.root();
        vec![
            attempt(
                0,
                host_root,
                workload_root,
                AttemptStatus::Valid { measurement: 100 },
            ),
            attempt(
                1,
                host_root,
                workload_root,
                AttemptStatus::InvalidHost {
                    reason: "thermal precheck failed".to_string(),
                },
            ),
            attempt(
                2,
                host_root,
                workload_root,
                AttemptStatus::Cancelled {
                    reason: "operator cancellation".to_string(),
                },
            ),
            attempt(
                3,
                host_root,
                workload_root,
                AttemptStatus::InsufficientSample {
                    valid_observed: 1,
                    valid_required: 3,
                },
            ),
            attempt(
                4,
                host_root,
                workload_root,
                AttemptStatus::Valid { measurement: 110 },
            ),
            attempt(
                5,
                host_root,
                workload_root,
                AttemptStatus::Valid { measurement: 120 },
            ),
            attempt(
                6,
                host_root,
                workload_root,
                AttemptStatus::ResourceRefused {
                    resource: ResourceKind::Time,
                    allowed: 100,
                    observed: 101,
                },
            ),
            attempt(
                7,
                host_root,
                workload_root,
                AttemptStatus::TargetFailed { exit_code: 1 },
            ),
            attempt(
                8,
                host_root,
                workload_root,
                AttemptStatus::InfrastructureFault {
                    code: "fixture-runner-fault".to_string(),
                },
            ),
        ]
    }

    fn fixture_telemetry(attempts: &[AttemptRecord]) -> BenchmarkTelemetry {
        BenchmarkTelemetry {
            schema_version: BENCHMARK_EVIDENCE_VERSION,
            attempts: attempts
                .iter()
                .map(|attempt| AttemptTelemetry {
                    attempt_id: attempt.attempt_id.clone(),
                    wall_clock_start_ns: 1_000 + u64::from(attempt.ordinal),
                    elapsed_ns: 10 + u64::from(attempt.ordinal),
                    process_id: 42,
                    absolute_working_directory: "/fixture".to_string(),
                    counters: vec![
                        CounterReading {
                            name: "cycles".to_string(),
                            value: 100 + u64::from(attempt.ordinal),
                        },
                        CounterReading {
                            name: "instructions".to_string(),
                            value: 200 + u64::from(attempt.ordinal),
                        },
                    ],
                })
                .collect(),
        }
    }

    fn fixture_bundle() -> Result<BenchmarkBundleCandidate, String> {
        let host = fixture_host("fixture-cpu");
        let workload = fixture_workload(3);
        let attempts = fixture_attempts(&host, &workload);
        let telemetry = fixture_telemetry(&attempts);
        assemble_bundle("fixture-run", host, workload, attempts, telemetry)
            .map_err(|error| format!("fixture must validate: {error:?}"))
    }

    fn fixture_schema_bytes(
        kind: BenchmarkSchemaKind,
        bundle: &BenchmarkBundleCandidate,
    ) -> Result<Vec<u8>, String> {
        match kind {
            BenchmarkSchemaKind::HostProfile => bundle
                .host_profile
                .as_ref()
                .map(host_profile_bytes)
                .ok_or_else(|| "fixture has no host profile".to_string()),
            BenchmarkSchemaKind::Workload => bundle
                .workload
                .as_ref()
                .map(workload_bytes)
                .ok_or_else(|| "fixture has no workload".to_string()),
            BenchmarkSchemaKind::RawAttempts => {
                Ok(attempts_bytes(bundle.attempts_started, &bundle.attempts))
            }
            BenchmarkSchemaKind::StatisticalSummary => bundle
                .summary
                .as_ref()
                .map(summary_bytes)
                .ok_or_else(|| "fixture has no statistical summary".to_string()),
            BenchmarkSchemaKind::Telemetry => bundle
                .telemetry
                .as_ref()
                .map(telemetry_bytes)
                .ok_or_else(|| "fixture has no telemetry".to_string()),
            BenchmarkSchemaKind::Bundle => Ok(bundle.to_canonical_bytes()),
        }
    }

    fn schema_header_version_offset(row: &BenchmarkSchemaRow) -> usize {
        std::mem::size_of::<u64>() + row.id.name.len()
    }

    #[test]
    fn durable_schema_registry_is_complete_unique_and_bidirectional() -> Result<(), String> {
        let source = production_source()?;
        let declared = declared_schema_pairs(source)?;
        let registered = registered_schema_pairs();
        assert_eq!(
            declared, registered,
            "every durable SchemaId declaration must have exactly one local registry row, \
             and every row must retain its declaration"
        );
        assert_eq!(registered.len(), BenchmarkSchemaKind::ALL.len());

        let mut kinds = BTreeSet::new();
        let mut names = BTreeSet::new();
        for row in BENCHMARK_SCHEMA_REGISTRY {
            assert!(
                kinds.insert(row.kind),
                "duplicate schema kind: {:?}",
                row.kind
            );
            assert!(
                names.insert(row.id.name),
                "duplicate schema name: {}",
                row.id.name
            );
            assert!(row.id.name.starts_with("fln.bench."));
            assert!(
                row.id.name.bytes().all(|byte| byte.is_ascii_lowercase()
                    || byte.is_ascii_digit()
                    || b".-".contains(&byte)),
                "schema name is not canonical: {}",
                row.id.name
            );
            assert!(!row.covers.is_empty());
            assert_eq!(
                registered_benchmark_schema(row.id.name, row.id.version),
                Ok(&row)
            );
        }
        assert_eq!(
            kinds,
            BenchmarkSchemaKind::ALL.into_iter().collect(),
            "a durable shape is omitted or duplicated"
        );

        let mut unregistered_source = source.to_string();
        unregistered_source.push_str("\npub const BENCHMARK_SNEAK_SCHEMA");
        unregistered_source.push_str(": SchemaId = SchemaId {");
        unregistered_source.push_str(
            "\n    name: \"fln.bench.sneak\",\n    version: \
             BENCHMARK_EVIDENCE_VERSION,\n};\n",
        );
        let unregistered = declared_schema_pairs(&unregistered_source)?;
        assert!(
            unregistered.iter().any(|pair| !registered.contains(pair)),
            "the production declaration scanner missed a planted unregistered format"
        );

        let moved_source = source.replacen(
            "name: \"fln.bench.bundle\"",
            "name: \"fln.bench.bundle-moved\"",
            1,
        );
        let moved = declared_schema_pairs(&moved_source)?;
        assert!(
            registered.iter().any(|pair| !moved.contains(pair)),
            "a moved declaration must leave a detectable stale row"
        );
        assert!(
            moved.iter().any(|pair| !registered.contains(pair)),
            "a moved declaration must also be detectably unregistered"
        );

        // The planted mutant must name the version the source ACTUALLY carries,
        // or `replacen` matches nothing, the "mutated" source equals the
        // original, and this assertion fails for the wrong reason on every
        // legitimate version bump. Moved 1->2 to 2->3 with the odwj bump,
        // then 3->4 to 4->5 with fln-odva's typed thermal-zone count.
        let version_drift_source = source.replacen(
            "pub const BENCHMARK_EVIDENCE_VERSION: u16 = 4;",
            "pub const BENCHMARK_EVIDENCE_VERSION: u16 = 5;",
            1,
        );
        assert_ne!(
            version_drift_source, source,
            "the planted version mutant matched nothing; it has drifted from the \
             constant it is supposed to perturb"
        );
        let version_drift = declared_schema_pairs(&version_drift_source)?;
        assert_ne!(
            version_drift, registered,
            "a declaration-side version bump must not agree with stale registry rows"
        );
        Ok(())
    }

    #[test]
    fn every_registered_shape_refuses_unknown_headers_before_reading_body() -> Result<(), String> {
        let bundle = fixture_bundle()?;
        for row in BENCHMARK_SCHEMA_REGISTRY {
            let bytes = fixture_schema_bytes(row.kind, &bundle)?;
            assert_eq!(
                validate_benchmark_schema_bytes(&bytes),
                Ok(row.kind),
                "{} live shape must decode under its exact registration",
                row.id.name
            );

            let version_offset = schema_header_version_offset(&row);
            let mut unknown_version = bytes;
            unknown_version
                .get_mut(version_offset..version_offset + std::mem::size_of::<u16>())
                .ok_or_else(|| format!("{} fixture has no schema version", row.id.name))?
                .copy_from_slice(&row.id.version.saturating_add(1).to_le_bytes());
            unknown_version.truncate(version_offset + std::mem::size_of::<u16>());
            let refusal = validate_benchmark_schema_bytes(&unknown_version);
            assert_eq!(
                refusal,
                Err(BenchmarkSchemaValidationError::Refused(
                    BenchmarkSchemaRefusal::UnsupportedVersion {
                        name: row.id.name,
                        seen: row.id.version.saturating_add(1),
                        supported: row.id.version,
                    }
                )),
                "{} must refuse an unknown version before trying to read the absent body",
                row.id.name
            );
            assert_eq!(
                refusal.err().and_then(|error| match error {
                    BenchmarkSchemaValidationError::Refused(refusal) => {
                        Some(refusal.finding_code())
                    }
                    BenchmarkSchemaValidationError::Decode(_) => None,
                }),
                Some("FLN-BENCH-SCHEMA-002")
            );
        }

        let row = BENCHMARK_SCHEMA_REGISTRY
            .first()
            .ok_or_else(|| "benchmark schema registry is empty".to_string())?;
        let mut unknown_name = fixture_schema_bytes(row.kind, &bundle)?;
        let first_name_byte = unknown_name
            .get_mut(std::mem::size_of::<u64>())
            .ok_or_else(|| "host schema fixture has no name byte".to_string())?;
        *first_name_byte = b'x';
        let header_end = schema_header_version_offset(row) + std::mem::size_of::<u16>();
        unknown_name.truncate(header_end);
        assert!(matches!(
            validate_benchmark_schema_bytes(&unknown_name),
            Err(BenchmarkSchemaValidationError::Refused(
                BenchmarkSchemaRefusal::UnknownName { .. }
            ))
        ));
        Ok(())
    }

    #[test]
    fn version_bearing_shapes_refuse_unknown_inner_versions_before_later_fields()
    -> Result<(), String> {
        let bundle = fixture_bundle()?;
        for (kind, expected_reason) in [
            (
                BenchmarkSchemaKind::HostProfile,
                "unsupported benchmark host-profile version",
            ),
            (
                BenchmarkSchemaKind::Workload,
                "unsupported benchmark workload version",
            ),
            (
                BenchmarkSchemaKind::Telemetry,
                "unsupported benchmark telemetry version",
            ),
            (
                BenchmarkSchemaKind::Bundle,
                "unsupported benchmark bundle version",
            ),
        ] {
            let row = BENCHMARK_SCHEMA_REGISTRY
                .iter()
                .find(|row| row.kind == kind)
                .ok_or_else(|| format!("registry has no {kind:?} row"))?;
            let mut bytes = fixture_schema_bytes(kind, &bundle)?;
            let body_offset = schema_header_version_offset(row) + std::mem::size_of::<u16>();
            bytes
                .get_mut(body_offset..body_offset + std::mem::size_of::<u16>())
                .ok_or_else(|| format!("{} fixture has no inner version", row.id.name))?
                .copy_from_slice(&BENCHMARK_EVIDENCE_VERSION.saturating_add(1).to_le_bytes());
            bytes.truncate(body_offset + std::mem::size_of::<u16>());
            assert_eq!(
                validate_benchmark_schema_bytes(&bytes),
                Err(BenchmarkSchemaValidationError::Decode(CanonError {
                    at: 0,
                    what: expected_reason,
                })),
                "{} must reject its inner version before reading the truncated body",
                row.id.name
            );
        }
        Ok(())
    }

    #[test]
    fn benchmark_host_profile_model() {
        let host = fixture_host("fixture-cpu");
        let policy = HostQualificationPolicy {
            require_physical_topology: true,
            require_power_governor: true,
            require_thermal_sensors: true,
            require_exclusive_cores: true,
            require_stable_frequency: true,
            require_thermal_stability: true,
            allow_virtualization: false,
            allow_translation: false,
            allow_profiler: false,
        };
        assert_eq!(validate_host(&host, policy), Ok(()));
        assert_eq!(host.root(), host.root());

        let mut other = host.clone();
        other.cpu_sku = text("other-cpu");
        assert_ne!(
            host.root(),
            other.root(),
            "a CPU substitution must change host identity"
        );

        let mut different_thermal_population = host.clone();
        different_thermal_population.thermal_sensor_count = number(1);
        assert_ne!(
            host.root(),
            different_thermal_population.root(),
            "the typed thermal-zone population must participate in host identity"
        );

        let mut missing = host.clone();
        missing.cpu_sku = Captured::unavailable(CaptureSource::Procfs, "model name absent");
        assert_eq!(
            validate_host(&missing, policy),
            Err(BenchmarkRefusal::HostNotQualified { check: "cpu-sku" })
        );

        let mut unordered = host;
        unordered.enabled_features.swap(0, 1);
        assert_eq!(
            validate_host(&unordered, policy),
            Err(BenchmarkRefusal::MalformedHostProfile {
                field: "features-or-counters"
            })
        );
    }

    #[test]
    fn cache_state_lattice() {
        let conditions = [
            CacheCondition::Cold,
            CacheCondition::Warm,
            CacheCondition::NotApplicable,
        ];
        let mut roots = BTreeSet::new();
        for filesystem in conditions {
            for page_cache in conditions {
                for reference_artifacts in conditions {
                    for candidate_artifacts in conditions {
                        for build_cache in conditions {
                            for imported_modules in conditions {
                                for daemon in conditions {
                                    let mut workload = fixture_workload(1);
                                    workload.cache_state = CacheState {
                                        filesystem,
                                        page_cache,
                                        reference_artifacts,
                                        candidate_artifacts,
                                        build_cache,
                                        imported_modules,
                                        daemon,
                                    };
                                    assert!(
                                        roots.insert(workload.root()),
                                        "two distinct cache-axis states collapsed"
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
        assert_eq!(roots.len(), 3_usize.pow(7));
    }

    #[test]
    fn statistical_reference_vectors() {
        let host = fixture_host("fixture-cpu");
        let workload = fixture_workload(5);
        let mut attempts = [10_u64, 20, 30, 40, 50]
            .into_iter()
            .enumerate()
            .map(|(ordinal, measurement)| {
                attempt(
                    ordinal as u32,
                    host.root(),
                    workload.root(),
                    AttemptStatus::Valid { measurement },
                )
            })
            .collect::<Vec<_>>();
        attempts.push(attempt(
            5,
            host.root(),
            workload.root(),
            AttemptStatus::InvalidHost {
                reason: "thermal".to_string(),
            },
        ));
        let summary = regenerate_summary(&workload, &attempts);
        assert_eq!(
            summary,
            Ok(StatisticalSummary {
                valid_samples: 5,
                excluded_attempts: 1,
                minimum: 10,
                maximum: 50,
                median: ExactRatio {
                    numerator: 30,
                    denominator: 1,
                },
                p95: 50,
                p99: 50,
                mean: ExactRatio {
                    numerator: 30,
                    denominator: 1,
                },
                sample_variance: ExactRatio {
                    numerator: 250,
                    denominator: 1,
                },
                median_absolute_deviation: ExactRatio {
                    numerator: 10,
                    denominator: 1,
                },
                relative_mad_basis_points: 3_334,
                median_confidence_low: 10,
                median_confidence_high: 50,
                repeatable: true,
            })
        );

        let even = [1_u64, 2, 8, 9]
            .into_iter()
            .enumerate()
            .map(|(ordinal, measurement)| {
                attempt(
                    ordinal as u32,
                    host.root(),
                    workload.root(),
                    AttemptStatus::Valid { measurement },
                )
            })
            .collect::<Vec<_>>();
        let even_summary = regenerate_summary(&workload, &even);
        assert_eq!(
            even_summary.as_ref().map(|summary| &summary.median),
            Ok(&ExactRatio {
                numerator: 5,
                denominator: 1,
            })
        );
    }

    #[test]
    fn benchmark_attempt_state_machine() -> Result<(), String> {
        let bundle = fixture_bundle()?;
        let validated = validate_bundle(&bundle);
        assert!(validated.is_ok());
        assert_eq!(
            bundle
                .summary
                .as_ref()
                .map(|summary| summary.excluded_attempts),
            Some(6),
            "every non-valid attempt state stays raw and excluded"
        );

        let mut duplicate = bundle.clone();
        let first_id = duplicate
            .attempts
            .first()
            .map(|attempt| attempt.attempt_id.clone())
            .ok_or_else(|| "fixture has no first attempt".to_string())?;
        duplicate
            .attempts
            .get_mut(1)
            .ok_or_else(|| "fixture has no second attempt".to_string())?
            .attempt_id = first_id;
        assert!(matches!(
            validate_bundle(&duplicate),
            Err(BenchmarkRefusal::DuplicateAttemptId { .. })
        ));

        let mut dropped = bundle.clone();
        dropped.attempts.remove(1);
        assert!(matches!(
            validate_bundle(&dropped),
            Err(BenchmarkRefusal::AttemptsStartedMismatch { .. })
        ));

        let mut cache_conflated = bundle.clone();
        cache_conflated
            .attempts
            .first_mut()
            .ok_or_else(|| "fixture has no first attempt".to_string())?
            .cache_state
            .daemon = CacheCondition::Warm;
        assert!(matches!(
            validate_bundle(&cache_conflated),
            Err(BenchmarkRefusal::CacheStateMismatch { .. })
        ));

        let mut profiled = bundle.clone();
        profiled
            .attempts
            .first_mut()
            .ok_or_else(|| "fixture has no first attempt".to_string())?
            .profiler = ProfilerState::Enabled;
        assert!(matches!(
            validate_bundle(&profiled),
            Err(BenchmarkRefusal::ProfilerContamination { .. })
        ));

        let host = fixture_host("fixture-cpu");
        let workload = fixture_workload(2);
        let attempts = fixture_attempts(&host, &workload);
        let telemetry = fixture_telemetry(&attempts);
        assert_eq!(
            assemble_bundle("overrun", host, workload, attempts, telemetry),
            Err(BenchmarkRefusal::SamplePlanOverrun {
                valid: 3,
                allowed: 2
            })
        );
        Ok(())
    }

    #[test]
    fn benchmark_bundle_validator() -> Result<(), String> {
        let bundle = fixture_bundle()?;

        let mut missing_host = bundle.clone();
        missing_host.host_profile = None;
        let refusal = validate_bundle(&missing_host);
        assert_eq!(refusal, Err(BenchmarkRefusal::MissingHostProfile));
        assert_eq!(
            refusal.err().map(|error| error.finding_code()),
            Some("FLN-BENCH-002")
        );

        let mut cross_host = bundle.clone();
        cross_host
            .attempts
            .get_mut(4)
            .ok_or_else(|| "fixture has no fifth attempt".to_string())?
            .host_root = fixture_host("second-host").root();
        let refusal = validate_bundle(&cross_host);
        assert!(matches!(
            refusal,
            Err(BenchmarkRefusal::HostProfileSubstitution { ref attempt_id })
                if attempt_id == "attempt-4"
        ));
        assert_eq!(
            refusal.err().map(|error| error.finding_code()),
            Some("FLN-BENCH-014")
        );

        let mut stopping_changed = bundle.clone();
        stopping_changed
            .workload
            .as_mut()
            .ok_or_else(|| "fixture lost its workload".to_string())?
            .sample_plan = SamplePlan::FixedValidSamples { samples: 2 };
        assert!(matches!(
            validate_bundle(&stopping_changed),
            Err(BenchmarkRefusal::WorkloadSubstitution { .. })
        ));

        let mut stale = bundle.clone();
        if let Some(summary) = &mut stale.summary {
            summary.p95 = summary.p95.saturating_add(1);
        }
        assert_eq!(validate_bundle(&stale), Err(BenchmarkRefusal::StaleSummary));

        let mut promoted = bundle.clone();
        promoted.benchmark_claim.state = ClaimState::Proven;
        assert_eq!(
            validate_bundle(&promoted),
            Err(BenchmarkRefusal::ClaimAuthorityMismatch {
                class: ClaimClass::Benchmark,
                state: ClaimState::Proven,
            })
        );

        let mut partial = bundle.clone();
        partial.claimed_roots = None;
        assert_eq!(
            validate_bundle(&partial),
            Err(BenchmarkRefusal::MissingRootChain)
        );

        let mut root_tamper = bundle.clone();
        if let Some(roots) = &mut root_tamper.claimed_roots {
            roots.statistics = digest("forged-statistics");
        }
        assert!(matches!(
            validate_bundle(&root_tamper),
            Err(BenchmarkRefusal::RootMismatch {
                component: RootComponent::Statistics,
                ..
            })
        ));

        let bytes = bundle.to_canonical_bytes();
        let decoded = validate_bundle_bytes(&bytes)
            .map_err(|error| format!("fixture byte validation failed: {error:?}"))?;
        assert_eq!(
            decoded.roots(),
            bundle
                .claimed_roots
                .ok_or_else(|| "validated fixture lost its root chain".to_string())?
        );

        let mut telemetry_changed = bundle.clone();
        let host = telemetry_changed
            .host_profile
            .take()
            .ok_or_else(|| "validated fixture lost its host profile".to_string())?;
        let workload = telemetry_changed
            .workload
            .take()
            .ok_or_else(|| "validated fixture lost its workload".to_string())?;
        let attempts = telemetry_changed.attempts.clone();
        let mut telemetry = telemetry_changed
            .telemetry
            .take()
            .ok_or_else(|| "validated fixture lost its telemetry".to_string())?;
        telemetry
            .attempts
            .first_mut()
            .ok_or_else(|| "validated fixture telemetry has no first attempt".to_string())?
            .process_id = 7_777;
        let changed = assemble_bundle("fixture-run", host, workload, attempts, telemetry)
            .map_err(|error| format!("telemetry-only rebuild failed: {error:?}"))?;
        let original_roots = bundle
            .claimed_roots
            .ok_or_else(|| "validated fixture lost its root chain".to_string())?;
        let changed_roots = changed
            .claimed_roots
            .ok_or_else(|| "rebuilt fixture lost its root chain".to_string())?;
        let changed_validated = validate_bundle(&changed)
            .map_err(|error| format!("changed fixture validation failed: {error:?}"))?;
        assert_eq!(original_roots.semantic, changed_roots.semantic);
        assert_ne!(original_roots.telemetry, changed_roots.telemetry);
        assert_ne!(original_roots.bundle, changed_roots.bundle);
        assert_eq!(
            decoded.semantic_ndjson(),
            changed_validated.semantic_ndjson()
        );
        assert_ne!(
            decoded.telemetry_ndjson(),
            changed_validated.telemetry_ndjson()
        );
        let semantic = decoded.semantic_ndjson();
        assert!(semantic.contains("\"status\":\"resource-refused\""));
        assert!(semantic.contains("\"resource\":\"time\""));
        assert!(semantic.contains("\"status\":\"target-failed\""));
        assert!(semantic.contains("\"status\":\"infrastructure-fault\""));
        Ok(())
    }

    #[test]
    fn benchmark_core_no_mock_e2e() -> Result<(), String> {
        let host = HostProfile::capture_local(LocalBuildIdentity {
            toolchain_manifest: include_bytes!("../../../rust-toolchain.toml"),
            target_triple: std::env::consts::ARCH,
            build_profile: if cfg!(debug_assertions) {
                "debug"
            } else {
                "release"
            },
            enabled_features: &[],
        })
        .map_err(|error| format!("real local host capture failed: {error}"))?;
        let mut workload = fixture_workload(3);
        workload.workload_id = "real-local-smoke".to_string();
        workload.host_policy = permissive_policy();
        workload.resource_bounds.max_measurement = u64::MAX;
        workload.resource_bounds.max_elapsed_ns_per_attempt = u64::MAX;
        let host_root = host.root();
        let workload_root = workload.root();

        let mut measurements = Vec::new();
        for seed in [3_u64, 5, 7] {
            let start = Instant::now();
            let mut value = seed;
            for index in 0..10_000_u64 {
                value = black_box(value.rotate_left(7) ^ index);
            }
            black_box(value);
            measurements.push(
                u64::try_from(start.elapsed().as_nanos())
                    .unwrap_or(u64::MAX)
                    .max(1),
            );
        }
        let mut measurements = measurements.into_iter();
        let first = measurements
            .next()
            .ok_or_else(|| "real measurement campaign produced no first sample".to_string())?;
        let second = measurements
            .next()
            .ok_or_else(|| "real measurement campaign produced no second sample".to_string())?;
        let third = measurements
            .next()
            .ok_or_else(|| "real measurement campaign produced no third sample".to_string())?;
        let statuses = vec![
            AttemptStatus::Valid { measurement: first },
            AttemptStatus::InvalidHost {
                reason: "planted host-quality failure".to_string(),
            },
            AttemptStatus::Cancelled {
                reason: "planted cancellation".to_string(),
            },
            AttemptStatus::InsufficientSample {
                valid_observed: 1,
                valid_required: 3,
            },
            AttemptStatus::Valid {
                measurement: second,
            },
            AttemptStatus::Valid { measurement: third },
        ];
        let attempts = statuses
            .into_iter()
            .enumerate()
            .map(|(ordinal, status)| {
                u32::try_from(ordinal)
                    .map(|ordinal| attempt(ordinal, host_root, workload_root, status))
                    .map_err(|_| "attempt ordinal exceeds u32".to_string())
            })
            .collect::<Result<Vec<_>, _>>()?;
        let cwd = std::env::current_dir()
            .map(|path| path.display().to_string())
            .unwrap_or_else(|error| format!("unavailable:{error}"));
        let telemetry = BenchmarkTelemetry {
            schema_version: BENCHMARK_EVIDENCE_VERSION,
            attempts: attempts
                .iter()
                .map(|attempt| AttemptTelemetry {
                    attempt_id: attempt.attempt_id.clone(),
                    wall_clock_start_ns: 0,
                    elapsed_ns: match attempt.status {
                        AttemptStatus::Valid { measurement } => measurement,
                        _ => 0,
                    },
                    process_id: std::process::id(),
                    absolute_working_directory: cwd.clone(),
                    counters: Vec::new(),
                })
                .collect(),
        };
        let bundle = assemble_bundle("real-local-smoke-run", host, workload, attempts, telemetry)
            .map_err(|error| format!("real bundle assembly failed: {error:?}"))?;
        let validated = validate_bundle_bytes(&bundle.to_canonical_bytes())
            .map_err(|error| format!("independent byte validation failed: {error:?}"))?;
        assert_eq!(
            validated.candidate().attempts.len(),
            6,
            "the invalid/cancelled/insufficient attempts must remain in raw evidence"
        );

        let mut corrupted = bundle.clone();
        let first_attempt = corrupted
            .attempts
            .first_mut()
            .ok_or_else(|| "real bundle has no first attempt".to_string())?;
        if let AttemptStatus::Valid { measurement } = &mut first_attempt.status {
            *measurement = measurement.saturating_add(1);
        }
        assert_eq!(
            validate_bundle(&corrupted),
            Err(BenchmarkRefusal::StaleSummary)
        );
        assert!(validate_bundle(&bundle).is_ok(), "clean retry must recover");

        let semantic = validated.semantic_ndjson();
        let telemetry = validated.telemetry_ndjson();
        assert!(!semantic.contains(&cwd));
        assert!(!semantic.contains("\"process_id\""));
        assert!(semantic.contains("\"publication_authority\":\"validated\""));
        assert!(semantic.contains("\"cache_filesystem\""));
        assert!(semantic.contains("\"quantile_method\":\"nearest-rank-v1\""));
        assert!(semantic.contains("\"reason\":\"planted host-quality failure\""));
        assert!(telemetry.contains(&cwd));
        assert!(telemetry.contains("\"process_id\""));
        assert!(telemetry.contains("\"bundle_root\""));
        Ok(())
    }
}
