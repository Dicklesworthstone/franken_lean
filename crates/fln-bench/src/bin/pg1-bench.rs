//! Live side-by-side PG-1 benchmark runner wired to the `fln-bench` evidence
//! substrate (plan §19, RULE 0.5).
//!
//! Runs BOTH the pinned Reference `lean` binary and the FrankenLean candidate
//! binary live in the same invocation (alternating trial order to cancel host
//! drift), binds both executable digests and all input bytes into canonical
//! `WorkloadManifest`s, validates both bundles through `fln_bench::validate_bundle`,
//! and fails closed with `BlockedHostQualification` when the host does not meet
//! strict PG-1 isolation unless `--allow-shared-host` is explicitly supplied for
//! non-PG1 development measurement.
#![forbid(unsafe_code)]

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, Stdio};
use std::time::{Instant, SystemTime, UNIX_EPOCH};

use fln_bench::{
    AttemptRecord, AttemptStatus, AttemptTelemetry, BENCHMARK_EVIDENCE_VERSION, BenchmarkTelemetry,
    CacheCondition, CacheState, ConfidenceAlgorithm, CounterReading, HostProfile,
    HostQualificationPolicy, LocalBuildIdentity, MeasurementUnit, OracleToolIdentity,
    OutlierPolicy, ProfilerState, QuantileAlgorithm, ResourceBounds, SamplePlan, WorkloadKind,
    WorkloadManifest, assemble_bundle, qualify_host, validate_bundle,
};
use fln_hash::domain::{Digest, Domain, hash};

struct Config {
    workload_id: String,
    workload_kind: WorkloadKind,
    reference: PathBuf,
    reference_args: Vec<String>,
    candidate: PathBuf,
    candidate_args: Vec<String>,
    sources: Vec<PathBuf>,
    warmup: u32,
    samples: u32,
    allow_shared_host: bool,
    out_dir: Option<PathBuf>,
}

fn usage() -> &'static str {
    "Usage: pg1-bench --reference <lean-bin> --candidate <fln-or-lean-bin> --source <file.lean>...\n\
     Options:\n\
       --workload-id <id>          Stable workload identifier (default: pg1-source-elaboration)\n\
       --kind <elaboration|kernel-recheck|module-import|corpus-build>\n\
       --reference-arg <arg>       Extra argument passed before sources to reference binary\n\
       --candidate-arg <arg>       Extra argument passed before sources to candidate binary\n\
       --warmup <N>                Interleaved warmup pairs (default: 1)\n\
       --samples <N>               Interleaved valid sample pairs (default: 5)\n\
       --allow-shared-host         Permit non-PG1 shared-host measurement after printing strict qualification verdict\n\
       --out-dir <dir>             Write validated semantic and telemetry NDJSON bundles\n"
}

fn parse_args() -> Result<Config, String> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut workload_id = "pg1-source-elaboration".to_owned();
    let mut workload_kind = WorkloadKind::Elaboration;
    let mut reference: Option<PathBuf> = None;
    let mut reference_args = Vec::new();
    let mut candidate: Option<PathBuf> = None;
    let mut candidate_args = Vec::new();
    let mut sources = Vec::new();
    let mut warmup = 1_u32;
    let mut samples = 5_u32;
    let mut allow_shared_host = false;
    let mut out_dir = None;

    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "-h" | "--help" => return Err(usage().to_owned()),
            "--workload-id" => {
                i += 1;
                workload_id = args.get(i).ok_or("--workload-id requires a value")?.clone();
            }
            "--kind" => {
                i += 1;
                let raw = args.get(i).ok_or("--kind requires a value")?;
                workload_kind = match raw.as_str() {
                    "elaboration" => WorkloadKind::Elaboration,
                    "kernel-recheck" => WorkloadKind::KernelRecheck,
                    "module-import" => WorkloadKind::ModuleImport,
                    "corpus-build" => WorkloadKind::CorpusBuild,
                    other => return Err(format!("unsupported --kind `{other}`")),
                };
            }
            "--reference" => {
                i += 1;
                reference = Some(PathBuf::from(
                    args.get(i).ok_or("--reference requires a path")?,
                ));
            }
            "--reference-arg" => {
                i += 1;
                reference_args.push(
                    args.get(i)
                        .ok_or("--reference-arg requires a value")?
                        .clone(),
                );
            }
            "--candidate" => {
                i += 1;
                candidate = Some(PathBuf::from(
                    args.get(i).ok_or("--candidate requires a path")?,
                ));
            }
            "--candidate-arg" => {
                i += 1;
                candidate_args.push(
                    args.get(i)
                        .ok_or("--candidate-arg requires a value")?
                        .clone(),
                );
            }
            "--source" => {
                i += 1;
                sources.push(PathBuf::from(
                    args.get(i).ok_or("--source requires a path")?,
                ));
            }
            "--warmup" => {
                i += 1;
                warmup = args
                    .get(i)
                    .ok_or("--warmup requires a value")?
                    .parse::<u32>()
                    .map_err(|e| format!("bad --warmup: {e}"))?;
            }
            "--samples" => {
                i += 1;
                samples = args
                    .get(i)
                    .ok_or("--samples requires a value")?
                    .parse::<u32>()
                    .map_err(|e| format!("bad --samples: {e}"))?;
            }
            "--allow-shared-host" => allow_shared_host = true,
            "--out-dir" => {
                i += 1;
                out_dir = Some(PathBuf::from(
                    args.get(i).ok_or("--out-dir requires a path")?,
                ));
            }
            other => return Err(format!("unknown argument `{other}`\n{}", usage())),
        }
        i += 1;
    }

    let reference = reference.ok_or_else(|| format!("--reference is required\n{}", usage()))?;
    let candidate = candidate.ok_or_else(|| format!("--candidate is required\n{}", usage()))?;
    if sources.is_empty() {
        return Err(format!("at least one --source is required\n{}", usage()));
    }
    if samples == 0 {
        return Err("--samples must be >= 1".to_owned());
    }
    Ok(Config {
        workload_id,
        workload_kind,
        reference,
        reference_args,
        candidate,
        candidate_args,
        sources,
        warmup,
        samples,
        allow_shared_host,
        out_dir,
    })
}

fn strict_pg1_host_policy() -> HostQualificationPolicy {
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

fn shared_dev_host_policy() -> HostQualificationPolicy {
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

fn hash_file(path: &Path) -> Result<Digest, String> {
    let bytes = fs::read(path).map_err(|e| format!("failed to read `{}`: {e}", path.display()))?;
    Ok(hash(Domain::OperationalMeta, &bytes))
}

fn corpus_root(sources: &[PathBuf]) -> Result<Digest, String> {
    let mut corpus_bytes = Vec::new();
    for path in sources {
        let content =
            fs::read(path).map_err(|e| format!("failed to read `{}`: {e}", path.display()))?;
        corpus_bytes.extend_from_slice(&(content.len() as u64).to_le_bytes());
        corpus_bytes.extend_from_slice(&content);
    }
    Ok(hash(Domain::OperationalMeta, &corpus_bytes))
}

fn input_order_root(sources: &[PathBuf], extra_args: &[String]) -> Digest {
    let mut order_bytes = Vec::new();
    order_bytes.extend_from_slice(&(extra_args.len() as u64).to_le_bytes());
    for arg in extra_args {
        order_bytes.extend_from_slice(&(arg.len() as u64).to_le_bytes());
        order_bytes.extend_from_slice(arg.as_bytes());
    }
    order_bytes.extend_from_slice(&(sources.len() as u64).to_le_bytes());
    for path in sources {
        let display = path.to_string_lossy();
        order_bytes.extend_from_slice(&(display.len() as u64).to_le_bytes());
        order_bytes.extend_from_slice(display.as_bytes());
    }
    hash(Domain::OperationalMeta, &order_bytes)
}

fn now_unix_ns() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |d| u64::try_from(d.as_nanos()).unwrap_or(u64::MAX))
}

struct ProcessTarget<'a> {
    binary: &'a Path,
    extra_args: &'a [String],
    sources: &'a [PathBuf],
    cwd: &'a str,
    host_root: Digest,
    workload_root: Digest,
    cache_state: CacheState,
}

fn run_one_process(
    target: &ProcessTarget<'_>,
    attempt_id: String,
    ordinal: u32,
) -> (AttemptRecord, AttemptTelemetry) {
    let wall_clock_start_ns = now_unix_ns();
    let started = Instant::now();
    let spawn = Command::new(target.binary)
        .args(target.extra_args)
        .args(target.sources)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn();
    let (pid, elapsed_ns, status) = match spawn {
        Ok(mut child) => {
            let pid = child.id();
            match child.wait() {
                Ok(exit) => {
                    let elapsed_ns = u64::try_from(started.elapsed().as_nanos())
                        .unwrap_or(u64::MAX)
                        .max(1);
                    if exit.success() {
                        (
                            pid,
                            elapsed_ns,
                            AttemptStatus::Valid {
                                measurement: elapsed_ns,
                            },
                        )
                    } else {
                        (
                            pid,
                            elapsed_ns,
                            AttemptStatus::TargetFailed {
                                exit_code: exit.code().unwrap_or(-1),
                            },
                        )
                    }
                }
                Err(_) => (
                    pid,
                    u64::try_from(started.elapsed().as_nanos())
                        .unwrap_or(u64::MAX)
                        .max(1),
                    AttemptStatus::InfrastructureFault {
                        code: "wait-failed".to_owned(),
                    },
                ),
            }
        }
        Err(_) => (
            0,
            u64::try_from(started.elapsed().as_nanos())
                .unwrap_or(u64::MAX)
                .max(1),
            AttemptStatus::InfrastructureFault {
                code: "spawn-failed".to_owned(),
            },
        ),
    };
    let record = AttemptRecord {
        attempt_id: attempt_id.clone(),
        ordinal,
        host_root: target.host_root,
        workload_root: target.workload_root,
        cache_state: target.cache_state,
        profiler: ProfilerState::Disabled,
        status,
    };
    let telemetry = AttemptTelemetry {
        attempt_id,
        wall_clock_start_ns,
        elapsed_ns,
        process_id: pid,
        absolute_working_directory: target.cwd.to_owned(),
        counters: vec![CounterReading {
            name: "wall_ns".to_owned(),
            value: elapsed_ns,
        }],
    };
    (record, telemetry)
}

struct ManifestSpec {
    workload_id: String,
    workload_kind: WorkloadKind,
    oracle_tools: Vec<OracleToolIdentity>,
    corpus_root: Digest,
    input_order_root: Digest,
    warmup_iterations: u32,
    samples: u32,
    cache_state: CacheState,
    host_policy: HostQualificationPolicy,
}

fn manifest(spec: ManifestSpec) -> WorkloadManifest {
    WorkloadManifest {
        schema_version: BENCHMARK_EVIDENCE_VERSION,
        workload_id: spec.workload_id,
        workload_kind: spec.workload_kind,
        oracle_tools: spec.oracle_tools,
        corpus_root: spec.corpus_root,
        input_order_root: spec.input_order_root,
        warmup_iterations: spec.warmup_iterations,
        sample_plan: SamplePlan::FixedValidSamples {
            samples: spec.samples,
        },
        quantile_algorithm: QuantileAlgorithm::NearestRankV1,
        confidence_algorithm: ConfidenceAlgorithm::DistributionFreeMedian95V1,
        outlier_policy: OutlierPolicy::RetainAllV1,
        variance_threshold_basis_points: 10_000,
        cache_state: spec.cache_state,
        unit: MeasurementUnit::Nanoseconds,
        host_policy: spec.host_policy,
        resource_bounds: ResourceBounds {
            max_attempts: spec.samples.saturating_add(8),
            max_measurement: 600_000_000_000,
            max_elapsed_ns_per_attempt: 600_000_000_000,
        },
    }
}

fn ratio_f64(ratio: &fln_bench::ExactRatio) -> f64 {
    (ratio.numerator as f64) / (ratio.denominator as f64)
}

fn run() -> Result<ExitCode, String> {
    let config = parse_args()?;
    let cwd = std::env::current_dir()
        .map_err(|e| format!("failed to read cwd: {e}"))?
        .to_string_lossy()
        .into_owned();

    let host = HostProfile::capture_local(LocalBuildIdentity {
        toolchain_manifest: b"franken_lean::pg1-bench/1",
        target_triple: std::env::consts::ARCH,
        build_profile: if cfg!(debug_assertions) {
            "debug"
        } else {
            "release"
        },
        enabled_features: &[],
    })
    .map_err(|e| format!("host capture failed: {e:?}"))?;

    let strict_verdict = qualify_host(&host, strict_pg1_host_policy());
    let host_qualified_pg1 = match &strict_verdict {
        Ok(()) => {
            println!(
                "HOST_QUALIFICATION strict_pg1=QUALIFIED host_root={}",
                host.root()
            );
            true
        }
        Err(blocked) => {
            eprintln!(
                "HOST_QUALIFICATION strict_pg1=BLOCKED host_root={} failing_checks={:?}",
                blocked.host_root, blocked.failing_checks
            );
            if !config.allow_shared_host {
                print!("{}", blocked.ndjson());
                return Ok(ExitCode::from(2));
            }
            eprintln!(
                "NOTE: --allow-shared-host enabled; output is SHARED_HOST_NON_PG1 development telemetry, not a PG-1 qualification claim."
            );
            false
        }
    };

    let host_policy = if host_qualified_pg1 {
        strict_pg1_host_policy()
    } else {
        shared_dev_host_policy()
    };

    let ref_hash = hash_file(&config.reference)?;
    let cand_hash = hash_file(&config.candidate)?;
    let corpus_root = corpus_root(&config.sources)?;
    let ref_order_root = input_order_root(&config.sources, &config.reference_args);
    let cand_order_root = input_order_root(&config.sources, &config.candidate_args);

    let mut tools = vec![
        OracleToolIdentity {
            name: "candidate_fln".to_owned(),
            binary_hash: cand_hash,
        },
        OracleToolIdentity {
            name: "reference_lean".to_owned(),
            binary_hash: ref_hash,
        },
    ];
    tools.sort();

    let warmed = if config.warmup > 0 {
        CacheCondition::Warm
    } else {
        CacheCondition::Cold
    };
    let ref_cache = CacheState {
        filesystem: warmed,
        page_cache: warmed,
        reference_artifacts: warmed,
        candidate_artifacts: CacheCondition::NotApplicable,
        build_cache: CacheCondition::Cold,
        imported_modules: CacheCondition::Cold,
        daemon: CacheCondition::Cold,
    };
    let cand_cache = CacheState {
        filesystem: warmed,
        page_cache: warmed,
        reference_artifacts: CacheCondition::NotApplicable,
        candidate_artifacts: warmed,
        build_cache: CacheCondition::Cold,
        imported_modules: CacheCondition::Cold,
        daemon: CacheCondition::Cold,
    };

    let qualification_tag = if host_qualified_pg1 {
        "pg1"
    } else {
        "shared-host-non-pg1"
    };
    let ref_workload = manifest(ManifestSpec {
        workload_id: format!("{}:reference:{qualification_tag}", config.workload_id),
        workload_kind: config.workload_kind,
        oracle_tools: tools.clone(),
        corpus_root,
        input_order_root: ref_order_root,
        warmup_iterations: config.warmup,
        samples: config.samples,
        cache_state: ref_cache,
        host_policy,
    });
    let cand_workload = manifest(ManifestSpec {
        workload_id: format!("{}:candidate:{qualification_tag}", config.workload_id),
        workload_kind: config.workload_kind,
        oracle_tools: tools,
        corpus_root,
        input_order_root: cand_order_root,
        warmup_iterations: config.warmup,
        samples: config.samples,
        cache_state: cand_cache,
        host_policy,
    });

    // Interleaved warmup pairs (not included in timed attempts). Fail fast if
    // either binary rejects the workload so misconfigured flags do not masquerade
    // as timed samples.
    for w in 0..config.warmup {
        let ref_status = Command::new(&config.reference)
            .args(&config.reference_args)
            .args(&config.sources)
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .map_err(|e| format!("warmup reference #{w} failed to spawn: {e}"))?;
        if !ref_status.success() {
            return Err(format!(
                "warmup reference #{w} exited non-zero ({ref_status})"
            ));
        }
        let cand_status = Command::new(&config.candidate)
            .args(&config.candidate_args)
            .args(&config.sources)
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .map_err(|e| format!("warmup candidate #{w} failed to spawn: {e}"))?;
        if !cand_status.success() {
            return Err(format!(
                "warmup candidate #{w} exited non-zero ({cand_status})"
            ));
        }
    }

    let host_root = host.root();
    let ref_target = ProcessTarget {
        binary: &config.reference,
        extra_args: &config.reference_args,
        sources: &config.sources,
        cwd: &cwd,
        host_root,
        workload_root: ref_workload.root(),
        cache_state: ref_cache,
    };
    let cand_target = ProcessTarget {
        binary: &config.candidate,
        extra_args: &config.candidate_args,
        sources: &config.sources,
        cwd: &cwd,
        host_root,
        workload_root: cand_workload.root(),
        cache_state: cand_cache,
    };
    let mut ref_attempts = Vec::with_capacity(config.samples as usize);
    let mut ref_telemetry = Vec::with_capacity(config.samples as usize);
    let mut cand_attempts = Vec::with_capacity(config.samples as usize);
    let mut cand_telemetry = Vec::with_capacity(config.samples as usize);

    for ordinal in 0..config.samples {
        let ref_id = format!("ref-{ordinal}");
        let cand_id = format!("cand-{ordinal}");
        if ordinal % 2 == 0 {
            let (r_rec, r_tel) = run_one_process(&ref_target, ref_id, ordinal);
            let (c_rec, c_tel) = run_one_process(&cand_target, cand_id, ordinal);
            ref_attempts.push(r_rec);
            ref_telemetry.push(r_tel);
            cand_attempts.push(c_rec);
            cand_telemetry.push(c_tel);
        } else {
            let (c_rec, c_tel) = run_one_process(&cand_target, cand_id, ordinal);
            let (r_rec, r_tel) = run_one_process(&ref_target, ref_id, ordinal);
            cand_attempts.push(c_rec);
            cand_telemetry.push(c_tel);
            ref_attempts.push(r_rec);
            ref_telemetry.push(r_tel);
        }
    }

    let ref_bundle = assemble_bundle(
        format!("{}-reference", config.workload_id),
        host.clone(),
        ref_workload,
        ref_attempts,
        BenchmarkTelemetry {
            schema_version: BENCHMARK_EVIDENCE_VERSION,
            attempts: ref_telemetry,
        },
    )
    .map_err(|e| format!("reference bundle assembly refused: {e:?}"))?;
    let ref_validated = validate_bundle(&ref_bundle)
        .map_err(|e| format!("reference bundle validation refused: {e:?}"))?;

    let cand_bundle = assemble_bundle(
        format!("{}-candidate", config.workload_id),
        host,
        cand_workload,
        cand_attempts,
        BenchmarkTelemetry {
            schema_version: BENCHMARK_EVIDENCE_VERSION,
            attempts: cand_telemetry,
        },
    )
    .map_err(|e| format!("candidate bundle assembly refused: {e:?}"))?;
    let cand_validated = validate_bundle(&cand_bundle)
        .map_err(|e| format!("candidate bundle validation refused: {e:?}"))?;

    let ref_summary = ref_validated
        .candidate()
        .summary
        .as_ref()
        .ok_or("missing validated reference summary")?;
    let cand_summary = cand_validated
        .candidate()
        .summary
        .as_ref()
        .ok_or("missing validated candidate summary")?;

    let ref_med_ns = ratio_f64(&ref_summary.median);
    let cand_med_ns = ratio_f64(&cand_summary.median);
    let ratio = cand_med_ns / ref_med_ns;

    println!("=== REFERENCE (incumbent) ===");
    print!("{}", ref_validated.report());
    println!("semantic_root={}", ref_validated.roots().semantic);
    println!("=== CANDIDATE (FrankenLean) ===");
    print!("{}", cand_validated.report());
    println!("semantic_root={}", cand_validated.roots().semantic);
    println!(
        "COMPARISON mode={qualification_tag} samples={} reference_median_ms={:.3} candidate_median_ms={:.3} candidate_over_reference={:.3}x reference_p95_ms={:.3} candidate_p95_ms={:.3}",
        config.samples,
        ref_med_ns / 1e6,
        cand_med_ns / 1e6,
        ratio,
        (ref_summary.p95 as f64) / 1e6,
        (cand_summary.p95 as f64) / 1e6,
    );

    if let Some(dir) = &config.out_dir {
        fs::create_dir_all(dir)
            .map_err(|e| format!("failed to create `{}`: {e}", dir.display()))?;
        fs::write(
            dir.join("reference.semantic.ndjson"),
            ref_validated.semantic_ndjson(),
        )
        .map_err(|e| format!("write reference semantic ndjson: {e}"))?;
        fs::write(
            dir.join("candidate.semantic.ndjson"),
            cand_validated.semantic_ndjson(),
        )
        .map_err(|e| format!("write candidate semantic ndjson: {e}"))?;
        fs::write(
            dir.join("reference.telemetry.ndjson"),
            ref_validated.telemetry_ndjson(),
        )
        .map_err(|e| format!("write reference telemetry ndjson: {e}"))?;
        fs::write(
            dir.join("candidate.telemetry.ndjson"),
            cand_validated.telemetry_ndjson(),
        )
        .map_err(|e| format!("write candidate telemetry ndjson: {e}"))?;
    }

    Ok(ExitCode::SUCCESS)
}

fn main() -> ExitCode {
    match run() {
        Ok(code) => code,
        Err(err) => {
            eprintln!("error: {err}");
            ExitCode::FAILURE
        }
    }
}
