//! Real pinned-Reference G0-4 syntax/hygiene differential.

#![forbid(unsafe_code)]

use fln_conformance::pin;
use fln_conformance::syntax_hygiene::{
    FixtureManifest, ReferenceTranscript, TelemetryObservation, acceptance_is_green,
    compare_manifest, local_c0_payload, measure_contract_usage, run_budget_matrix, semantic_root,
    semantic_stream, stock_trace_contract,
};
use std::path::Path;
use std::process::{Command, Stdio};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::time::{Duration, Instant};

const COMMITTED_SEMANTIC_EVIDENCE: &str =
    include_str!("../evidence/g04_syntax_hygiene/semantic_v4.32.0.ndjson");

fn proc_peak_rss_bytes(pid: u32) -> Option<u64> {
    let status = std::fs::read_to_string(format!("/proc/{pid}/status")).ok()?;
    ["VmHWM:", "VmRSS:"].into_iter().find_map(|label| {
        let row = status.lines().find(|line| line.starts_with(label))?;
        let kib = row.split_ascii_whitespace().nth(1)?.parse::<u64>().ok()?;
        kib.checked_mul(1024)
    })
}

fn run_reference(lean: &Path, fixture: &Path) -> Result<(String, u64, Option<u64>), String> {
    let started = Instant::now();
    let child = Command::new(lean)
        .arg(
            fixture
                .file_name()
                .ok_or_else(|| format!("fixture {} has no file name", fixture.display()))?,
        )
        .current_dir(
            fixture
                .parent()
                .ok_or_else(|| format!("fixture {} has no parent", fixture.display()))?,
        )
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| format!("spawn pinned Reference fixture: {error}"))?;
    let pid = child.id();
    let sampling_done = Arc::new(AtomicBool::new(false));
    let sampled_peak = Arc::new(AtomicU64::new(0));
    let sampler_done = Arc::clone(&sampling_done);
    let sampler_peak = Arc::clone(&sampled_peak);
    let sampler = std::thread::spawn(move || {
        while !sampler_done.load(Ordering::Acquire) {
            if let Some(bytes) = proc_peak_rss_bytes(pid) {
                sampler_peak.fetch_max(bytes, Ordering::AcqRel);
            }
            std::thread::sleep(Duration::from_millis(2));
        }
    });
    let output = child.wait_with_output();
    sampling_done.store(true, Ordering::Release);
    sampler
        .join()
        .map_err(|_| "pinned Reference RSS sampler panicked".to_string())?;
    let output = output.map_err(|error| format!("wait for pinned Reference fixture: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "pinned Reference fixture exited {:?}: stdout={:?} stderr={:?}",
            output.status.code(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    if !output.stderr.is_empty() {
        return Err(format!(
            "pinned Reference fixture emitted stderr: {:?}",
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    let stdout = String::from_utf8(output.stdout)
        .map_err(|_| "pinned Reference fixture stdout was not UTF-8".to_string())?;
    let elapsed = started.elapsed().as_micros().min(u128::from(u64::MAX)) as u64;
    let peak = sampled_peak.load(Ordering::Acquire);
    Ok((stdout, elapsed, (peak != 0).then_some(peak)))
}

fn mutate_first_payload(raw: &str) -> String {
    let mut lines = raw.lines().map(str::to_string).collect::<Vec<_>>();
    let mut fields = lines[0].split('\t').map(str::to_string).collect::<Vec<_>>();
    let payload = fields.last_mut().expect("Reference row has a payload");
    let final_nibble = payload.pop().expect("Reference payload is nonempty");
    payload.push(if final_nibble == '0' { '1' } else { '0' });
    lines[0] = fields.join("\t");
    lines.join("\n") + "\n"
}

#[test]
fn g0_4_no_mock_e2e() -> Result<(), String> {
    let run = pin::RigRun::new(pin::PinRig::G04NoMockE2e);
    let Some(lean) = pin::pinned_lean() else {
        let notice = run.typed_skip()?;
        eprintln!("{notice}");
        return Ok(());
    };
    let expected_commit =
        pin::pinned_commit().ok_or_else(|| "SUITE.lock has no Reference commit".to_string())?;
    let githash = Command::new(&lean)
        .arg("--githash")
        .output()
        .map_err(|error| format!("query pinned Reference githash: {error}"))?;
    if !githash.status.success() || !githash.stderr.is_empty() {
        return Err(format!(
            "pinned Reference --githash failed: status={:?} stderr={:?}",
            githash.status.code(),
            String::from_utf8_lossy(&githash.stderr)
        ));
    }
    assert_eq!(
        String::from_utf8_lossy(&githash.stdout).trim(),
        expected_commit,
        "the located Reference binary must be the SUITE.lock pin"
    );

    let root = pin::workspace_root();
    let fixture = root.join("crates/fln-conformance/fixtures/g04_reference_fixture.lean");
    let manifest = FixtureManifest::load_embedded()?;
    manifest.validate_grammar_roots()?;
    let (first_raw, first_micros, first_peak_rss) = run_reference(&lean, &fixture)?;
    let (second_raw, second_micros, second_peak_rss) = run_reference(&lean, &fixture)?;
    assert_eq!(
        first_raw, second_raw,
        "two fresh pinned Reference processes produced different syntax observations"
    );

    let first = ReferenceTranscript::parse(first_raw.clone(), &manifest)?;
    let second = ReferenceTranscript::parse(second_raw, &manifest)?;
    assert_eq!(first, second);
    assert_eq!(first.records().len(), manifest.rows().len());
    let observations = compare_manifest(&manifest, &first);
    for observation in observations
        .iter()
        .filter(|observation| observation.code == "c0-tree-or-sourceinfo-divergence")
    {
        let row = manifest
            .row(&observation.fixture)
            .expect("observation joined to manifest");
        let reference = first
            .record(&observation.fixture)
            .expect("observation joined to Reference");
        eprintln!(
            "g04-first-divergence fixture={} reference={:?} local={:?}",
            observation.fixture,
            String::from_utf8_lossy(&reference.payload),
            local_c0_payload(&row.source)?
        );
    }
    assert!(
        acceptance_is_green(&observations),
        "G0-4 comparator left an unclassified result or lost an exact/gap row: {observations:#?}"
    );
    let semantics = semantic_stream(&observations);
    assert_eq!(
        semantics, COMMITTED_SEMANTIC_EVIDENCE,
        "live pinned-Reference semantics drifted from the committed semantic receipt"
    );
    assert!(!semantics.contains("fln-g04-telemetry/1"));
    assert!(!semantics.contains("wall_micros"));

    let budget = run_budget_matrix(&manifest, 32)?;
    let usage = measure_contract_usage(&manifest)?;
    let telemetry = TelemetryObservation {
        run_id: format!("g04:{}:two-process", expected_commit),
        wall_micros: first_micros.saturating_add(second_micros),
        peak_rss_bytes: first_peak_rss.into_iter().chain(second_peak_rss).max(),
        reference_processes: 2,
        partitions: budget.partitions.clone(),
    }
    .to_ndjson();
    assert!(!telemetry.contains("fln-g04-semantic/1"));
    assert!(!telemetry.contains("reference_root"));
    if std::env::var_os("FLN_G04_PRINT_STREAMS").is_some() {
        eprint!("{semantics}");
        eprint!("{telemetry}");
    }

    let trace = stock_trace_contract()?;
    assert_eq!(trace.elab_step_count, 261);
    eprintln!(
        "g04-receipt reference_root={} manifest_root={} semantic_root={} \
         trace_root={} budget_root={} usage_root={}",
        first.root(),
        manifest.root(),
        semantic_root(&observations),
        trace.fixture_root,
        budget.stream_root,
        usage.root()
    );

    let changed_payload = mutate_first_payload(&first_raw);
    let mutant = ReferenceTranscript::parse(changed_payload, &manifest)?;
    let mutant_observations = compare_manifest(&manifest, &mutant);
    assert!(
        !acceptance_is_green(&mutant_observations),
        "a changed Reference payload must not survive the comparator"
    );

    let mut reordered = first_raw.lines().map(str::to_string).collect::<Vec<_>>();
    reordered.swap(0, 1);
    assert!(
        ReferenceTranscript::parse(reordered.join("\n") + "\n", &manifest).is_err(),
        "fixture order is semantic and must fail closed"
    );
    run.executed()
}
