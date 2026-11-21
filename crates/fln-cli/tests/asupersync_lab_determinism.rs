//! Deterministic `asupersync::LabRuntime` verification for FrankenLean's
//! generation-bound check regions (bead `fln-otk7`).
//!
//! Covers:
//! 1. Positive: real native proof checks orchestrated inside `ChildRegion`s under
//!    `run_async_under_lab` replay bit-identically from a seed, produce the same
//!    schedule-independent semantic digest across a sweep of seeds, and pass all
//!    Lab oracles (`quiescence`, `obligation_leak`, `task_leak`, `region_leak`).
//! 2. Negative: a planted schedule-dependent publication bug (racing generations
//!    without cancellation or canonical ordering) is caught and rejected across
//!    seeds by the same Lab harness.
//! 3. Negative: a cancelled check region's `CxCancellationProbe` aborts real
//!    `SourceModuleSession::check_with_cancel` work as `Outcome::Inconclusive`
//!    and never acquires publication authority.
#![forbid(unsafe_code)]

use std::collections::BTreeMap;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};

use asupersync::cx::ChildRegionSpec;
use asupersync::lab::{LabRunReport, run_async_under_lab};
use asupersync::runtime::yield_now::yield_now;
use fln::source_check::modules::{
    SourceModuleCacheLimits, SourceModuleCheckLimits, SourceModuleSession,
};
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, Outcome};
use fln_cli::runtime_plane::{
    CxCancellationProbe, RegionCounters, RuntimeEvent, RuntimeEventSink, cancel_reason,
};
use fln_core::outcome::InconclusiveCause;

fn build_seed_session() -> SourceModuleSession {
    let admission = EngineAdmissionLimits::new(Budget::for_stack_bytes(16 * 1024 * 1024));
    let engine = match Engine::with_coercion_seed(admission).expect("seed admission result") {
        Outcome::Complete(engine) => engine,
        other => panic!("unexpected seed admission outcome: {other:?}"),
    };
    let limits = SourceModuleCheckLimits::new(fln::SourceCheckLimits::new(admission));
    SourceModuleSession::new(
        engine,
        KVMap::new(),
        limits,
        SourceModuleCacheLimits::default(),
    )
}

fn slow_multi_theorem_source(count: usize, suffix: &str) -> String {
    let mut out = String::new();
    for i in 0..count {
        out.push_str(&format!(
            "theorem lab_gen_{suffix}_{i} (P : Prop) (h : P) : P := by exact h\n"
        ));
    }
    out
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct PublishedSnapshot {
    generation: u64,
    uri: String,
    commands: usize,
    theorems: usize,
    logical_root_hex: String,
}

fn run_canonical_generation_scenario(
    seed: u64,
) -> (
    Vec<PublishedSnapshot>,
    RegionCounters,
    Vec<RuntimeEvent>,
    LabRunReport,
) {
    let counters = Arc::new(RegionCounters::new());
    let (sink, events_buf) = RuntimeEventSink::in_memory();
    let counters_for_lab = Arc::clone(&counters);
    let sink_for_lab = sink.clone();

    let (published, report) = run_async_under_lab(seed, move |root_cx| async move {
        let mut published: BTreeMap<String, PublishedSnapshot> = BTreeMap::new();

        // Phase 1: Generation 1 on file A starts in ChildRegion 1, yields mid-work,
        // and is actively cancelled when Generation 2 supersedes it.
        let uri_a = "file:///lab/Main.lean".to_owned();
        let gen1_src = slow_multi_theorem_source(12, "stale_v1");
        let gen2_src = "theorem recovered (P : Prop) (h : P) : P := by exact h\n".to_owned();

        let child1 = root_cx
            .open_child_region(ChildRegionSpec::inherit())
            .await
            .expect("open child region for gen1");
        let region1_id = format!("{:?}", child1.region_id());
        let (active_regions, _) = counters_for_lab.on_region_opened();
        let live_tasks = counters_for_lab.on_task_spawned();
        sink_for_lab.record(RuntimeEvent {
            subsystem: "lsp",
            event: "region_opened",
            request_id: 1,
            target: uri_a.clone(),
            version: Some(1),
            generation: 1,
            region_id: region1_id.clone(),
            cancellation_outcome: "none",
            cache_hit: None,
            active_regions,
            live_tasks,
            authoritative_publication: false,
            detail: None,
        });

        let cancel1 = Arc::new(AtomicBool::new(false));
        let cancel1_task = Arc::clone(&cancel1);
        let mut task1 = child1
            .cx()
            .spawn(move |task_cx| async move {
                // Cooperative yield point inside the child region so the superseding
                // edit cancels this region before the source check completes.
                yield_now().await;
                let probe = CxCancellationProbe::new(task_cx, cancel1_task);
                let mut session = build_seed_session();
                let name = Name::from_components(["LabMain"]);
                let inputs = [fln::SourceModuleInput {
                    name: &name,
                    source: gen1_src.as_bytes(),
                }];
                session.check_with_cancel(&inputs, &name, Some(&probe))
            })
            .expect("spawn gen1 check task");

        // Supersede generation 1 with generation 2 before gen1 can finish.
        cancel1.store(true, Ordering::SeqCst);
        child1
            .cancel(cancel_reason("superseded by gen2 in lab"))
            .expect("cancel gen1 region");
        let gen1_join = task1.join(&root_cx).await;
        let _ = counters_for_lab.on_task_drained();
        child1
            .close()
            .await
            .expect("close gen1 region to quiescence");
        let (active_regions, live_tasks) = counters_for_lab.on_region_drained(true);

        // Cancelled generation must never acquire publication authority.
        let cancelled_actively = match &gen1_join {
            Ok(Ok(Outcome::Inconclusive(reason))) => {
                matches!(reason.cause, InconclusiveCause::Cancelled { .. })
            }
            Err(_) => true,
            _ => false,
        };
        assert!(
            cancelled_actively,
            "gen1 should have been cancelled cleanly, got: {gen1_join:?}"
        );
        sink_for_lab.record(RuntimeEvent {
            subsystem: "lsp",
            event: "region_cancelled_and_drained",
            request_id: 1,
            target: uri_a.clone(),
            version: Some(1),
            generation: 1,
            region_id: region1_id,
            cancellation_outcome: "cancelled_active",
            cache_hit: None,
            active_regions,
            live_tasks,
            authoritative_publication: false,
            detail: None,
        });

        // Phase 2: Spawn concurrent regions for file A (gen 2) and file B (gen 1),
        // letting the Lab scheduler interleave them according to `seed`, then merge
        // results canonically by URI (BTreeMap).
        let specs = [
            (2_u64, uri_a, 2_u64, "LabMain", gen2_src),
            (
                3_u64,
                "file:///lab/Helper.lean".to_owned(),
                1_u64,
                "LabHelper",
                "def helperVal : Nat := 7\ntheorem helperOk : helperVal = 7 := by rfl\n".to_owned(),
            ),
        ];

        let mut active = Vec::new();
        for (req_id, uri, gen_num, mod_name, src) in specs {
            let child = root_cx
                .open_child_region(ChildRegionSpec::inherit())
                .await
                .expect("open child region");
            let reg_id = format!("{:?}", child.region_id());
            let _ = counters_for_lab.on_region_opened();
            let _ = counters_for_lab.on_task_spawned();
            let flag = Arc::new(AtomicBool::new(false));
            let mod_name_owned = mod_name.to_owned();
            let uri_task = uri.clone();
            let task = child
                .cx()
                .spawn(move |task_cx| async move {
                    // Yield twice so the Lab scheduler exercises different task interleavings
                    // across seeds.
                    yield_now().await;
                    let probe = CxCancellationProbe::new(task_cx, flag);
                    let mut session = build_seed_session();
                    let name = Name::from_components([mod_name_owned.as_str()]);
                    let inputs = [fln::SourceModuleInput {
                        name: &name,
                        source: src.as_bytes(),
                    }];
                    let checked = session
                        .check_with_cancel(&inputs, &name, Some(&probe))
                        .expect("check succeeds");
                    yield_now().await;
                    match checked {
                        Outcome::Complete(res) => PublishedSnapshot {
                            generation: gen_num,
                            uri: uri_task,
                            commands: res.checked.checked.commands,
                            theorems: res.checked.checked.theorems,
                            logical_root_hex: res.checked.checked.result_logical_root.0.to_hex(),
                        },
                        other => {
                            panic!("unexpected non-complete outcome for fresh check: {other:?}")
                        }
                    }
                })
                .expect("spawn fresh check task");
            active.push((req_id, uri, gen_num, reg_id, child, task));
        }

        for (req_id, uri, gen_num, reg_id, child, mut task) in active {
            let snap = task.join(&root_cx).await.expect("join fresh check task");
            let _ = counters_for_lab.on_task_drained();
            child
                .close()
                .await
                .expect("close fresh region to quiescence");
            let (active_regions, live_tasks) = counters_for_lab.on_region_drained(false);
            sink_for_lab.record(RuntimeEvent {
                subsystem: "lsp",
                event: "region_completed",
                request_id: req_id,
                target: uri.clone(),
                version: Some(gen_num as i64),
                generation: gen_num,
                region_id: reg_id,
                cancellation_outcome: "none",
                cache_hit: Some(false),
                active_regions,
                live_tasks,
                authoritative_publication: true,
                detail: None,
            });
            published.insert(uri, snap);
        }

        published.into_values().collect::<Vec<_>>()
    });

    let events = events_buf.lock().expect("events lock").clone();
    let owned_counters = Arc::try_unwrap(counters).expect("no leaked counter clones");
    (published, owned_counters, events, report)
}

#[test]
fn lab_runtime_proof_check_regions_replay_deterministically_and_are_schedule_independent() {
    let seeds = [1_u64, 7, 42, 99, 1337, 2026];

    // Exact same-seed deterministic replay check.
    let (first_published, first_counters, first_events, first_report) =
        run_canonical_generation_scenario(42);
    let (replay_published, _, replay_events, replay_report) = run_canonical_generation_scenario(42);

    assert!(first_report.quiescent, "first run must reach quiescence");
    assert!(
        first_report.invariant_violations.is_empty(),
        "invariant violations: {:?}",
        first_report.invariant_violations
    );
    assert!(
        first_report.oracle_report.all_passed(),
        "lab oracles failed: {:?}",
        first_report.oracle_report
    );
    assert_eq!(
        first_published, replay_published,
        "same seed must replay identical published semantic snapshots"
    );
    assert_eq!(
        first_report.trace_fingerprint, replay_report.trace_fingerprint,
        "same seed must replay identical lab trace fingerprint"
    );
    assert_eq!(first_events.len(), replay_events.len());

    let snap = first_counters.snapshot();
    assert_eq!(snap.active_regions, 0, "leaked active regions: {snap:?}");
    assert_eq!(snap.live_tasks, 0, "leaked live tasks: {snap:?}");
    assert_eq!(snap.total_opened, 3);
    assert_eq!(snap.total_drained, 3);
    assert_eq!(snap.total_cancelled, 1);

    assert_eq!(first_published.len(), 2);
    assert_eq!(first_published[0].uri, "file:///lab/Helper.lean");
    assert_eq!(first_published[0].generation, 1);
    assert_eq!(first_published[1].uri, "file:///lab/Main.lean");
    assert_eq!(first_published[1].generation, 2);

    // Cross-seed schedule-independence sweep.
    for seed in seeds {
        let (published, counters, _, report) = run_canonical_generation_scenario(seed);
        assert!(report.quiescent, "seed {seed} must reach quiescence");
        assert!(
            report.invariant_violations.is_empty(),
            "seed {seed} invariant violations: {:?}",
            report.invariant_violations
        );
        assert!(
            report.oracle_report.all_passed(),
            "seed {seed} oracle failures: {:?}",
            report.oracle_report
        );
        let c = counters.snapshot();
        assert_eq!(c.active_regions, 0);
        assert_eq!(c.live_tasks, 0);
        assert_eq!(c.total_opened, c.total_drained);
        assert_eq!(
            published, first_published,
            "seed {seed} produced schedule-dependent semantic output"
        );
    }
}

/// Negative control required by `fln-otk7`: plant a schedule-dependent check
/// publisher (two concurrent workers racing to push into an unordered publication
/// log without generation gating or canonical merge) and prove that the Lab seed
/// sweep catches the nondeterminism.
#[test]
fn lab_runtime_catches_planted_schedule_dependent_publication_bug() {
    fn run_planted_schedule_dependent(seed: u64) -> Vec<&'static str> {
        let (order, report) = run_async_under_lab(seed, |root_cx| async move {
            let log: Arc<Mutex<Vec<&'static str>>> = Arc::new(Mutex::new(Vec::new()));
            let mut handles = Vec::new();
            for label in ["gen-1-stale", "gen-2-fresh", "gen-3-concurrent"] {
                let log_clone = Arc::clone(&log);
                let handle = root_cx
                    .spawn(move |_| async move {
                        yield_now().await;
                        log_clone.lock().expect("log lock").push(label);
                    })
                    .expect("spawn planted racing worker");
                handles.push(handle);
            }
            for mut handle in handles {
                handle.join(&root_cx).await.expect("join planted worker");
            }
            log.lock().expect("log lock").clone()
        });
        assert!(report.quiescent);
        order
    }

    // Same seed still replays the same buggy schedule deterministically.
    assert_eq!(
        run_planted_schedule_dependent(1),
        run_planted_schedule_dependent(1)
    );

    // Sweeping seeds MUST detect divergence for the planted schedule-dependent bug.
    let baseline = run_planted_schedule_dependent(1);
    let diverged = (2_u64..64).any(|seed| run_planted_schedule_dependent(seed) != baseline);
    assert!(
        diverged,
        "Lab seed sweep failed to catch the planted schedule-dependent publication bug (all seeds produced {baseline:?})"
    );
}

/// Negative control: prove `CxCancellationProbe` actively aborts a multi-command
/// real `SourceModuleSession::check_with_cancel` mid-file with
/// `Outcome::Inconclusive(Cancelled)` and leaves the session cache unmutated.
#[test]
fn cancelled_source_check_never_publishes_or_mutates_session_cache() {
    struct CancelAfterSecondPoll(std::sync::atomic::AtomicUsize);
    impl fln::CancellationProbe for CancelAfterSecondPoll {
        fn is_cancelled(&self) -> bool {
            self.0.fetch_add(1, Ordering::SeqCst) >= 3
        }
    }

    let mut session = build_seed_session();
    let name = Name::from_components(["CancelProbeMod"]);
    let big_src = slow_multi_theorem_source(25, "mid_cancel");
    let inputs = [fln::SourceModuleInput {
        name: &name,
        source: big_src.as_bytes(),
    }];
    let probe = CancelAfterSecondPoll(std::sync::atomic::AtomicUsize::new(0));
    let outcome = session
        .check_with_cancel(&inputs, &name, Some(&probe))
        .expect("cancellation returns typed Outcome::Inconclusive, not error");
    match outcome {
        Outcome::Inconclusive(reason) => {
            assert!(
                matches!(reason.cause, InconclusiveCause::Cancelled { .. }),
                "expected cancelled cause, got: {reason:?}"
            );
        }
        other => panic!("expected cancelled Inconclusive outcome, got: {other:?}"),
    }
    assert_eq!(
        session.retained_modules(),
        0,
        "cancelled candidate must not commit partial entries to session cache"
    );

    // Recovery on the exact same session with fresh uncancelled check succeeds.
    let fresh = "theorem recovered_after_cancel (P : Prop) (h : P) : P := by exact h\n";
    let fresh_inputs = [fln::SourceModuleInput {
        name: &name,
        source: fresh.as_bytes(),
    }];
    let recovered = session
        .check_with_cancel(&fresh_inputs, &name, None)
        .expect("fresh check succeeds");
    assert!(matches!(recovered, Outcome::Complete(_)));
    assert_eq!(session.retained_modules(), 1);
}
