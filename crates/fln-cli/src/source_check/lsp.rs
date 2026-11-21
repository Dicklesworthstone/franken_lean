//! Native proof-library diagnostics on an `asupersync` `Cx`-region effect plane
//! (bead `fln-otk7`).
//!
//! Each document check generation opens an owned `asupersync::cx::ChildRegion`
//! on a stack-calibrated runtime worker and passes a `Cx`-backed
//! [`crate::runtime_plane::CxCancellationProbe`] into
//! `SourceModuleSession::check_with_cancel`. When a superseding `didChange` or
//! `didClose` arrives while checking, the server cancels the old generation's
//! child region, awaits full region drain and quiescence, discards stale output
//! without acquiring publication authority, and serves the newer generation in a
//! fresh child region.
//!
//! A document whose imports include `.olean` modules is checked against that import
//! world, resolved and obtained exactly as `fln check-source` obtains it, under the
//! `reuse-verified` posture (bead `fln-uyuz`). The world's bytes are read afresh on
//! every check; the worker reuses a bounded set of sessions only when the
//! corresponding closure is byte-identical. Switching between documents does
//! not discard another document's admitted world or checked source prefixes.
use super::imports::EditorWorld;
use super::imports::editor::{self, Sources};
use super::*;
use crate::runtime_plane::{
    CxCancellationProbe, IncomingTransport, RegionCounters, RuntimeEvent, RuntimeEventSink,
    build_effect_runtime, cancel_reason, shutdown_runtime,
};
use asupersync::Cx;
use asupersync::cx::ChildRegionSpec;
use asupersync::runtime::Runtime;
use fln::source_check::modules::reuse::{ImportPosture, ImportPostureReport};
use fln::source_check::modules::{
    SourceModuleCacheLimits, SourceModuleCheckError, SourceModuleCheckLimits, SourceModuleSession,
};
use fln_server::dispatch::{
    CheckOutcome, IncomingCheckAction, OpenDocumentSource, classify_incoming_for_active_check,
};
use std::collections::{BTreeMap, VecDeque};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};

mod completion;
mod dependencies;
mod interactive;
mod navigation;
mod render;
mod tokens;
use fln::source_check::inspect::{ObservationKind, SourceObservation};
use fln_server::dispatch::semantic::{Answer, Query, QueryKind};

enum CheckRunOutcome {
    Completed {
        messages: Vec<String>,
        cache_hit: Option<bool>,
        authoritative: bool,
    },
    Cancelled,
}

pub(crate) struct Checker {
    runtime: Option<Arc<Runtime>>,
    sessions: Arc<Mutex<Sessions>>,
    transport: Option<Arc<Mutex<IncomingTransport>>>,
    counters: Arc<RegionCounters>,
    sink: RuntimeEventSink,
    generations: BTreeMap<String, u64>,
    dependencies: dependencies::Dependencies,
}

impl Drop for Checker {
    fn drop(&mut self) {
        if let Some(runtime) = self.runtime.take()
            && let Ok(owned) = Arc::try_unwrap(runtime)
        {
            shutdown_runtime(owned);
        }
    }
}

impl Checker {
    pub(crate) fn new() -> Self {
        Self {
            runtime: None,
            sessions: Arc::new(Mutex::new(Sessions::default())),
            transport: None,
            counters: Arc::new(RegionCounters::new()),
            sink: RuntimeEventSink::from_env(),
            generations: BTreeMap::new(),
            dependencies: dependencies::Dependencies::default(),
        }
    }

    pub(crate) fn with_runtime(
        runtime: Arc<Runtime>,
        transport: Option<Arc<Mutex<IncomingTransport>>>,
        counters: Arc<RegionCounters>,
        sink: RuntimeEventSink,
    ) -> Self {
        Self {
            runtime: Some(runtime),
            sessions: Arc::new(Mutex::new(Sessions::default())),
            transport,
            counters,
            sink,
            generations: BTreeMap::new(),
            dependencies: dependencies::Dependencies::default(),
        }
    }

    fn ensure_runtime(&mut self) -> Result<Arc<Runtime>, String> {
        if let Some(runtime) = &self.runtime {
            return Ok(Arc::clone(runtime));
        }
        // `.olean` worlds are admitted, or their records re-proved, on the
        // calibrated runtime worker under the `.olean` depth budget, as
        // `lake build`'s worker does. Source checking keeps its own budget.
        let stack_bytes = OLEAN_CHECK_KERNEL_STACK_BYTES.max(SOURCE_RUN_KERNEL_STACK_BYTES);
        let runtime = Arc::new(build_effect_runtime("fln-lsp-asupersync", 2, stack_bytes)?);
        self.runtime = Some(Arc::clone(&runtime));
        Ok(runtime)
    }

    fn next_generation(&mut self, uri: &str) -> u64 {
        let entry = self.generations.entry(uri.to_owned()).or_insert(0);
        *entry = entry.saturating_add(1);
        *entry
    }

    pub(crate) fn check(
        &mut self,
        uri: &str,
        text: &str,
        documents: &[OpenDocumentSource<'_>],
    ) -> Vec<String> {
        match self.check_cancellable_inner(uri, 0, text, documents, false) {
            CheckOutcome::Complete(messages) => messages,
            CheckOutcome::Cancelled => Vec::new(),
        }
    }

    fn check_cancellable_inner(
        &mut self,
        uri: &str,
        version: i64,
        text: &str,
        documents: &[OpenDocumentSource<'_>],
        allow_cancel: bool,
    ) -> CheckOutcome {
        self.dependencies.begin(uri, documents);
        if text.len() > SOURCE_RUN_DEFAULT_MAX_BYTES {
            return CheckOutcome::Complete(project(
                uri,
                text,
                &nonanswer("resource", "editor source exceeds its byte limit"),
            ));
        }
        // Header parsing uses the complete lexical source view. Keep its exact
        // error offset instead of flattening a syntax error into an I/O failure.
        match fln::source_check::modules::parse_source_header(text.as_bytes()) {
            Ok(header)
                if header.imports.is_empty() && (!header.module_system || header.prelude) =>
            {
                self.dependencies.no_imports(uri)
            }
            Ok(_) => {}
            Err(error) => {
                return CheckOutcome::Complete(project(
                    uri,
                    text,
                    &diagnostic(
                        uri,
                        text.as_bytes(),
                        error.primary_offset().map_or(0, |p| p.0),
                        &error.to_string(),
                    ),
                ));
            }
        }
        let sources = match editor::load(uri, text, documents, SOURCE_RUN_DEFAULT_MAX_BYTES) {
            Ok(sources) => sources,
            Err(error) => {
                let snapshot = failure(uri, text.as_bytes(), 0, error.class, &error.detail);
                return CheckOutcome::Complete(project(uri, text, &snapshot));
            }
        };
        self.dependencies
            .loaded(uri, &sources.uris, &sources.absent_sources);

        let runtime = match self.ensure_runtime() {
            Ok(runtime) => runtime,
            Err(error) => {
                return CheckOutcome::Complete(project(uri, text, &nonanswer("resource", &error)));
            }
        };

        let request_id = self.counters.next_request_id();
        let generation = self.next_generation(uri);
        let sessions = Arc::clone(&self.sessions);
        let transport = self.transport.clone();
        let counters = Arc::clone(&self.counters);
        let sink = self.sink.clone();
        let uri_owned = uri.to_owned();

        let outcome = runtime.block_on(async move {
            let root_cx = Cx::current().expect("asupersync runtime Cx");
            let child = match root_cx.open_child_region(ChildRegionSpec::inherit()).await {
                Ok(child) => child,
                Err(error) => {
                    return Ok(CheckOutcome::Complete(project(
                        &uri_owned,
                        text,
                        &nonanswer(
                            "resource",
                            &format!("could not open proof-check region: {error:?}"),
                        ),
                    )));
                }
            };
            let region_id = format!("{:?}", child.region_id());
            let (active_regions, live_tasks_before) = counters.on_region_opened();

            // Check any already-buffered FIFO frames before starting work.
            let mut pre_superseded = false;
            let mut watch_incoming = allow_cancel && transport.is_some();
            if watch_incoming
                && let Some(transport_arc) = &transport
                && let Ok(mut guard) = transport_arc.lock()
            {
                let mut inspected = VecDeque::new();
                while let Some(frame) = guard.pop_deferred() {
                    if let Ok(Some(ref bytes)) = frame {
                        match classify_incoming_for_active_check(bytes, &uri_owned, version) {
                            IncomingCheckAction::Supersedes => {
                                pre_superseded = true;
                            }
                            IncomingCheckAction::Barrier => {
                                watch_incoming = false;
                            }
                            IncomingCheckAction::NonBarrier => {}
                        }
                    } else {
                        watch_incoming = false;
                    }
                    inspected.push_back(frame);
                    if pre_superseded || !watch_incoming {
                        break;
                    }
                }
                while let Some(frame) = guard.pop_deferred() {
                    inspected.push_back(frame);
                }
                for frame in inspected {
                    guard.push_deferred(frame);
                }
            }

            if pre_superseded {
                sink.record(RuntimeEvent {
                    subsystem: "lsp",
                    event: "region_opened",
                    request_id,
                    target: uri_owned.clone(),
                    version: Some(version),
                    generation,
                    region_id: region_id.clone(),
                    cancellation_outcome: "none",
                    cache_hit: None,
                    active_regions,
                    live_tasks: live_tasks_before,
                    authoritative_publication: false,
                    detail: None,
                });
                let _ = child.cancel(cancel_reason("superseded before check start"));
                let _ = child.close().await;
                let (active_regions, live_tasks) = counters.on_region_drained(true);
                sink.record(RuntimeEvent {
                    subsystem: "lsp",
                    event: "region_cancelled_and_drained",
                    request_id,
                    target: uri_owned,
                    version: Some(version),
                    generation,
                    region_id,
                    cancellation_outcome: "cancelled_before_start",
                    cache_hit: None,
                    active_regions,
                    live_tasks,
                    authoritative_publication: false,
                    detail: None,
                });
                return Ok(CheckOutcome::Cancelled);
            }

            let cancel_flag = Arc::new(AtomicBool::new(false));
            let task_cancel = Arc::clone(&cancel_flag);
            let started_flag = Arc::new(AtomicBool::new(false));
            let task_started = Arc::clone(&started_flag);
            let live_tasks = counters.on_task_spawned();
            sink.record(RuntimeEvent {
                subsystem: "lsp",
                event: "region_opened",
                request_id,
                target: uri_owned.clone(),
                version: Some(version),
                generation,
                region_id: region_id.clone(),
                cancellation_outcome: "none",
                cache_hit: None,
                active_regions,
                live_tasks,
                authoritative_publication: false,
                detail: None,
            });

            let mut task = match child.cx().spawn(move |task_cx| async move {
                task_started.store(true, Ordering::SeqCst);
                let probe = CxCancellationProbe::new(task_cx, task_cancel);
                let Ok(mut guard) = sessions.lock() else {
                    return Err("proof worker session lock poisoned".to_owned());
                };
                Ok(check_sources_with_cancel(
                    &mut guard,
                    &sources,
                    Some(&probe),
                ))
            }) {
                Ok(task) => task,
                Err(error) => {
                    let _ = counters.on_task_drained();
                    let _ = child.close().await;
                    let (active_regions, live_tasks) = counters.on_region_drained(false);
                    sink.record(RuntimeEvent {
                        subsystem: "lsp",
                        event: "region_failed",
                        request_id,
                        target: uri_owned.clone(),
                        version: Some(version),
                        generation,
                        region_id,
                        cancellation_outcome: "none",
                        cache_hit: None,
                        active_regions,
                        live_tasks,
                        authoritative_publication: false,
                        detail: Some(format!("spawn failed: {error:?}")),
                    });
                    return Ok(CheckOutcome::Complete(project(
                        &uri_owned,
                        text,
                        &nonanswer(
                            "resource",
                            &format!("could not spawn proof-check task: {error:?}"),
                        ),
                    )));
                }
            };

            let mut superseded = false;
            let join_outcome = if watch_incoming {
                let mut join_fut = std::pin::pin!(task.join(&root_cx));
                let raced = std::future::poll_fn(|poll_cx| {
                    use std::future::Future;
                    use std::task::Poll;
                    if let Poll::Ready(res) = join_fut.as_mut().poll(poll_cx) {
                        return Poll::Ready(Some(res));
                    }
                    if watch_incoming
                        && let Some(transport_arc) = &transport
                        && let Ok(mut guard) = transport_arc.lock()
                    {
                        loop {
                            match guard.receiver_mut().poll_recv(&root_cx, poll_cx) {
                                Poll::Ready(Ok(frame)) => {
                                    let action = match &frame {
                                        Ok(Some(bytes)) => classify_incoming_for_active_check(
                                            bytes, &uri_owned, version,
                                        ),
                                        _ => IncomingCheckAction::Barrier,
                                    };
                                    guard.push_deferred(frame);
                                    match action {
                                        IncomingCheckAction::Supersedes => {
                                            return Poll::Ready(None);
                                        }
                                        IncomingCheckAction::NonBarrier => continue,
                                        IncomingCheckAction::Barrier => {
                                            watch_incoming = false;
                                            break;
                                        }
                                    }
                                }
                                Poll::Ready(Err(_)) => {
                                    guard.push_deferred(Ok(None));
                                    watch_incoming = false;
                                    break;
                                }
                                Poll::Pending => break,
                            }
                        }
                    }
                    Poll::Pending
                })
                .await;
                match raced {
                    Some(res) => res,
                    None => {
                        superseded = true;
                        cancel_flag.store(true, Ordering::SeqCst);
                        let _ =
                            child.cancel(cancel_reason("superseded by newer document generation"));
                        join_fut.await
                    }
                }
            } else {
                task.join(&root_cx).await
            };

            let _ = counters.on_task_drained();
            let _ = child.close().await;
            let (active_regions, live_tasks) = counters.on_region_drained(superseded);

            if superseded {
                let (cancellation_outcome, cache_hit) = match &join_outcome {
                    Ok(Ok(CheckRunOutcome::Cancelled)) => (
                        if started_flag.load(Ordering::Acquire) {
                            "cancelled_active"
                        } else {
                            "cancelled_before_start"
                        },
                        None,
                    ),
                    Ok(Ok(CheckRunOutcome::Completed {
                        cache_hit: Some(true),
                        ..
                    })) => ("cancelled_after_cache_hit", Some(true)),
                    Ok(Ok(CheckRunOutcome::Completed { cache_hit, .. })) => {
                        ("raced_with_completion_discarded", *cache_hit)
                    }
                    _ => ("cancelled_active", None),
                };
                sink.record(RuntimeEvent {
                    subsystem: "lsp",
                    event: "region_cancelled_and_drained",
                    request_id,
                    target: uri_owned,
                    version: Some(version),
                    generation,
                    region_id,
                    cancellation_outcome,
                    cache_hit,
                    active_regions,
                    live_tasks,
                    authoritative_publication: false,
                    detail: None,
                });
                return Ok(CheckOutcome::Cancelled);
            }

            match join_outcome {
                Ok(Ok(CheckRunOutcome::Completed {
                    messages,
                    cache_hit,
                    authoritative,
                })) => {
                    sink.record(RuntimeEvent {
                        subsystem: "lsp",
                        event: "region_completed",
                        request_id,
                        target: uri_owned,
                        version: Some(version),
                        generation,
                        region_id,
                        cancellation_outcome: "none",
                        cache_hit,
                        active_regions,
                        live_tasks,
                        authoritative_publication: authoritative,
                        detail: None,
                    });
                    Ok(CheckOutcome::Complete(messages))
                }
                Ok(Ok(CheckRunOutcome::Cancelled)) => {
                    sink.record(RuntimeEvent {
                        subsystem: "lsp",
                        event: "region_cancelled_and_drained",
                        request_id,
                        target: uri_owned,
                        version: Some(version),
                        generation,
                        region_id,
                        cancellation_outcome: "cancelled_active",
                        cache_hit: None,
                        active_regions,
                        live_tasks,
                        authoritative_publication: false,
                        detail: None,
                    });
                    Ok(CheckOutcome::Cancelled)
                }
                Ok(Err(detail)) => {
                    sink.record(RuntimeEvent {
                        subsystem: "lsp",
                        event: "region_failed",
                        request_id,
                        target: uri_owned,
                        version: Some(version),
                        generation,
                        region_id,
                        cancellation_outcome: "none",
                        cache_hit: None,
                        active_regions,
                        live_tasks,
                        authoritative_publication: false,
                        detail: Some(detail.clone()),
                    });
                    Err(detail)
                }
                Err(error) => {
                    let detail = format!("proof worker stopped without a result: {error:?}");
                    sink.record(RuntimeEvent {
                        subsystem: "lsp",
                        event: "region_failed",
                        request_id,
                        target: uri_owned,
                        version: Some(version),
                        generation,
                        region_id,
                        cancellation_outcome: "none",
                        cache_hit: None,
                        active_regions,
                        live_tasks,
                        authoritative_publication: false,
                        detail: Some(detail.clone()),
                    });
                    Err(detail)
                }
            }
        });

        match outcome {
            Ok(outcome) => outcome,
            Err(_) => {
                // A faulted worker never leaves a previous success authoritative.
                // Reset sessions so a later check starts from a fresh seed/cache.
                self.sessions = Arc::new(Mutex::new(Sessions::default()));
                CheckOutcome::Complete(project(
                    uri,
                    text,
                    &fault("lsp-proof-worker", "proof worker stopped without a result"),
                ))
            }
        }
    }
}

fn project(uri: &str, text: &str, snapshot: &ProjectionSnapshot) -> Vec<String> {
    let request = ProjectionRequest {
        epoch: fln_core::diag::DiagnosticEpoch::V4_32_0,
        mode: Mode::Sound,
        frontend: DiagnosticFrontend::Lsp,
        format: DiagnosticFormat::Lsp,
        channel: DiagnosticChannel::Protocol,
        color: DiagnosticColorPolicy::Never,
        path: DiagnosticPathPolicy::Preserve,
        ordering: fln_core::diag::DiagnosticOrderPolicy::SourcePositionV1,
    };
    fln_server::project_with_sources(request, snapshot, &[fln_server::LspSource::new(uri, text)])
        .map(|projection| projection.messages)
        .unwrap_or_default()
}
fn nonanswer(class: &'static str, detail: &str) -> ProjectionSnapshot {
    ProjectionSnapshot::Inconclusive(StructuredInconclusive {
        cause_class: class,
        detail: BoundedText::new(detail.to_owned()),
        diagnostic: None,
        progress: None,
    })
}
fn fault(invariant: &'static str, detail: &str) -> ProjectionSnapshot {
    ProjectionSnapshot::InternalFault(StructuredInternalFault {
        invariant,
        detail: BoundedText::new(detail.to_owned()),
        evidence: None,
    })
}
fn diagnostic(uri: &str, source: &[u8], offset: usize, message: &str) -> ProjectionSnapshot {
    ProjectionSnapshot::Complete {
        diagnostics: vec![StructuredDiagnostic {
            // Preserve the entire URI; re-encoding an already escaped path
            // would disconnect this publication from its open document.
            file_name: BoundedText::new(uri.to_owned()),
            pos: source_position_at(source, offset)
                .unwrap_or(fln_core::pos::Position { line: 1, column: 0 }),
            end_pos: None,
            severity: Severity::Error,
            error_name: None,
            caption: BoundedText::new(message.to_owned()),
            body: BoundedText::new(String::new()),
            cause_class: "engine-error",
            related: Vec::new(),
            evidence: Vec::new(),
            omitted_related: 0,
            omitted_evidence: 0,
        }],
    }
}
fn failure(
    uri: &str,
    source: &[u8],
    offset: usize,
    class: &'static str,
    detail: &str,
) -> ProjectionSnapshot {
    match class {
        "internal-fault" => fault("source-check", detail),
        "resource" | "inconclusive" | "cancelled" => nonanswer(class, detail),
        _ => diagnostic(uri, source, offset, detail),
    }
}

/// The worker's sessions: separate seed/unseeded worlds and a bounded LRU of
/// admitted `.olean` closures. These are process-local checked objects, never
/// producer-trusted serialized environments.
#[derive(Default)]
struct Sessions {
    seed: Option<SourceModuleSession>,
    unseeded: Option<SourceModuleSession>,
    worlds: VecDeque<World>,
}

// Bound both the number of independent source caches and their import input
// weight. Encoded bytes are an admission-input bound, not an RSS estimate:
// decoded terms and source-module caches have their own existing limits.
const MAX_RETAINED_WORLDS: usize = 4;
const MAX_RETAINED_ARTIFACT_BYTES: usize = 1 << 30;

/// An `.olean` world's session, reusable only for the exact captured closure.
struct World {
    identity: fln_hash::domain::Digest,
    artifact_bytes: usize,
    report: ImportPostureReport,
    session: SourceModuleSession,
}

/// How a check's `.olean` world was obtained, for `$/frankenLean/sourceCheck`.
struct WorldUse {
    /// The posture fields of the admission or reuse that produced the world.
    imports: String,
    /// Kept from an earlier check of this server, rather than obtained by this one.
    retained: bool,
}

enum Unavailable {
    Snapshot(Box<ProjectionSnapshot>),
    Failure(super::imports::Failure),
}

fn check_limits() -> SourceModuleCheckLimits {
    let admission = fln::EngineAdmissionLimits::new(fln::Budget::for_stack_bytes(
        SOURCE_RUN_KERNEL_STACK_BYTES,
    ));
    let mut limits = fln::SourceCheckLimits::new(admission);
    limits.max_bytes = SOURCE_RUN_DEFAULT_MAX_BYTES;
    SourceModuleCheckLimits::new(limits)
}

/// The session a document is checked in. Every lookup first reads and hashes
/// the current complete artifact closure. A stale or damaged artifact cannot
/// select a cached world by path, module name, mtime, or a prior success.
/// Misses evict least recently used worlds before admitting a new one.
fn select<'a>(
    sessions: &'a mut Sessions,
    sources: &Sources,
) -> Result<(&'a mut SourceModuleSession, Option<WorldUse>), Unavailable> {
    if sources.olean_roots.is_empty() {
        if sources.sources.iter().any(|source| {
            fln::source_check::modules::parse_source_header(source)
                .is_ok_and(|header| header.module_system)
        }) {
            let session = sessions.unseeded.get_or_insert_with(|| {
                SourceModuleSession::new(
                    fln::Engine::builder().build_empty(),
                    fln::KVMap::new(),
                    check_limits(),
                    SourceModuleCacheLimits::default(),
                )
            });
            return Ok((session, None));
        }
        ensure_session(&mut sessions.seed).map_err(Unavailable::Snapshot)?;
        return Ok((
            sessions.seed.as_mut().expect("initialized seed session"),
            None,
        ));
    }
    let world =
        EditorWorld::read(&sources.olean_roots, &sources.root).map_err(Unavailable::Failure)?;
    let position = sessions
        .worlds
        .iter()
        .position(|kept| kept.identity == world.identity);
    let retained = position.is_some();
    if let Some(position) = position {
        let kept = sessions
            .worlds
            .remove(position)
            .expect("matched retained world");
        sessions.worlds.push_back(kept);
    } else {
        let artifact_bytes = world.artifact_bytes();
        let Some(remaining) = MAX_RETAINED_ARTIFACT_BYTES.checked_sub(artifact_bytes) else {
            return Err(Unavailable::Snapshot(Box::new(nonanswer(
                "resource",
                "editor import world exceeds its retained artifact byte limit",
            ))));
        };
        while sessions.worlds.len() >= MAX_RETAINED_WORLDS
            || sessions
                .worlds
                .iter()
                .map(|kept| kept.artifact_bytes)
                .sum::<usize>()
                > remaining
        {
            sessions.worlds.pop_front();
        }
        let jobs = std::thread::available_parallelism()
            .ok()
            .and_then(|n| std::num::NonZeroUsize::new(n.get().min(8)))
            .unwrap_or(std::num::NonZeroUsize::MIN);
        let (receipt, report) = world
            .admit(jobs, ImportPosture::ReuseVerified)
            .map_err(Unavailable::Failure)?;
        sessions.worlds.push_back(World {
            identity: world.identity,
            artifact_bytes,
            report,
            session: SourceModuleSession::from_imports(
                receipt,
                fln::KVMap::new(),
                check_limits(),
                SourceModuleCacheLimits::default(),
            ),
        });
    }
    let kept = sessions.worlds.back_mut().expect("admitted world");
    let imports = format!("{{{}}}", posture_json(&kept.report));
    Ok((&mut kept.session, Some(WorldUse { imports, retained })))
}

fn check_sources_with_cancel(
    sessions: &mut Sessions,
    sources: &Sources,
    cancellation: Option<&dyn fln::CancellationProbe>,
) -> CheckRunOutcome {
    if cancellation.is_some_and(fln::CancellationProbe::is_cancelled) {
        return CheckRunOutcome::Cancelled;
    }
    let uri = &sources.uris[0];
    // Source bytes came from validated UTF-8 editor text or the native lexer.
    let text = std::str::from_utf8(&sources.sources[0]).expect("editor source is UTF-8");
    let (session, world) = match select(sessions, sources) {
        Ok(selected) => selected,
        Err(Unavailable::Snapshot(snapshot)) => {
            return CheckRunOutcome::Completed {
                messages: project(uri, text, &snapshot),
                cache_hit: None,
                authoritative: false,
            };
        }
        Err(Unavailable::Failure(failure)) => {
            return CheckRunOutcome::Completed {
                messages: project(
                    uri,
                    text,
                    &self::failure(uri, text.as_bytes(), 0, failure.class, &failure.detail),
                ),
                cache_hit: None,
                authoritative: false,
            };
        }
    };
    if cancellation.is_some_and(fln::CancellationProbe::is_cancelled) {
        return CheckRunOutcome::Cancelled;
    }
    let world = match world {
        Some(world) => format!(
            ",\"importWorld\":{},\"imports\":[{}]",
            json_string(if world.retained {
                "retained"
            } else {
                "obtained"
            }),
            world.imports
        ),
        None => ",\"imports\":[]".to_owned(),
    };
    let inputs: Vec<_> = sources
        .names
        .iter()
        .zip(&sources.sources)
        .map(|(name, source)| fln::SourceModuleInput { name, source })
        .collect();
    match session.check_with_cancel(&inputs, &sources.names[0], cancellation) {
        Ok(fln::Outcome::Complete(result)) => {
            let cache_hit = Some(result.reused_modules > 0 && result.elaborated_modules == 0);
            let mut messages = project(
                uri,
                text,
                &ProjectionSnapshot::Complete {
                    diagnostics: Vec::new(),
                },
            );
            messages.insert(0, format!(
                "{{\"jsonrpc\":\"2.0\",\"method\":\"$/frankenLean/sourceCheck\",\"params\":{{\"uri\":{},\"files\":{},\"commands\":{},\"theorems\":{},\"reusedModules\":{},\"elaboratedModules\":{},\"replayedDeclarations\":{},\"executed\":false{world}}}}}",
                json_string(uri), result.checked.checked.files, result.checked.checked.commands,
                result.checked.checked.theorems, result.reused_modules, result.elaborated_modules,
                result.checked.replayed_declarations,
            ));
            CheckRunOutcome::Completed {
                messages,
                cache_hit,
                authoritative: true,
            }
        }
        Ok(fln::Outcome::Inconclusive(reason))
            if matches!(
                reason.cause,
                fln_core::outcome::InconclusiveCause::Cancelled { .. }
            ) =>
        {
            CheckRunOutcome::Cancelled
        }
        Ok(fln::Outcome::Inconclusive(reason)) => CheckRunOutcome::Completed {
            messages: project(
                uri,
                text,
                &nonanswer("source-check", &format!("{reason:?}")),
            ),
            cache_hit: None,
            authoritative: false,
        },
        Ok(fln::Outcome::InternalFault(reason)) => CheckRunOutcome::Completed {
            messages: project(uri, text, &fault("source-check", &format!("{reason:?}"))),
            cache_hit: None,
            authoritative: false,
        },
        Err(error) => {
            let offset = match &error {
                SourceModuleCheckError::Header { module, error } if module == &sources.names[0] => {
                    error.primary_offset().map_or(0, |p| p.0)
                }
                SourceModuleCheckError::Source {
                    module,
                    error:
                        fln::SourceCheckError::Command { offset, .. }
                        | fln::SourceCheckError::Scope { offset, .. },
                } if module == &sources.names[0] => *offset,
                _ => 0,
            };
            let (class, _, _) = error.disposition();
            CheckRunOutcome::Completed {
                messages: project(
                    uri,
                    text,
                    &failure(uri, &sources.sources[0], offset, class, &error.to_string()),
                ),
                cache_hit: None,
                authoritative: !matches!(
                    class,
                    "internal-fault" | "resource" | "inconclusive" | "cancelled"
                ),
            }
        }
    }
}

impl fln_server::dispatch::WorkspaceChecker for Checker {
    fn semantic_queries(&self) -> bool {
        true
    }
    fn query(
        &mut self,
        query: Query<'_>,
        documents: &[OpenDocumentSource<'_>],
    ) -> Result<Option<Answer>, String> {
        if query.text.len() > SOURCE_RUN_DEFAULT_MAX_BYTES {
            return Err("editor source exceeds its byte limit".to_owned());
        }
        let sources = editor::load(
            query.uri,
            query.text,
            documents,
            SOURCE_RUN_DEFAULT_MAX_BYTES,
        )
        .map_err(|error| error.detail)?;
        let runtime = self.ensure_runtime()?;
        let sessions = Arc::clone(&self.sessions);
        let offset = query.offset;
        let kind = query.kind;
        let counters = Arc::clone(&self.counters);
        let result = runtime.block_on(async move {
            let root_cx = Cx::current().expect("asupersync runtime Cx");
            let child = root_cx
                .open_child_region(ChildRegionSpec::inherit())
                .await
                .map_err(|error| format!("could not open query region: {error:?}"))?;
            let _ = counters.on_region_opened();
            let _ = counters.on_task_spawned();
            let mut task = child
                .cx()
                .spawn(move |_task_cx| async move {
                    let Ok(mut guard) = sessions.lock() else {
                        return Err("proof worker session lock poisoned".to_owned());
                    };
                    inspect_sources(&mut guard, &sources, offset, kind)
                })
                .map_err(|error| format!("could not spawn query task: {error:?}"))?;
            let joined = task.join(&root_cx).await;
            let _ = counters.on_task_drained();
            let _ = child.close().await;
            let _ = counters.on_region_drained(false);
            match joined {
                Ok(answer) => answer,
                Err(_) => Err("proof worker stopped without a semantic result".to_owned()),
            }
        });
        if result
            .as_ref()
            .is_err_and(|msg| msg == "proof worker stopped without a semantic result")
        {
            self.sessions = Arc::new(Mutex::new(Sessions::default()));
        }
        result
    }

    fn check(
        &mut self,
        uri: &str,
        text: &str,
        documents: &[OpenDocumentSource<'_>],
    ) -> Vec<String> {
        Checker::check(self, uri, text, documents)
    }

    fn check_cancellable(
        &mut self,
        uri: &str,
        version: i64,
        text: &str,
        documents: &[OpenDocumentSource<'_>],
        allow_cancel: bool,
    ) -> CheckOutcome {
        self.check_cancellable_inner(uri, version, text, documents, allow_cancel)
    }

    fn affected(
        &mut self,
        changed: &[String],
        documents: &[OpenDocumentSource<'_>],
    ) -> Vec<String> {
        self.dependencies.affected(changed, documents)
    }
}

fn ensure_session(
    session: &mut Option<SourceModuleSession>,
) -> Result<(), Box<ProjectionSnapshot>> {
    if session.is_none() {
        let admission = fln::EngineAdmissionLimits::new(fln::Budget::for_stack_bytes(
            SOURCE_RUN_KERNEL_STACK_BYTES,
        ));
        let engine = match fln::Engine::with_coercion_seed(admission) {
            Ok(fln::Outcome::Complete(engine)) => engine,
            Ok(fln::Outcome::Inconclusive(reason)) => {
                return Err(Box::new(nonanswer("seed", &format!("{reason:?}"))));
            }
            Ok(fln::Outcome::InternalFault(reason)) => {
                return Err(Box::new(fault("seed-admission", &format!("{reason:?}"))));
            }
            Err(error) => return Err(Box::new(fault("seed-admission", &error.to_string()))),
        };
        *session = Some(SourceModuleSession::new(
            engine,
            fln::KVMap::new(),
            check_limits(),
            SourceModuleCacheLimits::default(),
        ));
    }
    Ok(())
}

fn inspect_sources(
    sessions: &mut Sessions,
    sources: &Sources,
    offset: usize,
    kind: QueryKind,
) -> Result<Option<Answer>, String> {
    let session = match select(sessions, sources) {
        Ok((session, _)) => session,
        Err(Unavailable::Snapshot(_)) => {
            return Err("native seed admission did not complete".to_owned());
        }
        Err(Unavailable::Failure(failure)) => return Err(failure.detail),
    };
    let inputs: Vec<_> = sources
        .names
        .iter()
        .zip(&sources.sources)
        .map(|(name, source)| fln::SourceModuleInput { name, source })
        .collect();
    let wanted = match kind {
        QueryKind::Goals | QueryKind::InteractiveGoals => ObservationKind::Goals,
        QueryKind::TermGoal | QueryKind::InteractiveTermGoal => ObservationKind::TermGoal,
        QueryKind::Hover => ObservationKind::Term,
        QueryKind::Definition => {
            return navigation::definition(session, sources, &inputs, offset);
        }
        QueryKind::DocumentSymbols => {
            return navigation::document_symbols(session, sources, &inputs);
        }
        QueryKind::SemanticTokens => {
            return tokens::collect(session, sources, &inputs);
        }
        QueryKind::Completion => {
            return completion::complete(session, sources, &inputs, offset);
        }
    };
    let mut locations = None;
    let result = if matches!(
        kind,
        QueryKind::InteractiveGoals | QueryKind::InteractiveTermGoal
    ) {
        session
            .inspect_with_navigation(&inputs, &sources.names[0], offset, wanted)
            .map_err(|error| error.to_string())?
            .map_complete(|navigation| {
                // Failure of the independent origin pass is represented by
                // unavailable navigation, not an invented empty destination or
                // the loss of an otherwise valid native goal/hover response.
                if let Ok(fln::Outcome::Complete(origins)) = navigation.locations {
                    locations = navigation::locations(sources, origins).ok();
                }
                navigation.inspection
            })
    } else {
        session
            .inspect(&inputs, &sources.names[0], offset, wanted)
            .map_err(|error| error.to_string())?
    };
    let inspected = match result {
        fln::Outcome::Complete(result) => result,
        fln::Outcome::Inconclusive(reason) => {
            return Err(format!("native inspection was inconclusive: {reason:?}"));
        }
        fln::Outcome::InternalFault(reason) => {
            return Err(format!("native inspection fault: {reason:?}"));
        }
    };
    Ok(match inspected.observation {
        None => None,
        Some(SourceObservation::Completion { .. }) => {
            return Err("completion context reached a different editor query".to_owned());
        }
        Some(SourceObservation::Goals { range, goals })
            if matches!(
                kind,
                QueryKind::InteractiveGoals | QueryKind::InteractiveTermGoal
            ) =>
        {
            Some(interactive::observe(
                goals,
                range,
                kind,
                fln::Budget::for_stack_bytes(SOURCE_RUN_KERNEL_STACK_BYTES),
                locations.as_ref(),
            )?)
        }
        Some(SourceObservation::Goals { range, goals }) => {
            if goals.len() > 256 {
                return Err("too many goals for one editor response".to_owned());
            }
            if kind == QueryKind::TermGoal && goals.len() != 1 {
                return Err("term inspection did not return exactly one goal".to_owned());
            }
            let mut displayed = Vec::new();
            let mut total = 0usize;
            for goal in goals {
                let mut renderer = render::Renderer::new();
                let mut names = Vec::new();
                for local in goal.locals.decls() {
                    names.push(renderer.local(&local.id, &local.user_name)?);
                }
                let mut lines = Vec::new();
                for (local, name) in goal.locals.decls().iter().zip(names) {
                    let type_ = renderer.expr(&local.type_)?;
                    let value = match &local.value {
                        Some(v) => format!(" := {}", renderer.expr(v)?),
                        None => String::new(),
                    };
                    lines.push(format!("{name} : {type_}{value}"));
                }
                lines.push(format!("⊢ {}", renderer.expr(&goal.target)?));
                let text = lines.join("\n");
                total = total
                    .checked_add(text.len())
                    .filter(|bytes| *bytes <= 64 * 1024)
                    .ok_or("goal display exceeded its byte limit")?;
                displayed.push(text);
            }
            if kind == QueryKind::TermGoal {
                let goal = displayed.pop().ok_or("term goal display is missing")?;
                Some(Answer::TermGoal { goal, range })
            } else {
                Some(Answer::Goals { goals: displayed })
            }
        }
        Some(SourceObservation::Term {
            range,
            expression,
            type_,
            locals,
        }) => {
            let mut renderer = render::Renderer::new();
            for local in locals.decls() {
                renderer.local(&local.id, &local.user_name)?;
            }
            Some(Answer::Hover {
                contents: format!(
                    "{} : {}",
                    renderer.expr(&expression)?,
                    renderer.expr(&type_)?
                ),
                range,
            })
        }
    })
}
