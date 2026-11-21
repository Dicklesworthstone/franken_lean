//! Governed `asupersync` effect plane for FrankenLean's LSP worker and Lake builds
//! (bead `fln-otk7`).
//!
//! Every check or build generation owns a runtime-backed `asupersync::cx::ChildRegion`
//! opened from a production runtime `Cx` (`Runtime::block_on` → `Cx::current()`).
//! Cancellation drives the real request → drain → finalize protocol via
//! `ChildRegion::cancel` + `ChildRegion::close().await` and bridges into FrankenLean's
//! cooperative `fln::CancellationProbe` so active source elaboration and module
//! compilation halt cleanly without publishing stale diagnostics or artifacts.

use std::collections::VecDeque;
use std::io::{self, BufRead, Write};
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use asupersync::channel::mpsc;
use asupersync::runtime::{Runtime, RuntimeBuilder};
use asupersync::{CancelReason, Cx};
use fln_server::dispatch::MessageSource;

/// Schema tag for structured NDJSON runtime telemetry events.
pub const RUNTIME_EVENT_SCHEMA: &str = "fln.asupersync-runtime-event/1";

/// Environment variable selecting an optional append-only NDJSON file for
/// structured runtime-plane region/generation/cancellation/resource logs.
/// Unset by default so stdout/stderr remain clean for protocol consumers.
pub const RUNTIME_EVENT_LOG_ENV: &str = "FLN_RUNTIME_EVENT_LOG";

/// Cooperative cancellation bridge from an `asupersync::Cx` (and its owning
/// `ChildRegion`) into `fln::CancellationProbe`.
#[derive(Clone)]
pub struct CxCancellationProbe {
    cx: Cx,
    cancelled: Arc<AtomicBool>,
}

impl CxCancellationProbe {
    #[must_use]
    pub fn new(cx: Cx, cancelled: Arc<AtomicBool>) -> Self {
        Self { cx, cancelled }
    }

    pub fn request_cancel(&self) {
        self.cancelled.store(true, Ordering::SeqCst);
    }

    #[must_use]
    pub fn cx(&self) -> &Cx {
        &self.cx
    }
}

impl fln::CancellationProbe for CxCancellationProbe {
    fn is_cancelled(&self) -> bool {
        self.cancelled.load(Ordering::Acquire) || self.cx.is_cancel_requested()
    }
}

/// Atomic resource-accounting counters for owned `asupersync` child regions and
/// region-owned tasks.
#[derive(Debug, Default)]
pub struct RegionCounters {
    active_regions: AtomicUsize,
    live_tasks: AtomicUsize,
    total_opened: AtomicU64,
    total_drained: AtomicU64,
    total_cancelled: AtomicU64,
    next_request_id: AtomicU64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RegionCountersSnapshot {
    pub active_regions: usize,
    pub live_tasks: usize,
    pub total_opened: u64,
    pub total_drained: u64,
    pub total_cancelled: u64,
}

impl RegionCounters {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    pub fn next_request_id(&self) -> u64 {
        self.next_request_id.fetch_add(1, Ordering::Relaxed) + 1
    }

    pub fn on_region_opened(&self) -> (usize, usize) {
        self.total_opened.fetch_add(1, Ordering::Relaxed);
        let regions = self.active_regions.fetch_add(1, Ordering::SeqCst) + 1;
        let tasks = self.live_tasks.load(Ordering::SeqCst);
        (regions, tasks)
    }

    pub fn on_task_spawned(&self) -> usize {
        self.live_tasks.fetch_add(1, Ordering::SeqCst) + 1
    }

    pub fn on_task_drained(&self) -> usize {
        self.live_tasks.fetch_sub(1, Ordering::SeqCst) - 1
    }

    pub fn on_region_drained(&self, cancelled: bool) -> (usize, usize) {
        self.total_drained.fetch_add(1, Ordering::Relaxed);
        if cancelled {
            self.total_cancelled.fetch_add(1, Ordering::Relaxed);
        }
        let regions = self.active_regions.fetch_sub(1, Ordering::SeqCst) - 1;
        let tasks = self.live_tasks.load(Ordering::SeqCst);
        (regions, tasks)
    }

    #[must_use]
    pub fn snapshot(&self) -> RegionCountersSnapshot {
        RegionCountersSnapshot {
            active_regions: self.active_regions.load(Ordering::SeqCst),
            live_tasks: self.live_tasks.load(Ordering::SeqCst),
            total_opened: self.total_opened.load(Ordering::SeqCst),
            total_drained: self.total_drained.load(Ordering::SeqCst),
            total_cancelled: self.total_cancelled.load(Ordering::SeqCst),
        }
    }
}

/// One structured runtime-plane lifecycle record for LSP or Lake work.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeEvent {
    pub subsystem: &'static str,
    pub event: &'static str,
    pub request_id: u64,
    pub target: String,
    pub version: Option<i64>,
    pub generation: u64,
    pub region_id: String,
    pub cancellation_outcome: &'static str,
    pub cache_hit: Option<bool>,
    pub active_regions: usize,
    pub live_tasks: usize,
    pub authoritative_publication: bool,
    pub detail: Option<String>,
}

impl RuntimeEvent {
    #[must_use]
    pub fn to_json_line(&self) -> String {
        let version = self
            .version
            .map_or_else(|| "null".to_owned(), |value| value.to_string());
        let cache_hit = self
            .cache_hit
            .map_or_else(|| "null".to_owned(), |value| value.to_string());
        let detail = self
            .detail
            .as_deref()
            .map_or_else(|| "null".to_owned(), fln_server::json_string);
        format!(
            "{{\"schema\":{},\"subsystem\":{},\"event\":{},\"requestId\":{},\"target\":{},\"version\":{version},\"generation\":{},\"regionId\":{},\"cancellationOutcome\":{},\"cacheHit\":{cache_hit},\"activeRegions\":{},\"liveTasks\":{},\"authoritativePublication\":{},\"detail\":{detail}}}",
            fln_server::json_string(RUNTIME_EVENT_SCHEMA),
            fln_server::json_string(self.subsystem),
            fln_server::json_string(self.event),
            self.request_id,
            fln_server::json_string(&self.target),
            self.generation,
            fln_server::json_string(&self.region_id),
            fln_server::json_string(self.cancellation_outcome),
            self.active_regions,
            self.live_tasks,
            self.authoritative_publication,
        )
    }
}

/// Optional structured log sink: captures events in memory (for tests) and/or
/// appends NDJSON lines to `FLN_RUNTIME_EVENT_LOG` when configured.
#[derive(Clone, Default)]
pub struct RuntimeEventSink {
    memory: Option<Arc<Mutex<Vec<RuntimeEvent>>>>,
    file_path: Option<PathBuf>,
    file_lock: Arc<Mutex<()>>,
}

impl RuntimeEventSink {
    #[must_use]
    pub fn from_env() -> Self {
        let file_path = std::env::var_os(RUNTIME_EVENT_LOG_ENV)
            .filter(|value| !value.is_empty())
            .map(PathBuf::from);
        Self {
            memory: None,
            file_path,
            file_lock: Arc::new(Mutex::new(())),
        }
    }

    #[must_use]
    pub fn in_memory() -> (Self, Arc<Mutex<Vec<RuntimeEvent>>>) {
        let buffer = Arc::new(Mutex::new(Vec::new()));
        (
            Self {
                memory: Some(Arc::clone(&buffer)),
                file_path: None,
                file_lock: Arc::new(Mutex::new(())),
            },
            buffer,
        )
    }

    pub fn record(&self, event: RuntimeEvent) {
        if let Some(path) = &self.file_path {
            let _guard = self.file_lock.lock();
            if let Ok(mut file) = std::fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(path)
            {
                let _ = writeln!(file, "{}", event.to_json_line());
            }
        }
        if let Some(memory) = &self.memory
            && let Ok(mut events) = memory.lock()
        {
            events.push(event);
        }
    }
}

/// Construct a stack-calibrated multi-threaded `asupersync` runtime for
/// production LSP proof-checking or Lake compilation.
pub fn build_effect_runtime(
    name_prefix: &str,
    worker_threads: usize,
    stack_bytes: usize,
) -> Result<Runtime, String> {
    RuntimeBuilder::multi_thread()
        .worker_threads(worker_threads.max(1))
        .thread_stack_size(stack_bytes)
        .thread_name_prefix(name_prefix)
        .build()
        .map_err(|error| format!("could not build asupersync runtime `{name_prefix}`: {error}"))
}

/// Gracefully shut down an owned `asupersync` runtime with a bounded drain.
pub fn shutdown_runtime(runtime: Runtime) {
    let _ = runtime.shutdown_timeout(Duration::from_secs(5));
}

/// Cancel a child region using the structured `asupersync` cancellation reason.
pub fn cancel_reason(message: &'static str) -> CancelReason {
    CancelReason::user(message)
}

/// Frame delivered from the live LSP input reader into the `asupersync` channel.
pub type IncomingFrame = Result<Option<Vec<u8>>, io::Error>;

/// Shared incoming message inbox bridging a live `BufRead` LSP stream into both
/// `fln_server::dispatch::MessageSource` and `lsp::Checker`'s active-check
/// `asupersync` select loop.
pub struct IncomingTransport {
    rx: mpsc::Receiver<IncomingFrame>,
    deferred: VecDeque<IncomingFrame>,
    eof: bool,
}

impl IncomingTransport {
    /// Start an owned stdin/stream frame reader feeding a bounded `asupersync`
    /// MPSC channel so the server can observe superseding `didChange`/`didClose`
    /// messages while a proof check is actively running.
    pub fn spawn_reader<R: BufRead + Send + 'static>(
        mut reader: R,
    ) -> io::Result<(Arc<Mutex<Self>>, std::thread::JoinHandle<()>)> {
        let (tx, rx) = mpsc::channel::<IncomingFrame>(256);
        let handle = std::thread::Builder::new()
            .name("fln-lsp-stdin-reader".to_owned())
            .spawn(move || {
                loop {
                    let item = fln_server::transport::read_message(&mut reader);
                    let stop = matches!(&item, Ok(None) | Err(_));
                    let mut pending = item;
                    loop {
                        match tx.try_send(pending) {
                            Ok(()) => break,
                            Err(mpsc::SendError::Full(returned)) => {
                                pending = returned;
                                std::thread::sleep(Duration::from_millis(1));
                            }
                            Err(
                                mpsc::SendError::Disconnected(_) | mpsc::SendError::Cancelled(_),
                            ) => {
                                return;
                            }
                        }
                    }
                    if stop {
                        return;
                    }
                }
            })?;
        Ok((
            Arc::new(Mutex::new(Self {
                rx,
                deferred: VecDeque::new(),
                eof: false,
            })),
            handle,
        ))
    }

    pub fn push_deferred(&mut self, frame: IncomingFrame) {
        self.deferred.push_back(frame);
    }

    pub fn pop_deferred(&mut self) -> Option<IncomingFrame> {
        self.deferred.pop_front()
    }

    pub fn receiver_mut(&mut self) -> &mut mpsc::Receiver<IncomingFrame> {
        &mut self.rx
    }

    /// Block until the next framed LSP message is available, preferring any
    /// already-buffered FIFO frames pushed during an earlier active check.
    pub fn next_frame(&mut self, runtime: &Runtime) -> io::Result<Option<Vec<u8>>> {
        if let Some(frame) = self.deferred.pop_front() {
            return match frame {
                Ok(None) => {
                    self.eof = true;
                    Ok(None)
                }
                other => other,
            };
        }
        if self.eof {
            return Ok(None);
        }
        let received = runtime.block_on(async {
            let cx = Cx::current().expect("asupersync runtime Cx");
            self.rx.recv(&cx).await
        });
        match received {
            Ok(Ok(Some(bytes))) => Ok(Some(bytes)),
            Ok(Ok(None)) | Err(_) => {
                self.eof = true;
                Ok(None)
            }
            Ok(Err(error)) => {
                self.eof = true;
                Err(error)
            }
        }
    }
}

/// `fln_server::dispatch::MessageSource` adapter backed by [`IncomingTransport`]
/// and an owned `asupersync` [`Runtime`] handle.
pub struct AsupersyncMessageSource {
    transport: Arc<Mutex<IncomingTransport>>,
    runtime: Arc<Runtime>,
}

impl AsupersyncMessageSource {
    #[must_use]
    pub fn new(transport: Arc<Mutex<IncomingTransport>>, runtime: Arc<Runtime>) -> Self {
        Self { transport, runtime }
    }
}

impl MessageSource for AsupersyncMessageSource {
    fn read_message(&mut self) -> io::Result<Option<Vec<u8>>> {
        let mut guard = self
            .transport
            .lock()
            .map_err(|_| io::Error::other("LSP incoming transport lock poisoned"))?;
        guard.next_frame(&self.runtime)
    }
}
