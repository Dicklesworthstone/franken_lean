//! Real installed-transport LSP and Lake `asupersync` active-cancellation E2E
//! verification (bead `fln-otk7`).
//!
//! No mocks, no alternate source engines, and no test-only sleeps in production:
//! - Drives the real compiled `fln serve-lsp` and `lean --server` binaries over
//!   live stdio Content-Length pipes with `FLN_RUNTIME_EVENT_LOG` NDJSON capture.
//! - Exercises real multi-command proofs cancelled actively via `didChange` and
//!   `didClose`, goal inspection before and after recovery, concurrent multi-file
//!   edits, warm cache hit vs cancellation, error propagation, `$/cancelRequest`,
//!   and real `lake build` region cancellation + artifact/lock cleanliness + recovery.
#![forbid(unsafe_code)]

use std::io::{BufReader, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::mpsc::{Receiver, channel};
use std::time::{Duration, Instant};

use fln_cli::runtime_plane::{RUNTIME_EVENT_LOG_ENV, RegionCounters, RuntimeEventSink};
use fln_server::{json_string as q, transport};

static NEXT: AtomicUsize = AtomicUsize::new(0);

fn scratch_dir(tag: &str) -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fln-otk7-{tag}-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&path).expect("create scratch dir");
    path
}

fn file_uri(path: &Path) -> String {
    let text = path.to_str().expect("UTF-8 path").replace('\\', "/");
    if text.starts_with('/') {
        format!("file://{text}")
    } else {
        format!("file:///{text}")
    }
}

fn open_msg(uri: &str, version: i64, text: &str) -> String {
    format!(
        "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{{\"textDocument\":{{\"uri\":{},\"languageId\":\"lean4\",\"version\":{version},\"text\":{}}}}}}}",
        q(uri),
        q(text)
    )
}

fn change_msg(uri: &str, version: i64, text: &str) -> String {
    format!(
        "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\",\"params\":{{\"textDocument\":{{\"uri\":{},\"version\":{version}}},\"contentChanges\":[{{\"text\":{}}}]}}}}",
        q(uri),
        q(text)
    )
}

fn close_msg(uri: &str) -> String {
    format!(
        "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didClose\",\"params\":{{\"textDocument\":{{\"uri\":{}}}}}}}",
        q(uri)
    )
}

fn goal_msg(id: &str, uri: &str, line: usize, character: usize) -> String {
    format!(
        "{{\"jsonrpc\":\"2.0\",\"id\":{},\"method\":\"$/lean/plainGoal\",\"params\":{{\"textDocument\":{{\"uri\":{}}},\"position\":{{\"line\":{line},\"character\":{character}}}}}}}",
        q(id),
        q(uri)
    )
}

fn wait_msg(id: &str, uri: &str, version: i64) -> String {
    format!(
        "{{\"jsonrpc\":\"2.0\",\"id\":{},\"method\":\"textDocument/waitForDiagnostics\",\"params\":{{\"uri\":{},\"version\":{version}}}}}",
        q(id),
        q(uri)
    )
}

fn cancel_req_msg(id: &str) -> String {
    format!(
        "{{\"jsonrpc\":\"2.0\",\"method\":\"$/cancelRequest\",\"params\":{{\"id\":{}}}}}",
        q(id)
    )
}

/// Real multi-command Lean proof large enough that elaborating + checking it
/// takes tens to hundreds of milliseconds, ending with an intentional error on
/// the final declaration so we can prove stale v2 diagnostics never leak if v2
/// is actively cancelled before completion.
fn large_real_proof_with_trailing_error(theorems: usize) -> String {
    let mut source = String::from(
        "structure PairBox where\n  left : Nat\n  right : Nat\n@[simp] def bump (n : Nat) : Nat := n\n",
    );
    for i in 0..theorems {
        source.push_str(&format!(
            "theorem heavy_{i} (P Q : Prop) (hp : P) (hq : Q) : And P Q := by\n  constructor\n  exact hp\n  exact hq\n"
        ));
    }
    source.push_str("def intentional_stale_v2_error : Nat := missing_stale_v2_symbol\n");
    source
}

#[derive(Clone, Copy)]
enum ServerDoor {
    FlnServeLsp,
    LeanServer,
}

impl ServerDoor {
    const fn label(self) -> &'static str {
        match self {
            Self::FlnServeLsp => "fln",
            Self::LeanServer => "lean",
        }
    }

    fn command(self) -> Command {
        match self {
            Self::FlnServeLsp => {
                let mut cmd = Command::new(env!("CARGO_BIN_EXE_fln"));
                cmd.arg("serve-lsp");
                cmd
            }
            Self::LeanServer => {
                let mut cmd = Command::new(env!("CARGO_BIN_EXE_lean"));
                cmd.arg("--server");
                cmd
            }
        }
    }
}

struct LiveLsp {
    child: Child,
    input: ChildStdin,
    output: Receiver<String>,
    all_messages: Vec<String>,
    log_path: PathBuf,
}

impl LiveLsp {
    fn start(door: ServerDoor, log_path: PathBuf) -> Self {
        let mut child = door
            .command()
            .env(RUNTIME_EVENT_LOG_ENV, &log_path)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("spawn installed LSP server");
        let input = child.stdin.take().expect("stdin");
        let stdout = child.stdout.take().expect("stdout");
        let (tx, output) = channel();
        std::thread::spawn(move || {
            let mut reader = BufReader::new(stdout);
            while let Ok(Some(body)) = transport::read_message(&mut reader) {
                if tx
                    .send(String::from_utf8(body).expect("UTF-8 LSP"))
                    .is_err()
                {
                    break;
                }
            }
        });
        let mut session = Self {
            child,
            input,
            output,
            all_messages: Vec::new(),
            log_path,
        };
        session.send(r#"{"jsonrpc":"2.0","id":"init","method":"initialize","params":{}}"#);
        session.wait_for(|m| m.contains("\"id\":\"init\""));
        session.send(r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#);
        session
    }

    fn send(&mut self, body: &str) {
        let mut frame = Vec::new();
        transport::write_message(&mut frame, body.as_bytes()).expect("frame message");
        self.input.write_all(&frame).expect("write frame");
        self.input.flush().expect("flush stdin");
    }

    fn wait_for(&mut self, predicate: impl Fn(&str) -> bool) -> Vec<String> {
        let mut batch = Vec::new();
        let deadline = Instant::now() + Duration::from_secs(120);
        loop {
            let remaining = deadline.saturating_duration_since(Instant::now());
            let message = self.output.recv_timeout(remaining).unwrap_or_else(|err| {
                panic!("LSP timed out ({err}); saw: {:#?}", self.all_messages)
            });
            let matched = predicate(&message);
            self.all_messages.push(message.clone());
            batch.push(message);
            if matched {
                return batch;
            }
        }
    }

    fn finish(mut self) -> (Vec<String>, Vec<String>) {
        self.send(r#"{"jsonrpc":"2.0","id":"end","method":"shutdown"}"#);
        self.wait_for(|m| m.contains("\"id\":\"end\""));
        self.send(r#"{"jsonrpc":"2.0","method":"exit"}"#);
        drop(self.input);
        let mut stderr = String::new();
        self.child
            .stderr
            .take()
            .expect("stderr")
            .read_to_string(&mut stderr)
            .expect("read stderr");
        let status = self.child.wait().expect("wait child");
        assert!(status.success(), "server failed: {stderr}");
        assert!(stderr.is_empty(), "server leaked stderr: {stderr}");
        let log_lines = std::fs::read_to_string(&self.log_path)
            .unwrap_or_default()
            .lines()
            .map(str::to_owned)
            .collect();
        (self.all_messages, log_lines)
    }
}

#[test]
fn real_installed_lsp_active_cancellation_goal_and_recovery() {
    let dir = scratch_dir("lsp-active-cancel");
    let uri = file_uri(&dir.join("ActiveCancel.lean"));

    let v1_unfinished = "theorem pending (P : Prop) (h : P) : P := by";
    let v2_slow = large_real_proof_with_trailing_error(160);
    let v3_recovered = "theorem recovered (P Q : Prop) (hp : P) (hq : Q) : P := by\n  exact hp\ntheorem nextGoal (A : Prop) (ha : A) : A := by";

    for door in [ServerDoor::FlnServeLsp, ServerDoor::LeanServer] {
        let label = door.label();
        let log_path = dir.join(format!("runtime_{label}.ndjson"));
        let mut lsp = LiveLsp::start(door, log_path);

        // 1. Open v1 (checked local proof with open goal) and query its actual goal.
        lsp.send(&open_msg(&uri, 1, v1_unfinished));
        lsp.wait_for(|m| m.contains("$/lean/fileProgress") && m.contains("\"processing\":[]"));
        lsp.send(&goal_msg("goal-v1", &uri, 0, v1_unfinished.len()));
        let goal_v1 = lsp.wait_for(|m| m.contains("\"id\":\"goal-v1\""));
        assert!(
            goal_v1.last().unwrap().contains("P : Prop\\nh : P\\n⊢ P"),
            "{label} v1 goal mismatch: {goal_v1:#?}"
        );

        // 2. Send slow v2 and wait for fileProgress(kind:1) proving v2's ChildRegion
        // is actively executing, then IMMEDIATELY supersede with v3!
        lsp.send(&change_msg(&uri, 2, &v2_slow));
        lsp.wait_for(|m| m.contains("$/lean/fileProgress") && m.contains("\"kind\":1"));
        lsp.send(&change_msg(&uri, 3, v3_recovered));

        // 3. Wait for v3 diagnostics & inspect v3's real goal.
        lsp.send(&wait_msg("wait-v3", &uri, 3));
        let wait_v3 = lsp.wait_for(|m| m.contains("\"id\":\"wait-v3\""));
        assert!(
            wait_v3.last().unwrap().contains("\"result\":{}"),
            "{label} wait-v3 failed: {wait_v3:#?}"
        );

        lsp.send(&goal_msg("goal-v3", &uri, 2, 46));
        let goal_v3 = lsp.wait_for(|m| m.contains("\"id\":\"goal-v3\""));
        assert!(
            goal_v3.last().unwrap().contains("A : Prop\\nha : A\\n⊢ A"),
            "{label} v3 goal mismatch: {goal_v3:#?}"
        );

        let (messages, logs) = lsp.finish();

        // No stale v2 error diagnostic may ever appear on the wire!
        assert!(
            !messages
                .iter()
                .any(|m| m.contains("missing_stale_v2_symbol")
                    || m.contains("intentional_stale_v2_error")),
            "{label} leaked stale cancelled v2 diagnostics: {messages:#?}"
        );

        // Structured runtime logs must prove active cancellation, zero leaked
        // regions/tasks, non-authoritative cancelled region, and fresh v3 completion.
        let v2_cancel = logs.iter().find(|line| {
            line.contains("\"event\":\"region_cancelled_and_drained\"")
                && line.contains("\"version\":2")
        });
        let v2_cancel = v2_cancel.unwrap_or_else(|| {
            panic!(
                "{label} missing v2 active cancellation log entry; logs:\n{}",
                logs.join("\n")
            )
        });
        assert!(
            v2_cancel.contains("\"cancellationOutcome\":\"cancelled_active\""),
            "{label} expected active mid-check cancellation on v2, got: {v2_cancel}"
        );
        assert!(
            v2_cancel.contains("\"activeRegions\":0") && v2_cancel.contains("\"liveTasks\":0"),
            "{label} v2 region did not drain cleanly: {v2_cancel}"
        );
        assert!(
            v2_cancel.contains("\"authoritativePublication\":false"),
            "{label} cancelled v2 must never claim publication authority: {v2_cancel}"
        );

        let v3_done = logs.iter().find(|line| {
            line.contains("\"event\":\"region_completed\"") && line.contains("\"version\":3")
        });
        let v3_done = v3_done.unwrap_or_else(|| {
            panic!(
                "{label} missing v3 completion log entry; logs:\n{}",
                logs.join("\n")
            )
        });
        assert!(
            v3_done.contains("\"activeRegions\":0") && v3_done.contains("\"liveTasks\":0"),
            "{label} v3 region did not drain cleanly: {v3_done}"
        );
    }
}

#[test]
fn real_lsp_concurrent_edits_cache_hit_error_propagation_close_and_cancel_request() {
    let dir = scratch_dir("lsp-concurrent-matrix");
    let uri_a = file_uri(&dir.join("FileA.lean"));
    let uri_b = file_uri(&dir.join("FileB.lean"));
    let log_path = dir.join("runtime_matrix.ndjson");

    let mut lsp = LiveLsp::start(ServerDoor::FlnServeLsp, log_path);

    // 1. Concurrent edits: open slow A v1, immediately open B v1 + supersede A v2 while A v1 is active.
    let slow_a = large_real_proof_with_trailing_error(140);
    lsp.send(&open_msg(&uri_a, 1, &slow_a));
    lsp.wait_for(|m| m.contains("$/lean/fileProgress") && m.contains("\"kind\":1"));
    lsp.send(&open_msg(
        &uri_b,
        1,
        "def bOk : Nat := 11\ntheorem bThm : bOk = 11 := by rfl",
    ));
    lsp.send(&change_msg(
        &uri_a,
        2,
        "def aOk : Nat := 22\ntheorem aThm : aOk = 22 := by rfl",
    ));
    lsp.send(&wait_msg("wait-b1", &uri_b, 1));
    lsp.send(&wait_msg("wait-a2", &uri_a, 2));
    lsp.wait_for(|m| m.contains("\"id\":\"wait-a2\""));

    // 2. Warm cache hit on textless didSave of A v2 (same checked source => reusedModules: 1, cacheHit: true).
    lsp.send(&format!(
        "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didSave\",\"params\":{{\"textDocument\":{{\"uri\":{}}}}}}}",
        q(&uri_a)
    ));
    lsp.wait_for(|m| {
        m.contains("$/frankenLean/sourceCheck")
            && m.contains(&q(&uri_a))
            && m.contains("\"reusedModules\":1")
    });

    // 3. Error propagation + recovery on A (v3 broken -> diagnostic error, v4 fixed -> clean).
    lsp.send(&change_msg(
        &uri_a,
        3,
        "def brokenA : Nat := nonexistent_ident",
    ));
    lsp.send(&wait_msg("wait-a3", &uri_a, 3));
    let err_batch = lsp.wait_for(|m| m.contains("\"id\":\"wait-a3\""));
    assert!(
        err_batch
            .iter()
            .any(|m| m.contains("publishDiagnostics") && m.contains("\"diagnostics\":[{")),
        "expected propagated error diagnostic for A v3: {err_batch:#?}"
    );

    lsp.send(&change_msg(&uri_a, 4, "def fixedA : Nat := 99"));
    lsp.send(&wait_msg("wait-a4", &uri_a, 4));
    lsp.wait_for(|m| m.contains("\"id\":\"wait-a4\""));

    // 4. $/cancelRequest cancels an outstanding waitForDiagnostics for a future version.
    lsp.send(&wait_msg("wait-future", &uri_a, 99));
    lsp.send(&cancel_req_msg("wait-future"));
    let cancelled_wait = lsp.wait_for(|m| m.contains("\"id\":\"wait-future\""));
    assert!(
        cancelled_wait.last().unwrap().contains("-32800"),
        "expected LSP RequestCancelled (-32800), got: {cancelled_wait:#?}"
    );

    // 5. didClose cancels an active slow check on A v5 cleanly.
    lsp.send(&change_msg(&uri_a, 5, &slow_a));
    lsp.wait_for(|m| m.contains("$/lean/fileProgress") && m.contains("\"kind\":1"));
    lsp.send(&close_msg(&uri_a));

    let (messages, logs) = lsp.finish();

    assert!(
        !messages
            .iter()
            .any(|m| m.contains("missing_stale_v2_symbol")),
        "stale cancelled diagnostics leaked: {messages:#?}"
    );
    assert!(
        logs.iter().any(|line| line.contains("\"cacheHit\":true")),
        "expected at least one recorded cacheHit:true event; logs:\n{}",
        logs.join("\n")
    );
    assert!(
        logs.iter().any(
            |line| line.contains("\"event\":\"region_cancelled_and_drained\"")
                && line.contains("\"version\":1")
        ),
        "expected A v1 active cancellation during concurrent B edit; logs:\n{}",
        logs.join("\n")
    );
    assert!(
        logs.iter().any(
            |line| line.contains("\"event\":\"region_cancelled_and_drained\"")
                && line.contains("\"version\":5")
        ),
        "expected A v5 active cancellation on didClose; logs:\n{}",
        logs.join("\n")
    );
    // Every terminal region event must report 0 active regions and 0 live tasks.
    for line in &logs {
        if line.contains("\"event\":\"region_completed\"")
            || line.contains("\"event\":\"region_cancelled_and_drained\"")
            || line.contains("\"event\":\"region_failed\"")
        {
            assert!(
                line.contains("\"activeRegions\":0") && line.contains("\"liveTasks\":0"),
                "leaked region/task resource count in log: {line}"
            );
        }
    }
}

#[test]
fn real_lake_build_asupersync_region_cancellation_drains_and_recovers() {
    let root = scratch_dir("lake-cancel");
    std::fs::write(
        root.join("lakefile.toml"),
        "name = \"cancel_demo\"\n\n[[lean_lib]]\nname = \"CancelDemo\"\n",
    )
    .expect("write lakefile.toml");

    // Multi-module package with real theorems so compilation runs inside the
    // asupersync ChildRegion long enough to observe active cancellation.
    let mut dep_src = String::from("prelude\n");
    for i in 0..80 {
        dep_src.push_str(&format!(
            "def dep_{i}.{{u}} {{A : Sort u}} (x : A) : A := x\n"
        ));
    }
    std::fs::create_dir_all(root.join("CancelDemo")).expect("mkdir CancelDemo");
    std::fs::write(root.join("CancelDemo").join("Dep.lean"), &dep_src).expect("write Dep.lean");
    let mut main_src = String::from("prelude\nimport CancelDemo.Dep\n");
    for i in 0..80 {
        main_src.push_str(&format!(
            "def use_{i}.{{u}} {{A : Sort u}} (x : A) : A := dep_{i} x\n"
        ));
    }
    std::fs::write(root.join("CancelDemo.lean"), &main_src).expect("write CancelDemo.lean");

    let counters = std::sync::Arc::new(RegionCounters::new());
    let (sink, events_buf) = RuntimeEventSink::in_memory();

    // 1. Start real Lake build inside an owned asupersync ChildRegion and trigger
    // cancellation once the region is open and running.
    let (cancel_tx, cancel_rx) = asupersync::channel::oneshot::channel::<()>();
    let events_watcher = std::sync::Arc::clone(&events_buf);
    let trigger = std::thread::spawn(move || {
        let deadline = Instant::now() + Duration::from_secs(30);
        while Instant::now() < deadline {
            if events_watcher
                .lock()
                .expect("events lock")
                .iter()
                .any(|e| e.subsystem == "lake" && e.event == "region_opened")
            {
                let _ = cancel_tx.send_blocking(());
                return;
            }
            std::thread::sleep(Duration::from_millis(2));
        }
    });

    let cancelled_out = fln_cli::run_lake_build_in_region(
        root.clone(),
        vec!["+CancelDemo:olean".to_owned()],
        true,
        std::num::NonZeroUsize::MIN,
        Some(cancel_rx),
        &counters,
        &sink,
    );
    trigger.join().expect("join cancel trigger");

    assert_ne!(
        cancelled_out.exit_code, 0,
        "cancelled Lake build must not exit 0: stdout={} stderr={}",
        cancelled_out.stdout, cancelled_out.stderr
    );
    let snap_after_cancel = counters.snapshot();
    assert_eq!(
        snap_after_cancel.active_regions, 0,
        "lake build leaked active region: {snap_after_cancel:?}"
    );
    assert_eq!(
        snap_after_cancel.live_tasks, 0,
        "lake build leaked live task: {snap_after_cancel:?}"
    );
    assert_eq!(snap_after_cancel.total_opened, 1);
    assert_eq!(snap_after_cancel.total_drained, 1);
    assert_eq!(snap_after_cancel.total_cancelled, 1);

    // No .olean artifact or stale build lock may exist after cancellation!
    let build_lib = root.join(".lake").join("build").join("lib").join("lean");
    assert!(
        !build_lib.join("CancelDemo.olean").exists(),
        "cancelled build published stale CancelDemo.olean"
    );
    assert!(
        !build_lib.join(".fln-olean-build.lock").exists(),
        "cancelled build leaked .fln-olean-build.lock"
    );

    // 2. Subsequent fresh Lake build in a new ChildRegion recovers cleanly!
    let recovered_out = fln_cli::run_lake_build_in_region(
        root.clone(),
        vec!["+CancelDemo:olean".to_owned()],
        true,
        std::num::NonZeroUsize::MIN,
        None,
        &counters,
        &sink,
    );
    assert_eq!(
        recovered_out.exit_code, 0,
        "recovered Lake build failed: stdout={} stderr={}",
        recovered_out.stdout, recovered_out.stderr
    );
    assert!(
        build_lib.join("CancelDemo.olean").is_file(),
        "recovered build did not publish CancelDemo.olean"
    );
    assert!(
        !build_lib.join(".fln-olean-build.lock").exists(),
        "recovered build left build lock behind"
    );

    let final_snap = counters.snapshot();
    assert_eq!(final_snap.active_regions, 0);
    assert_eq!(final_snap.live_tasks, 0);
    assert_eq!(final_snap.total_opened, 2);
    assert_eq!(final_snap.total_drained, 2);
    assert_eq!(final_snap.total_cancelled, 1);

    let events = events_buf.lock().expect("events lock");
    assert!(events.iter().any(|e| {
        e.subsystem == "lake"
            && e.event == "region_cancelled_and_drained"
            && !e.authoritative_publication
            && e.active_regions == 0
            && e.live_tasks == 0
    }));
    assert!(events.iter().any(|e| {
        e.subsystem == "lake"
            && e.event == "region_completed"
            && e.authoritative_publication
            && e.active_regions == 0
            && e.live_tasks == 0
    }));
}
