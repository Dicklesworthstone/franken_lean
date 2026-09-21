#![forbid(unsafe_code)]

//! Client-watched disk changes cross the actual installed server and real filesystem.
use super::*;
use std::io::Read;
use std::process::{Child, ChildStdin};
use std::sync::mpsc::{Receiver, channel};
use std::thread::JoinHandle;
use std::time::{Duration, Instant};

struct Live {
    child: Child,
    input: Option<ChildStdin>,
    output: Receiver<String>,
    reader: Option<JoinHandle<()>>,
    stderr: Option<JoinHandle<Vec<u8>>>,
    messages: Vec<String>,
}
impl Live {
    fn start(binary: &str, args: &[&str], decline: bool) -> Self {
        let mut child = Command::new(binary)
            .args(args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        let input = child.stdin.take().unwrap();
        let stdout = child.stdout.take().unwrap();
        let mut stderr = child.stderr.take().unwrap();
        let (send, output) = channel();
        let reader = std::thread::spawn(move || {
            let mut reader = BufReader::new(stdout);
            while let Ok(Some(bytes)) = transport::read_message(&mut reader) {
                if send.send(String::from_utf8(bytes).unwrap()).is_err() {
                    break;
                }
            }
        });
        let stderr = std::thread::spawn(move || {
            let mut bytes = Vec::new();
            stderr.read_to_end(&mut bytes).unwrap();
            bytes
        });
        let mut live = Self {
            child,
            input: Some(input),
            output,
            reader: Some(reader),
            stderr: Some(stderr),
            messages: Vec::new(),
        };
        live.send(r#"{"jsonrpc":"2.0","id":0,"method":"initialize","params":{"capabilities":{"workspace":{"didChangeWatchedFiles":{"dynamicRegistration":true}}}}}"#);
        live.until(|m| m.contains("\"id\":0,") && m.contains("\"result\""));
        assert!(
            !live
                .messages
                .iter()
                .any(|m| m.contains("client/registerCapability"))
        );
        live.send(r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#);
        let registration = live.until(|m| m.contains("client/registerCapability"));
        assert!(registration.contains("**/*.lean") && registration.contains("\"kind\":7"));
        let result = if decline {
            r#""error":{"code":-32601,"message":"watching disabled"}"#
        } else {
            r#""result":null"#
        };
        live.send(&format!(
            r#"{{"jsonrpc":"2.0","id":"frankenLean/source-watch/1",{result}}}"#
        ));
        live
    }
    fn send(&mut self, body: &str) {
        let input = self.input.as_mut().unwrap();
        transport::write_message(input, body.as_bytes()).unwrap();
        input.flush().unwrap();
    }
    fn until(&mut self, predicate: impl Fn(&str) -> bool) -> String {
        let deadline = Instant::now() + Duration::from_secs(45);
        loop {
            let message = self
                .output
                .recv_timeout(deadline.saturating_duration_since(Instant::now()))
                .unwrap_or_else(|error| {
                    panic!(
                        "server did not reach the protocol barrier: {error}; {:#?}",
                        self.messages
                    )
                });
            let done = predicate(&message);
            self.messages.push(message.clone());
            if done {
                return message;
            }
        }
    }
    fn barrier(&mut self, uri: &str, id: usize) -> String {
        self.send(&wait(uri, 1, id));
        self.until(|m| m.contains(&format!("\"id\":{id},")))
    }
    fn changed(&mut self, uri: &str, kind: usize) {
        self.send(&notify(
            "workspace/didChangeWatchedFiles",
            format!(r#"{{"changes":[{{"uri":{},"type":{kind}}}]}}"#, q(uri)),
        ));
    }
    fn finish(mut self) -> Vec<String> {
        self.send(r#"{"jsonrpc":"2.0","id":999,"method":"shutdown"}"#);
        self.until(|m| m.contains("\"id\":999,"));
        self.send(r#"{"jsonrpc":"2.0","method":"exit"}"#);
        self.input.take();
        let deadline = Instant::now() + Duration::from_secs(10);
        loop {
            if let Some(status) = self.child.try_wait().unwrap() {
                assert!(status.success());
                break;
            }
            assert!(Instant::now() < deadline, "server failed to exit");
            std::thread::sleep(Duration::from_millis(10));
        }
        self.reader.take().unwrap().join().unwrap();
        self.messages.extend(self.output.try_iter());
        let stderr = self.stderr.take().unwrap().join().unwrap();
        assert!(stderr.is_empty(), "{}", String::from_utf8_lossy(&stderr));
        std::mem::take(&mut self.messages)
    }
}
impl Drop for Live {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
        self.input.take();
        if let Some(reader) = self.reader.take() {
            let _ = reader.join();
        }
        if let Some(stderr) = self.stderr.take() {
            let _ = stderr.join();
        }
    }
}
fn main_successes<'a>(messages: &'a [String], uri: &str) -> Vec<&'a str> {
    successes(messages)
        .into_iter()
        .filter(|m| m.contains(&q(uri)))
        .collect()
}

#[test]
fn both_installed_servers_refresh_closed_disk_dependencies_and_clear_repairs() {
    for (binary, args) in [
        (env!("CARGO_BIN_EXE_fln"), &["serve-lsp"][..]),
        (env!("CARGO_BIN_EXE_lean"), &["--server"][..]),
    ] {
        let root = scratch();
        let path = root.join("Lib.lean");
        std::fs::write(&path, "def value := 0").unwrap();
        let lib = uri(&path);
        let main = uri(&root.join("Main.lean"));
        let mut live = Live::start(binary, args, false);
        live.send(&open(
            &main,
            "import Lib\ntheorem use : value = 0 := by rfl",
        ));
        live.barrier(&main, 81);
        std::fs::write(&path, "def value := 1").unwrap();
        live.changed(&lib, 2);
        live.barrier(&main, 82);
        assert_eq!(
            errors(&live.messages, &main).len(),
            1,
            "{:#?}",
            live.messages
        );
        std::fs::write(&path, "def value := 0").unwrap();
        live.changed(&lib, 2);
        assert!(live.barrier(&main, 83).contains("\"result\":{}"));
        let messages = live.finish();
        assert_eq!(main_successes(&messages, &main).len(), 2, "{messages:#?}");
        assert_eq!(
            messages
                .iter()
                .filter(|m| m.contains("client/registerCapability"))
                .count(),
            1
        );
    }
}

#[test]
fn creation_and_directory_removal_recover_without_reopening_the_importer() {
    let root = scratch();
    let dir = root.join("Library");
    let backup = root.join("Library.backup");
    let path = dir.join("Values.lean");
    let main = uri(&root.join("Main.lean"));
    let mut live = Live::start(env!("CARGO_BIN_EXE_fln"), &["serve-lsp"], false);
    live.send(&open(
        &main,
        "import Library.Values\ntheorem use : value = 0 := by rfl",
    ));
    live.barrier(&main, 84);
    std::fs::create_dir(&dir).unwrap();
    std::fs::write(&path, "def value := 0").unwrap();
    live.changed(&uri(&path), 1);
    live.barrier(&main, 85);
    assert_eq!(
        main_successes(&live.messages, &main).len(),
        1,
        "{:#?}",
        live.messages
    );
    assert!(!backup.exists());
    std::fs::rename(&dir, &backup).unwrap();
    live.changed(&uri(&dir), 3);
    live.barrier(&main, 86);
    assert_eq!(
        errors(&live.messages, &main).len(),
        2,
        "{:#?}",
        live.messages
    );
    std::fs::rename(&backup, &dir).unwrap();
    live.changed(&uri(&path), 1);
    live.barrier(&main, 87);
    assert_eq!(main_successes(&live.finish(), &main).len(), 2);
}

#[test]
fn filesystem_hints_never_replace_open_source_or_unavailable_buffer_authority() {
    let root = scratch();
    let path = root.join("Lib.lean");
    std::fs::write(&path, "def value := 1").unwrap();
    let lib = uri(&path);
    let main = uri(&root.join("Main.lean"));
    let mut live = Live::start(env!("CARGO_BIN_EXE_fln"), &["serve-lsp"], false);
    live.send(&open(&lib, "def value := 0"));
    live.send(&open(
        &main,
        "import Lib\ntheorem use : value = 0 := by rfl",
    ));
    live.barrier(&main, 88);
    live.changed(&lib, 2);
    live.barrier(&main, 89);
    assert!(
        errors(&live.messages, &main).is_empty(),
        "{:#?}",
        live.messages
    );
    let before = main_successes(&live.messages, &main).len();
    live.send(&notify(
        "textDocument/didChange",
        format!(
            "{{\"textDocument\":{{\"uri\":{},\"version\":2}},\"contentChanges\":false}}",
            q(&lib)
        ),
    ));
    live.changed(&lib, 2);
    assert!(live.barrier(&main, 90).contains("\"error\""));
    assert_eq!(main_successes(&live.messages, &main).len(), before);
    assert!(
        live.finish()
            .iter()
            .any(|m| m.contains("disk fallback is forbidden"))
    );
}

#[test]
fn repeated_events_are_coalesced_and_malformed_batches_do_not_partially_recheck() {
    let root = scratch();
    let path = root.join("Lib.lean");
    std::fs::write(&path, "def value := 0").unwrap();
    let lib = uri(&path);
    let main = uri(&root.join("Main.lean"));
    let mut live = Live::start(env!("CARGO_BIN_EXE_fln"), &["serve-lsp"], false);
    live.send(&open(
        &main,
        "import Lib\ntheorem use : value = 0 := by rfl",
    ));
    live.barrier(&main, 91);
    let event = format!(r#"{{"uri":{},"type":2}}"#, q(&lib));
    live.send(&notify(
        "workspace/didChangeWatchedFiles",
        format!(r#"{{"changes":[{event},{event},{event}]}}"#),
    ));
    live.barrier(&main, 92);
    assert_eq!(main_successes(&live.messages, &main).len(), 2);
    live.changed(&uri(&root.join("Unrelated.lean")), 2);
    live.barrier(&main, 93);
    assert_eq!(main_successes(&live.messages, &main).len(), 2);
    std::fs::write(&path, "def value := 1").unwrap();
    live.send(&notify(
        "workspace/didChangeWatchedFiles",
        format!(r#"{{"changes":[{event},{{"uri":"bad","type":4}}]}}"#),
    ));
    live.barrier(&main, 94);
    assert!(errors(&live.messages, &main).is_empty());
    assert!(
        live.messages
            .iter()
            .any(|m| m.contains("event type must be"))
    );
    live.changed(&lib, 2);
    live.barrier(&main, 95);
    assert_eq!(errors(&live.finish(), &main).len(), 1);
}

#[test]
fn registration_refusal_preserves_editing_and_preconfigured_file_notifications() {
    let root = scratch();
    let path = root.join("Lib.lean");
    std::fs::write(&path, "def value := 0").unwrap();
    let main = uri(&root.join("Main.lean"));
    let mut live = Live::start(env!("CARGO_BIN_EXE_fln"), &["serve-lsp"], true);
    live.send(&open(
        &main,
        "import Lib\ntheorem use : value = 0 := by rfl",
    ));
    live.barrier(&main, 96);
    std::fs::write(&path, "def value := 1").unwrap();
    live.changed(&uri(&path), 2);
    live.barrier(&main, 97);
    let messages = live.finish();
    assert!(
        messages
            .iter()
            .any(|m| m.contains("declined Lean source file watching"))
    );
    assert_eq!(errors(&messages, &main).len(), 1);
    assert_eq!(main_successes(&messages, &main).len(), 1);
}
