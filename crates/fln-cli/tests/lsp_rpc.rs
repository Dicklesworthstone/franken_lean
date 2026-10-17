//! Installed editor RPC conversations use real native proofs and unsaved sources.
#![forbid(unsafe_code)]
use fln_server::transport::{read_message, write_message};
use std::io::{BufReader, Write};
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::mpsc::{self, Receiver};
use std::thread::JoinHandle;
use std::time::{Duration, Instant};
const URI: &str = "file:///FlnRpc.lean";
const SOURCE: &str = "theorem pending (P : Prop) (β : P) : P := by\r\n  exact β";
fn quote(s: &str) -> String {
    fln_server::json_string(s)
}
fn request(id: &str, method: &str, params: &str) -> String {
    format!(
        "{{\"jsonrpc\":\"2.0\",\"id\":{},\"method\":{},\"params\":{params}}}",
        quote(id),
        quote(method)
    )
}
fn notification(method: &str, params: &str) -> String {
    format!(
        "{{\"jsonrpc\":\"2.0\",\"method\":{},\"params\":{params}}}",
        quote(method)
    )
}
fn position(line: usize, column: usize) -> String {
    format!(
        r#"{{"textDocument":{{"uri":"{URI}"}},"position":{{"line":{line},"character":{column}}}}}"#
    )
}
fn call(id: &str, session: &str, method: &str, line: usize, column: usize) -> String {
    let at = position(line, column);
    let params = format!(
        "{{\"sessionId\":{},\"method\":{},\"params\":{at},{}",
        quote(session),
        quote(method),
        &at[1..]
    );
    request(id, "$/lean/rpc/call", &params)
}
fn extract_string<'a>(value: &'a str, key: &str) -> &'a str {
    value
        .split_once(&format!("\"{key}\":\""))
        .unwrap_or_else(|| panic!("missing {key}: {value}"))
        .1
        .split('"')
        .next()
        .unwrap()
}
struct Client {
    child: Child,
    input: ChildStdin,
    output: Receiver<std::io::Result<String>>,
    reader: Option<JoinHandle<()>>,
    log: Vec<String>,
}
impl Client {
    fn start(binary: &str, args: &[&str], format: &str) -> Self {
        let mut child = Command::new(binary)
            .args(args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()
            .unwrap();
        let input = child.stdin.take().unwrap();
        let stdout = child.stdout.take().unwrap();
        let (sender, output) = mpsc::sync_channel(1024);
        let reader = std::thread::spawn(move || {
            let mut stream = BufReader::new(stdout);
            loop {
                let message = match read_message(&mut stream) {
                    Ok(Some(bytes)) => String::from_utf8(bytes)
                        .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e)),
                    Ok(None) => break,
                    Err(e) => {
                        let _ = sender.try_send(Err(e));
                        break;
                    }
                };
                if sender.try_send(message).is_err() {
                    break;
                }
            }
        });
        let mut client = Self {
            child,
            input,
            output,
            reader: Some(reader),
            log: Vec::new(),
        };
        let init = client.exchange(
            "init",
            &request(
                "init",
                "initialize",
                &format!(r#"{{"capabilities":{{"lean":{{"rpcWireFormat":"{format}"}}}}}}"#),
            ),
        );
        assert!(
            init.contains("\"rpcProvider\":{\"rpcWireFormat\":\"v1\"}"),
            "{init}"
        );
        client.send(&notification("initialized", "{}"));
        client
    }
    fn send(&mut self, text: &str) {
        write_message(&mut self.input, text.as_bytes()).unwrap();
        self.input.flush().unwrap();
    }
    fn exchange(&mut self, id: &str, text: &str) -> String {
        self.send(text);
        let key = format!("\"id\":{},", quote(id));
        let deadline = Instant::now() + Duration::from_secs(40);
        loop {
            let remaining = deadline.saturating_duration_since(Instant::now());
            let message = self
                .output
                .recv_timeout(remaining)
                .unwrap_or_else(|e| panic!("{id}: {e}; transcript: {:?}", self.log))
                .unwrap();
            self.log.push(message.clone());
            if message.contains(&key) {
                return message;
            }
        }
    }
    fn open(&mut self, source: &str) {
        self.send(&notification(
            "textDocument/didOpen",
            &format!(
                r#"{{"textDocument":{{"uri":"{URI}","version":1,"text":{}}}}}"#,
                quote(source)
            ),
        ));
    }
    fn change(&mut self, version: usize, source: &str) {
        self.send(&notification("textDocument/didChange",
            &format!(r#"{{"textDocument":{{"uri":"{URI}","version":{version}}},"contentChanges":[{{"text":{}}}]}}"#, quote(source))));
    }
    fn connect(&mut self, id: &str) -> String {
        let response = self.exchange(
            id,
            &request(id, "$/lean/rpc/connect", &format!(r#"{{"uri":"{URI}"}}"#)),
        );
        let session = extract_string(&response, "sessionId").to_owned();
        session.parse::<u64>().unwrap();
        session
    }
    fn finish(mut self) {
        assert!(
            self.exchange("end", &request("end", "shutdown", "null"))
                .contains("\"result\":null")
        );
        self.send(&notification("exit", "null"));
        let deadline = Instant::now() + Duration::from_secs(10);
        loop {
            if let Some(status) = self.child.try_wait().unwrap() {
                assert!(status.success());
                break;
            }
            assert!(Instant::now() < deadline, "server did not exit");
            std::thread::sleep(Duration::from_millis(10));
        }
    }
}
impl Drop for Client {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
        if let Some(reader) = self.reader.take() {
            let _ = reader.join();
        }
    }
}

#[test]
fn both_doors_and_wire_formats_show_native_goals_terms_and_current_edits() {
    for (binary, args) in [
        (env!("CARGO_BIN_EXE_fln"), &["serve-lsp"][..]),
        (env!("CARGO_BIN_EXE_lean"), &["--server"][..]),
    ] {
        for (format, key) in [("v0", "p"), ("v1", "__rpcref")] {
            let mut client = Client::start(binary, args, format);
            client.open(SOURCE);
            let session = client.connect("connect");
            let goals = client.exchange(
                "goals",
                &call("goals", &session, "Lean.Widget.getInteractiveGoals", 1, 2),
            );
            assert!(goals.contains("\"names\":[\"β\"]"), "{goals}");
            assert!(goals.contains("\"type\":{\"text\":\"P\"}"), "{goals}");
            assert!(!extract_string(&goals, "mvarId").is_empty());
            let reference = extract_string(&goals, key);
            let release = format!(
                r#"{{"uri":"{URI}","sessionId":"{session}","refs":[{{"{key}":"{reference}"}}]}}"#
            );
            client.send(&notification("$/lean/rpc/release", &release));
            let term = client.exchange(
                "term",
                &call("term", &session, "Lean.Widget.getInteractiveTermGoal", 1, 8),
            );
            assert!(term.contains("\"term\":"), "{term}");
            assert!(
                term.contains("\"end\":{\"line\":1,\"character\":9}"),
                "{term}"
            );
            client.send(&notification(
                "$/lean/rpc/keepAlive",
                &format!(r#"{{"uri":"{URI}","sessionId":"{session}"}}"#),
            ));
            client.change(
                2,
                "theorem pending (Q : Prop) (β : Q) : Q := by\r\n  exact β",
            );
            let changed = client.exchange(
                "changed",
                &call("changed", &session, "Lean.Widget.getInteractiveGoals", 1, 2),
            );
            assert!(changed.contains("\"text\":\"Q\""), "{changed}");
            assert!(!changed.contains("\"text\":\"P\""));
            client.send(&notification(
                "textDocument/didChange",
                &format!(
                    r#"{{"textDocument":{{"uri":"{URI}","version":3}},"contentChanges":false}}"#
                ),
            ));
            let invalid = client.exchange(
                "invalid",
                &call("invalid", &session, "Lean.Widget.getInteractiveGoals", 1, 2),
            );
            assert!(invalid.contains("\"code\":-32803"), "{invalid}");
            client.change(4, SOURCE);
            let recovered = client.exchange(
                "recovered",
                &call(
                    "recovered",
                    &session,
                    "Lean.Widget.getInteractiveGoals",
                    1,
                    2,
                ),
            );
            assert!(recovered.contains("\"text\":\"P\""), "{recovered}");
            client.finish();
        }
    }
}
#[test]
fn closed_sessions_reconnect_and_numeric_or_wrong_document_ids_refuse() {
    let mut client = Client::start(env!("CARGO_BIN_EXE_fln"), &["serve-lsp"], "v1");
    client.open(SOURCE);
    let session = client.connect("one");
    let numeric = call("numeric", &session, "Lean.Widget.getInteractiveGoals", 1, 2).replace(
        &format!("\"sessionId\":\"{session}\""),
        &format!("\"sessionId\":{session}"),
    );
    assert!(
        client
            .exchange("numeric", &numeric)
            .contains("\"code\":-32602")
    );
    let wrong = call("wrong", &session, "Lean.Widget.getInteractiveGoals", 1, 2)
        .replace(URI, "file:///Other.lean");
    assert!(client.exchange("wrong", &wrong).contains("\"code\":-32900"));
    let unsupported = client.exchange(
        "unsupported",
        &call("unsupported", &session, "Unknown.procedure", 1, 2),
    );
    assert!(unsupported.contains("\"code\":-32601"));
    client.send(&notification(
        "textDocument/didClose",
        &format!(r#"{{"textDocument":{{"uri":"{URI}"}}}}"#),
    ));
    client.open(SOURCE);
    assert!(
        client
            .exchange(
                "stale",
                &call("stale", &session, "Lean.Widget.getInteractiveGoals", 1, 2)
            )
            .contains("\"code\":-32900")
    );
    let fresh = client.connect("two");
    assert_ne!(fresh, session);
    assert!(
        client
            .exchange(
                "fresh",
                &call("fresh", &fresh, "Lean.Widget.getInteractiveGoals", 1, 2)
            )
            .contains("\"goals\":[{")
    );
    client.finish();
}
#[test]
fn rpc_term_goal_before_crlf_keeps_the_original_half_open_range() {
    let mut client = Client::start(env!("CARGO_BIN_EXE_lean"), &["--server"], "v1");
    let source = "-- 😀\r\nprelude\r\ndef pending (A : Type) (x : A) : A := _\r\n";
    client.open(source);
    let session = client.connect("connect");
    let line = source.lines().last().unwrap();
    let column = line[..line.rfind('_').unwrap()].encode_utf16().count();
    let term = client.exchange(
        "hole",
        &call(
            "hole",
            &session,
            "Lean.Widget.getInteractiveTermGoal",
            2,
            column,
        ),
    );
    assert!(term.contains("\"text\":\"A\""), "{term}");
    assert!(
        term.contains(&format!(
            "\"end\":{{\"line\":2,\"character\":{}}}",
            column + 1
        )),
        "{term}"
    );
    assert!(
        !client
            .log
            .iter()
            .any(|line| line.contains("$/frankenLean/sourceCheck")),
        "unfinished declaration was admitted"
    );
    client.finish();
}
