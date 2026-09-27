//! Installed front doors exercise real parsing, dual-checked prefixes and LSP wiring.
#![forbid(unsafe_code)]
use std::io::{Cursor, Write};
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};

fn quoted(text: &str) -> String {
    let mut out = String::from("\"");
    for c in text.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c.is_control() => out.push_str(&format!("\\u{:04x}", u32::from(c))),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}
fn open(uri: &str, text: &str) -> String {
    format!("{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{{\"textDocument\":{{\"uri\":{},\"languageId\":\"lean4\",\"version\":1,\"text\":{}}}}}}}", quoted(uri), quoted(text))
}
fn change(uri: &str, version: usize, text: &str) -> String {
    format!("{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\",\"params\":{{\"textDocument\":{{\"uri\":{},\"version\":{version}}},\"contentChanges\":[{{\"text\":{}}}]}}}}", quoted(uri), quoted(text))
}
fn request(id: usize, uri: &str, text: &str, at: usize) -> String {
    let prefix = &text[..at];
    let line = prefix.bytes().filter(|b| *b == b'\n').count();
    let character = prefix.rsplit('\n').next().unwrap().encode_utf16().count();
    format!("{{\"jsonrpc\":\"2.0\",\"id\":{id},\"method\":\"textDocument/definition\",\"params\":{{\"textDocument\":{{\"uri\":{}}},\"position\":{{\"line\":{line},\"character\":{character}}}}}}}", quoted(uri))
}
fn run(binary: &str, argument: &str, messages: &[String]) -> Vec<String> {
    let mut input = Vec::new();
    for message in [
        r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#,
        r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
    ].into_iter().chain(messages.iter().map(String::as_str)).chain([
        r#"{"jsonrpc":"2.0","id":99,"method":"shutdown"}"#,
        r#"{"jsonrpc":"2.0","method":"exit"}"#,
    ]) {
        fln_server::transport::write_message(&mut input, message.as_bytes()).unwrap();
    }
    let mut child = Command::new(binary).arg(argument)
        .stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped())
        .spawn().unwrap();
    let mut stdin = child.stdin.take().unwrap();
    let writer = std::thread::spawn(move || stdin.write_all(&input));
    let output = child.wait_with_output().unwrap();
    writer.join().unwrap().unwrap();
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    let mut reader = Cursor::new(output.stdout);
    let mut messages = Vec::new();
    while let Some(message) = fln_server::transport::read_message(&mut reader).unwrap() {
        messages.push(String::from_utf8(message).unwrap());
    }
    assert!(messages.iter().any(|m| m.contains(r#""definitionProvider":true"#)));
    messages
}
fn front_doors() -> [(&'static str, &'static str); 2] {
    [(env!("CARGO_BIN_EXE_fln"), "serve-lsp"), (env!("CARGO_BIN_EXE_lean"), "--server")]
}
fn response(messages: &[String], id: usize) -> &str {
    let key = format!("\"id\":{id},");
    let selected: Vec<_> = messages.iter().filter(|m| m.contains(&key)).collect();
    assert_eq!(selected.len(), 1, "missing or duplicate response {id}: {messages:?}");
    selected[0]
}
fn assert_location(messages: &[String], id: usize, uri: &str, line: usize, column: usize) {
    let expected = format!("\"result\":{{\"uri\":{},\"range\":{{\"start\":{{\"line\":{line},\"character\":{column}}},\"end\":{{\"line\":{line},\"character\":{}}}}}}}", quoted(uri), column + 5);
    assert!(response(messages, id).contains(&expected), "{}", response(messages, id));
}

#[test]
fn both_front_doors_navigate_globals_but_do_not_confuse_shadowing_parameters() {
    let uri = "file:///tmp/franken-lean-navigation.lean";
    let source = "def value : Nat := 7\ndef pending : Nat := value\ndef shadow (value : Nat) : Nat := value";
    for (binary, arg) in front_doors() {
        let messages = run(binary, arg, &[
            open(uri, source),
            request(20, uri, source, source.find("Nat := value").unwrap() + 7),
            request(21, uri, source, source.rfind("value").unwrap()),
        ]);
        assert_location(&messages, 20, uri, 0, 4);
        assert!(response(&messages, 21).contains(r#""result":null"#));
    }
}

struct Fixture { root: PathBuf }
impl Fixture {
    fn new() -> Self {
        static SERIAL: AtomicUsize = AtomicUsize::new(0);
        let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
        let root = std::env::temp_dir().join(format!("fln-definition-{}-{nonce}-{}", std::process::id(), SERIAL.fetch_add(1, Ordering::Relaxed)));
        std::fs::create_dir(&root).unwrap();
        Self { root }
    }
    fn uri(&self, file: &str) -> String {
        let path = self.root.join(file).to_string_lossy().replace('\\', "/");
        let mut escaped = String::new();
        for byte in path.bytes() {
            if byte.is_ascii_alphanumeric() || b"/-._~:".contains(&byte) {
                escaped.push(char::from(byte));
            } else {
                escaped.push_str(&format!("%{byte:02X}"));
            }
        }
        format!("file://{}{escaped}", if path.starts_with('/') { "" } else { "/" })
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        // Only this test's named file and empty, uniquely-created directory.
        let _ = std::fs::remove_file(self.root.join("Lib.lean"));
        let _ = std::fs::remove_dir(&self.root);
    }
}

#[test]
fn both_front_doors_use_unsaved_import_origins_and_refuse_invalidated_overlays() {
    let fixture = Fixture::new();
    std::fs::write(fixture.root.join("Lib.lean"), "namespace Library\ndef value : Nat := 1\nend Library\n").unwrap();
    let main = fixture.uri("Main.lean");
    let lib = fixture.uri("Lib.lean");
    let source = "import Lib\nopen Library\ndef pending : Nat := value";
    let overlay = "-- 😀 unsaved\r\n\r\nnamespace Library\r\ndef value : Nat := 2\r\nend Library\r\n";
    for (binary, arg) in front_doors() {
        let messages = run(binary, arg, &[
            open(&main, source), request(30, &main, source, source.rfind("value").unwrap()),
            open(&lib, overlay), request(31, &main, source, source.rfind("value").unwrap()),
            format!("{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\",\"params\":{{\"textDocument\":{{\"uri\":{},\"version\":2}},\"contentChanges\":null}}}}", quoted(&lib)),
            request(32, &main, source, source.rfind("value").unwrap()),
            format!("{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didClose\",\"params\":{{\"textDocument\":{{\"uri\":{}}}}}}}", quoted(&lib)),
            request(33, &main, source, source.rfind("value").unwrap()),
        ]);
        assert_location(&messages, 30, &lib, 1, 4);
        assert_location(&messages, 31, &lib, 3, 4);
        assert!(response(&messages, 32).contains(r#""error":{"code":-32803"#));
        assert!(!response(&messages, 32).contains("\"result\""));
        assert_location(&messages, 33, &lib, 1, 4);
    }
}

#[test]
fn failed_prefix_cannot_reuse_a_previous_definition_answer_and_recovery_relocates_it() {
    let uri = "file:///tmp/franken-lean-navigation-recovery.lean";
    let good = "def value : Nat := 1\ndef pending : Nat := value";
    let bad = "theorem bad : False := by exact True.intro\ndef value : Nat := 1\ndef pending : Nat := value";
    let recovered = "-- relocated\ndef value : Nat := 2\ndef pending : Nat := value";
    for (binary, arg) in front_doors() {
        let messages = run(binary, arg, &[
            open(uri, good), request(40, uri, good, good.rfind("value").unwrap()),
            change(uri, 2, bad), request(41, uri, bad, bad.rfind("value").unwrap()),
            change(uri, 3, recovered), request(42, uri, recovered, recovered.rfind("value").unwrap()),
        ]);
        assert_location(&messages, 40, uri, 0, 4);
        assert!(response(&messages, 41).contains(r#""error":{"code":-32803"#));
        assert_location(&messages, 42, uri, 1, 4);
    }
}
