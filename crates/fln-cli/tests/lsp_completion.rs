//! Both installed front doors exercise the native worker, not a mocked provider.
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
    format!(
        "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{{\"textDocument\":{{\"uri\":{},\"languageId\":\"lean4\",\"version\":1,\"text\":{}}}}}}}",
        quoted(uri),
        quoted(text)
    )
}
fn change(uri: &str, version: usize, text: &str) -> String {
    format!(
        "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\",\"params\":{{\"textDocument\":{{\"uri\":{},\"version\":{version}}},\"contentChanges\":[{{\"text\":{}}}]}}}}",
        quoted(uri),
        quoted(text)
    )
}
fn request(id: usize, uri: &str, text: &str, at: usize) -> String {
    let prefix = &text[..at];
    let line = prefix.bytes().filter(|b| *b == b'\n').count();
    let character = prefix.rsplit('\n').next().unwrap().encode_utf16().count();
    format!(
        "{{\"jsonrpc\":\"2.0\",\"id\":{id},\"method\":\"textDocument/completion\",\"params\":{{\"textDocument\":{{\"uri\":{}}},\"position\":{{\"line\":{line},\"character\":{character}}}}}}}",
        quoted(uri)
    )
}
fn run(binary: &str, argument: &str, messages: &[String]) -> Vec<String> {
    let mut input = Vec::new();
    for message in [
        r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#,
        r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
    ]
    .into_iter()
    .chain(messages.iter().map(String::as_str))
    .chain([
        r#"{"jsonrpc":"2.0","id":99,"method":"shutdown"}"#,
        r#"{"jsonrpc":"2.0","method":"exit"}"#,
    ]) {
        fln_server::transport::write_message(&mut input, message.as_bytes()).unwrap();
    }
    let mut child = Command::new(binary)
        .arg(argument)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let mut stdin = child.stdin.take().unwrap();
    let writer = std::thread::spawn(move || stdin.write_all(&input));
    let output = child.wait_with_output().unwrap();
    writer.join().unwrap().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let mut reader = Cursor::new(output.stdout);
    let mut messages = Vec::new();
    while let Some(message) = fln_server::transport::read_message(&mut reader).unwrap() {
        messages.push(String::from_utf8(message).unwrap());
    }
    assert!(
        messages
            .iter()
            .any(|m| m.contains("\"completionProvider\""))
    );
    messages
}
fn front_doors() -> [(&'static str, &'static str); 2] {
    [
        (env!("CARGO_BIN_EXE_fln"), "serve-lsp"),
        (env!("CARGO_BIN_EXE_lean"), "--server"),
    ]
}
fn response(messages: &[String], id: usize) -> &str {
    let key = format!("\"id\":{id},");
    let selected: Vec<_> = messages.iter().filter(|m| m.contains(&key)).collect();
    assert_eq!(
        selected.len(),
        1,
        "missing or duplicate response {id}: {messages:?}"
    );
    selected[0]
}
fn has_item(messages: &[String], id: usize, label: &str) -> bool {
    response(messages, id).contains(&format!("\"label\":{}", quoted(label)))
}

#[test]
fn both_front_doors_complete_checked_globals_without_admitting_unfinished_or_future_commands() {
    let uri = "file:///tmp/fln-completion.lean";
    let source =
        "def value : Nat := 7\ndef pending (value : Bool) : Nat := val\ndef valuable : Nat := 9";
    let cursor = source.find(":= val").unwrap() + ":= val".len();
    let broken_later = "def value : Nat := 7\ndef pending (value : Bool) : Nat := val\ndef broken := \"unterminated";
    for (binary, arg) in front_doors() {
        let messages = run(
            binary,
            arg,
            &[
                open(uri, source),
                request(20, uri, source, cursor),
                change(uri, 2, broken_later),
                request(21, uri, broken_later, cursor),
            ],
        );
        for id in [20, 21] {
            assert!(has_item(&messages, id, "value"));
            assert!(!has_item(&messages, id, "valuable"));
            assert!(!has_item(&messages, id, "pending"));
            assert!(response(&messages, id).contains(r#""newText":"_root_.value""#));
            assert!(response(&messages, id).contains(r#""isIncomplete":false"#));
        }
    }
}

#[test]
fn both_front_doors_return_exact_utf16_edits_at_crlf_line_ends() {
    let uri = "file:///tmp/fln-completion-crlf.lean";
    let source = "def αvalue : Nat := 7\r\ndef pending : Nat := /- 😀 -/ αva\r\n";
    let start = source.rfind("αva").unwrap();
    let cursor = start + "αva".len();
    let column = source[..start]
        .rsplit('\n')
        .next()
        .unwrap()
        .encode_utf16()
        .count();
    let expected = format!(
        "\"range\":{{\"start\":{{\"line\":1,\"character\":{column}}},\"end\":{{\"line\":1,\"character\":{}}}}}",
        column + 3
    );
    for (binary, arg) in front_doors() {
        let messages = run(
            binary,
            arg,
            &[open(uri, source), request(30, uri, source, cursor)],
        );
        assert!(has_item(&messages, 30, "αvalue"));
        assert!(
            response(&messages, 30).contains(&expected),
            "{}",
            response(&messages, 30)
        );
        assert!(response(&messages, 30).contains(r#""newText":"_root_.αvalue""#));
    }
}

#[test]
fn failed_prefixes_do_not_reuse_old_completion_lists_and_recovery_uses_new_names() {
    let uri = "file:///tmp/fln-completion-recovery.lean";
    let good = "def value : Nat := 1\ndef pending : Nat := val";
    let bad = "theorem bad : False := by exact True.intro\ndef value : Nat := 1\ndef pending : Nat := val";
    let recovered = "def value_recovered : Nat := 2\ndef pending : Nat := val";
    for (binary, arg) in front_doors() {
        let messages = run(
            binary,
            arg,
            &[
                open(uri, good),
                request(40, uri, good, good.len()),
                change(uri, 2, bad),
                request(41, uri, bad, bad.len()),
                change(uri, 3, recovered),
                request(42, uri, recovered, recovered.len()),
            ],
        );
        assert!(has_item(&messages, 40, "value"));
        assert!(response(&messages, 41).contains(r#""error":{"code":-32803"#));
        assert!(!response(&messages, 41).contains("\"result\""));
        assert!(has_item(&messages, 42, "value_recovered"));
        assert!(!has_item(&messages, 42, "value"));
    }
}

struct Fixture {
    root: PathBuf,
}
impl Fixture {
    fn new() -> Self {
        static SERIAL: AtomicUsize = AtomicUsize::new(0);
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let root = std::env::temp_dir().join(format!(
            "fln-completion-{}-{nonce}-{}",
            std::process::id(),
            SERIAL.fetch_add(1, Ordering::Relaxed)
        ));
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
        format!(
            "file://{}{escaped}",
            if path.starts_with('/') { "" } else { "/" }
        )
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        // Only this test's file and its uniquely-created, now-empty directory.
        let _ = std::fs::remove_file(self.root.join("Lib.lean"));
        let _ = std::fs::remove_dir(&self.root);
    }
}

#[test]
fn both_front_doors_use_unsaved_imports_and_do_not_fall_back_after_overlay_invalidation() {
    let fixture = Fixture::new();
    std::fs::write(
        fixture.root.join("Lib.lean"),
        "def library_disk : Nat := 1\n",
    )
    .unwrap();
    let main = fixture.uri("Main.lean");
    let lib = fixture.uri("Lib.lean");
    let source = "import Lib\ndef pending : Nat := library_";
    let overlay = "def library_unsaved : Nat := 2\n";
    for (binary, arg) in front_doors() {
        let messages = run(
            binary,
            arg,
            &[
                open(&main, source),
                request(50, &main, source, source.len()),
                open(&lib, overlay),
                request(51, &main, source, source.len()),
                format!(
                    "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\",\"params\":{{\"textDocument\":{{\"uri\":{},\"version\":2}},\"contentChanges\":null}}}}",
                    quoted(&lib)
                ),
                request(52, &main, source, source.len()),
                format!(
                    "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didClose\",\"params\":{{\"textDocument\":{{\"uri\":{}}}}}}}",
                    quoted(&lib)
                ),
                request(53, &main, source, source.len()),
            ],
        );
        assert!(has_item(&messages, 50, "library_disk"));
        assert!(has_item(&messages, 51, "library_unsaved"));
        assert!(!has_item(&messages, 51, "library_disk"));
        assert!(response(&messages, 52).contains(r#""error":{"code":-32803"#));
        assert!(!response(&messages, 52).contains("\"result\""));
        assert!(has_item(&messages, 53, "library_disk"));
        assert!(!has_item(&messages, 53, "library_unsaved"));
    }
}

#[test]
fn public_completion_uses_exported_imports_without_parsing_the_unfinished_body() {
    let fixture = Fixture::new();
    let secret = fixture.uri("Secret.lean");
    let api = fixture.uri("Api.lean");
    let main = fixture.uri("Main.lean");
    let imports = "module\nprelude\nimport Secret\npublic import Api\n";
    let public = format!("{imports}@[expose] public def use (A : Type) (x : A) : A := hid");
    let visible = format!("{imports}@[expose] public def use (A : Type) (x : A) : A := vis");
    let private = format!("{imports}private def use (A : Type) (x : A) : A := hid");
    let section =
        format!("{imports}@[expose] public section\ndef use (A : Type) (x : A) : A := hid");
    let query = format!("{imports}@[expose] public section\n#check hid");
    let wrapped = format!(
        "{imports}set_option maxRecDepth 256 in @[expose] public def use (A : Type) (x : A) : A := hid"
    );
    let wrapped_private = format!(
        "{imports}set_option maxRecDepth 256 in private def use (A : Type) (x : A) : A := hid"
    );
    let variable = format!("{imports}variable (x : hid");
    let public_variable = format!("{imports}public section\nvariable (x : hid");
    for (binary, arg) in front_doors() {
        let messages = run(
            binary,
            arg,
            &[
                open(
                    &secret,
                    "prelude\ndef hiddenValue (A : Type) (x : A) : A := x",
                ),
                open(
                    &api,
                    "prelude\ndef visibleValue (A : Type) (x : A) : A := x",
                ),
                open(&main, &public),
                request(80, &main, &public, public.len()),
                change(&main, 2, &visible),
                request(81, &main, &visible, visible.len()),
                change(&main, 3, &private),
                request(82, &main, &private, private.len()),
                change(&main, 4, &section),
                request(83, &main, &section, section.len()),
                change(&main, 5, &query),
                request(84, &main, &query, query.len()),
                change(&main, 6, &wrapped),
                request(85, &main, &wrapped, wrapped.len()),
                change(&main, 7, &wrapped_private),
                request(86, &main, &wrapped_private, wrapped_private.len()),
                change(&main, 8, &variable),
                request(87, &main, &variable, variable.len()),
                change(&main, 9, &public_variable),
                request(88, &main, &public_variable, public_variable.len()),
            ],
        );
        for id in [80, 83, 85, 88] {
            assert!(!has_item(&messages, id, "hiddenValue"), "{messages:#?}");
            assert!(
                response(&messages, id).contains("\"items\":[]"),
                "{messages:#?}"
            );
        }
        assert!(has_item(&messages, 81, "visibleValue"), "{messages:#?}");
        for id in [82, 84, 86, 87] {
            assert!(has_item(&messages, id, "hiddenValue"), "{messages:#?}");
        }
    }
}

#[test]
fn public_theorem_completion_switches_from_public_header_to_private_proof() {
    let fixture = Fixture::new();
    let secret = fixture.uri("Secret.lean");
    let api = fixture.uri("Api.lean");
    let main = fixture.uri("Main.lean");
    let imports = "module\nprelude\nimport Secret\npublic import Api\nprivate theorem hiddenLocal (P : Prop) (h : P) : P := h\n";
    let cases = [
        ("public theorem use (P : hid", false),
        ("public theorem use (P : Prop) (h : P) : hid", false),
        (
            "public theorem use (P : Prop) (h : P := by assumption) : hid",
            false,
        ),
        (
            "public theorem use (P : Prop) (h : P) : let Q := P; hid",
            false,
        ),
        (
            "public theorem use (P : Prop) (h : P) : P := by exact hid",
            true,
        ),
        (
            "public section\ntheorem use (P : Prop) (h : P) : P := hid",
            true,
        ),
        (
            "set_option maxRecDepth 256 in public theorem use (P : Prop) (h : P) : P := hid",
            true,
        ),
        ("public theorem use (P : Prop) : P -> P | h => hid", true),
        ("private theorem use (P : Prop) (h : P) : hid", true),
    ];
    for (binary, arg) in front_doors() {
        let visible = format!("{imports}public theorem use (P : Prop) : vis");
        let mut requests = vec![
            open(
                &secret,
                "prelude\ntheorem hiddenProof (P : Prop) (h : P) : P := h",
            ),
            open(&api, "prelude\ndef visibleStatement (P : Prop) : Prop := P"),
            open(&main, &visible),
            request(100, &main, &visible, visible.len()),
        ];
        for (index, (declaration, _)) in cases.iter().enumerate() {
            let source = format!("{imports}{declaration}");
            requests.push(change(&main, index + 2, &source));
            requests.push(request(101 + index, &main, &source, source.len()));
        }
        let messages = run(binary, arg, &requests);
        assert!(
            has_item(&messages, 100, "visibleStatement"),
            "{messages:#?}"
        );
        for (index, (declaration, private)) in cases.iter().enumerate() {
            let id = 101 + index;
            assert!(
                response(&messages, id).contains("\"items\":"),
                "{declaration}: {messages:#?}"
            );
            assert_eq!(
                has_item(&messages, id, "hiddenProof"),
                *private,
                "{declaration}: {messages:#?}"
            );
            assert_eq!(
                has_item(&messages, id, "hiddenLocal"),
                *private,
                "{declaration}: {messages:#?}"
            );
            if *private {
                assert!(
                    response(&messages, id).contains("\"newText\":\"_root_.hiddenLocal\""),
                    "{messages:#?}"
                );
            }
        }
    }
}
