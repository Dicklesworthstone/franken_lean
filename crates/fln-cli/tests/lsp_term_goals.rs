//! Installed native servers answer from the accepted unsaved document snapshot.
//! Abstract prelude programs need no external Reference or compiled Init import.
#![forbid(unsafe_code)]
use std::io::Write;
use std::process::{Command, Stdio};

const URI: &str = "file:///fln-term-goals.lean";

fn quoted(text: &str) -> String {
    let mut output = String::from("\"");
    for ch in text.chars() {
        match ch {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            '\n' => output.push_str("\\n"),
            '\r' => output.push_str("\\r"),
            '\t' => output.push_str("\\t"),
            ch if ch.is_control() => output.push_str(&format!("\\u{:04x}", u32::from(ch))),
            ch => output.push(ch),
        }
    }
    output.push('"');
    output
}

fn open(text: &str) -> String {
    format!(
        "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{{\"textDocument\":{{\"uri\":{},\"languageId\":\"lean4\",\"version\":1,\"text\":{}}}}}}}",
        quoted(URI),
        quoted(text),
    )
}

fn request(id: u32, line: u32, character: u32) -> String {
    format!(
        "{{\"jsonrpc\":\"2.0\",\"id\":{id},\"method\":\"$/lean/plainTermGoal\",\"params\":{{\"textDocument\":{{\"uri\":{}}},\"position\":{{\"line\":{line},\"character\":{character}}}}}}}",
        quoted(URI),
    )
}

fn frames(output: &[u8]) -> Vec<String> {
    let mut reader = std::io::BufReader::new(output);
    let mut messages = Vec::new();
    while let Some(message) = fln_server::transport::read_message(&mut reader).unwrap() {
        messages.push(String::from_utf8(message).unwrap());
    }
    messages
}

fn run(fln: bool, messages: Vec<String>) -> Vec<String> {
    let mut command = if fln {
        let mut command = Command::new(env!("CARGO_BIN_EXE_fln"));
        command.arg("serve-lsp");
        command
    } else {
        let mut command = Command::new(env!("CARGO_BIN_EXE_lean"));
        command.arg("--server");
        command
    };
    let mut child = command
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("start native server");
    let mut input = child.stdin.take().unwrap();
    let initialize = [
        r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":{}}}"#.to_owned(),
        r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#.to_owned(),
    ];
    let shutdown = [
        r#"{"jsonrpc":"2.0","id":99,"method":"shutdown","params":null}"#.to_owned(),
        r#"{"jsonrpc":"2.0","method":"exit","params":null}"#.to_owned(),
    ];
    for message in initialize.into_iter().chain(messages).chain(shutdown) {
        write!(input, "Content-Length: {}\r\n\r\n{message}", message.len()).unwrap();
    }
    drop(input);
    let output = child.wait_with_output().expect("wait for server shutdown");
    assert!(
        output.status.success(),
        "server failed: {}",
        String::from_utf8_lossy(&output.stderr),
    );
    frames(&output.stdout)
}

fn reply(messages: &[String], id: u32) -> &str {
    let needle = format!("\"id\":{id},");
    let replies: Vec<_> = messages.iter().filter(|m| m.contains(&needle)).collect();
    assert_eq!(
        replies.len(),
        1,
        "one response for request {id}: {messages:?}"
    );
    replies[0]
}

fn hole_column(text: &str) -> u32 {
    let line = text.lines().last().unwrap();
    let prefix = &line[..line.rfind('_').unwrap()];
    u32::try_from(prefix.encode_utf16().count()).unwrap()
}

#[test]
fn term_goals_follow_unsaved_changes_and_disappear_when_the_document_closes() {
    for fln in [false, true] {
        let first = "prelude\ndef pending (A : Type) (x : A) : A := _";
        let second = "prelude\ndef pending (B : Type) (y : B) : B := _";
        let change = format!(
            "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\",\"params\":{{\"textDocument\":{{\"uri\":{},\"version\":2}},\"contentChanges\":[{{\"text\":{}}}]}}}}",
            quoted(URI),
            quoted(second),
        );
        let close = format!(
            "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didClose\",\"params\":{{\"textDocument\":{{\"uri\":{}}}}}}}",
            quoted(URI),
        );
        let messages = run(
            fln,
            vec![
                open(first),
                request(2, 1, hole_column(first)),
                change,
                request(3, 1, hole_column(second)),
                request(4, 1, u32::MAX),
                close,
                request(5, 1, hole_column(second)),
            ],
        );
        let before = reply(&messages, 2);
        assert!(before.contains("\"goal\":"), "{before}");
        assert!(before.contains("x : A"), "{before}");
        assert!(before.contains("⊢ A"), "{before}");
        let after = reply(&messages, 3);
        assert!(after.contains("y : B"), "{after}");
        assert!(after.contains("⊢ B"), "{after}");
        assert!(!after.contains("x : A"), "stale context: {after}");
        assert!(reply(&messages, 4).contains("\"code\":-32602"));
        assert!(reply(&messages, 5).contains("\"result\":null"));
    }
}

#[test]
fn term_goal_range_survives_source_normalization_and_utf16_query_decoding() {
    for fln in [false, true] {
        let source = "-- 😀\r\nprelude\r\ndef pending (A : Type) (x : A) : A := _\r\n";
        let column = hole_column(source);
        let messages = run(
            fln,
            vec![open(source), request(2, 2, column), request(3, 0, 4)],
        );
        let goal = reply(&messages, 2);
        assert!(goal.contains("⊢ A"), "{goal}");
        assert!(goal.contains(&format!("\"start\":{{\"line\":2,\"character\":{column}}}")));
        assert!(goal.contains(&format!(
            "\"end\":{{\"line\":2,\"character\":{}}}",
            column + 1
        )));
        // Position 4 splits the emoji after the three ASCII prefix characters.
        assert!(reply(&messages, 3).contains("\"code\":-32602"));
    }
}

#[test]
fn inferred_term_goal_uses_the_same_dependent_context_as_elaboration() {
    for fln in [false, true] {
        let source = "prelude\ndef inferred (A : Type) (x : A) := x";
        let line = source.lines().last().unwrap();
        let column =
            u32::try_from(line[..line.rfind('x').unwrap()].encode_utf16().count()).unwrap();
        let messages = run(fln, vec![open(source), request(2, 1, column)]);
        let goal = reply(&messages, 2);
        assert!(goal.contains("\"goal\":"), "{goal}");
        assert!(goal.contains("x : A"), "{goal}");
        assert!(goal.contains("⊢ A"), "{goal}");
    }
}

#[test]
fn invalid_source_does_not_fabricate_a_term_goal() {
    for fln in [false, true] {
        let source = "prelude\ndef pending (A : Type) : A := missing";
        let column =
            u32::try_from(source.lines().last().unwrap().find("missing").unwrap()).unwrap();
        let messages = run(fln, vec![open(source), request(2, 1, column)]);
        let result = reply(&messages, 2);
        assert!(result.contains("\"code\":-32803"), "{result}");
        assert!(!result.contains("\"goal\":"), "{result}");
    }
}
