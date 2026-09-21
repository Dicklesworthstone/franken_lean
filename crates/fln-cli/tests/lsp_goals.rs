//! Installed native query requests use the real proof worker and editor sources.
#![forbid(unsafe_code)]
use std::io::{Cursor, Write};
use std::process::{Command, Stdio};

fn quote(text: &str) -> String {
    let mut out = String::from("\"");
    for c in text.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c.is_control() => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}
fn open(uri: &str, text: &str) -> String {
    format!(
        "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{{\"textDocument\":{{\"uri\":{},\"version\":1,\"text\":{}}}}}}}",
        quote(uri),
        quote(text)
    )
}
fn change(uri: &str, version: i64, text: &str) -> String {
    format!(
        "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\",\"params\":{{\"textDocument\":{{\"uri\":{},\"version\":{version}}},\"contentChanges\":[{{\"text\":{}}}]}}}}",
        quote(uri),
        quote(text)
    )
}
fn query(id: &str, method: &str, uri: &str, line: usize, column: usize) -> String {
    format!(
        "{{\"jsonrpc\":\"2.0\",\"id\":{},\"method\":{},\"params\":{{\"textDocument\":{{\"uri\":{}}},\"position\":{{\"line\":{line},\"character\":{column}}}}}}}",
        quote(id),
        quote(method),
        quote(uri)
    )
}
fn run(binary: &str, args: &[&str], messages: Vec<String>) -> Vec<String> {
    let mut wire = Vec::new();
    for m in [
        r#"{"jsonrpc":"2.0","id":"init","method":"initialize","params":{}}"#.to_owned(),
        r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#.to_owned(),
    ]
    .into_iter()
    .chain(messages)
    .chain([
        r#"{"jsonrpc":"2.0","id":"end","method":"shutdown"}"#.to_owned(),
        r#"{"jsonrpc":"2.0","method":"exit"}"#.to_owned(),
    ]) {
        fln_server::transport::write_message(&mut wire, m.as_bytes()).unwrap();
    }
    let mut child = Command::new(binary)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child.stdin.take().unwrap().write_all(&wire).unwrap();
    let output = child.wait_with_output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        output.stderr.is_empty(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let mut stream = Cursor::new(output.stdout);
    let mut replies = Vec::new();
    while let Some(body) = fln_server::transport::read_message(&mut stream).unwrap() {
        replies.push(String::from_utf8(body).unwrap());
    }
    replies
}
fn reply<'a>(messages: &'a [String], id: &str) -> &'a str {
    let key = format!("\"id\":{}", quote(id));
    let found: Vec<_> = messages.iter().filter(|m| m.contains(&key)).collect();
    assert_eq!(found.len(), 1, "{id}: {messages:#?}");
    found[0]
}
const URI: &str = "file:///tmp/Native%20Goals.lean";

#[test]
fn both_installed_doors_show_real_unfinished_goals_and_local_hover() {
    let unfinished = "theorem pending (P : Prop) (h : P) : P := by";
    let complete = "theorem pending (P : Prop) (h : P) : P := by\n  exact h";
    for (binary, args) in [
        (env!("CARGO_BIN_EXE_fln"), &["serve-lsp"][..]),
        (env!("CARGO_BIN_EXE_lean"), &["--server"][..]),
    ] {
        let messages = run(
            binary,
            args,
            vec![
                open(URI, unfinished),
                query("goal", "$/lean/plainGoal", URI, 0, unfinished.len()),
                change(URI, 2, complete),
                query("done", "$/lean/plainGoal", URI, 1, 999),
                query("hover", "textDocument/hover", URI, 1, 8),
            ],
        );
        assert!(reply(&messages, "init").contains("\"hoverProvider\":true"));
        assert!(
            reply(&messages, "goal").contains("P : Prop\\nh : P\\n⊢ P"),
            "{messages:#?}"
        );
        assert!(
            reply(&messages, "done").contains("\"goals\":[]"),
            "{messages:#?}"
        );
        assert!(
            reply(&messages, "hover").contains("\"value\":\"h : P\""),
            "{messages:#?}"
        );
        let goal_position = messages
            .iter()
            .position(|m| m == reply(&messages, "goal"))
            .unwrap();
        assert!(
            !messages[..goal_position]
                .iter()
                .any(|m| m.contains("$/frankenLean/sourceCheck")),
            "unfinished theorem was reported as checked"
        );
        assert!(
            messages[..goal_position]
                .iter()
                .any(|m| m.contains("publishDiagnostics") && !m.contains("\"diagnostics\":[]"))
        );
    }
}
#[test]
fn real_multiple_goals_keep_their_own_context() {
    let source = "theorem pending (P Q : Prop) (h : P) (k : Q) : And P Q := by\n  constructor\n  exact h\n  exact k";
    let messages = run(
        env!("CARGO_BIN_EXE_fln"),
        &["serve-lsp"],
        vec![
            open(URI, source),
            query("split", "$/lean/plainGoal", URI, 2, 2),
        ],
    );
    let answer = reply(&messages, "split");
    assert!(answer.contains("⊢ P"));
    assert!(answer.contains("⊢ Q"));
    assert!(
        answer.contains("\",\""),
        "expected two separate goals: {answer}"
    );
}
#[test]
fn query_lifecycle_never_falls_back_to_stale_or_invalid_text() {
    let source = "theorem pending (P : Prop) : P := by";
    let corrupt = format!(
        "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\",\"params\":{{\"textDocument\":{{\"uri\":{},\"version\":3}},\"contentChanges\":false}}}}",
        quote(URI)
    );
    let close = format!(
        "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didClose\",\"params\":{{\"textDocument\":{{\"uri\":{}}}}}}}",
        quote(URI)
    );
    let messages = run(
        env!("CARGO_BIN_EXE_fln"),
        &["serve-lsp"],
        vec![
            open(URI, source),
            change(URI, 2, "theorem pending : False := by"),
            change(URI, 1, source),
            query("new", "$/lean/plainGoal", URI, 0, 999),
            corrupt,
            query("invalid", "$/lean/plainGoal", URI, 0, 999),
            change(URI, 4, source),
            query("recover", "$/lean/plainGoal", URI, 0, 999),
            close,
            query("closed", "$/lean/plainGoal", URI, 0, 999),
        ],
    );
    assert!(reply(&messages, "new").contains("⊢ False"));
    assert!(reply(&messages, "invalid").contains("\"code\":-32803"));
    assert!(reply(&messages, "recover").contains("⊢ P"));
    assert!(reply(&messages, "closed").contains("\"result\":null"));
}
#[test]
fn unicode_hover_uses_original_utf16_ranges_and_rejects_bad_coordinates() {
    let source =
        "def emoji : String := \"😀\"\r\ntheorem pending (P : Prop) (β : P) : P := by\r\n  exact β";
    let mut duplicate = query("duplicate", "textDocument/hover", URI, 2, 8);
    duplicate = duplicate.replace("\"line\":2", "\"line\":2,\"line\":1");
    let messages = run(
        env!("CARGO_BIN_EXE_fln"),
        &["serve-lsp"],
        vec![
            open(URI, source),
            query("unicode", "textDocument/hover", URI, 2, 8),
            query("split", "textDocument/hover", URI, 0, 24),
            duplicate,
        ],
    );
    assert!(
        reply(&messages, "unicode").contains("β : P"),
        "{messages:#?}"
    );
    assert!(reply(&messages, "unicode").contains("\"start\":{\"line\":2,\"character\":8}"));
    assert!(reply(&messages, "duplicate").contains("\"code\":-32602"));
    assert!(
        reply(&messages, "split").contains("\"code\":-32602"),
        "{messages:#?}"
    );
}
#[test]
fn invalid_prefix_and_earlier_tactic_failures_are_not_successful_queries() {
    let messages = run(
        env!("CARGO_BIN_EXE_fln"),
        &["serve-lsp"],
        vec![
            open(URI, "def bad : Nat := true\ntheorem pending : False := by"),
            query("prefix", "$/lean/plainGoal", URI, 1, 999),
            change(
                URI,
                2,
                "theorem pending : False := by\n  exact True.intro\n  skip",
            ),
            query("tactic", "$/lean/plainGoal", URI, 2, 2),
        ],
    );
    assert!(reply(&messages, "prefix").contains("\"code\":-32803"));
    assert!(reply(&messages, "tactic").contains("\"code\":-32803"));
}
#[test]
fn queries_check_the_current_unsaved_import_closure() {
    let base = "file:///tmp/GoalBase.lean";
    let main = "file:///tmp/GoalMain.lean";
    let source = "import GoalBase\ntheorem pending : Nat := by\n  exact value";
    let messages = run(
        env!("CARGO_BIN_EXE_fln"),
        &["serve-lsp"],
        vec![
            open(base, "def value : Nat := 42"),
            open(main, source),
            query("imported", "textDocument/hover", main, 2, 8),
            change(base, 2, "def value : Bool := true"),
            query("changed", "textDocument/hover", main, 2, 8),
        ],
    );
    assert!(
        reply(&messages, "imported").contains("value : Nat"),
        "{messages:#?}"
    );
    // The old Nat environment must not answer after an accepted Bool edit.
    assert!(!reply(&messages, "changed").contains("value : Nat"));
    assert!(
        reply(&messages, "changed").contains("\"code\":-32803")
            || reply(&messages, "changed").contains("value : Bool")
    );
}
