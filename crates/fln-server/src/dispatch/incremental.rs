//! Live-dispatch regressions: edits affect exactly one checked source snapshot.

use super::*;
use crate::transport::{read_message, write_message};
use std::io::BufReader;

fn run(messages: &[&str]) -> (ServerOutcome, Vec<String>, Vec<(String, String)>) {
    let mut input = Vec::new();
    let mut send = |body: &str| write_message(&mut input, body.as_bytes()).unwrap();
    send(r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#);
    send(r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#);
    for message in messages {
        send(message);
    }
    send(r#"{"jsonrpc":"2.0","id":99,"method":"shutdown"}"#);
    send(r#"{"jsonrpc":"2.0","method":"exit"}"#);
    let mut output = Vec::new();
    let mut seen = Vec::new();
    let outcome = serve(
        &mut BufReader::new(input.as_slice()),
        &mut output,
        &mut |uri, text| {
            seen.push((uri.to_string(), text.to_string()));
            vec![clear_diagnostics_notification(uri)]
        },
    )
    .unwrap();
    let mut frames = Vec::new();
    let mut reader = BufReader::new(output.as_slice());
    while let Some(frame) = read_message(&mut reader).unwrap() {
        frames.push(String::from_utf8(frame).unwrap());
    }
    (outcome, frames, seen)
}

#[test]
fn ordered_utf16_edits_check_only_the_final_snapshot_and_save_it() {
    let (outcome, frames, seen) = run(&[
        r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"untitled:proof%20one","version":1,"text":"a🤖b\r\nc"}}}"#,
        r#"{"jsonrpc":"2.0","id":"waiting","method":"textDocument/waitForDiagnostics","params":{"uri":"untitled:proof%20one","version":2}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"untitled:proof%20one","version":2},"contentChanges":[{"range":{"start":{"line":0,"character":1},"end":{"line":0,"character":3}},"rangeLength":2,"text":"X\nY"},{"range":{"start":{"line":1,"character":1},"end":{"line":1,"character":2}},"text":"B"}]}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didSave","params":{"textDocument":{"uri":"untitled:proof%20one"}}}"#,
    ]);
    assert!(outcome.clean);
    assert_eq!(outcome.documents_changed, 1);
    assert_eq!(outcome.documents_saved, 1);
    assert_eq!(seen.len(), 3);
    assert_eq!(seen[0].1, "a🤖b\r\nc");
    assert_eq!(seen[1].1, "aX\nYB\r\nc");
    assert_eq!(seen[2], seen[1]);
    assert!(seen.iter().all(|(uri, _)| uri == "untitled:proof%20one"));
    let wait = frames
        .iter()
        .position(|s| s.contains(r#""id":"waiting","result":{}"#))
        .unwrap();
    assert!(
        frames[..wait]
            .iter()
            .any(|s| s.contains(r#""processing":[]"#))
    );
    assert_eq!(
        frames
            .iter()
            .filter(|s| s.contains(r#""id":"waiting""#))
            .count(),
        1
    );
}

#[test]
fn a_bad_second_edit_never_checks_the_first_and_full_text_recovers() {
    let (outcome, frames, seen) = run(&[
        r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///x","version":1,"text":"original"}}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///x","version":2},"contentChanges":[{"text":"a🤖b"},{"range":{"start":{"line":0,"character":2},"end":{"line":0,"character":2}},"text":"bad"}]}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didSave","params":{"textDocument":{"uri":"file:///x"}}}"#,
        r#"{"jsonrpc":"2.0","id":"invalidated","method":"textDocument/waitForDiagnostics","params":{"uri":"file:///x","version":1}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///x","version":3},"contentChanges":[{"text":"recovered"},{"range":{"start":{"line":0,"character":9},"end":{"line":0,"character":9}},"text":"!"}]}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didSave","params":{"textDocument":{"uri":"file:///x"}}}"#,
    ]);
    assert!(outcome.clean);
    assert_eq!(outcome.documents_changed, 1);
    assert_eq!(outcome.documents_saved, 1);
    assert_eq!(
        seen.iter()
            .map(|(_, text)| text.as_str())
            .collect::<Vec<_>>(),
        ["original", "recovered!", "recovered!"]
    );
    assert!(
        frames
            .iter()
            .any(|s| s.contains("splits a UTF-16 surrogate pair"))
    );
    assert!(
        frames
            .iter()
            .any(|s| s.contains(r#""id":"invalidated","error":{"code":-32803"#))
    );
}

#[test]
fn stale_malformed_edits_cannot_invalidate_the_newest_source_or_frontier() {
    let (outcome, frames, seen) = run(&[
        r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///x","version":5,"text":"newest"}}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///x","version":4},"contentChanges":[{"range":null,"text":null}]}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///x","version":5},"contentChanges":null}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didSave","params":{"textDocument":{"uri":"file:///x"}}}"#,
        r#"{"jsonrpc":"2.0","id":"ready","method":"textDocument/waitForDiagnostics","params":{"uri":"file:///x","version":5}}"#,
    ]);
    assert_eq!(outcome.documents_changed, 0);
    assert_eq!(outcome.documents_saved, 1);
    assert_eq!(seen.len(), 2);
    assert_eq!(seen[0], seen[1]);
    assert!(
        frames
            .iter()
            .any(|s| s.contains(r#""id":"ready","result":{}"#))
    );
    assert_eq!(
        frames
            .iter()
            .filter(|s| s.contains("non-monotone didChange version"))
            .count(),
        2
    );
}

#[test]
fn incremental_changes_without_retained_source_fail_instead_of_replaying_stale_text() {
    let (outcome, frames, seen) = run(&[
        r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///x","version":1,"text":"old"}}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///x","version":2},"contentChanges":null}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///x","version":3},"contentChanges":[{"range":{"start":{"line":0,"character":0},"end":{"line":0,"character":0}},"text":"new"}]}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didSave","params":{"textDocument":{"uri":"file:///x"}}}"#,
    ]);
    assert_eq!(outcome.documents_changed, 0);
    assert_eq!(outcome.documents_saved, 0);
    assert_eq!(seen.len(), 1);
    assert!(
        frames
            .iter()
            .any(|s| s.contains("requires a retained source snapshot"))
    );
}

#[test]
fn empty_batches_advance_the_version_without_changing_source() {
    let (outcome, frames, seen) = run(&[
        r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///x","version":1,"text":"same"}}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///x","version":2},"contentChanges":[]}}"#,
        r#"{"jsonrpc":"2.0","id":"ready","method":"textDocument/waitForDiagnostics","params":{"uri":"file:///x","version":2}}"#,
    ]);
    assert_eq!(outcome.documents_changed, 1);
    assert_eq!(seen.len(), 2);
    assert_eq!(seen[0], seen[1]);
    assert!(
        frames
            .iter()
            .any(|s| s.contains(r#""id":"ready","result":{}"#))
    );
}
