//! Real transcript binary validates native semantic payloads, not just objects.
#![forbid(unsafe_code)]
use std::{
    path::PathBuf,
    process::{Command, Output},
    sync::atomic::{AtomicUsize, Ordering},
};
static NEXT: AtomicUsize = AtomicUsize::new(0);

fn frame(messages: &[String]) -> Vec<u8> {
    let mut wire = Vec::new();
    for message in messages {
        fln_server::transport::write_message(&mut wire, message.as_bytes()).unwrap();
    }
    wire
}
fn join(method: &str, response: &str) -> Output {
    let dir: PathBuf = std::env::temp_dir().join(format!(
        "fln-semantic-correlation-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&dir).unwrap();
    let client = frame(&[
        r#"{"jsonrpc":"2.0","id":"init","method":"initialize","params":{}}"#.to_owned(),
        r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#.to_owned(),
        format!(r#"{{"jsonrpc":"2.0","id":"query","method":"{method}","params":{{}}}}"#),
        r#"{"jsonrpc":"2.0","id":"end","method":"shutdown"}"#.to_owned(),
        r#"{"jsonrpc":"2.0","method":"exit"}"#.to_owned(),
    ]);
    let server = frame(&[
        r#"{"jsonrpc":"2.0","id":"init","result":{"capabilities":{}}}"#.to_owned(),
        format!(r#"{{"jsonrpc":"2.0","id":"query",{response}}}"#),
        r#"{"jsonrpc":"2.0","id":"end","result":null}"#.to_owned(),
    ]);
    let c = dir.join("client.frames");
    let s = dir.join("server.frames");
    std::fs::write(&c, &client).unwrap();
    std::fs::write(&s, &server).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_fln-lsp-correlate"))
        .arg(&c)
        .arg(&s)
        .output()
        .unwrap();
    assert_eq!(std::fs::read(c).unwrap(), client);
    assert_eq!(std::fs::read(s).unwrap(), server);
    output
}
fn accepted(method: &str, response: &str, counter: &str) {
    let output = join(method, response);
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty());
    let receipt = String::from_utf8(output.stdout).unwrap();
    assert!(receipt.contains(counter), "{receipt}");
    assert!(
        receipt.contains("\"methodContractViolations\":0"),
        "{receipt}"
    );
}

#[test]
fn native_goal_and_hover_results_have_typed_counters() {
    for goals in [
        r#""result":{"rendered":"P : Prop\n⊢ P","goals":["P : Prop\n⊢ P"]}"#,
        r#""result":{"rendered":"","goals":[]}"#,
    ] {
        accepted("$/lean/plainGoal", goals, "\"semanticQueryResults\":1");
    }
    accepted(
        "textDocument/hover",
        r#""result":{"contents":{"kind":"plaintext","value":"β : Nat"},"range":{"start":{"line":1,"character":2},"end":{"line":1,"character":3}}}"#,
        "\"semanticQueryResults\":1",
    );
}

#[test]
fn no_information_and_typed_nonanswers_remain_distinct() {
    for method in ["$/lean/plainGoal", "textDocument/hover"] {
        accepted(
            method,
            r#""result":null"#,
            "\"noInformationQueryResults\":1",
        );
        for code in [-32602, -32803, -32800] {
            accepted(
                method,
                &format!(r#""error":{{"code":{code},"message":"not a result"}}"#),
                "\"semanticQueryErrors\":1",
            );
        }
    }
}

#[test]
fn malformed_or_wrong_kind_results_cannot_pass_the_semantic_contract() {
    for (method, payload) in [
        ("$/lean/plainGoal", r#"{"rendered":"x","goals":[7]}"#),
        (
            "$/lean/plainGoal",
            r#"{"rendered":"x","goals":[],"goals":["x"]}"#,
        ),
        ("$/lean/plainGoal", r#"{"goals":["x"]}"#),
        ("$/lean/plainGoal", r#"{"rendered":"x","goals":["x",]}"#),
        (
            "textDocument/hover",
            r#"{"contents":{"kind":"plaintext","value":7},"range":{"start":{"line":0,"character":0},"end":{"line":0,"character":1}}}"#,
        ),
        (
            "textDocument/hover",
            r#"{"contents":{"kind":"plaintext","value":"x"},"range":{"start":{"line":0,"character":2},"end":{"line":0,"character":1}}}"#,
        ),
        (
            "textDocument/hover",
            r#"{"contents":{"kind":"plaintext","value":"x"},"range":{"start":{"line":-1,"character":0},"end":{"line":0,"character":1}}}"#,
        ),
        ("textDocument/hover", r#"{"rendered":"x","goals":[]}"#),
        ("textDocument/completion", r#"{"rendered":"x","goals":[]}"#),
    ] {
        let output = join(method, &format!(r#""result":{payload}"#));
        assert!(!output.status.success(), "{method}: {payload}");
        assert!(output.stdout.is_empty());
        assert!(!output.stderr.is_empty());
    }
    let too_many = format!(
        r#""result":{{"rendered":"x","goals":[{}]}}"#,
        vec!["\"x\""; 257].join(",")
    );
    assert!(!join("$/lean/plainGoal", &too_many).status.success());
}
