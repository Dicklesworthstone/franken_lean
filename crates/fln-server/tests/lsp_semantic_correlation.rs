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
        ("textDocument/definition", r#"{"rendered":"x","goals":[]}"#),
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

// ---------------------------------------------------------------------------
// Completion and definition: typed results since method-response/3 (2026-10-05)
// ---------------------------------------------------------------------------

/// The exact completion and definition payloads the dispatcher emits
/// (`dispatch/semantic/completion.rs`, `dispatch/semantic/navigation_tests.rs`).
const COMPLETION: &str = r#"{"isIncomplete":true,"items":[{"label":"value","kind":21,"insertTextFormat":1,"filterText":"_root_.value","textEdit":{"range":{"start":{"line":1,"character":2},"end":{"line":1,"character":5}},"newText":"_root_.value"}}]}"#;
const DEFINITION: &str = r#"{"uri":"file:///Lib%20One.lean","range":{"start":{"line":1,"character":3},"end":{"line":1,"character":8}}}"#;

#[test]
fn native_completion_and_definition_results_have_typed_counters() {
    accepted(
        "textDocument/completion",
        &format!(r#""result":{COMPLETION}"#),
        "\"semanticQueryResults\":1",
    );
    accepted(
        "textDocument/completion",
        r#""result":{"isIncomplete":false,"items":[]}"#,
        "\"semanticQueryResults\":1",
    );
    accepted(
        "textDocument/definition",
        &format!(r#""result":{DEFINITION}"#),
        "\"semanticQueryResults\":1",
    );
    for method in ["textDocument/completion", "textDocument/definition"] {
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
    // Term goals have no native answer yet, so only null passes there.
    accepted(
        "$/lean/plainTermGoal",
        r#""result":null"#,
        "\"noInformationQueryResults\":1",
    );
}

#[test]
fn wrong_completion_or_definition_answers_fail_the_contract() {
    let completion = |from: &str, to: &str| {
        assert!(COMPLETION.contains(from), "plant site {from} is gone");
        COMPLETION.replacen(from, to, 1)
    };
    let definition = |from: &str, to: &str| {
        assert!(DEFINITION.contains(from), "plant site {from} is gone");
        DEFINITION.replacen(from, to, 1)
    };
    let planted = [
        // A snippet the server never sends, an out-of-range kind, an empty label.
        (
            "textDocument/completion",
            completion(r#""insertTextFormat":1"#, r#""insertTextFormat":2"#),
        ),
        (
            "textDocument/completion",
            completion(r#""kind":21"#, r#""kind":99"#),
        ),
        (
            "textDocument/completion",
            completion(r#""label":"value""#, r#""label":"""#),
        ),
        // An edit spanning two lines, and one whose end precedes its start.
        (
            "textDocument/completion",
            completion(r#""end":{"line":1,"#, r#""end":{"line":2,"#),
        ),
        (
            "textDocument/completion",
            completion(r#""character":5}"#, r#""character":1}"#),
        ),
        (
            "textDocument/completion",
            completion(r#""isIncomplete":true,"#, ""),
        ),
        (
            "textDocument/completion",
            completion(r#""newText":"_root_.value""#, r#""newText":7"#),
        ),
        (
            "textDocument/completion",
            r#"{"isIncomplete":false,"items":{}}"#.to_owned(),
        ),
        // A bare item array is a legal LSP shape, but not this server's.
        ("textDocument/completion", r#"[]"#.to_owned()),
        // An empty target range, a missing URI, a control character in the URI.
        (
            "textDocument/definition",
            definition(r#""character":8}"#, r#""character":3}"#),
        ),
        (
            "textDocument/definition",
            definition(r#""uri":"file:///Lib%20One.lean","#, ""),
        ),
        (
            "textDocument/definition",
            definition("file:///Lib%20One.lean", r"file:///Lib\tOne.lean"),
        ),
        // A Location array is a legal LSP shape, but not this server's.
        ("textDocument/definition", format!("[{DEFINITION}]")),
        // The other method's answer.
        ("textDocument/definition", COMPLETION.to_owned()),
        ("textDocument/completion", DEFINITION.to_owned()),
        ("$/lean/plainTermGoal", DEFINITION.to_owned()),
    ];
    for (method, payload) in planted {
        let output = join(method, &format!(r#""result":{payload}"#));
        assert!(!output.status.success(), "{method} accepted: {payload}");
        assert!(output.stdout.is_empty());
        assert!(!output.stderr.is_empty());
    }
    let too_many = COMPLETION.replacen(
        r#""items":[{"#,
        &format!(r#""items":[{}{{"#, r#"{"label":"x","kind":21,"insertTextFormat":1,"textEdit":{"range":{"start":{"line":1,"character":2},"end":{"line":1,"character":5}},"newText":"x"}},"#.repeat(256)),
        1,
    );
    assert!(
        !join(
            "textDocument/completion",
            &format!(r#""result":{too_many}"#)
        )
        .status
        .success()
    );
}

// The real dispatcher, end to end: what `fln serve-lsp` and `lean --server` actually send
// must pass the contract, and the same stream with one planted wrong answer must not.

struct Native;
impl fln_server::dispatch::WorkspaceChecker for Native {
    fn semantic_queries(&self) -> bool {
        true
    }
    fn query(
        &mut self,
        query: fln_server::dispatch::semantic::Query<'_>,
        _: &[fln_server::dispatch::OpenDocumentSource<'_>],
    ) -> Result<Option<fln_server::dispatch::semantic::Answer>, String> {
        use fln_server::dispatch::semantic::{Answer, CompletionItem, QueryKind};
        Ok(Some(match query.kind {
            QueryKind::Completion => Answer::Completion {
                items: vec![CompletionItem {
                    label: "value".to_owned(),
                    replacement: "_root_.value".to_owned(),
                }],
                range: 4..7,
                is_incomplete: false,
            },
            QueryKind::Definition => Answer::Definition {
                uri: "file:///Lib.lean".to_owned(),
                source: "def value := 1".to_owned(),
                range: 4..9,
            },
            QueryKind::Goals | QueryKind::Hover => return Ok(None),
        }))
    }
    fn check(
        &mut self,
        uri: &str,
        _: &str,
        _: &[fln_server::dispatch::OpenDocumentSource<'_>],
    ) -> Vec<String> {
        vec![format!(
            r#"{{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{{"uri":"{uri}","diagnostics":[]}}}}"#
        )]
    }
    fn affected(
        &mut self,
        _: &[String],
        _: &[fln_server::dispatch::OpenDocumentSource<'_>],
    ) -> Vec<String> {
        Vec::new()
    }
}

fn bodies(mut wire: &[u8]) -> Vec<String> {
    let mut out = Vec::new();
    while let Some(body) = fln_server::transport::read_message(&mut wire).unwrap() {
        out.push(String::from_utf8(body).unwrap());
    }
    out
}

fn correlate(client: &[String], server: &[String]) -> Output {
    let dir: PathBuf = std::env::temp_dir().join(format!(
        "fln-semantic-correlation-native-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&dir).unwrap();
    let c = dir.join("client.frames");
    let s = dir.join("server.frames");
    std::fs::write(&c, frame(client)).unwrap();
    std::fs::write(&s, frame(server)).unwrap();
    Command::new(env!("CARGO_BIN_EXE_fln-lsp-correlate"))
        .arg(&c)
        .arg(&s)
        .output()
        .unwrap()
}

#[test]
fn the_real_dispatchers_answers_pass_and_a_planted_wrong_answer_fails() {
    let client: Vec<String> = [
        r#"{"jsonrpc":"2.0","id":"init","method":"initialize","params":{}}"#,
        r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///Main.lean","version":7,"text":"😀val"}}}"#,
        r#"{"jsonrpc":"2.0","id":"completion","method":"textDocument/completion","params":{"textDocument":{"uri":"file:///Main.lean"},"position":{"line":0,"character":5}}}"#,
        r#"{"jsonrpc":"2.0","id":"definition","method":"textDocument/definition","params":{"textDocument":{"uri":"file:///Main.lean"},"position":{"line":0,"character":3}}}"#,
        r#"{"jsonrpc":"2.0","id":"end","method":"shutdown"}"#,
        r#"{"jsonrpc":"2.0","method":"exit"}"#,
    ]
    .map(str::to_owned)
    .to_vec();
    let mut output = Vec::new();
    let outcome = fln_server::dispatch::serve_workspace(
        &mut std::io::Cursor::new(frame(&client)),
        &mut output,
        &mut Native,
    )
    .unwrap();
    assert!(outcome.clean);
    let server = bodies(&output);
    let completion = server
        .iter()
        .position(|body| body.contains(r#""id":"completion","result":{"#))
        .expect("the dispatcher answered completion with a result");
    let definition = server
        .iter()
        .position(|body| body.contains(r#""id":"definition","result":{"uri":"file:///Lib.lean""#))
        .expect("the dispatcher answered definition with a Location");

    let honest = correlate(&client, &server);
    let receipt = String::from_utf8(honest.stdout).unwrap();
    assert!(
        honest.status.success(),
        "{receipt}{}",
        String::from_utf8_lossy(&honest.stderr)
    );
    assert!(receipt.contains("\"semanticQueryResults\":2"), "{receipt}");
    assert!(
        receipt.contains("\"methodContractViolations\":0"),
        "{receipt}"
    );

    for (index, from, to) in [
        (
            completion,
            r#""insertTextFormat":1"#,
            r#""insertTextFormat":2"#,
        ),
        (completion, r#""newText":"_root_.value""#, r#""newText":"""#),
        (
            definition,
            r#""end":{"line":0,"character":9}"#,
            r#""end":{"line":0,"character":4}"#,
        ),
    ] {
        let mut planted = server.clone();
        assert!(
            planted[index].contains(from),
            "plant site {from} is gone: {}",
            planted[index]
        );
        planted[index] = planted[index].replacen(from, to, 1);
        let output = correlate(&client, &planted);
        assert!(!output.status.success(), "planted {to} passed the contract");
        assert!(output.stdout.is_empty());
        assert!(!output.stderr.is_empty());
    }
}
