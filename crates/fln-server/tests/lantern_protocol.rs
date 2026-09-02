#![forbid(unsafe_code)]

use std::io::BufReader;

use fln_server::dispatch::{ServerOutcome, serve};
use fln_server::transport::{read_message, write_message};

fn frame(output: &mut Vec<u8>, body: &[u8]) {
    write_message(output, body).expect("frame test input");
}

fn framed_json(output: &mut Vec<u8>, body: &str) {
    frame(output, body.as_bytes());
}

fn protocol_session(extra: &[&str]) -> Vec<u8> {
    let mut input = Vec::new();
    framed_json(
        &mut input,
        r#"{"jsonrpc":"2.0","id":"init","method":"initialize","params":{}}"#,
    );
    framed_json(
        &mut input,
        r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
    );
    for message in extra {
        framed_json(&mut input, message);
    }
    framed_json(
        &mut input,
        r#"{"jsonrpc":"2.0","id":99,"method":"shutdown","params":null}"#,
    );
    framed_json(
        &mut input,
        r#"{"jsonrpc":"2.0","method":"exit","params":null}"#,
    );
    input
}

fn decode_frames(output: &[u8]) -> Vec<String> {
    let mut reader = BufReader::new(output);
    let mut messages = Vec::new();
    while let Some(body) = read_message(&mut reader).expect("decode server frame") {
        messages.push(String::from_utf8(body).expect("server emits UTF-8 JSON"));
    }
    messages
}

fn run(
    input: Vec<u8>,
    callback: &mut dyn FnMut(&str, &str) -> Vec<String>,
) -> (ServerOutcome, Vec<String>) {
    let mut reader = BufReader::new(input.as_slice());
    let mut output = Vec::new();
    let outcome = serve(&mut reader, &mut output, callback).expect("serve protocol transcript");
    (outcome, decode_frames(&output))
}

#[test]
fn full_sync_transcript_is_ordered_versioned_and_cleanly_closed() {
    let input = protocol_session(&[
        r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///Main.lean","languageId":"lean4","version":1,"text":"def x := 1"}}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///Main.lean","version":2},"contentChanges":[{"text":"def x := 2"}]}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didSave","params":{"textDocument":{"uri":"file:///Main.lean"}}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didClose","params":{"textDocument":{"uri":"file:///Main.lean"}}}"#,
    ]);
    let mut seen = Vec::new();
    let (outcome, output) = run(input, &mut |uri, text| {
        seen.push((uri.to_string(), text.to_string()));
        vec![format!(
            "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",\"params\":{{\"uri\":{},\"diagnostics\":[]}}}}",
            fln_server::json_string(uri)
        )]
    });

    assert!(outcome.clean);
    assert_eq!(outcome.documents_opened, 1);
    assert_eq!(outcome.documents_changed, 1);
    assert_eq!(outcome.documents_saved, 1);
    assert_eq!(
        seen,
        vec![
            ("file:///Main.lean".to_string(), "def x := 1".to_string()),
            ("file:///Main.lean".to_string(), "def x := 2".to_string()),
            ("file:///Main.lean".to_string(), "def x := 2".to_string()),
        ]
    );
    assert!(output[0].contains("\"id\":\"init\""));
    assert!(output[0].contains("\"positionEncoding\":\"utf-16\""));
    assert_eq!(
        output
            .iter()
            .filter(|message| message.contains("$/lean/fileProgress"))
            .count(),
        6
    );
    assert!(output.iter().any(|message| {
        message.contains("textDocument/publishDiagnostics")
            && message.contains("\"uri\":\"file:///Main.lean\"")
            && message.contains("\"diagnostics\":[]")
    }));
    assert!(output.iter().any(|message| {
        message.contains("\"id\":99") && message.contains("\"result\":null")
    }));
}

#[test]
fn malformed_json_recovers_before_the_next_request() {
    let input = protocol_session(&[
        r#"{"jsonrpc":"2.0","id":5,"method":"textDocument/hover","params":{"bad":tru}}"#,
        r#"{"jsonrpc":"2.0","id":6,"method":"textDocument/hover","params":{}}"#,
    ]);
    let (outcome, output) = run(input, &mut |_, _| Vec::new());
    assert!(outcome.clean);
    assert!(output.iter().any(|message| {
        message.contains("\"id\":null") && message.contains("\"code\":-32700")
    }));
    assert!(output.iter().any(|message| {
        message.contains("\"id\":6") && message.contains("\"result\":null")
    }));
}

#[test]
fn invalid_utf8_recovers_before_the_next_request() {
    let mut input = Vec::new();
    framed_json(
        &mut input,
        r#"{"jsonrpc":"2.0","id":"init","method":"initialize","params":{}}"#,
    );
    framed_json(
        &mut input,
        r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
    );
    frame(&mut input, &[0xff, 0xfe]);
    framed_json(
        &mut input,
        r#"{"jsonrpc":"2.0","id":7,"method":"textDocument/hover","params":{}}"#,
    );
    framed_json(
        &mut input,
        r#"{"jsonrpc":"2.0","id":99,"method":"shutdown"}"#,
    );
    framed_json(
        &mut input,
        r#"{"jsonrpc":"2.0","method":"exit"}"#,
    );

    let (outcome, output) = run(input, &mut |_, _| Vec::new());
    assert!(outcome.clean);
    assert!(output.iter().any(|message| {
        message.contains("\"id\":null")
            && message.contains("\"code\":-32700")
            && message.contains("not valid UTF-8")
    }));
    assert!(output.iter().any(|message| {
        message.contains("\"id\":7") && message.contains("\"result\":null")
    }));
}

#[test]
fn empty_callback_cannot_masquerade_as_a_clean_diagnostic_result() {
    let input = protocol_session(&[
        r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///Fault.lean","version":1,"text":"source"}}}"#,
    ]);
    let (outcome, output) = run(input, &mut |_, _| Vec::new());

    assert!(outcome.clean);
    assert_eq!(outcome.documents_opened, 1);
    assert!(output.iter().any(|message| {
        message.contains("textDocument/publishDiagnostics")
            && message.contains("\"uri\":\"file:///Fault.lean\"")
            && message.contains("\"diagnostics\":[]")
    }));
    assert!(output.iter().any(|message| {
        message.contains("$/lean/diagnosticOutcome")
            && message.contains("diagnostic-callback-terminal-message")
            && message.contains("\"authority\":false")
    }));
}

#[test]
fn callback_terminal_detection_is_structural_and_uri_bound() {
    let input = protocol_session(&[
        r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///Primary.lean","version":1,"text":"source"}}}"#,
    ]);
    let (outcome, output) = run(input, &mut |_, _| {
        vec![
            r#"{"jsonrpc":"2.0","method":"window/logMessage","params":{"type":3,"message":"\"method\":\"textDocument/publishDiagnostics\""}}"#.to_string(),
            r#"{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file:///Other.lean","diagnostics":[]}}"#.to_string(),
        ]
    });

    assert!(outcome.clean);
    assert!(output.iter().any(|message| {
        message.contains("\"uri\":\"file:///Other.lean\"")
            && message.contains("textDocument/publishDiagnostics")
    }));
    assert!(output.iter().any(|message| {
        message.contains("\"uri\":\"file:///Primary.lean\"")
            && message.contains("\"diagnostics\":[]")
    }));
    assert!(output.iter().any(|message| {
        message.contains("diagnostic-callback-terminal-message")
            && message.contains("\"authority\":false")
    }));
}

#[test]
fn malformed_callback_output_is_withheld_and_faulted() {
    let input = protocol_session(&[
        r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///Fault.lean","version":1,"text":"source"}}}"#,
    ]);
    let (outcome, output) = run(input, &mut |_, _| {
        vec!["{malformed-callback".to_string()]
    });

    assert!(outcome.clean);
    assert!(output.iter().any(|message| {
        message.contains("discarded malformed diagnostic callback output")
    }));
    assert!(!output
        .iter()
        .any(|message| message.contains("{malformed-callback")));
    assert!(output.iter().any(|message| {
        message.contains("diagnostic-callback-terminal-message")
            && message.contains("\"authority\":false")
    }));
}

#[test]
fn request_notification_roles_and_server_state_fail_closed() {
    let mut input = Vec::new();
    for message in [
        r#"{"jsonrpc":"2.0","id":1,"method":"textDocument/hover","params":{}}"#,
        r#"{"jsonrpc":"2.0","id":"init","method":"initialize","params":{}}"#,
        r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
        r#"{"jsonrpc":"2.0","id":2,"method":"textDocument/didOpen","params":{}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/hover","params":{}}"#,
        r#"{"jsonrpc":"2.0","id":3,"method":"$/lean/rpc/connect","params":{}}"#,
        r#"{"jsonrpc":"2.0","id":99,"method":"shutdown"}"#,
        r#"{"jsonrpc":"2.0","method":"exit"}"#,
    ] {
        framed_json(&mut input, message);
    }

    let (outcome, output) = run(input, &mut |_, _| Vec::new());
    assert!(outcome.clean);
    assert!(output.iter().any(|message| {
        message.contains("\"id\":1") && message.contains("\"code\":-32002")
    }));
    assert!(output.iter().any(|message| {
        message.contains("\"id\":2") && message.contains("\"code\":-32600")
    }));
    assert!(output.iter().any(|message| {
        message.contains("request-only LSP method sent as a notification")
    }));
    assert!(output.iter().any(|message| {
        message.contains("\"id\":3") && message.contains("\"code\":-32803")
    }));
}

#[test]
fn wait_for_diagnostics_completes_only_after_requested_publication() {
    let input = protocol_session(&[
        r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///Wait.lean","version":1,"text":"v1"}}}"#,
        r#"{"jsonrpc":"2.0","id":"ready","method":"textDocument/waitForDiagnostics","params":{"uri":"file:///Wait.lean","version":1}}"#,
        r#"{"jsonrpc":"2.0","id":"future","method":"textDocument/waitForDiagnostics","params":{"uri":"file:///Wait.lean","version":3}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///Wait.lean","version":2},"contentChanges":[{"text":"v2"}]}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///Wait.lean","version":3},"contentChanges":[{"text":"v3"}]}}"#,
    ]);
    let (outcome, output) = run(input, &mut |uri, text| {
        vec![format!(
            "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",\"params\":{{\"uri\":{},\"diagnostics\":[{{\"message\":{}}}]}}}}",
            fln_server::json_string(uri),
            fln_server::json_string(text)
        )]
    });

    assert!(outcome.clean);
    let ready = output
        .iter()
        .position(|message| message.contains("\"id\":\"ready\",\"result\":{}"))
        .expect("ready wait response");
    let version_three = output
        .iter()
        .position(|message| {
            message.contains("textDocument/publishDiagnostics")
                && message.contains("\"message\":\"v3\"")
        })
        .expect("version-three diagnostic publication");
    let future = output
        .iter()
        .position(|message| message.contains("\"id\":\"future\",\"result\":{}"))
        .expect("future wait response");
    assert!(ready < version_three);
    assert!(version_three < future);
}

#[test]
fn waits_follow_terminal_authority_and_can_recover_at_the_same_version() {
    let input = protocol_session(&[
        r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///Wait.lean","version":1,"text":"v1"}}}"#,
        r#"{"jsonrpc":"2.0","id":"failed","method":"textDocument/waitForDiagnostics","params":{"uri":"file:///Wait.lean","version":1}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didSave","params":{"textDocument":{"uri":"file:///Wait.lean"},"text":"v1"}}"#,
        r#"{"jsonrpc":"2.0","id":"recovered","method":"textDocument/waitForDiagnostics","params":{"uri":"file:///Wait.lean","version":1}}"#,
    ]);
    let mut callback_count = 0usize;
    let (outcome, output) = run(input, &mut |uri, _| {
        callback_count += 1;
        if callback_count == 1 {
            Vec::new()
        } else {
            vec![format!(
                "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",\"params\":{{\"uri\":{},\"diagnostics\":[]}}}}",
                fln_server::json_string(uri)
            )]
        }
    });

    assert!(outcome.clean);
    assert!(output.iter().any(|message| {
        message.contains("\"id\":\"failed\"") && message.contains("\"code\":-32803")
    }));
    assert!(output.iter().any(|message| {
        message.contains("\"id\":\"recovered\"")
            && message.contains("\"result\":{}")
    }));
}

#[test]
fn future_wait_fails_when_target_publication_is_nonauthoritative() {
    let input = protocol_session(&[
        r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///Wait.lean","version":1,"text":"v1"}}}"#,
        r#"{"jsonrpc":"2.0","id":"future","method":"textDocument/waitForDiagnostics","params":{"uri":"file:///Wait.lean","version":2}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///Wait.lean","version":2},"contentChanges":[{"text":"v2"}]}}"#,
    ]);
    let mut callback_count = 0usize;
    let (outcome, output) = run(input, &mut |uri, _| {
        callback_count += 1;
        if callback_count == 1 {
            vec![format!(
                "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",\"params\":{{\"uri\":{},\"diagnostics\":[]}}}}",
                fln_server::json_string(uri)
            )]
        } else {
            Vec::new()
        }
    });

    assert!(outcome.clean);
    assert_eq!(
        output
            .iter()
            .filter(|message| message.contains("\"id\":\"future\""))
            .count(),
        1
    );
    assert!(output.iter().any(|message| {
        message.contains("\"id\":\"future\"") && message.contains("\"code\":-32803")
    }));
}

#[test]
fn pending_waits_cancel_close_or_shutdown_exactly_once() {
    let input = protocol_session(&[
        r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///Wait.lean","version":1,"text":"v1"}}}"#,
        r#"{"jsonrpc":"2.0","id":"cancelled","method":"textDocument/waitForDiagnostics","params":{"uri":"file:///Wait.lean","version":9}}"#,
        r#"{"jsonrpc":"2.0","method":"$/cancelRequest","params":{"id":"cancelled"}}"#,
        r#"{"jsonrpc":"2.0","id":"closed","method":"textDocument/waitForDiagnostics","params":{"uri":"file:///Wait.lean","version":9}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didClose","params":{"textDocument":{"uri":"file:///Wait.lean"}}}"#,
    ]);
    let (outcome, output) = run(input, &mut |uri, _| {
        vec![format!(
            "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",\"params\":{{\"uri\":{},\"diagnostics\":[]}}}}",
            fln_server::json_string(uri)
        )]
    });

    assert!(outcome.clean);
    assert_eq!(
        output
            .iter()
            .filter(|message| message.contains("\"id\":\"cancelled\""))
            .count(),
        1
    );
    assert!(output.iter().any(|message| {
        message.contains("\"id\":\"cancelled\"") && message.contains("\"code\":-32800")
    }));
    assert_eq!(
        output
            .iter()
            .filter(|message| message.contains("\"id\":\"closed\""))
            .count(),
        1
    );
    assert!(output.iter().any(|message| {
        message.contains("\"id\":\"closed\"")
            && message.contains("\"code\":-32803")
            && message.contains("document closed before the requested diagnostics version")
    }));
}

#[test]
fn pending_wait_is_failed_once_by_shutdown() {
    let input = protocol_session(&[
        r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///Wait.lean","version":1,"text":"v1"}}}"#,
        r#"{"jsonrpc":"2.0","id":"shutdown-wait","method":"textDocument/waitForDiagnostics","params":{"uri":"file:///Wait.lean","version":99}}"#,
    ]);
    let (outcome, output) = run(input, &mut |uri, _| {
        vec![format!(
            "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",\"params\":{{\"uri\":{},\"diagnostics\":[]}}}}",
            fln_server::json_string(uri)
        )]
    });

    assert!(outcome.clean);
    assert_eq!(
        output
            .iter()
            .filter(|message| message.contains("\"id\":\"shutdown-wait\""))
            .count(),
        1
    );
    assert!(output.iter().any(|message| {
        message.contains("\"id\":\"shutdown-wait\"")
            && message.contains("\"code\":-32803")
            && message.contains("server shut down before the requested diagnostics version")
    }));
}
