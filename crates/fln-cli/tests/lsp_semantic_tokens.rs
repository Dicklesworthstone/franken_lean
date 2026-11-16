//! Both installed front doors exercise native source syntax and LSP deltas.
#![forbid(unsafe_code)]
use std::io::{Cursor, Write};
use std::process::{Command, Stdio};

const URI: &str = "file:///tmp/fln-semantic-tokens.lean";

fn quoted(text: &str) -> String {
    fln_server::json_string(text)
}

fn open(text: &str) -> String {
    format!(
        "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{{\"textDocument\":{{\"uri\":{},\"languageId\":\"lean4\",\"version\":1,\"text\":{}}}}}}}",
        quoted(URI),
        quoted(text)
    )
}

fn request(id: usize, range: Option<&str>) -> String {
    let method = if range.is_some() { "range" } else { "full" };
    let range = range.map_or(String::new(), |range| format!(",\"range\":{range}"));
    format!(
        "{{\"jsonrpc\":\"2.0\",\"id\":{id},\"method\":\"textDocument/semanticTokens/{method}\",\"params\":{{\"textDocument\":{{\"uri\":{}}}{range}}}}}",
        quoted(URI)
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
    assert!(messages.iter().any(|message| message.contains(r#""semanticTokensProvider":{"legend":{"tokenTypes":["keyword","variable","property","function""#)));
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
    let selected: Vec<_> = messages
        .iter()
        .filter(|message| message.contains(&key))
        .collect();
    assert_eq!(
        selected.len(),
        1,
        "missing or duplicate response {id}: {messages:?}"
    );
    selected[0]
}

fn tokens(messages: &[String], id: usize) -> Vec<[u32; 4]> {
    let response = response(messages, id);
    let data = response
        .split_once("\"data\":[")
        .unwrap_or_else(|| panic!("{response}"))
        .1
        .split_once(']')
        .unwrap()
        .0;
    let data: Vec<u32> = if data.is_empty() {
        Vec::new()
    } else {
        data.split(',')
            .map(|field| field.parse().unwrap())
            .collect()
    };
    assert_eq!(data.len() % 5, 0);
    let mut last = (0, 0);
    data.chunks_exact(5)
        .map(|token| {
            last.0 += token[0];
            last.1 = if token[0] == 0 {
                last.1 + token[1]
            } else {
                token[1]
            };
            assert_eq!(token[4], 0);
            [last.0, last.1, token[2], token[3]]
        })
        .collect()
}

#[test]
fn both_front_doors_highlight_original_syntax_with_utf16_crlf_and_pin_range_selection() {
    let source = "-- namespace def\r\nnamespace Highlight\r\ndef «😀» : Nat := by exact 1\r\ndef value : Nat := «😀»\r\nend Highlight\r\n";
    let expected = vec![
        [1, 0, 9, 0],
        [2, 0, 3, 0],
        [2, 18, 2, 0],
        [2, 21, 5, 0],
        [3, 0, 3, 0],
        [4, 0, 3, 0],
    ];
    for (binary, argument) in front_doors() {
        let messages = run(
            binary,
            argument,
            &[
                open(source),
                request(20, None),
                request(
                    21,
                    Some(r#"{"start":{"line":2,"character":19},"end":{"line":2,"character":22}}"#),
                ),
                request(
                    22,
                    Some(r#"{"start":{"line":2,"character":6},"end":{"line":3,"character":0}}"#),
                ),
                request(
                    23,
                    Some(r#"{"start":{"line":3,"character":0},"end":{"line":2,"character":0}}"#),
                ),
            ],
        );
        assert_eq!(tokens(&messages, 20), expected);
        // `by` begins before the range; `exact` starts inside and is not clipped.
        assert_eq!(tokens(&messages, 21), vec![[2, 21, 5, 0]]);
        assert!(response(&messages, 22).contains(r#""error":{"code":-32602"#));
        assert!(response(&messages, 23).contains(r#""error":{"code":-32602"#));
    }
}

#[test]
fn both_front_doors_highlight_parser_projections_and_scoped_custom_syntax() {
    let source = "structure Entry where\n  value : Nat\ndef get (entry : Entry) : Nat := (entry).value\nnamespace Tokens\nscoped notation \"magic\" => 7\nend Tokens\nopen scoped Tokens in\ndef answer : Nat := magic\n";
    for (binary, argument) in front_doors() {
        let messages = run(binary, argument, &[open(source), request(30, None)]);
        assert_eq!(
            tokens(&messages, 30),
            vec![
                [0, 0, 9, 0],
                [0, 16, 5, 0],
                [2, 0, 3, 0],
                [2, 41, 5, 2],
                [3, 0, 9, 0],
                [4, 0, 6, 0],
                [4, 7, 8, 0],
                [5, 0, 3, 0],
                [6, 0, 4, 0],
                [6, 5, 6, 0],
                [6, 19, 2, 0],
                [7, 0, 3, 0],
                [7, 20, 5, 0],
            ]
        );
    }
}

#[test]
fn both_front_doors_invalidate_tokens_when_document_source_is_lost_and_recover_on_save() {
    for (binary, argument) in front_doors() {
        let messages = run(
            binary,
            argument,
            &[
                open("def first : Nat := 1"),
                request(40, None),
                format!(
                    "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\",\"params\":{{\"textDocument\":{{\"uri\":{},\"version\":2}},\"contentChanges\":null}}}}",
                    quoted(URI)
                ),
                request(41, None),
                format!(
                    "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didSave\",\"params\":{{\"textDocument\":{{\"uri\":{}}},\"text\":\"-- recovered\\ndef second : Nat := 2\"}}}}",
                    quoted(URI)
                ),
                request(42, None),
            ],
        );
        assert_eq!(tokens(&messages, 40), vec![[0, 0, 3, 0]]);
        assert!(response(&messages, 41).contains(r#""error":{"code":-32803"#));
        assert!(!response(&messages, 41).contains("\"result\""));
        assert_eq!(tokens(&messages, 42), vec![[1, 0, 3, 0]]);
    }
}
