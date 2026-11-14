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
fn expression_reference<'a>(value: &'a str, expression: &str, key: &str) -> &'a str {
    let marker = format!(r#","subexprPos":"/"}},{{"text":{}}}]}}"#, quote(expression));
    let prefix = value
        .split_once(&marker)
        .unwrap_or_else(|| panic!("missing tagged expression {expression}: {value}"))
        .0;
    prefix
        .rsplit_once(&format!("\"{key}\":\""))
        .unwrap_or_else(|| panic!("missing expression reference {key}: {value}"))
        .1
        .split('"')
        .next()
        .unwrap()
}
fn info_call(id: &str, session: &str, key: &str, reference: &str) -> String {
    request(
        id,
        "$/lean/rpc/call",
        &format!(
            r#"{{"textDocument":{{"uri":"{URI}"}},"position":{{"line":0,"character":0}},"sessionId":"{session}","method":"Lean.Widget.InteractiveDiagnostics.infoToInteractive","params":{{"{key}":"{reference}"}}}}"#
        ),
    )
}
fn navigation_call(id: &str, session: &str, key: &str, reference: &str, kind: &str) -> String {
    request(
        id,
        "$/lean/rpc/call",
        &format!(
            r#"{{"textDocument":{{"uri":"{URI}"}},"position":{{"line":0,"character":0}},"sessionId":"{session}","method":"Lean.Widget.getGoToLocation","params":{{"kind":"{kind}","info":{{"{key}":"{reference}"}}}}}}"#
        ),
    )
}

fn location_link(line: usize, end: usize, selection: std::ops::Range<usize>) -> String {
    format!(
        r#"{{"targetUri":"{URI}","targetRange":{{"start":{{"line":{line},"character":0}},"end":{{"line":{line},"character":{end}}}}},"targetSelectionRange":{{"start":{{"line":{line},"character":{}}},"end":{{"line":{line},"character":{}}}}}}}"#,
        selection.start, selection.end,
    )
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
            init.contains("\"experimental\":{\"rpcProvider\":{\"rpcWireFormat\":\"v1\"}}"),
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
            let info = expression_reference(&goals, "P", key).to_owned();
            info.parse::<u64>().unwrap();
            let popup = client.exchange("popup", &info_call("popup", &session, key, &info));
            assert!(popup.contains(r#""exprExplicit":{"text":"P"}"#), "{popup}");
            assert!(popup.contains(r#""type":{"text":"Prop"}"#), "{popup}");
            assert!(!extract_string(&goals, "mvarId").is_empty());
            let context = goals.split_once("\"ctx\":").unwrap().1;
            let reference = extract_string(context, key);
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
            let current_info = expression_reference(&changed, "Q", key);
            let current_popup = client.exchange(
                "current-popup",
                &info_call("current-popup", &session, key, current_info),
            );
            assert!(
                current_popup.contains(r#""exprExplicit":{"text":"Q"}"#),
                "{current_popup}"
            );
            // Old references deliberately retain the earlier immutable proof
            // presentation; they must not silently requery the edited source.
            let old_popup =
                client.exchange("old-popup", &info_call("old-popup", &session, key, &info));
            assert!(
                old_popup.contains(r#""exprExplicit":{"text":"P"}"#),
                "{old_popup}"
            );
            client.send(&notification(
                "$/lean/rpc/release",
                &format!(
                    r#"{{"uri":"{URI}","sessionId":"{session}","refs":[{{"{key}":"{info}"}}]}}"#
                ),
            ));
            let released = client.exchange(
                "released-popup",
                &info_call("released-popup", &session, key, &info),
            );
            assert!(released.contains("\"code\":-32602"), "{released}");
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
fn both_doors_navigate_retained_native_goal_tags_to_checked_declarations_and_types() {
    let source = "-- 😀\r\ninductive Token where | mk\r\ndef value : Token := Token.mk\r\ndef pending (P : Prop) (β : P) : Token :=\r\n  let item : Token := value\r\n  by exact item";
    let expected_type = location_link(1, 26, 10..15);
    let expected_definition = location_link(2, "def value : Token := Token.mk".len(), 4..9);
    for (binary, args) in [
        (env!("CARGO_BIN_EXE_fln"), &["serve-lsp"][..]),
        (env!("CARGO_BIN_EXE_lean"), &["--server"][..]),
    ] {
        for (format, key) in [("v0", "p"), ("v1", "__rpcref")] {
            let mut client = Client::start(binary, args, format);
            client.open(source);
            let session = client.connect("connect");
            let goals = client.exchange(
                "goals",
                &call("goals", &session, "Lean.Widget.getInteractiveGoals", 5, 5),
            );
            let value = expression_reference(&goals, "value", key).to_owned();
            let token = expression_reference(&goals, "Token", key).to_owned();
            let local = expression_reference(&goals, "P", key).to_owned();
            for (kind, expected) in [
                ("declaration", &expected_definition),
                ("definition", &expected_definition),
                ("type", &expected_type),
            ] {
                let result =
                    client.exchange(kind, &navigation_call(kind, &session, key, &value, kind));
                assert!(
                    result.contains(&format!(r#""result":[{expected}]"#)),
                    "{result}"
                );
            }
            let result = client.exchange(
                "type-global",
                &navigation_call("type-global", &session, key, &token, "definition"),
            );
            assert!(
                result.contains(&format!(r#""result":[{expected_type}]"#)),
                "{result}"
            );
            for (reference, kind) in [(&local, "definition"), (&local, "type"), (&token, "type")] {
                let result = client.exchange(
                    "empty",
                    &navigation_call("empty", &session, key, reference, kind),
                );
                assert!(result.contains(r#""result":[]"#), "{result}");
            }
            client.change(2, &format!("\r\n{source}"));
            let new_goals = client.exchange(
                "new-goals",
                &call(
                    "new-goals",
                    &session,
                    "Lean.Widget.getInteractiveGoals",
                    6,
                    5,
                ),
            );
            let new_value = expression_reference(&new_goals, "value", key);
            let new_location = client.exchange(
                "new-location",
                &navigation_call("new-location", &session, key, new_value, "definition"),
            );
            assert!(
                new_location.contains(&format!(
                    r#""result":[{}]"#,
                    location_link(3, "def value : Token := Token.mk".len(), 4..9)
                )),
                "{new_location}"
            );
            let old = client.exchange(
                "old-location",
                &navigation_call("old-location", &session, key, &value, "definition"),
            );
            assert!(
                old.contains(&format!(r#""result":[{expected_definition}]"#)),
                "{old}"
            );
            client.send(&notification(
                "$/lean/rpc/release",
                &format!(
                    r#"{{"uri":"{URI}","sessionId":"{session}","refs":[{{"{key}":"{value}"}}]}}"#
                ),
            ));
            let released = client.exchange(
                "released",
                &navigation_call("released", &session, key, &value, "definition"),
            );
            assert!(released.contains(r#""code":-32602"#), "{released}");
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

#[test]
fn native_projected_diagnostics_reach_rpc_and_clear_after_a_checked_edit() {
    for (binary, args) in [
        (env!("CARGO_BIN_EXE_fln"), &["serve-lsp"][..]),
        (env!("CARGO_BIN_EXE_lean"), &["--server"][..]),
    ] {
        let mut client = Client::start(binary, args, "v1");
        client.open("module\nprelude\ndef broken : Prop := missing\n");
        let session = client.connect("connect");
        let diagnostics = client.exchange(
            "diagnostics",
            &call(
                "diagnostics",
                &session,
                "Lean.Widget.getInteractiveDiagnostics",
                2,
                0,
            ),
        );
        assert!(diagnostics.contains("\"result\":[{"), "{diagnostics}");
        assert!(
            diagnostics.contains("\"message\":{\"text\":"),
            "{diagnostics}"
        );
        assert!(diagnostics.contains("missing"), "{diagnostics}");
        assert!(
            client.log.iter().any(|message| {
                message.contains("\"method\":\"textDocument/publishDiagnostics\"")
                    && message.contains("missing")
            }),
            "RPC did not use the real checked diagnostic publication"
        );
        client.change(
            2,
            "module\nprelude\ndef identity (P : Prop) (h : P) : P := h\n",
        );
        let clean = client.exchange(
            "clean",
            &call(
                "clean",
                &session,
                "Lean.Widget.getInteractiveDiagnostics",
                2,
                0,
            ),
        );
        assert!(clean.contains("\"result\":[]"), "{clean}");
        client.finish();
    }
}

#[test]
fn diagnostic_highlighting_uses_the_live_pinned_wire_shape_and_session_guards() {
    // These results were compared with the locked Lean server in both wire
    // formats. In particular, the reference does not merge overlapping hits.
    let fixtures = [
        (
            "ana",
            r#"{"text":"banana"}"#,
            r#"{"append":[{"text":"b"},{"tag":["highlighted",{"text":"ana"}]},{"tag":["highlighted",{"text":"ana"}]}]}"#,
        ),
        (
            "βγ😀",
            r#"{"append":[{"text":"alphaβ"},{"text":"γ😀tail"}]}"#,
            r#"{"append":[{"append":[{"text":"alpha"},{"tag":["highlighted",{"text":"β"}]}]},{"append":[{"tag":["highlighted",{"text":"γ😀"}]},{"text":"tail"}]}]}"#,
        ),
        (
            "aaa",
            r#"{"append":[{"text":"aaa"},{"text":"a"}]}"#,
            r#"{"append":[{"tag":["highlighted",{"text":"aaa"}]},{"tag":["highlighted",{"text":"a"}]}]}"#,
        ),
        (
            "",
            r#"{"append":[{"text":""},{"append":[]},{"text":"😀"}]}"#,
            r#"{"append":[{"text":""},{"append":[]},{"text":"😀"}]}"#,
        ),
        ("a", r#"{"text":"A"}"#, r#"{"text":"A"}"#),
    ];
    let search = |id: &str, session: &str, query: &str, message: &str| {
        request(
            id,
            "$/lean/rpc/call",
            &format!(
                r#"{{"sessionId":{},"method":"Lean.Widget.highlightMatches","params":{{"query":{},"msg":{message}}},"textDocument":{{"uri":"{URI}"}},"position":{{"line":0,"character":0}}}}"#,
                quote(session),
                quote(query)
            ),
        )
    };
    for (binary, args) in [
        (env!("CARGO_BIN_EXE_fln"), &["serve-lsp"][..]),
        (env!("CARGO_BIN_EXE_lean"), &["--server"][..]),
    ] {
        for format in ["v0", "v1"] {
            let mut client = Client::start(binary, args, format);
            client.open("prelude\n");
            let session = client.connect("connect");
            for (index, (query, message, expected)) in fixtures.iter().enumerate() {
                let id = format!("highlight-{index}");
                let result = client.exchange(&id, &search(&id, &session, query, message));
                assert!(
                    result.contains(&format!("\"result\":{expected}")),
                    "{result}"
                );
            }
            let unsupported = client.exchange(
                "embedded",
                &search(
                    "embedded",
                    &session,
                    "x",
                    r#"{"tag":[{"expr":{"text":"x"}},{"text":""}]}"#,
                ),
            );
            assert!(unsupported.contains("\"code\":-32803"), "{unsupported}");
            client.send(&notification(
                "textDocument/didClose",
                &format!(r#"{{"textDocument":{{"uri":"{URI}"}}}}"#),
            ));
            client.open("prelude\n");
            let stale =
                client.exchange("stale", &search("stale", &session, "x", r#"{"text":"x"}"#));
            assert!(stale.contains("\"code\":-32900"), "{stale}");
            let session = client.connect("reconnect");
            let recovered = client.exchange(
                "recovered",
                &search("recovered", &session, "x", r#"{"text":"x"}"#),
            );
            assert!(
                recovered.contains(r#""result":{"tag":["highlighted",{"text":"x"}]}"#),
                "{recovered}"
            );
            client.finish();
        }
    }
}

#[test]
fn get_widgets_returns_empty_panel_list_and_enforces_bare_position_and_session_guards() {
    let widgets_call = |id: &str, session: &str, params: &str| {
        request(
            id,
            "$/lean/rpc/call",
            &format!(
                r#"{{"sessionId":{},"method":"Lean.Widget.getWidgets","params":{params},"textDocument":{{"uri":"{URI}"}},"position":{{"line":0,"character":0}}}}"#,
                quote(session),
            ),
        )
    };
    for (binary, args) in [
        (env!("CARGO_BIN_EXE_fln"), &["serve-lsp"][..]),
        (env!("CARGO_BIN_EXE_lean"), &["--server"][..]),
    ] {
        for format in ["v0", "v1"] {
            let mut client = Client::start(binary, args, format);
            client.open("-- 😀\r\nprelude\r\ndef x (P : Prop) (h : P) : P := h\r\n");
            let session = client.connect("connect");
            for (index, pos) in [
                r#"{"line":2,"character":0}"#,
                r#"{"line":99,"character":99}"#,
            ]
            .iter()
            .enumerate()
            {
                let id = format!("widgets-{index}");
                let reply = client.exchange(&id, &widgets_call(&id, &session, pos));
                assert!(reply.contains(r#""result":{"widgets":[]}"#), "{reply}");
            }
            for (index, bad) in [
                "null",
                r#"{"line":-1,"character":0}"#,
                r#"{"line":0,"character":4}"#,
                r#"{"textDocument":{"uri":"file:///FlnRpc.lean"},"position":{"line":2,"character":0}}"#,
            ]
            .iter()
            .enumerate()
            {
                let id = format!("bad-widgets-{index}");
                let reply = client.exchange(&id, &widgets_call(&id, &session, bad));
                assert!(reply.contains("\"code\":-32602"), "{bad}: {reply}");
            }
            client.send(&notification(
                "textDocument/didClose",
                &format!(r#"{{"textDocument":{{"uri":"{URI}"}}}}"#),
            ));
            client.open("prelude\n");
            let stale = client.exchange(
                "stale-widgets",
                &widgets_call("stale-widgets", &session, r#"{"line":0,"character":0}"#),
            );
            assert!(stale.contains("\"code\":-32900"), "{stale}");
            client.finish();
        }
    }
}
