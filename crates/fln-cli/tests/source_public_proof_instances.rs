//! Installed module and editor doors consume authored proof-class instances.
//! All dependencies are ordinary checked source files, with no seeded Init.
#![forbid(unsafe_code)]

use std::io::{Cursor, Write};
use std::path::PathBuf;
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT: AtomicUsize = AtomicUsize::new(0);

struct Project(PathBuf);
impl Project {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "fln-public-proof-instances-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir(&path).unwrap();
        let project = Self(path);
        project.write("Base.lean", BASE);
        project.write("Secret.lean", SECRET);
        project
    }

    fn write(&self, name: &str, source: &str) {
        std::fs::write(self.0.join(name), source).unwrap();
    }

    fn uri(&self, name: &str) -> String {
        format!("file://{}", self.0.join(name).display())
    }

    fn command(&self, verb: &str) -> Output {
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args([verb, "--json", "Main.lean"])
            .current_dir(&self.0)
            .env("LEAN_PATH", &self.0)
            .output()
            .unwrap()
    }

    fn complete(&self, verb: &str) -> String {
        let output = self.command(verb);
        assert!(output.status.success(), "{output:?}");
        assert!(output.stderr.is_empty(), "{output:?}");
        let text = String::from_utf8(output.stdout).unwrap();
        assert!(text.contains("\"outcome\":\"complete\""), "{text}");
        text
    }

    fn lean(&self) -> Output {
        Command::new(env!("CARGO_BIN_EXE_lean"))
            .arg("Main.lean")
            .current_dir(&self.0)
            .env("LEAN_PATH", &self.0)
            .output()
            .unwrap()
    }

    fn server(&self, binary: &str, argument: &str, messages: Vec<String>) -> Vec<String> {
        let mut input = Vec::new();
        for message in [
            r#"{"jsonrpc":"2.0","id":"init","method":"initialize","params":{}}"#.to_owned(),
            r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#.to_owned(),
        ]
        .into_iter()
        .chain(messages)
        .chain([
            r#"{"jsonrpc":"2.0","id":"shutdown","method":"shutdown"}"#.to_owned(),
            r#"{"jsonrpc":"2.0","method":"exit"}"#.to_owned(),
        ]) {
            fln_server::transport::write_message(&mut input, message.as_bytes()).unwrap();
        }
        let mut child = Command::new(binary)
            .arg(argument)
            .current_dir(&self.0)
            .env("LEAN_PATH", &self.0)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        let mut stdin = child.stdin.take().unwrap();
        let writer = std::thread::spawn(move || stdin.write_all(&input));
        let output = child.wait_with_output().unwrap();
        writer.join().unwrap().unwrap();
        assert!(output.status.success(), "{output:?}");
        assert!(output.stderr.is_empty(), "{output:?}");
        let mut stream = Cursor::new(output.stdout);
        let mut replies = Vec::new();
        while let Some(body) = fln_server::transport::read_message(&mut stream).unwrap() {
            replies.push(String::from_utf8(body).unwrap());
        }
        replies
    }
}

impl Drop for Project {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

const BASE: &str = "prelude\ninductive Truth : Prop where\n| make\nclass Law (P : Prop) : Prop where\n  proof : P\ndef chosenLaw (P : Prop) [law : Law P] : Law P := law\ninductive Bool where\n| false\n| true\nclass Pick where\n  value : Bool";
const SECRET: &str = "prelude\nimport Base\ndef hiddenProof : Truth := Truth.make\ndef Hidden (P : Prop) : Prop := P\ninductive Secret : Prop where\n| make";
const HEADER: &str = "module\nprelude\npublic import Base\nimport Secret\n";

#[test]
fn installed_doors_check_imported_proof_instances_and_execute_exposed_data() {
    let project = Project::new();
    project.write("Api.lean", &format!("{HEADER}private theorem helper : Truth := hiddenProof\npublic instance (priority := 1600) witnessed : Law Truth := Law.mk helper\npublic instance {{P : Prop}} [law : Law P] : Law (Law P) := Law.mk law\npublic instance data : Pick := Pick.mk Bool.true"));
    project.write("Facade.lean", "module\nprelude\npublic import Api");
    let main = "prelude\nimport Facade\ntheorem client : Truth := @Law.proof Truth (@Law.proof (Law Truth) (chosenLaw (Law Truth)))";
    project.write("Main.lean", main);
    project.complete("check-source");
    let lean = project.lean();
    assert!(lean.status.success(), "{lean:?}");
    assert!(lean.stderr.is_empty(), "{lean:?}");
    assert!(lean.stdout.is_empty(), "{lean:?}");
    project.write("Main.lean", &format!("{main}\n#eval Pick.value"));
    let runtime = project.complete("run");
    assert!(
        runtime.contains("\"kind\":\"bool\",\"value\":true"),
        "{runtime}"
    );
}

#[test]
fn installed_hidden_headers_bad_proofs_and_exposed_private_bodies_refuse_then_recover() {
    let project = Project::new();
    project.write(
        "Main.lean",
        "prelude\nimport Api\ntheorem client : Truth := @Law.proof Truth (chosenLaw Truth)",
    );
    let good = format!("{HEADER}public instance witnessed : Law Truth := Law.mk hiddenProof");
    project.write("Api.lean", &good);
    project.complete("check-source");
    for bad in [
        "public instance leaked : Law Secret := Law.mk Secret.make",
        "public instance invalid (P Q : Prop) (proof : P) : Law Q := Law.mk proof",
        "@[expose] public instance leaked : Law Truth := Law.mk hiddenProof",
    ] {
        project.write("Api.lean", &format!("{HEADER}{bad}"));
        for verb in ["check-source", "run"] {
            let output = project.command(verb);
            assert!(!output.status.success(), "{bad}: {output:?}");
            assert!(
                output.stdout.is_empty(),
                "a failed module published output: {output:?}"
            );
            assert!(!output.stderr.is_empty(), "missing refusal: {output:?}");
        }
        assert!(!project.lean().status.success(), "{bad}");
        project.write("Api.lean", &good);
        project.complete("check-source");
        project.complete("run");
    }
}

fn quoted(text: &str) -> String {
    let mut result = String::from("\"");
    for c in text.chars() {
        match c {
            '\\' => result.push_str("\\\\"),
            '"' => result.push_str("\\\""),
            '\n' => result.push_str("\\n"),
            '\r' => result.push_str("\\r"),
            '\t' => result.push_str("\\t"),
            c if c.is_control() => result.push_str(&format!("\\u{:04x}", u32::from(c))),
            c => result.push(c),
        }
    }
    result.push('"');
    result
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

fn query(id: &str, method: &str, uri: &str, text: &str, offset: usize) -> String {
    let prefix = &text[..offset];
    let line = prefix.bytes().filter(|b| *b == b'\n').count();
    let column = prefix.rsplit('\n').next().unwrap().encode_utf16().count();
    format!(
        "{{\"jsonrpc\":\"2.0\",\"id\":{},\"method\":{},\"params\":{{\"textDocument\":{{\"uri\":{}}},\"position\":{{\"line\":{line},\"character\":{column}}}}}}}",
        quoted(id),
        quoted(method),
        quoted(uri)
    )
}

fn reply<'a>(messages: &'a [String], id: &str) -> &'a str {
    let key = format!("\"id\":{}", quoted(id));
    let selected: Vec<_> = messages
        .iter()
        .filter(|message| message.contains(&key))
        .collect();
    assert_eq!(selected.len(), 1, "{id}: {messages:#?}");
    selected[0]
}

#[test]
fn both_editor_doors_classify_proof_headers_before_using_the_private_body_world() {
    let project = Project::new();
    let uri = project.uri("Api.lean");
    let prefix = format!(
        "{HEADER}namespace Proofs\npublic class OpenLaw (P : Prop) : Prop where\n  proof : P\nend Proofs\nprivate theorem hiddenLocal : Truth := hiddenProof\n"
    );
    let pending = format!("{prefix}public instance pending : Law Truth := by");
    let complete = format!("{pending}\n  exact Law.mk hiddenLocal");
    let bad_header = format!(
        "{prefix}public instance pending : Law (Hidden Truth) := by exact Law.mk hiddenLocal"
    );
    let bad_proof = format!("{pending}\n  exact Law.mk missingProof");
    let body_completion = format!("{prefix}public instance pending : Law Truth := Law.mk hid");
    let header_completion = format!("{prefix}public instance pending : Law hid");
    let exposed_completion =
        format!("{prefix}@[expose] public instance pending : Law Truth := Law.mk hid");
    let wrapped_body_completion = format!(
        "{prefix}set_option maxRecDepth 2048 in open Proofs in public instance pending : OpenLaw Truth := OpenLaw.mk hid"
    );
    let wrapped_header_completion = format!(
        "{prefix}set_option maxRecDepth 2048 in open Proofs in public instance pending : OpenLaw hid"
    );
    let wrapped_exposed_completion = format!(
        "{prefix}set_option maxRecDepth 2048 in open Proofs in @[expose] public instance pending : OpenLaw Truth := OpenLaw.mk hid"
    );
    for (binary, argument) in [
        (env!("CARGO_BIN_EXE_fln"), "serve-lsp"),
        (env!("CARGO_BIN_EXE_lean"), "--server"),
    ] {
        let messages = project.server(
            binary,
            argument,
            vec![
                open(&uri, &pending),
                query("goal", "$/lean/plainGoal", &uri, &pending, pending.len()),
                query("warm", "$/lean/plainGoal", &uri, &pending, pending.len()),
                change(&uri, 2, &complete),
                query(
                    "proved",
                    "$/lean/plainGoal",
                    &uri,
                    &complete,
                    complete.len(),
                ),
                query(
                    "hover",
                    "textDocument/hover",
                    &uri,
                    &complete,
                    complete.rfind("hiddenLocal").unwrap() + 2,
                ),
                change(&uri, 3, &bad_header),
                query(
                    "bad-header",
                    "$/lean/plainGoal",
                    &uri,
                    &bad_header,
                    bad_header.len(),
                ),
                change(&uri, 4, &bad_proof),
                query(
                    "bad-proof",
                    "$/lean/plainGoal",
                    &uri,
                    &bad_proof,
                    bad_proof.len(),
                ),
                change(&uri, 5, &complete),
                query(
                    "recovered",
                    "$/lean/plainGoal",
                    &uri,
                    &complete,
                    complete.len(),
                ),
                change(&uri, 6, &body_completion),
                query(
                    "body-completion",
                    "textDocument/completion",
                    &uri,
                    &body_completion,
                    body_completion.len(),
                ),
                change(&uri, 7, &header_completion),
                query(
                    "header-completion",
                    "textDocument/completion",
                    &uri,
                    &header_completion,
                    header_completion.len(),
                ),
                change(&uri, 8, &exposed_completion),
                query(
                    "exposed-completion",
                    "textDocument/completion",
                    &uri,
                    &exposed_completion,
                    exposed_completion.len(),
                ),
                change(&uri, 9, &wrapped_body_completion),
                query(
                    "wrapped-body-completion",
                    "textDocument/completion",
                    &uri,
                    &wrapped_body_completion,
                    wrapped_body_completion.len(),
                ),
                change(&uri, 10, &wrapped_header_completion),
                query(
                    "wrapped-header-completion",
                    "textDocument/completion",
                    &uri,
                    &wrapped_header_completion,
                    wrapped_header_completion.len(),
                ),
                change(&uri, 11, &wrapped_exposed_completion),
                query(
                    "wrapped-exposed-completion",
                    "textDocument/completion",
                    &uri,
                    &wrapped_exposed_completion,
                    wrapped_exposed_completion.len(),
                ),
            ],
        );
        for id in ["goal", "warm"] {
            assert!(reply(&messages, id).contains("Law Truth"), "{messages:#?}");
            assert!(
                !reply(&messages, id).contains("\"error\":"),
                "{messages:#?}"
            );
        }
        for id in ["proved", "recovered"] {
            assert!(
                reply(&messages, id).contains("\"goals\":[]"),
                "{messages:#?}"
            );
        }
        assert!(
            reply(&messages, "hover").contains("hiddenLocal"),
            "{messages:#?}"
        );
        assert!(
            !reply(&messages, "hover").contains("\"error\":"),
            "{messages:#?}"
        );
        for id in ["bad-header", "bad-proof"] {
            assert!(
                reply(&messages, id).contains("\"code\":-32803"),
                "{messages:#?}"
            );
        }
        for label in ["hiddenProof", "hiddenLocal"] {
            for id in ["body-completion", "wrapped-body-completion"] {
                assert!(
                    reply(&messages, id).contains(&format!("\"label\":{}", quoted(label))),
                    "{messages:#?}"
                );
            }
            for id in [
                "header-completion",
                "exposed-completion",
                "wrapped-header-completion",
                "wrapped-exposed-completion",
            ] {
                assert!(reply(&messages, id).contains("\"items\":"), "{messages:#?}");
                assert!(
                    !reply(&messages, id).contains(&format!("\"label\":{}", quoted(label))),
                    "{messages:#?}"
                );
            }
        }
    }
}
