//! Installed editor proof checking, source imports, open-buffer authority and reuse.
#![forbid(unsafe_code)]
use std::io::{BufReader, Cursor, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use fln_server::{json_string as q, transport};

static NEXT: AtomicUsize = AtomicUsize::new(0);
fn scratch() -> PathBuf {
    let path = std::env::temp_dir().join(format!("fln-lsp-proof-{}-{}", std::process::id(), NEXT.fetch_add(1, Ordering::Relaxed)));
    std::fs::create_dir_all(&path).unwrap();
    path
}
fn uri(path: &Path) -> String {
    let path = path.to_str().unwrap().replace('\\', "/");
    let mut result = String::from("file://");
    if !path.starts_with('/') { result.push('/'); }
    for byte in path.bytes() {
        if byte.is_ascii_alphanumeric() || matches!(byte, b'/' | b':' | b'-' | b'.' | b'_' | b'~') {
            result.push(char::from(byte));
        } else { result.push_str(&format!("%{byte:02X}")); }
    }
    result
}
fn notify(method: &str, params: String) -> String {
    format!("{{\"jsonrpc\":\"2.0\",\"method\":{},\"params\":{params}}}", q(method))
}
fn open(uri: &str, text: &str) -> String {
    notify("textDocument/didOpen", format!("{{\"textDocument\":{{\"uri\":{},\"version\":1,\"languageId\":\"lean4\",\"text\":{}}}}}", q(uri), q(text)))
}
fn change(uri: &str, version: usize, text: &str) -> String {
    notify("textDocument/didChange", format!("{{\"textDocument\":{{\"uri\":{},\"version\":{version}}},\"contentChanges\":[{{\"text\":{}}}]}}", q(uri), q(text)))
}
fn document(method: &str, uri: &str) -> String {
    notify(method, format!("{{\"textDocument\":{{\"uri\":{}}}}}", q(uri)))
}
fn wait(uri: &str, version: usize, id: usize) -> String {
    format!("{{\"jsonrpc\":\"2.0\",\"id\":{id},\"method\":\"textDocument/waitForDiagnostics\",\"params\":{{\"uri\":{},\"version\":{version}}}}}", q(uri))
}
fn run(binary: &str, args: &[&str], events: &[String]) -> Vec<String> {
    let mut frames = Vec::new();
    for body in [r#"{"jsonrpc":"2.0","id":0,"method":"initialize","params":{}}"#, r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#].iter().copied()
        .chain(events.iter().map(String::as_str))
        .chain([r#"{"jsonrpc":"2.0","id":999,"method":"shutdown"}"#, r#"{"jsonrpc":"2.0","method":"exit"}"#])
    { transport::write_message(&mut frames, body.as_bytes()).unwrap(); }
    let mut child = Command::new(binary).args(args).stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped()).spawn().unwrap();
    child.stdin.take().unwrap().write_all(&frames).unwrap();
    let output = child.wait_with_output().unwrap();
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    assert!(output.stderr.is_empty(), "{}", String::from_utf8_lossy(&output.stderr));
    let mut reader = BufReader::new(Cursor::new(output.stdout));
    let mut messages = Vec::new();
    while let Some(body) = transport::read_message(&mut reader).unwrap() {
        messages.push(String::from_utf8(body).unwrap());
    }
    assert!(!messages.iter().any(|m| m.contains("malformed diagnostic callback") || m.contains("ambiguous diagnostic callback")), "{messages:#?}");
    messages
}
fn fln(events: &[String]) -> Vec<String> { run(env!("CARGO_BIN_EXE_fln"), &["serve-lsp"], events) }
fn successes(messages: &[String]) -> Vec<&str> {
    messages.iter().filter(|m| m.contains("$/frankenLean/sourceCheck")).map(String::as_str).collect()
}
fn errors<'a>(messages: &'a [String], uri: &str) -> Vec<&'a str> {
    messages.iter().filter(|m| m.contains("publishDiagnostics") && m.contains(&q(uri)) && m.contains("\"diagnostics\":[{")).map(String::as_str).collect()
}

#[test]
fn both_installed_server_doors_check_proofs_records_and_registered_simp() {
    let source = "namespace Library\n@[simp] def wrap (n : Nat) : Nat := n\ntheorem checked (n : Nat) : wrap n = n := by simp\nend Library\nstructure Box where\n  value : Nat\ndef boxed : Box := { value := 7 }\ntheorem field : boxed.value = 7 := by rfl";
    for (binary, args) in [(env!("CARGO_BIN_EXE_fln"), &["serve-lsp"][..]), (env!("CARGO_BIN_EXE_lean"), &["--server"][..])] {
        let messages = run(binary, args, &[open("untitled:NativeProof.lean", source)]);
        let success = successes(&messages);
        assert_eq!(success.len(), 1, "{messages:#?}");
        assert!(success[0].contains("\"theorems\":2"));
        assert!(success[0].contains("\"executed\":false"));
        assert!(errors(&messages, "untitled:NativeProof.lean").is_empty());
    }
}

#[test]
fn an_unsaved_entry_checks_disk_imports_and_textless_save_reuses_the_graph() {
    let root = scratch();
    std::fs::write(root.join("Lib.lean"), "@[simp] def wrap (n : Nat) : Nat := n").unwrap();
    let entry = uri(&root.join("Unsaved Main.lean"));
    let messages = fln(&[open(&entry, "import Lib\ntheorem use (n : Nat) : wrap n = n := by simp"), document("textDocument/didSave", &entry)]);
    let success = successes(&messages);
    assert_eq!(success.len(), 2, "{messages:#?}");
    assert!(success[0].contains("\"elaboratedModules\":2"));
    assert!(success[1].contains("\"reusedModules\":2"));
    assert!(success[1].contains("\"replayedDeclarations\":0"));
    assert!(errors(&messages, &entry).is_empty());
    assert!(!root.join("Unsaved Main.lean").exists());
}

#[test]
fn open_imports_override_disk_and_closed_imports_return_to_disk_without_stale_hits() {
    let root = scratch();
    std::fs::write(root.join("Lib.lean"), "def value := 0").unwrap();
    let lib = uri(&root.join("Lib.lean"));
    let entry = uri(&root.join("Main.lean"));
    let messages = fln(&[
        open(&lib, "def value := 7"),
        open(&entry, "import Lib\ntheorem use : value = 7 := by rfl"),
        change(&lib, 2, "def value := 9"),
        document("textDocument/didSave", &entry),
        change(&entry, 2, "import Lib\ntheorem use : value = 9 := by rfl"),
        document("textDocument/didClose", &lib),
        document("textDocument/didSave", &entry),
        change(&entry, 3, "import Lib\ntheorem use : value = 0 := by rfl"),
    ]);
    assert_eq!(successes(&messages).len(), 5, "{messages:#?}");
    assert_eq!(errors(&messages, &entry).len(), 4, "{messages:#?}");
    assert_eq!(std::fs::read_to_string(root.join("Lib.lean")).unwrap(), "def value := 0");
}

#[test]
fn invalidated_open_imports_block_disk_fallback_and_diagnostic_waits_then_recover() {
    let root = scratch();
    std::fs::write(root.join("Lib.lean"), "def value := 7").unwrap();
    let lib = uri(&root.join("Lib.lean"));
    let entry = uri(&root.join("Main.lean"));
    let rejected = notify("textDocument/didChange", format!("{{\"textDocument\":{{\"uri\":{},\"version\":2}},\"contentChanges\":false}}", q(&lib)));
    let repaired = notify("textDocument/didSave", format!("{{\"textDocument\":{{\"uri\":{}}},\"text\":\"def value := 7\"}}", q(&lib)));
    let messages = fln(&[
        open(&lib, "def value := 7"), open(&entry, "import Lib\ntheorem use : value = 7 := by rfl"),
        rejected, document("textDocument/didSave", &entry), wait(&entry, 1, 23),
        repaired, document("textDocument/didSave", &entry), wait(&entry, 1, 24),
    ]);
    assert!(messages.iter().any(|m| m.contains("disk fallback is forbidden")), "{messages:#?}");
    assert!(messages.iter().any(|m| m.contains("\"id\":23") && m.contains("\"error\"")), "{messages:#?}");
    assert!(messages.iter().any(|m| m.contains("\"id\":24") && m.contains("\"result\":{}")), "{messages:#?}");
    assert_eq!(successes(&messages).len(), 5, "{messages:#?}");
}

#[test]
fn a_new_open_import_can_supply_source_without_an_on_disk_file() {
    let root = scratch();
    let lib = uri(&root.join("NewLibrary.lean"));
    let entry = uri(&root.join("Main.lean"));
    let messages = fln(&[open(&lib, "def value := 13"), open(&entry, "import NewLibrary\ntheorem use : value = 13 := by rfl")]);
    assert_eq!(successes(&messages).len(), 2, "{messages:#?}");
    assert!(errors(&messages, &entry).is_empty());
    assert!(!root.join("NewLibrary.lean").exists());
}

#[test]
fn unrelated_documents_cannot_lend_declarations_and_false_proofs_do_not_poison_recovery() {
    let messages = fln(&[
        open("untitled:Library.lean", "def secret := 7"),
        open("untitled:Main.lean", "theorem stolen : secret = 7 := by rfl"),
        change("untitled:Main.lean", 2, "theorem falseProof : (0 : Nat) = 1 := by rfl"),
        change("untitled:Main.lean", 3, "theorem repaired : (7 : Nat) = 7 := by rfl"),
    ]);
    assert_eq!(successes(&messages).len(), 2, "{messages:#?}");
    assert_eq!(errors(&messages, "untitled:Main.lean").len(), 2, "{messages:#?}");
}

#[test]
fn resource_stops_are_nonanswers_and_do_not_reuse_an_old_success() {
    let document_uri = "untitled:Limit.lean";
    let messages = fln(&[
        open(document_uri, "def valid := 7"),
        change(document_uri, 2, &" ".repeat(1024 * 1024 + 1)), wait(document_uri, 2, 31),
        change(document_uri, 3, "theorem valid : (7 : Nat) = 7 := by rfl"), wait(document_uri, 3, 32),
    ]);
    assert!(messages.iter().any(|m| m.contains("diagnosticOutcome") && m.contains("resource")), "{messages:#?}");
    assert!(messages.iter().any(|m| m.contains("\"id\":31") && m.contains("\"error\"")), "{messages:#?}");
    assert!(messages.iter().any(|m| m.contains("\"id\":32") && m.contains("\"result\":{}")), "{messages:#?}");
    assert_eq!(successes(&messages).len(), 2);
}

#[test]
fn admission_only_editor_reports_eval_instead_of_running_or_silently_ignoring_it() {
    let messages = fln(&[open("untitled:NoExecution.lean", "#eval 7")]);
    assert!(successes(&messages).is_empty());
    assert_eq!(errors(&messages, "untitled:NoExecution.lean").len(), 1, "{messages:#?}");
}

#[path = "lsp_proof_modules/reactive.rs"]
mod reactive;
