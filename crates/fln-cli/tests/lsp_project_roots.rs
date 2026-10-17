//! Real editor queries resolve nested package modules, not the entry's directory.
#![forbid(unsafe_code)]
use fln_server::{json_string as q, transport};
use std::io::{Cursor, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};
static NEXT: AtomicUsize = AtomicUsize::new(0);
const BASE: &str = "prelude\ntheorem Lib.keep (P : Prop) (h : P) : P := h\n";
const MAIN: &str =
    "prelude\nimport Lib.Base\ntheorem keep (P : Prop) (h : P) : P := by\n  exact Lib.keep P h\n";
fn scratch() -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fln-editor-project-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&path).unwrap();
    path
}
fn write(root: &Path, name: &str, text: &str) -> PathBuf {
    let path = root.join(name);
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(&path, text).unwrap();
    path
}
fn uri(path: &Path) -> String {
    let mut result = String::from("file://");
    let path = path.to_str().unwrap().replace('\\', "/");
    if !path.starts_with('/') {
        result.push('/');
    }
    for byte in path.bytes() {
        if byte.is_ascii_alphanumeric() || b"/:-._~".contains(&byte) {
            result.push(char::from(byte));
        } else {
            result.push_str(&format!("%{byte:02X}"));
        }
    }
    result
}
fn event(method: &str, params: &str) -> String {
    format!(
        "{{\"jsonrpc\":\"2.0\",\"method\":{},\"params\":{params}}}",
        q(method)
    )
}
fn open(path: &Path, source: &str) -> String {
    event(
        "textDocument/didOpen",
        &format!(
            "{{\"textDocument\":{{\"uri\":{},\"version\":1,\"text\":{}}}}}",
            q(&uri(path)),
            q(source)
        ),
    )
}
fn change(path: &Path, version: usize, source: &str) -> String {
    event(
        "textDocument/didChange",
        &format!(
            "{{\"textDocument\":{{\"uri\":{},\"version\":{version}}},\"contentChanges\":[{{\"text\":{}}}]}}",
            q(&uri(path)),
            q(source)
        ),
    )
}
fn goal(path: &Path, id: usize) -> String {
    format!(
        "{{\"jsonrpc\":\"2.0\",\"id\":{id},\"method\":\"$/lean/plainGoal\",\"params\":{{\"textDocument\":{{\"uri\":{}}},\"position\":{{\"line\":3,\"character\":2}}}}}}",
        q(&uri(path))
    )
}
fn run(binary: &str, args: &[&str], events: &[String]) -> Vec<String> {
    let mut input = Vec::new();
    for message in [
        r#"{"jsonrpc":"2.0","id":0,"method":"initialize","params":{}}"#,
        r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
    ]
    .into_iter()
    .chain(events.iter().map(String::as_str))
    .chain([
        r#"{"jsonrpc":"2.0","id":999,"method":"shutdown"}"#,
        r#"{"jsonrpc":"2.0","method":"exit"}"#,
    ]) {
        transport::write_message(&mut input, message.as_bytes()).unwrap();
    }
    let mut child = Command::new(binary)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child.stdin.take().unwrap().write_all(&input).unwrap();
    let deadline = Instant::now() + Duration::from_secs(30);
    while child.try_wait().unwrap().is_none() {
        if Instant::now() >= deadline {
            let _ = child.kill();
            let _ = child.wait();
            panic!("editor query timed out");
        }
        std::thread::sleep(Duration::from_millis(10));
    }
    let output = child.wait_with_output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let mut stream = Cursor::new(output.stdout);
    let mut messages = Vec::new();
    while let Some(message) = transport::read_message(&mut stream).unwrap() {
        messages.push(String::from_utf8(message).unwrap());
    }
    messages
}
fn result(messages: &[String], id: usize) -> &str {
    let key = format!("\"id\":{id},");
    messages
        .iter()
        .find(|message| message.contains(&key))
        .unwrap_or_else(|| panic!("missing {id}: {messages:#?}"))
}
fn succeeds(messages: &[String], id: usize) {
    let answer = result(messages, id);
    assert!(
        answer.contains("\"goals\":[") && answer.contains("⊢ P"),
        "{answer}"
    );
}
fn config() -> &'static str {
    "name = \"editor\"\n[[lean_lib]]\nname = \"App\"\n[[lean_lib]]\nname = \"Lib\"\n"
}
#[test]
fn nested_modules_work_on_both_installed_doors() {
    let root = scratch();
    write(&root, "lakefile.toml", config());
    write(&root, "Lib/Base.lean", BASE);
    let main = write(&root, "App/Deep/Main.lean", MAIN);
    for (binary, args) in [
        (env!("CARGO_BIN_EXE_fln"), &["serve-lsp"][..]),
        (env!("CARGO_BIN_EXE_lean"), &["--server"][..]),
    ] {
        let messages = run(binary, args, &[open(&main, MAIN), goal(&main, 1)]);
        succeeds(&messages, 1);
        assert!(
            messages
                .iter()
                .any(|m| m.contains("$/frankenLean/sourceCheck")),
            "{messages:#?}"
        );
    }
}
#[test]
fn different_library_source_directories_keep_unsaved_dependency_authority() {
    let root = scratch();
    write(
        &root,
        "lakefile.toml",
        "name = \"editor\"\nsrcDir = \"sources\"\n[[lean_lib]]\nname = \"App\"\nsrcDir = \"application\"\n[[lean_lib]]\nname = \"Lib\"\nsrcDir = \"library\"\n",
    );
    let dep = write(&root, "sources/library/Lib/Base.lean", "prelude\n");
    let main = write(&root, "sources/application/App/Deep/Main.lean", MAIN);
    let messages = run(
        env!("CARGO_BIN_EXE_fln"),
        &["serve-lsp"],
        &[
            open(&dep, BASE),
            open(&main, MAIN),
            goal(&main, 1),
            change(
                &dep,
                2,
                "prelude\ndef Lib.keep (P : Prop) (h : P) : P := P\n",
            ),
            goal(&main, 2),
            change(&dep, 3, BASE),
            goal(&main, 3),
            event(
                "textDocument/didClose",
                &format!("{{\"textDocument\":{{\"uri\":{}}}}}", q(&uri(&dep))),
            ),
            goal(&main, 4)
                .replace("$/lean/plainGoal", "textDocument/hover")
                .replace("\"character\":2", "\"character\":8"),
        ],
    );
    succeeds(&messages, 1);
    assert!(result(&messages, 2).contains("\"error\":"), "{messages:#?}");
    succeeds(&messages, 3);
    assert!(
        result(&messages, 4).contains("\"error\":"),
        "disk lacks Lib.keep: {messages:#?}"
    );
    let successes = messages
        .iter()
        .filter(|m| m.contains("$/frankenLean/sourceCheck") && m.contains(&q(&uri(&main))))
        .count();
    assert_eq!(
        successes, 2,
        "dependency edits must also refresh importer diagnostics: {messages:#?}"
    );
}
#[test]
fn same_module_names_in_other_projects_cannot_override_local_imports() {
    let first = scratch();
    let second = scratch();
    for root in [&first, &second] {
        write(root, "lakefile.toml", config());
    }
    write(&first, "Lib/Base.lean", BASE);
    let other = write(&second, "Lib/Base.lean", BASE);
    let main = write(&first, "App/Deep/Main.lean", MAIN);
    let messages = run(
        env!("CARGO_BIN_EXE_fln"),
        &["serve-lsp"],
        &[open(&other, "prelude\n"), open(&main, MAIN), goal(&main, 1)],
    );
    succeeds(&messages, 1);
}
#[test]
fn ambiguous_library_ownership_and_escaping_directories_refuse() {
    for config in [
        "name = \"editor\"\n[[lean_lib]]\nname = \"App\"\n[[lean_lib]]\nname = \"Lib\"\n[[lean_lib]]\nname = \"Other\"\nroots = [\"Lib\"]\nsrcDir = \"other\"\n",
        "name = \"editor\"\nsrcDir = \"../outside\"\n[[lean_lib]]\nname = \"App\"\n",
    ] {
        let root = scratch();
        write(&root, "lakefile.toml", config);
        write(&root, "Lib/Base.lean", BASE);
        let main = write(&root, "App/Deep/Main.lean", MAIN);
        let messages = run(
            env!("CARGO_BIN_EXE_fln"),
            &["serve-lsp"],
            &[open(&main, MAIN), goal(&main, 1)],
        );
        let answer = result(&messages, 1);
        assert!(answer.contains("\"error\":"), "{answer}");
        assert!(
            answer.contains("source director") || answer.contains("ambiguous"),
            "{answer}"
        );
    }
}

#[test]
fn declared_roots_and_space_containing_source_directories_are_respected() {
    let root = scratch();
    write(
        &root,
        "lakefile.toml",
        "name = \"editor\"\n[[lean_lib]]\nname = \"Misc\"\n[[lean_lib]]\nname = \"Application\"\nroots = [\"App\"]\nsrcDir = \"app sources\"\n[[lean_lib]]\nname = \"Library\"\nroots = [\"Lib\"]\nsrcDir = \"lib sources\"\n",
    );
    write(&root, "lib sources/Lib/Base.lean", BASE);
    let main = write(&root, "app sources/App/Deep/Main.lean", MAIN);
    succeeds(
        &run(
            env!("CARGO_BIN_EXE_fln"),
            &["serve-lsp"],
            &[open(&main, MAIN), goal(&main, 1)],
        ),
        1,
    );
}

#[test]
fn malformed_and_oversized_configuration_cannot_fall_back_to_another_root() {
    for config in ["name = false".to_owned(), " ".repeat(65537)] {
        let root = scratch();
        write(&root, "lakefile.toml", &config);
        let main = write(&root, "App/Main.lean", MAIN);
        // A tempting legacy-directory source must not rescue bad project metadata.
        write(&root, "App/Lib/Base.lean", BASE);
        let messages = run(
            env!("CARGO_BIN_EXE_fln"),
            &["serve-lsp"],
            &[open(&main, MAIN), goal(&main, 1)],
        );
        assert!(result(&messages, 1).contains("\"error\":"), "{messages:#?}");
        assert!(
            !messages
                .iter()
                .any(|m| m.contains("$/frankenLean/sourceCheck")),
            "{messages:#?}"
        );
    }
}

#[cfg(unix)]
#[test]
fn configured_source_symlinks_are_refused_before_importing_them() {
    let root = scratch();
    let outside = scratch();
    write(&outside, "Lib/Base.lean", BASE);
    write(
        &root,
        "lakefile.toml",
        "name = \"editor\"\n[[lean_lib]]\nname = \"App\"\n[[lean_lib]]\nname = \"Lib\"\nsrcDir = \"linked\"\n",
    );
    std::os::unix::fs::symlink(&outside, root.join("linked")).unwrap();
    let main = write(&root, "App/Main.lean", MAIN);
    let messages = run(
        env!("CARGO_BIN_EXE_fln"),
        &["serve-lsp"],
        &[open(&main, MAIN), goal(&main, 1)],
    );
    assert!(result(&messages, 1).contains("symlink"), "{messages:#?}");
    assert!(
        !messages
            .iter()
            .any(|m| m.contains("$/frankenLean/sourceCheck")),
        "{messages:#?}"
    );
}
