//! Installed `fln serve-lsp` resolves `.olean` imports as `fln check-source` does, under
//! the `reuse-verified` posture (bead `fln-uyuz`). The imported modules are `prelude`
//! libraries built here by `lake build`, so no `Init` closure is admitted.
#![forbid(unsafe_code)]
use std::io::{BufReader, Write};
use std::path::PathBuf;
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::mpsc::{Receiver, channel};
use std::time::Duration;

static NEXT: AtomicUsize = AtomicUsize::new(0);

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
fn hover(id: &str, uri: &str, line: usize, column: usize) -> String {
    format!(
        "{{\"jsonrpc\":\"2.0\",\"id\":{},\"method\":\"textDocument/hover\",\"params\":{{\"textDocument\":{{\"uri\":{}}},\"position\":{{\"line\":{line},\"character\":{column}}}}}}}",
        quote(id),
        quote(uri)
    )
}

/// A scratch tree: a `prelude` library `Ext` built to `.olean`s by the installed
/// `lake`, and a consumer directory whose files import it. One record store each.
struct Project(PathBuf);
impl Project {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "fln-lsp-olean-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir_all(&path).unwrap();
        let project = Self(path);
        project.library("producer", EXT_A);
        project.write("consumer/Local.lean", LOCAL);
        project.write("consumer/Use.lean", USE);
        project
    }
    fn write(&self, relative: &str, text: &str) {
        let path = self.0.join(relative);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, text).unwrap();
    }
    /// Build `Ext.A` and `Ext.B` from `a` in the package `directory`.
    fn library(&self, directory: &str, a: &str) {
        self.write(
            &format!("{directory}/lakefile.toml"),
            "name = \"ext\"\n[[lean_lib]]\nname = \"Ext\"\n",
        );
        self.write(&format!("{directory}/Ext/A.lean"), a);
        self.write(&format!("{directory}/Ext/B.lean"), EXT_B);
        for target in ["+Ext.A:olean", "+Ext.B:olean"] {
            let output = Command::new(env!("CARGO_BIN_EXE_lake"))
                .arg("--dir")
                .arg(self.0.join(directory))
                .args(["build", target])
                .env("LEAN_PATH", self.0.join("no-imports"))
                .env("FLN_IMPORT_REUSE_DIR", self.0.join("lake-records"))
                .output()
                .unwrap();
            assert!(output.status.success(), "{output:?}");
        }
    }
    fn search(&self) -> PathBuf {
        self.0.join("producer/.lake/build/lib/lean")
    }
    fn olean(&self) -> PathBuf {
        self.search().join("Ext/A.olean")
    }
    fn uri(&self) -> String {
        format!("file://{}", self.0.join("consumer/Use.lean").display())
    }
    fn server(&self) -> Command {
        let mut command = Command::new(env!("CARGO_BIN_EXE_fln"));
        command
            .arg("serve-lsp")
            .env("LEAN_PATH", self.search())
            .env("FLN_IMPORT_REUSE_DIR", self.0.join("records"));
        command
    }
}
impl Drop for Project {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

const EXT_A: &str = "prelude\ndef Ext.A (P : Prop) (h : P) : P := h\n";
const EXT_B: &str = "prelude\ndef Ext.B (P : Prop) (h : P) : P := h\n";
const LOCAL: &str = "prelude\ndef Local.id (P : Prop) (h : P) : P := h\n";
const USE: &str = "prelude\nimport Ext.A\nimport Local\ndef Use.first (P : Prop) (h : P) : P := Ext.A P (Local.id P h)\n";

/// A live server, driven one message at a time; every message is logged.
struct Session {
    child: Child,
    input: ChildStdin,
    output: Receiver<String>,
}
impl Session {
    fn start(project: &Project) -> Self {
        let mut child = project
            .server()
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        let input = child.stdin.take().unwrap();
        let stdout = child.stdout.take().unwrap();
        let (sender, output) = channel();
        std::thread::spawn(move || {
            let mut reader = BufReader::new(stdout);
            while let Ok(Some(body)) = fln_server::transport::read_message(&mut reader) {
                if sender.send(String::from_utf8(body).unwrap()).is_err() {
                    break;
                }
            }
        });
        let mut session = Self {
            child,
            input,
            output,
        };
        session.send(r#"{"jsonrpc":"2.0","id":"init","method":"initialize","params":{}}"#);
        session.until(|message| message.contains("\"id\":\"init\""));
        session.send(r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#);
        session
    }
    fn send(&mut self, message: &str) {
        eprintln!("--> {message}");
        let mut wire = Vec::new();
        fln_server::transport::write_message(&mut wire, message.as_bytes()).unwrap();
        self.input.write_all(&wire).unwrap();
        self.input.flush().unwrap();
    }
    /// Messages up to and including the first that satisfies `done`.
    fn until(&mut self, done: impl Fn(&str) -> bool) -> Vec<String> {
        let mut seen = Vec::new();
        loop {
            let message = self
                .output
                .recv_timeout(Duration::from_secs(600))
                .unwrap_or_else(|error| panic!("{error}: after {seen:#?}"));
            eprintln!("<-- {message}");
            let finished = done(&message);
            seen.push(message);
            if finished {
                return seen;
            }
        }
    }
    /// Send a document event and return the check it caused: its optional
    /// `$/frankenLean/sourceCheck` notification and its diagnostics publication.
    fn check(&mut self, message: &str) -> Check {
        self.send(message);
        let messages = self.until(|message| message.contains("textDocument/publishDiagnostics"));
        Check {
            source_check: messages
                .iter()
                .find(|message| message.contains("$/frankenLean/sourceCheck"))
                .cloned(),
            diagnostics: messages.last().unwrap().clone(),
        }
    }
    fn hover(&mut self, uri: &str, line: usize, column: usize) -> String {
        self.send(&hover("hover", uri, line, column));
        self.until(|message| message.contains("\"id\":\"hover\""))
            .pop()
            .unwrap()
    }
    fn finish(mut self) {
        self.send(r#"{"jsonrpc":"2.0","id":"end","method":"shutdown"}"#);
        self.until(|message| message.contains("\"id\":\"end\""));
        self.send(r#"{"jsonrpc":"2.0","method":"exit"}"#);
        let mut stderr = String::new();
        std::io::Read::read_to_string(&mut self.child.stderr.take().unwrap(), &mut stderr).unwrap();
        let status = self.child.wait().unwrap();
        assert!(status.success(), "{stderr}");
        assert!(stderr.is_empty(), "{stderr}");
    }
}

struct Check {
    source_check: Option<String>,
    diagnostics: String,
}
impl Check {
    fn clean(&self) -> &str {
        assert!(
            self.diagnostics.contains("\"diagnostics\":[]"),
            "{}",
            self.diagnostics
        );
        self.source_check
            .as_deref()
            .unwrap_or_else(|| panic!("no sourceCheck: {}", self.diagnostics))
    }
}

fn field<'a>(message: &'a str, key: &str) -> &'a str {
    let marker = format!("\"{key}\":\"");
    let start = message
        .find(&marker)
        .unwrap_or_else(|| panic!("{key}: {message}"))
        + marker.len();
    &message[start..start + message[start..].find('"').unwrap()]
}

/// The imported world's posture fields, as the notification reports them.
fn world(source_check: &str) -> (String, String, String, String, String) {
    let imports = &source_check[source_check.find("\"imports\":[").expect("imports")..];
    let write = imports
        .find("\"recordWrite\":\"")
        .map(|_| field(imports, "recordWrite").to_owned())
        .unwrap_or_default();
    (
        field(source_check, "importWorld").to_owned(),
        field(imports, "trust").to_owned(),
        field(imports, "admission").to_owned(),
        field(imports, "record").to_owned(),
        write,
    )
}

fn position(text: &str, needle: &str) -> (usize, usize) {
    let (line, row) = text
        .lines()
        .enumerate()
        .find(|(_, row)| row.contains(needle))
        .unwrap();
    (line, row.find(needle).unwrap() + 2)
}

/// One editor session over a file importing an `.olean` and a local source: checked
/// clean, hovered against the imported declaration, and refused when the body does
/// not typecheck against it or names a module it did not import.
#[test]
fn an_editor_session_checks_and_hovers_against_imported_oleans() {
    let project = Project::new();
    let uri = project.uri();
    let mut session = Session::start(&project);
    let opened = session.check(&open(&uri, USE));
    let notification = opened.clean();
    assert_eq!(
        world(notification),
        (
            "obtained".into(),
            "reuse-verified".into(),
            "council".into(),
            "absent".into(),
            "stored".into()
        )
    );
    assert_eq!(
        field(notification, "closureKey").len(),
        64,
        "{notification}"
    );
    let (line, column) = position(USE, "Ext.A P");
    let hovered = session.hover(&uri, line, column);
    assert!(
        hovered.contains("Ext.A : (∀ (P✝1 : Prop), (∀ (h✝1 : P✝1), P✝1))"),
        "{hovered}"
    );
    let wrong = USE.replace("Ext.A P (Local.id P h)", "Ext.A P");
    let rejected = session.check(&change(&uri, 2, &wrong));
    assert!(
        rejected.source_check.is_none(),
        "{:?}",
        rejected.source_check
    );
    // The pin refuses `Ext.A P` (of type `P → P`, expected `P`) while elaborating:
    // "Type mismatch" at the definition's column 40 (v4.32.0, measured 2026-10-07 on the
    // same three definitions in one headerless file). So does FrankenLean now, as a
    // refused conversion, in its own words.
    assert!(
        rejected
            .diagnostics
            .contains("command 0, byte 34: frontend refused source: elaboration refused source"),
        "{}",
        rejected.diagnostics
    );
    // Ext.B exists on the search path, but this file never imported it. The pin on this
    // file, with Ext.A, Ext.B and Local compiled to .olean: `4:40:
    // error(lean.unknownIdentifier): Unknown identifier `Ext.B`` (v4.32.0, 2026-10-05).
    let leaked = USE.replace("Ext.A P (Local.id P h)", "Ext.B P h");
    let unimported = session.check(&change(&uri, 3, &leaked));
    assert!(unimported.source_check.is_none());
    assert!(
        unimported
            .diagnostics
            .contains("Unknown identifier `Ext.B`"),
        "{}",
        unimported.diagnostics
    );
    session.finish();
}

/// A second server re-proves the first one's record instead of admitting again, and
/// answers the same: one key, one hover.
#[test]
fn a_second_session_re_proves_the_record_instead_of_admitting_again() {
    let project = Project::new();
    let uri = project.uri();
    let (line, column) = position(USE, "Ext.A P");
    let mut results = Vec::new();
    for _ in 0..2 {
        let mut session = Session::start(&project);
        let opened = session.check(&open(&uri, USE));
        let notification = opened.clean().to_owned();
        let hovered = session.hover(&uri, line, column);
        session.finish();
        results.push((notification, hovered));
    }
    assert_eq!(
        world(&results[0].0),
        (
            "obtained".into(),
            "reuse-verified".into(),
            "council".into(),
            "absent".into(),
            "stored".into()
        )
    );
    assert_eq!(
        world(&results[1].0),
        (
            "obtained".into(),
            "reuse-verified".into(),
            "reused".into(),
            "hit".into(),
            String::new()
        )
    );
    assert_eq!(
        field(&results[0].0, "closureKey"),
        field(&results[1].0, "closureKey")
    );
    let range = |hover: &str| hover[hover.find("\"result\"").unwrap()..].to_owned();
    assert_eq!(range(&results[0].1), range(&results[1].1));
}

/// Within one server, the world is kept while its bytes are identical and obtained
/// again the moment they are not. A rebuilt `.olean` is re-admitted under a new key;
/// a damaged one is refused, never answered from the old world; restoring the
/// original bytes hits the original record.
#[test]
fn within_a_session_the_world_is_kept_only_while_its_bytes_are_unchanged() {
    let project = Project::new();
    let uri = project.uri();
    let original = std::fs::read(project.olean()).unwrap();
    project.library(
        "rebuilt",
        "prelude\ndef Ext.A (P : Prop) (h : P) : P := h\ndef Ext.extra (P : Prop) (h : P) : P := h\n",
    );
    let rebuilt =
        std::fs::read(project.0.join("rebuilt/.lake/build/lib/lean/Ext/A.olean")).unwrap();
    assert_ne!(rebuilt, original);
    let mut session = Session::start(&project);

    let first = session.check(&open(&uri, USE));
    let first = first.clean().to_owned();
    assert_eq!(world(&first).2, "council");
    let edited = USE.replace("Use.first", "Use.second");
    let kept = session.check(&change(&uri, 2, &edited));
    let kept = kept.clean().to_owned();
    assert_eq!(world(&kept).0, "retained");
    assert_eq!(field(&kept, "closureKey"), field(&first, "closureKey"));

    std::fs::write(project.olean(), &rebuilt).unwrap();
    let uses_extra = USE.replace("Ext.A P (Local.id P h)", "Ext.extra P h");
    let readmitted = session.check(&change(&uri, 3, &uses_extra));
    let readmitted = readmitted.clean().to_owned();
    assert_eq!(
        world(&readmitted),
        (
            "obtained".into(),
            "reuse-verified".into(),
            "council".into(),
            "absent".into(),
            "stored".into()
        )
    );
    assert_ne!(
        field(&readmitted, "closureKey"),
        field(&first, "closureKey")
    );

    let mut damaged = rebuilt.clone();
    damaged[0] ^= 0x01;
    std::fs::write(project.olean(), &damaged).unwrap();
    let refused = session.check(&change(&uri, 4, &uses_extra));
    assert!(refused.source_check.is_none(), "{:?}", refused.source_check);
    assert!(
        refused.diagnostics.contains("\"severity\":1"),
        "{}",
        refused.diagnostics
    );
    assert!(
        refused.diagnostics.contains("olean"),
        "{}",
        refused.diagnostics
    );

    std::fs::write(project.olean(), &original).unwrap();
    let restored = session.check(&change(&uri, 5, USE));
    let restored = restored.clean().to_owned();
    assert_eq!(
        world(&restored),
        (
            "obtained".into(),
            "reuse-verified".into(),
            "reused".into(),
            "hit".into(),
            String::new()
        )
    );
    assert_eq!(field(&restored, "closureKey"), field(&first, "closureKey"));
    session.finish();
}

/// An import with no open buffer, no source file and no `.olean` is named as such.
#[test]
fn an_unresolvable_import_is_named_with_the_search_path() {
    let project = Project::new();
    let uri = project.uri();
    let mut session = Session::start(&project);
    let missing = USE.replace("import Local", "import Ext.Missing");
    let checked = session.check(&open(&uri, &missing));
    assert!(checked.source_check.is_none());
    assert!(
        checked
            .diagnostics
            .contains("import `Ext.Missing` is neither a source file"),
        "{}",
        checked.diagnostics
    );
    session.finish();
}
